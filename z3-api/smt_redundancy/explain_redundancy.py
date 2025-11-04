import re
import time
from bisect import bisect_right
from typing import List, Tuple

from utils.helper import get_decls_and_sorts, get_logic_from_smt2, prettify_error
from z3 import *

from .minimizer import quick_explain

PASS = "GoalNotEntailedByInput"
FAIL = "GoalEntailedByInput"
UNRESOLVED = "UNRESOLVED"


def find_assertion_line_ranges(
    smtlib_script: str,
) -> List[Tuple[int, int, int, int, ExprRef]]:
    """Find (start_line, end_line, start_col, end_col, ast_ref) for every (assert ...)."""

    assert_pattern = re.compile(r"\(\s*assert\b", re.IGNORECASE)

    lines = smtlib_script.split("\n")
    line_offsets = [0]
    for line in lines:
        line_offsets.append(line_offsets[-1] + len(line) + 1)

    def pos_to_line_col(pos: int) -> Tuple[int, int]:
        idx = bisect_right(line_offsets, pos) - 1
        if idx < 0:
            idx = 0
        column = pos - line_offsets[idx]
        return idx + 1, column

    assertion_texts_with_ranges: list[Tuple[int, int, int, int, str]] = []

    i = 0
    script_len = len(smtlib_script)

    while i < script_len:
        ch = smtlib_script[i]

        if ch == ";":
            newline_pos = smtlib_script.find("\n", i)
            if newline_pos == -1:
                break
            i = newline_pos + 1
            continue

        if ch.isspace():
            i += 1
            continue

        match = assert_pattern.match(smtlib_script, i)
        if match:
            start_pos = i
            paren_count = 0
            cursor = i
            end_pos = None

            while cursor < script_len:
                current_char = smtlib_script[cursor]

                if current_char == ";":
                    newline_pos = smtlib_script.find("\n", cursor)
                    if newline_pos == -1:
                        cursor = script_len
                        break
                    cursor = newline_pos + 1
                    continue

                if current_char == "(":
                    paren_count += 1
                elif current_char == ")":
                    paren_count -= 1
                    if paren_count == 0:
                        end_pos = cursor + 1
                        break

                cursor += 1

            if paren_count != 0 or end_pos is None:
                raise ValueError(
                    f"Malformed assertion starting at position {start_pos}: unmatched parentheses"
                )

            assertion_text = smtlib_script[start_pos:end_pos]
            start_line, start_col = pos_to_line_col(start_pos)
            end_line, end_col_inclusive = pos_to_line_col(end_pos - 1)
            end_col = end_col_inclusive + 2

            assertion_texts_with_ranges.append(
                (start_line, end_line, start_col, end_col, assertion_text)
            )

            i = end_pos
            continue

        i += 1

    # Get all assertions from the given script
    script_logic = get_logic_from_smt2(smtlib_script)
    solver = SolverFor(script_logic) if script_logic else Solver()
    solver.from_string(smtlib_script)
    all_assertions = list(solver.assertions())

    sorts_env, decls_env = get_decls_and_sorts(all_assertions)

    # Match syntactically found assertions with semantically parsed ones
    # Parse each assertion (in SMT-LIB formal) individually by creating a temporary script
    assertion_ranges = []

    for (
        start_line,
        end_line,
        start_col,
        end_col,
        assertion_text,
    ) in assertion_texts_with_ranges:
        # Parse the assertion individually
        try:
            parsed = parse_smt2_string(
                assertion_text,
                sorts=sorts_env,
                decls=decls_env,
                ctx=solver.ctx,
            )

            if len(parsed) >= 1:
                ast_ref = parsed[-1]
                assertion_ranges.append(
                    (start_line, end_line, start_col, end_col, ast_ref)
                )
        except Exception:
            # If we can't parse this assertion, skip it
            pass

    return assertion_ranges


def explain_redundancy_unsat_core(
    solver: Solver,
    given_assert: ExprRef,
    original_assertions: list[ExprRef],
    smt_logic: str = None,
) -> tuple[float, list[ExprRef]]:
    s = SolverFor(smt_logic, ctx=solver.ctx) if smt_logic else Solver(ctx=solver.ctx)
    s.set(unsat_core=True)
    s.set("core.minimize", True)

    start = time.time()

    # Add NOT(given_assert) - we want to find what contradicts this
    s.add(Not(given_assert))

    # Track each assertion
    trackerToAssertion = {}
    for i, assertion in enumerate(original_assertions):
        tracker = Bool("noOneWillEverUseThisTrackerVariableName_" + str(i))
        trackerToAssertion[tracker] = assertion
        s.assert_and_track(assertion, tracker)

    # Check if the assertions entail given_assert
    if s.check() == unsat:
        # Get the unsat core
        core = s.unsat_core()
        # Map trackers back to assertions
        minimal_set = [trackerToAssertion[tracker] for tracker in core]
        time_taken = time.time() - start
        return time_taken, minimal_set
    else:
        # The assertions do not entail given_assert
        time_taken = time.time() - start
        return time_taken, []


def explain_redundancy_marker_quick_explain(
    solver: Solver,
    given_assert: ExprRef,
    original_assertions: list[ExprRef],
    smt_logic: str = None,
) -> tuple[float, list[ExprRef]]:
    s = SolverFor(smt_logic, ctx=solver.ctx) if smt_logic else Solver(ctx=solver.ctx)
    s.set(random_seed=42)

    # Create markers for each assertion
    markers = []
    markerToAssertion = {}

    for i, assertion in enumerate(original_assertions):
        marker = Bool("noOneWillEverUseThisMarkerVariableName_" + str(i))
        markers.append(marker)
        # Use string representation as key for reliable lookup
        markerToAssertion[str(marker)] = assertion

    # Build the constraint: markers imply their corresponding assertions
    for i, assertion in enumerate(original_assertions):
        s.add(Implies(markers[i], assertion))

    # Add the negation of the goal
    s.add(Not(given_assert))

    def test(inp: list) -> str:
        """Test if the assertions corresponding to inp (markers) entail given_assert"""
        s.push()
        for marker in markers:
            if marker in inp:
                s.add(marker == True)
            else:
                s.add(marker == False)

        res = s.check()
        s.pop()

        if res == unsat:
            # The selected assertions entail given_assert
            return FAIL
        else:
            # The selected assertions do not entail given_assert
            return PASS

    start = time.time()
    min_markers = quick_explain(test, markers)
    # Map markers back to assertions using string representation
    if min_markers == PASS:
        min_set = []
    else:
        min_set = [markerToAssertion[str(marker)] for marker in min_markers]
    time_taken = time.time() - start

    return time_taken, min_set


def explain_redundancy_from_smtlib(
    smtlib_script: str, line_number: int, method: str = "quick_explain"
) -> Tuple[float, List[ExprRef], ExprRef, List[List[int]], List[int]]:
    """Explain redundancy of the assertion at the given `line number` in the SMT-LIB script."""
    smt_logic = get_logic_from_smt2(smtlib_script)
    solver = SolverFor(smt_logic) if smt_logic else Solver()
    solver.from_string(smtlib_script)
    all_assertions = list(solver.assertions())

    if len(all_assertions) == 0:
        raise ValueError(prettify_error("The SMT-LIB script contains no assertions"))

    # Find line ranges and ASTRef for each assertion
    try:
        assertion_ranges = find_assertion_line_ranges(smtlib_script)
    except ValueError as e:
        raise ValueError(prettify_error(f"Error parsing assertions: {str(e)}"))

    if len(assertion_ranges) == 0:
        raise ValueError(
            prettify_error("No (assert ...) statements found in the script")
        )

    # Create a mapping from ASTRef to line ranges for assertions we found syntactically
    ast_to_line_range = {}
    for start_line, end_line, start_col, end_col, ast_ref in assertion_ranges:
        # Use the AST structure as a key (we'll match by equality later)
        # id to use as key (memory address)
        ast_to_line_range[id(ast_ref)] = (
            start_line,
            end_line,
            start_col,
            end_col,
            ast_ref,
        )

    # Find which assertion contains the given line_number
    # Match by AST equality
    # When multiple assertions are on the same line- (currently, the last one)
    # FIXME: better to use explain_redundancy_from_smtlib_by_assertion in such cases
    assertion_index = None
    matched_ast_id = None
    matching_candidates = []

    for ast_id, (
        start_line,
        end_line,
        start_col,
        end_col,
        ast_ref,
    ) in ast_to_line_range.items():
        if start_line <= line_number <= end_line:
            # Found a syntactic match, now find the corresponding semantic assertion
            for i, semantic_assertion in enumerate(all_assertions):
                if eq(ast_ref, semantic_assertion):
                    matching_candidates.append(
                        (i, ast_id, start_line, end_line, start_col, end_col)
                    )
                    break

    # If we have multiple candidates (multiple assertions on same line),
    # prefer the last one in the order they appear in the assertion_ranges list
    # FIXME: better to use explain_redundancy_from_smtlib_by_assertion in such cases
    if matching_candidates:
        # Sort by the order in which they appear in all_assertions (semantic order)
        # Then take the last one that matches the line number
        assertion_index = matching_candidates[-1][0]
        matched_ast_id = matching_candidates[-1][1]

    if assertion_index is None:
        # Line number might be within an assertion syntactically but that assertion
        # was popped or not in the final assertion set
        available_ranges = [
            (start_line, end_line)
            for start_line, end_line, start_col, end_col, _ in assertion_ranges
        ]
        raise ValueError(
            prettify_error(
                f"Line {line_number} is not within any active (assert ...) statement. "
                f"Available assertion line ranges: {available_ranges}. "
                f"Note: assertions within push/pop blocks may not be active."
            )
        )

    # Extract the assertion to explain
    given_assert = all_assertions[assertion_index]

    # Get the range information for the target assertion
    target_range = matching_candidates[-1] if matching_candidates else None

    # Create list of other assertions (excluding the one we're explaining)
    original_assertions = []

    for i, a in enumerate(all_assertions):
        if i != assertion_index:
            original_assertions.append(a)

    # Select the explanation method
    methods = {
        "unsat_core": explain_redundancy_unsat_core,
        "quick_explain": explain_redundancy_marker_quick_explain,
    }

    if method not in methods:
        raise ValueError(
            f"Unknown method: {method}. Choose from {list(methods.keys())}"
        )

    explain_func = methods[method]

    # Run the explanation
    time_taken, minimal_set = explain_func(solver, given_assert, original_assertions)

    # Map the minimal set back to line ranges using ASTRef matching
    minimal_line_ranges = []
    for assertion in minimal_set:
        # Find this assertion in the syntactic mapping by checking AST equality
        for ast_id, (
            start_line,
            end_line,
            start_col,
            end_col,
            ast_ref,
        ) in ast_to_line_range.items():
            if ast_id != matched_ast_id and eq(assertion, ast_ref):
                minimal_line_ranges.append([start_line, end_line, start_col, end_col])
                break

    # Get the target assertion range
    target_assertion_range = None
    if target_range:
        # target_range is (i, ast_id, start_line, end_line, start_col, end_col)
        target_assertion_range = [
            target_range[2],
            target_range[3],
            target_range[4],
            target_range[5],
        ]

    return (
        time_taken,
        minimal_set,
        given_assert,
        minimal_line_ranges,
        target_assertion_range,
    )


def explain_redundancy_from_smtlib_by_assertion(
    smtlib_script: str, assertion_text: str, method: str = "quick_explain"
) -> Tuple[float, List[ExprRef], ExprRef, List[List[int]], List[int]]:
    """
    Explain redundancy by providing the `assertion text` directly instead of a line number.
    This is more precise when multiple assertions are on the same line.
    """
    smt_logic = get_logic_from_smt2(smtlib_script)
    solver = SolverFor(smt_logic) if smt_logic else Solver()
    solver.from_string(smtlib_script)
    all_assertions = list(solver.assertions())

    if len(all_assertions) == 0:
        raise ValueError(prettify_error("The SMT-LIB script contains no assertions"))

    normalized_assertion_text = assertion_text.strip()

    # Parse the assertion text to get its AST
    sorts_env, decls_env = get_decls_and_sorts(all_assertions)
    try:
        parsed = parse_smt2_string(
            normalized_assertion_text,
            sorts=sorts_env,
            decls=decls_env,
            ctx=solver.ctx,
        )

        if len(parsed) == 0:
            raise ValueError(
                prettify_error(f"Could not parse assertion from: {assertion_text}")
            )

        target_ast = parsed[-1]
    except Exception as e:
        raise ValueError(
            prettify_error(f"Error parsing assertion '{assertion_text}': {str(e)}")
        )

    # Find this assertion in the all_assertions list
    assertion_index = None
    for i, semantic_assertion in enumerate(all_assertions):
        if eq(target_ast, semantic_assertion):
            assertion_index = i
            break

    if assertion_index is None:
        raise ValueError(
            prettify_error(
                f"Assertion '{assertion_text}' not found in the active assertions. "
                f"It may have been popped or not exist in the script. "
                f"Active assertions: {[str(a) for a in all_assertions]}"
            )
        )

    # Extract the assertion to explain
    given_assert = all_assertions[assertion_index]

    # Create list of other assertions (excluding the one we're explaining)
    original_assertions = []
    for i, a in enumerate(all_assertions):
        if i != assertion_index:
            original_assertions.append(a)

    # FIXME: Maybe we don't need all of them. So far, quick explain marker performs best.
    methods = {
        "unsat_core": explain_redundancy_unsat_core,
        "quick_explain": explain_redundancy_marker_quick_explain,
    }

    if method not in methods:
        raise ValueError(
            f"Unknown method: {method}. Choose from {list(methods.keys())}"
        )

    explain_func = methods[method]

    time_taken, minimal_set = explain_func(solver, given_assert, original_assertions)

    # Find line ranges for each assertion (for mapping results back to source)
    try:
        assertion_ranges = find_assertion_line_ranges(smtlib_script)
    except ValueError as e:
        raise ValueError(prettify_error(f"Error parsing assertions: {str(e)}"))

    # Create a mapping from ASTRef to line ranges
    ast_to_line_range = {}
    for start_line, end_line, start_col, end_col, ast_ref in assertion_ranges:
        ast_to_line_range[id(ast_ref)] = (
            start_line,
            end_line,
            start_col,
            end_col,
            ast_ref,
        )

    # Map the minimal set back to line ranges using ASTRef matching
    minimal_line_ranges = []
    for assertion in minimal_set:
        # Find this assertion in the syntactic mapping by checking AST equality
        for ast_id, (
            start_line,
            end_line,
            start_col,
            end_col,
            ast_ref,
        ) in ast_to_line_range.items():
            if eq(assertion, ast_ref):
                minimal_line_ranges.append([start_line, end_line, start_col, end_col])
                break

    # Find the target assertion range
    target_assertion_range = None
    for ast_id, (
        start_line,
        end_line,
        start_col,
        end_col,
        ast_ref,
    ) in ast_to_line_range.items():
        if eq(target_ast, ast_ref):
            target_assertion_range = [start_line, end_line, start_col, end_col]
            break

    return (
        time_taken,
        minimal_set,
        given_assert,
        minimal_line_ranges,
        target_assertion_range,
    )


def explain_redundancy_from_smtlib_file(
    file_path: str, line_number: int, method: str = "unsat_core"
) -> Tuple[float, List[ExprRef], ExprRef, List[List[int]]]:
    # Read the file
    with open(file_path, "r") as f:
        smtlib_script = f.read()

    return explain_redundancy_from_smtlib(smtlib_script, line_number, method)
