import re
import time
from typing import List, Tuple

from utils.helper import get_all_vars, get_logic_from_smt2, prettify_error
from z3 import *

from .minimizer import quick_explain

PASS = "GoalNotEntailedByInput"
FAIL = "GoalEntailedByInput"
UNRESOLVED = "UNRESOLVED"


def find_assertion_line_ranges(
    smtlib_script: str,
) -> List[Tuple[int, int, int, int, ExprRef]]:
    """Find the line ranges (start_line, end_line, start_col, end_col, ast_ref) for each (assert ...) statement."""
    # Matches: (assert, ( assert, (  assert  , etc.
    assert_pattern = re.compile(r"\(\s*assert\s+", re.IGNORECASE)

    lines = smtlib_script.split("\n")
    assertion_texts_with_ranges = (
        []
    )  # To store (start_line, end_line, start_col, end_col, assertion_text)

    # Track position in the entire script
    char_position = 0

    for line_idx, line in enumerate(lines):
        line_start_pos = char_position

        # Find all assert statements in this line
        for match in assert_pattern.finditer(line):
            match_start_in_line = match.start()
            match_start_pos = line_start_pos + match_start_in_line

            # Start from the opening parenthesis of (assert
            start_line = line_idx + 1  # 1-indexed
            start_col = match_start_in_line + 1  # 1-indexed column

            # Count parentheses to find where the assertion ends
            paren_count = 0
            end_line = None
            end_col = None
            end_char_pos = None

            # Search through the script starting from this position
            for search_line_idx in range(line_idx, len(lines)):
                search_line = lines[search_line_idx]

                # Determine where to start searching in this line
                if search_line_idx == line_idx:
                    start_col = match_start_in_line
                else:
                    start_col = 0

                for col_idx in range(start_col, len(search_line)):
                    char = search_line[col_idx]

                    if char == "(":
                        paren_count += 1
                    elif char == ")":
                        paren_count -= 1

                        if paren_count == 0:
                            # Found the end of this assertion
                            end_line = search_line_idx + 1  # 1-indexed
                            end_col = (
                                col_idx + 2
                            )  # 1-indexed, +2 to include the closing paren
                            # Calculate absolute character position
                            if search_line_idx == line_idx:
                                end_char_pos = line_start_pos + col_idx + 1
                            else:
                                end_char_pos = (
                                    sum(
                                        len(lines[i]) + 1
                                        for i in range(search_line_idx)
                                    )
                                    + col_idx
                                    + 1
                                )
                            break

                if paren_count == 0:
                    break

            if paren_count != 0:
                # Malformed assertion - couldn't find matching closing paren
                raise ValueError(
                    f"Malformed assertion starting at line {start_line}: unmatched parentheses"
                )

            # Extract the assertion text
            assertion_text = smtlib_script[match_start_pos:end_char_pos]
            assertion_texts_with_ranges.append(
                (start_line, end_line, start_col, end_col, assertion_text)
            )

        char_position += len(line) + 1  # Move to next line

    # Get all assertions from the given script
    script_logic = get_logic_from_smt2(smtlib_script)
    solver = SolverFor(script_logic) if script_logic else Solver()
    solver.from_string(smtlib_script)
    all_assertions = list(solver.assertions())

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
            # Get all variables from all_assertions to build proper declarations
            all_vars = get_all_vars(all_assertions)

            # Build SMT-LIB declarations for each variable
            declarations = []
            for var in all_vars:
                if is_const(var):
                    # It's a constant - generate a declare-const statement
                    var_name = var.decl().name()
                    var_sort = var.sort()
                    declarations.append(f"(declare-const {var_name} {var_sort})")
                elif hasattr(var, "name") and hasattr(var, "arity"):
                    # It's a function declaration - generate a declare-fun statement
                    func_name = var.name()
                    arity = var.arity()
                    domain_sorts = [var.domain(i) for i in range(arity)]
                    range_sort = var.range()
                    domain_str = " ".join(str(s) for s in domain_sorts)
                    declarations.append(
                        f"(declare-fun {func_name} ({domain_str}) {range_sort})"
                    )

            # Create a temporary script with declarations + this assertion
            temp_script = "\n".join(declarations) + "\n" + assertion_text

            temp_solver = SolverFor(script_logic) if script_logic else Solver()
            temp_solver.from_string(temp_script)
            temp_assertions = list(temp_solver.assertions())

            if len(temp_assertions) >= 1:
                # Use the last assertion (the one we just added)
                ast_ref = temp_assertions[-1]
                assertion_ranges.append(
                    (start_line, end_line, start_col, end_col, ast_ref)
                )
        except Exception as e:
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
    all_vars = get_all_vars(all_assertions)
    try:
        declarations = []
        for var in all_vars:
            if is_const(var):
                # It's a constant - generate a declare-const statement
                var_name = var.decl().name()
                var_sort = var.sort()
                declarations.append(f"(declare-const {var_name} {var_sort})")
            elif hasattr(var, "name") and hasattr(var, "arity"):
                # It's a function declaration
                func_name = var.name()
                arity = var.arity()
                domain_sorts = [var.domain(i) for i in range(arity)]
                range_sort = var.range()
                domain_str = " ".join(str(s) for s in domain_sorts)
                declarations.append(
                    f"(declare-fun {func_name} ({domain_str}) {range_sort})"
                )

        temp_script = "\n".join(declarations) + "\n" + normalized_assertion_text
        temp_solver = SolverFor(smt_logic) if smt_logic else Solver()
        temp_solver.from_string(temp_script)
        temp_assertions = list(temp_solver.assertions())

        if len(temp_assertions) == 0:
            raise ValueError(
                prettify_error(f"Could not parse assertion from: {assertion_text}")
            )

        target_ast = temp_assertions[-1]
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
