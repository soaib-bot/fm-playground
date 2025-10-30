import time
from z3 import *
from .minimizer import ddmin, quick_explain
from typing import Tuple, List

PASS = "GoalNotEntailedByInput"
FAIL = "GoalEntailedByInput"
UNRESOLVED = "UNRESOLVED"


def find_assertion_line_ranges(smtlib_script: str) -> List[Tuple[int, int]]:
    """
    Find the line ranges (start_line, end_line) for each (assert ...) statement.
    Handles multi-line assertions by tracking parentheses.

    Returns:
        List of tuples (start_line, end_line) for each assertion (1-indexed, inclusive)
    """
    lines = smtlib_script.split("\n")
    assertion_ranges = []

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # Check if this line starts an assertion
        if line.startswith("(assert ") or line == "(assert":
            start_line = i + 1  # 1-indexed

            # Count parentheses to find where the assertion ends
            paren_count = 0
            j = i

            while j < len(lines):
                for char in lines[j]:
                    if char == "(":
                        paren_count += 1
                    elif char == ")":
                        paren_count -= 1
                        if paren_count == 0:
                            # Found the end of this assertion
                            end_line = j + 1  # 1-indexed
                            assertion_ranges.append((start_line, end_line))
                            i = j  # Continue from after this assertion
                            break

                if paren_count == 0:
                    break
                j += 1

            if paren_count != 0:
                # Malformed assertion - couldn't find matching closing paren
                raise ValueError(
                    f"Malformed assertion starting at line {start_line}: unmatched parentheses"
                )

        i += 1

    return assertion_ranges


def explain_redundancy_ddmin(
    solver: Solver, given_assert: ExprRef, original_assertions: list[ExprRef]
) -> tuple[float, list[ExprRef]]:
    s = Solver(ctx=solver.ctx)
    s.set(random_seed=42)

    def test(inp: list) -> str:
        """Test if inp entails given_assert"""
        s.push()
        if len(inp) > 0:
            s.add(And(inp))
        # Check if they entail given_assert by checking if inp AND NOT(given_assert) is UNSAT
        s.add(Not(given_assert))
        res = s.check()
        s.pop()

        if res == unsat:
            # inp entails given_assert, i.e., we can dig deeper
            return FAIL
        else:
            # inp does not entail given_assert
            return PASS

    start = time.time()
    min_set = ddmin(test, original_assertions)
    time_taken = time.time() - start

    return time_taken, min_set


def explain_redundancy_quick_explain(
    solver: Solver, given_assert: ExprRef, original_assertions: list[ExprRef]
) -> tuple[float, list[ExprRef]]:
    s = Solver(ctx=solver.ctx)
    s.set(random_seed=42)

    def test(inp: list) -> str:
        s.push()
        if len(inp) > 0:
            s.add(And(inp))
        s.add(Not(given_assert))
        res = s.check()
        s.pop()

        if res == unsat:
            return FAIL
        else:
            return PASS

    start = time.time()
    min_set = quick_explain(test, original_assertions)
    time_taken = time.time() - start

    return time_taken, min_set


def explain_redundancy_unsat_core(
    solver: Solver, given_assert: ExprRef, original_assertions: list[ExprRef]
) -> tuple[float, list[ExprRef]]:
    s = Solver(ctx=solver.ctx)
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


def explain_redundancy_marker_ddmin(
    solver: Solver, given_assert: ExprRef, original_assertions: list[ExprRef]
) -> tuple[float, list[ExprRef]]:
    s = Solver(ctx=solver.ctx)
    s.set(random_seed=42)

    # Create markers for each assertion
    markers = []
    markerToAssertion = {}

    for i, assertion in enumerate(original_assertions):
        marker = Bool("noOneWillEverUseThisMarkerVariableName_" + str(i))
        markers.append(marker)
        markerToAssertion[marker] = assertion

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
    min_markers = ddmin(test, markers)
    # Map markers back to assertions
    min_set = [markerToAssertion[marker] for marker in min_markers]
    time_taken = time.time() - start

    return time_taken, min_set


def explain_redundancy_marker_quick_explain(
    solver: Solver, given_assert: ExprRef, original_assertions: list[ExprRef]
) -> tuple[float, list[ExprRef]]:
    s = Solver(ctx=solver.ctx)
    s.set(random_seed=42)

    # Create markers for each assertion
    markers = []
    markerToAssertion = {}

    for i, assertion in enumerate(original_assertions):
        marker = Bool("noOneWillEverUseThisMarkerVariableName_" + str(i))
        markers.append(marker)
        markerToAssertion[marker] = assertion

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
    # Map markers back to assertions
    min_set = [markerToAssertion[marker] for marker in min_markers]
    time_taken = time.time() - start

    return time_taken, min_set


def explain_redundancy_from_smtlib(
    smtlib_script: str, line_number: int, method: str = "marker_quick_explain"
) -> Tuple[float, List[ExprRef], ExprRef, List[List[int]]]:
    solver = Solver()
    solver.from_string(smtlib_script)
    all_assertions = list(solver.assertions())

    if len(all_assertions) == 0:
        raise ValueError("The SMT-LIB script contains no assertions")

    # Find line ranges for each assertion
    try:
        assertion_ranges = find_assertion_line_ranges(smtlib_script)
    except ValueError as e:
        raise ValueError(f"Error parsing assertions: {e}")

    if len(assertion_ranges) == 0:
        raise ValueError("No (assert ...) statements found in the script")

    # Check if we have the right number of assertions
    if len(assertion_ranges) != len(all_assertions):
        raise ValueError(
            f"Mismatch: found {len(assertion_ranges)} assert statements but Z3 parsed {len(all_assertions)} assertions. This might be due to malformed SMT-LIB."
        )

    # Find which assertion contains the given line_number
    assertion_index = None
    for i, (start, end) in enumerate(assertion_ranges):
        if start <= line_number <= end:
            assertion_index = i
            break

    if assertion_index is None:
        # Line number is not within any assertion
        raise ValueError(
            f"Line {line_number} is not within any (assert ...) statement. Assertion line ranges are: {assertion_ranges}"
        )

    # Extract the assertion to explain
    given_assert = all_assertions[assertion_index]

    # Create list of other assertions (excluding the one we're explaining)
    original_assertions = []

    for i, a in enumerate(all_assertions):
        if i != assertion_index:
            original_assertions.append(a)

    # Select the explanation method
    methods = {
        "ddmin": explain_redundancy_ddmin,
        "quick_explain": explain_redundancy_quick_explain,
        "unsat_core": explain_redundancy_unsat_core,
        "marker_ddmin": explain_redundancy_marker_ddmin,
        "marker_quick_explain": explain_redundancy_marker_quick_explain,
    }

    if method not in methods:
        raise ValueError(
            f"Unknown method: {method}. Choose from {list(methods.keys())}"
        )

    explain_func = methods[method]

    # Run the explanation
    time_taken, minimal_set = explain_func(solver, given_assert, original_assertions)

    # Map the minimal set back to line ranges
    minimal_line_ranges = []
    for assertion in minimal_set:
        # Find this assertion in the original list by checking equality
        for i, orig_assertion in enumerate(all_assertions):
            if i != assertion_index and eq(assertion, orig_assertion):
                start, end = assertion_ranges[i]
                minimal_line_ranges.append([start, end])
                break

    return time_taken, minimal_set, given_assert, minimal_line_ranges


def explain_redundancy_from_smtlib_file(
    file_path: str, line_number: int, method: str = "unsat_core"
) -> Tuple[float, List[ExprRef], ExprRef, List[List[int]]]:
    # Read the file
    with open(file_path, "r") as f:
        smtlib_script = f.read()

    return explain_redundancy_from_smtlib(smtlib_script, line_number, method)


# spec = """(declare-const x Int)
# (declare-const y Int)

#   (assert
#     (> x 2)
#   )
# (assert
#     (> x 1)
#   )
# """
# print(explain_redundancy_from_smtlib(spec, 7))
