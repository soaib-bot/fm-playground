import re

from z3 import *

from utils.helper import get_decls_and_sorts

from .minimizer import ddmin, quick_explain

PASS = "GoalNotEntailedByInput"
FAIL = "GoalEntailedByInput"
UNRESOLVED = "UNRESOLVED"

TIMEOUT = 10

Z3_SUPPORTED_LOGICS = [
    "QF_UF",
    "QF_BV",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_NIA",
    "QF_NRA",
    "QF_AUFLIA",
    "QF_AUFBV",
    "QF_ABV",
    "QF_UFBV",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "UFNIA",
    "UFLRA",
    "LRA",
    "NRA",
    "LIA",
    "UFBV",
    "BV",
    "QF_FP",
    "QF_FPBV",
    "QF_BVFP",
    "HORN",
    "QF_FD",
    "SAT",
]


def get_assertion_line_mapping(smt2_file: str):
    """Parse SMT2 file and return a list of (start_line, end_line, assertion_text)."""
    assertion_ranges = []
    lines = smt2_file.split("\n")
    line_starts = [0]  # Character position where each line starts
    for i, line in enumerate(lines):
        line_starts.append(line_starts[-1] + len(line) + 1)  # +1 for newline

    def char_pos_to_line(pos):
        """Convert character position to line number (1-indexed)"""
        for i, start in enumerate(line_starts):
            if pos < start:
                return i  # i is already 1-indexed because line_starts[0] = 0
        return len(lines)

    # Find all (assert ...) in the file
    i = 0
    while i < len(smt2_file):
        # Skip whitespace and comments
        if smt2_file[i].isspace():
            i += 1
            continue
        if smt2_file[i] == ";":
            while i < len(smt2_file) and smt2_file[i] != "\n":
                i += 1
            continue

        # Check for (assert
        if smt2_file[i] == "(":
            start_pos = i

            # Skip whitespace after '('
            j = i + 1
            while j < len(smt2_file) and smt2_file[j].isspace():
                j += 1

            if smt2_file[j : j + 6].lower() != "assert":
                i += 1
                continue

            start_line = char_pos_to_line(start_pos)

            # Count parentheses to find the end
            paren_count = 0
            j = i
            while j < len(smt2_file):
                if smt2_file[j] == "(":
                    paren_count += 1
                elif smt2_file[j] == ")":
                    paren_count -= 1
                    if paren_count == 0:
                        end_pos = j + 1
                        end_line = char_pos_to_line(end_pos - 1)

                        # Extract and normalize
                        assertion_text = smt2_file[start_pos:end_pos]
                        assertion_ranges.append((start_line, end_line, assertion_text))

                        i = end_pos
                        break
                j += 1
            continue

        i += 1

    return assertion_ranges


def unsat_core(
    slvr: Solver, assertions: list[ExprRef], smt2_file: str = None, logic: str = None
):
    if logic and logic in Z3_SUPPORTED_LOGICS:
        solver = SolverFor(logic, ctx=slvr.ctx)
    else:
        solver = Solver(ctx=slvr.ctx)
    solver.set(unsat_core=True)
    solver.set("core.minimize", True)

    # Get line number mapping if file provided
    parsed_assertions = []
    if smt2_file:
        raw_assertions = get_assertion_line_mapping(smt2_file)
        sorts_env, decls_env = get_decls_and_sorts(assertions)

        for start_line, end_line, assertion_text in raw_assertions:
            try:
                parsed = parse_smt2_string(
                    assertion_text,
                    sorts=sorts_env,
                    decls=decls_env,
                    ctx=slvr.ctx,
                )
                if parsed:
                    parsed_assertions.append((start_line, end_line, parsed[-1]))
            except Z3Exception:
                continue

    rs = [
        Bool("nobodyWillEverChooseThisVariableName" + str(i))
        for i in range(len(assertions))
    ]
    non_red_constraints = []
    red_constraints = []
    elementToAssertion = {}
    for i, assertion in enumerate(assertions):
        non_red_constraints.append(Implies(rs[i], assertion))
        red_constraints.append(Or(rs[i], assertion))
        elementToAssertion[rs[i]] = assertion

    non_red_constraints = And(non_red_constraints)
    red_constraints = And(red_constraints)
    redundancy = Implies(non_red_constraints, red_constraints)
    solver.add(Not(redundancy))

    trackerToElement = {}
    for i, assertion in enumerate(assertions):
        tracker = Bool("nobodyWillEverChooseThisTrackerName" + str(i))
        trackerToElement[tracker] = rs[i]
        solver.assert_and_track(trackerToElement[tracker], tracker)

    redundant_lines = set()

    if solver.check() == unsat:
        c = solver.unsat_core()
        c = [trackerToElement[tracker] for tracker in c]
        e = [elementToAssertion[element] for element in c]
    cleanedSolver = SolverFor(logic) if logic else Solver()
    cleanedSolver.add(e)

    for a in assertions:
        if a not in e:
            sexpr = a.sexpr()
            # Try to find line number
            line_range = None
            if smt2_file:
                for start, end, parsed_assertion in parsed_assertions:
                    if eq(a, parsed_assertion):
                        line_range = (start, end)
                        break

            if line_range:
                for line_num in range(line_range[0], line_range[1] + 1):
                    redundant_lines.add(line_num)
        else:
            e.remove(a)

    return redundant_lines