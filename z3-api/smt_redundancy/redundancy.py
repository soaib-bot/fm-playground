from z3 import *
from .explain_redundancy import find_assertion_line_ranges

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


def _normalize_sexpr(expr: str) -> str:
    return " ".join(expr.split())


def get_assertion_line_mapping(smt2_file: str):
    """Parse SMT2 script and map each assertion sexpr to its line span."""
    try:
        assertion_ranges = find_assertion_line_ranges(smt2_file)
    except ValueError:
        return {}

    line_mapping: dict[str, list[tuple[int, int]]] = {}

    for start_line, end_line, _, _, ast_ref in assertion_ranges:
        normalized = _normalize_sexpr(ast_ref.sexpr())
        line_mapping.setdefault(normalized, []).append((start_line, end_line))

    return line_mapping


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
    line_mapping: dict[str, list[tuple[int, int]]] = {}
    if smt2_file:
        line_mapping = get_assertion_line_mapping(smt2_file)

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
            line_ranges: list[tuple[int, int]] = []
            if smt2_file:
                normalized_sexpr = _normalize_sexpr(sexpr)
                line_ranges = line_mapping.get(normalized_sexpr, [])

            for start, end in line_ranges:
                for line_num in range(start, end + 1):
                    redundant_lines.add(line_num)
        else:
            e.remove(a)

    return redundant_lines
