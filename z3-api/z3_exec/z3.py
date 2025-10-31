import concurrent.futures
import os
import queue
import re
import subprocess
import tempfile
from z3 import *
from utils.logics_filter import Z3_SUPPORTED_LOGICS
from utils.helper import prettify_error, get_logic_from_smt2, prettify_warning
from utils.z3_cache_manager import cache_manager

from smt_redundancy.redundancy import unsat_core

MAX_CONCURRENT_REQUESTS = 10
executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_CONCURRENT_REQUESTS)
code_queue = queue.Queue()


def all_smt(s: Solver, vars: list):
    def block_term(s, m, t):
        s.add(t != m.eval(t, model_completion=True))

    def fix_term(s, m, t):
        s.add(t == m.eval(t, model_completion=True))

    def all_smt_rec(terms):
        if sat == s.check():
            m = s.model()
            yield m
            for i in range(len(terms)):
                s.push()
                block_term(s, m, terms[i])
                for j in range(i):
                    fix_term(s, m, terms[j])
                yield from all_smt_rec(terms[i:])
                s.pop()

    yield from all_smt_rec(list(vars))


def get_all_vars(assertions):
    all_vars = set()

    def collect_vars(expr, vars_set=None):
        if vars_set is None:
            vars_set = set()
        # Collect uninterpreted constants
        if is_const(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED:
            vars_set.add(expr)
        # Collect uninterpreted functions (extract function declaration from applications)
        elif (
            is_app(expr)
            and expr.decl().kind() == Z3_OP_UNINTERPRETED
            and expr.num_args() > 0
        ):
            # Add the function declaration (not the application)
            vars_set.add(expr.decl())
        for child in expr.children():
            collect_vars(child, vars_set)
        return vars_set

    for assertion in assertions:
        all_vars |= collect_vars(assertion)
    return all_vars


def get_next_model(specId: str):
    model = cache_manager.get_next(specId)
    logic = (
        cache_manager.caches[specId].logic if specId in cache_manager.caches else None
    )
    if isinstance(model, str):
        return model
    model = model.sexpr()
    return logic + "\n" + model


def run_z3_with_cache(spec: str) -> str:
    error_msg = None
    try:
        assertions = parse_smt2_string(spec)
    except Z3Exception as e:
        error_msg = prettify_error(e.args[0].decode())

    if error_msg:
        specId = cache_manager.create_cache(
            cached_value=error_msg,
            logic="",
            ttl_seconds=3600,
        )
        return specId
    logic = get_logic_from_smt2(spec)
    if logic is None or logic not in Z3_SUPPORTED_LOGICS:
        logic = prettify_warning(
            "; No logic specified or unsupported logic, using default solver settings."
        )

    solver = SolverFor(logic) if logic else Solver()
    solver.add(assertions)
    check_sat_result = solver.check()
    if check_sat_result == sat:
        redundant_lines = list(
            unsat_core(solver, solver.assertions(), smt2_file=spec, logic=logic)
        )
    all_vars = list(get_all_vars(assertions))
    generator = all_smt(solver, all_vars)
    if generator:
        specId = cache_manager.create_cache(
            cached_value=generator,
            logic=logic,
            ttl_seconds=3600,
        )
    return specId, redundant_lines if check_sat_result == sat else []


def run_z3(code: str) -> str:
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".smt2")
    tmp_file.write(code.strip())
    tmp_file.close()
    command = ["z3", "-smt2", tmp_file.name]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        os.remove(tmp_file.name)
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Process timed out after {} seconds".format(5)


def at_least_one_sat(model: str) -> bool:
    """
    Check if any line in the model contains 'sat'.
    Returns 'sat' if found, otherwise 'unsat'.
    """
    lines = model.split("\n")
    for line in lines:
        if "sat" in line.lower():
            return True
    return False


def run_z3_with_redundancy_detection(code: str):
    res = run_z3(code)
    logic = get_logic_from_smt2(code)
    if not at_least_one_sat(res):
        return res, []
    try:
        solver = SolverFor(logic) if logic else Solver()
        solver.from_string(code)
    except Exception:
        return res, []
    redundant_lines = list(unsat_core(solver, solver.assertions(), smt2_file=code))
    return res, redundant_lines


def check_redundancy_only(code: str):
    logic = get_logic_from_smt2(code)
    solver = SolverFor(logic) if logic else Solver()
    try:
        solver.from_string(code)
    except Exception as e:
        return str(e), []
    redundant_lines = unsat_core(solver, solver.assertions(), smt2_file=code)
    return "", redundant_lines


def process_commands(code: str, check_redundancy: bool = False):
    code_queue.put(code)
    while True:
        code_command = code_queue.get()
        if code_queue is None:
            break
        if check_redundancy:
            ex = executor.submit(check_redundancy_only, code_command)
        else:
            # For now we always check redundancy
            ex = executor.submit(run_z3_with_redundancy_detection, code_command)
        return ex.result()
