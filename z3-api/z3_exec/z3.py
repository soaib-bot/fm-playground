import concurrent.futures
import multiprocessing
import os
import queue
import re
import subprocess
import tempfile
from z3 import *
from utils.logics_filter import Z3_SUPPORTED_LOGICS
from utils.helper import (
    prettify_error,
    get_logic_from_smt2,
    prettify_warning,
    get_all_vars,
)
from utils.z3_cache_manager import cache_manager

from smt_redundancy.redundancy import unsat_core

MAX_CONCURRENT_REQUESTS = 10
TIMEOUT = 30  # seconds

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


def run_z3(code: str) -> str:
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".smt2")
    tmp_file.write(code.strip())
    tmp_file.close()
    command = ["z3", "-smt2", tmp_file.name]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        os.remove(tmp_file.name)
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Process timed out after {} seconds".format(10)


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


def _check_redundancy_worker(result_queue, code: str):
    """Worker function to run redundancy check in a separate process"""
    try:
        logic = get_logic_from_smt2(code)
        solver = SolverFor(logic) if logic else Solver()
        solver.from_string(code)
        redundant_lines = list(unsat_core(solver, solver.assertions(), smt2_file=code))
        result_queue.put(("", redundant_lines))
    except Exception as e:
        result_queue.put((str(e), []))


def _run_z3_with_redundancy_worker(result_queue, code: str):
    """Worker function to run Z3 with redundancy detection in a separate process"""
    try:
        res = run_z3(code)
        logic = get_logic_from_smt2(code)
        if not at_least_one_sat(res):
            result_queue.put((res, []))
            return

        solver = SolverFor(logic) if logic else Solver()
        solver.from_string(code)
        redundant_lines = list(unsat_core(solver, solver.assertions(), smt2_file=code))
        result_queue.put((res, redundant_lines))
    except Exception as e:
        result_queue.put((str(e), []))


def run_with_timeout(worker_func, code: str, timeout=TIMEOUT):
    """Run a worker function with timeout using multiprocessing."""
    result_queue = multiprocessing.Queue()
    process = multiprocessing.Process(target=worker_func, args=(result_queue, code))
    process.start()
    process.join(timeout)

    if process.is_alive():
        # Process timed out
        process.terminate()
        process.join()
        return f"Process timed out after {timeout} seconds", []

    # Get result from queue
    if not result_queue.empty():
        return result_queue.get()
    else:
        return "No result returned", []


def check_redundancy_only(code: str):
    """Check redundancy with timeout protection using multiprocessing"""
    return run_with_timeout(_check_redundancy_worker, code, timeout=TIMEOUT)


def process_commands(code: str, check_redundancy: bool = False):
    code_queue.put(code)
    while True:
        code_command = code_queue.get()
        if code_command is None:
            break
        if check_redundancy:
            # Submit to thread pool for concurrent handling
            # Each thread will internally use multiprocessing with timeout
            ex = executor.submit(check_redundancy_only, code_command)
        else:
            # For now we always check redundancy
            # Submit to thread pool for concurrent handling
            ex = executor.submit(
                run_with_timeout, _run_z3_with_redundancy_worker, code_command, TIMEOUT
            )
        return ex.result()
