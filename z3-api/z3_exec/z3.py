import concurrent.futures
import multiprocessing
import os
import queue
import re
import subprocess
import tempfile
from typing import Any, Dict, List

from smt_redundancy.redundancy import unsat_core
from utils.helper import (
    get_all_vars,
    get_logic_from_smt2,
    prettify_error,
    prettify_warning,
)
from utils.logics_filter import Z3_SUPPORTED_LOGICS
from utils.z3_cache_manager import cache_manager
from z3 import *

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


def run_z3_with_cache(spec: str):
    z3_result = ""
    try:
        z3_result = run_z3(spec)
    except Exception as e:
        z3_result = prettify_error(e.args[0].decode())
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
        return specId, z3_result
    logic = get_logic_from_smt2(spec)
    if logic is None or logic not in Z3_SUPPORTED_LOGICS:
        logic_msg = prettify_warning(
            "; No logic specified or unsupported logic, using default solver settings."
        )
        z3_result = logic_msg + "\n" + z3_result

    solver = SolverFor(logic) if logic else Solver()
    solver.add(assertions)
    if solver.check() == sat:
        all_vars = list(get_all_vars(assertions))
        generator = all_smt(solver, all_vars)
        if generator:
            specId = cache_manager.create_cache(
                cached_value=generator,
                logic=logic_msg if "logic_msg" in locals() else logic,
                ttl_seconds=3600,
            )
        return specId, z3_result
    return None, z3_result


def get_next_model(specId: str):
    model = cache_manager.get_next(specId)
    logic = (
        cache_manager.caches[specId].logic if specId in cache_manager.caches else None
    )
    if isinstance(model, str):
        return model
    model = model.sexpr()
    return logic + "\n" + model


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
        # Just run z3 and check redundancy in the worker process
        # Don't create cache here since it won't be accessible in parent process
        z3_result = run_z3(code)
        logic = get_logic_from_smt2(code)

        if not at_least_one_sat(z3_result):
            result_queue.put((z3_result, []))
            return

        solver = SolverFor(logic) if logic else Solver()
        solver.from_string(code)
        redundant_lines = list(unsat_core(solver, solver.assertions(), smt2_file=code))
        result_queue.put((z3_result, redundant_lines))
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


def get_cache_info(specId: str):
    return cache_manager.get_cache_info(specId)


def delete_cache(specId: str) -> bool:
    return cache_manager.delete_cache(specId)


def list_all_caches() -> List[Dict[str, Any]]:
    return cache_manager.list_caches()


def process_commands(code: str):
    """Process Z3 commands with timeout and create cache in parent process"""
    code_queue.put(code)
    while True:
        code_command = code_queue.get()
        if code_command is None:
            break

        # Run z3 with redundancy check in separate process (for timeout protection)
        ex = executor.submit(
            run_with_timeout, _run_z3_with_redundancy_worker, code_command, TIMEOUT
        )
        result = ex.result()

        # result is either (z3_result, redundant_lines) or error message
        if len(result) == 2:
            z3_result, redundant_lines = result

            # Now create the cache in the parent process
            try:
                assertions = parse_smt2_string(code_command)
                logic = get_logic_from_smt2(code_command)

                if logic is None or logic not in Z3_SUPPORTED_LOGICS:
                    logic_msg = prettify_warning(
                        "; No logic specified or unsupported logic, using default solver settings."
                    )
                    if not z3_result.startswith(logic_msg):
                        z3_result = logic_msg + "\n" + z3_result

                solver = SolverFor(logic) if logic else Solver()
                solver.add(assertions)

                specId = None
                if solver.check() == sat:
                    all_vars = list(get_all_vars(assertions))
                    generator = all_smt(solver, all_vars)
                    if generator:
                        specId = cache_manager.create_cache(
                            cached_value=generator,
                            logic=logic_msg if "logic_msg" in locals() else logic,
                            ttl_seconds=3600,
                        )

                return specId, z3_result, redundant_lines
            except Exception as e:
                # If cache creation fails, still return the results
                return None, z3_result, redundant_lines
        else:
            # Error case
            return None, result[0] if result else "Unknown error", []
