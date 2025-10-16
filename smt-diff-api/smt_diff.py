import concurrent.futures
import os
import queue
import re
import subprocess
import tempfile
from z3 import *
from generator_cache_manager import cache_manager
from typing import List, Optional, Dict, Any

TTL_SECONDS = 3600  # Default cache TTL in seconds


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
        if is_const(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED:
            vars_set.add(expr)
        for child in expr.children():
            collect_vars(child, vars_set)
        return vars_set

    for assertion in assertions:
        all_vars |= collect_vars(assertion)
    return all_vars


def diff_witness(assertions1, assertions2):
    solver_s1_not_s2 = Solver()
    solver_s1_not_s2.add(And(assertions1), And(Not(And(assertions2))))
    if solver_s1_not_s2.check() == sat:
        vars_s1 = get_all_vars(assertions1)
        vars_s2 = get_all_vars(assertions2)
        vars_for_enum = list(vars_s1.intersection(vars_s2))

        # If no common variables, use union instead
        if len(vars_for_enum) == 0:
            vars_for_enum = list(vars_s1.union(vars_s2))

        generator = all_smt(solver_s1_not_s2, vars_for_enum)
        return generator

    return None


def common_witness(assertions1, assertions2):
    combined_solver = Solver()
    combined_solver.add(assertions1)
    combined_solver.add(assertions2)
    if combined_solver.check() == sat:
        s1_vars = get_all_vars(assertions1)
        s2_vars = get_all_vars(assertions2)
        all_vars = list(s1_vars.intersection(s2_vars))
        # If no common variables, use union instead
        if len(all_vars) == 0:
            all_vars = list(s1_vars.union(s2_vars))
        generator = all_smt(combined_solver, all_vars)
        return generator
    return None


def get_next_witness(specId: str) -> Optional[str]:
    model = cache_manager.get_next(specId)
    if model is None:
        return None
    return model.sexpr()


def store_witness(s1: str, s2: str, mode: str):
    assertions1 = parse_smt2_string(s1)
    assertions2 = parse_smt2_string(s2)

    if mode == "diff":
        generator = diff_witness(assertions1, assertions2)
    elif mode == "common":
        generator = common_witness(assertions1, assertions2)

    if generator:
        specId = cache_manager.create_cache(generator, TTL_SECONDS)
        if specId:
            return specId
    return None


def get_cache_info(specId: str):
    return cache_manager.get_cache_info(specId)


def delete_cache(specId: str) -> bool:
    return cache_manager.delete_cache(specId)


def list_all_caches() -> List[Dict[str, Any]]:
    return cache_manager.list_caches()
