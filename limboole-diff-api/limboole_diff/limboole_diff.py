import re
from typing import Any
from .limboole_executor import process_commands
from .cache_manager import cache_manager


def get_sat_unsat(output: str):
    if output.startswith("% SATISFIABLE"):
        return "sat"
    elif output.startswith("% UNSATISFIABLE"):
        return "unsat"
    return "unknown"

def sanitize_formula(formula: str) -> str:
    lines = formula.splitlines()
    sanitized_lines = [line.split("%")[0] for line in lines if line.strip()]
    sanitize_formula = " ".join(sanitized_lines)
    sanitize_formula = re.sub(r'\s+', ' ', sanitize_formula).strip()
    return sanitize_formula


def diff_witness(f1: str, f2: str):
    f1_not_f2 = f"({f1}) & (!({f2}))"
    return f1_not_f2,  process_commands(f1_not_f2)


def common_witness(f1: str, f2: str):
    conjuncted = f"({f1}) & ({f2})"
    return conjuncted, process_commands(conjuncted)


def semantic_relation(f1: str, f2: str):
    """Determine the semantic relation between two formulas f1 and f2.
    f1: current formula
    f2: previous formula
    """
    f1 = sanitize_formula(f1)
    f2 = sanitize_formula(f2)
    f1_not_f2 = process_commands(f"({f1}) & (!({f2}))")
    not_f1_but_f2 = process_commands(f"(!({f1})) & ({f2})")
    res_f1_not_f2 = get_sat_unsat(f1_not_f2)
    res_not_f1_but_f2 = get_sat_unsat(not_f1_but_f2)

    if res_f1_not_f2 == "unknown" or res_not_f1_but_f2 == "unknown":
        return "Error in the formula"

    if res_f1_not_f2 == "unsat" and res_not_f1_but_f2 == "unsat":
        return "Current ≡ Previous\nAll valuations that satisfy the current formula also satisfy the previous formula, and vice versa."
    elif res_f1_not_f2 == "sat" and res_not_f1_but_f2 == "unsat":
        return "Previous ⊨ Current\nAll valuations that satisfy the previous formula also satisfy the current formula. Some valuations that satisfy the current formula do not satisfy the previous formula."
    elif res_f1_not_f2 == "unsat" and res_not_f1_but_f2 == "sat":
        return "Current ⊨ Previous\nAll valuations that satisfy the current formula also satisfy the previous formula. Some valuations that satisfy the previous formula do not satisfy the current formula."
    elif res_f1_not_f2 == "sat" and res_not_f1_but_f2 == "sat":
        return "The formulas are incomparable\nThere exist valuations that satisfy the current formula but not the previous formula, and vice versa."
    else:
        return None


def get_formula_from_valuation(valuation: str) -> str:
    lines = valuation.strip().splitlines()
    assignments = []
    for line in lines:
        line = line.strip()
        if line and not line.startswith("%"):
            if line.endswith("= 1"):
                assignments.append(line.replace("= 1", "").strip())
            elif line.endswith("= 0"):
                assignments.append(f"!{line.replace('= 0', '').strip()}")
    formula = " & ".join(assignments)
    formula = f"({formula})"
    return formula


def store_witness(f1: str, f2: str, mode: str):
    f1 = sanitize_formula(f1)
    f2 = sanitize_formula(f2)
    if mode == "diff":
        formula, res = diff_witness(f1, f2)
    elif mode == "common":
        formula, res = common_witness(f1, f2)

    if res:
        valuation_formula = get_formula_from_valuation(res)
        store_formula = f"({formula}) & (!{valuation_formula})"
        specId = cache_manager.create_cache(store_formula, ttl_seconds=3600)
        if specId:
            return specId, res
    return None, None


def get_next_witness(specId: str):
    witness = cache_manager.get_value(specId)
    res = process_commands(witness)
    if res.startswith("% UNSATISFIABLE"):
        return None
    valuation = get_formula_from_valuation(res)
    if witness:
        new_witness = witness.rstrip(")") + f") & !{valuation})"
        cache_manager.update_cache(specId, new_witness)
        return res
    return None

def evaluate_formula(specId: str, formula: str) -> Any:
    formula = sanitize_formula(formula)
    cache_info = cache_manager.get_cache_info(specId)
    if cache_info is None:
        return None
    stored_formula = cache_manager.get_value(specId)
    if stored_formula is None:
        return None
    conjuncted_formula = re.sub(r'\(', f'({formula} & ', stored_formula, count=1)
    # TODO: Should we update the cache with the new conjuncted formula?
    return process_commands(conjuncted_formula)


def get_cache_info(specId: str):
    return cache_manager.get_cache_info(specId)


def delete_cache(specId: str) -> bool:
    return cache_manager.delete_cache(specId)

