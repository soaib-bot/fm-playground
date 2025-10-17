from .limboole_executor import process_commands


def get_sat_unsat(output: str):
    if output.startswith("% SATISFIABLE"):
        return "sat"
    elif output.startswith("% UNSATISFIABLE"):
        return "unsat"
    return "unknown"


def process_diff_witness_output(output: str):
    return output.replace(
        "% SATISFIABLE formula (satisfying assignment follows)", ""
    ).strip()


def diff_witness(f1: str, f2: str):
    f1_not_f2 = f"({f1}) & (!({f2}))"
    output = process_commands(f1_not_f2)
    return process_diff_witness_output(output)


def common_witness(f1: str, f2: str):
    conjuncted = f"({f1}) & ({f2})"
    return process_commands(conjuncted)


def semantic_relation(f1: str, f2: str):
    """Determine the semantic relation between two formulas f1 and f2.
    f1: current formula
    f2: previous formula
    """
    f1_not_f2 = process_commands(f"({f1}) & (!({f2}))")
    not_f1_but_f2 = process_commands(f"(!({f1})) & ({f2})")
    res_f1_not_f2 = get_sat_unsat(f1_not_f2)
    res_not_f1_but_f2 = get_sat_unsat(not_f1_but_f2)

    if res_f1_not_f2 == "unknown" or res_not_f1_but_f2 == "unknown":
        return "Error in the formula"

    if res_f1_not_f2 == "unsat" and res_not_f1_but_f2 == "unsat":
        return "The formulas are equivalent."
    elif res_f1_not_f2 == "sat" and res_not_f1_but_f2 == "unsat":
        return "Previous ⊨ Current"
    elif res_f1_not_f2 == "unsat" and res_not_f1_but_f2 == "sat":
        return "Current ⊨ Previous"
    elif res_f1_not_f2 == "sat" and res_not_f1_but_f2 == "sat":
        return "The formulas are incomparable."
    else:
        return None
