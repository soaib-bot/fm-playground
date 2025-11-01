import re

from utils.logics_filter import Z3_SUPPORTED_LOGICS
from z3 import *


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


def get_logic_from_smt2(spec: str):
    set_logic_pattern = re.compile(r"\(\s*set-logic\s+", re.IGNORECASE)
    lines = spec.splitlines()
    for line in lines:
        line = line.strip()
        if set_logic_pattern.match(line):
            logic = line.split()[1].rstrip(")")
            if logic in Z3_SUPPORTED_LOGICS:
                return logic
    return None


def prettify_error(error_msg):
    error_msg = str(error_msg).strip()
    error_msg = error_msg.replace("\\n", "<br/>")
    error_msg = error_msg.replace("\n", "<br/>")

    return f"<span style='color: red;'>{error_msg}</span>"


def prettify_warning(warning_msg: str):
    return f"<span style='color: orange;'>{warning_msg.strip()}</span>"
