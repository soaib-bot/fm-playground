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


def get_decls_and_sorts(assertions):
    """Collect Z3 declarations and sorts required to re-parse individual assertions."""

    decls: dict[str, FuncDeclRef] = {}
    sorts: dict[str, SortRef] = {}

    seen_decl: set[FuncDeclRef] = set()
    seen_sort: set[SortRef] = set()

    array_sort_kind = globals().get("Z3_ARRAY_SORT")
    set_sort_kind = globals().get("Z3_SET_SORT")
    seq_sort_kind = globals().get("Z3_SEQ_SORT")
    relation_sort_kind = globals().get("Z3_RELATION_SORT")

    def register_sort(sort: SortRef):
        if sort is None or sort in seen_sort:
            return
        seen_sort.add(sort)

        kind = sort.kind()

        if kind in (Z3_UNINTERPRETED_SORT, Z3_DATATYPE_SORT, Z3_FINITE_DOMAIN_SORT):
            sorts[str(sort)] = sort

        if array_sort_kind is not None and kind == array_sort_kind:
            register_sort(sort.domain())
            register_sort(sort.range())
        elif set_sort_kind is not None and kind == set_sort_kind:
            register_sort(sort.domain())
        elif seq_sort_kind is not None and kind == seq_sort_kind:
            register_sort(sort.basis())
        elif relation_sort_kind is not None and kind == relation_sort_kind:
            # Relations expose arity/domain via domain(i)
            for i in range(getattr(sort, "arity", lambda: 0)()):
                register_sort(sort.domain(i))

    def register_decl(decl: FuncDeclRef):
        if decl is None or decl in seen_decl:
            return

        kind = decl.kind()

        if kind == Z3_OP_UNINTERPRETED:
            seen_decl.add(decl)
            name = str(decl.name())
            if decl.arity() == 0:
                try:
                    decls[name] = decl()
                except Z3Exception:
                    decls[name] = decl
            else:
                decls[name] = decl

            register_sort(decl.range())
            for i in range(decl.arity()):
                register_sort(decl.domain(i))

    def walk(expr: ExprRef):
        if is_quantifier(expr):
            for i in range(expr.num_vars()):
                register_sort(expr.var_sort(i))
            walk(expr.body())
            return

        if not is_app(expr):
            return

        register_decl(expr.decl())
        for child in expr.children():
            walk(child)

    for assertion in assertions:
        walk(assertion)

    return sorts, decls


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
