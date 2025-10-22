from typing import Any, Dict, List, Optional

from generator_cache_manager import cache_manager
from logics_filter import common_logic
from z3 import *
import sexpdata

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


def get_logic_from_smt2(spec: str):
    lines = spec.splitlines()
    for line in lines:
        line = line.strip()
        if line.startswith("(set-logic"):
            return line.split()[1].rstrip(")")
    return None


def get_all_vars(assertions):
    all_vars = set()

    def collect_vars(expr, vars_set=None):
        if vars_set is None:
            vars_set = set()
        # Collect uninterpreted constants
        if is_const(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED:
            vars_set.add(expr)
        # Collect uninterpreted functions (extract function declaration from applications)
        elif is_app(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED and expr.num_args() > 0:
            # Add the function declaration (not the application)
            vars_set.add(expr.decl())
        for child in expr.children():
            collect_vars(child, vars_set)
        return vars_set

    for assertion in assertions:
        all_vars |= collect_vars(assertion)
    return all_vars

def prettify_result(s1: AstVector, s2: AstVector, model: str):
    vars_s1 = set(get_all_vars(s1))
    vars_s2 = set(get_all_vars(s2))
    common_vars = vars_s1.intersection(vars_s2)
    previous_vars = vars_s1 - common_vars
    current_vars = vars_s2 - common_vars
    
    # Split the model 
    result = []
    i = 0
    current_text = ""
    
    while i < len(model):
        # Check if we're starting a define-fun expression
        if model[i:].lstrip().startswith("(define-fun"):
            # Add any accumulated text before this define-fun
            if current_text:
                result.append(current_text)
                current_text = ""
            
            # Find the start of the define-fun expression (skip leading whitespace)
            leading_whitespace = ""
            while i < len(model) and model[i] in ' \t\n':
                leading_whitespace += model[i]
                i += 1
            
            # We found the start of a define-fun
            # Parse the S-expression starting from here
            paren_count = 0
            expr_str = ""
            
            # Count parentheses to find the complete expression
            while i < len(model):
                char = model[i]
                expr_str += char
                if char == '(':
                    paren_count += 1
                elif char == ')':
                    paren_count -= 1
                    if paren_count == 0:
                        i += 1
                        break
                i += 1
            
            # Extract the variable name from the define-fun expression
            # Format: (define-fun <name> ...)
            try:
                parsed = sexpdata.loads(expr_str)
                if len(parsed) >= 2:
                    var_name = str(parsed[1])
                    
                    # Determine the color based on variable set membership
                    color = ""  # default
                    if var_name in [str(v) for v in common_vars]:
                        color = ""
                    elif var_name in [str(v) for v in previous_vars]:
                        color = "red"
                    elif var_name in [str(v) for v in current_vars]:
                        color = "green"
                    
                    # Wrap in span with appropriate color
                    wrapped = f"{leading_whitespace}<span style='color: {color};'>{expr_str}</span>"
                    result.append(wrapped)
                else:
                    # If parsing fails, just add the expression as-is
                    result.append(leading_whitespace + expr_str)
            except:
                # If parsing fails, just add the expression as-is
                result.append(leading_whitespace + expr_str)
        else:
            # Not a define-fun, accumulate the character
            current_text += model[i]
            i += 1
    
    # Append any remaining text
    if current_text:
        result.append(current_text)
    
    return "".join(result)

def diff_witness(assertions1, assertions2, logic1=None, logic2=None):
    logic = common_logic(logic1, logic2)
    solver_s1_not_s2 = SolverFor(logic) if logic else Solver()
    solver_s1_not_s2.add(And(assertions1), And(Not(And(assertions2))))
    if solver_s1_not_s2.check() == sat:
        vars_s1 = get_all_vars(assertions1)
        vars_s2 = get_all_vars(assertions2)
        vars_for_enum = list(vars_s1.intersection(vars_s2))

        # FIXME: If no common variables, use union instead
        if len(vars_for_enum) == 0:
            vars_for_enum = list(vars_s1.union(vars_s2))

        generator = all_smt(solver_s1_not_s2, vars_for_enum)
        return generator

    return None


def common_witness(assertions1, assertions2, logic1=None, logic2=None):
    logic = common_logic(logic1, logic2)
    combined_solver = SolverFor(logic) if logic else Solver()
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


def get_semantic_relation(s1: str, s2: str) -> Optional[str]:
    """
    s1: current spec
    s2: previous spec
    """
    spec_1 = parse_smt2_string(s1)
    spec_2 = parse_smt2_string(s2)
    logic1 = get_logic_from_smt2(s1)
    logic2 = get_logic_from_smt2(s2)

    cm_logic = common_logic(logic1, logic2)
    s1_not_s2_solver = SolverFor(cm_logic) if cm_logic else Solver()
    s1_not_s2_solver.add(spec_1)
    s1_not_s2_solver.add(Not(And(spec_2)))
    res_s1_not_s2 = s1_not_s2_solver.check()

    s2_not_s1_solver = SolverFor(cm_logic) if cm_logic else Solver()
    s2_not_s1_solver.add(spec_2)
    s2_not_s1_solver.add(Not(And(spec_1)))
    res_s2_not_s1 = s2_not_s1_solver.check()

    if res_s1_not_s2 == unsat and res_s2_not_s1 == unsat:
        return "Current ≡ Previous\nAll models that satisfy the current script also satisfy the previous script, and vice versa."
    elif res_s1_not_s2 == sat and res_s2_not_s1 == sat:
        return "Scripts are incomparable\nThere exist models that satisfy the current script but not the previous script, and vice versa."
    elif res_s1_not_s2 == unsat and res_s2_not_s1 == sat:
        return "Current ⊨ Previous \nAll models that satisfy the current script also satisfy the previous script. Some models that satisfy the previous script do not satisfy the current script."
    elif res_s1_not_s2 == sat and res_s2_not_s1 == unsat:
        return "Previous ⊨ Current\nAll models that satisfy the previous script also satisfy the current script. Some models that satisfy the current script do not satisfy the previous script."
    else:
        return "unknown"


def get_next_witness(specId: str) -> Optional[str]:
    model = cache_manager.get_next(specId)
    if model is None:
        return None
    model = model.sexpr()
    previous = cache_manager.caches[specId].previous
    current = cache_manager.caches[specId].current
    if previous is None or current is None:
        return model
    print(previous, current, model)
    res = prettify_result(previous, current, model)
    return res


def store_witness(s1: str, s2: str, analysis: str):
    """
    s1: previous spec
    s2: current spec
    """
    assertions1 = parse_smt2_string(s1)
    assertions2 = parse_smt2_string(s2)
    logic1 = get_logic_from_smt2(s1)
    logic2 = get_logic_from_smt2(s2)
    if analysis == "not-previous-but-current":
        generator = diff_witness(assertions2, assertions1, logic2, logic1)
    elif analysis == "not-current-but-previous":
        generator = diff_witness(assertions1, assertions2, logic1, logic2)
    elif analysis == "common-witness":
        generator = common_witness(assertions1, assertions2, logic1, logic2)

    if generator:
        specId = cache_manager.create_cache(generator, previous=assertions1, current=assertions2, ttl_seconds=TTL_SECONDS)
        if specId:
            return specId
    return None


def get_cache_info(specId: str):
    return cache_manager.get_cache_info(specId)


def delete_cache(specId: str) -> bool:
    return cache_manager.delete_cache(specId)


def list_all_caches() -> List[Dict[str, Any]]:
    return cache_manager.list_caches()
