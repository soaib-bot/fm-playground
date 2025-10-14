# use z3 to parse an smt file
import os
import ast
import subprocess
from z3 import *

TIMEOUT = 60


def check_z3_smt2(spec: str) -> str:
    """
    Run the Z3 solver on the given SMT-LIB specification and return the result.

    """
    try:
        proc = subprocess.Popen(
            ["z3", "-in"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        stdout, stderr = proc.communicate(input=spec, timeout=TIMEOUT)

        return stdout.strip()
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        return "TO"
    except Exception as e:
        return f"ERROR: {e}"


def check_semantic_comparison(spec_1: str, spec_2: str):
    """
    Compare two SMT-LIB specifications using Z3 and return the result.
    The comparison is based on the satisfiability of the negation of the conjunction of the two specifications.
        if both are unsat then they are equivalent
        if both are sat then they are incomparable
        if one is sat and the other is unsat then we have a refinement relation

        the check is very naive and ignores issues like renaming of variables
        it also ignores structures like push and pop and only takes the final list of assertions into account
        it requires some detailed analysis when some spec is unsat to begin with
    Args:
        spec_1 (str): Path to the first SMT-LIB specification.
        spec_2 (str): Path to the second SMT-LIB specification.
    Returns:
        str: "equivalent", "incomparable", "s1_refines_s2", "s2_refines_s1","unknown", or error message.

    """
    removes = ["(get-assignment)"]
    try:
        # Read and parse SMT2 files safely
        with open(spec_1, "r", encoding="utf-8") as f1:
            smt1 = f1.read()
        for remove in removes:
            smt1 = smt1.replace(remove, "")
        with open(spec_2, "r", encoding="utf-8") as f2:
            smt2 = f2.read()
        for remove in removes:
            smt2 = smt2.replace(remove, "")

        a1 = parse_smt2_string(smt1)
        a2 = parse_smt2_string(smt2)

        s1not2 = Solver()
        s1not2.add(a1)
        s1not2.add(Not(And(a2)))
        res_s1not2 = check_z3_smt2(s1not2.to_smt2())

        s2not1 = Solver()
        s2not1.add(a2)
        s2not1.add(Not(And(a1)))
        res_s2not1 = check_z3_smt2(s2not1.to_smt2())

        if res_s1not2 == "unsat" and res_s2not1 == "unsat":
            return "equivalent"
        elif res_s1not2 == "sat" and res_s2not1 == "sat":
            return "incomparable"
        elif res_s1not2 == "unsat" and res_s2not1 == "sat":
            return "s1_refines_s2"
        elif res_s1not2 == "sat" and res_s2not1 == "unsat":
            return "s2_refines_s1"
        else:
            return "unknown"
    except OSError as e:
        print(f"Error comparing {spec_1} and {spec_2}: {e}")
        return "Z3_ERROR"
    except Exception as e:
        print(f"General error comparing {spec_1} and {spec_2}: {e}")
        return "Z3_ERROR"




print(check_semantic_comparison("tests/resources/spec1.smt2", "tests/resources/spec2.smt2"))







