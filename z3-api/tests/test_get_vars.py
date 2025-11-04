from utils.helper import get_all_vars
from z3 import *


def test_data_types():
    spec = """(declare-datatypes () ((Nat zero (succ (pred Nat)))))
(declare-fun p (Nat) Bool)
(assert (p zero))
(assert (p zero))
(assert (forall ((x Nat)) (implies (p (pred x)) (p x))))
(assert (not (forall ((x Nat)) (p x))))
(check-sat)"""
    s = Solver()
    s.from_string(spec)
    all_vars = get_all_vars(s.assertions())
    assert len(all_vars) == 1  # p
