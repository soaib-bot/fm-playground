from smt_diff import *

s1 = """
(declare-const x Real)
(assert (> x 0))
(assert (is_int x))
"""

s2 = """
(declare-const x Real)
(assert (> x 0.5))"""


def test_int_real_diff():
    id = get_next_witness(s2, s1, mode="diff")
    witness = get_next_witness(id)
    print(witness)
    assert "Real" in witness
    
    
def test_datatype_changes():
    s1 = """
    ; (declare-datatypes () ((S A B)))
    (declare-datatypes () ((S A B C)))
    (declare-const x S)
    (assert (< x C))"""
    s2 = """
    (declare-datatypes () ((S A B C)))
    (declare-const x S)"""
    
    id = get_next_witness(s1, s2, mode="diff")
    witness = get_next_witness(id)
    print(witness)
    assert "D" not in witness
    
def test_store_witness():
    s1 = """
    (declare-const x Int)
    (assert (> x 0))
    (assert (< x 5))
    """
    s2 = """
    (declare-const x Int)
    (assert (> x 3))
    """
    
    id = store_witness(s1, s2, mode="diff")
    witness1 = get_next_witness(id)
    witness2 = get_next_witness(id)
    assert witness1 != witness2
