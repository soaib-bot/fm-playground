from smt_diff.smt_diff import *
from z3 import *

def test_get_next_witness():
    s1 = """(declare-const x Int)
    (declare-const y Int)
    (declare-sort A)
    (declare-fun f (A) A)
    (declare-const a A)
    (assert (> y 0))
    (assert (> x 0))
    (assert (= (f a) a))"""

    s2 = """(declare-const x Int)
    (declare-const z Int)
    (assert (< x 5))
    (assert (< z 10))"""
    specId = store_witness(s1, s2, analysis="not-previous-but-current")
    witness = get_next_witness(specId)
    assert witness is not None
    
def test_get_all_vars():
    s1 = """(declare-const x Int)
    (declare-const y Int)
    (declare-sort A)
    (declare-fun f (A) A)
    (declare-const a A)
    (declare-sort Type)
    (declare-fun subtype (Type Type) Bool)
    (declare-fun array-of (Type) Type)
    (assert (forall ((x Type)) (subtype x x)))
    (assert (> y 0))
    (assert (> x 0))
    (assert (= (f a) a))"""
    vars = get_all_vars(parse_smt2_string(s1))
    names = {str(v) for v in vars}
    assert "x" in names
    assert "subtype" in names

def test_prettify_result():
    s1 = """(declare-const x Int)
    (declare-const y Int)
    (declare-sort A)
    (declare-fun f (A) A)
    (declare-const a A)
    (assert (> y 0))
    (assert (> x 0))
    (assert (= (f a) a))"""

    s2 = """(declare-const x Int)
    (declare-const z Int)
    (assert (< x 5))
    (assert (< z 10))"""
    specId = store_witness(s1, s2, analysis="not-previous-but-current")
    witness = get_next_witness(specId)
    pretty_witness = prettify_result(parse_smt2_string(s1), parse_smt2_string(s2), witness)
    assert pretty_witness is not None
    
def test_filter():
    s1 = """
    (declare-const x Real)
    (assert (< x 1))
    """

    s2 = """
    (declare-const x Real)
    (assert (> x 0.5))"""
    specId = store_witness(s1, s2, analysis="not-previous-but-current", filter="(assert (> x 0.7))")
    assert specId is not None
    witness = get_next_witness(specId)
    assert witness is not None
    
    specId = store_witness(s1, s2, analysis="common-witness", filter="(assert (> x 0.7))")
    assert specId is not None
    witness = get_next_witness(specId)
    assert witness is not None