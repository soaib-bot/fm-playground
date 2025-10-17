from smt_diff import *


def test_int_real_diff():
    s1 = """
    (declare-const x Real)
    (assert (> x 0))
    (assert (is_int x))
    """

    s2 = """
    (declare-const x Real)
    (assert (> x 0.5))"""
    generator = diff_witness(parse_smt2_string(s2), parse_smt2_string(s1))

    witness = next(generator).sexpr()
    assert "Real" in witness


def test_datatype_changes():
    s1 = """
    (declare-datatypes () ((S A B )))
    ;(declare-datatypes () ((S A B C)))
    (declare-const x S)
    (assert (= x A))
    ;(assert (< x C))"""
    s2 = """
    (declare-datatypes () ((S A B C)))
    (declare-const y S)
    (assert (= y B))"""
    s1_assertions = parse_smt2_string(s1)
    s2_assertions = parse_smt2_string(s2)
    generator = diff_witness(s1_assertions, s2_assertions)
    witness = next(generator).sexpr()
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

    generator = diff_witness(parse_smt2_string(s1), parse_smt2_string(s2))
    witness1 = next(generator).sexpr()
    witness2 = next(generator).sexpr()
    assert witness1 != witness2
