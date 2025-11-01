from smt_redundancy.explain_redundancy import explain_redundancy_from_smtlib
from z3 import *


def test_redundancy_explanation():
    spec = """(declare-const x Int)
(assert (> x 2))
(assert (> x 1))
(check-sat)"""
    explanation = explain_redundancy_from_smtlib(spec, 3)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[2, 2, 0, 17]]
    explanation = explain_redundancy_from_smtlib(spec, 2)
    assert explanation[3] == []


def test_space_in_assert():
    spec = """(declare-const x Int)
(assert (> x 2))
( assert (> x 1))
(check-sat)"""
    explanation = explain_redundancy_from_smtlib(spec, 3)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[2, 2, 0, 17]]
    explanation = explain_redundancy_from_smtlib(spec, 2)
    assert explanation[3] == []


def test_line_comment_in_assert():
    spec = """(declare-const x Int)
(assert (> x 2))
  (     assert
    ( > x 1)  ; this is a comment
    ; this is a comment
)
(check-sat)"""
    explanation = explain_redundancy_from_smtlib(spec, 3)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[2, 2, 0, 17]]
    explanation = explain_redundancy_from_smtlib(spec, 4)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[2, 2, 0, 17]]
    explanation = explain_redundancy_from_smtlib(spec, 5)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[2, 2, 0, 17]]
    explanation = explain_redundancy_from_smtlib(spec, 2)
    assert explanation[3] == []


def test_multiple_asserts_single_line():
    spec = """(
    declare-const x Int)
(assert (> x 2)) (assert (> x 1))
(check-sat)"""
    explanation = explain_redundancy_from_smtlib(spec, 3)
    assert explanation is not None
    assert explanation[2].sexpr() == "(> x 1)"
    assert explanation[3] == [[3, 3, 0, 17]]
    assert explanation[4] == [3, 3, 17, 34]


def test_push_pop_asserts():
    spec = """(declare-const x Int)
(push)
(assert (> x 2))
(pop)
(assert (> x 1))
(check-sat)"""
    explanation = explain_redundancy_from_smtlib(spec, 5)
    assert explanation is not None
    assert explanation[3] == []


def test_push_pop_asserts2():
    spec2 = """(declare-const x Int)
(declare-const y Int)
(push)
(assert (or (> y 0) (> x 0)))
(check-sat)
(pop)
(assert (> x 1))
(assert (> x 13))
(check-sat)
; (assert (= x 2))
"""
    explanation2 = explain_redundancy_from_smtlib(spec2, 8)
    assert explanation2 is not None
    assert explanation2[3] == []
    explanation2 = explain_redundancy_from_smtlib(spec2, 7)
    assert explanation2 is not None
    assert explanation2[3] == [[8, 8, 0, 18]]
    try:
        explanation2 = explain_redundancy_from_smtlib(spec2, 4)
    except Exception as e:
        # Should raise an exception since assertion at line 4 is in a popped context
        assert isinstance(e, ValueError)
