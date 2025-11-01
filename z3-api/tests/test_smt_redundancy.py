from smt_redundancy.redundancy import unsat_core
from z3 import *


def test_redundant_lines():
    spec = """(set-option :produce-unsat-cores true)
(declare-const x Int)
(declare-const y Int)

; Core-1: {Xg1, Xl1}
; Core-2: {Xg1, Xl0}
(assert (> x 2))
(assert (> x 1))


(assert (or
    (> (+ x y) 0)
        (< y 0)))
(assert (or (>= y 0) (>= x 0)))
(assert (or (< y 0) (< x 0)))
(assert (or (> y 0) (> x 0)))
(check-sat)
(get-model) ; unsat
; (get-unsat-core)
"""
    solver = Solver()
    solver.from_string(spec)
    redundant_lines = unsat_core(solver, solver.assertions(), smt2_file=spec)
    assert {8}.issubset(redundant_lines)
    assert {11, 12, 13}.issubset(redundant_lines)
    assert not {7}.issubset(redundant_lines)
