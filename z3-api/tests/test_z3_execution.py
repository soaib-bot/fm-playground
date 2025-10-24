from z3_exec.z3 import run_z3, run_z3_with_redundancy_detection


valid_spec = """(declare-const a Int)
(declare-const b Int)
(assert (> a 1))
(assert (> b 1))
(assert (= (* a b) 17))
(check-sat)
(get-model)"""


def test_train_success():
    result = run_z3(valid_spec)
    assert "unsat" in result
    assert " model is not available" in result


def test_run_z3_redundancy_detection():
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
    result, redundant_lines = run_z3_with_redundancy_detection(spec)
    assert "sat" in result