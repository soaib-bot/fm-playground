; Simple Z3 SMT-LIB example
; Check if there exist integers x and y such that x + y = 10 and x - y = 2

(declare-const x Int)
(declare-const y Int)

(assert (= (+ x y) 10))
(assert (= (- x y) 2))

(check-sat)
(get-model)
