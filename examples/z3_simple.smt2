; Simple Z3 SMT-LIB 2.0 example
; Tests basic integer arithmetic

(set-logic QF_LIA)

; Declare variables
(declare-const x Int)
(declare-const y Int)

; Add constraints
(assert (> x 0))
(assert (> y 0))
(assert (= (+ x y) 10))
(assert (< x y))

; Check satisfiability
(check-sat)
