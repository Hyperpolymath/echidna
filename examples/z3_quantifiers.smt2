; Z3 example with quantifiers
; Tests universal quantification

(set-logic ALL)

; Declare function
(declare-fun f (Int) Int)

; Universal property: f is monotonic
(assert (forall ((x Int) (y Int))
    (=> (< x y)
        (< (f x) (f y)))))

; Specific values
(declare-const a Int)
(declare-const b Int)

(assert (= a 1))
(assert (= b 2))

; Check if f(a) < f(b) follows from monotonicity
(assert (not (< (f a) (f b))))

(check-sat)
