#lang project1/NPCF

(def (x Num) 1)
(def (y (List Num)) (cons 1 (nil Num)))
(def (fib (→ Num Num)) (λ (m Num) (if0 m
                                       0
                                       (if0 (- m 1)
                                            1
                                            (+ (fib (- m 1)) (fib (- m 2)))))))

fib

;(fib 0)
;; expected (0 : Num)
;; returned (0 :)


;(fib 1)
;; expected (1 : Num)
;; returned (1 :)

;(fib 2)
;; expected (1 : Num)
;; returned nothing infinite loop or extremely slow (is it because it is not tail recursive?)
