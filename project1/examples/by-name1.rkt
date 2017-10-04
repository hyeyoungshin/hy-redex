#lang project1/NPCF

(def (x Num) 1)
(def (y (List Num)) (cons 1 (nil Num)))
(def (fib (→ Num Num)) (λ (m Num) (if0 m
                                       0
                                       (if0 (- m 1)
                                            1
                                            (+ (fib (- x 1)) (fib (- x 2)))))))

(fib 2)
