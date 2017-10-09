#lang project1/NPCF-tlc

(def x : Num 1)
(def y : (List Num) (cons 1 (nil Num)))
#;
(def fib : (→ Num Num) (λ  m : Num (if0 m
                                       0
                                       (if0 (- m 1)
                                            1
                                            (+ (fib (- m 1)) (fib (- m 2)))))))

x
