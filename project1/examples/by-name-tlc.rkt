#lang project1/NPCF-tlc

(def y : Num 2)
(def add2 : (→ Num Num) (λ y : Num (+ y 2)))

(add2 y)