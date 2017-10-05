#lang project1/VPCF

(def (y Num) 2)

(def (x (→ (→ Num Num) Num)) (λ (t Num) (λ (f Num) t)))




y


;((x 66) 4)
