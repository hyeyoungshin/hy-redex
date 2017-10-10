#lang project1/VPCF

(def (y Num) 2)
(def (add2 (→ Num Num)) (λ (y Num) (+ y 2)))

;(def (x (→ (→ Num Num) Num)) (λ (t Num) (λ (f Num) t)))

(add2 y)

;; test 1 -----------------------------------
;y
;; expected '(2 : Num)
;; returned '(2 :)


;; test 2 -----------------------------------
;((x 66) 4)
;; expected '(66 : Num)
;; returned '(66 :)


;; test 3 -----------------------------------
;(λ (t Num) (λ (f Num) t))
;; expected '((λ (t Num) (λ (f Num) t)) :(→ Num (→ Num Num)))
;; returned '((λ (t Num) (λ (f Num) t)) :) when the second definition is not commented out

