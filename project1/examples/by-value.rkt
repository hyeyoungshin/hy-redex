#lang project1/VPCF

; (def (ones (List Num)) (cons 1 (cons 2 (cons 3 (nil Num)))))

(def (x Num) 1)
#;
(def (y (List Num)) (nil Num))

(def (y (List Num)) (cons 1 (nil Num)))


(def (add1* (→ (List Num) (List Num)))
  (λ (l (List Num))
    (if0 (nil? l)
         (nil Num)
         (cons (+ (fst l) 1) (add1* (rst l))))))

(add1* (cons (+ x 22) y))

#;
(cons x 1)

#;
(cons x y)

#;
(fst (cons (+ 1 (fst y)) y))

