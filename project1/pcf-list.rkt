#lang racket

;; This module implements PCF with lists in three variants:
;; -- call-by-name 
;; -- call-by-value
;; -- call-by-value with unit type [TODO]

(provide
  ;; the grammar for PCF plus lists 
  VPCF
  NPCF

  ;; the reduction systems 
  ->value
  ->name
  ;; the judgment systems
  ⊢_vp
  ⊢_np)


;; ---------------------------------------------------------------------------------------------------
;; dependencies

;(require redex/reduction-semantics)
(require redex)

;; ---------------------------------------------------------------------------------------------------
;; implementation 

(define-language PCF-list 
  ;; Types
  (T Bool
     Num
     (→ T T)
     (List T))
  ;; Programs
  (p (prog d ... e))
  ;; Defs
  (d (def (x T) v))
  ;; Terms
  (e v  
     x
     (λ (x T) e)
     (e e)
     (fix e) 
     (cons e e)
     (fst e)
     (rst e)
     (cons? e)
     (nil? e)
     (nil T)
     (+ e e)
     (- e e)
     (if0 e e e)
   )
  ;; Values
  (v tt
     ff
     n
     (λ (x T) e)
     (nil T)
     (fix v)
     (err T string))
  ;; Numbers
  (n number)
  ;; Variables
  (x variable-not-otherwise-mentioned)
  ;; Type environment
  (Γ ·
     (Γ (x T) ...))

  #:binding-forms
  (λ (x T) e #:refers-to x)
 )

;; ---------------------------------------------------------------------------------------------------
;; Typing judgement for PCF-list programs
(define-judgment-form PCF-list
  #:mode (⊢_p I I O)
  #:contract (⊢_p Γ p T)
  [(⊢_e (Γ (x_1 T_1) ...) v_1 T_1)
   ...
   (⊢_e (Γ (x_1 T_1) ...) e T)
   ------------------------------------------------------ "T-PRO"
   (⊢_p Γ (prog (def ((name x_1 x_!_1) T_1) v_1) ... e) T)]
)



;; ---------------------------------------------------------------------------------------------------
;; Tests on PCF-list
(module+ test
  ;(judgement-holds Γ (x Num) ⊢_p x Num
  (require chk)
  (define def1 (term (x Num)))
  (define def2 (term (y Num)))
  (define def3 (term (z (List Num))))
  (define example1 (term (prog (def ,def1 2) (def ,def2 3) (+ x y))))
  (test-equal (judgment-holds (⊢_p · ,example1 Num)) #t)
  (test-equal (judgment-holds (⊢_e (· ,def1 ,def2) 2 Num)) #t)
  (test-equal (judgment-holds (⊢_e (· ,def1 ,def2) 3 Num)) #t)
  (test-equal (judgment-holds (⊢_e (· (y Num) (x Num)) x Num)) #t)
  (test-equal (judgment-holds (⊢_e (· ,def1 ,def2) (+ x y) Num)) #t)
  (test-equal (judgment-holds (⊢_e (· ,def1 ,def3) (cons x z) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (nil Num) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (cons 2 (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (cons 2 (cons 2 (nil Num))) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (cons? (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e · (nil? (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e · (fst (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e · (rst (cons 2 (nil Num))) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (rst (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (fst (nil Num)) Num)) #t)
  (test-equal (judgment-holds (⊢_p · (prog (def (x Num) 1) (def (y (List Num)) (nil Num)) (cons x y)) (List Num)))
              #t)
  (test-equal (judgment-holds (⊢_p · (prog (def (x Num) 1) (def (y (List Num)) (cons 1 (nil Num))) (cons x y)) (List Num)))
              #t)
  (chk
   #:t (redex-match? PCF-list (x_!_1 ...) (term (x y z)))
   #:! #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term ()))
   #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term (x)))
   #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term (x y z)))
   #:! #:t (redex-match? PCF-list (x_!_1 ...) (term (x y x)))
   #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x y) z)))
   #:! #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x y) x)))
   #:! #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x x) z)))
   
   #:t (redex-match? PCF-list p (term (prog (+ 2 3))))
   #:t (redex-match? PCF-list p (term (prog 5)))
   #:t (redex-match? PCF-list Γ (term ·))
   #:t (redex-match? PCF-list n (term 2))
   #:t (redex-match? PCF-list p (term (prog (def (x Num) 2) 2)))
   #:t (redex-match? PCF-list p (term (prog (def (x Num) 2) x)))
   #:t (redex-match? PCF-list p example1)
   #:t (redex-match? PCF-list e (term (nil Num)))
   #:t (redex-match? PCF-list p (term (prog (def (x Num) 2) (def (z (List Num)) (nil Num)) (cons x z))))
   #:= (judgment-holds (⊢_e (· (x Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e (· (x Num) (y Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e (· (x Num) (y Bool)) y T) T)
   (list (term Bool))
   #:= (judgment-holds (⊢_e (· (x Num)) 1 T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e (· (x Num)) (+ x 1) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p · (prog (def (x Num) 2) (+ x 1)) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p · ,example1 Num) Num)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p · (prog (def (x Num) 2) (def (y Bool) tt) y) T) T)
   (list (term Bool))
   #:= 
   (judgment-holds (⊢_p · (prog (def (x Num) 2) (def (y Num) 3) (+ x y)) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p · (prog (def (x Num) 2) (def (y (List Num)) (nil Num)) (cons x y)) T) T)
   (list (term (List Num)))
  ))

;; ---------------------------------------------------------------------------------------------------
;; Typing judgement for PCF-list expressions
(define-judgment-form PCF-list
  #:mode (⊢_e I I O)
  #:contract (⊢_e Γ e T) 
  [--------------- "T-TRUE"
   (⊢_e Γ tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e Γ ff Bool)]

  [------------- "T-NUM"
   (⊢_e Γ n Num)]

  ;; (x_3 T_3) ... is preserving previous typing
  [(⊢_e (Γ (x_1 T_1) (x_3 T_3) ...) e_2 T_2)
   ----------------------------------------------------- "T-ABS"
   (⊢_e (Γ (x_3 T_3) ...) (λ (x_1 T_1) e_2) (→ T_1 T_2))]
  
  [(⊢_e Γ e_1 (→ T_1 T_2))
   (⊢_e Γ e_2 T_1)
   ---------------------- "T-APP"
   (⊢_e Γ (e_1 e_2) T_2)]

  #;
  [(⊢_e Γ x_2 T_1)
   ------------------------------------------ "T-WEAK" 
   (⊢_e (Γ (x_!_1 T_2)) (name x_2 x_!_1) T_1)]

  [
   ----------------------------------------------------- "T-VAR" 
   (⊢_e (Γ (x T) ... (x_1 T_1) (x_!_1 T_2) ...) x_1 T_1)]




  
  [(⊢_e Γ e_1 (→ T_1 T_1))
   --------------------- "T-FIX"
   (⊢_e Γ (fix e_1) T_1)]
  
  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 Num)
   ----------------------- "T-SUM"
   (⊢_e Γ (+ e_1 e_2) Num)]

  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 Num)
   ----------------------- "T-SUB"
   (⊢_e Γ (- e_1 e_2) Num)]

  [(⊢_e Γ e_1 T_1)
   (⊢_e Γ e_2 (List T_1))
   --------------------------------- "T-CONS"
   (⊢_e Γ (cons e_1 e_2) (List T_1))]

  [(⊢_e Γ e_1 (List T_1))
   --------------------- "T-FST"
   (⊢_e Γ (fst e_1) T_1)]

  [(⊢_e Γ e_1 (List T_1))
   ---------------------------- "T-RST"
   (⊢_e Γ (rst e_1) (List T_1))]

  [(⊢_e Γ e_1 T_1)
   (⊢_e Γ e_2 (List T_1))
   ---------------------------- "T_CONS?"
   (⊢_e Γ (cons? (cons e_1 e_2)) Num)]

  [(⊢_e Γ e_1 (List T))
   ----------------------- "T-NIL?"
   (⊢_e Γ (nil? e_1) Num)]


  [
   ------------------------------ "T-NIL"
   (⊢_e Γ (nil T_1) (List T_1))]


  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 T)
   (⊢_e Γ e_3 T)
   ----------------------------- "T-IF0"
   (⊢_e Γ (if0 e_1 e_2 e_3) T)]

  [
   ------------------------ "T-ERR"
   (⊢_e Γ (err T string) T)]
  )


;; ---------------------------------------------------------------------------------------------------
;; An extended language of PCF-list that calls-by-value
(define-extended-language VPCF PCF-list
  (v .... (cons v v))
  (P-value (prog d ... E-value))
  (E-value hole
           (E-value e)
           (v E-value)
           (fix E-value)
           (cons E-value e)
           (cons v E-value)
           (fst E-value)
           (rst E-value)
           (cons? E-value)
           (nil? E-value)
           (+ E-value e)
           (+ v E-value)
           (- E-value e)
           (- v E-value)
           (if0 E-value e e))
  )

;; ---------------------------------------------------------------------------------------------------
;; Typing judgement for VPCF programs
(define-extended-judgment-form VPCF ⊢_p
  #:mode (⊢_vp I I O)
  #:contract (⊢_vp Γ p T))

;; ---------------------------------------------------------------------------------------------------
;; Reduction Relations for VPCF programs
 (define ->value
  (reduction-relation
   VPCF
   #:domain p
   (--> (in-hole P-value ((λ (x T) e) v)) 
        (in-hole P-value (substitute e x v))  
        "EV-beta")
   
   (--> (in-hole P-value (fix (λ (x T) e)))
        (in-hole P-value (mf-apply substitute e x (fix (λ (x T) e))))
        "EV-fix")
   
   (--> (in-hole P-value ((fix (λ (x T) e)) v))
        (in-hole P-value (((λ (x T) e) (fix (λ (x T) e))) v))
        "EV-fixapp")
   
   (--> (in-hole P-value (fst (cons v_1 v_2)))
        (in-hole P-value v_1)
        "EV-fst")
   (--> (in-hole P-value (fst (nil T)))
        (in-hole P-value (err T "fst of nil"))
        "EV-fsterr")
   (--> (in-hole P-value (rst (cons v_1 v_2)))
        (in-hole P-value v_2)
        "EV-rst")
   (--> (in-hole P-value (rst (nil T)))
        (in-hole P-value (err T "rst of nil"))
        "EV-rsterr")
   (--> (in-hole P-value (cons? (cons v_1 v_2)))
        (in-hole P-value 0)
        "EV-cons?tt")
   (--> (in-hole P-value (cons? (nil T)))
        (in-hole P-value 1)
        "EV-cons?ff")
   (--> (in-hole P-value (nil? (nil T)))
        (in-hole P-value 0)
        "EV-nil?tt")
   (--> (in-hole P-value (nil? (cons v_1 v_2)))
        (in-hole P-value 1)
        "EV-nil?ff")
   (--> (in-hole P-value (if0 0 e_1 e_2))
        (in-hole P-value e_1)
        "EV-if0tt")
   (--> (in-hole P-value (if0 n e_1 e_2))
        (in-hole P-value e_2)
        (side-condition (not (equal? 0 (term n))))
        "EV-if0ff")
   (--> (in-hole P-value (+ n_1 n_2))
        (in-hole P-value ,(+ (term n_1) (term n_2)))
        "EV-plus")
   (--> (in-hole P-value (- n_1 n_2))
        (in-hole P-value ,(- (term n_1) (term n_2)))
        "EV-sub")
   (--> (prog (def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...
           (in-hole E-value x))
        (prog (def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...
           (in-hole E-value v))
        "EV-def")
   )
 )

(define-metafunction VPCF
  eval-value : p -> v
  [(eval-value p)
   v
   (where (prog d ... v) ,(first (apply-reduction-relation* ->value (term p))))])


;; ---------------------------------------------------------------------------------------------------
;; Tests on VPCF
(module+ test
  (traces ->value (term (prog (+ 1 1))))
  (stepper ->value (term (prog (+ 1 1))))
 
  (chk
   #:= 
   (judgment-holds (⊢_vp · (prog (def (x Num) 1) (def (y (List Num)) (cons 1 (nil Num))) (cons x y)) T) T)
   (list (term (List Num)))
   #:t (redex-match? VPCF p (term (prog (def (x Num) 1) (def (y (List Num)) (cons 1 (nil Num))) (cons x y))))

   
   #:t (redex-match? VPCF (prog (def (xx (→ (→ Num Bool) Num)) (λ (ie (→ Num Bool))
                                                                 (λ (x Num) (if0 x tt (if0 (- x 1) ff (ie (- x 2)))))))
                                ((fix xx) 7)))
   
   #:t (redex-match? VPCF ((fix (λ (x (→ Num Num)) x)) 1))
   
   #:t (redex-match? VPCF (in-hole P-value (+ n_1 n_2)) (term (prog (+ 2 3))))
   #:t (redex-match? VPCF p (term (prog (+ 2 3))))
   #:= (term (eval-value (prog (+ 2 3))))
   (term 5)
   #:= (term (eval-value (prog (- 2 3))))
   (term -1)
   #:= (term (eval-value (prog (def (x Num) 2) (def (y Num) 3) (+ x y))))
   (term 5)
   #:= (term (eval-value (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (cons x y))))
   (term (cons 2 (cons 3 (nil Num))))
   #:= (term (eval-value (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (fst (cons x y)))))
   (term 2)
   #:= (term (eval-value (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (rst (cons x y)))))
   (term (cons 3 (nil Num)))
   #:= (term (eval-value (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (cons 7 (rst (cons x y))))))
   (term (cons 7 (cons 3 (nil Num))))
   #:= (term (eval-value (prog (def (y (→ Num Num)) (λ (x Num) (+ x 1))) (y 2))))
   (term 3)
   #:= (term (eval-value (prog (def (x (List Bool)) (nil Bool)) (nil? x))))
   (term 0)

   #:= (term (eval-value (prog (def (xx (→ (→ Num Bool) Num)) (λ (ie (→ Num Bool))
                                                                (λ (x Num)
                                                                  (if0 x tt
                                                                       (if0 (- x 1) ff (ie (- x 2)))))))
                               ((fix xx) 3))))
   (term ff)
   ))




;; ---------------------------------------------------------------------------------------------------
;; An extended language of PCF-list that calls-by-name
(define-extended-language NPCF PCF-list
  (v .... (cons e e))
  (P-name (prog d ... E-name))
  (E-name hole
          (E-name e)
          (fix E-name)
          (fst E-name)
          (rst E-name)
          (cons? E-name)
          (nil? E-name)
          (+ E-name e)
          (+ v E-name)
          (- E-name e)
          (- v E-name)
          (if0 E-name e e))
)
          
;; ---------------------------------------------------------------------------------------------------
;; Typing judgement for NPCF programs
(define-extended-judgment-form NPCF ⊢_p
  #:mode (⊢_np I I O)
  #:contract (⊢_np Γ p T))

;; ---------------------------------------------------------------------------------------------------
;; Reduction Relations for NPCF programs
(define ->name
  (reduction-relation
   NPCF
   #:domain p
   (--> (in-hole P-name ((λ (x T) e_1) e_2))
        (in-hole P-name (mf-apply substitute e_1 x e_2))
        "EN-beta")
   (--> (in-hole P-name (fix (λ (x T) e)))
        (in-hole P-name (mf-apply substitute e x (fix (λ (x T) e))))
        "EN-fix")
   (--> (in-hole P-name ((fix (λ (x T) e)) v))
        (in-hole P-name (((λ (x T) e) (fix (λ (x T) e))) v))
        "EN-fixapp")
   
   (--> (in-hole P-name (fst (cons e_1 e_2)))
        (in-hole P-name e_1)
        "EN-fst")
   (--> (in-hole P-name (fst (nil T)))
        (in-hole P-name (err T "fst of nil"))
        "EN-fsterr")
   (--> (in-hole P-name (rst (cons e_1 e_2)))
        (in-hole P-name e_2)
        "EN-rst")
   (--> (in-hole P-name (rst (nil T)))
        (in-hole P-name (err T "rst of nil"))
        "EN-rsterr")
   (--> (in-hole P-name (cons? (cons e_1 e_2)))
        (in-hole P-name 0)
        "EN-cons?tt")
   (--> (in-hole P-name (cons? (nil T)))
        (in-hole P-name 1)
        "EN-cons?ff")
   (--> (in-hole P-name (nil? (nil T)))
        (in-hole P-name 0)
        "EN-nil?tt")
   (--> (in-hole P-name (nil? (cons e_1 e_2)))
        (in-hole P-name 1)
        "EN-nil?ff")
   (--> (in-hole P-name (if0 0 e_1 e_2))
        (in-hole P-name e_1)
        "EN-if0tt")
   (--> (in-hole P-name (if0 n e_1 e_2))
        (in-hole P-name e_2)
        (side-condition (not (equal? 0 (term n))))
        "EN-if0ff")
   (--> (in-hole P-name (+ n_1 n_2))
        (in-hole P-name ,(+ (term n_1) (term n_2)))
        "EN-sum")
   (--> (in-hole P-name (- n_1 n_2))
        (in-hole P-name ,(- (term n_1) (term n_2)))
        "EN-sub")
   (--> (prog (def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...
           (in-hole E-name x))
        (prog (def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...
           (in-hole E-name v))
        "EN-def")
  )
 )

(define-metafunction NPCF
  eval-name : p -> v
  [(eval-name p)
   v
   (where (prog d ... v) ,(first (apply-reduction-relation* ->name (term p))))])


;; ---------------------------------------------------------------------------------------------------
;; Tests on NPCF
(module+ test
  #; 
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1* (→ (List Num) (List Num)))
                                   (λ (l (List Num))
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                   (fst (cons (+ 1 (fst ones)) y))) T) T) ;;to test having add1* definition is a problem => YES

  ;; to test if having a (very simple) funtion definition is a problem => NO
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1 (→ Num Num)) (λ (x Num) (+ 1 x)))
                                 (add1 2)) T) T)

  ;; to test if having a recursive funtion definition is a problem => YES
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (fib (→ Num Num)) (λ (m Num) (if0 m
                                                                 0
                                                                 (if0 (- m 1)
                                                                      1
                                                                      (+ (fib (- x 1)) (fib (- x 2)))))))
                                 (fib 4)) T) T)

  #; 
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1* (→ (List Num) (List Num)))
                                   (λ (l (List Num))
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                   (add1* y)) T) T) ;; to test using add1* definition is a problem => MAYBE
  #;
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1* (→ (List Num) (List Num)))
                                   (λ (l (List Num))
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (cons (+ 1 (fst ones)) y)) T) T)
  #;
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1* (→ (List Num) (List Num)))
                                   (λ (l (List Num))
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (fst ones)) T) T)

  #;
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (def (add1* (→ (List Num) (List Num)))
                                   (λ (l (List Num))
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (+ x 1)) T) T)
  
  ;; to test ⊢_np is producing ANY types => YES
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (+ x 1)) T) T)

  ;; to test judgment for infinite list => FINE
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 ones) T) T) 

  ;; to test using infinite list is a problem => NO
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                 (def (y (List Num)) (cons 1 (nil Num)))
                                 (def (ones (List Num)) (cons 1 ones))
                                 (fst ones)) T) T)
  ;; to test cons with infinite list is a problem => NO
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                (def (y (List Num)) (cons 1 (nil Num)))
                                (def (ones (List Num)) (cons 1 ones))
                                (fst (cons (fst ones) y))) T) T)

  ;; to test having cons "e" e is a problem => NO
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                (def (y (List Num)) (cons 1 (nil Num)))
                                (def (ones (List Num)) (cons 1 ones))
                                (cons (+ 1 (fst ones)) y)) T) T)

  ;; to test having more than two definition is a problem => NO
  (judgment-holds (⊢_np · (prog (def (x Num) 1)
                                (def (y (List Num)) (cons 1 (nil Num)))
                                (def (ones (List Num)) (cons 1 ones))
                                (def (z Bool) tt)
                                (fst (cons (+ 1 (fst ones)) y))) T) T)

  
  
  (chk
   #:t (judgment-holds (⊢_np · (prog (fst (cons (+ 1 1) (cons 1 (nil Num))))) Num))

   #;
   #:t (redex-match? NPCF ((fix (λ (x (→ Num Num)) x)) 1))
   
   #:t (redex-match? NPCF (in-hole P-name (+ n_1 n_2)) (term (prog (+ 2 3))))
   #:t (redex-match? NPCF p (term (prog (+ 2 3))))

   #;
   #:t (redex-match? NPCF p (term (prog (def (xx (→ (→ Num Bool) Num)) (λ (ie (→ Num Bool))
                                                                (λ (x Num)
                                                                  (if0 x tt
                                                                       (if0 (- x 1) ff (ie (- x 2)))))))
                               ((fix xx) 3))))
   
   #:= (term (eval-name (prog (+ 2 3))))
   (term 5)
   #:= (term (eval-name (prog (- 2 3))))
   (term -1)
   #:= (term (eval-name (prog (def (x Num) 2) (def (y Num) 3) (+ x y))))
   (term 5)
   #:= (term (eval-name (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (cons x y))))
   (term (cons x y))
   #:= (term (eval-name (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (fst (cons x y)))))
   (term 2)
   #:= (term (eval-name (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (rst (cons x y)))))
   (term (cons 3 (nil Num)))
   #:= (term (eval-name (prog (def (x Num) 2) (def (y (List Num)) (cons 3 (nil Num))) (cons 7 (rst (cons x y))))))
   (term (cons 7 (rst (cons x y))))
   #:= (term (eval-name (prog (def (y (→ Num Num)) (λ (x Num) (+ x 1))) (y 2))))
   (term 3)
   #:= (term (eval-name (prog (def (x (List Bool)) (nil Bool)) (nil? x))))
   (term 0)

   #;
   #:= (term (eval-name (prog (def (xx (→ (→ Num Bool) Num)) (λ (ie (→ Num Bool))
                                                                (λ (x Num)
                                                                  (if0 x tt
                                                                     (if0 (- x 1) ff (ie (- x 2)))))))
                             ((fix xx) 3))))
   (term ff)
   
   #:= (term (eval-name (prog (fst (nil Bool)))))
   (term (err Bool "fst of nil"))
   ))




(define-metafunction PCF-list
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])




;;Redex Random testing
(define (progress-holds? e)
  (if (types? e)
      (or (v? e)
          (reduces? e))
      #t))

(define-judgment-form VPCF
  #:mode (typed I I O)
  [(⊢_e Γ e T)
   --------------
   (typed Γ e T)])

(define (types? e)
  (not (null? (judgment-holds (⊢_p · ,e T)
                              T))))
 
(define v? (redex-match VPCF (prog d ... v)))  ;;define a new definition of "value program" 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->value
               (term ,e))))) ;;or wrap an expression in a program (term (prog (,e))) and check ⊢_e
