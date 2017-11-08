#lang racket

;; This module implements PCF with lists in three variants:
;; -- core language: PCF-list
;; -- PCF-list with call-by-value eval: VPCF
;; -- PCF-list with call-by-name eval: NPCF
;; -- call-by-value with unit type [TODO]

(provide
  ;; the grammar for PCF plus lists 
  VPCF
  NPCF
  SPCF

  ;; the reduction systems 
  ->value
  ->name
  ->soup
  
  ;; the judgment systems
  ⊢_vp
  ⊢_np
  ⊢_sp)


;; ---------------------------------------------------------------------------------------------------
;; dependencies

;(require redex/reduction-semantics)
(require redex)
(module+ test (require chk))

;; ---------------------------------------------------------------------------------------------------
;; Syntax of PCF-list

(define-language PCF-list
  ;; Types
  (T ::= Bool
         Num
         (→ T T)
         (List T)
         )
  ;; Programs
  (p ::= (prog (def x_!_1 : T v) ... e))
  ;; Defs
  ;(d ::= (def x : T v))
  ;; Terms
  (e ::= v  
         x
         (λ x : T e)
         (e e)
         (cons e e)
         (fst e)
         (rst e)
         (cons? e)
         (nil? e)
         (nil T)
         (+ e e)
         (- e e)
         (if0 e e e))
  ;; Values
  (v ::= tt
         ff
         n
         (λ x : T e)
         (nil T)
         (err T string))
  ;; Numbers
  (n ::= number)
  ;; Variables
  (x ::= variable-not-otherwise-mentioned)
  ;; Type environment
  (Γ ::= ((x : T) ...))

  ;;This has to come last in the grammar
  #:binding-forms
  (λ x : T e #:refers-to x))

;; ---------------------------------------------------------------------------------------------------
;; Typing of PCF-list

(define-judgment-form PCF-list
  #:mode (⊢_p I I O)
  #:contract (⊢_p Γ p T)
  [(⊢_e ((x_1 : T_1) ...) v_1 T_1)
   ...
   (⊢_e ((x_1 : T_1) ...) e T)
   ------------------------------------------------------ "T-PROG"
   (⊢_p () (prog (def x_1 : T_1 v_1) ... e) T)]
)



;; ---------------------------------------------------------------------------------------------------
;; Tests on PCF-list programs
#;
(module+ test 
  (define def1 (term (x : Num)))
  (define def2 (term (y : Num)))
  (define def3 (term (z : (List Num))))
  (define example1 (term (prog (def x : Num 2) (def y : Num 3) (+ x y))))
  (test-equal (judgment-holds (⊢_p (),example1 Num)) #t)
  (test-equal (judgment-holds (⊢_e (,def1 ,def2) 2 Num)) #t)
  (test-equal (judgment-holds (⊢_e (,def1 ,def2) 3 Num)) #t)
  (test-equal (judgment-holds (⊢_e ((y : Num) (x : Num)) x Num)) #t)
  (test-equal (judgment-holds (⊢_e (,def1 ,def2) (+ x y) Num)) #t)
  (test-equal (judgment-holds (⊢_e (,def1 ,def3) (cons x z) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (nil Num) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (cons 2 (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (cons 2 (cons 2 (nil Num))) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (cons? (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e () (nil? (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e () (fst (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e () (rst (cons 2 (nil Num))) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (rst (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e () (fst (nil Num)) Num)) #t)
  (test-equal (judgment-holds (⊢_e () (cons 1 (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e ((x : (List Num))) x (List Num))) #t)
  #;
  (test-equal (judgment-holds (⊢_p ((x : (List Num))) (prog () x) (List Num))) #t)
 
  (test-equal (judgment-holds (⊢_p () (prog (def x : Bool tt) x) Bool)) #t)
  #; 
  (test-equal (judgment-holds (⊢_p ((x : Num)) (prog (def x : Bool tt) x) Bool)) #t)
  (test-equal (judgment-holds (⊢_e ((x : Bool)) x Bool)) #t)

;;----------------------------------------------------------------------------------------------
  (judgment-holds (⊢_e ((x : (List Bool)) (y : Num) (x : Num)) x T) T)  ;; What should this return?
                                                                        ;; It returns '((List Bool) Num) now.
;;----------------------------------------------------------------------------------------------

  (test-equal (judgment-holds (⊢_p () (prog (def x : Bool tt) x) Bool)) #t)
  (judgment-holds (⊢_p () (prog (def x : Num 1) (def y : (List Num) (nil Num)) (cons x y)) T) T)
  (judgment-holds (⊢_p () (prog (def x : Num 1) (def y : Num 2) (+ x y)) T) T)

 
  (test-equal (judgment-holds (⊢_p () (prog (def x : Num 1) (def y : (List Num) (nil Num)) (cons x y)) (List Num)))
              #t)
  (chk
   
   ;; -----------------------------------------------------------------------------------------------------------
   ;; Semantics of _!
   ;; Note that A #:! t test, where t is another test, represents the expectation that test t will fail.
   
   #:t (redex-match? PCF-list (x_!_1 ...) (term (x y z)))
   #:! #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term ())) ;; expected to fail 
   #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term (x)))
   #:t (redex-match? PCF-list (x_!_1 ... x_!_1) (term (x y z)))
   #:! #:t (redex-match? PCF-list (x_!_1 ...) (term (x y x))) ;; expected to fail
   #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x y) z)))
   #:t (redex-match? PCF-list (x_!_1 ... x x_!_1 ...) (term (x y x)))
   #:! #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x y) x))) ;; expected to fail
   #:! #:t (redex-match? PCF-list ((name x_3 (x_!_1 ...)) (name x_2 x_!_1)) (term ((x x) z))) ;; expected to fail
   ;; -----------------------------------------------------------------------------------------------------------
   
   #:t (redex-match? PCF-list p (term (prog (+ 2 3))))
   #:t (redex-match? PCF-list p (term (prog 5)))
   #:t (redex-match? PCF-list n (term 2))
   #:t (redex-match? PCF-list p (term (prog (def x : Num 2) 2)))
   #:t (redex-match? PCF-list p (term (prog (def x : Num 2) x)))
   #:t (redex-match? PCF-list p example1)
   #:t (redex-match? PCF-list e (term (nil Num)))
   #:t (redex-match? PCF-list p (term (prog (def x : Num 2) (def z : (List Num) (nil Num)) (cons x z))))
   #:= (judgment-holds (⊢_e ((x : Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e ((x : Num) (y : Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e ((x : Num) (y : Bool)) y T) T)
   (list (term Bool))
   #:= (judgment-holds (⊢_e ((x : Num)) 1 T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e ((x : Num)) (+ x 1) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p () (prog (def x : Num 2) (+ x 1)) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p () ,example1 Num) Num)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p () (prog (def x : Num 2) (def y : Bool tt) y) T) T)
   (list (term Bool))
   #:= 
   (judgment-holds (⊢_p () (prog (def x : Num 2) (def y : Num 3) (+ x y)) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p () (prog (def x : Num 2) (def y : (List Num) (nil Num)) (cons x y)) T) T)
   (list (term (List Num)))
  ))

;; ---------------------------------------------------------------------------------------------------
;; Typing of PCF-list expressions

(define-judgment-form PCF-list
  #:mode (⊢_e I I O)
  #:contract (⊢_e Γ e T) 
  [--------------- "T-TRUE"
   (⊢_e ((x_1 : T_1) ...) tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e ((x_1 : T_1) ...) ff Bool)]

  [------------- "T-NUM"
   (⊢_e ((x_1 : T_1) ...) n Num)]

  [(⊢_e ((x_1 : T_1) ... (x : T) (x_n : T_n) ...) e_2 T_2)
   ----------------------------------------------------- "T-ABS"
   (⊢_e ((x_1 : T_1) ... (x_n : T_n) ...) (λ x : T e_2) (→ T T_2))]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 (→ T_3 T_4))
   (⊢_e ((x_1 : T_1) ...) e_2 T_3)
   ---------------------- "T-APP"
   (⊢_e ((x_1 : T_1) ...) (e_1 e_2) T_4)]
     
  [
   ----------------------------------------------------- "T-VAR" 
   (⊢_e ((x_1 : T_1) ... (x : T) (x_n : T_n) ...) x T)]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 Num)
   (⊢_e ((x_1 : T_1) ...) e_2 Num)
   ----------------------- "T-SUM"
   (⊢_e ((x_1 : T_1) ...) (+ e_1 e_2) Num)]

  [(⊢_e ((x_1 : T_1) ...) e_1 Num)
   (⊢_e ((x_1 : T_1) ...) e_2 Num)
   ----------------------- "T-SUB"
   (⊢_e ((x_1 : T_1) ...) (- e_1 e_2) Num)]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 T)
   (⊢_e ((x_1 : T_1) ...) e_2 (List T))
   --------------------------------- "T-CONS"
   (⊢_e ((x_1 : T_1) ...) (cons e_1 e_2) (List T))]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 (List T))
   --------------------- "T-FST"
   (⊢_e ((x_1 : T_1) ...) (fst e_1) T)]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 (List T))
   ---------------------------- "T-RST"
   (⊢_e ((x_1 : T_1) ...) (rst e_1) (List T))]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 T)
   (⊢_e ((x_1 : T_1) ...) e_2 (List T))
   ---------------------------- "T_CONS?"
   (⊢_e ((x_1 : T_1) ...) (cons? (cons e_1 e_2)) Num)]
  
  [(⊢_e ((x_1 : T_1) ...) e_1 (List T))
   ----------------------- "T-NIL?"
   (⊢_e ((x_1 : T_1) ...) (nil? e_1) Num)]
  
  [
   ------------------------------ "T-NIL"
   (⊢_e ((x_1 : T_1) ...) (nil T) (List T))]

  [(⊢_e ((x_1 : T_1) ...) e_1 Num)
   (⊢_e ((x_1 : T_1) ...) e_2 T)
   (⊢_e ((x_1 : T_1) ...) e_3 T)
   ----------------------------- "T-IF0"
   (⊢_e ((x_1 : T_1) ...) (if0 e_1 e_2 e_3) T)]

  [
   -------------------------- "T-ERR"
   (⊢_e ((x_1 : T_1) ...) (err T string) T)]
  )


;; ---------------------------------------------------------------------------------------------------
;; Syntax of VPCF

(define-extended-language VPCF PCF-list
  (v ::= .... (cons v v))
  (P-value ::= (prog (def x_!_1 : T v) ... E-value))
  (E-value ::= hole
               (E-value e)
               (v E-value)
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
               (if0 E-value e e)))

;; ---------------------------------------------------------------------------------------------------
;; Typing of VPCF programs
#;
(define-judgment-form VPCF
  #:mode (⊢_vp I I O)
  #:contract (⊢_vp Γ p T)
  ((⊢_p Γ p T) ; (where _ , (begin (displayln `(,(term Γ) ,(term p))) 0)) <------ debugging typing
   ------------
   (⊢_vp Γ p T)))

(define-extended-judgment-form VPCF ⊢_p
  #:mode (⊢_vp I I O)
  #:contract (⊢_vp Γ p T))


         

;; ---------------------------------------------------------------------------------------------------
;; Evaluation of VPCF programs

 (define ->value
  (reduction-relation
   VPCF
   #:domain p
   (--> (in-hole P-value ((λ x : T e) v)) 
        (in-hole P-value (substitute e x v))  
        "EV-BETA")
   (--> (in-hole P-value (fst (cons v_1 v_2)))
        (in-hole P-value v_1)
        "EV-FST")
   (--> (in-hole P-value (fst (nil T)))
        (in-hole P-value (err T "fst of nil"))    
        "EV-FSTERR")
   (--> (in-hole P-value (rst (cons v_1 v_2)))
        (in-hole P-value v_2)
        "EV-RST")
   (--> (in-hole P-value (rst (nil T)))
        (in-hole P-value (err T "rst of nil"))     
        "EV-RSTERR")
   (--> (in-hole P-value (cons? (cons v_1 v_2)))
        (in-hole P-value 0)
        "EV-CONS?TT")
   (--> (in-hole P-value (cons? v))
        (in-hole P-value 1)
        (side-condition (not (redex-match? VPCF (cons v_1 v_2) (term v))))
        "EV-CONS?FF")
   (--> (in-hole P-value (nil? (nil T)))
        (in-hole P-value 0)
        "EV-NIL?TT")
   (--> (in-hole P-value (nil? v))
        (in-hole P-value 1)
        (side-condition (not (redex-match? VPCF (nil T) (term v))))
        "EV-NIL?FF")
   (--> (in-hole P-value (if0 0 e_1 e_2))
        (in-hole P-value e_1)
        "EV-IF0TT")
   (--> (in-hole P-value (if0 n e_1 e_2))
        (in-hole P-value e_2)
        (side-condition (not (equal? 0 (term n))))
        "EV-IF0FF")
   (--> (in-hole P-value (+ n_1 n_2))
        (in-hole P-value ,(+ (term n_1) (term n_2)))
        "EV-SUM")
   (--> (in-hole P-value (- n_1 n_2))
        (in-hole P-value ,(- (term n_1) (term n_2)))
        "EV-SUB")
   (--> (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_n : T_n v_n) ...
           (in-hole E-value x))
        (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_n : T_n v_n) ...
           (in-hole E-value v))
        "EV-DEF")
  )
 )

(define-metafunction VPCF
  eval-value : p -> v
  [(eval-value p)
   v
   (where (prog (def x_!_1 : T v_1) ... v) ,(first (apply-reduction-relation* ->value (term p))))])
  ;(side-condition (type-checks-value? (term p)))])  

(define (type-checks-value? p)
  (not (null? (judgment-holds (⊢_vp () ,p T)
                              T))))


;; ---------------------------------------------------------------------------------------------------
;; Tests on VPCF
#;
(module+ test
  #;
  (judgment-holds (⊢_vp () (prog (def ones : (List Num) (cons 1 ones)) (fst ones)) T) T)
  (judgment-holds (⊢_vp () (prog (def listofnums1 : (List Num) (cons 1 2)) listofnums1) T) T)
  #;
  (judgment-holds (⊢_vp () (prog (def ones : (List (Unit → Num)) (cons (λ _ : Unit 1) (cons (λ _ : Unit (fst ones)) (nil (Unit → Num)))))
                                  ((fst ones)  unit)     ;; should return 1
                                  ((fst (rst ones)) unit)) ;; should return 1
                        T) T)
  
  
  (judgment-holds (⊢_vp () (prog (def listofnums2 : (List Num) (cons 1 (cons 2 (nil Num)))) listofnums2) T) T)
  #;
  (judgment-holds (⊢_vp () (prog (def ones : (List (Unit → Num)) (cons (λ _ : Unit 1) (λ _ : Unit ones)) (fst ones)))))
  (judgment-holds (⊢_vp () (prog (def x : Num 2) x) T) T)
  (judgment-holds (⊢_vp () (prog (def x : (List Num) (nil Num)) x) T) T)
  (judgment-holds (⊢_vp () (prog (def x : Bool ff) x) T) T)
  (judgment-holds (⊢_vp () (prog (def x : (List Num) (cons 2 2)) x) T) T)
    
  (judgment-holds (⊢_vp () (prog (def x : Num 1) (def y : (List Num) (cons 2 (nil Num))) (cons x y)) T) T)
  (judgment-holds (⊢_vp () (prog (def x : Num 1) (def y : (List Num) (cons 2 (nil Num))) (fst (cons x y))) T) T)
  (test-equal (judgment-holds (⊢_vp () (prog (def x : Num 1) (def y : (List Num) (cons 1 (nil Num))) (cons x y)) (List Num)))
              #t)
  (stepper ->value (term (prog (def x : Num 3) (def y : Num 2) (def z : Bool tt) x)))
   (chk
    #:= (judgment-holds (⊢_vp () (prog (def y : Num 2) (def add2 : (→ Num Num) (λ y : Num (+ y 2))) y) T) T)
    (list (term Num))
    #:= (judgment-holds (⊢_vp () (prog (def x : Num 1) (def y : (List Num) (cons 1 (nil Num))) (cons x y)) T) T)
    (list (term (List Num)))
    #:= (judgment-holds (⊢_vp () (prog (def y : Num 2) (def add2 : (→ Num Num) (λ y : Num (+ y 2))) (add2 y)) T) T)
    (list (term Num))
    #:t (redex-match? VPCF p (term (prog (def x : Num 1) (def y : (List Num) (cons 1 (nil Num))) (cons x y))))
    #:t (redex-match? VPCF p (term (prog (+ (+ 2 3) 5))))
    #:t (redex-match? VPCF (in-hole P-value (+ n_1 n_2)) (term (prog (+ 2 3))))
    #:= (term (eval-value (prog (+ 2 3))))
    (term 5)
    #:= (term (eval-value (prog (- 2 3))))
    (term -1)
   #:= (term (eval-value (prog (def x : Num 2) (def y : Num 3) (+ x y))))
   (term 5)
   #:= (term (eval-value (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (cons x y))))
   (term (cons 2 (cons 3 (nil Num))))
   #:= (term (eval-value (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (fst (cons x y)))))
   (term 2)
   #:= (term (eval-value (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (rst (cons x y)))))
   (term (cons 3 (nil Num)))
   #:= (term (eval-value (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (cons 7 (rst (cons x y))))))
   (term (cons 7 (cons 3 (nil Num))))
   #:= (term (eval-value (prog (def y : (→ Num Num) (λ x : Num (+ x 1))) (y 2))))
   (term 3)
   #:= (term (eval-value (prog (def x : (List Bool) (nil Bool)) (nil? x))))
   (term 0)
   ))




;; ---------------------------------------------------------------------------------------------------
;; Syntax of NPCF

(define-extended-language NPCF PCF-list
  (v ::= .... (cons e e))
  (P-name ::= (prog (def x_!_1 : T ... v) ... E-name))
  (E-name ::= hole
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
              (if0 E-name e e)))
          
;; ---------------------------------------------------------------------------------------------------
;; Typing of NPCF programs

(define-judgment-form NPCF
  #:mode (⊢_np I I O)
  #:contract (⊢_np Γ p T)
  ((⊢_p Γ p T)
   ------------
   (⊢_np Γ p T)))


;; ---------------------------------------------------------------------------------------------------
;; Evaluation of NPCF programs

(define ->name
  (reduction-relation
   NPCF
   #:domain p
   (--> (in-hole P-name ((λ x : T e_1) e_2))
        (in-hole P-name (mf-apply substitute e_1 x e_2))
        "EN-BETA")
   (--> (in-hole P-name (fst (cons e_1 e_2)))
        (in-hole P-name e_1)
        "EN-FST")
   (--> (in-hole P-name (fst (nil T)))
        (in-hole P-name (err T "fst of nil"))
        "EN-FSTERR")
   (--> (in-hole P-name (rst (cons e_1 e_2)))
        (in-hole P-name e_2)
        "EN-RST")
   (--> (in-hole P-name (rst (nil T)))
        (in-hole P-name (err T "rst of nil"))
        "EN-RSTERR")
   (--> (in-hole P-name (cons? (cons e_1 e_2)))
        (in-hole P-name 0)
        "EN-CONS?TT")
   (--> (in-hole P-name (cons? v))
        (in-hole P-name 1)
        (side-condition (not (redex-match? NPCF (cons v_1 v_2) (term v))))
        "EN-CONS?FF")
   (--> (in-hole P-name (nil? (nil T)))
        (in-hole P-name 0)
        "EN-NIL?TT")
   (--> (in-hole P-name (nil? v))
        (in-hole P-name 1)
        (side-condition (not (redex-match? NPCF (nil T) (term v))))
        "EN-NIL?FF")
   (--> (in-hole P-name (if0 0 e_1 e_2))
        (in-hole P-name e_1)
        "EN-IF0TT")
   (--> (in-hole P-name (if0 n e_1 e_2))
        (in-hole P-name e_2)
        (side-condition (not (equal? 0 (term n))))
        "EN-IF0FF")
   (--> (in-hole P-name (+ n_1 n_2))
        (in-hole P-name ,(+ (term n_1) (term n_2)))
        "EN-SUM")
   (--> (in-hole P-name (- n_1 n_2))
        (in-hole P-name ,(- (term n_1) (term n_2)))
        "EN-SUB")
   (--> (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_2 : T_2 v_2) ...
           (in-hole E-name x))
        (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_2 : T_2 v_2) ...
           (in-hole E-name v))
        "EN-DEF")
  )
 )

;; ---------------------------------------------------------------------------------------------------

(define-metafunction NPCF
  eval-name : p -> v
  [(eval-name p)
   v
   (where (prog (def x_!_1 : T v_1) ... v) ,(first (apply-reduction-relation* ->name (term p))))])

(define (type-checks-name? p)
  (not (null? (judgment-holds (⊢_np () ,p T)
                              T))))
;; ---------------------------------------------------------------------------------------------------
;; Tests on NPCF
#;
(module+ test
  (judgment-holds (⊢_np () (prog (def ones : (List Num) (cons 1 ones)) (fst ones)) T) T)
  #; 
  (judgment-holds (() ⊢_np (prog (def x : Num 1)
                              (def y : (List Num) (cons 1 (nil Num)))
                              (def ones : (List Num) (cons 1 ones))
                              (def add1* : (→ (List Num) (List Num))
                                (λ l : (List Num)
                                  (if0 (nil? l)
                                       (nil Num)
                                       (cons (+ (fst l) 1) (add1* (rst l))))))
                                (fst (cons (+ 1 (fst ones)) y))) T) T) ;;to test having add1* definition is a problem => YES

  ;; to test if having a (very simple) funtion definition is a problem => NO
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                              (def y : (List Num) (cons 1 (nil Num)))
                              (def ones : (List Num) (cons 1 ones))
                              (def add1 : (→ Num Num) (λ x : Num (+ 1 x)))
                              (add1 2)) T) T)

  ;; to test if having a recursive funtion definition is a problem => YES
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                              (def y : (List Num) (cons 1 (nil Num)))
                              (def ones : (List Num) (cons 1 ones))
                              (def fib : (→ Num Num) (λ m : Num (if0 m
                                                                 0
                                                                 (if0 (- m 1)
                                                                      1
                                                                      (+ (fib (- x 1)) (fib (- x 2)))))))
                                 (fib 4)) T) T)

  #; 
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (def add1* : (→ (List Num) (List Num))
                                   (λ l : (List Num)
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                   (add1* y)) T) T) ;; to test using add1* definition is a problem => MAYBE
  #;
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (def add1* : (→ (List Num) (List Num))
                                   (λ l : (List Num)
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (cons (+ 1 (fst ones)) y)) T) T)
  #;
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (def add1* : (→ (List Num) (List Num))
                                   (λ l : (List Num)
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (fst ones)) T) T)

  #;
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (def add1* : (→ (List Num) (List Num))
                                   (λ l : (List Num)
                                     (if0 (nil? l)
                                          (nil Num)
                                          (cons (+ (fst l) 1) (add1* (rst l))))))
                                 (+ x 1)) T) T)
  
  ;; to test ⊢_np is producing ANY types => YES
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (+ x 1)) T) T)

  ;; to test judgment for infinite list => FINE
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 ones) T) T) 

  ;; to test using infinite list is a problem => NO
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                 (def y : (List Num) (cons 1 (nil Num)))
                                 (def ones : (List Num) (cons 1 ones))
                                 (fst ones)) T) T)
  ;; to test cons with infinite list is a problem => NO
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                (def y : (List Num) (cons 1 (nil Num)))
                                (def ones : (List Num) (cons 1 ones))
                                (fst (cons (fst ones) y))) T) T)

  ;; to test having cons "e" e is a problem => NO
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                (def y : (List Num) (cons 1 (nil Num)))
                                (def ones : (List Num) (cons 1 ones))
                                (cons (+ 1 (fst ones)) y)) T) T)

  ;; to test having more than two definition is a problem => NO
  (judgment-holds (⊢_np () (prog (def x : Num 1)
                                (def y : (List Num) (cons 1 (nil Num)))
                                (def ones : (List Num) (cons 1 ones))
                                (def z : Bool tt)
                                (fst (cons (+ 1 (fst ones)) y))) T) T)

  
  
  (chk
   #:t (judgment-holds (⊢_np () (prog (fst (cons (+ 1 1) (cons 1 (nil Num))))) Num))
   #:t (redex-match? NPCF (in-hole P-name (+ n_1 n_2)) (term (prog (+ 2 3))))
   #:t (redex-match? NPCF p (term (prog (+ 2 3))))
   #:= (term (eval-name (prog (+ 2 3))))
   (term 5)
   #:= (term (eval-name (prog (- 2 3))))
   (term -1)
   #:= (term (eval-name (prog (def x : Num 2) (def y : Num 3) (+ x y))))
   (term 5)
   #:= (term (eval-name (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (cons x y))))
   (term (cons x y))
   #:= (term (eval-name (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (fst (cons x y)))))
   (term 2)
   #:= (term (eval-name (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (rst (cons x y)))))
   (term (cons 3 (nil Num)))
   #:= (term (eval-name (prog (def x : Num 2) (def y : (List Num) (cons 3 (nil Num))) (cons 7 (rst (cons x y))))))
   (term (cons 7 (rst (cons x y))))
   #:= (term (eval-name (prog (def y : (→ Num Num) (λ x : Num (+ x 1))) (y 2))))
   (term 3)
   #:= (term (eval-name (prog (def x : (List Bool) (nil Bool)) (nil? x))))
   (term 0)
   #:= (term (eval-name (prog (fst (nil Bool)))))
   (term (err Bool "fst of nil"))
   ))
;; --------------------------------------------------------------------------------------------------------------------

(define-metafunction PCF-list
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])




;; --------------------------------------------------------------------------------------------------------------------
;; Redex Random testing

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
  (not (null? (judgment-holds (⊢_p () ,e T)
                              T))))
 
(define v? (redex-match VPCF (prog d ... v)))  ;;define a new definition of "value program" 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->value
               (term ,e))))) ;;or wrap an expression in a program (term (prog (,e))) and check ⊢_e





;; ---------------------------------------------------------------------------------------------------
;; Syntax of SPCF

(define-extended-language SPCF VPCF
  (T   ::= ....
           Unit
           (Stream T))
  (p   ::= ....)
  (e   ::= ....
           unit
           (thunk? e))
  (v   ::= ....
           unit)
  (E-value ::= ....
               (thunk? E-value))
)
       

;; ---------------------------------------------------------------------------------------------------
;; Typing of SPCF programs
(define-judgment-form SPCF
  #:mode (⊢_sp I I O)
  #:contract (⊢_sp Γ p T)
  [(⊢_se ((x_1 : T_1) ...) v_1 T_1)
   ...
   (⊢_se ((x_1 : T_1) ...) e T)
   ------------------------------------------------------ "T-SPROG"
   (⊢_sp () (prog (def x_1 : T_1 v_1) ... e) T)]
)


(define-extended-judgment-form SPCF ⊢_e
  #:mode (⊢_se I I O)
  #:contract (⊢_se Γ e T)
  
 [----------------------------------------------------- "T-UNIT"
  (⊢_se ((x_1 : T_1) ...) unit Unit)] 

 [(⊢_se ((x_1 : T_1) ...) e_1 T)
  (⊢_se ((x_1 : T_1) ...) e_2 (Stream T))
  ----------------------------------------------------- "T-STR"
  (⊢_se ((x_1 : T_1) ...) (cons e_1 e_2) (Stream T) )]

 [----------------------------------------------------- "T-NILSTR"
  (⊢_se ((x_1 : T_1) ...) (nil T) (Stream T))]

 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-THUNK"
  (⊢_se ((x_1 : T_1) ...) (λ _ : Unit e) (Stream T))]

 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-FSTSTR"
  (⊢_se ((x_1 : T_1) ...) (fst e) T)]

 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-RSTSTR"
  (⊢_se ((x_1 : T_1) ...) (rst e) (Stream T))]

 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-CONS?STR"
  (⊢_se ((x_1 : T_1) ...) (cons? e) Num)]  

 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-NIL?STR"
  (⊢_se ((x_1 : T_1) ...) (nil? e) Num)]
  
 [(⊢_se ((x_1 : T_1) ...) e (Stream T)) 
  ----------------------------------------------------- "T-THUNK?STR"
  (⊢_se ((x_1 : T_1) ...) (thunk? e) Num)]  
)

;; ---------------------------------------------------------------------------------------------------
;; Evaluation of SPCF programs

(define-metafunction SPCF
  eval-soup : p -> v
  [(eval-soup p)
   v
   (where (prog (def x_!_1 : T v_1) ... v) ,(first (apply-reduction-relation* ->soup (term p))))])

 ;; Violates abstration principle in software engineering
 ;; copy and paste of ->value
 ;; Can I just inherit ->value?
 ;; But maybe I need to redefine fst and rst correspondingly to Stream T type
 (define ->soup
  (reduction-relation
   SPCF
   #:domain p
   (--> (in-hole P-value ((λ x : T e) v)) 
        (in-hole P-value (substitute e x v))  
        "ES-BETA")
   (--> (in-hole P-value (fst (cons v_1 v_2)))
        (in-hole P-value v_1)
        "ES-FST")
   (--> (in-hole P-value (fst v))
        (in-hole P-value (fst (v unit)))
        (side-condition (redex-match? SPCF (λ _ : T e) (term v)))
        "ES-FSTTHUNK")
   (--> (in-hole P-value (fst (nil T)))
        (in-hole P-value (err T "fst of nil"))       
        "ES-FSTERR")
   (--> (in-hole P-value (rst (cons v_1 v_2)))
        (in-hole P-value v_2)
        "ES-RST")
   (--> (in-hole P-value (rst v))
        (in-hole P-value (v unit))
        (side-condition (redex-match? SPCF (λ _ : T e) (term v)))
        "ES-RSTTHUNK")
   (--> (in-hole P-value (rst (nil T)))
        (in-hole P-value (err T "rst of nil"))
        (side-condition (not (redex-match? SPCF (λ _ : T e) (term v))))
        "ES-RSTERR")
   (--> (in-hole P-value (cons? (cons v_1 v_2)))
        (in-hole P-value 0)
        "ES-CONS?TT")
   (--> (in-hole P-value (cons? v))
        (in-hole P-value 1)
        (side-condition (not (redex-match? SPCF (cons v_1 v_2) (term v))))
        "ES-CONS?FF")
   (--> (in-hole P-value (nil? (nil T)))
        (in-hole P-value 0)
        "ES-NIL?TT")
   (--> (in-hole P-value (nil? v))
        (in-hole P-value 1)
        (side-condition (not (redex-match? SPCF (nil T) (term v))))
        "ES-NIL?FF")
   ;; --------------------------------------------------------------------
   ;; thunk? 
   (--> (in-hole P-value (thunk? v))
        (in-hole P-value 0)
        (side-condition (redex-match? SPCF (λ _ : T e) (term v)))
        "ES-THUNK?TT")
   (--> (in-hole P-value (thunk? v))
        (in-hole P-value 1)
        (side-condition (not (redex-match? SPCF (λ _ : T e) (term v))))
        "ES-THUNK?FF")
   ;; --------------------------------------------------------------------
   (--> (in-hole P-value (if0 0 e_1 e_2))
        (in-hole P-value e_1)
        "ES-IF0TT")
   (--> (in-hole P-value (if0 n e_1 e_2))
        (in-hole P-value e_2)
        (side-condition (not (equal? 0 (term n))))
        "ES-IF0FF")
   (--> (in-hole P-value (+ n_1 n_2))
        (in-hole P-value ,(+ (term n_1) (term n_2)))
        "ES-SUM")
   (--> (in-hole P-value (- n_1 n_2))
        (in-hole P-value ,(- (term n_1) (term n_2)))
        "ES-SUB")
   (--> (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_n : T_n v_n) ...
           (in-hole E-value x))
        (prog (def x_1 : T_1 v_1) ... (def x : T v) (def x_n : T_n v_n) ...
           (in-hole E-value v))
        "EV-DEF")
  )
 )


(module+ test
  (define ones (term (cons 1 (λ any : Unit ones))))
  (judgment-holds (⊢_sp () (prog (def x : Num 1) x) T) T)
  (judgment-holds (⊢_sp () (prog (def x : Num 1) (nil Num)) T) T)
  (judgment-holds (⊢_sp () (prog (def x : Num 1) (λ any : Unit (nil Num))) T) T)
  (judgment-holds (⊢_sp () (prog (def l : (Stream Num) (cons 1 (nil Num))) l) T) T)
  (judgment-holds (⊢_sp () (prog (def ones : (Stream Num) (cons 1 (λ any : Unit ones))) ones) T) T)
  (judgment-holds (⊢_sp () (prog (def ones : (Stream Num) (cons 1 (λ any : Unit ones))) (fst ones)) T) T)
  (judgment-holds (⊢_sp () (prog (def ones : (Stream Num) (cons 1 (λ any : Unit ones))) (rst ones)) T) T)
  ;; below does not type check (it might be because (cons 1 (nil Num)) is both (List Num) and (Stream Num))
  (judgment-holds (⊢_sp () (prog (def length : (→ (Stream Num) Num) (λ l : (Stream Num) (if0 (nil? l)
                                                                        0
                                                                        (+ 1 (length (rst l))))))
                                 (length (cons 1 (nil Num)))) T) T)

  (judgment-holds (⊢_sp () (prog (cons 1 (nil Num))) T) T)

  (judgment-holds (⊢_sp () (prog (def add1 : (→ Num Num) (λ x : Num (+ 1 x))) (add1 1)) T) T)

  ;; ---------------------------------------------------------------------------------------------------------------------
  ;; length (ones) example
  #;
  (stepper ->soup (term (prog (def length : (→ (Stream Num) Num) (λ l : (Stream Num) (if0 (nil? l)
                                                                                      0
                                                                                     (+ 1 (length (rst l))))))
                              (def three-ones : (Stream Num) (cons 1 (cons 1 (cons 1 (nil Num)))))
                              (def ones : (Stream Num) (cons 1 (λ _ : Unit ones)))
                              (length ones))))
  #;
  (stepper ->soup (term (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones))) (fst (rst (rst (rst (rst (rst ones)))))))))
  #;
  (stepper ->soup (term (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones))) (rst ones))))
  #;
  (stepper ->soup (term (prog ((λ _ : (Stream Num) 42) (rst (cons 1 (λ _ : Unit 1)))))))

  
  (chk
   #:= (term (eval-soup (prog (thunk? (λ _ : Unit 1)))))
   (term 0)
   #:= (term (eval-soup (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones))) (fst ones))))
    (term 1)
   #:= (term (eval-soup (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones))) (fst (rst ones)))))
    (term 1)
   #:= (term (eval-soup (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones))) (rst ones))))
    (term (λ _ : Unit ones))
   #:= (term (eval-soup (prog (def ones : (Stream Num) (cons 1 (λ _ : Unit ones)))
                              (fst (rst (rst (rst ones)))))))
    (term 1)
   #:= (term (eval-soup (prog (def ones : (Stream Num) (cons 1 (cons 1 (nil Num))))
                              (rst ones))))
    (term (cons 1 (nil Num)))
   #:= (term (eval-soup (prog ((λ _ : (Stream Num) 42) (rst (cons 1 (λ _ : Unit 1)))))))
    (term 42)
    )
  )

;; ----------------------------------------------------------------------------------------------------
;; A Compiler from VPCF to SPCF

(define-union-language UPCF (v-. VPCF) (s-. SPCF))

#;
(define-metafunction SPCF
  compile-npcf : e -> e
  [(compile-npcf v) v]
  [(compile-npcf x) x]
  [(compile-npcf (λ x : T e)) (λ x : T e)]
  [(compile-npcf (e e)) (e e)]
  [(compile-npcf (cons v e)) (cons v (λ _ : Unit e))]
  [(compile-npcf (fst e)) (fst e)]
  [(compile-npcf (rst e)) (rst e)]
  [(compile-npcf (cons? e)) (cons? e)]
  [(compile-npcf (nil? e)) (nil? e)]
  [(compile-npcf (+ e e)) (+ e e)]
  [(compile-npcf (- e e)) (- e e)]
  [(compile-npcf (if0 e e e)) (if0 e e e)])
  
  
  