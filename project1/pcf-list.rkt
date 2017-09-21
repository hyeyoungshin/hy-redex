#lang racket

(require redex/reduction-semantics)

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
     d
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
     (err T string)
   )
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

(define-judgment-form PCF-list
  #:mode (⊢_p I I O)
  #:contract (⊢_p Γ p T)
  [(⊢_e (Γ (x_1 T_1) ...) v_1 T_1)
   ...
   (⊢_e (Γ (x_1 T_1) ...) e T)
   ------------------------------------------
   (⊢_p Γ (prog (def (x_1 T_1) v_1) ... e) T)]
)
  
(module+ test
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
  (test-equal (judgment-holds (⊢_e · (cons? (cons 2 (nil Num))) Bool)) #t)
  (test-equal (judgment-holds (⊢_e · (nil? (cons 2 (nil Num))) Bool)) #t)
  (test-equal (judgment-holds (⊢_e · (fst (cons 2 (nil Num))) Num)) #t)
  (test-equal (judgment-holds (⊢_e · (rst (cons 2 (nil Num))) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (rst (nil Num)) (List Num))) #t)
  (test-equal (judgment-holds (⊢_e · (fst (nil Num)) Num)) #t) ;;;;;;;;;;;;;;;;;should this be ok?
;  
  
  (chk
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
   (judgment-holds (⊢_p · (prog (def (y Num) 2) (def (y Num) 3) (+ 2 y)) T) T)
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
   

;   #:= 
;   (judgment-holds (⊢_p · (prog (def (x Num) 2) (def (x Bool) tt) x) T) T)
;   (list (term (Bool)))
  ))


(define-judgment-form PCF-list
  #:mode (⊢_e I I O)
  #:contract (⊢_e Γ e T) 
  [--------------- "T-TRUE"
   (⊢_e Γ tt Bool)]

  [--------------- "T-FALSE"
   (⊢_e Γ ff Bool)]

  [------------- "T-NUM"
   (⊢_e Γ n Num)]

  [(⊢_e (Γ (x_1 T_1)) e_2 T_2)
   ------------------------------------- "T-ABS"
   (⊢_e Γ (λ (x_1 T_1) e_2) (→ T_1 T_2))]
  
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


  [
   --------------------------------------------------------------------------------------------------- "T-SHADOW" 
   (⊢_e (Γ (x_s T_s) ... (x_1 T_1) (x_s2 T_s2) ... ((name x_1 x_!_1) T_2) (x_!_1 T_rest) ...) x_1 T_2)]

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
   (⊢_e Γ (cons? (cons e_1 e_2)) Bool)]

  [(⊢_e Γ e_1 (List T))
   ----------------------- "T-NIL?"
   (⊢_e Γ (nil? e_1) Bool)]


  [
   ------------------------------ "T-NIL"
   (⊢_e Γ (nil T_1) (List T_1))]


  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 T)
   (⊢_e Γ e_3 T)
   ----------------------------- "T-IF0"
   (⊢_e Γ (if0 e_1 e_2 e_3) T)]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

 (define ->value
  (reduction-relation
   VPCF
   #:domain p
   (--> (in-hole P-value ((λ (x T) e_1) v_1)) 
        (in-hole P-value (substitute e_1 x v_1))  
        "EV-beta")
   (--> (in-hole P-value (fix (λ (x T) e_1)))
        (in-hole P-value (mf-apply substitute x (fix (λ (x T) e_1)) e_1))
        "EV-fix")
   (--> (in-hole P-value ((fix (λ (x T) e_1)) e_2))
        (in-hole P-value (((λ (x T) e_1) (fix (λ (x T) e_1))) e_2))
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
        (in-hole P-value tt)
        "EV-cons?tt")
   (--> (in-hole P-value (cons? (nil T)))
        (in-hole P-value ff)
        "EV-cons?ff")
   (--> (in-hole P-value (nil? (nil T)))
        (in-hole P-value tt)
        "EV-nil?tt")
   (--> (in-hole P-value (nil? (cons v_1 v_2)))
        (in-hole P-value ff)
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

(module+ test
(chk
   #:t (redex-match? VPCF (in-hole P-value (+ n_1 n_2)) (term (prog (+ 2 3))))
   #:t (redex-match? VPCF p (term (prog (+ 2 3))))
   #:= (term (eval-value (prog (+ 2 3))))
   (term 5)
   ))


;(define-metafunction VPCF
;  EV-∑ : number ... -> number
;  [(EV-∑ number ...)
;   ,(apply + (term (number ...)))])

(define-metafunction VPCF
  eval-value : p -> v
  [(eval-value p)
   v
   (where (prog d ... v) ,(first (apply-reduction-relation* ->value (term p))))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-extended-language NPCF PCF-list
  (v (cons e e))
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
          (if0 E-name e e))
)
          

(define ->name
  (reduction-relation
   NPCF
   #:domain p
   (--> (in-hole P-name ((λ (x T) e_1) e_2))
        (in-hole P-name (subst e_2 x e_1))
        "EN-beta")
   (--> (in-hole P-name (fix (λ (x T) e_1)))
        (in-hole P-name (subst x (fix (λ (x T) e_1)) e_1))
        "EN-fix")
   (--> (in-hole P-name ((fix (λ (x T) e_1)) e_2))
        (in-hole P-name (((λ (x T) e_1) (fix (λ (x T) e_1))) e_2))
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
        (in-hole P-name tt)
        "EN-cons?tt")
   (--> (in-hole P-name (cons? (nil T)))
        (in-hole P-name ff)
        "EN-cons?ff")
   (--> (in-hole P-name (nil? (nil T)))
        (in-hole P-name tt)
        "EN-nil?tt")
   (--> (in-hole P-name (nil? (cons e_1 e_2)))
        (in-hole P-name ff)
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
   (--> (prog f ... v)
        v
        "EN-halt")
  )
 )

;(require redex/tut-subst)
;(define-metafunction NPCF
;  subst : x v e -> t
;  [(subst x v e)
;   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])
;(define x? (redex-match NPCF x))


;(define-metafunction NPCF
;  eval-name : t -> v
;  [(eval-name t) ,(first (apply-reduction-relation* ->name (term t)))])

(define-metafunction PCF-list
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])




;;Redex Random testing Trial
(define (progress-holds? e)
  (if (types? e)
      (or (v? e)
          (reduces? e))
      #t))

(define (types? e)
  (not (null? (judgment-holds (⊢_e · ,e t)
                              t))))
 
(define v? (redex-match NPCF v))
 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->name
               (term (,e))))))
