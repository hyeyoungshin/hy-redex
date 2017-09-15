#lang racket

(require redex/reduction-semantics)

(define-language PCF-list 
  ;; Types
  (T Num
     Bool
     (→ T T)
     (List T))
  ;; Programs
  (p (prog (f ...) e))
  ;; Functions
  (f (def x e))
  ;; Terms
  (e (e e)
     (λ (x : T) ... e)
     x
     v
     (nil (T))
     (cons (T) e e)
     (fst (T) e)
     (rst (T) e)
     (nil? e)
     (cons? e)
     (+ e ...)
     (if0 e e e)
     (fix e)
     (def x e) ;;;;;;;;;;;;; should this be just f?
     ;(err t string)
     )
  ;; Values
  (v n
     tt
     ff
     (λ (x : T) ... e)
     (fix v)
     nil (T)
     (cons (T) v ...))
  ;; Numbers
  (n number)
  ;; Variables
  (x variable-not-otherwise-mentioned)

  #:binding-forms
  (λ (x : T) e #:refers-to x)
  
  ;; Type environment
  (Γ ·
     (x : T Γ)))

(define-judgment-form PCF-list
  #:mode (types I I O)
  #:contract (types Γ e T)
  
  [(types Γ e_1 (→ T_2 T_3))
   (types Γ e_2 T_2)
   ------------------------- ;;T-APP
   (types Γ (e_1 e_2) T_3)]
  
  [(types (x : T_1 Γ) e T_2)
   ----------------------------------- ;;T-ABS
   (types Γ (λ (x T_1) e) (→ T_1 T_2))]

  [
   ---------------------;;T-VAR
   (types (x : T Γ) x T)]

  [(types Γ x_1 T_1)
   (side-condition (different x_1 x_2))
   ------------------------------------ ;;T-WEAKENING? (x_2 \notin dom(Γ))
   (types (x_2 : T_2 Γ) x_1 T_1)]

  [
   -------------------------------- ;;T-NIL
   (types Γ (nil (T_1)) (List T_1))]

  [(types Γ e_1 T_1)
   (types Γ e_2 (List T_1))
   --------------------------------------- ;;T-CONS
   (types Γ (cons (T_1) e_1 e_2) (List T_1))]

  [
   ------------------------------- ;; T-NIL?
   (types Γ (nil? (T_1)) Bool)]

  [(types Γ e_1 T_1)
   (types Γ e_2 (List T_1))
   ----------------- ;; T_CONS?
   (types Γ (cons (T_1) e_1 e_2) Bool)]

  [(types Γ e_1 (List T_1))
   --------------------------- ;; T-FST
   (types Γ (fst (T_1) e_1) T_1)]

  [(types Γ e_1 (List T_1))
   --------------------------- ;; T-FST
   (types Γ (rst (T_1) e_1) T_1)]
 
  [
   -------------------- ;;T-NUM
   (types Γ n Num)]
  
  [(types Γ n_1 Num) ...
   ------------------------ ;;T-ADD
   (types Γ (+ n_1 ...) Num)]
  
  [(types Γ e_1 Num)
   (types Γ e_2 T)
   (types Γ e_3 T)
   ----------------------------- ;;T-IF0
   (types Γ (if0 e_1 e_2 e_3) T)]
  
  [(types Γ e_1 (→ T_1 T_1))
   ------------------------ ;;T-FIX
   (types Γ (fix e_1) T_1)]
  
  [
   ----------------- ;;T-TRUE
   (types Γ tt Bool)]

  [
   ----------------- ;;T-FALSE
   (types Γ ff Bool)]
)
  
(define-extended-language NPCF PCF-list
  (P-name (prog (f ...) E-name))
  (E-name hole
          (E-name e)
          (+ v ... E-name e ...)
          (if0 E-name e e)
          (cons (T) v ... E-name e ...)
          (fst (T) E-name)
          (rst (T) E-name)
          (nil? E-name)
          (cons? E-name)
          (fix E-name)))
          

(require redex/tut-subst)
(define-metafunction NPCF
  subst : x v e -> t
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])
(define x? (redex-match NPCF x))

(define ->name
  (reduction-relation
   NPCF
   #:domain p
   (--> (in-hole P-name (if0 0 e_1 e_2))
        (in-hole P-name e_1)
        "if0t-name")
   (--> (in-hole P-name (if0 v e_1 e_2))
        (in-hole P-name e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f-name")
   (--> (in-hole P-name (fst (T) (cons (T) e_1 e_2)))
        (in-hole P-name e_1)
        "fst-cons-name")
   (--> (in-hole P-name (rst (T) (cons (T) e_1 e_2)))
        (in-hole P-name e_2)
        "rst-cons-name")
   (--> (in-hole P-name (fst (T) (nil (T))))
        (in-hole P-name (nil (T)))
        "fst-nil-name")
   (--> (in-hole P-name (rst (T) (nil (T))))
        (in-hole P-name (nil (T)))
        "rst-nil-name")
   (--> (in-hole P-name (cons? (cons (T) e_1 e_2)))
        (in-hole P-name tt)
        "cons?-cons-name")
   (--> (in-hole P-name (cons? (nil (T))))
        (in-hole P-name ff)
        "cons?-nil-name")
   (--> (in-hole P-name ((fix (λ (x : T) e_1)) e_2))
        (in-hole P-name (((λ (x : T) e_1) (fix (λ (x : T) e_1))) e_2))
        "fix-name")
   (--> (in-hole P-name (fix (λ (x: T) e_2)))
        (in-hole P-name (subst x (fix (λ (x: T) e_2)) e_2))
        "fix-beta-name")
   (--> (in-hole P-name ((λ (x : T) e_1) e_2))
        (in-hole P-name (subst x e_2 e_1))
        "beta-name")
   (--> (in-hole P-name (+ n ...))
        (in-hole P-name (∑-name n ...))
        "plus-name")
   (--> (prog ((def x_1 v_1) ... (def x v) (def x_2 v_2) ...)
        (in-hole E-name x))
        (prog ((def x_1 v_1) ... (def x v) (def x_2 v_2) ...)
           (in-hole E-name v))
        "def-name")
   (--> (prog f ... v)
         v
        "halt-name")))
  
(define-metafunction NPCF
  ∑-name : number ... -> number
  [(∑-name number ...)
   ,(apply + (term (number ...)))])

(define-metafunction NPCF
  eval-name : t -> v
  [(eval-name t) ,(first (apply-reduction-relation* ->name (term t)))])

(define-extended-language VPCF PCF-list
  (P-value (prog (f ...) E-value))
  (E-value hole
           (v E-value)
           (E-value e)
           (+ v ... E-value e ...)
           (if0 E-value e e)
           (cons (T) v ... E-value e ...)
           (fst (T) E-value)
           (rst (T) E-value)
           (nil? E-value)
           (cons? E-value))
           (fix E-value))
 
  
(define ->value
  (reduction-relation
   VPCF
   #:domain p
   (--> (in-hole P-value ((λ (x : T) e) v))
        (in-hole P-value (substitute e x v))
        "beta-value")
   (--> (in-hole P-value (if0 0 e_1 e_2))
        (in-hole P-value e_1)
        "if0t-value")
   (--> (in-hole P-value (if0 v e_1 e_2))
        (in-hole P-value e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f-value")
   (--> (in-hole P-value (fst (T) (cons (T) e_1 e_2)))
        (in-hole P-value e_1)
        "fst-cons-value")
   (--> (in-hole P-value (rst (T) (cons (T) e_1 e_2)))
        (in-hole P-value e_2)
        "rst-cons-value")
   (--> (in-hole P-value (fst (T) (nil (T))))
        (in-hole P-value (nil (T)))
        "fst-nil-value")
   (--> (in-hole P-value (rst (T) (nil (T))))
        (in-hole P-value (nil (T)))
        "rst-nil-value")
   (--> (in-hole P-value (cons? (cons (T) e_1 e_2)))
        (in-hole P-value tt)
        "cons?-cons-value")
   (--> (in-hole P-value (cons? (nil (T))))
        (in-hole P-value ff)
        "cons?-nil-value")
   (--> (in-hole P-value ((fix (λ (x : T) e_1)) e_2))
        (in-hole P-value (((λ (x : T) e_1) (fix (λ (x : T) e_1))) e_2))
        "fix-value")
   (--> (in-hole P-value (fix (λ (x: T) e_2)))
        (in-hole P-value (subst x (fix (λ (x: T) e_2)) e_2))
        "fixbeta-value")
   (--> (in-hole P-value (+ number ...))
        (in-hole P-value (∑-value number ...))
        "plus-value")
   (--> (prog ((def x_1 v_1) ... (def x v) (def x_2 v_2) ...)
        (in-hole E-value x))
        (prog ((def x_1 v_1) ... (def x v) (def x_2 v_2) ...)
           (in-hole E-value v))
        "def-value")
   (--> (prog f ... v)
        v
        "halt-value")))

(define-metafunction VPCF
  ∑-value : number ... -> number
  [(∑-value number ...)
   ,(apply + (term (number ...)))])

(define-metafunction VPCF
  eval-value : e -> v
  [(eval-value e) ,(first (apply-reduction-relation* ->value (term e)))])



;;Random testing
(define (progress-holds? e)
  (if (types? e)
      (or (v? e)
          (reduces? e))
      #t))

(define (types? e)
  (not (null? (judgment-holds (types · ,e t)
                              t))))
 
(define v? (redex-match NPCF v))
 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->name
               (term (,e))))))







