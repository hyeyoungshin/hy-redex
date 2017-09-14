#lang racket

(require redex/reduction-semantics)

(define-language PCF-list 
  ;; Types
  (T Num
     Bool
     (→ T T)
     (List T))
  ;; Terms
  (t (t t)
     (λ (x T) ... t)
     x
     v
     nil (T)
     (cons (T) t t)
     (fst (T) t)
     (rst (T) t)
     (nil? t)
     (cons? t)
     (+ n ...)
     (if0 t t t)
     ;(def t t)
     (fix t)
     ;(err t string)
     )
  ;; Values
  (v n
     tt
     ff
     (λ (x T) ... t)
     (fix v)
     nil (T)
     (cons (T) v ...))
  ;; Numbers
  (n number)
  ;; Operations
;;  (o cons
;;     fst
;;     lst
;;     +
;;     ;;;;;;;;;;;;;;;;;;;;;;;;;;should be able to compute length of a list
;;     )
  ;; Variables
  (x variable-not-otherwise-mentioned)
  ;; Type environment
  (Γ ·
     (x : T Γ)))

(define-judgment-form PCF-list
  #:mode (types I I O)
  #:contract (types Γ t T)
  
  [(types Γ t_1 (→ T_2 T_3))
   (types Γ t_2 T_2)
   ------------------------- ;;T-APP
   (types Γ (t_1 t_2) T_3)]

  [(types (x : T_1 Γ) t T_2)
   ----------------------------------- ;;T-ABS
   (types Γ (λ (x T_1) t) (→ T_1 T_2))]

  [
   ---------------------;;T-VAR
   (types (x : T Γ) x T)]

  [(types Γ x_1 T_1)
   (side-condition (different x_1 x_2))
   ------------------------------------ ;;T-WEAKENING? (x_2 \notin dom(Γ))
   (types (x_2 : T_2 Γ) x_1 T_1)]

  [
   ---------------------------- ;;T-NIL
   (types Γ nil (T_1) list T_1)]

  [(types Γ t_1 T_1)
   (types Γ t_2 list T_1)
   --------------------------------------- ;;T-CONS
   (types Γ (cons (T_1) t_1 t_2) list T_1)]

  [(types Γ t_1 List T_1)
   ------------------------------- ;; T-NIL?
   (types Γ nil? (T_1) t_1 Bool)]

  [(types Γ t_1 T_1)
   ----------------- ;; T_CONS?
   (types Γ cons (T_1) t_1 Bool)]

  [(types Γ t_1 List T_1)
   --------------------------- ;; T-FST
   (types Γ fst (T_1) t_1 T_1)]

  [(types Γ t_1 List T_1)
   --------------------------- ;; T-FST
   (types Γ rst (T_1) t_1 T_1)]
 
  [
   -------------------- ;;T-NUM
   (types Γ n Num)]
  
  [(types Γ n_1 Num) ...
   ------------------------ ;;T-ADD
   (types Γ (+ n_1 ...) Num)]
  
  [(types Γ t_1 Num)
   (types Γ t_2 T)
   (types Γ t_3 T)
   ----------------------------- ;;T-IF0
   (types Γ (if0 t_1 t_2 t_3) T)]
  
  [(types Γ t_1 (→ T_1 T_1))
   ------------------------ ;;T-FIX
   (types Γ (fix t_1) T_1)]
  
  [
   ----------------- ;;T-TRUE
   (types Γ tt Bool)]

  [
   ----------------- ;;T-FALSE
   (types Γ ff Bool)]
  
;  [(types Γ (err t string) t)]
;  [(types Γ e (→ (t_0 ...) t))
;   (types Γ e_0 t_0)
;        ...
;   -------------------------- ;;;;;;;;;;;;n-ary application
;   (types Γ (e e_0 ...) t)]
)
  
(define-extended-language PCF-list-name PCF-list
  (p (t ...))
  (P (t ... E t ...))
  (E-name hole
        (v E)
        (E e)
        (+ v ... E e ...)
        (if0 E e e)
        (fix E)))

(define-metafunction PCF-list-name
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])

(require redex/tut-subst)
(define-metafunction PCF-list-name
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])
(define x? (redex-match PCF-list-name x))


(define ->name
  (reduction-relation
   PCF-list-name
   #:domain p
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "if0t")
   (--> (in-hole P (if0 v e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f")
   (--> (in-hole P ((fix (λ (x t) e)) v))
        (in-hole P (((λ (x t) e) (fix (λ (x t) e))) v))
        "fix")
   (--> (in-hole P ((λ (x t) e) v))
        (in-hole P (subst x v e))
        "βv")
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "+")
   (--> (e_1 ... (in-hole E (amb e_2 ...)) e_3 ...)
        (e_1 ... (in-hole E e_2) ... e_3 ...)
        "amb")))


(define ->name
  (reduction-relation
   PCF-list-name
   #:domain e
   (--> (in-hole E-name ((lambda (x) e_1) e_2))
        (in-hole E-name (substitute e_1 x e_2))
        beta-name)
   (--> (in-hole E-name (if tt e_1 e_2))
        (in-hole E-name e_1)
        if-tt-name)
   (--> (in-hole E-name (if ff e_1 e_2))
        (in-hole E-name e_2)
        if-ff-name)
   (--> (in-hole E-name (+ n_1 n_2))
        (in-hole E-name ,(+ (term n_1) (term n_2)))
        plus-name)))

  


(define-metafunction PCF-list-name
  eval-name : e -> v
  [(eval-name e) ,(first (apply-reduction-relation* ->name (term e)))])






(define-extended-language PCF-list-value PCF-list
  (E-value ::=
          hole
          (E-value e)
          ((lambda (x) e) E-value)))

(define ->value
  (reduction-relation
   PCF-list-value
   #:domain e
   (--> (in-hole E-value ((lambda (x) e) v))
        (in-hole E-value (substitute e x v))
        beta-value)
   (--> (in-hole E-value (if tt e_1 e_2))
        (in-hole E-value e_1)
        if-tt-value)
   (--> (in-hole E-value (if ff e_1 e_2))
        (in-hole E-value e_2)
        if-ff-value)
   (--> (in-hole E-value (n_1 + n_2))
        (in-hole E-value ,(+ (term n_1) (term n_2)))
        plus-value)))
  


(define-metafunction PCF-list-value
  eval-value : e -> v
  [(eval-value e) ,(first (apply-reduction-relation* ->value (term e)))])

     







