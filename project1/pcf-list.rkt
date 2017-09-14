#lang racket

(require redex/reduction-semantics)

(define-language PCF-list 
  ;; Types
  (T Num
     Bool
     (→ T T)
     (List T))
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
     (+ n ...)
     (if0 e e e)
     ;(def t t)
     (fix e)
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
  
;  [(types Γ (err t string) t)]
;  [(types Γ e (→ (t_0 ...) t))
;   (types Γ e_0 t_0)
;        ...
;   -------------------------- ;;;;;;;;;;;;n-ary application
;   (types Γ (e e_0 ...) t)]
)
  
(define-extended-language NPCF PCF-list
  (p (e ...))
  (P (e ... E-Name e ...))
  (E-Name hole
          (E-Name e)
          (+ v ... E-Name e ...)
          (if0 E-Name e e)
          (cons (T) v ... E-Name e ...)
          (fst (T) E-Name)
          (rst (T) E-Name)
          (nil? E-Name)
          (cons? E-Name)
          (fix E-Name)))
          

(define-metafunction NPCF
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])

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
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "Nif0t")
   (--> (in-hole P (if0 e e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term e))))
        "Nif0f")
   (--> (in-hole P (fst (T) (cons (T) e_1 e_2)))
        (in-hole P e_1)
        "Nfst-cons")
   (--> (in-hole P (rst (T) (cons (T) e_1 e_2)))
        (in-hole P e_2)
        "Nrst-cons")
   (--> (in-hole P (fst (T) (nil (T))))
        (in-hole P (nil (T)))
        "Nfst-nil")
   (--> (in-hole P (rst (T) (nil (T))))
        (in-hole P (nil (T)))
        "Nrst-nil")
   (--> (in-hole P (cons? (cons (T) e_1 e_2)))
        (in-hole P tt)
        "Ncons?-cons")
   (--> (in-hole P (cons? (nil (T))))
        (in-hole P ff)
        "Ncons?-nil")
   (--> (in-hole P ((fix (λ (x : T) e_1)) e_2))
        (in-hole P (((λ (x : T) e_1) (fix (λ (x : T) e_1))) e_2))
        "Nfix")
   (--> (in-hole P (fix (λ (x: T) e_2)))
        (in-hole P (subst x (fix (λ (x: T) e_2)) e_2))
        "Nfix-beta")
   (--> (in-hole P ((λ (x : T) e_1) e_2))
        (in-hole P (subst x e_2 e_1))
        "Nbeta")
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "Nplus")))
   
  


(define-metafunction NPCF
  eval-name : t -> v
  [(eval-name t) ,(first (apply-reduction-relation* ->name (term t)))])



;(define-extended-language Ev L+Γ
;  (p (e ...))
;  (P (e ... E e ...))
;  (E (v E)
;     (E e)
;     (+ v ... E e ...)
;     (if0 E e e)
;     (fix E)
;     hole)
;  (v (λ (x t) e)
;     (fix v)
;     number))



(define-extended-language VPCF PCF-list
  (p (e ...))
  (P (e ... E-Value e ...))
  (E-Value hole
           (v E-Value)
           (E-Value e)
           (+ v ... E-Value e ...)
           (cons (T) v ... E-Value e ...)
           (fst (T) E-Value)
           (rst (T) E-Value)
           (nil? E-Value)
           (cons? E-Value))
           (if0 E-Value e e)
           (fix E-Value))
 
  
(define ->value
  (reduction-relation
   VPCF
   #:domain e
   (--> (in-hole P ((lambda (x) e) v))
        (in-hole P (substitute e x v))
        "Vbeta")
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "Vif0t")
   (--> (in-hole P (if0 e e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term e))))
        "Vif0f")
   (--> (in-hole P (fst (T) (cons (T) e_1 e_2)))
        (in-hole P e_1)
        "Vfst-cons")
   (--> (in-hole P (rst (T) (cons (T) e_1 e_2)))
        (in-hole P e_2)
        "Vrst-cons")
   (--> (in-hole P (fst (T) (nil (T))))
        (in-hole P (nil (T)))
        "Vfst-nil")
   (--> (in-hole P (rst (T) (nil (T))))
        (in-hole P (nil (T)))
        "Vrst-nil")
   (--> (in-hole P (cons? (cons (T) e_1 e_2)))
        (in-hole P tt)
        "Vcons?-cons")
   (--> (in-hole P (cons? (nil (T))))
        (in-hole P ff)
        "Vcons?-nil")
   (--> (in-hole P ((fix (λ (x : T) e_1)) e_2))
        (in-hole P (((λ (x : T) e_1) (fix (λ (x : T) e_1))) e_2))
        "Vfix")
   (--> (in-hole P (fix (λ (x: T) e_2)))
        (in-hole P (subst x (fix (λ (x: T) e_2)) e_2))
        "Vfixbeta")
   (--> (in-hole P (+ e_1 e_2))
        (in-hole P ,(+ (term e_1) (term e_2)))
        "VPlus")))



(define-metafunction VPCF
  eval-value : e -> v
  [(eval-value e) ,(first (apply-reduction-relation* ->value (term e)))])

     







