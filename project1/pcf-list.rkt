#lang racket

(require redex/reduction-semantics)

(define-language PCF-list 
  ;; Types
  (t ::= num
         bool
         (→ t t)
         (list t ...))
  ;; Terms
  (e ::= (e e)
         (λ (x t) e)
         x
         v
         (list e ...)
         number
         (+ e ...)
         (if0 e e e)
         (fix e)
         ;(err t string)
         )
  ;; Values
  (v ::= n
         tt
         ff
         (λ (x t) ... e)
         (list v ...))
  ;; Numbers
  (n ::= number)
  ;; Operations
  (o ::= cons
         fst
         lst
         +
         ;;;;;;;;;;;;;;;;;;;;;;;;;;should be able to compute length of a list
         )
  ;; Variables
  (x ::= variable-not-otherwise-mentioned)
  ;; Type environment
  (Γ ::= ·
         (x : t Γ)))

(define-judgment-form PCF-list
  #:mode (types I I O)
  #:contract (types Γ e t)
  
  [(types Γ e_1 (→ t_2 t_3))
   (types Γ e_2 t_2)
   ------------------------- ;;;;;;;;;;;;;application
   (types Γ (e_1 e_2) t_3)]
  [(types (x  t_1 Γ) e t_2)
   ----------------------------------- ;;;abstraction
   (types Γ (λ (x t_1) e) (→ t_1 t_2))]
  [---------------------;;;;;;;;;;;;;;;;;;variable
   (types (x : t Γ) x t)]
  [(types Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (types (x_2 : t_2 Γ) x_1 t_1)]
   [(types Γ e t) ...
   --------------------------;;;;;;;;;;;;;;;;;;;can I just do list(t)?
   (types Γ (list e ...) (list t ...))]
;  [(types Γ e_1 t_1)
;   (types Γ e_2 t_2) ...
;   --------------------------;;;;;;;;;;;;;;;;;;;list(t_1 t_2 ...)?
;   (types Γ (list e_1 e_2 ...) (list t_1 t_2 ...))]
  [--------------------;;;;;;;;;;;;;;;;;;;;;;;;;num
   (types Γ number num)]
  [(types Γ e num) ...
   -----------------------;;;;;;;;;;;;;;;;;;;;;;add
   (types Γ (+ e ...) num)]
  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   -----------------------------;;;;;;;;;;;;;;;;if0
   (types Γ (if0 e_1 e_2 e_3) t)]
  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ---------------------------------------;;;;;;fix
   (types Γ (fix e) (→ t_1 t_2))]
  [-----------------
   (types Γ tt bool)]
  [-----------------
   (types Γ ff bool)]
;  [(types Γ (err t string) t)]
;  [(types Γ e (→ (t_0 ...) t))
;   (types Γ e_0 t_0)
;        ...
;   -------------------------- ;;;;;;;;;;;;n-ary application
;   (types Γ (e e_0 ...) t)]
)
  
(define-extended-language PCF-list-name PCF-list
  (E-name ::=
          hole
          (E-name e)))

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
   (--> (in-hole E-name (n_1 + n_2))
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

     







