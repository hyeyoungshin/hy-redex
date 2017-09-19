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
  (e v  ;tt|ff|n
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
     (err T string))
  ;; Numbers
  (n number)
  ;; Variables
  (x variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x T) e #:refers-to x)
  ;; Type environment
  (Γ ·
     (Γ (x T)))
  )

(define-judgment-form PCF-list
  #:mode (⊢ I I O)
  #:contract (⊢ Γ e T) 
  [------------- "T-TRUE"
   (⊢ · tt Bool)]

  [------------- "T-FALSE"
   (⊢ · ff Bool)]

  [------------- "T-NUM"
   (⊢ · n Num)]

  [(⊢ (Γ (x_1 T_1)) e_2 T_2)
   ----------------------------------- "T-ABS"
   (⊢ Γ (λ (x_1 T_1) e_2) (→ T_1 T_2))]
  
  [(⊢ Γ e_1 (→ T_1 T_2))
   (⊢ Γ e_2 T_1)
   ------------------------- "T-APP"
   (⊢ Γ (e_1 e_2) T_2)]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"T-PROG" or "T-DEF"

  [(⊢ Γ x_1 T_1)
   (side-condition (different x_1 x_2))
   ------------------------------------ "T-VAR" 
   (⊢ (Γ (x_2 T_2)) x_1 T_1)]

  [(⊢ Γ e_1 (→ T_1 T_1))
   --------------------- "T-FIX"
   (⊢ Γ (fix e_1) T_1)]
  
  [(⊢ Γ e_1 Num)
   (⊢ Γ e_2 Num)
   --------------------- "T-SUM"
   (⊢ Γ (+ e_1 e_2) Num)]

  [(⊢ Γ e_1 Num)
   (⊢ Γ e_2 Num)
   --------------------- "T-SUB"
   (⊢ Γ (- e_1 e_2) Num)]

  [(⊢ Γ e_1 T_1)
   (⊢ Γ e_2 (List T_1))
   ------------------------------- "T-CONS"
   (⊢ Γ (cons e_1 e_2) (List T_1))]

  [(⊢ Γ e_1 (List T_1))
   ------------------- "T-FST"
   (⊢ Γ (fst e_1) T_1)]

  [(⊢ Γ e_1 (List T_1))
   -------------------------- "T-RST"
   (⊢ Γ (rst e_1) (List T_1))]

  [(⊢ Γ e_1 T_1)
   (⊢ Γ e_2 (List T_1))
   -------------------------- "T_CONS?"
   (⊢ Γ (cons? e_1 e_2) Bool)]

  [(⊢ Γ e_1 (List T))
   ------------------------------- "T-NIL?"
   (⊢ Γ (nil? e_1) Bool)]


  [
   -------------------------------- "T-NIL"
   (⊢ · (nil (T_1)) (List T_1))]


  [(⊢ Γ e_1 Num)
   (⊢ Γ e_2 T)
   (⊢ Γ e_3 T)
   ----------------------------- "T-IF0"
   (⊢ Γ (if0 e_1 e_2 e_3) T)]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-extended-language VPCF PCF-list
  (v (cons v v))
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
   (--> (in-hole P-value ((λ (x T) e_1) v_1)) ;;Does this enforce a value 
        (in-hole P-value (subst e_1 x v_1))   ;;for an argument?
        "EV-beta")
   (--> (in-hole P-value (fix (λ (x T) e_1)))
        (in-hole P-value (subst x (fix (λ (x T) e_1)) e_1))
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
   (--> (prog ((def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...)
           (in-hole E-value x))
        (prog ((def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...)
           (in-hole E-value v))
        "EV-def")
   (--> (prog f ... v)
        v
        "EV-halt")
  )
 )

;(define-metafunction VPCF
;  EV-∑ : number ... -> number
;  [(EV-∑ number ...)
;   ,(apply + (term (number ...)))])

(define-metafunction VPCF
  eval-value : e -> v
  [(eval-value e) ,(first (apply-reduction-relation* ->value (term e)))])


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
   (--> (prog ((def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...)
           (in-hole E-name x))
        (prog ((def (x_1 T_1) v_1) ... (def (x T) v) (def (x_2 T_2) v_2) ...)
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




;;Redex Random testing Trial
(define (progress-holds? e)
  (if (types? e)
      (or (v? e)
          (reduces? e))
      #t))

(define (types? e)
  (not (null? (judgment-holds (⊢ · ,e t)
                              t))))
 
(define v? (redex-match NPCF v))
 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               ->name
               (term (,e))))))