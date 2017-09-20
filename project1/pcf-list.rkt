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

  ;; Type environment
  (Γ ·
     (Γ (x T) ...))
    #:binding-forms
  (λ (x T) e #:refers-to x)
  )

(define-judgment-form PCF-list
  #:mode (⊢_p I I O)
  #:contract (⊢_p Γ p T)
  [(⊢_e (Γ (x_1 T_1) ...) v_1 T_1) ...
   (⊢_e (Γ (x_1 T_1) ...) e T)
   ------------------------------------------
   (⊢_p Γ (prog (def (x_1 T_1) v_1) ... e) T)]
)
  
;  [(⊢_e (Γ (x_1 T_1) (x_2 T_2) ... (x_n T_n)) v_1 T_1)
;   (⊢_e (Γ (x_1 T_1) (x_2 T_2) ... (x_n T_n)) v_2 T_2) ...
;   (⊢_e (Γ (x_1 T_1) (x_2 T_2) ... (x_n T_n)) v_n T_n)
;   (⊢_e (Γ (x_1 T_1) (x_2 T_2) ... (x_n T_n)) e T)
;   ---------------------------------------------------------------------------------- "T-PROG"
;   (⊢_p Γ (prog (def (x_1 T_1) v_1) (def (x_2 T_2) v_2) ... (def (x_n T_n) v_n) e) T)]
;)

(module+ test
   (require chk)
  (chk
   #:t (redex-match? PCF-list Γ (term ·))
   #:t (redex-match? PCF-list n (term 2))
   #:t (redex-match? PCF-list p (term (prog (def (x Num) 2) 2)))
   #:= (judgment-holds (⊢_e (· (x Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e ((· (x Num)) (y Num)) x T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e (· (x Num)) 1 T) T)
   (list (term Num))
   #:= (judgment-holds (⊢_e (· (x Num)) (+ x 1) T) T)
   (list (term Num))
   #:= 
   (judgment-holds (⊢_p · (prog (def (x Num) 2) (+ x 1)) T) T)
   (list (term Num))
  ))

(define-judgment-form PCF-list
  #:mode (⊢_e I I O)
  #:contract (⊢_e Γ e T) 
  [------------- "T-TRUE"
   (⊢_e Γ tt Bool)]

  [------------- "T-FALSE"
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

  [(⊢_e (Γ [(x_1 T_1) (x_2 T_2) ... (x_n T_n)]) v_1 T_1)
   (⊢_e (Γ [(x_1 T_1) (x_2 T_2) ... (x_n T_n)]) v_2 T_2) ...
   (⊢_e (Γ [(x_1 T_1) (x_2 T_2) ... (x_n T_n)]) v_n T_n)
   (⊢_e (Γ [(x_1 T_1) (x_2 T_2) ... (x_n T_n)]) e T)
   ---------------------------------------------------------------------------------- "T-PROG"
   (⊢_e Γ (prog (def (x_1 T_1) v_1) (def (x_2 T_2) v_2) ... (def (x_n T_n) v_n) e) T)]

  [(⊢_e Γ x_2 T_1)
   ------------------------------------ "T-WEAK" 
   (⊢_e (Γ (x_!_1 T_2)) (name x_2 x_!_1) T_1)]

  [
   ------------------------------------ "T-VAR" 
   (⊢_e (Γ (x_1 T_1)) x_1 T_1)]

  [(⊢_e Γ e_1 (→ T_1 T_1))
   --------------------- "T-FIX"
   (⊢_e Γ (fix e_1) T_1)]
  
  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 Num)
   --------------------- "T-SUM"
   (⊢_e Γ (+ e_1 e_2) Num)]

  [(⊢_e Γ e_1 Num)
   (⊢_e Γ e_2 Num)
   --------------------- "T-SUB"
   (⊢_e Γ (- e_1 e_2) Num)]

  [(⊢_e Γ e_1 T_1)
   (⊢_e Γ e_2 (List T_1))
   ------------------------------- "T-CONS"
   (⊢_e Γ (cons e_1 e_2) (List T_1))]

  [(⊢_e Γ e_1 (List T_1))
   ------------------- "T-FST"
   (⊢_e Γ (fst e_1) T_1)]

  [(⊢_e Γ e_1 (List T_1))
   -------------------------- "T-RST"
   (⊢_e Γ (rst e_1) (List T_1))]

  [(⊢_e Γ e_1 T_1)
   (⊢_e Γ e_2 (List T_1))
   -------------------------- "T_CONS?"
   (⊢_e Γ (cons? e_1 e_2) Bool)]

  [(⊢_e Γ e_1 (List T))
   ------------------------------- "T-NIL?"
   (⊢_e Γ (nil? e_1) Bool)]


  [
   -------------------------------- "T-NIL"
   (⊢_e · (nil (T_1)) (List T_1))]


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
   (--> (in-hole P-value ((λ (x T) e_1) v_1)) 
        (in-hole P-value (subst e_1 x v_1))  
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
