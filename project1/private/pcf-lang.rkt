#lang racket

(provide define-language)

;; Defines a language like `PCF` in terms of a Redex reduction
;; like `PCF1` --- given the grammar and a pattern for recognizing
;; definitions.

(define-syntax-rule
  (define-language
    #:module-name lang-module-name
    #:reductions (reduction)
    #:grammar grammar-id
    #:defn-pattern defn-pattern
    #:type-judgment ⊢_p)
  ;; ==> 
  (begin
    
    (provide
     reduction
     #%datum
     (rename-out
      [top-interaction #%top-interaction]
      [module-begin    #%module-begin]))

    ;; -----------------------------------------------------------------------------------------------
    ;; dependencies

    (require project1/private/pcfs
             (for-syntax racket/base)
             (for-syntax syntax/parse)
             redex/reduction-semantics)

    ;; -----------------------------------------------------------------------------------------------
    ;; implementation

    (define-syntax (top-interaction stx)
      (syntax-case stx ()
        [(_ . e)
         #`(#%top-interaction . (run-all grammar-id reduction (prog ,@definitions e)))]))

    (define-syntax (module-begin stx)
      (syntax-parse stx
        [(_ defns:id e (... ...)) ; the `defns` identifier is added by the reader
         #`(#%module-begin
            (define defns (filter (redex-match? grammar-id defn-pattern) (term (e (... ...)))))
            (run grammar-id reduction ⊢_p (prog e (... ...))))]))

    ;; -----------------------------------------------------------------------------------------------
    ;; reader

    (module reader syntax/module-reader
      lang-module-name

      ;; the next three are needed 
      #:read
      read
      #:read-syntax
      read-syntax
      #:wrapper1
      (lambda (x) (cons 'definitions (x))) ; include `definitions` as if in the original
      
      ;; this provides you wit a stepper button for redex (good for debugging)
      #:info
      (lambda (key default default-filter)
        ;; area% -> void 
        (define (add-stepper-button-to-window drr-window)
          (define mod ;; retrieve program text object from DrRacket window 
            (with-module-reading-parameterization
                (lambda ()
                  (read (open-input-string (send (send drr-window get-definitions-text) get-text))))))
          (stepper
           (dynamic-require 'lang-module-name 'reduction)
           ;; the next step should reuse the above pattern 
           (match mod
             [`(module ,_ ,_
                 (#%module-begin
                  definitions
                  ,defs (... ...))) (term (prog ,@defs))])))
        ;; -- in -- 
        (case key
          [(drracket:toolbar-buttons)
           (list
            (list
             "Redex Stepper"
             (make-object bitmap% 16 16) ; a 16 x 16 white square
             add-stepper-button-to-window))]
          [else default]))
      
      (require racket/class racket/match redex syntax/modread racket/draw))))

(require "../pcf-list.rkt")

#;
(define-language
  #:module-name   project1/VPCF
  #:reductions    (->value)
  #:grammar       PCF-list
  #:defn-pattern  (defun (x_1 T_1) e_1))
