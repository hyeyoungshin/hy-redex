#lang racket

;; -----------------------------------------------------------------------------
(provide run)

;; -----------------------------------------------------------------------------
(require redex)

;; -----------------------------------------------------------------------------
(define-syntax-rule
  (run syntax reduction Γ_0 ⊢_pxxx e)
  (let/ec return
    (displayln (term e))
    (when (not (redex-match? syntax p (term e)))
      (return 'syntax-error))
    (define the-type (judgment-holds (⊢_pxxx Γ_0 e T) T))
    (when (not the-type)
      (return 'type-error))
    ;; else:
    (define results (apply-reduction-relation* reduction (term e)))
    (define the-result
      (cond
        [(empty? results)
         ; Infinite loop detected!
         ; The programmer asked for an infinite loop, so let's give them one.
         (let loop () (loop))]
        [(empty? (rest results)) (car results)]
        [else (displayln `(warning: ambiguous outcome))
              (for ([i results]) (displayln `(--> ,i)))
              (car results)]))
    ;; now deal with result
    (match the-result
      [`(prog ,d (... ...) ,v) (list* v ': the-type)]
      [else `(strange value ,results)])))

