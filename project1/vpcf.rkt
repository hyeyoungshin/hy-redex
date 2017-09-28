#lang racket/base

(require "private/pcf-lang.rkt")
(require "pcf-list.rkt")

(define-language
  #:module-name   project1/VPCF
  #:reductions    (->value)
  #:grammar       VPCF
  #:defn-pattern  (defun (x_1 T_1) e_1)
  #:type-judgment ⊢_p)
