#lang racket/base

(require "private/pcf-lang.rkt")
(require "pcf-list-tlc.rkt")

(define-language
  #:module-name   project1/VPCF-tlc
  #:reductions    (->value)
  #:grammar       VPCF
  #:defn-pattern  (def x_1 : T_1 e_1)
  #:type-judgment ⊢_vp)