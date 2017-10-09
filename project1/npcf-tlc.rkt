#lang racket/base

(require "private/pcf-lang.rkt")
(require "pcf-list-tlc.rkt")

(define-language
  #:module-name   project1/NPCF-tlc
  #:reductions    (->name)
  #:grammar       NPCF
  #:defn-pattern  (def x_1 : T_1 v_1)
  #:type-judgment ⊢_np)
