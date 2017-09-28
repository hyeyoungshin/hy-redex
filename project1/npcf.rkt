#lang racket/base

(require "private/pcf-lang.rkt")
(require "pcf-list.rkt")

(define-language
  #:module-name   project1/NPCF
  #:reductions    (->name)
  #:grammar       NPCF
  #:defn-pattern  (def (x_1 T_1) e_1)
  #:type-judgment ⊢_np)
