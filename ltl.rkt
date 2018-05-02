#lang racket

(require "./dfa.rkt")

(define-syntax-rule (ltl/dfa/exact el)
  (define-dfa/autofail start fail
    [start #f ([el accept])]
    [accept #t ([_ accept])]))

(define-syntax-rule (ltl/exact/c el)
  (λ (seq)
    (dfa-accept? (run (ltl/dfa/exact el) seq))))

(define-syntax-rule (ltl/next/c ltl/after)
  (λ (seq)
    (ltl/after (rest seq))))
