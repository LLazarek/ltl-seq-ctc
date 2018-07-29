#lang racket

(require "common.rkt" rackunit)

(define-syntax (check-runs stx)
    (syntax-case stx (: ->)
      [(check-runs consumer : seq ... -> res)
       (syntax/loc stx
         (check-equal? (run-consumer consumer '(seq ...)) 'res))]))

(define-syntax (check-runs* stx)
    (syntax-case stx (: ->)
      [(check-runs/parallel (c1 ...) : seq ... -> res)
       (syntax/loc stx
         (begin
           (check-equal? (run-consumer c1 '(seq ...)) 'res)
           ...))]))

(provide [all-from-out rackunit]
         check-runs
         check-runs*)
