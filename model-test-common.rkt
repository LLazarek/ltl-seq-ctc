#lang racket

(require redex rackunit)

(define <=3? (term (λ (x) (zero? (pred (pred (pred x)))))))
(define >3? (term (negate ,<=3?)))
(define <=1? (term (λ (x) (zero? (pred x)))))
(define one (term (succ zero)))
(define two (term (succ ,one)))
(define three (term (succ ,two)))
(define four (term (succ ,three)))

(provide (all-from-out rackunit)
         (all-defined-out))
