#lang racket

(define even-number? (and/c number? even?))
(define negative-number? (and/c number? negative?))
(define positive-number? (and/c number? positive?))
(provide number? even-number? negative-number? positive-number?)
