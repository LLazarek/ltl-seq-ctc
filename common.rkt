#lang racket

(provide world/c
         result/c
         consumer/c
         run-consumer)

(define world/c any/c)
(define result/c (or/c 't 'f '?))

;; An ltl formula's encoding is a Consumer
(define consumer/c
  (-> world/c (values result/c (recursive-contract consumer/c))))

(define/contract (run-consumer generator seq [init '?])
  (->* (consumer/c (listof world/c))
       (result/c)
       result/c)

  (if (empty? seq)
      init
      (let-values ([(accept? next-consumer) (generator (first seq))])
        (run-consumer next-consumer (rest seq) accept?))))

