#lang racket

(require "../ltl-nodfa.rkt" "test.rkt" "test-defs.rkt")

(define man/p (primitive/first number?))
(define man/X-num (c/next (primitive/first number?)))
(define man/num-U-even (c/until (primitive/first number?)
                                (primitive/first even-number?)))
(define man/not-num (c/not (primitive/first number?)))
(define man/neg-or-even (c/or (primitive/first negative-number?)
                              (primitive/first even-number?)))
(define man/pos-and-even (c/and (primitive/first positive-number?)
                                (primitive/first even-number?)))
(define man/num=>even (c/implies (primitive/first number?)
                                 (primitive/first even-number?)))
(define man/num<=>X-even (c/iff (primitive/first number?)
                                (c/next (primitive/first even-number?))))
(define man/even-R-num (c/release (primitive/first even-number?)
                                  (primitive/first number?)))
(define man/F-num (c/eventually (primitive/first number?)))
(define man/G-num (c/globally (primitive/first number?)))
(define man/compound (c/or (c/until (primitive/first number?)
                                    (primitive/first negative-number?))
                           (c/next (c/next (primitive/first number?)))))


(module+ test
  (require "../test-common.rkt")

  ;; Tests verifying parity between generated ltl formulas and
  ;; manually constructed ones

  (check-runs* (ltl/p man/p) :  -> ?)
  (check-runs* (ltl/p man/p) : 1 -> t)
  (check-runs* (ltl/p man/p) : 1 a -> t)
  (check-runs* (ltl/p man/p) : a -> f)
  (check-runs* (ltl/p man/p) : a 1 -> f)

  (check-runs* (ltl/X-num man/X-num) :  -> ?)
  (check-runs* (ltl/X-num man/X-num) : a -> ?)
  (check-runs* (ltl/X-num man/X-num) : a 1 -> t)
  (check-runs* (ltl/X-num man/X-num) : a 1 c -> t)
  (check-runs* (ltl/X-num man/X-num) : a b -> f)
  (check-runs* (ltl/X-num man/X-num) : a b 3 -> f)
  
  (check-runs* (ltl/num-U-even man/num-U-even) :  -> ?)
  (check-runs* (ltl/num-U-even man/num-U-even) : 1 -> ?)
  (check-runs* (ltl/num-U-even man/num-U-even) : 1 3 -> ?)
  (check-runs* (ltl/num-U-even man/num-U-even) : 2 -> t)
  (check-runs* (ltl/num-U-even man/num-U-even) : 1 2 -> t)
  (check-runs* (ltl/num-U-even man/num-U-even) : 1 2 #f -> t)
  (check-runs* (ltl/num-U-even man/num-U-even) : #f -> f)
  (check-runs* (ltl/num-U-even man/num-U-even) : 1 3 #f -> f)

  (check-runs* (ltl/not-num man/not-num) :  -> ?)
  (check-runs* (ltl/not-num man/not-num) : 1 -> f)
  (check-runs* (ltl/not-num man/not-num) : 1 a -> f)
  (check-runs* (ltl/not-num man/not-num) : a -> t)
  (check-runs* (ltl/not-num man/not-num) : a 1 -> t)

  (check-runs* (ltl/neg-or-even man/neg-or-even) :  -> ?)
  (check-runs* (ltl/neg-or-even man/neg-or-even) : -1 -> t)
  (check-runs* (ltl/neg-or-even man/neg-or-even) : 2 -> t)
  (check-runs* (ltl/neg-or-even man/neg-or-even) : 1 -> f)
  (check-runs* (ltl/neg-or-even man/neg-or-even) : a -> f)
  
  (check-runs* (ltl/pos-and-even man/pos-and-even) :  -> ?)
  (check-runs* (ltl/pos-and-even man/pos-and-even) : 2 -> t)
  (check-runs* (ltl/pos-and-even man/pos-and-even) : -2 -> f)
  (check-runs* (ltl/pos-and-even man/pos-and-even) : -1 -> f)
  (check-runs* (ltl/pos-and-even man/pos-and-even) : 1 -> f)
  
  (check-runs* (ltl/num=>even man/num=>even) :  -> ?)
  (check-runs* (ltl/num=>even man/num=>even) : 2 -> t)
  (check-runs* (ltl/num=>even man/num=>even) : a -> t)
  (check-runs* (ltl/num=>even man/num=>even) : 1 -> f)
  
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) :  -> ?)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : 1 -> ?)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : a -> ?)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : 1 2 -> t)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : 1 3 -> f)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : a 2 -> f)
  (check-runs* (ltl/num<=>X-even man/num<=>X-even) : a 3 -> t)
  
  (check-runs* (ltl/even-R-num man/even-R-num) :  -> ?)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 -> ?)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 3 5 -> ?)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 3 5 2 -> t)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 3 5 2 a -> t)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 #f -> f)
  (check-runs* (ltl/even-R-num man/even-R-num) : 1 #f 3 2 -> f)
  
  (check-runs* (ltl/F-num man/F-num) :  -> ?)
  (check-runs* (ltl/F-num man/F-num) : a -> ?)
  (check-runs* (ltl/F-num man/F-num) : a #f -> ?)
  (check-runs* (ltl/F-num man/F-num) : a #f 1 -> t)
  (check-runs* (ltl/F-num man/F-num) : 1 -> t)
  
  (check-runs* (ltl/G-num man/G-num) :  -> ?)
  (check-runs* (ltl/G-num man/G-num) : 1 -> ?)
  (check-runs* (ltl/G-num man/G-num) : 1 2 -> ?)
  (check-runs* (ltl/G-num man/G-num) : 1 2 3 4 -1 5 200 -> ?)
  (check-runs* (ltl/G-num man/G-num) : 1 2 3 4 #f -1 5 200 -> f)
  (check-runs* (ltl/G-num man/G-num) : a -> f)

  (check-runs* (ltl/compound man/compound) :  -> ?)
  (check-runs* (ltl/compound man/compound) : 1 2 -> ?)
  (check-runs* (ltl/compound man/compound) : a -> ?)
  (check-runs* (ltl/compound man/compound) : a b c -> f)
  (check-runs* (ltl/compound man/compound) : 1 2 5 -2 -> t)
  (check-runs* (ltl/compound man/compound) : 1 2 5 -2 #f -> t)
  (check-runs* (ltl/compound man/compound) : 1 2 a -> f)
  (check-runs* (ltl/compound man/compound) : a b 5 -> t)
  (check-runs* (ltl/compound man/compound) : 1 2 5 -> t))