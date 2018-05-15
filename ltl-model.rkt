#lang racket

(require redex)

(define-language ltl-lang
  [ltl true
     false
     (first p)
     (all p)
     (not ltl)
     (or ltl)
     (next ltl)
     (until ltl ltl)]
  [p ??? #| todo: Any predicate: don't know how to encode |#]
  [seq empty
       (cons seq-el seq)]
  [seq-el ??? #| todo: Anything: don't know how to encode |#]
  [r #t
     #f]
  [ltl-state (state ltl r seq)]) ;; No ctxs because sub-formula
                                 ;; reduction doesn't make sense.


;; How to encode consuming elements of a sequence on each step?
;; -> try having the sequence as part of the state
(define ltl-red
  (reduction-relation
   ltl-lang
   (--> (state true r (cons seq-el seq))
        (state true #t seq)
        r-true)

   (--> (state false r (cons seq-el seq))
        (state false #f seq)
        r-false)

   (--> (state (first p) r (cons seq-el seq))
        (state true #t seq)
        #:if (p seq-el) ;; todo: is this how to write rule premises?
                        ;; Also multiple ones below.
        r-first-t)
   (--> (state (first p) r (cons seq-el seq))
        (state false #f seq)
        #:if (not (p seq-el))
        r-first-t)

   (--> (state (all p) r (cons seq-el seq))
        (state (all p) #t seq)
        #:if (p seq-el)
        r-all-t)
   (--> (state (all p) r (cons seq-el seq))
        (state false #f seq)
        #:if (not (p seq-el))
        r-all-f)


   (--> (state (not ltl_0) r_0 (cons seq-el seq))
        (state (not ltl_1) ,(not r_1) seq)
        #:if (--> (state ltl_0 r_0 (cons seq-el seq))
                  (state ltl_1 r_1 seq))
        r-not)

   (--> (state (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (state (or ltl_A_1 ltl_B_1) ,(or r_A r_B) seq)
        #:if (--> (state ltl_A_0 r_0 (cons seq-el seq))
                  (state ltl_A_1 r_A seq))
        #:if (--> (state ltl_B_0 r_0 (cons seq-el seq))
                  (state ltl_B_1 r_B seq))
        r-or)

   (--> (state (next ltl) r (cons seq-el seq))
        (state ltl #f seq)
        r-next)

   (--> (state (until ltl_A_0 ltl_B_0) r (cons seq-el seq))
        (state ltl_B_1 #t seq)
        #:if (--> (state ltl_B_0 r (cons seq-el seq))
                  (state ltl_B_1 #t seq))
        r-until-start-B)
   (--> (state (until ltl_A_0 ltl_B_0) r (cons seq-el seq))
        (state (until ltl_A_1 ltl_B_0) r_A seq)
        #:if (--> (state ltl_B_0 r (cons seq-el seq))
                  (state ltl_B_1 #f seq))
        #:if (--> (state ltl_A_0 r (cons seq-el seq))
                  (state ltl_A_1 r_A seq))
        r-until-still-A)))
