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
  [p ??? #| todo: how to encode any predicate? |#]
  [seq empty
       (cons seq-el seq)]
  [seq-el ??? #| todo: how to encode anything? |#]
  [r #t
     #f]
  [ltl-state (state ltl r seq)]) ;; No ctxs because sub-formula
                                 ;; reduction doesn't make sense.


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
        ;; todo: is this how to write rule premises? Can I use bound
        ;; variables from the rule like this?
        (side-condition (p seq-el))
        r-first-true)
   (--> (state (first p) r (cons seq-el seq))
        (state false #f seq)
        (side-condition (not (p seq-el)))
        r-first-false)

   (--> (state (all p) r (cons seq-el seq))
        (state (all p) #t seq)
        (side-condition (p seq-el))
        r-all-true)
   (--> (state (all p) r (cons seq-el seq))
        (state false #f seq)
        (side-condition (not (p seq-el)))
        r-all-false)


   (--> (state (not ltl_0) r_0 (cons seq-el seq))
        (state (not ltl_1) ,(not r_1) seq)
        ;; todo: I don't think this is right, but I can't find how to
        ;; do this
        (where (--> (state ltl_0 r_0 (cons seq-el seq))
                    (state ltl_1 r_1 seq)))
        r-not)

   (--> (state (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (state (or ltl_A_1 ltl_B_1) ,(or r_A r_B) seq)
        (where (--> (state ltl_A_0 r_0 (cons seq-el seq))
                    (state ltl_A_1 r_A seq)))
        (where (--> (state ltl_B_0 r_0 (cons seq-el seq))
                    (state ltl_B_1 r_B seq)))
        r-or)

   (--> (state (next ltl) r (cons seq-el seq))
        (state ltl #f seq)
        r-next)

   (--> (state (until ltl_A_0 ltl_B_0) r (cons seq-el seq))
        (state ltl_B_1 #t seq)
        (where (--> (state ltl_B_0 r (cons seq-el seq))
                    (state ltl_B_1 #t seq)))
        r-until-start-B)
   (--> (state (until ltl_A_0 ltl_B_0) r (cons seq-el seq))
        (state (until ltl_A_1 ltl_B_0) #f seq)
        (where (--> (state ltl_B_0 r (cons seq-el seq))
                    (state ltl_B_1 #f seq)))
        (where (--> (state ltl_A_0 r (cons seq-el seq))
                    (state ltl_A_1 r_A seq)))
        r-until-still-A)


   (--> (state (and ltl_A ltl_B) r seq)
        (state (not (or (not ltl_A) (not ltl_B))) r seq)
        r-expand-and)
   (--> (state (implies ltl_A ltl_B) r seq)
        (state (or (not ltl_A) ltl_B) r seq)
        r-expand-implies)
   (--> (state (iff ltl_A ltl_B) r seq)
        (state (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq)
        r-expand-iff)
   (--> (state (release ltl_A ltl_B) r seq)
        (state (not (until (not ltl_A) (not ltl_B))) r seq)
        r-expand-release)
   (--> (state (eventually ltl) r seq)
        (state (until true ltl) r seq)
        r-expand-eventually)
   (--> (state (globally ltl) r seq)
        (state (not (eventually (not ltl))) r seq)
        r-expand-globally)
   (--> (state (weak-until ltl_A ltl_B) r seq)
        (state (or (until ltl_A ltl_B) (globally ltl_A)) r seq)
        r-expand-weak-until)
   (--> (state (strong-release ltl_A ltl_B) r seq)
        (state (and (release ltl_A ltl_B) (eventually ltl_A)) r seq)
        r-expand-strong-release)))
