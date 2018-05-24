#lang racket

(require redex)

(module+ test
  (require rackunit))

(define-language ltl-lang
  [ltl true
       false
       (first p)
       (all p)
       (not ltl)
       (or ltl ltl)
       (next ltl)
       (until ltl ltl)]
  [seq empty
       (cons seq-el seq)]
  [ltl-state (state/left ltl r seq)
             (state/mid ltl r seq)
             (state/right ltl r seq)]
  [meta-state (meta/not ltl-state)
              (meta/or ltl-state ltl-state)
              (meta/until ltl-state ltl-state ltl)]
  [meta-E hole
          (meta/not meta-E)
          (meta/or meta-E ltl-state)
          (meta/or (state/right ltl r seq) meta-E)
          (meta/until (state/mid ltl r seq) meta-E ltl)
          (meta/until meta-E ltl-state ltl)]

  [p predλ-e]
  [seq-el predλ-v]
  [r #t
     #f]

  [predλ-e x
           #t #f
           (λ (x) predλ-e)
           zero (succ predλ-v)
           (predλ-e predλ-e)
           (if predλ-e predλ-e predλ-e)
           (succ predλ-e)
           (pred predλ-e)
           zero?
           (negate predλ-e)]
  [predλ-v r (λ (x) predλ-e) zero (succ predλ-v)]
  [x variable-not-otherwise-mentioned]
  [E hole
     (E predλ-e)
     (predλ-v E)
     (if E predλ-e predλ-e)
     (succ E)
     (pred E)
     (zero? E)
     (negate E)]
  #:binding-forms
  (λ (x) predλ-e #:refers-to x))


;; write lambda calc with simple values
;; Embed it in this language

(define predλ-red
  (reduction-relation
   ltl-lang
   (==> ((λ (x) predλ-e) predλ-v)
        (substitute predλ-e x predλ-v)
        predλ-r-app)
   (==> (if #f predλ-e_1 predλ-e_2)
        predλ-e_2
        predλ-r-false)
   (==> (if predλ-v predλ-e_1 predλ-e_2)
        predλ-e_1
        (side-condition (not (equal? (term predλ-v)
                                     (term #f))))
        predλ-r-true)
   (==> (pred zero)
        zero
        predλ-r-pred-z)
   (==> (pred (succ predλ-v))
        predλ-v
        predλ-r-pred-v)
   (==> (zero? zero)
        #t
        predλ-r-zero)
   (==> (zero? predλ-v)
        #f
        (side-condition (not (equal? (term predλ-v)
                                     (term zero))))
        predλ-r-n)
   (==> (negate predλ-e)
        (λ (x) (if (predλ-e x) #f #t))
        predλ-r-negate)

   with
   [(--> (in-hole E a) (in-hole E b))
    (==> a b)]))


(module+ test
  (test-->> predλ-red
            (term ((λ (x) x) zero))
            (term zero))
  (test-->> predλ-red
            (term ((λ (x) x) (λ (x) x)))
            (term (λ (x) x)))
  (test-->> predλ-red
            (term (if #t zero (succ zero)))
            (term zero))
  (test-->> predλ-red
            (term (if #f zero (succ zero)))
            (term (succ zero)))
  (test-->> predλ-red
            (term (pred (succ zero)))
            (term zero))
  (test-->> predλ-red
            (term (zero? zero))
            (term #t))
  (test-->> predλ-red
            (term (zero? (succ zero)))
            (term #f))
  (test-->> predλ-red
            (term ((negate zero?) zero))
            (term #f))
  (test-->> predλ-red
            (term ((negate zero?) #t))
            (term #t))

  (test-->> predλ-red
            (term ((λ (x) x)
                   (if #t #f zero)))
            (term #f))

  (test-->> predλ-red
            (term ((if (zero? (succ zero))
                       (λ (x) x)
                       (λ (x) (if (zero? x)
                                  x
                                  (pred x))))
                   zero))
            (term zero))
  (test-->> predλ-red
            (term ((if (zero? (succ zero))
                       (λ (x) x)
                       (λ (x) (if (zero? x)
                                  x
                                  (pred x))))
                   (succ zero)))
            (term zero))
  (test-->> predλ-red
            (term ((if (zero? (succ zero))
                       (λ (x) x)
                       (λ (x) (if (zero? x)
                                  x
                                  (pred x))))
                   (succ (succ zero))))
            (term (succ zero))))



(define-metafunction ltl-lang
  not-metafn : r -> r
  [(not-metafn #t) #f]
  [(not-metafn #f) #t])
(module+ test
  (test-equal (term (not-metafn #t))
              (term #f))
  (test-equal (term (not-metafn #f))
              (term #t)))

(define-metafunction ltl-lang
  or-metafn : r r -> r
  [(or-metafn #t r) #t]
  [(or-metafn #f #t) #t]
  [(or-metafn #f #f) #f])
(module+ test
  (test-equal (term (or-metafn #t #t))
              (term #t))
  (test-equal (term (or-metafn #t #f))
              (term #t))
  (test-equal (term (or-metafn #f #t))
              (term #t))
  (test-equal (term (or-metafn #f #f))
              (term #f)))

(define ltl-red
  (reduction-relation
   ltl-lang
   (==> (state/left true r (cons seq-el seq))
        (state/right true #t seq)
        r-true)
   ;; Note that only top-level simple formulas can transition
   ;; themselves from state/left to state/right
   ;; Non-top-level formulas should have this handled by a
   ;; meta-context
   (--> (state/right true #t seq)
        (state/left true #t seq)
        r-true/reset)


   (==> (state/left false r (cons seq-el seq))
        (state/right false #f seq)
        r-false)
   (--> (state/right false #f seq)
        (state/left false #f seq)
        r-false/reset)


   (==> (state/left (first p) r (cons seq-el seq))
        (state/right true #t seq)
        ;; todo: is this how to write rule premises? Can I use bound
        ;; variables from the rule like this?
        (side-condition
         (not (equal? (apply-reduction-relation* predλ-red (term (p seq-el)))
                      (list (term #f)))))
        r-first-true)
   (==> (state/left (first p) r (cons seq-el seq))
        (state/right false #f seq)
        (side-condition
         (equal? (apply-reduction-relation* predλ-red (term (p seq-el)))
                 (list (term #f))))
        r-first-false)
   (--> (state/right (first p) r seq)
        (state/left (first p) r seq)
        r-first/reset)


   (==> (state/left (all p) r (cons seq-el seq))
        (state/right (all p) #t seq)
        (side-condition
         (not (equal? (apply-reduction-relation* predλ-red (term (p seq-el)))
                      (list (term #f)))))
        r-all-true)
   (==> (state/left (all p) r (cons seq-el seq))
        (state/right false #f seq)
        (side-condition
         (equal? (apply-reduction-relation* predλ-red (term (p seq-el)))
                 (list (term #f))))
        r-all-false)
   (--> (state/right (all p) r seq)
        (state/left (all p) r seq)
        r-all/reset)


   (==> (state/left (not ltl_0) r_0 (cons seq-el seq))
        (meta/not (state/left ltl_0 r_0 (cons seq-el seq)))
        r-not/meta-enter)
   ;; Now, subterm (state/left ltl r (cons seq-el seq))
   ;; may take a single reduction step -> (state/right ...)
   (==> (meta/not (state/right ltl r seq))
        (state/right (not ltl) (not-metafn r) seq)
        r-not/meta-exit)
   (--> (state/right (not ltl) r seq)
        (state/left (not ltl) r seq)
        r-not/reset)


   (==> (state/left (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (meta/or (state/left ltl_A_0 r_0 (cons seq-el seq))
                 (state/left ltl_B_0 r_0 (cons seq-el seq)))
        r-or/meta-enter)
   ;; Now, subterms ltl_A and ltl_B can take a single step each
   (==> (meta/or (state/right ltl_A r_A seq)
                 (state/right ltl_B r_B seq))
        (state/right (or ltl_A ltl_B) (or-metafn r_A r_B) seq)
        r-or/meta-exit)
   (--> (state/right (or ltl_A ltl_B) r seq)
        (state/left (or ltl_A ltl_B) r seq)
        r-or/reset)


   (==> (state/left (next ltl) r (cons seq-el seq))
        (state/right ltl #f seq)
        r-next)


   (==> (state/left (until ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/left ltl_B_0 r_0 (cons seq-el seq))
                    ltl_B_0)
        r-until/meta-enter-B)
   ;; Now, subterm ltl_B_0 can take a single step
   (==> (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #t seq)
                    ltl_B_0)
        (state/right ltl_B #t seq)
        r-until/meta-exit/B-true)
   ;; ltl_B_0 stepped to #f, so set up to let ltl_A_0 step
   (==> (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #f seq)
                    ltl_B_0)
        (meta/until (state/left ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #f seq)
                    ltl_B_0)
        r-until/meta-enter-A)
   ;; Now, subterm ltl_A_0 can take a single step
   (==> (meta/until (state/right ltl_A r_A seq)
                    (state/right ltl_B #f seq)
                    ltl_B_0)
        (state/right (until ltl_A ltl_B_0) #f seq)
        r-until/meta-exit/B-false)
   (--> (state/right (until ltl_A ltl_B_0) r seq)
        (state/left (until ltl_A ltl_B_0) r seq)
        r-until/reset)


   (==> (state/left (and ltl_A ltl_B) r seq)
        (state/left (not (or (not ltl_A) (not ltl_B))) r seq)
        r-expand-and)
   (==> (state/left (implies ltl_A ltl_B) r seq)
        (state/left (or (not ltl_A) ltl_B) r seq)
        r-expand-implies)
   (==> (state/left (iff ltl_A ltl_B) r seq)
        (state/left (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq)
        r-expand-iff)
   (==> (state/left (release ltl_A ltl_B) r seq)
        (state/left (not (until (not ltl_A) (not ltl_B))) r seq)
        r-expand-release)
   (==> (state/left (eventually ltl) r seq)
        (state/left (until true ltl) r seq)
        r-expand-eventually)
   (==> (state/left (globally ltl) r seq)
        (state/left (not (eventually (not ltl))) r seq)
        r-expand-globally)
   (==> (state/left (weak-until ltl_A ltl_B) r seq)
        (state/left (or (until ltl_A ltl_B) (globally ltl_A)) r seq)
        r-expand-weak-until)
   (==> (state/left (strong-release ltl_A ltl_B) r seq)
        (state/left (and (release ltl_A ltl_B) (eventually ltl_A)) r seq)
        r-expand-strong-release)

   with
   [(--> (in-hole meta-E a) (in-hole meta-E b))
    (==> a b)]))

(module+ test
  ;; -------------------- true, false --------------------
  (test-->> ltl-red
            (term (state/left true #f (cons zero empty)))
            (term (state/left true #t empty)))
  (test-->> ltl-red
            (term (state/left false #f (cons zero empty)))
            (term (state/left false #f empty)))

  ;; -------------------- first --------------------
  (test-->> ltl-red
            (term (state/left (first zero?) #f (cons zero empty)))
            (term (state/left true #t empty)))
  (test-->> ltl-red
            (term (state/left (first zero?) #f (cons #t empty)))
            (term (state/left false #f empty)))
  (test-->> ltl-red
            (term (state/left (first zero?) #f (cons zero (cons #t empty))))
            (term (state/left true #t empty)))

  ;; -------------------- all --------------------
  (test-->> ltl-red
            (term (state/left (all zero?) #t empty))
            (term (state/left (all zero?) #t empty)))
  (test-->> ltl-red
            (term (state/left (all zero?) #t (cons zero (cons zero empty))))
            (term (state/left (all zero?) #t empty)))
  (test-->> ltl-red
            (term (state/left (all zero?) #t (cons #t empty)))
            (term (state/left false #f empty)))
  (test-->> ltl-red
            (term (state/left (all zero?) #t
                              (cons zero (cons #t (cons zero empty)))))
            (term (state/left false #f empty)))

  ;; -------------------- not --------------------
  (test-->> ltl-red
            (term (state/left (not (all zero?)) #t
                              (cons zero empty)))
            (term (state/left (not (all zero?)) #f empty)))
  (test-->> ltl-red
            (term (state/left (not (all zero?)) #t
                              (cons #t empty)))
            (term (state/left (not false) #t empty)))
  (test-->> ltl-red
            (term (state/left (not (all zero?)) #t
                              (cons zero (cons #t (cons zero empty)))))
            (term (state/left (not false) #t empty)))
  (test-->> ltl-red
            (term (state/left (not (first zero?)) #t
                              (cons zero (cons #t (cons zero empty)))))
            (term (state/left (not true) #f empty)))
  (test-->> ltl-red
            (term (state/left (not (first zero?)) #t
                              (cons (succ zero) (cons #t (cons zero empty)))))
            (term (state/left (not false) #t empty)))

  ;; -------------------- or --------------------
  ;; #f or #f : #f
  (test-->> ltl-red
            (term (state/left (or (first zero?) (all (negate zero?))) #t
                              (cons (succ zero) (cons #t (cons zero empty)))))
            (term (state/left (or false false) #f empty)))
  ;; #f or #t : #t
  (test-->> ltl-red
            (term (state/left (or (first zero?) (not (all zero?))) #t
                              (cons (succ zero) (cons #t (cons zero empty)))))
            (term (state/left (or false (not false)) #t empty)))
  ;; #t or #f : #t
  (test-->> ltl-red
            (term (state/left (or (first zero?) (all (negate zero?))) #t
                              (cons zero (cons #t (cons zero empty)))))
            (term (state/left (or true false) #t empty)))
  ;; #t or #t : #t
  (test-->> ltl-red
            (term (state/left (or (first zero?) (all (λ (x) (if x #t #f)))) #t
                              (cons (succ zero) (cons #t (cons #t empty)))))
            (term (state/left (or false (all (λ (x) (if x #t #f)))) #t empty)))


  ;; -------------------- next --------------------
  (test-->> ltl-red
            (term (state/left (next (all zero?)) #t
                              (cons zero (cons zero empty))))
            (term (state/left (all zero?) #t empty)))
  (test-->> ltl-red
            (term (state/left (next (all zero?)) #t
                              (cons zero (cons zero (cons #f empty)))))
            (term (state/left false #f empty)))
  (test-->> ltl-red
            (term (state/left (next (first zero?)) #t
                              (cons zero (cons zero (cons #f empty)))))
            (term (state/left true #t empty)))
  (test-->> ltl-red
            (term (state/left (next (first zero?)) #t
                              (cons zero empty)))
            (term (state/left (first zero?) #f empty)))


  ;; -------------------- until --------------------
  ;; First element satisfies A, B never satisfied
  (test-->> ltl-red
            (term (state/left (until (all zero?) (all (negate zero?))) #t
                              (cons zero empty)))
            (term (state/left (until (all zero?) (all (negate zero?))) #f
                              empty)))
  ;; First element satisfies A, second element satisfies B
  (test-->> ltl-red
            (term (state/left (until (all zero?) (all (negate zero?))) #t
                              (cons zero (cons #f empty))))
            (term (state/left (all (negate zero?)) #t empty)))
  ;; First element satisfies B
  (test-->> ltl-red
            (term (state/left (until (all zero?) (all (negate zero?))) #t
                              (cons #f empty)))
            (term (state/left (all (negate zero?)) #t empty)))
  ;; First element satisfies A, second element satisfies B
  ;; (different B)
  (test-->> ltl-red
            (term (state/left (until (all zero?) (first (negate zero?))) #t
                              (cons zero (cons #f empty))))
            (term (state/left true #t empty)))
  ;; First element satisfies A, second element satisfies B
  ;; (different B)
  (test-->> ltl-red
            (term (state/left (until (all zero?)
                                     (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #t
                              (cons zero (cons (succ zero) empty))))
            (term (state/left (all (λ (x) (zero? (pred x))))
                              #t
                              empty)))
  ;; First element satisfies A, second element fails both A and B
  (test-->> ltl-red
            (term (state/left (until (all zero?)
                                     (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #t
                              (cons zero (cons (succ (succ zero)) empty))))
            (term (state/left false
                              #f
                              empty)))

  ;; -------------------- and --------------------
  ;; #t and #t : #t
  (test-->> ltl-red
            (term (state/left (and (first zero?)
                                   (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #t
                              (cons zero empty)))
            (term (state/left
                   (not (or (not true)
                            (not (all (λ (x) (zero? (pred x))))))) ;; <=1?
                              #t
                              empty)))
  ;; #t and #f : #f
  (test-->> ltl-red
            (term (state/left (and (first zero?)
                                   (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #t
                              (cons zero (cons (succ (succ zero)) empty))))
            (term (state/left (not (or (not true)
                                       (not false)))
                              #f
                              empty)))
  ;; #f and #t : #f
  (test-->> ltl-red
            (term (state/left (and (all (λ (x) (zero? (pred x))))  ;; <=1?
                                   (first zero?))
                              #t
                              (cons zero (cons (succ (succ zero)) empty))))
            (term (state/left (not (or (not false)
                                       (not true)))
                              #f
                              empty)))
  ;; #f and #f : #f
  (test-->> ltl-red
            (term (state/left (and (all (λ (x) (zero? (pred x))))  ;; <=1?
                                   (first zero?))
                              #t
                              (cons (succ zero)
                                    (cons (succ (succ zero)) empty))))
            (term (state/left (not (or (not false)
                                       (not false)))
                              #f
                              empty)))

  ;; -------------------- implies --------------------
  ;; premise and conclusion satisfied
  ;; #t => #t : #t
  (test-->> ltl-red
            (term (state/left (implies (first zero?) (all zero?))
                              #f
                              (cons zero (cons zero empty))))
            (term (state/left (or (not true) (all zero?))
                              #t
                              empty)))
  ;; premise but not conclusion satisfied
  ;; #t => #f : #f
  (test-->> ltl-red
            (term (state/left (implies (first zero?) (all zero?))
                              #f
                              (cons zero (cons #f empty))))
            (term (state/left (or (not true) false)
                              #f
                              empty)))
  ;; conclusion but not premise satisfied
  ;; #f => #t : #t
  (test-->> ltl-red
            (term (state/left (implies (not (first zero?))
                                       (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #f
                              (cons zero (cons (succ zero) empty))))
            (term (state/left (or (not (not true))
                                  (all (λ (x) (zero? (pred x)))))
                              #t
                              empty)))
  ;; neither conclusion nor premise satisfied
  ;; #f => #f : #t
  (test-->> ltl-red
            (term (state/left (implies (not (first zero?))
                                       (all (λ (x) (zero? (pred x))))) ;; <=1?
                              #f
                              (cons zero (cons (succ (succ zero)) empty))))
            (term (state/left (or (not (not true)) false)
                              #t
                              empty)))
  )
