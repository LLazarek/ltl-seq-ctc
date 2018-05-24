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
       (or ltl)
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
          (meta/until (state/mid ltl r seq) meta-E)
          (meta/until meta-E ltl-state)]

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
           zero?]
  [predλ-v r (λ (x) predλ-e) zero (succ predλ-v)]
  [x variable-not-otherwise-mentioned]
  [E hole
     (E predλ-e)
     (predλ-v E)
     (if E predλ-e predλ-e)
     (succ E)
     (pred E)
     (zero? E)]
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
        (state/left true #t seq)
        r-true)

   (==> (state/left false r (cons seq-el seq))
        (state/left false #f seq)
        r-false)

   (==> (state/left (first p) r (cons seq-el seq))
        (state/left true #t seq)
        ;; todo: is this how to write rule premises? Can I use bound
        ;; variables from the rule like this?
        (side-condition
         (equal? (apply-reduction-relation predλ-red (term (p seq-el)))
                 (list (term #t))))
        r-first-true)
   (==> (state/left (first p) r (cons seq-el seq))
        (state/left false #f seq)
        (side-condition
         (equal? (apply-reduction-relation predλ-red (term (p seq-el)))
                 (list (term #f))))
        r-first-false)

   (==> (state/left (all p) r (cons seq-el seq))
        (state/left (all p) #t seq)
        (side-condition
         (equal? (apply-reduction-relation predλ-red (term (p seq-el)))
                 (list (term #t))))
        r-all-true)
   (==> (state/left (all p) r (cons seq-el seq))
        (state/left false #f seq)
        (side-condition
         (equal? (apply-reduction-relation predλ-red (term (p seq-el)))
                 (list (term #f))))
        r-all-false)


   (==> (state/left (not ltl_0) r_0 (cons seq-el seq))
        (meta/not (state/left ltl_0 r_0 (cons seq-el seq)))
        r-not/meta-enter)
   ;; Now, subterm (state/left ltl r (cons seq-el seq))
   ;; may take a single reduction step -> (state/right ...)
   (==> (meta/not (state/right ltl) r seq)
        (state/left (not ltl) (not-metafn r) seq)
        r-not/meta-exit)

   
   (==> (state/left (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (meta/or (state/left ltl_A_0 r_0 (cons seq-el seq))
                 (state/left ltl_B_0 r_0 (cons seq-el seq)))
        r-or/meta-enter)
   ;; Now, subterms ltl_A and ltl_B can take a single step each
   (==> (meta/or (state/right ltl_A r_A seq)
                 (state/right ltl_B r_B seq)) ;; todo: write metafunction or
        (state/left (or ltl_A ltl_B) (or-metafn r_A r_B) seq))

   (==> (state (next ltl) r (cons seq-el seq))
        (state ltl #f seq)
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
        (state/left ltl_B #t seq)
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
        (state/left (until ltl_A ltl_B_0) r_A seq))


   (==> (state (and ltl_A ltl_B) r seq)
        (state (not (or (not ltl_A) (not ltl_B))) r seq)
        r-expand-and)
   (==> (state (implies ltl_A ltl_B) r seq)
        (state (or (not ltl_A) ltl_B) r seq)
        r-expand-implies)
   (==> (state (iff ltl_A ltl_B) r seq)
        (state (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq)
        r-expand-iff)
   (==> (state (release ltl_A ltl_B) r seq)
        (state (not (until (not ltl_A) (not ltl_B))) r seq)
        r-expand-release)
   (==> (state (eventually ltl) r seq)
        (state (until true ltl) r seq)
        r-expand-eventually)
   (==> (state (globally ltl) r seq)
        (state (not (eventually (not ltl))) r seq)
        r-expand-globally)
   (==> (state (weak-until ltl_A ltl_B) r seq)
        (state (or (until ltl_A ltl_B) (globally ltl_A)) r seq)
        r-expand-weak-until)
   (==> (state (strong-release ltl_A ltl_B) r seq)
        (state (and (release ltl_A ltl_B) (eventually ltl_A)) r seq)
        r-expand-strong-release)

   with
   [(--> (in-hole meta-E a) (in-hole meta-E b))
    (==> a b)]))

(module+ test
  (test-->> ltl-red
            (term (state/left true #f (cons zero empty)))
            (term (state/left true #t empty)))
  (test-->> ltl-red
            (term (state/left false #f (cons zero empty)))
            (term (state/left false #f empty)))

  (test-->> ltl-red
            (term (state/left (first zero?) #f (cons zero empty)))
            (term (state/left true #t empty)))
  (test-->> ltl-red
            (term (state/left (first zero?) #f (cons #t empty)))
            (term (state/left false #f empty)))
  )
