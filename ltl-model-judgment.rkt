#lang racket

(require redex)

(module+ test
  (require rackunit))

(define-language ltl-lang
  [ltl true
       false
       (first p)
       (next ltl)
       (until ltl ltl)
       (not ltl)
       (or ltl ltl)
       (and ltl ltl)
       (implies ltl ltl)
       (iff ltl ltl)
       (release ltl ltl)
       (eventually ltl)
       (globally ltl)
       ;; (weak-until ltl ltl)
       ;; (strong-release ltl ltl)
       ]
  [seq empty
       (cons seq-el seq)]
  [ltl-state (state/left ltl r seq)
             (state/mid ltl r seq)
             (state/right ltl r seq)]
  [meta-state (meta/not ltl-state)
              (meta/or ltl-state ltl-state)
              (meta/until ltl-state ltl-state
                          ltl ltl
                          seq)]
  [meta-E hole
          (meta/not meta-E)
          (meta/or meta-E ltl-state)
          (meta/or (state/right ltl r seq) meta-E)
          (meta/until (state/mid ltl r seq) meta-E
                      ltl ltl
                      seq)
          (meta/until meta-E ltl-state
                      ltl ltl
                      seq)]

  [p predλ-e]
  [seq-el predλ-v]
  [r #t
     #f
     ?]

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
  [(not-metafn #f) #t]
  [(not-metafn ?) ?])
(module+ test
  (test-equal (term (not-metafn #t))
              (term #f))
  (test-equal (term (not-metafn #f))
              (term #t)))

(define-metafunction ltl-lang
  or-metafn : r r -> r
  [(or-metafn #t r) #t]
  [(or-metafn #f r) r]
  [(or-metafn ? #f) ?]
  [(or-metafn ? #t) #t]
  [(or-metafn ? ?) ?])
(module+ test
  (test-equal (term (or-metafn #t #t))
              (term #t))
  (test-equal (term (or-metafn #t #f))
              (term #t))
  (test-equal (term (or-metafn #f #t))
              (term #t))
  (test-equal (term (or-metafn #f #f))
              (term #f)))

(define-syntax (reduces-with stx)
  (syntax-case stx (: --> -/->)
    [(reduces-with red : A --> B)
     (syntax/loc stx
       (equal? (apply-reduction-relation* red (term A))
               (list (term B))))]
    [(reduces-with red : A -/-> B)
     (syntax/loc stx
       (not (reduces-with red : A --> B)))]))

(define-judgment-form ltl-lang
  #:mode (~> I O)
  [--- "true"
       (~> (state true r (cons seq-el seq)) (state true #t seq))]
  [--- "false"
       (~> (state false r (cons seq-el seq)) (state false #f seq))]

  [(side-condition (reduces-with predλ-red : (p seq-el) -/-> #f))
   --- "first/t"
   (~> (state (first p) r (cons seq-el seq))
       (state true #t seq))]
  [(side-condition (reduces-with predλ-red : (p seq-el) --> #f))
   --- "first/f"
   (~> (state (first p) r (cons seq-el seq))
       (state false #f seq))]

  [
   --- "next"
   (~> (state (next ltl) r (cons seq-el seq))
       (state ltl ? seq))]

  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #t _))
   --- "until/B-t"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state true #t seq))]
  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #f _))
   (~> (state ltl_A r (cons seq-el seq))
       (state _     #t _))
   --- "until/B-f/A-t"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state (until ltl_A ltl_B) r seq))]
  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #f _))
   (~> (state ltl_A r (cons seq-el seq))
       (state _     #f _))
   --- "until/B-f/A-f"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state false #f seq))]

  [(~> (state ltl_0 r_0 (cons seq-el seq))
       (state ltl_1 r_1 seq))
   --- "not"
   (~> (state (not ltl_0) r_0 (cons seq-el seq))
       (state (not ltl_1) (not-metafn r_1) seq))]

  [(~> (state ltl_A_0 r_0 (cons seq-el seq))
       (state ltl_A_1 r_A seq))
   (~> (state ltl_B_0 r_0 (cons seq-el seq))
       (state ltl_B_1 r_B seq))
   --- "or"
   (~> (state (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
       (state (or ltl_A_1 ltl_B_1) (or-metafn r_A r_B) seq))]

  [
   --- "and"
   (~> (state (and ltl_A ltl_B) r seq)
       (state (not (or (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "implies"
   (~> (state (implies ltl_A ltl_B) r seq)
       (state (or (not ltl_A) ltl_B) r seq))]
  [
   --- "iff"
   (~> (state (iff ltl_A ltl_B) r seq)
       (state (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq))]
  [
   --- "release"
   (~> (state (release ltl_A ltl_B) r seq)
       (state (not (until (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "eventually"
   (~> (state (eventually ltl) r seq)
       (state (until true ltl) r seq))]
  [
   --- "globally"
   (~> (state (globally ltl) r seq)
       (state (not (eventually (not ltl))) r seq))]
  )

(module+ test
  
  (judgment-holds (~> (state true #t (cons zero empty)) (state true #t empty))))
