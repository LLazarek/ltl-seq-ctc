#lang racket

(provide (all-defined-out) ltl-lang)

(require redex)

(module+ test
  (require "model-test-common.rkt"))

(define-language ltl-lang
  [ltl true
       false
       (first p)
       (next ltl)
       (until ltl ltl)
       (not ltl)
       (or ltl ltl)
       ltl-sugar
       ]
  [ltl-sugar (and ltl ltl)
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
  [ltl-state-variant state/left state/mid state/right]
  [ltl-state (ltl-state-variant ltl r seq)]
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

  [ltl-expand-ctx hole
                  (next ltl-expand-ctx)
                  (until ltl-expand-ctx ltl)
                  (until ltl ltl-expand-ctx)
                  (not ltl-expand-ctx)
                  (or ltl-expand-ctx ltl)
                  (or ltl ltl-expand-ctx)]

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
   (--> (state/right true r seq)
        (state/left true r seq)
        r-true/reset)


   (==> (state/left false r (cons seq-el seq))
        (state/right false #f seq)
        r-false)
   (--> (state/right false r seq)
        (state/left false r seq)
        r-false/reset)


   (==> (state/left (first p) r (cons seq-el seq))
        (state/right true #t seq)
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


   (==> (state/left (next ltl) r (cons seq-el seq))
        (state/right ltl ? seq)
        r-next)


   ;; -------------------- begin Until --------------------

   ;; Since the model can move back and forth in time without restriction,
   ;; it can evaluate full ltl sub-formulas by just saving the current
   ;; point in time (sequence + formula states) and allowing the sub-formulas
   ;; to progress until finished, and rolling back to the saved state as
   ;; necessary.
   ;;
   ;; This will look as follows:
   ;; (state (until A B) _ seq) -->
   ;; (meta (state/mid A _ seq) (state/left B _ seq) A B seq)
   ;;
   ;; This allows B to progress until a conclusion is reached, either #t or #f
   ;; If it's #t, we're done: --> (state true ...)
   ;; If it's #f,
   ;; (meta (state/mid A _ seq) (state/right _ #f _) A B seq) -->
   ;; (meta (state/left A _ seq) (state/right ...) A B seq)
   ;;
   ;; This allows A to progress (from the start!; we roll back time to the saved
   ;; original sequence) until a conclusion is reached
   ;; If it's #f, we're done: --> (state false ...)
   ;; If it's #t,
   ;; (meta (state/right _ #t _) (state/right ...) A B seq) -->
   ;; (state (until A B) ? (rest seq))
   ;;
   ;; Now the question remains of how to deal with the fact that now we can be
   ;; inside a meta state at the end of a sequence. Obviously in such a case we
   ;; should return ?.
   ;; Actually, it doesn't matter because this model has no notion of
   ;; "returning" a judgment. It is simply *in* a state and we inspect the
   ;; state to determine what its judgment is.
   ;; So we can just assume that any time it's in a meta state, its
   ;; judgment is ?.
   ;;
   ;; The only problem this raises is that of mild inconsistency with the
   ;; simpler formulas, where with those the outcome is explicitly stored
   ;; in the state, while with until it must be implicitly inferred
   ;; from the state.
   ;; Can this easily be resolved?
   ;; I suppose it can in the sense that a meta state always implies ?,
   ;; so we can tell if the model accepts by trying to match
   ;; (ltl-state _ #t _)
   ;; and we can tell if it rejects by trying to match
   ;; (ltl-state _ #f _)
   ;; and if neither apply then it must be ?.
   (==> (state/left (until ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
        (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/left ltl_B_0 r_0 (cons seq-el seq))
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        r-until/meta-enter-B)
   ;; Now, subterm ltl_B_0 can take as many steps as necessary...
   (==> (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B ? seq_1)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/left ltl_B ? seq_1)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        r-until/meta-step-B)
   ;; ... until it reaches a good/bad prefix
   ;; B reached a good prefix, so we can transition right to true
   (==> (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #t seq_1)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        ;; But note that we rewind the sequence to the element AFTER the
        ;; one that started the sequence B accepted.
        (state/right true #t seq_1)
        r-until/meta-exit/B-true)
   ;; B reached a bad prefix, so set up A to step
   (==> (meta/until (state/mid ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #f seq_1)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        (meta/until (state/left ltl_A_0 r_0 (cons seq-el seq))
                    (state/right ltl_B #f seq_1)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        r-until/meta-enter-A)
   ;; Now, subterm ltl_A_0 can take as many steps as necessary...
   (==> (meta/until (state/right ltl_A ? seq_1)
                    (state/right ltl_B #f seq_2)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        (meta/until (state/left ltl_A ? seq_1)
                    (state/right ltl_B #f seq_2)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        r-until/meta-step-A)
   ;; ... until it reaches a good/bad prefix
   ;; A reached a bad prefix, so we can transition right to false
   (==> (meta/until (state/right ltl_A #f seq_1)
                    (state/right ltl_B #f seq_2)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        (state/right false #f seq)
        r-until/meta-exit/A-false)
   ;; A reached a good prefix, so we can transition back to our starting
   ;; until formula and rewind back to the second element of the
   ;; original sequence
   (==> (meta/until (state/right ltl_A #t seq_1)
                    (state/right ltl_B #f seq_2)
                    ltl_A_0
                    ltl_B_0
                    (cons seq-el seq))
        (state/right (until ltl_A_0 ltl_B_0) ? seq)
        r-until/meta-exit/A-true)
   (--> (state/right (until ltl_A ltl_B_0) r seq)
        (state/left (until ltl_A ltl_B_0) r seq)
        r-until/reset)

   ;; -------------------- end Until --------------------



   (==> (state/left (not ltl_0) r_0 (cons seq-el seq))
        (meta/not (state/left ltl_0 r_0 (cons seq-el seq)))
        r-not/meta-enter)
   ;; Now, subterm (state/left ltl r (cons seq-el seq))
   ;; may take steps as necessary -> (state/right ...)
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
   ;; Now, subterms ltl_A and ltl_B can both step as necessary
   (==> (meta/or (state/right ltl_A r_A seq)
                 (state/right ltl_B r_B seq))
        (state/right (or ltl_A ltl_B) (or-metafn r_A r_B) seq)
        r-or/meta-exit)
   (--> (state/right (or ltl_A ltl_B) r seq)
        (state/left (or ltl_A ltl_B) r seq)
        r-or/reset)


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
   ;; These two don't really make a lot of sense in three-valued
   ;; semantics, so I'll leave them out.
   ;;
   ;; (==> (state/left (weak-until ltl_A ltl_B) r seq)
   ;;      (state/left (or (until ltl_A ltl_B) (globally ltl_A)) r seq)
   ;;      r-expand-weak-until)
   ;; (==> (state/left (strong-release ltl_A ltl_B) r seq)
   ;;      (state/left (and (release ltl_A ltl_B) (eventually ltl_A)) r seq)
   ;;      r-expand-strong-release)

   with
   [(--> (in-hole meta-E a) (in-hole meta-E b))
    (==> a b)]))

(module+ test
  ;; -------------------- true, false --------------------
  (test-->> ltl-red
            (term (state/left
                   true
                   #f
                   (cons zero empty)))
            (term (state/left
                   true
                   #t
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   false
                   #f
                   (cons zero empty)))
            (term (state/left
                   false
                   #f
                   empty)))

  ;; -------------------- first --------------------
  (test-->> ltl-red
            (term (state/left
                   (first zero?)
                   #f
                   (cons zero empty)))
            (term (state/left
                   true
                   #t
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (first zero?)
                   #f
                   (cons #t empty)))
            (term (state/left
                   false
                   #f
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (first zero?)
                   #f
                   (cons zero (cons #t empty))))
            (term (state/left
                   true
                   #t
                   empty)))


  ;; -------------------- not --------------------
  (test-->> ltl-red
            (term (state/left
                   (not (first zero?))
                   #t
                   (cons zero empty)))
            (term (state/left
                   (not true)
                   #f
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (not (first zero?))
                   #t
                   (cons #t empty)))
            (term (state/left
                   (not false)
                   #t
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (not (first zero?))
                   #t
                   (cons zero (cons #t (cons zero empty)))))
            (term (state/left
                   (not true)
                   #f
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (not (first zero?))
                   #t
                   (cons ,one (cons #t (cons zero empty)))))
            (term (state/left
                   (not false)
                   #t
                   empty)))


  ;; -------------------- next --------------------
  (test-->> ltl-red
            (term (state/left
                   (next (first zero?))
                   #t
                   (cons zero (cons zero empty))))
            (term (state/left
                   true
                   #t
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (next (first zero?))
                   #t
                   (cons zero (cons zero (cons #f empty)))))
            (term (state/left
                   true
                   #t
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (next (first zero?))
                   #t
                   (cons zero (cons #f empty))))
            (term (state/left
                   false
                   #f
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (next (first zero?))
                   #t
                   (cons zero empty)))
            (term (state/left
                   (first zero?)
                   ?
                   empty)))


  ;; -------------------- until --------------------
  ;; First element satisfies A, B never satisfied
  (test-->> ltl-red
            (term (state/left
                   (until (first zero?) (first (negate zero?)))
                   #t
                   (cons zero empty)))
            (term (state/left
                   (until (first zero?) (first (negate zero?)))
                   ?
                   empty)))
  ;; First element satisfies A, second element satisfies B
  (test-->> ltl-red
            (term (state/left
                   (until (first zero?) (first (negate zero?)))
                   #t
                   (cons zero (cons #f empty))))
            (term (state/left
                   true
                   #t
                   empty)))
  ;; First element satisfies B
  (test-->> ltl-red
            (term (state/left
                   (until (first zero?) (first (negate zero?)))
                   #t
                   (cons #f empty)))
            (term (state/left
                   true
                   #t
                   empty)))
  ;; First element satisfies A, second element fails both A and B
  (test-->> ltl-red
            (term (state/left
                   (until (first ,<=3?) (first ,<=1?))
                   ?
                   (cons ,two empty)))
            (term (state/left
                   (until (first ,<=3?) (first ,<=1?))
                   ?
                   empty)))
  (test-->> ltl-red
            (term (state/left
                   (until (first ,<=3?) (first ,<=1?))
                   #t
                   (cons ,two (cons ,four empty))))
            (term (state/left
                   false
                   #f
                   empty)))

  ;; Compound until taking many steps to check both A and B
  ;; B gets satisfied "right away"
  (test-->> ltl-red
            (term (state/left
                   (until (next (next (first ,<=3?))) (next (first ,<=1?)))
                   #t
                   (cons #t (cons zero (cons ,two (cons ,four empty))))))
            (term (state/left
                   true
                   #t
                   empty)))
  ;; B gets satisfied on second el, so does A
  (test-->> ltl-red
            (term (state/left
                   (until (next (next (first ,<=3?))) (next (first ,<=1?)))
                   #t
                   (cons #t (cons ,three (cons ,one (cons ,two empty))))))
            (term (state/left
                   true
                   #t
                   empty)))
  ;; B gets satisfied on second el, and A fails
  (test-->> ltl-red
            (term (state/left
                   (until (next (next (first ,<=3?))) (next (first ,<=1?)))
                   #t
                   (cons #t (cons ,three (cons ,one (cons ,four empty))))))
            (term (state/left
                   true
                   #t
                   empty)))
  ;; Second el satisfies B but first el fails A : #f
  (test-->> ltl-red
            (term (state/left
                   (until (next (next (next (first ,<=3?)))) (next (first ,<=1?)))
                   #t
                   (cons #t (cons ,three (cons ,one (cons ,four empty))))))
            (term (state/left
                   false
                   #f
                   empty)))
  ;; Third el satisfies B but second el can't satisfy A due to not enough
  ;; els to verify
  (test-->> ltl-red
            (term (state/left
                   (until (next (next (next (first ,<=3?)))) (next (first ,<=1?)))
                   #t
                   (cons #t (cons ,three (cons ,two (cons ,one empty))))))
            ;; meta/until basically means ?
            (term (meta/until
                   (state/left
                    (first (λ (x) (zero? (pred (pred (pred x))))))
                    ?
                    empty)
                   (state/right false #f (cons (succ zero) empty))
                   (next
                    (next
                     (next
                      (first (λ (x) (zero? (pred (pred (pred x)))))))))
                   (next (first (λ (x) (zero? (pred x)))))
                   (cons
                    (succ (succ (succ zero)))
                    (cons (succ (succ zero)) (cons (succ zero) empty))))))



  ;; -------------------- or --------------------
  ;; #f or #f : #f
  (test-->> ltl-red
            (term (state/left
                   (or (first zero?) (until (first ,<=1?) (not (first ,<=3?))))
                   #t
                   (cons ,one
                         (cons ,two
                               (cons zero empty)))))
            (term (state/left
                   (or false false)
                   #f
                   empty)))
  ;; #f or #t : #t
  (test-->> ltl-red
            (term (state/left
                   (or (first zero?) (until (first ,<=1?) (not (first ,<=3?))))
                   #t
                   (cons ,one
                         (cons ,four
                               (cons zero empty)))))
            (term (state/left
                   (or false true)
                   #t
                   empty)))
  ;; #t or #f : #t
  (test-->> ltl-red
            (term (state/left
                   (or (first zero?) (until (first ,<=1?) (not (first ,<=3?))))
                   #t
                   (cons zero
                         (cons ,two
                               (cons zero empty)))))
            (term (state/left
                   (or true false)
                   #t
                   empty)))
  ;; #t or #t : #t
  (test-->> ltl-red
            (term (state/left
                   (or (first zero?) (until (first ,<=1?) (not (first ,<=3?))))
                   #t
                   (cons zero
                         (cons ,four
                               (cons zero empty)))))
            (term (state/left
                   (or true true)
                   #t
                   empty)))



  ;; -------------------- and --------------------
  ;; #t and #t : #t
  (test-->> ltl-red
            (term (state/left
                   (and (first zero?)
                        (until (first ,<=1?) (first ,>3?)))
                   #t
                   (cons zero (cons ,four empty))))
            (term (state/left
                   (not (or (not true)
                            (not true)))
                   #t
                   empty)))
  ;; #t and #f : #f
  (test-->> ltl-red
            (term (state/left
                   (and (first zero?)
                        (until (first ,<=1?) (first ,>3?)))
                   #t
                   (cons zero (cons ,two empty))))
            (term (state/left
                   (not (or (not true)
                            (not false)))
                   #f
                   empty)))
  ;; #f and #t : #f
  (test-->> ltl-red
            (term (state/left
                   (and (first zero?)
                        (until (first ,<=1?) (first ,>3?)))
                   #t
                   (cons ,one (cons ,four empty))))
            (term (state/left
                   (not (or (not false)
                            (not true)))
                   #f
                   empty)))
  ;; #f and #f : #f
  (test-->> ltl-red
            (term (state/left
                   (and (first zero?)
                        (until (first ,<=1?) (first ,>3?)))
                   #t
                   (cons ,one
                         (cons ,two empty))))
            (term (state/left
                   (not (or (not false)
                            (not false)))
                   #f
                   empty)))


  ;; -------------------- implies --------------------
  ;; premise and conclusion satisfied
  ;; #t => #t : #t
  (test-->> ltl-red
            (term (state/left
                   (implies (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons zero (cons zero (cons ,four empty)))))
            (term (state/left
                   (or (not true) true)
                   #t
                   empty)))
  ;; premise but not conclusion satisfied
  ;; #t => #f : #f
  (test-->> ltl-red
            (term (state/left
                   (implies (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons zero (cons ,one empty))))
            (term (state/left
                   (or (not true) false)
                   #f
                   empty)))
  ;; conclusion but not premise satisfied
  ;; #f => #t : #t
  (test-->> ltl-red
            (term (state/left
                   (implies (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons ,four empty)))
            (term (state/left
                   (or (not false) true)
                   #t
                   empty)))
  ;; neither conclusion nor premise satisfied
  ;; #f => #f : #t
  (test-->> ltl-red
            (term (state/left
                   (implies (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons ,one empty)))
            (term (state/left
                   (or (not false) false)
                   #t
                   empty)))


  ;; -------------------- iff --------------------
  ;; premise and conclusion satisfied
  ;; #t <=> #t : #t
  (test-->> ltl-red
            (term (state/left
                   (iff (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons zero (cons zero (cons ,four empty)))))
            (term (state/left
                   (not (or (not (or (not true) true))
                            (not (or (not true) true))))
                   #t
                   empty)))
  ;; premise but not conclusion satisfied
  ;; #t <=> #f : #f
  (test-->> ltl-red
            (term (state/left
                   (iff (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons zero (cons ,one empty))))
            (term (state/left
                   (not (or (not (or (not true) false))
                            (not (or (not false) true))))
                   #f
                   empty)))
  ;; conclusion but not premise satisfied
  ;; #f <=> #t : #f
  (test-->> ltl-red
            (term (state/left
                   (iff (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons ,four empty)))
            (term (state/left
                   (not (or (not (or (not false) true))
                            (not (or (not true) false))))
                   #f
                   empty)))
  ;; neither conclusion nor premise satisfied
  ;; #f <=> #f : #t
  (test-->> ltl-red
            (term (state/left
                   (iff (first zero?) (until (first zero?) (first ,>3?)))
                   #f
                   (cons ,one empty)))
            (term (state/left
                   (not (or (not (or (not false) false))
                            (not (or (not false) false))))
                   #t
                   empty)))

  ;; -------------------- release --------------------
  ;; A R B : A never comes : #t
  (test-->> ltl-red
            (term (state/left
                   (release (first zero?)
                            (first ,<=1?))
                   #f
                   (cons ,one (cons ,one empty))))
            (term (state/left
                   (not
                    (until
                     (not (first zero?))
                     (not (first ,<=1?))))
                   ?
                   empty)))
  ;; A R B : B fails before A : #f
  (test-->> ltl-red
            (term (state/left
                   (release (first zero?)
                            (first ,<=1?))
                   #f
                   (cons ,two (cons ,two empty))))
            (term (state/left
                   (not true)
                   #f
                   empty)))
  ;; A R B : A comes before end : #t
  (test-->> ltl-red
            (term (state/left
                   (release (first zero?)
                            (first ,<=1?))
                   #f
                   (cons ,one (cons zero (cons #t empty)))))
            (term (state/left
                   (not false)
                   #t empty)))
  ;; A R B : A comes at start : #t
  (test-->> ltl-red
            (term (state/left
                   (release (first zero?)
                            (first ,<=1?))
                   #f
                   (cons zero (cons #t empty))))
            (term (state/left
                   (not false)
                   #t empty)))


  ;; -------------------- eventually --------------------
  ;; F A : A never happens : ?
  (test-->> ltl-red
            (term (state/left
                   (eventually (first zero?))
                   #f
                   (cons #t (cons ,one empty))))
            (term (state/left
                   (until true (first zero?))
                   ?
                   empty)))
  ;; F A : A happens : #t
  (test-->> ltl-red
            (term (state/left
                   (eventually (first zero?))
                   #f
                   (cons #t (cons zero empty))))
            (term (state/left
                   true
                   #t
                   empty)))

  ;; -------------------- globally --------------------
  ;; G A : A never happens : #f
  (test-->> ltl-red
            (term (state/left
                   (globally (first zero?))
                   #f
                   (cons #t (cons ,one empty))))
            (term (state/left
                   (not true)
                   #f
                   empty)))
  ;; G A : A happens sometimes : #f
  (test-->> ltl-red
            (term (state/left
                   (globally (first zero?))
                   #f
                   (cons zero (cons ,one empty))))
            (term (state/left
                   (not true)
                   #f
                   empty)))
  ;; G A : A happens always : ?
  (test-->> ltl-red
            (term (state/left
                   (globally (first zero?))
                   #f
                   (cons zero (cons zero empty))))
            (term (state/left
                   (not (until true (not (first zero?))))
                   ?
                   empty)))

  ;; ;; -------------------- weak-until --------------------
  ;; ;; First element satisfies A, B never satisfied
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (weak-until (all zero?) (all (negate zero?)))
  ;;                  #t
  ;;                  (cons zero empty)))
  ;;           (term (state/left
  ;;                  (or (until (all zero?) (all (negate zero?)))
  ;;                      (not (until true (not (all zero?)))))
  ;;                  #t
  ;;                  empty)))
  ;; ;; First element satisfies A, second element satisfies B
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (weak-until (all zero?) (all (negate zero?)))
  ;;                  #t
  ;;                  (cons zero (cons #f empty))))
  ;;           (term (state/left
  ;;                  (or (all (negate zero?)) (not (not false)))
  ;;                  #t empty)))
  ;; ;; First element satisfies B
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (until (all zero?) (all (negate zero?)))
  ;;                  #t
  ;;                  (cons #f empty)))
  ;;           (term (state/left
  ;;                  (all (negate zero?))
  ;;                  #t empty)))
  ;; ;; First element satisfies A, second element satisfies B
  ;; ;; (different B)
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (weak-until (all zero?) (first (negate zero?)))
  ;;                  #t
  ;;                  (cons zero (cons #f empty))))
  ;;           (term (state/left
  ;;                  (or true (not (not false)))
  ;;                  #t empty)))
  ;; ;; First element satisfies A, second element satisfies B
  ;; ;; (different B)
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (until (all zero?)
  ;;                         (all ,<=1?))
  ;;                  #t
  ;;                  (cons zero (cons ,one empty))))
  ;;           (term (state/left
  ;;                  (all ,<=1?)
  ;;                  #t
  ;;                  empty)))
  ;; ;; First element satisfies A, second element fails both A and B
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (weak-until (all zero?)
  ;;                              (all ,<=1?))
  ;;                  #t
  ;;                  (cons zero (cons ,two empty))))
  ;;           (term (state/left
  ;;                  (or false (not (not false)))
  ;;                  #f
  ;;                  empty)))


  ;; ;; -------------------- strong-release --------------------
  ;; ;; A SR B : A never comes : #f
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (strong-release (first zero?)
  ;;                                  (all ,<=1?))
  ;;                  #f
  ;;                  (cons ,one (cons ,one empty))))
  ;;           (term (state/left
  ;;                  (not
  ;;                   (or (not (not
  ;;                             (until
  ;;                              (not false)
  ;;                              (not (all ,<=1?)))))
  ;;                       (not (until true (first zero?)))))
  ;;                  #f
  ;;                  empty)))
  ;; ;; A SR B : B fails before A : #f
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (strong-release (first zero?)
  ;;                                  (all ,<=1?))
  ;;                  #f
  ;;                  (cons ,two (cons ,two empty))))
  ;;           (term (state/left
  ;;                  (not (or (not (not (not false)))
  ;;                           (not (until true (first zero?)))))
  ;;                  #f
  ;;                  empty)))
  ;; ;; A SR B : A comes before end : #t
  ;; (test-->> ltl-red
  ;;           (term (state/left
  ;;                  (strong-release (first zero?)
  ;;                                  (all ,<=1?))
  ;;                  #f
  ;;                  (cons ,one (cons zero (cons #t empty)))))
  ;;           ;; todo: not sure I understand this, but it might just be
  ;;           ;; bc I don't get the formula fully
  ;;           (term (state/left
  ;;                  (not (or (not (not
  ;;                                 (until
  ;;                                  (not false)
  ;;                                  (not (all ,<=1?)))))
  ;;                           (not true)))
  ;;                  #t empty)))
  ;; ;; A SR B : A comes at start : #t
  ;; (test-->> ltl-red
  ;;           (term (state/left (strong-release (first zero?)
  ;;                                      (all ,<=1?))
  ;;                             #f
  ;;                             (cons zero (cons #t empty))))
  ;;           (term (state/left
  ;;                  (not (or (not (not
  ;;                                 (until
  ;;                                  (not true)
  ;;                                  (not (all ,<=1?)))))
  ;;                           (not true)))
  ;;                  #t empty)))
  )
