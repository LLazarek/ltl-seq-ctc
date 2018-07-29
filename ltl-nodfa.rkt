#lang racket

(provide run-consumer
         primitive/first
         c/next
         c/until
         c/not
         c/or
         c/and
         c/implies
         c/iff
         c/release
         c/eventually
         c/globally)


;; -------------------- Fundamental definitions --------------------
(require "common.rkt")
(define result/good? (curry equal? 't))
(define result/bad? (curry equal? 'f))
(define result/indeterminate? (curry equal? '?))
(define result/not-good? (or/c result/bad? result/indeterminate?))
(define result/not-bad? (or/c result/good? result/indeterminate?))

(define (bool->result b)
  (if b 't 'f))

(define (result/invert r)
  (match r
    ['t 'f]
    ['f 't]
    ['? '?]))

(define (result/or r-a r-b)
  (cond [(or (result/good? r-a)
             (result/good? r-b))
         't]

        [(not (and (result/bad? r-a)
                   (result/bad? r-b)))
         '?]

        [else 'f]))


;; -------------------- Testing preliminaries --------------------
(module+ test
  (require "test-common.rkt"))

;; -------------------- Primitive ltl constructors --------------------
;; A primitive constructor converts a value or predicate into a consumer

;; Creates a consumer that always produces the given value
(define/contract (primitive/value-thunk v)
  (-> result/c consumer/c)

  (define (thunk x)
    (values v thunk))
  thunk)

;; Produces a consumer that checks PRED against the first element
;; in a sequence
(define/contract (primitive/first pred)
  (-> predicate/c consumer/c)

  (λ (world)
    (let* ([pred-res (pred world)]
           [res (bool->result pred-res)]
           [res-gen (primitive/value-thunk res)])
      (values res res-gen))))

(define c/true (primitive/value-thunk 't))
(define c/false (primitive/value-thunk 'f))

(module+ test
  (define first-a-c (primitive/first (curry equal? 'a)))

  (check-runs first-a-c :  -> ?)
  (check-runs first-a-c : a -> t)
  (check-runs first-a-c : a a -> t)
  (check-runs first-a-c : a b -> t)
  (check-runs first-a-c : 1 2 -> f)
  (check-runs first-a-c : b -> f)

  (check-runs c/true : a 2 4 -> t)
  (check-runs c/true : -3 66.4 #f "ff" -> t)
  (check-runs c/false : a 2 4 -> f)
  (check-runs c/false : -3 66.4 #f "ff" -> f))



;; -------------------- Compound ltl constructors --------------------

;; --------------- next ---------------
;; Generator -> Generator
(define/contract (c/next next)
  (-> consumer/c consumer/c)
  (λ (world)
    (values '? next)))

(module+ test
  (define next-is-a-c (c/next (primitive/first (curry equal? 'a))))

  (check-runs next-is-a-c :  -> ?)
  (check-runs next-is-a-c : a -> ?)
  (check-runs next-is-a-c : b -> ?)
  (check-runs next-is-a-c : "test" a -> t)
  (check-runs next-is-a-c : #f a b -> t)
  (check-runs next-is-a-c : a b c -> f))


;; --------------- until ---------------

;; How until works:
;; Keep track of pairs of A/B formulas that progress in tandem
;;
;; As long as no A formula produces 'f,
;; add a new version of A/B starting over on every time step
;;   Also on every step remove any A formulas that produce 't
;;
;; Once an A formula produces 'f,
;; switch to a new function that will just reduce the corresponding B formula(s)
;; (i.e. just return the B formula)

(struct ltl-pair (A B A-result B-result))
(define ((A-result-is? what) pair)
  (equal? (ltl-pair-A-result pair) what))
(define ((B-result-is? what) pair)
  (equal? (ltl-pair-B-result pair) what))

;; Generator Generator -> Generator
(define/contract (c/until A B)
  (-> consumer/c consumer/c consumer/c)

  (define (step-all A-B-pairs world)
    (for/list ([pair (in-list A-B-pairs)])
      (define-values (this-A/result this-A/new) ((ltl-pair-A pair) world))
      (define-values (this-B/result this-B/new) ((ltl-pair-B pair) world))
      (ltl-pair this-A/new    this-B/new
                this-A/result this-B/result)))
  (define (check-recurrently-with A-B-pairs)
    (λ (world)
      (define stepped-pairs (step-all A-B-pairs world))
      (define pairs/without-good-As (filter-not (A-result-is? 't)
                                                stepped-pairs))
      (define new-pairs (cons (ltl-pair A B '? '?) pairs/without-good-As))

      (define good-Bs (filter (B-result-is? 't) stepped-pairs))
      (define bad-As (filter (A-result-is? 'f) stepped-pairs))

      (define bad-As/indeterminate-Bs (filter (B-result-is? '?) bad-As))

      (cond [(not (empty? good-Bs))
             (values 't c/true)]

            [(empty? bad-As)
             ;; A's are all good or indeterminate
             (values '? (check-recurrently-with new-pairs))]

            [(empty? bad-As/indeterminate-Bs)
             ;; Some of the A's are bad, and all of their B's are bad
             (values 'f c/false)]

            [else
             ;; Found bad prefix(es) for A,
             ;; but their Bs may still work:
             ;; check their Bs
             (values '? (check-all-Bs bad-As/indeterminate-Bs))])))

  (define (check-all-Bs A-B-pairs)
    (λ (world)
      (define stepped-pairs (step-all A-B-pairs world))
      (define any-B-good? (ormap (B-result-is? 't) stepped-pairs))
      (define indeterminate-Bs (filter (B-result-is? '?) stepped-pairs))

      (cond [any-B-good?
             (values 't c/true)]

            [(empty? indeterminate-Bs)
             (values 'f c/false)]

            [else
             (values '? (check-all-Bs indeterminate-Bs))])))

  (check-recurrently-with (list (ltl-pair A B '? '?))))

;; todo: need to figure out how UNTIL actually works.
;; For example:
;; (primitive/first 'a) U (primitive/first 'b)
;; Does this succeed on the sequence '(a c b)?
;;   By one measure, no: (primitive/first 'a) fails on the second element 'c
;;   Another, yes: it succeeds on '(a c), and (primitive/first 'b) works on 'b
;;
;;
;; Resolving the above, what about this one:
;; (primitive/first 'a) U (c/next 'b)
;; How does this even work? Since (c/next 'b) will always return ? for its first
;; element; am I supposed to restart it on every element, even while keeping
;; track of the continuation of each one I start until it becomes 't or 'f?
;;
;; And what about this one:
;; (c/next 'a) U (primitive/first 'b)
;; Am I supposed to do the restarting thing on every element here too?
;; Keeping track of every strand that gets spawned on every element,
;; until one becomes 't?
;;
;; The more I think about it the more that seems like the way it has to be...

(module+ test
  (define a-until-b-c (c/until (primitive/first (curry equal? 'a))
                               (primitive/first (curry equal? 'b))))
  
  (check-runs a-until-b-c :  -> ?)
  (check-runs a-until-b-c : a -> ?)
  (check-runs a-until-b-c : a a -> ?)

  (check-runs a-until-b-c : b -> t)
  (check-runs a-until-b-c : a b -> t)
  (check-runs a-until-b-c : a a a b -> t)
  (check-runs a-until-b-c : a a a b b b b -> t)
  (check-runs a-until-b-c : b d e -> t)

  (check-runs a-until-b-c : a c -> f)
  (check-runs a-until-b-c : a c b -> f)
  (check-runs a-until-b-c : 1 2 3 -> f)

 (define naunb-c
   (c/until (c/next (primitive/first (curry equal? 'a)))
            (c/next (c/next (primitive/first (curry equal? 'b))))))
 (check-runs naunb-c : c a a a c b d -> t)
 (check-runs naunb-c : c a a a c -> ?))


;; --------------- not ---------------
;; Generator -> Generator
(define/contract (c/not gen)
  (-> consumer/c consumer/c)

  (λ (world)
    (let-values ([(res new-c) (gen world)])
      (values (result/invert res)
              (c/not new-c)))))

(module+ test
  (define not-next-is-a-c (c/not next-is-a-c))

  (check-runs not-next-is-a-c :  -> ?)
  (check-runs not-next-is-a-c : a -> ?)
  (check-runs not-next-is-a-c : b -> ?)
  (check-runs not-next-is-a-c : "test" a -> f)
  (check-runs not-next-is-a-c : #f a b -> f)
  (check-runs not-next-is-a-c : a b c -> t)

  (define not-a-until-b-c (c/not a-until-b-c))
  (check-runs not-a-until-b-c :  -> ?)
  (check-runs not-a-until-b-c : a -> ?)
  (check-runs not-a-until-b-c : a a -> ?)

  (check-runs not-a-until-b-c : b -> f)
  (check-runs not-a-until-b-c : a b -> f)
  (check-runs not-a-until-b-c : a a a b -> f)
  (check-runs not-a-until-b-c : a a a b b b b -> f)
  (check-runs not-a-until-b-c : b d e -> f)

  (check-runs not-a-until-b-c : a c -> t)
  (check-runs not-a-until-b-c : a c b -> t)
  (check-runs not-a-until-b-c : 1 2 3 -> t))


;; --------------- or ---------------
(define/contract (c/or a-c b-c)
  (-> consumer/c consumer/c consumer/c)

  (λ (world)
    (let-values ([(a-accept? a-c/new) (a-c world)]
                 [(b-accept? b-c/new) (b-c world)])
      (values (result/or a-accept? b-accept?)
              (c/or a-c/new b-c/new)))))

(module+ test
  (define true-c (c/or next-is-a-c not-next-is-a-c))
  (check-runs true-c : -> ?)
  (check-runs true-c : a a a -> t)
  (check-runs true-c : b 2 3 a "ashdh" #f a -> t)
  (check-runs true-c : #f 2 33.0 -> t)

  (define num-c (primitive/first number?))
  (define noaub-c (c/or (c/next num-c)
                        a-until-b-c))
  (check-runs noaub-c : -> ?)
  (check-runs noaub-c : c -> ?)
  (check-runs noaub-c : a a -> ?)

  (check-runs noaub-c : c 5 -> t)
  (check-runs noaub-c : b -> t)
  (check-runs noaub-c : a b -> t)
  (check-runs noaub-c : a a b 5 -> t)

  (check-runs noaub-c : c a a b 5 -> f)
  (check-runs noaub-c : #t c -> f)
  (check-runs noaub-c : a a 1 2 3 -> f))


;; --------------- and ---------------
(define/contract (c/and a-c b-c)
  (-> consumer/c consumer/c consumer/c)
  (c/not (c/or (c/not a-c)
               (c/not b-c))))
(module+ test
  (define false-c (c/and next-is-a-c not-next-is-a-c))
  (check-runs false-c :  -> ?)
  (check-runs false-c : a a a -> f)
  (check-runs false-c : b 2 3 a "ashdh" #f a -> f)

  (define =2-c (primitive/first (curry equal? 2)))
  (define x2eu42-c
    (c/and (c/next =2-c)
           (c/until (primitive/first (and/c number? even?))
                    (primitive/first (curry equal? 42)))))
  (check-runs x2eu42-c :  -> ?)
  (check-runs x2eu42-c : 42 -> ?)
  (check-runs x2eu42-c : 0 2 -> ?)
  (check-runs x2eu42-c : 0 2 40 -> ?)
  (check-runs x2eu42-c : 0 2 42 -> t)
  (check-runs x2eu42-c : 42 2 1 -> t)
  (check-runs x2eu42-c : 0 2 40 42 1 -> t)
  (check-runs x2eu42-c : 0 1 2 40 -> f)
  (check-runs x2eu42-c : 0 2 40 1 42 -> f)
  (check-runs x2eu42-c : 0 2 #f 42 1 -> f))


;; --------------- implies ---------------
(define/contract (c/implies premise-c conclusion-c)
  (-> consumer/c consumer/c consumer/c)
  (c/or (c/not premise-c)
                conclusion-c))

(module+ test
  (define x2->x22-c (c/implies (c/next =2-c)
                               (c/next (c/next =2-c))))
  ;; Not enough info yet
  (check-runs x2->x22-c :  -> ?)
  (check-runs x2->x22-c : 0 -> ?)
  (check-runs x2->x22-c : 0 2 -> ?)
  ;; Premise satisfied and so is conclusion
  (check-runs x2->x22-c : 0 2 2 -> t)
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-runs x2->x22-c : a b 2 -> t)
  (check-runs x2->x22-c : 0 1 2 -> t)
  ;; and neither is conclusion
  (check-runs x2->x22-c : a b c -> t)
  (check-runs x2->x22-c : 1 3 5 -> t)

  ;; Premise satisfied but not conclusion
  (check-runs x2->x22-c : 1 2 3 5 -> f)
  (check-runs x2->x22-c : 1 2 a b -> f)
  (check-runs x2->x22-c : a 2 4 6 -> f))



;; --------------- iff ---------------
(define/contract (c/iff left-c right-c)
  (-> consumer/c consumer/c consumer/c)

  (c/and (c/implies left-c right-c)
         (c/implies right-c left-c)))

(module+ test
  (define x2<->x22-c (c/iff (c/next =2-c)
                            (c/next (c/next =2-c))))
  ;; Not enough info yet
  (check-runs x2<->x22-c :  -> ?)
  (check-runs x2<->x22-c : 0 -> ?)
  (check-runs x2<->x22-c : 0 2 -> ?)

  ;; Premise satisfied and so is conclusion
  (check-runs x2<->x22-c : 0 2 2 6 -> t)
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-runs x2<->x22-c : a b 2 -> f)
  (check-runs x2<->x22-c : 0 1 2 -> f)
  ;; and neither is conclusion
  (check-runs x2<->x22-c : a b c -> t)
  (check-runs x2<->x22-c : 1 3 5 -> t)

  ;; Premise satisfied but not conclusion
  (check-runs x2<->x22-c : 1 2 3 5 -> f)
  (check-runs x2<->x22-c : 1 2 a b -> f)
  (check-runs x2<->x22-c : a 2 4 6 -> f))



;; --------------- release ---------------
(define/contract (c/release releaser-c held-c)
  (-> consumer/c consumer/c consumer/c)

  (c/not (c/until (c/not releaser-c)
                  (c/not held-c))))

(module+ test
  (define 2rn-c (c/release =2-c num-c))

  ;; Too short
  (check-runs 2rn-c :  -> ?)
  ;; Never get the release
  (check-runs 2rn-c : 1 3 5 -> ?)
  ;; Get the release and then end
  (check-runs 2rn-c : 1 3 5 2 -> t)
  ;; Get the release and then whatever
  (check-runs 2rn-c : 2 a -> t)
  (check-runs 2rn-c : 1 2 #f c -> t)
  ;; Fail the held condition before getting release
  (check-runs 2rn-c : 1 3 #f 2 #f c -> f))



;; --------------- eventually ---------------
(define/contract (c/eventually eventual)
  (-> consumer/c consumer/c)

  (c/until c/true eventual))

(module+ test
  (define ev2-c (c/eventually =2-c))

  ;; Eventually can only ever give ? or t
  ;; because there is never enough elements to prove an eventually
  ;; formula false (because every finite seq is treated as a prefix of
  ;; an inf trace)
  (check-runs ev2-c :  -> ?)
  (check-runs ev2-c : a b -> ?)
  (check-runs ev2-c : a b 2 -> t)
  (check-runs ev2-c : a b #f "ha" 2 3 22.0 -> t))


;; --------------- globally ---------------
(define/contract (c/globally always-c)
  (-> consumer/c consumer/c)

  (c/release c/false always-c))

(module+ test
  (define all-n-c (c/globally num-c))

  ;; Globally can only ever give ? or f
  ;; by the same logic as eventually
  (check-runs all-n-c :  -> ?)
  (check-runs all-n-c : 1 -> ?)
  (check-runs all-n-c : 1 2.0 3.3 4 -> ?)
  (check-runs all-n-c : a b -> f)
  (check-runs all-n-c : a b #f "ha" 2 3 22.0 -> f))


#|

These variants on until and release actually don't really make
sense, because the situations they are supposed to invert actually
result in ?, so they shouldn't behave differently.

For example, until is normally considered "strong" in that it is
required that B become true for A U B to be satisfied. However, any
finite trace always satisfying A but not B will just produce ? (rather
than f), because traces are treated as partial prefixes: that is, they
may be extended. It is therefore always too early to call the trace
false on the grounds that it doesn't satisfy B, so these tweaks to
behavior never have their effect.

Thus, I leave them out entirely.

;; --------------- weak until ---------------
(define/contract (c/until/weak first-c then-c)
  (-> consumer/c consumer/c consumer/c)

  (c/or (c/until first-c then-c)
        (c/globally first-c)))

;; --------------- strong release ---------------
(define/contract (c/release/strong releaser-c held-c)
  (-> consumer/c consumer/c consumer/c)

  (c/and (c/release releaser-c held-c)
                 (c/eventually releaser-c)))
|#
