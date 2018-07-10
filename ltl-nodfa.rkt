#lang racket

;; -------------------- Fundamental definitions --------------------
(define world/c any/c)

(define result/c (or/c 't 'f '?))
(define result/good? (curry equal? 't))
(define result/bad? (curry equal? 'f))
(define result/indeterminate? (curry equal? '?))
(define result/not-good? (or/c result/bad? result/indeterminate?))
(define result/not-bad? (or/c result/good? result/indeterminate?))

(define (bool->result b)
  (if b 't 'f))

(define (invert-result r)
  (match r
    ['t 'f]
    ['f 't]
    ['? '?]))

;; An ltl formula's encoding is a Consumer
(define consumer/c
  (-> world/c (values result/c (recursive-contract consumer/c))))


;; -------------------- Testing preliminaries --------------------
(define/contract (check-consumer generator seq [init '?])
  (-> consumer/c (listof world/c) result/c)

  (if (empty? seq)
      init
      (let-values ([(accept? next-consumer) (generator (first seq))])
        (check-consumer next-consumer (rest seq) accept?))))

(module+ test
  (require rackunit)
  (define-syntax-rule (check-? expr-c)
    (check-equal? expr-c '?))
  (define-syntax-rule (check-t expr-c)
    (check-equal? expr-c 't))
  (define-syntax-rule (check-f expr-c)
    (check-equal? expr-c 'f)))

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

(module+ test
  (define first-a-c (primitive/first (curry equal? 'a)))

  (check-? (check-consumer first-a-c '()))
  (check-t (check-consumer first-a-c '(a)))
  (check-t (check-consumer first-a-c '(a a)))
  (check-t (check-consumer first-a-c '(a b)))
  (check-f (check-consumer first-a-c '(1 2)))
  (check-f (check-consumer first-a-c '(b))))


;; -------------------- Compound ltl constructors --------------------

;; --------------- next ---------------
;; Generator -> Generator
(define/contract (c/next next)
  (-> consumer/c consumer/c)
  (λ (world)
    (values '? next)))

(module+ test
  (define next-is-a-c (c/next (primitive/first (curry equal? 'a))))

  (check-? (check-consumer next-is-a-c '()))
  (check-? (check-consumer next-is-a-c '(a)))
  (check-? (check-consumer next-is-a-c '(b)))
  (check-t (check-consumer next-is-a-c '("test" a)))
  (check-t (check-consumer next-is-a-c '(#f a b)))
  (check-f (check-consumer next-is-a-c '(a b c))))


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
             (values 't (primitive/value-thunk 't))]

            [(empty? bad-As)
             ;; A's are all good or indeterminate
             (values '? (check-recurrently-with new-pairs))]

            [(empty? bad-As/indeterminate-Bs)
             ;; Some of the A's are bad, and all of their B's are bad
             (values 'f (primitive/value-thunk 'f))]

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
             (values 't (primitive/value-thunk 't))]

            [(empty? indeterminate-Bs)
             (values 'f (primitive/value-thunk 'f))]

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

 (check-? (check-consumer a-until-b-c '()))
 (check-? (check-consumer a-until-b-c '(a)))
 (check-? (check-consumer a-until-b-c '(a a)))

 (check-t (check-consumer a-until-b-c '(b)))
 (check-t (check-consumer a-until-b-c '(a b)))
 (check-t (check-consumer a-until-b-c '(a a a b)))
 (check-t (check-consumer a-until-b-c '(a a a b b b b)))
 (check-t (check-consumer a-until-b-c '(b d e)))

 (check-f (check-consumer a-until-b-c '(a c)))
 (check-f (check-consumer a-until-b-c '(a c b)))
 (check-f (check-consumer a-until-b-c '(1 2 3)))

 (define next-a-until-next-b-c
   (c/until (c/next (primitive/first (curry equal? 'a)))
            (c/next (c/next (primitive/first (curry equal? 'b))))))
 (check-t (check-consumer next-a-until-next-b-c '(c a a a c b d)))
 (check-? (check-consumer next-a-until-next-b-c '(c a a a c))))


;; --------------- until ---------------
;; Generator -> Generator
(define/contract (c/not gen)
  (-> consumer/c consumer/c)

  (λ (world)
    (let-values ([(res new-c) (gen world)])
      (values (invert-result res)
              (c/not new-c)))))

(module+ test
  (define not-next-is-a-c (c/not next-is-a-c))

  (check-? (check-consumer not-next-is-a-c '()))
  (check-? (check-consumer not-next-is-a-c '(a)))
  (check-? (check-consumer not-next-is-a-c '(b)))
  (check-f (check-consumer not-next-is-a-c '("test" a)))
  (check-f (check-consumer not-next-is-a-c '(#f a b)))
  (check-t (check-consumer not-next-is-a-c '(a b c)))

  (define not-a-until-b-c (c/not a-until-b-c))
  (check-? (check-consumer not-a-until-b-c '()))
  (check-? (check-consumer not-a-until-b-c '(a)))
  (check-? (check-consumer not-a-until-b-c '(a a)))

  (check-f (check-consumer not-a-until-b-c '(b)))
  (check-f (check-consumer not-a-until-b-c '(a b)))
  (check-f (check-consumer not-a-until-b-c '(a a a b)))
  (check-f (check-consumer not-a-until-b-c '(a a a b b b b)))
  (check-f (check-consumer not-a-until-b-c '(b d e)))

  (check-t (check-consumer not-a-until-b-c '(a c)))
  (check-t (check-consumer not-a-until-b-c '(a c b)))
  (check-t (check-consumer not-a-until-b-c '(1 2 3))))

#|

(define/contract (c/or a-c b-c)
  (-> consumer/c consumer/c consumer/c)

  (λ (world)
    (let-values ([(a-accept? a-c/new) (a-c world)]
                 [(b-accept? b-c/new) (b-c world)])
      (values (or a-accept? b-accept?)
              (c/or a-c/new b-c/new)))))

(module+ test
  (define or-true-c (c/or all-a-c not-all-a-c))
  (check-t (check-consumer or-true-c '(a a a)))
  (check-t (check-consumer or-true-c '(b 2 3 a "ashdh" #f a)))
  ;; False because both components require at least one element to become true
  (check-f (check-consumer or-true-c '()))

  (define next-is-number-or-all-b-c
    (c/or (c/next (primitive/first number?))
                  (c/all (curry equal? 'b))))
  (check-t (check-consumer next-is-number-or-all-b-c '(b 1 b b b)))
  (check-t (check-consumer next-is-number-or-all-b-c '(b b b b)))
  (check-t (check-consumer next-is-number-or-all-b-c '(b 1 "b" #f)))
  (check-t (check-consumer next-is-number-or-all-b-c '(c -200 "a" #f)))
  (check-f (check-consumer next-is-number-or-all-b-c '(c b "a" #f)))
  (check-f (check-consumer next-is-number-or-all-b-c '(b b b b #f))))


(define/contract (c/and a-c b-c)
  (-> consumer/c consumer/c consumer/c)
  (c/not (c/or (c/not a-c)
                               (c/not b-c))))
(module+ test
  (define and-false-c (c/and all-a-c not-all-a-c))
  (check-f (check-consumer and-false-c '(a a a)))
  (check-f (check-consumer and-false-c '(b 2 3 a "ashdh" #f a)))
  (check-f (check-consumer and-false-c '()))

  (define all-even-and-next-is-2-c
    (c/and (c/next (primitive/first (curry = 2)))
                   (c/all (and/c number? even?))))
  (check-t (check-consumer all-even-and-next-is-2-c '(16 2)))
  (check-t (check-consumer all-even-and-next-is-2-c '(0 2 4 6 8)))
  (check-t (check-consumer all-even-and-next-is-2-c '(2 2 2)))
  ;; False because next isn't 2: it's not anything.
  (check-f (check-consumer all-even-and-next-is-2-c '(42)))
  (check-f (check-consumer all-even-and-next-is-2-c '(1 2)))
  (check-f (check-consumer all-even-and-next-is-2-c '(0 2 3 4 6)))
  (check-f (check-consumer all-even-and-next-is-2-c '(0 2 b)))
  (check-f (check-consumer all-even-and-next-is-2-c '(0 2 #f 5))))


(define/contract (c/implies premise-c conclusion-c)
  (-> consumer/c consumer/c consumer/c)
  (c/or (c/not premise-c)
                conclusion-c))

(module+ test
  (define if-next-is-2-then-all-even
    (c/implies (c/next (primitive/first (curry equal? 2)))
                       (c/all (and/c number? even?))))
  ;; Premise satisfied and so is conclusion
  (check-t (check-consumer if-next-is-2-then-all-even
                               '(0 2 4 6)))
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-t (check-consumer if-next-is-2-then-all-even
                               '(42)))
  (check-t (check-consumer if-next-is-2-then-all-even
                               '(2 4 6 8)))
  ;; and neither is conclusion
  (check-t (check-consumer if-next-is-2-then-all-even
                               '(a b c)))
  (check-t (check-consumer if-next-is-2-then-all-even
                               '(1 3 5)))

  ;; Premise satisfied but not conclusion
  (check-f (check-consumer if-next-is-2-then-all-even
                                '(1 2 3 5)))
  (check-f (check-consumer if-next-is-2-then-all-even
                                '(1 2 a b)))
  (check-f (check-consumer if-next-is-2-then-all-even
                                '(a 2 4 6))))

(define/contract (c/iff left-c right-c)
  (-> consumer/c consumer/c consumer/c)

  (c/and (c/implies left-c right-c)
                 (c/implies right-c left-c)))

(module+ test
  (define next-is-2-iff-all-even
    (c/iff (c/next (primitive/first (curry equal? 2)))
                   (c/all (and/c number? even?))))
  ;; Premise satisfied and so is conclusion
  (check-t (check-consumer next-is-2-iff-all-even
                               '(0 2 4 6)))
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-f (check-consumer next-is-2-iff-all-even
                               '(42)))
  (check-f (check-consumer next-is-2-iff-all-even
                               '(2 4 6 8)))
  ;; and neither is conclusion
  (check-t (check-consumer next-is-2-iff-all-even
                               '(a b c)))
  (check-t (check-consumer next-is-2-iff-all-even
                               '(1 3 5)))

  ;; Premise satisfied but not conclusion
  (check-f (check-consumer next-is-2-iff-all-even
                                '(1 2 3 5)))
  (check-f (check-consumer next-is-2-iff-all-even
                                '(1 2 a b)))
  (check-f (check-consumer next-is-2-iff-all-even
                                '(a 2 4 6))))

(define/contract (c/release releaser-c held-c)
  (-> consumer/c consumer/c consumer/c)

  (c/not (c/until (c/not releaser-c)
                                  (c/not held-c))))

(module+ test
  (define (small? x)
    (printf "Checking if ~v is small\n" x)
    (and (positive? x) (<= x 10)))
  (define (ten? x)
    (printf "Checking if ~v is 10\n" x)
    (= x 10))
  (define ten-releases-small-c
    (c/release (primitive/first ten?)
                       (c/all small?)))

  ;; Never get the release
  ;; (check-t (check-consumer ten-releases-small-c
                               ;; '(1 3 5)))
  ;; Get the release and then end
  ;; (check-t (check-consumer ten-releases-small-c
                               ;; '(1 3 5 10)))
  ;; Get the release and then whatever
  (printf "---\n")
  (check-t (check-consumer ten-releases-small-c
                               '(10 11)))
  (printf "---\n")
  (check-t (check-consumer ten-releases-small-c
                               '(1 10 11))))

(define/contract (c/eventually eventual)
  (-> consumer/c consumer/c)

  (c/until (c/all true-pred)
                   eventual))

(define/contract (c/globally always-c)
  (-> consumer/c consumer/c)

  (c/release (c/all false-pred)
                     always-c))

(define/contract (c/until/weak first-c then-c)
  (-> consumer/c consumer/c consumer/c)

  (c/or (c/until first-c then-c)
                (c/globally first-c)))

(define/contract (c/release/strong releaser-c held-c)
  (-> consumer/c consumer/c consumer/c)

  (c/and (c/release releaser-c held-c)
                 (c/eventually releaser-c)))
|#
