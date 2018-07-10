#lang racket

(module+ test
  (require rackunit)
  (define-syntax-rule (check-? expr-c)
    (check-equal? expr-c '?))
  (define-syntax-rule (check-t expr-c)
    (check-equal? expr-c 't))
  (define-syntax-rule (check-f expr-c)
    (check-equal? expr-c 'f)))

(define world/c any/c)
(define result/c (or/c 't 'f '?))

(define generator/c
  (-> world/c (values result/c (recursive-contract generator/c))))

(define/contract (check-consumer generator seq [init '?])
  (-> generator/c (listof world/c) result/c)

  (if (empty? seq)
      init
      (let-values ([(accept? next-consumer) (generator (first seq))])
	(check-consumer next-consumer (rest seq) accept?))))

(define (false-pred _) 'f)
(define (true-pred _) 't)
(define (primitive/value-thunk v)
  (define (thunk x)
    (values x thunk))
  thunk)

(define (bool->result b)
  (if b 't 'f))

;; Produces a consumer that checks PRED against the first element
;; in a sequence
(define/contract (primitive/first pred)
  (-> predicate/c generator/c)
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



;; Generator -> Generator
(define/contract (c/next next)
  (-> generator/c generator/c)
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

;; Generator Generator -> Generator
(define/contract (c/until first-c then-c)
  (-> generator/c generator/c generator/c)

  (define (check-first-until-then first-c/current then-c/current)
    (λ (world)
      (let-values ([(first-res first-c/new)
		    (first-c/current world)]
		   [(then-res then-c/new)
		    (then-c/current world)])
	(cond [(and first-res (not then-res))
	       ;; note: returning false while in first predicate because
	       ;; this is a *strong* until; THEN *must* become
	       ;; true for this to be true
	       (values #f (check-first-until-then first-c/new
						  then-c/current))]

              ;; todo confirm: until doesn't say anything about
              ;; first-c's truth once then-c becomes true
              ;; Alternative: (when then-c becomes true first-c
              ;; must be false)
              ;; [(and (not first-res) then-res)
	      [then-res
	       (values then-res then-c/new)]

	      [else
	       ;; FIRST has failed and so has THEN
	       (values #f (c/all false-pred))]))))

  (check-first-until-then first-c then-c))

(module+ test
 (define a-until-b-c (c/until (c/all (curry equal? 'a))
					(c/all (curry equal? 'b))))

 (check-true (check-consumer a-until-b-c '(a b)))
 (check-true (check-consumer a-until-b-c '(a a a b)))
 (check-true (check-consumer a-until-b-c '(a a a b b b b)))
 (check-true (check-consumer a-until-b-c '(a b b)))
 (check-true (check-consumer a-until-b-c '(b)))
 (check-true (check-consumer a-until-b-c '(b b b b b)))

 (check-false (check-consumer a-until-b-c '()))
 (check-false (check-consumer a-until-b-c '(a)))
 (check-false (check-consumer a-until-b-c '(a a)))
 (check-false (check-consumer a-until-b-c '(a b a)))
 (check-false (check-consumer a-until-b-c '(a a a a b a b b b b)))
 (check-false (check-consumer a-until-b-c '(b a a a)))
 (check-false (check-consumer a-until-b-c '(b b b b b a)))
 (check-false (check-consumer a-until-b-c '(a a b b 1)))
 (check-false (check-consumer a-until-b-c '(1 2 3)))
 (check-false (check-consumer a-until-b-c '("hello")))

 (define first-number-then-all-symbols-c
   (c/until (primitive/first number?)
		    (c/all symbol?)))
 (check-true (check-consumer first-number-then-all-symbols-c
			      '(1 a)))
 (check-true (check-consumer first-number-then-all-symbols-c
			      '(42 a b c c)))
 (check-true (check-consumer first-number-then-all-symbols-c
			      '(1000.0 b b kl g r edcsdsvc f)))
 (check-true (check-consumer first-number-then-all-symbols-c
			      ;; should be true because A is never true and B is
			      '(b b kl g r edcsdsvc f)))

 ;; todo confirm: should this check succeed?
 ;; I could argue yes bc 1 satisfies A, so the whole sequence
 ;; satisfies A, and after 2 the rest satisfies B
 (check-true (check-consumer first-number-then-all-symbols-c
                              '(1 2 b b kl g r edcsdsvc f)))

 (check-false (check-consumer first-number-then-all-symbols-c
                              '(1 2 b 3 f)))
 (check-false (check-consumer first-number-then-all-symbols-c
			       '(1 b b kl g r "edcsdsvc" f)))
 (check-false (check-consumer first-number-then-all-symbols-c
			       '(1)))
 (check-false (check-consumer first-number-then-all-symbols-c
			       '())))

;; Generator -> Generator
(define/contract (c/not gen)
  (-> generator/c generator/c)

  (λ (world)
    (let-values ([(res new-c) (gen world)])
      (values (not res)
              (c/not (or new-c
                                 (c/all true-pred)))))))

(module+ test
  (define not-first-number-then-all-symbols-c
    (c/not first-number-then-all-symbols-c))
  (check-false (check-consumer not-first-number-then-all-symbols-c
                               '(42 a b c c)))
  (check-false (check-consumer not-first-number-then-all-symbols-c
                               '(1000.0 b b kl g r edcsdsvc f)))
  (check-true (check-consumer not-first-number-then-all-symbols-c
                                '(1 2 b 3 kl g r edcsdsvc f)))
  (check-true (check-consumer not-first-number-then-all-symbols-c
                                '(1)))

  (define not-a-until-b-c (c/not a-until-b-c))
  (check-false (check-consumer not-a-until-b-c '(a b b)))
  (check-false (check-consumer not-a-until-b-c '(b)))
  (check-true (check-consumer not-a-until-b-c '(b b b b b a)))
  (check-true (check-consumer not-a-until-b-c '(a a b b 1)))

  (define not-next-starts-with-number-c
    (c/not next-starts-with-number-c))
  (check-false (check-consumer not-next-starts-with-number-c '("nan" 2 a)))
  (check-false (check-consumer not-next-starts-with-number-c
                                '("nan" 2 a "b" 3)))
  (check-true (check-consumer not-next-starts-with-number-c '(1 a)))
  (check-true (check-consumer not-next-starts-with-number-c '(a a)))

  (define not-next-is-all-a-c (c/not next-is-all-a-c))
  (check-false (check-consumer not-next-is-all-a-c '(#f a a a a a a)))
  (check-false (check-consumer not-next-is-all-a-c '(b a a a a a a)))
  (check-true (check-consumer not-next-is-all-a-c '(a b c)))
  (check-true (check-consumer not-next-is-all-a-c '(a a c)))

  (define not-first-a-c (c/not first-a-c))
  (check-false (check-consumer not-first-a-c '(a b)))
  (check-true (check-consumer not-first-a-c '(b a b)))

  (define not-all-a-c (c/not all-a-c))
  (check-false (check-consumer not-all-a-c '(a a a a a a)))
  (check-true (check-consumer not-all-a-c '(a b))))


(define/contract (c/or a-c b-c)
  (-> generator/c generator/c generator/c)

  (λ (world)
    (let-values ([(a-accept? a-c/new) (a-c world)]
                 [(b-accept? b-c/new) (b-c world)])
      (values (or a-accept? b-accept?)
              (c/or a-c/new b-c/new)))))

(module+ test
  (define or-true-c (c/or all-a-c not-all-a-c))
  (check-true (check-consumer or-true-c '(a a a)))
  (check-true (check-consumer or-true-c '(b 2 3 a "ashdh" #f a)))
  ;; False because both components require at least one element to become true
  (check-false (check-consumer or-true-c '()))

  (define next-is-number-or-all-b-c
    (c/or (c/next (primitive/first number?))
                  (c/all (curry equal? 'b))))
  (check-true (check-consumer next-is-number-or-all-b-c '(b 1 b b b)))
  (check-true (check-consumer next-is-number-or-all-b-c '(b b b b)))
  (check-true (check-consumer next-is-number-or-all-b-c '(b 1 "b" #f)))
  (check-true (check-consumer next-is-number-or-all-b-c '(c -200 "a" #f)))
  (check-false (check-consumer next-is-number-or-all-b-c '(c b "a" #f)))
  (check-false (check-consumer next-is-number-or-all-b-c '(b b b b #f))))


(define/contract (c/and a-c b-c)
  (-> generator/c generator/c generator/c)
  (c/not (c/or (c/not a-c)
                               (c/not b-c))))
(module+ test
  (define and-false-c (c/and all-a-c not-all-a-c))
  (check-false (check-consumer and-false-c '(a a a)))
  (check-false (check-consumer and-false-c '(b 2 3 a "ashdh" #f a)))
  (check-false (check-consumer and-false-c '()))

  (define all-even-and-next-is-2-c
    (c/and (c/next (primitive/first (curry = 2)))
                   (c/all (and/c number? even?))))
  (check-true (check-consumer all-even-and-next-is-2-c '(16 2)))
  (check-true (check-consumer all-even-and-next-is-2-c '(0 2 4 6 8)))
  (check-true (check-consumer all-even-and-next-is-2-c '(2 2 2)))
  ;; False because next isn't 2: it's not anything.
  (check-false (check-consumer all-even-and-next-is-2-c '(42)))
  (check-false (check-consumer all-even-and-next-is-2-c '(1 2)))
  (check-false (check-consumer all-even-and-next-is-2-c '(0 2 3 4 6)))
  (check-false (check-consumer all-even-and-next-is-2-c '(0 2 b)))
  (check-false (check-consumer all-even-and-next-is-2-c '(0 2 #f 5))))


(define/contract (c/implies premise-c conclusion-c)
  (-> generator/c generator/c generator/c)
  (c/or (c/not premise-c)
                conclusion-c))

(module+ test
  (define if-next-is-2-then-all-even
    (c/implies (c/next (primitive/first (curry equal? 2)))
                       (c/all (and/c number? even?))))
  ;; Premise satisfied and so is conclusion
  (check-true (check-consumer if-next-is-2-then-all-even
                               '(0 2 4 6)))
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-true (check-consumer if-next-is-2-then-all-even
                               '(42)))
  (check-true (check-consumer if-next-is-2-then-all-even
                               '(2 4 6 8)))
  ;; and neither is conclusion
  (check-true (check-consumer if-next-is-2-then-all-even
                               '(a b c)))
  (check-true (check-consumer if-next-is-2-then-all-even
                               '(1 3 5)))

  ;; Premise satisfied but not conclusion
  (check-false (check-consumer if-next-is-2-then-all-even
                                '(1 2 3 5)))
  (check-false (check-consumer if-next-is-2-then-all-even
                                '(1 2 a b)))
  (check-false (check-consumer if-next-is-2-then-all-even
                                '(a 2 4 6))))

(define/contract (c/iff left-c right-c)
  (-> generator/c generator/c generator/c)

  (c/and (c/implies left-c right-c)
                 (c/implies right-c left-c)))

(module+ test
  (define next-is-2-iff-all-even
    (c/iff (c/next (primitive/first (curry equal? 2)))
                   (c/all (and/c number? even?))))
  ;; Premise satisfied and so is conclusion
  (check-true (check-consumer next-is-2-iff-all-even
                               '(0 2 4 6)))
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-false (check-consumer next-is-2-iff-all-even
                               '(42)))
  (check-false (check-consumer next-is-2-iff-all-even
                               '(2 4 6 8)))
  ;; and neither is conclusion
  (check-true (check-consumer next-is-2-iff-all-even
                               '(a b c)))
  (check-true (check-consumer next-is-2-iff-all-even
                               '(1 3 5)))

  ;; Premise satisfied but not conclusion
  (check-false (check-consumer next-is-2-iff-all-even
                                '(1 2 3 5)))
  (check-false (check-consumer next-is-2-iff-all-even
                                '(1 2 a b)))
  (check-false (check-consumer next-is-2-iff-all-even
                                '(a 2 4 6))))

(define/contract (c/release releaser-c held-c)
  (-> generator/c generator/c generator/c)

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
  ;; (check-true (check-consumer ten-releases-small-c
                               ;; '(1 3 5)))
  ;; Get the release and then end
  ;; (check-true (check-consumer ten-releases-small-c
                               ;; '(1 3 5 10)))
  ;; Get the release and then whatever
  (printf "---\n")
  (check-true (check-consumer ten-releases-small-c
                               '(10 11)))
  (printf "---\n")
  (check-true (check-consumer ten-releases-small-c
                               '(1 10 11))))

(define/contract (c/eventually eventual)
  (-> generator/c generator/c)

  (c/until (c/all true-pred)
                   eventual))

(define/contract (c/globally always-c)
  (-> generator/c generator/c)

  (c/release (c/all false-pred)
                     always-c))

(define/contract (c/until/weak first-c then-c)
  (-> generator/c generator/c generator/c)

  (c/or (c/until first-c then-c)
                (c/globally first-c)))

(define/contract (c/release/strong releaser-c held-c)
  (-> generator/c generator/c generator/c)

  (c/and (c/release releaser-c held-c)
                 (c/eventually releaser-c)))

