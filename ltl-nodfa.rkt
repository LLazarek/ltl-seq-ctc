#lang racket

(module+ test
  (require rackunit))

(define world/c any/c)

;; Generator := (World -> (values Bool Generator)) | #f
(define generator/c
  (or/c false? (-> world/c (values boolean? (recursive-contract generator/c)))))

;; Generator Seq[World] -> Bool
(define/contract (check-generator generator seq [init #f])
  (-> generator/c (listof world/c) boolean?)

  (if (or (empty? seq) (false? generator))
      init
      (let-values ([(accept? next-generator) (generator (first seq))])
	(check-generator next-generator (rest seq) accept?))))

;; Generator World -> (values Bool Generator)
(define/contract (apply-generator gen el)
  (-> generator/c world/c (values boolean? generator/c))

  (if gen
      (gen el)
      (values #f #f)))

(define (false-pred _) #f)
(define (true-pred _) #t)
(define (make-const-pred res)
  (if res true-pred false-pred))

;; Predicate -> Generator
;;
;; Produces a generator that checks PRED against the first element
;; in a sequence
(define/contract (first-generator pred)
  (-> predicate/c generator/c)
  (λ (world)
    (let* ([res (pred world)]
           [res-gen (all-generator (make-const-pred res))])
      (values res res-gen))))

(module+ test
  (define first-a-gen (first-generator (curry equal? 'a)))

  (check-true (check-generator first-a-gen '(a)))
  (check-true (check-generator first-a-gen '(a a)))
  (check-true (check-generator first-a-gen '(a b)))
  (check-false (check-generator first-a-gen '(b a b)))
  (check-false (check-generator first-a-gen '(1 2)))
  (check-false (check-generator first-a-gen '(b)))
  (check-false (check-generator first-a-gen '())))

;; Predicate -> Generator
;;
;; Produces a generator that checks PRED against every element
;; in a sequence, only returning #t if all satisfy it
(define/contract (all-generator pred)
  (-> predicate/c generator/c)

  (define (check world)
    (let ([satisfies? (pred world)])
      (values satisfies?
	      (if satisfies? check (all-generator false-pred)))))
  check)

(module+ test
  (define all-a-gen (all-generator (curry equal? 'a)))

  (check-true (check-generator all-a-gen '(a)))
  (check-true (check-generator all-a-gen '(a a)))
  (check-true (check-generator all-a-gen '(a a a a a a)))
  (check-false (check-generator all-a-gen '(a b)))
  (check-false (check-generator all-a-gen '()))
  (check-false (check-generator all-a-gen '(1 a)))
  (check-false (check-generator all-a-gen '(a a a a a a "hi")))

  (define all-symbols-gen (all-generator symbol?))
  (check-false (check-generator all-symbols-gen '(1 b))))

;; Generator -> Generator
(define/contract (next-generator next)
  (-> generator/c generator/c)
  (λ (world)
    (values #f next)))

(module+ test
  (define next-is-all-a-gen (next-generator (all-generator (curry equal? 'a))))

  (check-true (check-generator next-is-all-a-gen '(a a)))
  (check-true (check-generator next-is-all-a-gen '("test" a)))
  (check-true (check-generator next-is-all-a-gen '(a a a)))
  (check-true (check-generator next-is-all-a-gen '(a a a a a a)))
  (check-true (check-generator next-is-all-a-gen '(#f a a a a a a)))
  (check-true (check-generator next-is-all-a-gen '(b a a a a a a)))
  (check-false (check-generator next-is-all-a-gen '(a b c)))
  (check-false (check-generator next-is-all-a-gen '(a a c)))
  (check-false (check-generator next-is-all-a-gen '(a)))
  (check-false (check-generator next-is-all-a-gen '(a a a a a b)))
  (check-false (check-generator next-is-all-a-gen '(a a a a a b a)))
  (check-false (check-generator next-is-all-a-gen '(a b a a a a a)))

  (define next-starts-with-number-gen
    (next-generator (first-generator number?)))
  (check-true (check-generator next-starts-with-number-gen '(1 2)))
  (check-true (check-generator next-starts-with-number-gen '(1 2 3)))
  (check-true (check-generator next-starts-with-number-gen '("nan" 2 3)))
  (check-true (check-generator next-starts-with-number-gen '("nan" 2 a)))
  (check-true (check-generator next-starts-with-number-gen '("nan" 2 a "b" 3)))
  (check-false (check-generator next-starts-with-number-gen '(1 a)))
  (check-false (check-generator next-starts-with-number-gen '(a a)))
  (check-false (check-generator next-starts-with-number-gen '()))
  (check-false (check-generator next-starts-with-number-gen '(= "2" 3))))

;; Generator Generator -> Generator
(define/contract (until-generator first-gen then-gen)
  (-> generator/c generator/c generator/c)

  (define (check-first-until-then first-gen/current then-gen/current)
    (λ (world)
      (let-values ([(first-res first-gen/new)
		    (apply-generator first-gen/current world)]
		   [(then-res then-gen/new)
		    (apply-generator then-gen/current world)])
	(cond [(and first-res (not then-res))
	       ;; note: returning false while in first predicate because
	       ;; this is a *strong* until; THEN-PREDICATE *must* become
	       ;; true for this to be true
	       (values #f (check-first-until-then first-gen/new
						  then-gen/current))]

              ;; todo confirm: until doesn't say anything about
              ;; first-gen's truth once then-gen becomes true
              ;; Alternative: (when then-gen becomes true first-gen
              ;; must be false)
              ;; [(and (not first-res) then-res)
	      [then-res
	       (values then-res then-gen/new)]

	      [else
	       ;; FIRST has failed and so has THEN
	       (values #f #f)]))))

  (check-first-until-then first-gen then-gen))

(module+ test
 (define a-until-b-gen (until-generator (all-generator (curry equal? 'a))
					(all-generator (curry equal? 'b))))

 (check-true (check-generator a-until-b-gen '(a b)))
 (check-true (check-generator a-until-b-gen '(a a a b)))
 (check-true (check-generator a-until-b-gen '(a a a b b b b)))
 (check-true (check-generator a-until-b-gen '(a b b)))
 (check-true (check-generator a-until-b-gen '(b)))
 (check-true (check-generator a-until-b-gen '(b b b b b)))

 (check-false (check-generator a-until-b-gen '()))
 (check-false (check-generator a-until-b-gen '(a)))
 (check-false (check-generator a-until-b-gen '(a a)))
 (check-false (check-generator a-until-b-gen '(a b a)))
 (check-false (check-generator a-until-b-gen '(a a a a b a b b b b)))
 (check-false (check-generator a-until-b-gen '(b a a a)))
 (check-false (check-generator a-until-b-gen '(b b b b b a)))
 (check-false (check-generator a-until-b-gen '(a a b b 1)))
 (check-false (check-generator a-until-b-gen '(1 2 3)))
 (check-false (check-generator a-until-b-gen '("hello")))

 (define first-number-then-all-symbols
   (until-generator (first-generator number?)
		    (all-generator symbol?)))
 (check-true (check-generator first-number-then-all-symbols
			      '(1 a)))
 (check-true (check-generator first-number-then-all-symbols
			      '(42 a b c c)))
 (check-true (check-generator first-number-then-all-symbols
			      '(1000.0 b b kl g r edcsdsvc f)))
 (check-true (check-generator first-number-then-all-symbols
			      ;; should be true because A is never true and B is
			      '(b b kl g r edcsdsvc f)))

 ;; todo confirm: should this check succeed?
 ;; I could argue yes bc 1 satisfies A, so the whole sequence
 ;; satisfies A, and after 2 the rest satisfies B
 (check-true (check-generator first-number-then-all-symbols
                              '(1 2 b b kl g r edcsdsvc f)))

 (check-false (check-generator first-number-then-all-symbols
                              '(1 2 b 3 f)))
 (check-false (check-generator first-number-then-all-symbols
			       '(1 b b kl g r "edcsdsvc" f)))
 (check-false (check-generator first-number-then-all-symbols
			       '(1)))
 (check-false (check-generator first-number-then-all-symbols
			       '())))

;; Generator -> Generator
(define/contract (not-generator gen)
  (-> generator/c generator/c)

  (λ (world)
    (let-values ([(res new-gen) (apply-generator gen world)])
      (values (not res)
              (not-generator (or new-gen
                                 (all-generator true-pred)))))))

(module+ test
  (define not-first-number-then-all-symbols
    (not-generator first-number-then-all-symbols))
  (check-false (check-generator not-first-number-then-all-symbols
                               '(42 a b c c)))
  (check-false (check-generator not-first-number-then-all-symbols
                               '(1000.0 b b kl g r edcsdsvc f)))
  (check-true (check-generator not-first-number-then-all-symbols
                                '(1 2 b 3 kl g r edcsdsvc f)))
  (check-true (check-generator not-first-number-then-all-symbols
                                '(1)))

  (define not-a-until-b-gen (not-generator a-until-b-gen))
  (check-false (check-generator not-a-until-b-gen '(a b b)))
  (check-false (check-generator not-a-until-b-gen '(b)))
  (check-true (check-generator not-a-until-b-gen '(b b b b b a)))
  (check-true (check-generator not-a-until-b-gen '(a a b b 1)))

  (define not-next-starts-with-number-gen
    (not-generator next-starts-with-number-gen))
  (check-false (check-generator not-next-starts-with-number-gen '("nan" 2 a)))
  (check-false (check-generator not-next-starts-with-number-gen
                                '("nan" 2 a "b" 3)))
  (check-true (check-generator not-next-starts-with-number-gen '(1 a)))
  (check-true (check-generator not-next-starts-with-number-gen '(a a)))

  (define not-next-is-all-a-gen (not-generator next-is-all-a-gen))
  (check-false (check-generator not-next-is-all-a-gen '(#f a a a a a a)))
  (check-false (check-generator not-next-is-all-a-gen '(b a a a a a a)))
  (check-true (check-generator not-next-is-all-a-gen '(a b c)))
  (check-true (check-generator not-next-is-all-a-gen '(a a c)))

  (define not-first-a-gen (not-generator first-a-gen))
  (check-false (check-generator not-first-a-gen '(a b)))
  (check-true (check-generator not-first-a-gen '(b a b)))

  (define not-all-a-gen (not-generator all-a-gen))
  (check-false (check-generator not-all-a-gen '(a a a a a a)))
  (check-true (check-generator not-all-a-gen '(a b))))


(define/contract (or-generator a-gen b-gen)
  (-> generator/c generator/c generator/c)

  (λ (world)
    (let-values ([(a-accept? a-gen/new) (apply-generator a-gen world)]
                 [(b-accept? b-gen/new) (apply-generator b-gen world)])
      (values (or a-accept? b-accept?)
              (or-generator a-gen/new b-gen/new)))))

(module+ test
  (define or-true-gen (or-generator all-a-gen not-all-a-gen))
  (check-true (check-generator or-true-gen '(a a a)))
  (check-true (check-generator or-true-gen '(b 2 3 a "ashdh" #f a)))
  ;; False because both components require at least one element to become true
  (check-false (check-generator or-true-gen '()))

  (define next-is-number-or-all-b-gen
    (or-generator (next-generator (first-generator number?))
                  (all-generator (curry equal? 'b))))
  (check-true (check-generator next-is-number-or-all-b-gen '(b 1 b b b)))
  (check-true (check-generator next-is-number-or-all-b-gen '(b b b b)))
  (check-true (check-generator next-is-number-or-all-b-gen '(b 1 "b" #f)))
  (check-true (check-generator next-is-number-or-all-b-gen '(c -200 "a" #f)))
  (check-false (check-generator next-is-number-or-all-b-gen '(c b "a" #f)))
  (check-false (check-generator next-is-number-or-all-b-gen '(b b b b #f))))


(define/contract (and-generator a-gen b-gen)
  (-> generator/c generator/c generator/c)
  (not-generator (or-generator (not-generator a-gen)
                               (not-generator b-gen))))
(module+ test
  (define and-false-gen (and-generator all-a-gen not-all-a-gen))
  (check-false (check-generator and-false-gen '(a a a)))
  (check-false (check-generator and-false-gen '(b 2 3 a "ashdh" #f a)))
  (check-false (check-generator and-false-gen '()))

  (define all-even-and-next-is-2-gen
    (and-generator (next-generator (first-generator (curry = 2)))
                   (all-generator (and/c number? even?))))
  (check-true (check-generator all-even-and-next-is-2-gen '(16 2)))
  (check-true (check-generator all-even-and-next-is-2-gen '(0 2 4 6 8)))
  (check-true (check-generator all-even-and-next-is-2-gen '(2 2 2)))
  ;; False because next isn't 2: it's not anything.
  (check-false (check-generator all-even-and-next-is-2-gen '(42)))
  (check-false (check-generator all-even-and-next-is-2-gen '(1 2)))
  (check-false (check-generator all-even-and-next-is-2-gen '(0 2 3 4 6)))
  (check-false (check-generator all-even-and-next-is-2-gen '(0 2 b)))
  (check-false (check-generator all-even-and-next-is-2-gen '(0 2 #f 5))))


(define/contract (implies-generator premise-gen conclusion-gen)
  (-> generator/c generator/c generator/c)
  (or-generator (not-generator premise-gen)
                conclusion-gen))

(module+ test
  (define if-next-is-2-then-all-even
    (implies-generator (next-generator (first-generator (curry equal? 2)))
                       (all-generator (and/c number? even?))))
  ;; Premise satisfied and so is conclusion
  (check-true (check-generator if-next-is-2-then-all-even
                               '(0 2 4 6)))
  ;; Premise not satisfied...
  ;; But conclusion is
  (check-true (check-generator if-next-is-2-then-all-even
                               '(42)))
  (check-true (check-generator if-next-is-2-then-all-even
                               '(2 4 6 8)))
  ;; and neither is conclusion
  (check-true (check-generator if-next-is-2-then-all-even
                               '(a b c)))
  (check-true (check-generator if-next-is-2-then-all-even
                               '(1 3 5)))

  ;; Premise satisfied but not conclusion
  (check-false (check-generator if-next-is-2-then-all-even
                                '(1 2 3 5)))
  (check-false (check-generator if-next-is-2-then-all-even
                                '(1 2 a b)))
  (check-false (check-generator if-next-is-2-then-all-even
                                '(a 2 4 6))))
