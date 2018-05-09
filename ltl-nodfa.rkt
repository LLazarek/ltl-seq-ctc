#lang racket

(module+ test
  (require rackunit))

;; Generator := (World -> (values Bool Generator)) | #f

;; Generator Seq[World] -> (values Bool Generator)
(define (check-generator generator seq [init #f])
  (if (or (empty? seq) (false? generator))
      init
      (let-values ([(accept? next-generator) (generator (first seq))])
	(check-generator next-generator (rest seq) accept?))))

;; Generator World -> (values Bool Generator)
(define (apply-generator gen el)
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
(define (first-generator pred)
  (λ (world)
    (values (pred world) #f)))

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
(define (all-generator pred)
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
  (check-false (check-generator all-a-gen '(a a a a a a "hi"))))

;; Generator -> Generator
(define (next-generator next)
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
(define (until-generator first-gen then-gen)
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

	      [(and (not first-res) then-res)
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

 (check-false (check-generator first-number-then-all-symbols
			       '(1 2 b b kl g r edcsdsvc f)))
 (check-false (check-generator first-number-then-all-symbols
			       '(1 b b kl g r "edcsdsvc" f)))
 (check-false (check-generator first-number-then-all-symbols
			       '(1)))
 (check-false (check-generator first-number-then-all-symbols
			       '())))

;; Generator -> Generator
(define (not-generator gen)
  (λ (world)
    (let-values ([(res new-gen) (gen world)])
      (values (not res) (not-generator new-gen)))))

