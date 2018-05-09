#lang racket

(module+ test
  (require rackunit))

;; Generator = (World -> (values Bool Generator))

;; Generator List[World] -> (values Bool Generator)
(define (check-generator generator seq [init #f])
  (if (or (empty? seq) (false? generator))
      init
      (let-values ([(accept? next-generator) (generator (first seq))])
	(check-generator next-generator (rest seq) accept?))))


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
(define (next-generator next-predicate)
  (λ (world)
    (values #f (all-generator next-predicate))))

(module+ test
  (define next-is-all-a-gen (next-generator (curry equal? 'a)))

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
  (check-false (check-generator next-is-all-a-gen '(a b a a a a a))))

;; Generator Generator -> Generator
(define (until-generator first-predicate then-predicate)
  (define (check-first-until-then world)
    (let ([first-res (first-predicate world)]
	  [then-res (then-predicate world)])
      (cond [(and first-res (not then-res))
	     (values first-res check-first-until-then)]

	    [(and (not first-res) then-res)
	     (values then-res (all-generator then-predicate))]

	    [else
	     (values #f (all-generator false-pred))])))

  check-first-until-then)


