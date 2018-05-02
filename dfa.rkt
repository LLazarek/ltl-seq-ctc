#lang racket

#|(define ltl/exact/c first-equal?/c)
;; not/c
;; or/c
(define (first-equal?/c spec)
  (λ (seq) (equal? spec (first seq))))
(define (ltl/next/c A)
  (λ (seq) ((first-equal?/c A) (rest seq))))
|#

(define-struct dfa (state accept?) #:transparent)

(define-syntax (define-dfa stx)
  (syntax-case stx ()
    [(_ start-state fail-state
	[state accept? ([input next-state] ...)] ...)
     #'(let ([state #f] ... [fail-state #f])
	 (set! state (make-dfa (λ (seq)
				 (match (first seq)
				   [input (values next-state (rest seq))]
				   ...))
			       accept?))
	 ...
	 (set! fail-state (make-dfa (λ (seq) (values fail-state seq)) #f))
	 start-state)]))

;; example:
(define mydfa (define-dfa start fail
		;; States
		[start #f ([#\a A]
			   [#\b B]
			   [_ fail])]
		[A #t ([#\a A]
		       [_ fail])]
		[B #t ([#\b B]
		       [_ fail])]))

;; dfa ::= (list transition-λ accept?)
;; transition-λ : seq -> (values (list transition-λ accept?) seq)

(define (run a-dfa seq)
  (if (empty? seq)
      a-dfa
      (let-values ([(new-dfa new-seq) ((dfa-state a-dfa) seq)])
	(run new-dfa new-seq))))

(provide )
