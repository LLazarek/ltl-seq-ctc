#lang racket

;; dfa ::= (transition-λ accept?)
;; transition-λ : seq -> (values (list transition-λ accept?) seq)
(define-struct dfa (state accept? done?) #:transparent)

(define-syntax (define-dfa stx)
  (syntax-case stx ()
    [(_ start-state fail-state
	[state accept? ([input next-state] ...)] ...)
     #'(let ([state #f] ... [fail-state #f])
	 (set! state (make-dfa (λ (seq)
				 (match (first seq)
				   [input (values next-state (rest seq))]
				   ...))
			       accept?
			       #f))
	 ...
	 (set! fail-state (make-dfa (λ (seq) (values fail-state seq))
				    #f
				    #t))
	 start-state)]))

(define-syntax (define-dfa/autofail stx)
  (syntax-case stx ()
    [(_ start-state fail-state
	[state accept? ([input next-state] ...)] ...)
     #'(define-dfa start-state fail-state
	 [state accept? ([input next-state] ... [_ fail-state])]
	 ...)]))

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
(define mydfa2 (define-dfa/autofail start fail
		 ;; States
		 [start #f ([#\a A]
			    [#\b B])]
		 [A #t ([#\a A])]
		 [B #t ([#\b B])]))

(define (run a-dfa seq)
  (if (or (dfa-done? a-dfa) (empty? seq))
      (values a-dfa seq)
      (let-values ([(new-dfa new-seq) ((dfa-state a-dfa) seq)])
	(run new-dfa new-seq))))

;; Runs A-DFA on SEQ until it fails
;; Then it returns the dfa and seq from the step *before* A-DFA failed
;;
;; If the returned sequence is empty, then the dfa ran without failing
;; or not at all (because the given SEQ was empty)
(define (run-until-before-fail a-dfa seq)
  (if (or (dfa-done? a-dfa) (empty? seq))
      (values a-dfa seq)
      (let-values ([(new-dfa new-seq) ((dfa-state a-dfa) seq)])
	(if (dfa-done? new-dfa)
	    (if (dfa-accept? new-dfa)
		(values new-dfa new-seq) ;; ran successfully all the way
		(values a-dfa seq)) ;; that last step failed
	    (run-until-before-fail new-dfa new-seq)))))

(provide make-dfa dfa? dfa-accept? dfa-done? dfa-state
	 define-dfa define-dfa/autofail
	 run run-until-before-fail)
