#lang racket

(require "./dfa.rkt")

;; ltl == dfa

(define-syntax-rule (ltl/c dfa)
  (λ (seq)
    (let-values ([(dfa-result seq-remaining) (run dfa seq)])
      (dfa-accept? dfa-result))))

(define-syntax-rule (ltl/dfa/exact el)
  (define-dfa/autofail start fail
    [start #f ([el accept])]
    [accept #t ()]))

(define-syntax-rule (ltl/exact el)
  (ltl/dfa/exact el))


(define-syntax-rule (ltl/dfa/next dfa/after)
  (define-dfa start fail
    [start #f ([_ dfa/after])]))

(define-syntax-rule (ltl/next ltl/after)
  (ltl/dfa/next ltl/after))


;; Question: is until *U* supposed to continuously re-run ltl/first
;; until it returns a reject state, or is it just supposed to run it once
;; and then run ltl/then?
;;
;; Only running it once seems to be what the definition says, but then
;; you can't say
;; (ltl/exact 'a) *U* (ltl/exact 'b) <= a+b
;; Which seems intuitively to be the way one would want this to work..
;; 
;; Maybe we would need an extra ltl/repeat or something to express it
;; like this?
;; (ltl/repeat (ltl/exact 'a)) *U* (ltl/exact 'b) <= a+b

(define-syntax-rule (ltl/dfa/until dfa/first dfa/after)
  (make-dfa
   (λ (seq)
     (let-values ([(dfa/first/run seq-remaining)
		   (run-until-before-fail dfa/first seq)])
       (run dfa/after seq-remaining)))
   #f
   #f))

(define-syntax-rule (ltl/until ltl/first ltl/then)
  (ltl/dfa/until ltl/first ltl/then))
