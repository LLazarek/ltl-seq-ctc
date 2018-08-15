#lang racket

(require redex "ltl-model.rkt")


(module+ test
  (require "model-test-common.rkt"))

(define-syntax (reduces-with stx)
  (syntax-case stx (: --> -/->)
    [(reduces-with red : A --> B)
     (syntax/loc stx
       (equal? (apply-reduction-relation* red (term A))
               (list (term B))))]
    [(reduces-with red : A -/-> B)
     (syntax/loc stx
       (not (reduces-with red : A --> B)))]))

(define-judgment-form ltl-lang
  #:mode (~> I O)
  [--- "true"
       (~> (state/left true r (cons seq-el seq)) (state/left true #t seq))]
  [--- "false"
       (~> (state/left false r (cons seq-el seq)) (state/left false #f seq))]


  ;; This doesn't work??
  ;; I have tried replacing with the identical expr that works in ltl-model.
  ;; Still doesn't seem to guard properly.
  ;; This makes me wonder if `side-condition` behaves the same way for
  ;; judgment forms as it does for reduction relations. But the docs say they
  ;; do behave the same way.
  ;; Nonetheless, manually testing each of the (reduces-with ...) with
  ;; (term (zero? zero)) produces the expected results (ie not both #t).
  ;; An interesting thing though is that print statements inside
  ;; the side-condition never get printed!
  ;; Doing the same in ltl-red *does* cause the expected printouts
  ;; (e.g. with `traces`), so it seems that the side condition is being
  ;; ignored entirely..
  ;; 
  [(side-condition (begin
                     (printf "first/t: checking ~v -/-> #f\n" (term (p seq-el)))
                     (reduces-with predλ-red : (p seq-el) -/-> #f)))
   --- "first/t"
   (~> (state/left (first p) r (cons seq-el seq))
       (state/left true #t seq))]
  [(side-condition (begin
                     (printf "first/f: checking ~v --> #f\n" (term (p seq-el)))
                     (reduces-with predλ-red : (p seq-el) --> #f)))
   --- "first/f"
   (~> (state/left (first p) r (cons seq-el seq))
       (state/left false #f seq))]

  [
   --- "next"
   (~> (state/left (next ltl) r (cons seq-el seq))
       (state/left ltl ? seq))]

  [(~> (state/left ltl_B r (cons seq-el seq))
       (state/left _     #t _))
   --- "until/B-t"
   (~> (state/left (until ltl_A ltl_B) r (cons seq-el seq))
       (state/left true #t seq))]
  [(~> (state/left ltl_B r (cons seq-el seq))
       (state/left _     #f _))
   (~> (state/left ltl_A r (cons seq-el seq))
       (state/left _     #t _))
   --- "until/B-f/A-t"
   (~> (state/left (until ltl_A ltl_B) r (cons seq-el seq))
       (state/left (until ltl_A ltl_B) r seq))]
  [(~> (state/left ltl_B r (cons seq-el seq))
       (state/left _     #f _))
   (~> (state/left ltl_A r (cons seq-el seq))
       (state/left _     #f _))
   --- "until/B-f/A-f"
   (~> (state/left (until ltl_A ltl_B) r (cons seq-el seq))
       (state/left false #f seq))]

  [(~> (state/left ltl_0 r_0 (cons seq-el seq))
       (state/left ltl_1 r_1 seq))
   --- "not"
   (~> (state/left (not ltl_0) r_0 (cons seq-el seq))
       (state/left (not ltl_1) (not-metafn r_1) seq))]

  [(~> (state/left ltl_A_0 r_0 (cons seq-el seq))
       (state/left ltl_A_1 r_A seq))
   (~> (state/left ltl_B_0 r_0 (cons seq-el seq))
       (state/left ltl_B_1 r_B seq))
   --- "or"
   (~> (state/left (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
       (state/left (or ltl_A_1 ltl_B_1) (or-metafn r_A r_B) seq))]

  [
   --- "and"
   (~> (state/left (and ltl_A ltl_B) r seq)
       (state/left (not (or (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "implies"
   (~> (state/left (implies ltl_A ltl_B) r seq)
       (state/left (or (not ltl_A) ltl_B) r seq))]
  [
   --- "iff"
   (~> (state/left (iff ltl_A ltl_B) r seq)
       (state/left (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq))]
  [
   --- "release"
   (~> (state/left (release ltl_A ltl_B) r seq)
       (state/left (not (until (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "eventually"
   (~> (state/left (eventually ltl) r seq)
       (state/left (until true ltl) r seq))]
  [
   --- "globally"
   (~> (state/left (globally ltl) r seq)
       (state/left (not (eventually (not ltl))) r seq))])

(module+ test
  (check-true
   (judgment-holds (~> (state/left true #t (cons zero empty))
                       (state/left true #t empty))))
  (check-false
   (judgment-holds (~> (state/left (first zero?) ? (cons zero empty))
                       (state/left false #f empty))))
  (check-true
   (judgment-holds (~> (state/left (first zero?) ? (cons zero empty))
                       (state/left true #t empty)))))


;; -------------------- Random parity checking --------------------
(module+ test
  (define-syntax-rule (assert expr)
    (unless expr
      (error "Assertion failed:" 'expr)))


  (define (extract-binding match-list sym)
    (define match-struct (first match-list))
    (define bindings (match-bindings match-struct))
    (struct nothing ())
    (define matching-binding
      (for/fold ([sym-binding (nothing)])
                ([binding (in-list bindings)])
        (if (equal? (bind-name binding) sym)
            (bind-exp binding)
            sym-binding)))
    (if (nothing? matching-binding)
        (error "No binding found for ~v in ~v!" sym bindings)
        matching-binding))
  (define (get-outcome/ctx ltl-formula seq)
    (assert (redex-match? ltl-lang ltl ltl-formula))
    (assert (not (redex-match? ltl-lang empty seq)))

    (define end-terms
      (apply-reduction-relation* ltl-red
                                 (term (state/left ,ltl-formula ? ,seq))))
    (define end-term (first end-terms))
    (define matched/state-variant (redex-match ltl-lang
                                               (ltl-state-variant _ r _)
                                               end-term))
    (define matches-meta? (redex-match? ltl-lang meta-state end-term))

    (define false-or-empty? (or/c false? empty?))
    (cond [matches-meta?
           (term ?)]

          [(not (false-or-empty? matched/state-variant))
           (extract-binding matched/state-variant 'r)]

          [else
           (error "Something went horribly wrong")]))
  (define-syntax-rule (get-outcome/ctx* ltl-formula seq)
    (get-outcome/ctx (term ltl-formula) (term seq)))
  


  (check-equal? (get-outcome/ctx* (first zero?)
                                  (cons zero empty))
                #t)
  (check-equal? (get-outcome/ctx* (next (first zero?))
                                  (cons #f empty))
                '?)
  (check-equal? (get-outcome/ctx* (next (first zero?))
                                  (cons #f (cons ,one empty)))
                #f)
  (check-equal? (get-outcome/ctx* (until (first ,<=3?) (first zero?))
                                  (cons ,one (cons ,four empty)))
                #f)
  (check-equal? (get-outcome/ctx* (until (first ,<=3?) (first zero?))
                                  (cons zero empty))
                #t)
  (check-equal? (get-outcome/ctx* (until (first ,<=3?) (first zero?))
                                  (cons ,one empty))
                '?)
  (check-equal? (get-outcome/ctx* (until (first ,<=3?) (first zero?))
                                  (cons ,one (cons ,two empty)))
                '?)



  ;; todo: Doesn't work
  (define (get-outcome/jf ltl-formula seq)
    (judgment-holds (~> (state/left ,ltl-formula ? seq)
                        (state/left ltl outcome seq_1))
                    outcome))
  (define-syntax-rule (get-outcome/jf* ltl-formula seq)
    (get-outcome/jf (term ltl-formula) (term seq)))



  (define (models-equivalent-for ltl-formula seq)
    (define ctx-outcome (get-outcome/ctx ltl-formula seq))
    (define jf-outcome (get-outcome/jf ltl-formula seq))
    (equal? ctx-outcome jf-outcome)))
