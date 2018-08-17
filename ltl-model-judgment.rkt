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


  ;; Note the unquote! Necessary in define-judgment-form.
  [(side-condition ,(reduces-with predλ-red : (p seq-el) -/-> #f))
   --- "first/t"
   (~> (state/left (first p) r (cons seq-el seq))
       (state/left true #t seq))]
  [(side-condition ,(reduces-with predλ-red : (p seq-el) --> #f))
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
                       (state/left true #t empty))))
  (check-true
   (judgment-holds (~> (state/left (first zero?) ? (cons #f empty))
                       (state/left false #f empty))))
  (check-true
   (judgment-holds (~> (state/left (first zero?) ? (cons #f (cons zero empty)))
                       (state/left false #f (cons zero empty))))))


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
  (define (get-outcome red ltl-formula seq)
    (assert (redex-match? ltl-lang ltl ltl-formula))
    (assert (not (redex-match? ltl-lang empty seq)))

    (define end-terms
      (apply-reduction-relation* red
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
  (define-syntax-rule (get-outcome* red ltl-formula seq)
    (get-outcome red (term ltl-formula) (term seq)))
  


  (check-equal? (get-outcome* ltl-red
                              (first zero?)
                              (cons zero empty))
                #t)
  (check-equal? (get-outcome* ltl-red
                              (next (first zero?))
                              (cons #f empty))
                '?)
  (check-equal? (get-outcome* ltl-red
                              (next (first zero?))
                              (cons #f (cons ,one empty)))
                #f)
  (check-equal? (get-outcome* ltl-red
                              (until (first ,<=3?) (first zero?))
                              (cons ,one (cons ,four empty)))
                #f)
  (check-equal? (get-outcome* ltl-red
                              (until (first ,<=3?) (first zero?))
                              (cons zero empty))
                #t)
  (check-equal? (get-outcome* ltl-red
                              (until (first ,<=3?) (first zero?))
                              (cons ,one empty))
                '?)
  (check-equal? (get-outcome* ltl-red
                              (until (first ,<=3?) (first zero?))
                              (cons ,one (cons ,two empty)))
                '?)



  (define (models-equivalent-for? ltl-formula seq)
    (define ltl-red-outcome (get-outcome ltl-red ltl-formula seq))
    (define ~>-outcome (get-outcome ~> ltl-formula seq))
    (equal? ltl-red-outcome ~>-outcome))

  (define-syntax-rule (models-equivalent-for?* ltl-formula seq)
    (models-equivalent-for? (term ltl-formula) (term seq)))

  (check-true (models-equivalent-for?*
               (first zero?)
               (cons zero empty)))
  (check-true (models-equivalent-for?*
               (next (first zero?))
               (cons #f empty)))
  (check-true (models-equivalent-for?*
               (next (first zero?))
               (cons #f (cons ,one empty))))
  (check-true (models-equivalent-for?*
               (until (first ,<=3?) (first zero?))
               (cons ,one (cons ,four empty))))
  (check-true (models-equivalent-for?*
               (until (first ,<=3?) (first zero?))
               (cons zero empty)))
  (check-true (models-equivalent-for?*
               (until (first ,<=3?) (first zero?))
               (cons ,one empty)))
  (check-true (models-equivalent-for?*
               (until (first ,<=3?) (first zero?))
               (cons ,one (cons ,two empty))))


  ;; Random testing
  (define (models-equivalent-for?/empty-guarded ltl-formula seq)
    (if (redex-match? ltl-lang empty seq)
        (term ?)
        (models-equivalent-for? ltl-formula seq)))
  (redex-check ltl-lang (ltl seq)
               (models-equivalent-for?/empty-guarded (term ltl) (term seq))))
