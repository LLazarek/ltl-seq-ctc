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
       (~> (state true r (cons seq-el seq)) (state true #t seq))]
  [--- "false"
       (~> (state false r (cons seq-el seq)) (state false #f seq))]

  [(side-condition (reduces-with predλ-red : (p seq-el) -/-> #f))
   --- "first/t"
   (~> (state (first p) r (cons seq-el seq))
       (state true #t seq))]
  [(side-condition (reduces-with predλ-red : (p seq-el) --> #f))
   --- "first/f"
   (~> (state (first p) r (cons seq-el seq))
       (state false #f seq))]

  [
   --- "next"
   (~> (state (next ltl) r (cons seq-el seq))
       (state ltl ? seq))]

  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #t _))
   --- "until/B-t"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state true #t seq))]
  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #f _))
   (~> (state ltl_A r (cons seq-el seq))
       (state _     #t _))
   --- "until/B-f/A-t"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state (until ltl_A ltl_B) r seq))]
  [(~> (state ltl_B r (cons seq-el seq))
       (state _     #f _))
   (~> (state ltl_A r (cons seq-el seq))
       (state _     #f _))
   --- "until/B-f/A-f"
   (~> (state (until ltl_A ltl_B) r (cons seq-el seq))
       (state false #f seq))]

  [(~> (state ltl_0 r_0 (cons seq-el seq))
       (state ltl_1 r_1 seq))
   --- "not"
   (~> (state (not ltl_0) r_0 (cons seq-el seq))
       (state (not ltl_1) (not-metafn r_1) seq))]

  [(~> (state ltl_A_0 r_0 (cons seq-el seq))
       (state ltl_A_1 r_A seq))
   (~> (state ltl_B_0 r_0 (cons seq-el seq))
       (state ltl_B_1 r_B seq))
   --- "or"
   (~> (state (or ltl_A_0 ltl_B_0) r_0 (cons seq-el seq))
       (state (or ltl_A_1 ltl_B_1) (or-metafn r_A r_B) seq))]

  [
   --- "and"
   (~> (state (and ltl_A ltl_B) r seq)
       (state (not (or (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "implies"
   (~> (state (implies ltl_A ltl_B) r seq)
       (state (or (not ltl_A) ltl_B) r seq))]
  [
   --- "iff"
   (~> (state (iff ltl_A ltl_B) r seq)
       (state (and (implies ltl_A ltl_B) (implies ltl_B ltl_A)) r seq))]
  [
   --- "release"
   (~> (state (release ltl_A ltl_B) r seq)
       (state (not (until (not ltl_A) (not ltl_B))) r seq))]
  [
   --- "eventually"
   (~> (state (eventually ltl) r seq)
       (state (until true ltl) r seq))]
  [
   --- "globally"
   (~> (state (globally ltl) r seq)
       (state (not (eventually (not ltl))) r seq))])

(module+ test
  (check-true (judgment-holds (~> (state true #t (cons zero empty))
                                  (state true #t empty)))))

  
  (judgment-holds (~> (state true #t (cons zero empty)) (state true #t empty))))
