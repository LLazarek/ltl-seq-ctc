#lang racket

(module+ test
  (require rackunit)
  ;; note: this version works but upon test failure points inside of
  ;; this definition; the below version correctly preserves source
  ;; location so that test failure points to the actual test code that
  ;; fails
  #;(define-syntax (check-runs stx)
    (syntax-case stx (->)
      [(check-runs ltl seq ... -> accept?)
       #'(check-match (run ltl '(seq ...)) (ltl-state _ accept? '()))]))
  (define-syntax (check-runs stx)
    (syntax-case stx (->)
      [(check-runs ltl seq ... -> accept?)
       (syntax/loc stx
         (check-match (run ltl '(seq ...)) (ltl-state _ accept? '())))]))

  ;; Note: This exact function is provided by rackunit, but it reports
  ;; failure locations inside of the rackunit source. So make my own
  ;; version that works correctly.
  (define-syntax-rule (check-match val pat)
    (check-true (match val
                  [pat #t]
                  [_ #f]))))

(define world/c any/c)
(define-struct ltl ())
(define-struct (ltl/true ltl) ())
(define-struct (ltl/false ltl) ())
(define-struct/contract (ltl/first ltl) ([predicate (-> world/c boolean?)]))
(define-struct/contract (ltl/all ltl) ([predicate (-> world/c boolean?)]))
(define-struct/contract (ltl/not ltl) ([ltl ltl?]))
(define-struct/contract (ltl/or ltl) ([lhs ltl?] [rhs ltl?]))
(define-struct/contract (ltl/next ltl) ([ltl ltl?]))
(define-struct/contract (ltl/until ltl) ([first ltl?] [then ltl?]))

(define-struct/contract ltl-state ([ltl ltl?]
                                   [accept? boolean?]
                                   [seq (listof world/c)])
  #:transparent)

(define/contract (step state)
  (ltl-state? . -> . ltl-state?)
  (match state
    [(ltl-state _ _ '()) state]
    [(ltl-state (ltl/true) _ (cons h t)) (make-ltl-state (ltl/true) #t t)]
    [(ltl-state (ltl/false) _ (cons h t)) (make-ltl-state (ltl/false) #f t)]
    [(ltl-state (ltl/first p) _ (cons h t))
     (let* ([res (p h)]
            [new-ltl (if res (ltl/true) (ltl/false))])
       (make-ltl-state new-ltl res t))]
    [(ltl-state (ltl/all p) _ (cons h t))
     (let* ([res (p h)]
            [new-ltl (if res (make-ltl/all p) (ltl/false))])
       (make-ltl-state new-ltl res t))]
    [(ltl-state (ltl/not ltl) r (cons h t))
     (let* ([stepped-inner (step (ltl-state ltl r (cons h t)))]
            [new-ltl (make-ltl/not (ltl-state-ltl stepped-inner))]
            [res (not (ltl-state-accept? stepped-inner))])
       (make-ltl-state new-ltl res t))]
    [(ltl-state (ltl/or lhs rhs) r (cons h t))
     (let* ([stepped-lhs (step (ltl-state lhs r (cons h t)))]
            [stepped-rhs (step (ltl-state rhs r (cons h t)))]
            [new-ltl (make-ltl/or (ltl-state-ltl stepped-lhs)
                                  (ltl-state-ltl stepped-rhs))]
            [res (or (ltl-state-accept? stepped-lhs)
                     (ltl-state-accept? stepped-rhs))])
       (make-ltl-state new-ltl res t))]
    [(ltl-state (ltl/next ltl) r (cons h t))
     (make-ltl-state ltl #f t)]
    [(ltl-state (ltl/until first-ltl then-ltl) r (cons h t))
     (let* ([stepped-then (step (ltl-state then-ltl r (cons h t)))]
            [then-accepted? (ltl-state-accept? stepped-then)]
            [stepped-first (step (ltl-state first-ltl r (cons h t)))]
            [new-ltl (if then-accepted?
                         (ltl-state-ltl stepped-then)
                         (make-ltl/until (ltl-state-ltl stepped-first)
                                         (ltl-state-ltl stepped-then)))])
       (make-ltl-state new-ltl then-accepted? t))]))


(define/contract (run ltl seq [init #f])
  ((ltl? (listof world/c)) (boolean?) . ->* . ltl-state?)

  (step-all (make-ltl-state ltl init seq)))

(define/contract (step-all state)
  (ltl-state? . -> . ltl-state?)

  (define stepped (step state))
  (if (equal? state stepped)
      state
      (step-all stepped)))

(module+ test
  ;; -------------------- true, false --------------------
  (check-runs (ltl/true) 1 -> #t)
  (check-runs (ltl/false) 1 -> #f)

  ;; -------------------- first --------------------
  ;; first satisfies
  (check-runs (ltl/first zero?) 0 -> #t)
  ;; first fails
  (check-runs (ltl/first zero?) 1 -> #f)
  ;; first satisfies, with more after
  (check-runs (ltl/first zero?) 0 b c -> #t)
  ;; first fails, with more after
  (check-runs (ltl/first zero?) 1 b c -> #f)

  ;; -------------------- all --------------------
  (check-runs (ltl/all symbol?) a b c -> #t)
  (check-runs (ltl/all symbol?) a 2 c -> #f)
  (check-runs (ltl/all symbol?) 1 #t '() -> #f)
  )

