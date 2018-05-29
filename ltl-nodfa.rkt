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

;; Base definitions
(define world/c any/c)
(define-struct ltl ())
(define-struct (ltl/true ltl) ())
(define-struct (ltl/false ltl) ())
(define-struct/contract (ltl/first ltl) ([predicate predicate/c]))
(define-struct/contract (ltl/all ltl) ([predicate predicate/c]))

(define (ensure-ltl . xs)
  (unless (andmap ltl? xs)
    (error "Error: non-ltl provided to ltl combinator.")))

(define-syntax (define-ltl-combinator stx)
  (syntax-case stx ()
    [(define-ltl-combinator name f ...)
     (syntax/loc stx
       ;; I'd like to use define-struct/contract here, but it doesn't
       ;; seem to work
       (struct name ltl (f ...) #:guard ensure-ltl))]))

;; Combinators
(define-ltl-combinator ltl/not ltl)
(define-ltl-combinator ltl/or lhs rhs)
(define-ltl-combinator ltl/next ltl)
(define-ltl-combinator ltl/until first then)
(define-ltl-combinator ltl/and lhs rhs)
(define-ltl-combinator ltl/implies lhs rhs)
(define-ltl-combinator ltl/iff lhs rhs)
(define-ltl-combinator ltl/release releaser held)
(define-ltl-combinator ltl/eventually ltl)
(define-ltl-combinator ltl/globally ltl)
(define-ltl-combinator ltl/weak-until first then)
(define-ltl-combinator ltl/strong-release releaser held)

(define-struct/contract ltl-state ([ltl ltl?]
                                   [accept? boolean?]
                                   [seq (listof world/c)])
  #:transparent)

(define/contract (step state)
  (ltl-state? . -> . ltl-state?)
  (match state
    [(ltl-state _ _ '()) state]

    [(ltl-state (ltl/true) _ (cons h t)) (ltl-state (ltl/true) #t t)]

    [(ltl-state (ltl/false) _ (cons h t)) (ltl-state (ltl/false) #f t)]

    [(ltl-state (ltl/first p) _ (cons h t))
     (let* ([res (p h)]
            [new-ltl (if res (ltl/true) (ltl/false))])
       (ltl-state new-ltl res t))]

    [(ltl-state (ltl/all p) _ (cons h t))
     (let* ([res (p h)]
            [new-ltl (if res (ltl/all p) (ltl/false))])
       (ltl-state new-ltl res t))]

    [(ltl-state (ltl/not ltl) r (cons h t))
     (let* ([stepped-inner (step (ltl-state ltl r (cons h t)))]
            [new-ltl (ltl/not (ltl-state-ltl stepped-inner))]
            [res (not (ltl-state-accept? stepped-inner))])
       (ltl-state new-ltl res t))]

    [(ltl-state (ltl/or lhs rhs) r (cons h t))
     (let* ([stepped-lhs (step (ltl-state lhs r (cons h t)))]
            [stepped-rhs (step (ltl-state rhs r (cons h t)))]
            [new-ltl (ltl/or (ltl-state-ltl stepped-lhs)
                             (ltl-state-ltl stepped-rhs))]
            [res (or (ltl-state-accept? stepped-lhs)
                     (ltl-state-accept? stepped-rhs))])
       (ltl-state new-ltl res t))]

    [(ltl-state (ltl/next ltl) r (cons h t))
     (ltl-state ltl #f t)]

    [(ltl-state (ltl/until first-ltl then-ltl) r (cons h t))
     (let* ([stepped-then (step (ltl-state then-ltl r (cons h t)))]
            [then-accepted? (ltl-state-accept? stepped-then)]
            [stepped-first (step (ltl-state first-ltl r (cons h t)))])
       (if then-accepted?
           (ltl-state (ltl-state-ltl stepped-then) #t t)
           (ltl-state (ltl/until (ltl-state-ltl stepped-first)
                                 then-ltl)
                      #f ;; this is strong until; then must become true
                      t)))]))


(define/contract (run ltl seq [init #f])
  ((ltl? (listof world/c)) (boolean?) . ->* . ltl-state?)

  (step-all (ltl-state ltl init seq)))

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

  ;; -------------------- not --------------------
  (check-runs (ltl/not (ltl/all symbol?)) a b c -> #f)
  (check-runs (ltl/not (ltl/all symbol?)) a 1 c -> #t)
  (check-runs (ltl/not (ltl/all symbol?)) 1 #t #f -> #t)
  (check-runs (ltl/not (ltl/first symbol?)) 1 #t #f -> #t)
  (check-runs (ltl/not (ltl/first symbol?)) a #t #f -> #f)

  ;; -------------------- or --------------------
  ;; #t or #t -> #t
  (check-runs (ltl/or (ltl/first negative-integer?)
                      (ltl/all integer?))
              -1 2 3 -> #t)
  ;; #f or #t -> #t
  (check-runs (ltl/or (ltl/first negative-integer?)
                      (ltl/all integer?))
              1 2 3 -> #t)
  ;; #t or #f -> #t
  (check-runs (ltl/or (ltl/first negative-integer?)
                      (ltl/all integer?))
              -1 a b -> #t)
  ;; #f or #f -> #f
  (check-runs (ltl/or (ltl/first negative-integer?)
                      (ltl/all integer?))
              #t a b -> #f)

  ;; -------------------- next --------------------
  (check-runs (ltl/next (ltl/first integer?)) 1 2 #f -> #t)
  (check-runs (ltl/next (ltl/first integer?)) a 2 #f -> #t)
  (check-runs (ltl/next (ltl/first integer?)) a b #f -> #f)
  (check-runs (ltl/next (ltl/all integer?)) 1 2 #f -> #f)
  (check-runs (ltl/next (ltl/all integer?)) a 2 #f -> #f)
  (check-runs (ltl/next (ltl/all integer?)) a 2 3 -> #t)

  ;; -------------------- until --------------------
  ;; First element satisfies A, B never satisfied
  (check-runs (ltl/until (ltl/all integer?)
                         (ltl/all symbol?))
              0 1 -> #f)
  ;; First element satisfies A, second element satisfies B
  (check-runs (ltl/until (ltl/all integer?)
                         (ltl/all symbol?))
              0 b c -> #t)
  ;; First element satisfies B
  (check-runs (ltl/until (ltl/all integer?)
                         (ltl/all symbol?))
              b -> #t)
  ;; First element satisfies A, second element fails both A and B
  (check-runs (ltl/until (ltl/all integer?)
                         (ltl/all symbol?))
              0 #f -> #f)
  )
