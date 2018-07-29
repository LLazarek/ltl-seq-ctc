#lang br/quicklang

(define-macro (ltl-mb PARSE-TREE)
  #'(#%module-begin
     PARSE-TREE))
(provide (rename-out [ltl-mb #%module-begin]))

(define-macro (ltl-definitions DEF-REQUIRES FORMULA ...)
  #'(begin
      DEF-REQUIRES
      FORMULA ...))

(define-macro-cases def-requires
  [(def-requires "(" "require" (string-module-path PATH-STR) ")")
   #'(require PATH-STR)]
  [(def-requires "(" "require" ID-STR ")")
   (with-pattern ([ID (format-id #'ID-STR "~a" (syntax-e #'ID-STR))])
     #'(require ID))])

(define-macro (formula-def "[" ID BODY "]")
  ;; Using format-id allows the id definition to be seen
  ;; Outside the macro
  (with-pattern ([ID-STX (format-id #'ID "~a" (syntax-e #'ID))]
                 ;; [(BODY-STX ...) (format-datum '~a #'(BODY ...))]
                 )
    #'(begin (define ID-STX BODY)
             (provide ID-STX))))


(define-macro-cases ltl-formula
  [(ltl-formula "X" A)
   #'(c/next (ltl-formula A))]
  [(ltl-formula A "U" B)
   #'(c/until (ltl-formula A) (ltl-formula B))]
  [(ltl-formula "not" A)
   #'(c/not (ltl-formula A))]
  [(ltl-formula A "or" B)
   #'(c/or (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "and" B)
   #'(c/and (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "=>" B)
   #'(c/implies (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "<=>" B)
   #'(c/iff (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "R" B)
   #'(c/release (ltl-formula A) (ltl-formula B))]
  [(ltl-formula "F" A)
   #'(c/eventually (ltl-formula A))]
  [(ltl-formula "G" A)
   #'(c/globally (ltl-formula A))]

  ;; Deal with nesting introduced by parenthesized formulas
  [(ltl-formula (paren-ltl-formula FORM ...))
   #'(ltl-formula FORM ...)]
  [(ltl-formula (ltl-formula FORM ...))
   #'(ltl-formula FORM ...)]

  ;; Handle plain predicate
  [(ltl-formula PRED)
   (with-pattern ([PRED-ID (format-id #'PRED "~a" (syntax-e #'PRED))])
     #'(primitive/first PRED-ID))]

  ;; Failure clause
  [(ltl-formula A ...)
   #'(error (format "Invalid ltl formula operator/element in: ~a" '(A ...)))])

(define-macro (paren-ltl-formula FORM ...)
  #'(ltl-formula FORM ...))

(require "../ltl-nodfa.rkt")
(provide (all-from-out "../ltl-nodfa.rkt"))
(provide ltl-definitions ltl-formula paren-ltl-formula def-requires formula-def)

