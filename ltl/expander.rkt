#lang br/quicklang

(define-macro (ltl-mb PARSE-TREE)
  #'(#%module-begin
     PARSE-TREE))
(provide (rename-out [ltl-mb #%module-begin]))

(define-macro (ltl-definitions DEF-REQUIRES FORMULA ...)
  #'(begin
      DEF-REQUIRES
      FORMULA ...))

(define-macro (def-requires "(" "require" ID-STR ")")
  (with-pattern ([ID (format-id #'ID-STR "~a" (syntax-e #'ID-STR))])
    #'(require ID)))

(define-macro (formula-def "[" ID BODY ... "]")
  ;; Using format-id allows the id definition to be seen
  ;; Outside the macro
  (with-pattern ([ID-STX (format-id #'ID "~a" (syntax-e #'ID))]
                 ;; [(BODY-STX ...) (format-datum '~a #'(BODY ...))]
                 )
    #'(define ID-STX (ltl-formula BODY ...))))

(define-macro-cases ltl-formula
  [(ltl-formula "X" FORMULA)
   #'(list 'c/next (ltl-formula FORMULA))]
  [(ltl-formula PRED)
   (with-pattern ([PRED-ID (format-id #'PRED "~a" (syntax-e #'PRED))])
     #'(list 'primitive/first PRED-ID))]
  [(ltl-formula A ...)
   #''(catch-all A ...)])

(provide ltl-definitions def-requires formula-def)
(require racket/list)
(provide (all-from-out racket/list))

