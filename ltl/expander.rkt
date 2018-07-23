#lang br/quicklang

(define-macro (ltl-mb PARSE-TREE)
  #'(#%module-begin
     PARSE-TREE))
(provide (rename-out [ltl-mb #%module-begin]))

(define-macro (ltl-definitions RACKET-DEFS FORMULA ...)
  #'(begin
      RACKET-DEFS
      FORMULA ...))

(require (for-syntax racket/port))
(define-macro (racket-defs DEFS-STR)
  (define def-sexps
    (port->list read (open-input-string (syntax->datum #'DEFS-STR))))
  (with-pattern ([(DEFS-DATUM ...) (format-datums '~a def-sexps)])
    #'(begin DEFS-DATUM ...)))

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
     #'(list 'primitive/first 'PRED-ID))]
  [(ltl-formula A ...)
   #''(catch-all A ...)])

(provide ltl-definitions racket-defs formula-def)
(require racket/list)
(provide (all-from-out racket/list))

