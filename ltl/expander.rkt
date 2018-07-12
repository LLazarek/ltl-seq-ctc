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

;; (require (for-syntax racket/string))
;; (define-macro (formula-def FORMULA-STR)
;;   (define formula-elements (string-split (syntax->datum #'FORMULA-STR)))
;;   (with-pattern ([(FORMULA-DATUM ...) (format-datums '~a formula-elements)])
;;     #'(define FORMULA-DATUM ...)))

(define-macro (formula-def "[" ID BODY ... "]")
  (with-pattern ([ID-STX (format-datum '~a #'ID)]
                 [(BODY-STX ...) (format-datum '~a #'(BODY ...))])
    #''(define ID-STX (ltl-formula BODY-STX ...))))

(define-macro-cases ltl-formula
  [(ltl-formula 'X FORM ...)
   (next)])

(provide ltl-definitions racket-defs formula-def)
