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
  [(ltl-formula "X" A)
   #'(list 'c/next (ltl-formula A))]
  [(ltl-formula A "U" B)
   #'(list 'c/until (ltl-formula A) (ltl-formula B))]
  [(ltl-formula "not" A)
   #'(list 'c/not (ltl-formula A))]
  [(ltl-formula A "or" B)
   #'(list 'c/or (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "and" B)
   #'(list 'c/and (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "=>" B)
   #'(list 'c/implies (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "<=>" B)
   #'(list 'c/iff (ltl-formula A) (ltl-formula B))]
  [(ltl-formula A "R" B)
   #'(list 'c/release (ltl-formula A) (ltl-formula B))]
  [(ltl-formula "F" A)
   #'(list 'c/eventually (ltl-formula A))]
  [(ltl-formula "G" A)
   #'(list 'c/globally (ltl-formula A))]
  [(ltl-formula PRED)
   (with-pattern ([PRED-ID (format-id #'PRED "~a" (syntax-e #'PRED))])
     #'(list 'primitive/first PRED-ID))]
  [(ltl-formula A ...)
   #''(catch-all A ...)])

;; todo: Add parenthesization

(provide ltl-definitions def-requires formula-def)
(require racket/list)
(provide (all-from-out racket/list))

