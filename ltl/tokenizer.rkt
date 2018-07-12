#lang br/quicklang
(require brag/support
         (prefix-in : br-parser-tools/lex-sre))

(define (make-tokenizer port)
  (port-count-lines! port)
  (define (next-token)
    (define ltl-lexer
      (lexer
       [(eof) eof]
       [(from/to ";" "\n") (next-token)]
       [(from/to "DEFINITIONS\n" "\nEND")
        (token 'DEFS-TOK (trim-ends "DEFINITIONS\n" lexeme "\nEND")
               #:position (+ (pos lexeme-start) 19)
               #:line (pos lexeme-start)
               #:column (col lexeme-start)
               #:span (- (pos lexeme-end)
                         (pos lexeme-start)
                         22))]
       [(:+ (:or (:/ "A" "Z" "a" "z" "0" "9")
                 (char-set "?!-_:/")))
        (token 'ID-TOK lexeme
               #:position (pos lexeme-start)
               #:line (pos lexeme-start)
               #:column (col lexeme-start)
               #:span (- (pos lexeme-end)
                         (pos lexeme-start)))]
       [(char-set "[]") lexeme]
       ;; [(from/to "[" "]")
       ;;  (token 'FORMULA-TOK (trim-ends "[" lexeme "]")
       ;;         #:position (+ (pos lexeme-start) 1)
       ;;         #:line (pos lexeme-start)
       ;;         #:column (col lexeme-start)
       ;;         #:span (- (pos lexeme-end)
       ;;                   (pos lexeme-start)
       ;;                   2))]
       ;; [(from/to "(" ")")
       ;;  (token 'GROUP-TOK (trim-ends "(" lexeme ")")
       ;;         #:position (+ (pos lexeme-start) 1)
       ;;         #:line (pos lexeme-start)
       ;;         #:column (col lexeme-start)
       ;;         #:span (- (pos lexeme-end)
       ;;                   (pos lexeme-start)
       ;;                   2))]
       ;; [(:+ "[A-Za-z?!-_:/]")
       ;;  (token 'ELEMENT-TOK lexeme
       ;;         #:position (pos lexeme-start)
       ;;         #:line (pos lexeme-start)
       ;;         #:column (col lexeme-start)
       ;;         #:span (- (pos lexeme-end)
       ;;                   (pos lexeme-start)))]
       [(char-set " \n\t") (next-token)]))
    (ltl-lexer port))
  next-token)

(provide make-tokenizer)
