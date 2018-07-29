#lang br

(provide ltl-lexer)

(require brag/support
         (prefix-in : br-parser-tools/lex-sre))

(define-lex-abbrev id (:+ (:or (:/ "A" "Z" "a" "z" "0" "9")
                               (char-set "!@#$%^&*-=+_:/=<>.?"))))

(define ltl-lexer
  (lexer-srcloc
   [(eof) eof]
   [(from/to ";" "\n") (token lexeme #:skip? #t)]
   [(from/to "\"" "\"") (token 'STRING-TOK (trim-ends "\"" lexeme "\""))]
   [(:or (char-set "[]()\"") "require") (token lexeme lexeme)]
   [id
    (token 'ID-TOK lexeme)]
   [(char-set " \n\t") (token lexeme #:skip? #t)]))

