#lang br/quicklang

(require "lexer.rkt" brag/support)

(define (make-tokenizer port [path #f])
  (port-count-lines! port)
  (lexer-file-path path)
  (define (next-token) (ltl-lexer port))
  next-token)

(provide make-tokenizer)
