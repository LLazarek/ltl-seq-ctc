#lang br/quicklang
(require "tokenizer.rkt" "parser.rkt")

(define (read-syntax path port)
  (define parse-tree (parse path (make-tokenizer port)))
  (define module-datum `(module ltl-module ltl/expander
                          ,parse-tree))
  (datum->syntax #f module-datum))

(provide read-syntax)