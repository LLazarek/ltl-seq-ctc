#lang brag
ltl-definitions : racket-defs formula-def*
racket-defs : DEFS-TOK
formula-def : "[" ID-TOK ID-TOK+ "]"
