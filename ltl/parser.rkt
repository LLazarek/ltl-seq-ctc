#lang brag
ltl-definitions : def-requires formula-def*
def-requires : "(" "require" ID-TOK ")"
formula-def : "[" ID-TOK ID-TOK+ "]"
