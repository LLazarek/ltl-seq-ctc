#lang brag
ltl-definitions : def-requires formula-def*
def-requires : "(" "require" (ID-TOK | string-module-path) ")"
string-module-path : STRING-TOK
formula-def : "[" ID-TOK ltl-formula "]"
ltl-formula : (ID-TOK | paren-ltl-formula)+
paren-ltl-formula : /"(" ltl-formula /")"
