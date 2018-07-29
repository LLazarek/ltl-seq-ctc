#lang ltl

(require "test-defs.rkt")

; First element is a number
[ltl/p  number?]
; Next is number
[ltl/X-num  X number?]
; All numbers until an even number
[ltl/num-U-even  number? U even-number?]
; First is not number
[ltl/not-num  not number?]
; First is either negative or even
[ltl/neg-or-even  negative-number? or even-number?]
; First is both positive and even
[ltl/pos-and-even  positive-number? and even-number?]
; If first is number it must be even
[ltl/num=>even  number? => even-number?]
; If first is number it must be even, and if even must be number
[ltl/num<=>X-even  number? <=> (X even-number?)]
; All numbers until even number
[ltl/even-R-num  even-number? R number?]
; Eventually a number shows up
[ltl/F-num  F number?]
; All elements are numbers
[ltl/G-num  G number?]
; Either all numbers until negative, or third element is number
[ltl/compound  (number? U negative-number?) or (X (X number?))]
