#lang racket
(define (lhs term)
  (list-ref term 0))
(define (rhs term)
  (list-ref term 1))
(define (lambda-star var term)
  (match term
    [sym #:when (eqv? sym var)
           '((s k) k)]
    [(list lhs rhs) (quasiquote ((s (unquote (lambda-star var lhs))) (unquote (lambda-star var rhs))))]
    [sym (quasiquote (k (unquote sym)))]))
(define (prettify-lambda-star term)
  (match term
    [(list lhs rhs) (begin
                      (prettify-lambda-star lhs)
                      (display " ⨾ ")
                      (display "(")
                      (prettify-lambda-star rhs)
                      (display ")"))]
    [sym (display sym)]))