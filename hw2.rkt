#lang racket

(require rackunit)

;; Gradescope loads this file as a module and expects each required name
;; in the provide form below to exist. Replace each "not implemented"
;; expression with your solution, but keep the filename, names, and
;; argument lists unchanged.

(provide list-ref
         union
         extend
         walk-symbol
         lambda->lumbda
         reference-occurs?
         var-references
         unique-var-references
         free-reference-occurs?
         bound-reference-occurs?
         unique-free-references
         unique-bound-references
         lex)

#| Free, Bound, and Lexical Address |#

;; There may, indeed, be other applications of the system than its use
;; as a logic.

;; -- Alonzo Church

#| Assignment Guidelines |#

;; In addition to the standard Assignment Guidelines
;; (https://hemann.pl/26FA-CS3113/hw/)

;; You will likely find memv, remv, assv, and letrec useful.

;; A lambda-calculus expression is one of:
;;  - variables (implemented as symbols)
;;  - lambda expressions that take exactly one argument and have exactly one body
;;  - applications (lists of exactly two lambda calculus expressions)

;; In this assignment, you will use the functions you define in the
;; first section as helpers in the later problems.

;; An association list is a list of pairs of associated values. For
;; example, the following is an association list:
;; '((a . 5) (b . (1 2)) (c . a))

;; You must use match in each of the problems from section 2 of this
;; assignment, unless the assignment states otherwise.

;; Most of section 2's problems require both match and recursion on
;; lambda-calculus expressions.

;; You will want each of these problems to be structurally recursive.

;; You may find match also simplifies other problems.

;; The match features we demonstrated in class are sufficient. Do not
;; use features of match we did not discuss in class.

;; Yes, the same expression can contain both a free
;; reference to `x` and a bound reference to `x`.

;; In a subset of Racket where lambdas have only one argument, the
;; lexical address of a variable is the number of lambdas between the
;; place where the variable is declared (i.e. the formal parameter)
;; and the place where it is referenced. The o at the very bottom of
;; the following expression is a bound variable reference. It has a
;; lexical address of 4, because there are four lambda expressions
;; between the formal parameter o at the top and the reference to o at
;; the bottom.

#|
(lambda (o)
  (lambda (r)
    (lambda (s)
      (lambda (p)
        (lambda (g)
          o)))))
|#

#| Part I Natural Recursion Refresher |#

#|

1. Consider the following incomplete definition of the list-ref
function. It should behave like Racket's list-ref.

|#

;; list-ref: listof any natnum -> any
;; Purpose: Returns the nth element of ls.
(define (list-ref ls n)
  (letrec
      ([nth-cdr
        (λ (n)
          (cond
            [(zero? n) ls] ;; 0th cdr of ls = ls
            ;; recur on n - 1 to get the (n - 1)th cdr, then take the cdr of that result
            [else (cdr (nth-cdr (sub1 n)))]))])
    (car (nth-cdr n))))

(check-equal? (list-ref '(a b c d) 0) 'a)
(check-equal? (list-ref '(a b c d) 1) 'b)
(check-equal? (list-ref '(a b c d) 2) 'c)
(check-equal? (list-ref '(a b c d) 3) 'd)

;; (define (... e)
;;   (match e
;;     [`,y #:when (symbol? y) ...]
;;     [`(lambda (,x) ,body) (do something (... body))]
;;     [`(,rator ,rand) (do something (... rator) (... rand))]))
;;       

;; The inner, nested function nth-cdr needs its body. Complete the
;; list-ref's definition by completing a naturally-recursive
;; implementation of nth-cdr, so that it behaves like Racket's list-ref.
;; You must not modify the provided code beyond adding a body. You may of
;; course add newlines as needed. Do not call list-ref, either ours or
;; Racket's, in your definition. Follow our pattern: figure out the
;; base case, write the natural recursion, and figure out what to do
;; with the result of the recursion.

#|

2. Define and test a procedure union that takes two lists, where
neither list contains the same element twice (that is, the list
represents a set), and returns a list containing the union of the two
input lists. Again, the order of the elements in your answer does not
matter. You should use `memv` on this problem.

|#

;; union: set set -> set
;; Purpose: Takes two sets of elements and returns a set of their union.
(define (union s1 s2)
  (match s1
    [`() s2] ;; if s1 is empty, return s2
    ;; non-empty case
    ;; (union s1^ s2) builds the set union
    ;; (remv elem ...) takes out the elem if it exists in the union
    ;; (cons elem ...) puts elem back at the front
    [`(,elem . ,s1^) (cons elem (remv elem (union s1^ s2)))]))

#|

3. Define and test a procedure extend that takes two arguments, say x
and a predicate pred. (Recall from the previous assignment the
definition of a predicate.) extend should return a predicate. The
returned predicate should hold for exactly those things that are eqv?
to x or satisfy pred.

> ((extend 1 even?) 1)
#t

|#

;; extend: any any->boolean -> any->boolean
;; Purpose: Takes a value x and a predicate pred and returns a new predicate that holds if input is eqv? to x or satified pred.
(define (extend x pred)
  (lambda (y) ;; new pred that consumes a new y input
    ;; returns true if y is eqv? to x or if y satisfies pred
    (or (eqv? y x) (pred y))))

(check-equal? ((extend 1 even?) 1) #t)
(check-equal? ((extend 2 odd?) 5) #t)
(check-equal? ((extend 3 even?) 9) #f)
(check-equal? ((extend 'a number?) 17) #t)
(check-equal? ((extend 'a number?) 'b) #f)


#|

4. Define and test a procedure walk-symbol that takes a Racket datum x
and s, an association list of symbols to Racket data. Your procedure
should search through s for the value associated with x. If the
associated value is a symbol, it too must be walked in s. If x has no
association, then walk-symbol should return x. You should use `assv`
on this problem. Cycles are absolutely bad data.

> (walk-symbol 'd '((a . 5) (b . (1 2)) (c . a) (e . c) (d . e)))
5

|#

;; 

;; walk-symbol: any listof pair -> any
;; Purpose: Searches for a key x in list s, walking through each symbol until finding a non-symbol or unassociated val.
(define (walk-symbol x s)
  (letrec ([pair (assv x s)]) ;; lookup pair with key x in s using assv
    (match pair
      [#f x] ;; if key x is not in s, return x
      ;; if the val in pair is a sym, recur on the symbol in s
      [`(,key . ,val) #:when (symbol? val) (walk-symbol val s)]
      ;; if the value in pair is not sym, return it
      [`(,key . ,val) val])))

;; Case 1 (not in s)
(check-equal? (walk-symbol 'f '((a . 1) (b . (2 3)) (c . 4) (d . e))) 'f)
;; Case 2 (val is sym) -> pair (d . e) -> symbol? 'e -> 'e != key -> 'e
(check-equal? (walk-symbol 'd '((a . 1) (b . (2 3)) (c . 4) (d . e))) 'e)
;; Case 3 (val is not sym)
(check-equal? (walk-symbol 'a '((a . 1) (b . (2 3)) (c . 4) (d . e))) 1)


#| Part II Free, Bound, Lexical Address |#

#|

5. Define and test a procedure lambda->lumbda that takes a
lambda-calculus expression and returns the expression unchanged with
the exception that each lambda *as a binder* has been replaced with the
word lumbda (notice you should not change declarations of a variable
`lambda`).

|#

;; lambda->lumbda: lambda-expr -> lambda-expr
;; Purpose: Replaces lambda as a binder in a lambda calculus expression.
;; - Preserves the variable refs and declarations.
(define (lambda->lumbda expr)
  (match expr
    ;; if given simple var ref and it's a sym, return it
    [`,y #:when (symbol? y) y]
    ;; replace lambda with lumbda and recur on the rest
    [`(lambda (,x) ,body) `(lumbda (,x) ,(lambda->lumbda body))]
    ;; recur on both operator and operand
    [`(,rator ,rand) `(,(lambda->lumbda rator) ,(lambda->lumbda rand))]))

;; Case 1 (referring to a symbol 'lambda with no declaration)
(check-equal? (lambda->lumbda 'lambda) 'lambda)
;; Case 2 (lambda abstraction)
(check-equal? (lambda->lumbda '(lambda (x) x)) '(lumbda (x) x))
;; Case 2 (lambda abstraction during declaration)
(check-equal? (lambda->lumbda '(lambda (lambda) lambda)) '(lumbda (lambda) lambda))
;; Case 3 (list of lambda abstractions)
(check-equal? (lambda->lumbda '((lambda (x) x) (lambda (y) y))) '((lumbda (x) x) (lumbda (y) y)))


#|

6. Define and test a procedure reference-occurs? that takes a variable
name and a lambda-calculus expression and returns a boolean answering
whether the expression contains a reference to that variable.

|#

;; reference-occurs?: symbol lambda-expr -> boolean
;; Purpose: Determines whether a symbol x occurs as a variable reference anywhere in the lambda-expr expr.
(define (reference-occurs? x expr)
  (match expr
    ;; if y is a symbol, return true if y equals x
    [`,y #:when (symbol? y) (eqv? y x)]
    ;; if expr is a lambda-expr, recur on its body
    [`(lambda (,param) ,body) (reference-occurs? x body)]
    ;; if expr is a listof lambda-exprs, recur on rator and rand
    [`(,rator ,rand) (or (reference-occurs? x rator) (reference-occurs? x rand))]))

(check-equal? (reference-occurs? 'x 'x) #t)
(check-equal? (reference-occurs? 'x 'y) #f)
;; In declaration, but not referenced
(check-equal? (reference-occurs? 'x '(lambda (x) y)) #f)
;; Declared and references
(check-equal? (reference-occurs? 'x '(lambda (x) x)) #t)
;; Free reference to x
(check-equal? (reference-occurs? 'x '(lambda (y) x)) #t)
;; x occurs in the operand '((lambda (y) y) [x]))
(check-equal? (reference-occurs? 'x '((lambda (y) y) x)) #t)

#|

7. Define and test a procedure var-references that takes a lambda-calculus
expression and returns a list containing all the variable references
(the variable name itself) in the expression. This should be a
straightforward modification of lambda->lumbda, and the order of the
variables in your answer does not matter.

|#

;; var-references: lambda-expr -> listof symbol
;; Purpose: Forms a list of all variable references occuring in the lambda-expr expr.
(define (var-references expr)
  (match expr
    ;; if y is symbol?, return it as a list with a single element y
    [`,y #:when (symbol? y) (list y)]
    ;; if expr is a lambda-expr, recur on its body
    [`(lambda (,x) ,body) (var-references body)]
    ;; if expr is a listof lambda-expr, recur on rator and rand
    [`(,rator ,rand) (append (var-references rator) (var-references rand))]))

(check-equal? (var-references 'x) '(x))
(check-equal? (var-references '(lambda (x) (x y))) '(x y))
(check-equal? (var-references '((lambda (x) x) (lambda (y) y))) '(x y))

#|

8. Define and test a function called unique-var-references that
behaves like var-references but returns a set---i.e. it eliminates
duplicates as it evaluates. Use union in your definition.

|#

;; unique-var-references: lambda-expr -> listof symbol
;; Purpose: Forms a list of unique variable references occuring in the lambda-expr expr. 
(define (unique-var-references expr)
  (match expr
    ;; if y is symbol, return it as a list with a single element y
    [`,y #:when (symbol? y) (list y)]
    ;; if expr is a lambda-expr, recur on its body
    [`(lambda (,x) ,body) (unique-var-references body)]
    ;; if expr is a listof lambda-exprs, recur on rator and rand and combine with union operation
    [`(,rator ,rand) (union (unique-var-references rator) (unique-var-references rand))]))

(check-equal? (unique-var-references 'x) '(x))
(check-equal? (unique-var-references '(lambda (x) (x (x y)))) '(x y))
(check-equal? (unique-var-references '((lambda (x) (x y)) (lambda (z) (x y)))) '(x y))

#|

9. Define and test a procedure free-reference-occurs? that takes a
symbol and a lambda-calculus expression and returns #t if that that
expression contains a free reference to that variable, and #f
otherwise. You may have seen solutions in class to these problems that
use accumulators. You are not permitted to use accumulators on these
problems; such solutions do not receive credit.

|#

;; free-reference-occurs?: symbol lambda-expr -> boolean
;; Purpose: Check is symbol x is a free reference in lambda-expr expr.
(define (free-reference-occurs? x expr)
  (match expr
    ;; if y is symbol, check if y = x
    [`,y #:when (symbol? y) (eqv? y x)]
    ;; if expr is lambda-exprm return #f if param = x, else recur on body
    [`(lambda (,param) ,body) (if (eqv? param x) #f (free-reference-occurs? x body))]
    ;; if expr is a listof lambda-exprs, recur on rator and rand
    [`(,rator ,rand)
     (or (free-reference-occurs? x rator)
         (free-reference-occurs? x rand))]))

;; x is a free variable
(check-equal? (free-reference-occurs? 'x 'x) #t)
;; x is bound by lambda (x)
(check-equal? (free-reference-occurs? 'x '(lambda (x) x)) #f)
;; x is free inside lambda (y)
(check-equal? (free-reference-occurs? 'x '(lambda (y) x)) #t)
;; x is bound in rator, but free in rand
(check-equal? (free-reference-occurs? 'x '((lambda (x) x) x)) #t)

#|

10. Define and test a procedure bound-reference-occurs? that takes a
symbol and a lambda-calculus expression and returns #t if that
expression contains a bound reference to the variable, and #f
otherwise.

|#

;; bound-reference-occurs?: symbol lambda-expr -> boolean
;; Purpose: Checks if symbol x occurs as a bound reference in the lambda-expr expr.
(define (bound-reference-occurs? x expr)
  (match expr
    ;; if y is a symbol, a single symbol cannot be a bound reference
    [`,y #:when (symbol? y) #f]
    ;; if expr is a lambda-expr, check if parameter y equals x
    [`(lambda (,param) ,body)
     (if (eqv? param x)
         ;; if y equals x, check if x occurs as a reference anywhere in body
         (reference-occurs? x body)
         ;; if y does not equal x, recur on body for bound references
         (bound-reference-occurs? x body))]
    ;; if expr is a listof lambda-exprs, recur on rator and rand
    [`(,rator ,rand)
     (or (bound-reference-occurs? x rator)
         (bound-reference-occurs? x rand))]))

;; x is a free symbol
(check-equal? (bound-reference-occurs? 'x 'x) #f)
;; x is bound by lambda (x) and referenced in body
(check-equal? (bound-reference-occurs? 'x '(lambda (x) x)) #t)
;; x is declared but never referenced in body
(check-equal? (bound-reference-occurs? 'x '(lambda (x) y)) #f)
;; 'x is bound in rator but free in rand
(check-equal? (bound-reference-occurs? 'x '((lambda (x) x) x)) #t)


#|

11. Define and test a procedure unique-free-references that takes a
lambda-calculus expression and returns a set (represented as a list)
of all the free variable references in that expression. Order doesn't
matter, but the list must not contain duplicate variables. You may
find it helpful to use the definition of unique-var-references as a
starting point.

|#

;; unique-free-references: lambda-expr -> listof symbol
;; Purpose: Forms a set of all unique free variable references occurring in the lambda-expr expr.
(define (unique-free-references expr)
  (match expr
    ;; if y is a symbol, return it as a list with a single element y
    [`,y #:when (symbol? y) (list y)]
    ;; if expr is a lambda-expr, recur on body and remove parameter x from the result
    [`(lambda (,x) ,body) (remv x (unique-free-references body))]
    ;; if expr is a listof lambda-exprs, recur on rator and rand and combine with union
    [`(,rator ,rand)
     (union (unique-free-references rator) (unique-free-references rand))]))

;; x is a symbol 'x
(check-equal? (unique-free-references 'x) '(x))
;; x is bound by lambda (x)
(check-equal? (unique-free-references '(lambda (x) x) ) '())
;; x is bound by lambda (x), but y is free
(check-equal? (unique-free-references '(lambda (x) (x y))) '(y))
;; x is bound in rator, but free in rand
(check-equal? (unique-free-references '((lambda (x) x) x)) '(x))

;; Note that for instance

;; '((lambda (x) ((x y) e)) (lambda (c) (x (lambda (x) (x (e c))))))

;; is a single lambda-calculus expression (a procedure application),
;; not a list of lambda-calculus expressions.

#|

12. Define and test a procedure unique-bound-references that takes a
lambda-calculus expression and returns a set (represented as a list)
of all the bound variable references in the input expression. Order
doesn't matter, but the list must not contain duplicate variables.

|#

;; unique-bound-references: lambda-expr -> listof symbol
;; Purpose: Forms a list of unique bound variable references occurring in the lambda-expr expr.
(define (unique-bound-references expr)
  (match expr
    ;; if y is a symbol, return empty list
    [`,y #:when (symbol? y) '()]
    ;; if expr is a lambda-expr, check if x occurs free in body
    [`(lambda (,x) ,body)
     (if (free-reference-occurs? x body)
         (union (list x) (unique-bound-references body))
         (unique-bound-references body))]
    ;; if expr is a listof lambda-exprs, recur on rator and rand and combine with union operation
    [`(,rator ,rand)
     (union (unique-bound-references rator) (unique-bound-references rand))]))

;; x is a symbol
(check-equal? (unique-bound-references 'x) '())

;; x is bound by lambda (x) and referenced in body 
(check-equal? (unique-bound-references '(lambda (x) x)) '(x))

;; x is declared but never referenced in body 
(check-equal? (unique-bound-references '(lambda (x) y)) '())

;; x is free inside lambda (y)
(check-equal? (unique-bound-references '(lambda (y) x)) '())

;; 'x is bound in rator but free in rand
(check-equal? (unique-bound-references '((lambda (x) x) x)) '(x))


#|

13. Define and test a procedure lex that takes a lambda-calculus
expression and an accumulator (which starts as the empty list), and
returns the same expression with all bound variable references
replaced by lists of two elements whose car is the symbol var and
whose cadr is the lexical address of the referenced variable. For this
problem expressions with free variable references are bad data.

This problem has several good solutions. I suggest you start by
building some lambda expressions on paper and then, by hand, find the
lexical addresses of some variable references that occur in them. Try
and do it almost mechanically, starting from the top of the expression
and working your way down. Then think about what it is you're doing,
and try and figure out how to do it without having to go back up the
tree. That is, ensure that when you get to a variable position in the
expression where you need to fill in the lexical address, that you
already have all the information you need to figure it out. Then code
that.

> (lex '(lambda (y) (lambda (x) (x y))) '())
'(lambda (lambda ((var 0) (var 1))))


If you find the list-index-ofv function from your hw1
will help you, copy it over to this file.

|#

;; Copied from hw1
;; list-index-ofv: any listof any -> natnum
;; Purpose: Finds the index of x in ls.
(define (list-index-ofv x ls)
  (cond
    [(eqv? (car ls) x) 0] ;; if x is first, return 0 (first index)
    ;; add1 to move past first element, recur on the rest of ls to find x
    [else (add1 (list-index-ofv x (cdr ls)))]))

(check-equal? (list-index-ofv 'a '(a b c d)) 0)
(check-equal? (list-index-ofv 'c '(a b b b b d c )) 6)
(check-equal? (list-index-ofv 42 '(10 20 30 42 50)) 3)
(check-equal? (list-index-ofv 'x '(a b x c x d)) 2)


;; lex: lambda-expr listof symbol -> lexical-expr
;; Purpose: Replaces bound variable references in expr with lexical addresses using acc.
(define (lex expr acc)
  (match expr
    ;; if y is a symbol, look up its index in acc and return (var index)
    [`,y #:when (symbol? y) `(var ,(list-index-ofv y acc))]
    ;; if expr is a lambda-expr, recur on body with x added to front of acc
    [`(lambda (,x) ,body) `(lambda ,(lex body (cons x acc)))]
    ;; if expr is a listof lambda-exprs, recur on rator and rand
    [`(,rator ,rand) `(,(lex rator acc) ,(lex rand acc))]))

;; identity lambda
(check-equal? (lex '(lambda (x) x) '()) '(lambda (var 0)))

;; nested lambdas
(check-equal? (lex '(lambda (y) (lambda (x) (x y))) '()) '(lambda (lambda ((var 0) (var 1)))))

;; multiple var refs
(check-equal? (lex '(lambda (a) (lambda (b) (lambda (c) ((a c) (b c))))) '())'(lambda (lambda (lambda (((var 2) (var 0)) ((var 1) (var 0)))))))