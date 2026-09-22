#lang racket
(require rackunit)

;; Gradescope loads this file as a module. Replace each "not implemented"
;; expression with your solution, but keep the filename, required names,
;; and any given argument lists unchanged.

(provide (all-defined-out))

#| Assignment 3: Environments and Interpreters |#

;; Inverting the adage that a data type is just a simple programming
;; language, we take the position that a programming language is,
;; semantically, just a complex data type; evaluation of a program is
;; just another operation in the data type.
;;
;; -- Mitch Wand

#| ===== Assignment Guidelines ===== |#

;; In addition to the standard Assignment Guidelines
;; (https://hemann.pl/26FA-CS3113/hw/), follow the
;; assignment-specific artifact and review requirements below.
;;
;; Recall that in recent lectures, we've learned how to write an
;; interpreter that takes a Racket expression and returns the
;; expression's value. We have also learned to make this interpreter
;; representation independent with respect to environments, and we
;; have written two different representations of the helpers
;; extend-env, apply-env, and empty-env.
;;
;; In the first part of this assignment you will implement the three
;; interpreters I presented in lecture.

;; For the 2nd and 3rd interpreters you must also define two sets of
;; environment helpers: one that uses functional (higher-order)
;; representation of environments, and one that uses data-structural
;; representation of environments.

;; Your data structure representations should be the tagged list
;; representation demonstrated in class.

;; You must name your interpreters and helpers for each of the first
;; three problems respectively by the following naming
;; conventions. These below names may differ sligtly from the names I
;; used in lecture.
;;
;; Your first three interpreters must all handle the following forms:
;; numbers, booleans, variables, lambda-abstraction, application,
;; zero?, sub1, *, +, if, and let.
;; Addition accepts any number of arguments, as in Racket.

;; In the second part you will implement a fourth interpreter, this
;; time an interpreter for a new language.

;; For this assignment your solutions must be compositional or you
;; will lose credit.  E.g. although we could rewrite the expression
;; (let ([x e]) body) as ((lambda (x) body) e), you must not use
;; lambda in this way for your interpreter's line for let
;; expressions. Instead, you must implement let in its own right.

#| ===== Individual code review ===== |#

;; Assignment 3 has two separately graded items: the submitted artifact
;; and an individual code review lasting about ten minutes. The shared
;; pass, understanding, quality, penalty-unit, and course-pass policy is
;; in the syllabus:
;; https://hemann.pl/26FA-CS3113/syllabus/#assignment-3-and-assignment-9-code-reviews
;;
;; Book a review appointment through the CSAS 3113 code-review booking
;; page: https://hemann.pl/book/csas-3113-code-review/
;;
;; The booking page is the current source for available appointment
;; dates and times.
;;
;; You must pass the Assignment 3 code review no later than Friday,
;; October 9, 2026, at 5:00 p.m. Eastern. Approved accommodations or
;; documented exceptional circumstances may receive the adjusted
;; deadline described in the syllabus.
;;
;; Be prepared to trace and explain your code on the whiteboard from
;; memory. Do not bring or consult a copy of your code.
;;
;; Be prepared to discuss the evaluation rules in your interpreters,
;; compositional treatment of let, functional and data-structural
;; environment representations, the environment interface and
;; representation independence
;;
;; Assignment 3 maps the syllabus's passing quality ratings to points as
;; follows:
;;
;;   Convincing:   4/4
;;   Solid:        3/4
;;   Minimum pass: 2/4
;;
;; Its accumulated penalty units cap a successful review as follows:
;;
;;   Penalty units   Maximum score
;;   0               4/4
;;   1               3/4
;;   2 or more       2/4
;;
;; The recorded score is the lower of the holistic quality score and
;; this cap. The cap floor does not itself establish a pass.

#| ===== Interpreters and environments ===== |#

#|

1. Define value-of, an interpreter whose environment is represented
directly as a Racket function from variable names to values. The
environment argument supplied to value-of is already such a function.

|#

;; value-of: expr env -> val
;; Purpose: Evaluates an expression expr under an environment env and returns its value val.
(define (value-of expr env)
  (match expr
    ;; symbol? variable reference, ask env for its value
    [`,y #:when (symbol? y) (env y)]
    ;; a number is its own value
    [`,y #:when (number? y) y]
    ;; a boolean is its own value
    [`,y #:when (boolean? y) y]
    ;; evaluate e to value, then ask if e = 0
    [`(zero? ,e) (zero? (value-of e env))]
    ;; evaluate e to value, then subtract 1 from it
    [`(sub1 ,e) (sub1 (value-of e env))]
    ;; evaluate e1 and e2 to values, then mult them
    [`(* ,e1 ,e2) (* (value-of e1 env) (value-of e2 env))]
    ;; varies; take the whole arg list, evaluate each to a value then sum them
    [`(+ . ,exprs) (sum-list (evlist exprs env))]
    ;; evaluate test, then only evaluate the taken branch
    [`(if ,test ,conse ,alt) (if (value-of test env)
                                (value-of conse env)
                                (value-of alt env))]
    ;; doesn't evaluate body; return a procedure that extends env with x bound to a once applied
    [`(lambda (,(? symbol? x)) ,body)
     (lambda (a)
       (value-of body (lambda (y) (if (eqv? x y) a (env y)))))]
    ;; evaluate e in original env, body evaluated with x extended
    [`(let ([,(? symbol? x) ,e]) ,body)
     (let ([val (value-of e env)])
       (value-of body (lambda (y) (if (eqv? x y) val (env y)))))]
    ;; application
    [`(,rator ,rand) ((value-of rator env) (value-of rand env))]))


;; evlist: listof expr env -> listof val 
;; Purpose: Evaluates each expr in exprs under env, returns the values.
(define (evlist exprs env)
  (match exprs
    ['() '()]
    [`(,first . ,rest) (cons (value-of first env) (evlist rest env))]))

;; sum-list: listof number -> number
;; Purpose: Adds up all the numbers in ls.
(define (sum-list ls)
  (match ls
    ['() 0]
    [`(,first . ,rest) (+ first (sum-list rest))]))

(test-equal?
 "A nearly-sufficient test-case of your program's functionality"
 (value-of
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n)))))))
    5)
  (lambda (y) (value-of y)))
 120)

(test-equal?
 "A nearly-sufficient test-case of your program's functionality with addition"
 (value-of
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n)))))))
    5)
  (lambda (y) (value-of y)))
 16)


#|

2. Define value-of-fn. We walked through the steps of implementing
this in lecture, at least for the basic forms. From a software
engineering point-of-view, you can see this process as follows. In the
above, we hard-coded our implementation of "environment", tightly
coupling the client code (value-of) to the implementation of
environments. Now, we will correct that mistake by engineering an
interface: `apply-env-fn`, `extend-env-fn`, and `empty-env-fn`
collectively make up the interface for environments. By replacing
those hard-coded implementations of environments with calls to these
"help functions" we will construct an interface against which we can
program, correctly separating the client code that uses environment
from the implementation that provides environment across the
interface. This interpreter must use only empty-env-fn, extend-env-fn,
and apply-env-fn to create, extend, and inspect environments.
Implement those three operations with a functional, higher-order
representation of environments.

These helpers collectively form the environment interface. The
interpreter is so to say the client of that interface and must not
depend on the representation behind it.

|#

;; empty-env-fn: -> env
;; Purpose: An environment with no bindings; any lookup errors.
(define (empty-env-fn)
  (lambda (name)
    (error 'apply-env-fn "unbound variable: ~a" name)))

;; extend-env-fn: sym val env -> env
;; Purpose: An environment with x additionally bound to a, shadowing any old x.
(define (extend-env-fn x a env)
  (lambda (query)
    (if (eqv? query x)
        a
        (apply-env-fn env query))))

;; apply-env-fn: env sym -> val
;; Purpose: Lookup y's value in env.
(define (apply-env-fn env y)
  (env y))

;; value-of-fn: expr env -> val
;; Purpose: same as value-of
(define (value-of-fn expr env)
  (match expr
    [`,y #:when (symbol? y) (apply-env-fn env y)]
    [`,y #:when (number? y) y]
    [`,y #:when (boolean? y) y]
    [`(zero? ,e) (zero? (value-of-fn e env))]
    [`(sub1 ,e) (sub1 (value-of-fn e env))]
    [`(* ,e1 ,e2) (* (value-of-fn e1 env) (value-of-fn e2 env))]
    [`(+ . ,exprs) (sum-list (evlist-fn exprs env))]
    [`(if ,test ,conse ,alt)
     (if (value-of-fn test env) (value-of-fn conse env) (value-of-fn alt env))]
    [`(lambda (,x) ,body) #:when (symbol? x)
        (lambda (a) (value-of-fn body (extend-env-fn x a env)))]
    [`(let ([,x ,e]) ,body) #:when (symbol? x)
                            (value-of-fn body (extend-env-fn x (value-of-fn e env) env))]
    [`(,rator ,rand) ((value-of-fn rator env) (value-of-fn rand env))]))


;; Same as evlist, just with fn
(define (evlist-fn exprs env)
  (match exprs
    ['() '()]
    [`(,first . ,rest) (cons (value-of-fn first env) (evlist-fn rest env))]))

(test-equal?
 "A nearly-sufficient test-case of your program's functionality"
 (value-of-fn
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n)))))))
    5)
  (empty-env-fn))
 120)

(test-equal?
 "A nearly-sufficient test-case of your program's functionality with addition"
 (value-of-fn
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n)))))))
    5)
  (empty-env-fn))
 16)


#|

3. Define value-of-ds. We walked through the steps of implementing
this in lecture, at least for the basic forms. We can also see this
step from a software engineering point-of-view as follows. In the
above, we shimmed in an interface to separate our client code that
uses environment and our implementation code that provides
environment, across an interface that is the three functions
`apply-env-fn`, `extend-env-fn`, and `empty-env-fn`. In this step, we
will now demonstrate to ourselves that this was a well-defined
interface, that is, that our interface is not "leaky." We will
re-implement environment, using an entirely different representation
behind-the-scenes. Since our client (the interpreter) is programming
against the interface, though, the client code won't have to change at
all*.

With this switch to a representation of environments as data
structures, we notice another neat thing. We changed our environment
went from a higher-order, functional representation in the last part
of the assignment to now, a first-order data structure
representation. And we can match against our environment like you
would any old data definition.


* Okay, so we're in point of fact changing both the interpreter client
code and the "helper" interface functions from -fn to -ds, but this is
just so that you can have the different versions of this interpreter in
the same file for us to test.

|#

;; Env ::= (empty-environment) | (environment-extension symbol value Env)
(struct empty-environment () #:transparent)
(struct environment-extension (name value rest) #:transparent)

;; empty-env-ds: -> env
;; Purpose: An environment with no bindings as data.
(define (empty-env-ds)
  (empty-environment))

;; extend-env-ds: symbol value env -> env
;; Purpose: Wraps env in a new environment-extension tag holding x and a.
(define (extend-env-ds x a env)
  (environment-extension x a env))

;; apply-env-ds: env symbol -> val
;; Purpose: Pattern-matches on env's tag to search for y's binding.
(define (apply-env-ds env y)
  (match env
    ;; no bindings, y never declared
    [(empty-environment) (error 'apply-env-ds "unbound variable: ~a" y)]
    ;; check the newest binding first, else recur into the rest
    [(environment-extension name value rest)
     (if (eqv? y name) value (apply-env-ds rest y))]))

;; Same as value-of and value-of-fn
(define (value-of-ds expr env)
  (match expr
    [`,y #:when (symbol? y) (apply-env-ds env y)]
    [`,y #:when (number? y) y]
    [`,y #:when (boolean? y) y]
    [`(zero? ,e) (zero? (value-of-ds e env))]
    [`(sub1 ,e) (sub1 (value-of-ds e env))]
    [`(* ,e1 ,e2) (* (value-of-ds e1 env) (value-of-ds e2 env))]
    [`(+ . ,exprs) (sum-list (evlist-ds exprs env))]
    [`(if ,test ,cons ,alt)
     (if (value-of-ds test env) (value-of-ds cons env) (value-of-ds alt env))]
    [`(lambda (,x) ,body) #:when (symbol? x)
     (lambda (a)
       (value-of-ds body (extend-env-ds x a env)))]
    [`(let ([,x ,e]) ,body) #:when (symbol? x)
     (value-of-ds body (extend-env-ds x (value-of-ds e env) env))]
    [`(,rator ,rand) ((value-of-ds rator env) (value-of-ds rand env))]))

;; Same as evlist
(define (evlist-ds exprs env)
  (match exprs
    ['() '()]
    [`(,first . ,rest) (cons (value-of-ds first env) (evlist-ds rest env))]))

(test-equal?
 "A nearly-sufficient test-case of your program's functionality"
 (value-of-ds
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (* n ((f f) (sub1 n)))))))
    5)
  (empty-env-ds))
 120)

(test-equal?
 "A nearly-sufficient test-case of your program's functionality with addition"
 (value-of-ds
  '(((lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n))))))
     (lambda (f)
       (lambda (n) (if (zero? n) 1 (+ n ((f f) (sub1 n)))))))
    5)
  (empty-env-ds))
 16)


#| ===== A new syntax ===== |#

#|

4. Implement an interpreter fo-eulav. Let the below examples guide
you. I only require you to implement those forms I use in those
examples.

|#

;; deep-reverse: datum -> datum
;; Purpose: Reverses each symbol's spelling and each ls element order recursively.
(define (deep-reverse expr)
  (cond
    ;; number?, return that number
    [(number? expr) expr]
    ;; boolean?, return that boolean
    [(boolean? expr) expr]
    ;; symbol -> string -> reversed chars -> reversed-string -> reversed-symbol (in to out)
    [(symbol? expr)
     (string->symbol (list->string (reverse (string->list (symbol->string expr)))))]
    [(list? expr) (reverse (map deep-reverse expr))]
    [else (error 'deep-reverse "not a fo-eulax expression: ~a" expr)]))
     
;; fo-eulav: reversed-expr env -> value
;; Purpose: Undoes the reversal, then passes to value-of.
(define (fo-eulav expr env)
  (value-of (deep-reverse expr) env))

(test-equal?
 "Ppa"
 (fo-eulav '(5 (x (x) adbmal)) (lambda (y) (error 'fo-eulav "unbound variable ~s" y)))
 5)
(test-equal?
 "Stnemugra sa Snoitcnuf"
 (fo-eulav '(((x 1bus) (x) adbmal) ((5 f) (f) adbmal)) (lambda (y) (error 'fo-eulav "unbound variable ~s" y)))
 4)
(test-equal?
 "Tcaf"
 (fo-eulav
  '(5
    (((((((n 1bus) (f f)) n *) 1 (n ?orez) fi)
       (n) adbmal)
      (f) adbmal)
     ((((((n 1bus) (f f)) n *) 1 (n ?orez) fi)
       (n) adbmal)
      (f) adbmal)))
  (lambda (y) (error 'fo-eulav "unbound variable ~s" y)))
 120)

(test-equal?
 "Mus"
 (fo-eulav
  '(5
    (((((((n 1bus) (f f)) n +) 1 (n ?orez) fi)
       (n) adbmal)
      (f) adbmal)
     ((((((n 1bus) (f f)) n +) 1 (n ?orez) fi)
       (n) adbmal)
      (f) adbmal)))
  (lambda (y) (error 'fo-eulav "unbound variable ~s" y)))
 16)

#| ===== Lexical addresses ===== |#

;; Consider the following interpreter for a deBruijnized version of
;; the lambda-calculus (i.e. lambda-calculus expressions using lexical
;; addresses addresses instead of variables). Notice this interpreter
;; is representation-independent with respect to environments. There
;; are a few other slight variations in the syntax of the
;; language. These are of no particular consequence.

(define (value-of-lex expr env)
  (match expr
    [`(const ,expr) expr]
    [`(mult ,x1 ,x2) (* (value-of-lex x1 env) (value-of-lex x2 env))]
    [`(plus ,x1 ,x2) (+ (value-of-lex x1 env) (value-of-lex x2 env))]
    [`(zero ,x) (zero? (value-of-lex x env))]
    [`(sub1 ,body) (sub1 (value-of-lex body env))]
    [`(if ,t ,c ,a) (if (value-of-lex t env) (value-of-lex c env) (value-of-lex a env))]
    [`(var ,num) (apply-env-lex env num)]
    [`(lambda ,body) (lambda (a) (value-of-lex body (extend-env-lex a env)))]
    [`(,rator ,rand) ((value-of-lex rator env) (value-of-lex rand env))]))

(define (empty-env-lex)
  '())

#|

5. Without using lambda or the implicit lambda in an "MIT-define",
define apply-env-lex and extend-env-lex. A correct solution is very
short.

|#

;; extend-env-lex: val nameless-env -> nameless-env
;; Purpose: Cons a onto env.
(define extend-env-lex cons) ;; no name to check, so is cons itself

;; apply-env-lex: nameless-env natnum -> val
;; Purpose: Look up the value at address num.
(define apply-env-lex list-ref)

(test-equal?
 "This test shows we're using a data-structure representation of environments."
 (value-of-lex '((lambda (var 0)) (const 5)) (empty-env-lex))
 5)

#| Just Dessert |#

#|

6. Go back and extend your interpreter value-of to support set! and
begin2, where begin2 is a variant of Racket's begin that takes exactly
two arguments, and set! mutates variables.

|#

;; value-of-set: expr env -> value
;; Purpose: Same as value-of, plus using set! and begin2.
;; env maps names to boxes
(define (value-of-set expr env)
  (match expr
    ;; env hands back
    [`,y #:when (symbol? y) (unbox (env y))]
    ;; a number is a val itself, return it
    [`,y #:when (number? y) y]
    ;; a boolean is a val itself, return it
    [`,y #:when (boolean? y) y]
    ;; evaluate e, then check whether the resulting number is 0
    [`(zero? ,e) (zero? (value-of-set e env))]
    ;; evaluate e, then subtract 1 from the resulting number
    [`(sub1 ,e) (sub1 (value-of-set e env))]
    ;; evaluate e1 and e2, then multiply the two resulting numbers
    [`(* ,e1 ,e2) (* (value-of-set e1 env) (value-of-set e2 env))]
    ;; varies; evaluate the ls of expr, then sum the ls' values
    [`(+ . ,exprs) (sum-list (evlist exprs env))]
    ;; evaluate test, run exactly one branch of conse or alt based off result
    [`(if ,test ,conse ,alt)
     (if (value-of-set test env) (value-of-set conse env) (value-of-set alt env))]
    ;; box is built once per call, not lookup
    [`(lambda (,x) ,body) #:when (symbol? x)
     (lambda (a)
       (define x-box (box a))
       (value-of-set body (lambda (y) (if (eqv? x y) x-box (env y)))))]
    [`(let ([,x ,e]) ,body) #:when (symbol? x)
     (define x-box (box (value-of-set e env)))
     (value-of-set body (lambda (y) (if (eqv? x y) x-box (env y))))]
    ;; mutated the shared box in place
    [`(set! ,x ,e)
     (set-box! (env x) (value-of-set e env))]
    ;; e1 for effect only; e2's value is returned
    [`(begin2 ,e1 ,e2)
     (value-of-set e1 env)
     (value-of-set e2 env)]
    ;; application
    [`(,rator ,rand) ((value-of-set rator env) (value-of-set rand env))]))

(test-equal?
 "set! actually mutates a captured variable"
 (value-of-set
  '(let ([x 5])
     (begin2 (set! x 10) x))
  (lambda (y) (error 'value-of "unbound variable ~a" y)))
 10)

;; 7.
;; The lambda calculus can be used to define a representation of
;; natural numbers, called Church numerals, and arithmetic over
;; them. For instance, c5 is the definition of the Church numeral for
;; 5. This is often described as "representing a number by its
;; fold". What they mean by this is: think of any given number not a
;; piece of data, but in terms of "the interface it implements." What
;; does a number *do* for you? It tells you how many times to iterate
;; some behavior.



(define c0 (lambda (s) (lambda (z) z)))
(define c5 (lambda (s) (lambda (z) (s (s (s (s (s z))))))))

(test-equal?
 "Church 5 acts like 5"
 ((c5 add1) 0)
 5)

(test-equal?
 "Church 0 acts like 0"
 ((c0 add1) 0)
 0)

;; The following is a definition for Church plus, which performs
;; addition over Church numerals.

(define c+
  (lambda (m)
    (lambda (n)
      (lambda (s)
        (lambda (z)
          ((m s) ((n s) z)))))))


(define c10 ((c+ c5) c5))

(test-equal?
 "Church addition acts like addition on Church numerals"
 ((c10 add1) 0)
 10)

;; One way to understand the definition of c+ is that it, when
;; provided two Church numerals, returns a function that, when
;; provided a meaning for add1 and a meaning for zero, uses provides
;; to m the meaning for add1 and, instead of the meaning for zero,
;; provides it the meaning for its second argument. m is the sort of
;; thing that will count up m times, so the resulting function is the
;; meaning of m + n.

#|

7. Your task, however, is to implement csub1, Church predecessor. You
should also provide tests. The Church predecessor of Church zero is
zero, as we haven't a notion of negative numbers. This was a difficult
problem, but it's fun, so don't Google it. If you think it might help
though, consider taking a [trip to the
dentist](http://link.springer.com/chapter/10.1007%2FBFb0062850).

|#

;; Fold pairs (prev, cur) forward: (0,0) (0,1) (1,2) ... (n-1, n).
;; first of the n-times-folded pair is n - 1.
 
;; cons-pair: value -> value -> pair
;; Purpose: Church-encodes a pair of a and b.
(define cons-pair (lambda (a)
                    (lambda (b)
                      (lambda (f) ((f a) b)))))

;; Purpose: Gets the first component of a Church pair.
(define first (lambda (p) (p (lambda (a) (lambda (b) a)))))

;; Purpose: Gets the second component of a Church pair.
(define second (lambda (p) (p (lambda (a) (lambda (b) b)))))

;; Purpose: One more fold than n.
(define csucc (lambda (n) (lambda (s) (lambda (z) (s ((n s) z))))))

;; Purpose: (prev, cur) -> (cur, cur + 1)
(define shift
  (lambda (p)
    ((cons-pair (second p)) (csucc (second p)))))

;; Fold shifts n times from (x0, x0); return first component.
(define csub1
  (lambda (n)
    (first ((n shift) ((cons-pair c0) c0)))))

(test-equal?
 "Church predecessor of 5 acts like 4"
 (((csub1 c5) add1) 0)
 4)

(test-equal?
 "Church predecessor of 0 acts like 0"
 (((csub1 c0) add1) 0)
 0)

(test-equal?
 "Church predecessor of 10 acts like 9"
 (((csub1 c10) add1) 0)
 9)