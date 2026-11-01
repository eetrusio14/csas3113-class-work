#lang racket

(require rackunit)

;; Gradescope loads this file as a module and expects each required name
;; in the provide form below to exist. Replace each "not implemented"
;; expression with your solution, but keep the filename, names, and
;; argument lists unchanged.

(provide lex
         value-of-cps
         empty-env
         extend-env
         empty-k)

#| Assignment 7: Continuations and Representation Independence |#

;; So, you're telling us that the universe is written in
;; continuation-passing style?

;; -- Phil Wadler, sometime during ICFP 2004

#| Assignment Guidelines |#

;; In addition to the standard Assignment Guidelines

;; Make sure and save every step of the way in part II of this
;; assignment.

#| ==== Part I: lex ==== |#

#|

1. Just when you thought you'd seen the last of it---lex is back. If
   you've got the previous version working, then all we're asking for is
   a handful of changes. Don't CPS this function.

  - Start by copying and pasting in your most recent implementation.
  - Replace your application line with the following [`(,rator ,rand) `(app ,(lex rator acc) ,(lex rand acc))]
  - Replace your zero? line with the following [`(zero? ,nexp) `(zero ,(lex nexp acc))]
  - Replace your * line with the following [`(* ,nexp1 ,nexp2) `(mult ,(lex nexp1 acc) ,(lex nexp2 acc))]
  - Add lines to lex that implement let/cc and throw. Of these, let/cc is the more interesting one.

These first three changes aren't required to correctly perform lexical addressing, but will make your lex useful in part II.

|#

;; list-index-ofv: any listof any -> natnum
;; Purpose: Returns the index of the first occurrence of x in ls; errors if x is absent.
(define (list-index-ofv x ls)
  (cond
    [(null? ls) (error 'list-index-ofv "~a not found" x)]
    [(eqv? (car ls) x) 0]
    [else (add1 (list-index-ofv x (cdr ls)))]))

(check-equal? (list-index-ofv 'a '(b a b a b)) 1)
(check-equal? (list-index-ofv 'c '(a b c d)) 2)

;; My original lex interpreter with the changes above
(define (lex expr acc)
  (match expr
    [`,n #:when (number? n) `(const ,n)]
    [`,y #:when (symbol? y) `(var ,(list-index-ofv y acc))]
    [`(zero? ,e) `(zero ,(lex e acc))]                 
    [`(sub1 ,e) `(sub1 ,(lex e acc))]
    [`(* ,e1 ,e2) `(mult ,(lex e1 acc) ,(lex e2 acc))]   
    [`(if ,t ,c ,a) `(if ,(lex t acc) ,(lex c acc) ,(lex a acc))]
    [`(let/cc ,k ,body) `(letcc ,(lex body (cons k acc)))]
    [`(throw ,k-exp ,v-exp) `(throw ,(lex k-exp acc) ,(lex v-exp acc))] 
    [`(lambda (,x) ,body) `(lambda ,(lex body (cons x acc)))]
    [`(let ([,x ,e]) ,body) `(let ,(lex e acc) ,(lex body (cons x acc)))]
    [`(,rator ,rand) `(app ,(lex rator acc) ,(lex rand acc))]))

;; a variable becomes its position in acc; * becomes mult
;; (* x 3), acc = (x): x is first -> (var 0); 3 -> (const 3)
(check-equal? (lex '(* x 3) '(x)) '(mult (var 0) (const 3)))

;; lambda pushes its parameter onto acc, so outer names get one number deeper
;; acc: () -> (x) -> (y x); the body x is at index 1
(check-equal? (lex '(lambda (x) (lambda (y) x)) '()) '(lambda (lambda (var 1))))

;; let: the bound expression is lexed with the old acc, the body with y added
;; e = x in (x) -> (var 0); body y in (y x) -> (var 0)
(check-equal? (lex '(let ([y x]) y) '(x)) '(let (var 0) (var 0)))

;; let/cc pushes k onto acc like a lambda parameter; throw just lexes both parts
;; acc becomes (k); k -> (var 0); 5 -> (const 5)
(check-equal? (lex '(let/cc k (throw k 5)) '()) '(letcc (throw (var 0) (const 5))))

#| ==== Part II: The interpreter === |#

;; This part of the assignment will be completed in several
;; stages. You should do each of these steps in a separate file. Turn
;; in only the file containing the last step, and call it hw7.rkt. But it is
;; **imperative** that you keep each of the previous steps. I will
;; ask to see them, and you should be able to walk me through by hand
;; how you got from each saved version to the next. Again, it is
;; **imperative** that you keep previous steps. You should have at
;; least these concrete milestones.
;;
;; You will use your corrected final hw7 interpreter as the starting
;; point for Assignment 9 (to be released later):
;; https://github.com/jasonhemann/26FA-CS3113/tree/master/_starter_code/hw9

;; You should begin with the interpreter below. This is an interpreter
;; for a lexed language, like the interpreter of problem 5 on
;; Assignment 3.

#|

You should take value-of as well as the definitions of
empty-env and empty-k, which will prove useful as you begin
your transformations. When you write your own test programs, you will
probably prefer not to write them directly in the language of this
interpreter. You can write test programs in Racket, use your lex
to transform them to the language of our interpreter, and evaluate the
results with value-of-cps. Use empty-env and empty-k when testing.

===Steps for Part II===

  1 CPS this interpreter. Call it value-of-cps. Use the "let trick" to
    eliminate the let binding when you CPS the let line. You might
    consider always using k^ as the additional continuation variable to
    your extended environments. Do not apply k^ to the call to error in
    empty-env. This is similar to the behavior of times-cps-shortcut from
    Assignment 6. Racket's let/cc **may not** be used in your CPSed
    interpreter. You might consider commenting out some of your match
    clauses, and CPSing the interpreter a few lines at a time. But try to
    finish this step entirely before you move on to the next one. Since
    your closures and environments are both implemented as functions, you
    should consider renaming them to env-cps and c-cps, respectively.

  2 Define apply-env, apply-closure, and apply-k, and add all the
    calls to those functions. Notice that after CPSing, your apply-closure
    and apply-env now take three arguments.
  
  3 Define extend-env and replace all 3 of your explicitly
    higher-order representations of environments with calls to extend-env.

  4 Add a ^ to each of the formal parameters of extend-env (not the
    inner function, mind you). Ensure that the inner functions in both
    extend-env and empty-env use the same formal parameters as the second
    argument to apply-env (here, typically y and k^).

  5 Replace your higher-order function representation of environments
    with a tagged-list data structure representation. Consider first
    ensuring that the last two formal parameters to apply-env (y and k)
    are the same as the formal parameters to the inner functions in
    extend-env and empty-env. Remember, if you add (else (env-cps y k)) as
    the last line of your match expression, you can test each
    transformation one at a time.

  6 If you used it, remove the (else (env-cps y k)) as the last line
    of your match expression in apply-env.

  7 Define make-closure and replace your explicitly higher-order
    representation of a closure with a call to make-closure.

  8 Replace your higher-order function representation of closures with
    a tagged-list data structure representation. Consider first ensuring
    that the last two formal parameters to apply-closure (a and k) are the
    same as the formal parameters to the inner function in make-closure.

  9 Define constructors for your continuations, and replace your
    explicitly higher-order function continuations with calls to these
    constructors. For nested continuations, you should consider working
    from the inside out. Remember, if you transform your constructors one
    at a time, you can test your program after each replacement.

 10 Add a ^ to each of the formal parameters of your continuation
    helpers, and change the body to match (that is, do an alpha
    substitution). Then, ensure that the inner function in each of your
    continuation helpers uses the same formal parameter as the second
    argument to apply-k (typically, v).

 11 Replace your higher-order function representations of
    continuations with a tagged-list data structure
    representation. Remember, if you add (else (k v)) as the last line of
    your match, you can test each transformation one at a time. If you're
    good, you can do almost all of this step with a keyboard macro.

 12 Remove the (else (k v)) line to ensure that you've properly
    removed all higher-order function representations of continuations.

 13 **Place your final version in a file named hw7.rkt and submit it
    via Gradescope.** Make sure to include both part I and part II of the
    assignment in your final submission as well.

|#

;; value-of-cps: lex-expr env continuation -> any
;; Purpose: Delivers the value of expr, evaluated in env, to continuation k.
(define (value-of-cps expr env k)
  (match expr
    ;; a constant is already a value
    [`(const ,cexpr) (apply-k k cexpr)]
    ;; evaluate nexp1, then nexp2, then multiply the two values
    [`(mult ,nexp1 ,nexp2) (value-of-cps nexp1 env (make-mult-outer-k nexp2 env k))]
    ;; evaluate the operand, then apply sub1 to its value
    [`(sub1 ,nexp) (value-of-cps nexp env (make-sub1-k k))]
    ;; evaluate the operand, then apply zero? to its value
    [`(zero ,nexp) (value-of-cps nexp env (make-zero-k k))]
    ;; evaluate the test, then continue with one branch as a tail call that reuses k
    [`(if ,test ,conseq ,alt) (value-of-cps test env (make-if-k conseq alt env k))]
    ;; bind k itself at address 0; if the body just returns, it returns to k
    [`(letcc ,body) (value-of-cps body (extend-env k env) k)]
    ;; evaluate k-exp to a continuation, then evaluate v-exp straight into it; the current k is dropped
    [`(throw ,k-exp ,v-exp) (value-of-cps k-exp env (make-throw-k v-exp env))]
    ;; evaluate e, then run the body in env extended with that value
    [`(let ,e ,body) (value-of-cps e env (make-let-k body env k))]
    ;; look up the lexical address and deliver what it holds
    [`(var ,y) (apply-env env y k)]
    ;; a closure is a value; it remembers the body and the definition-time env
    [`(lambda ,body) (apply-k k (make-closure body env))]
    ;; evaluate rator, then rand, then apply the closure with the caller's k
    [`(app ,rator ,rand) (value-of-cps rator env (make-app-outer-k rand env k))]))

;; Reorganized for readability

;; Environments

;; empty-env: none -> env
(define (empty-env)
  `(empty-env))

;; extend-env: val env -> env
;; Purpose: Binds addr 0 to a^, then every other addr is one frame out (1, 2, 3, ...)
(define (extend-env a^ env^)
  `(extend-env ,a^ ,env^))

;; apply-env: env natnum continuation -> any
;; Purpose: Delivers the value stored at address y in env to k^.
(define (apply-env env y k^)
  (match env
    ;; unbound: stop with an error and do not call k^
    [`(empty-env) (error 'value-of "unbound identifier")]
    ;; address 0 is this frame; otherwise look one frame out
    [`(extend-env ,a^ ,env^)
     (if (zero? y)
         (apply-k k^ a^)
         (apply-env env^ (sub1 y) k^))]))

;; Closures

;; make-closure: expr env -> closure
(define (make-closure body^ env^) `(closure ,body^ ,env^))

;; apply-closure: closure val continuation -> any
;; Purpose: Runs the closure's body with the argument at address 0, delivering to k^.
(define (apply-closure c a k^)
  (match c
    [`(closure ,body^ ,env^)
     (value-of-cps body^ (extend-env a env^) k^)]))

;; Continuations

;; empty-k: -> continuation
(define (empty-k) `(empty-k))

;; one constructor per place where value-of-cps has work pending
(define (make-mult-outer-k nexp2^ env^ k^) `(mult-outer-k ,nexp2^ ,env^ ,k^))
(define (make-mult-inner-k v1^ k^) `(mult-inner-k ,v1^ ,k^))
(define (make-sub1-k k^) `(sub1-k ,k^))
(define (make-zero-k k^) `(zero-k ,k^))
(define (make-if-k conseq^ alt^ env^ k^) `(if-k ,conseq^ ,alt^ ,env^ ,k^))
(define (make-throw-k v-exp^ env^) `(throw-k ,v-exp^ ,env^))
(define (make-let-k body^ env^ k^) `(let-k ,body^ ,env^ ,k^))
(define (make-app-outer-k rand^ env^ k^) `(app-outer-k ,rand^ ,env^ ,k^))
(define (make-app-inner-k f^ k^) `(app-inner-k ,f^ ,k^))

;; apply-k: continuation val -> any
;; Purpose: resumes the pending work in k with the incoming value v.
(define (apply-k k v)
  (match k
    ;; nothing pending: v is the final answer
    [`(empty-k) v]
    ;; v is the first factor; go evaluate the second
    [`(mult-outer-k ,nexp2^ ,env^ ,k^)
     (value-of-cps nexp2^ env^ (make-mult-inner-k v k^))]
    ;; v is the second factor; multiply and deliver
    [`(mult-inner-k ,v1^ ,k^) (apply-k k^ (* v1^ v))]
    [`(sub1-k ,k^) (apply-k k^ (sub1 v))]
    [`(zero-k ,k^) (apply-k k^ (zero? v))]
    ;; v is the test result; only the chosen branch runs
    [`(if-k ,conseq^ ,alt^ ,env^ ,k^)
     (if v
         (value-of-cps conseq^ env^ k^)
         (value-of-cps alt^ env^ k^))]
    ;; v is the continuation being thrown to
    [`(throw-k ,v-exp^ ,env^) (value-of-cps v-exp^ env^ v)]
    ;; v is the bound value; run the body with it at address 0
    [`(let-k ,body^ ,env^ ,k^) (value-of-cps body^ (extend-env v env^) k^)]
    ;; v is the closure; go evaluate the argument
    [`(app-outer-k ,rand^ ,env^ ,k^)
     (value-of-cps rand^ env^ (make-app-inner-k v k^))]
    ;; v is the argument; apply the closure
    [`(app-inner-k ,f^ ,k^) (apply-closure f^ v k^)]))

(module+ test
  (require rackunit)

  (define-syntax check-true*
    (syntax-rules ()
      [(_ pred (actual expected) ...)
       (begin (check-true (pred actual expected)) ...)]))

(check-true* equal?
        ((value-of-cps '(const 5) (empty-env) (empty-k)) 5)
        ((value-of-cps '(mult (const 5) (const 5)) (empty-env) (empty-k)) 25)
        ((value-of-cps '(zero (const 5)) (empty-env) (empty-k)) #f)
        ((value-of-cps '(zero (mult (const 5) (const 5))) (empty-env) (empty-k)) #f)
        ((value-of-cps '(sub1 (const 5)) (empty-env) (empty-k)) 4)
        ((value-of-cps '(sub1 (sub1 (const 5))) (empty-env) (empty-k)) 3)
        ((value-of-cps '(sub1 (sub1 (const 5))) (extend-env 3 (empty-env)) (empty-k)) 3)
        ((value-of-cps '(zero (sub1 (const 6))) (empty-env) (empty-k)) #f)
        ((value-of-cps '(mult (sub1 (const 5)) (const 5)) (empty-env) (empty-k)) 20)
        ((value-of-cps '(mult (const 5) (sub1 (const 5))) (empty-env) (empty-k)) 20)
        ((value-of-cps '(if (zero (const 5)) (const 3) (const 4)) (empty-env) (empty-k)) 4)
        ((value-of-cps '(if (zero (const 0)) (const 4) (const 3)) (empty-env) (empty-k)) 4)
        ((value-of-cps '(mult (if (zero (const 0)) (const 4) (const 3)) (const 2)) (empty-env) (empty-k)) 8)
        ((value-of-cps '(mult (const 2) (if (zero (const 0)) (const 4) (const 3))) (empty-env) (empty-k)) 8)
        ((value-of-cps '(let (const 6) (const 4)) (empty-env) (empty-k)) 4)
        ((value-of-cps '(let (const 5) (var 0)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(let (mult (const 5) (const 3)) (var 0)) (empty-env) (empty-k)) 15)
        ((value-of-cps '(let (const 5) (mult (var 0) (var 0))) (empty-env) (empty-k)) 25)
        ((value-of-cps '(let (const 5) (let (const 6) (var 1))) (empty-env) (empty-k)) 5)
        ((value-of-cps '(let (const 5) (let (const 6) (mult (var 0) (var 1)))) (empty-env) (empty-k)) 30)
        ((value-of-cps '(let (const 5) (let (const 6) (mult (var 1) (var 0)))) (empty-env) (empty-k)) 30)
        ((value-of-cps '(mult (const 5) (let (const 5) (var 0))) (empty-env) (empty-k)) 25)
        ((value-of-cps '(app (lambda (const 5)) (const 6)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(app (lambda (var 0)) (const 5)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(app (app (lambda (lambda (var 1))) (const 6)) (const 5)) (empty-env) (empty-k)) 6)
        ((value-of-cps '(app (lambda (app (lambda (var 1)) (const 6))) (const 5)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(app (lambda (if (zero (var 0)) (const 4) (const 5))) (const 3)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(app (if (zero (const 4)) (lambda (var 0)) (lambda (const 5))) (const 3)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(app (if (zero (const 0)) (lambda (var 0)) (lambda (const 5))) (const 3)) (empty-env) (empty-k)) 3)
        ((value-of-cps '(letcc (const 5)) (empty-env) (empty-k)) 5)
        ((value-of-cps '(letcc (throw (var 0) (const 5))) (empty-env) (empty-k)) 5)
        ((value-of-cps '(letcc (throw (var 0) (mult (const 5) (const 5)))) (empty-env) (empty-k)) 25)
        ((value-of-cps '(letcc (throw (app (lambda (var 0)) (var 0)) (mult (const 5) (const 5)))) (empty-env) (empty-k)) 25)
        ((value-of-cps '(letcc (sub1 (throw (var 0) (const 5)))) (empty-env) (empty-k)) 5)
        ((value-of-cps '(letcc (throw (throw (var 0) (const 5)) (const 6))) (empty-env) (empty-k)) 5)
        ((value-of-cps '(letcc (throw (const 5) (throw (var 0) (const 5)))) (empty-env) (empty-k)) 5)
        ((value-of-cps '(mult (const 3) (letcc (throw (const 5) (throw (var 0) (const 5))))) (empty-env) (empty-k)) 15)
        ((value-of-cps '(if (zero (const 5)) (app (lambda (app (var 0) (var 0))) (lambda (app (var 0) (var 0)))) (const 4))
                       (empty-env)
                       (empty-k))
         4)
        ((value-of-cps '(if (zero (const 0)) (const 4) (app (lambda (app (var 0) (var 0))) (lambda (app (var 0) (var 0)))))
                       (empty-env)
                       (empty-k))
         4)
        ((value-of-cps '(app (lambda (app (app (var 0) (var 0)) (const 2)))
                             (lambda
                               (lambda
                                 (if (zero (var 0))
                                     (const 1)
                                     (app (app (var 1) (var 1)) (sub1 (var 0)))))))
                       (empty-env)
                       (empty-k))
         1))
)

#| Optional enrichment

Part III and Just Dessert are optional. Gradescope does not require or
test them. They extend the week's ideas toward streams and mechanical
CPS transformation, and you are strongly encouraged to attempt them.
They deliberately have no starter stubs.

|#

#| Part III |#

#|

This week, you'll also get to learn about streams, a data-structure
that enables us to process infinite lists of items. It's a lazily-evaluated, memoized
(also termed //delayed//) list.

To play around, we'll first need to implement a few tools.

|#

(define-syntax cons$
  (syntax-rules ()
    ((cons$ x y) (cons x (delay y)))))

(define car$ car)

(define cdr$
  (lambda ($) (force (cdr $))))

#|

We'll get back to those helpers. For now, it's enough that they're
tweaked cons, car, and cdr.  The first question to ask is: how do you
build an infinite list? The only reasonable answer is: one item at a
time, as needed.  Here, we're going to define an infinite stream of
ones.

|#

(define inf-1s (cons$ 1 inf-1s))

#|

It looks like that can't possibly work. We're defining the stream in
terms of itself. That's a circular definition.  But, in fact, that's
precisely what we're after. We're defining a list that has a 1 in
front and whose cdr - well, whatever that thing is, it has a 1 in the
front of it. And thus it's 1s all the way down.

So we can build a procedure take$

|#

(define take$
  (lambda (n $)
    (cond
      ((zero? n) '())
      (else (cons (car$ $)
              (let ((n- (sub1 n)))
                (cond
                  ((zero? n-) '())
                  (else (take$ n- (cdr$ $))))))))))

#|

... that pulls n items from the stream, and returns them in a
list (the $ stands for $tream, by the way).

|#

;; > (take$ 5 inf-1s)
;; (1 1 1 1 1)
;; > (take$ 10 inf-1s)
;; (1 1 1 1 1 1 1 1 1 1)

#|

So how is this all working? There's nothing to car$. That's just
car with fancy window-dressing. cons$ is the first macro
definition we've looked at in class. But there's nothing much to it,
either. You can think of it as performing a textual transformation --
every time we see something of the form (cons$ <thing1>
<thing2>), that code is actually transformed as (cons
<thing1> (delay <thing2>)) Importantly, <thing2> isn't
evaluated in the process. But do take note of the delay form, and
the force form in cdr$. As we've already seen, there are times
in which we might like to evaluate an expression only once, and
thereafter just return that already computed value. And we might like
to hold off on doing that evaluation, instead of doing it right
away. delay does both of those -- it creates a //promise//, of
which force can then force the evaluation. From there on out,
every time we force that promise, we get the same value.

|#

;; > (define worlds-worst-random
;;     (delay (random 4)))
;; > (force worlds-worst-random)
;; 2
;; > (force worlds-worst-random)
;; 2
;; > (force worlds-worst-random)
;; 2

#|

So, to put it all together, we define inf-1s to be a cons whose
car is 1 and whose cdr is a promise. When we finally get
around to evaluating that promise, we find that its value is in fact
inf-1s -- that is, a cons whose car is 1 and whose cdr is
a promise.

Hopefully that all makes sense.

Your task this week is to implement the tribonacci stream. It is the
sequence in which 0 is the first number, 1 is the
second, 1 is the third, and the values thereafter are each the sum of
the three previous values in the sequence. Call it trib$.

 (check-true* equal?
   ((car$ trib$) 0)
   ((car$ (cdr$ trib$)) 1)
   ((take$ 7 trib$) '(0 1 1 2 4 7 13)))

|#


#| ==== Just Dessert ==== |#

#|

By now, you probably have a pretty strong intuition as to the
mechanical process by which you CPS programs. As mentioned in class,
it is possible to write a program that automatically performs CPS
transformations. Write a procedure that takes an expression and
returns a CPSed version of that expression. You may find it
exceedingly helpful to consult Danvy and Nielsen's ["A First-Order
One-Pass CPS
Transformation"](https://link.springer.com/content/pdf/10.1007/3-540-45931-6_8.pdf),
specifically Figure 2 on page 102 and the surrounding discussion. Take
note of the four specific cases in which they treat applications.

This is a little more open-ended than most of our problems; you can
get it to work on the lambda-calculus, or add more forms if you
want (this will probably make it easier to test and to use it). Add a
comment in your assignment to tell us how to call and to use your
CPSer.


If you /really/ want to prove that you have a product that you can
sell to next semester's students, make sure your procedure should be
able to handle fact, fib, and something like the product function below.

|#

(define product
  (lambda (ls)
    ((lambda (f)
       (f f ls))
     (lambda (f ls)
       (cond
	 [(empty? ls) 1]
	 [(zero? (car ls)) 0]
	 [else (* (car ls) (f f (cdr ls)))])))))