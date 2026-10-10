#lang racket

(provide apply-env
         extend-env
         empty-env
         val-of-cbv
         val-of-cbr
         val-of-cbname
         val-of-cbneed)

(require rackunit)

#|  Parameter-passing Conventions |#

;; These are your father's parentheses. Elegant weapons for a more
;; ... civilized age.

;; - Randall Munroe,
;; [xkcd](http://imgs.xkcd.com/comics/lisp_cycles.png)

#| Assignment Guidelines |#

;; In addition to the standard Assignment Guidelines

;; All four interpreters must handle the following: booleans, numbers,
;; variables, lambda, let, application, zero?, sub1, *, if, and
;; random.

;; Your val-of-cbr and val-of-cbv interpreters (not the other two)
;; must also handle begin2 and set!.

;; In val-of-cbname and val-of-cbneed, let must be non-strict: do not
;; evaluate the right-hand-side expression before extending the
;; environment. CBName and CBNeed must not force it merely to make the
;; binding, and CBNeed must preserve sharing across both names.

;; You will need to implement the empty-env, extend-env, apply-env
;; helpers. You can reuse this same set of helpers for every
;; interpreter.

;; You should use a **representation-dependent**, functional
;; representation of closures. (If it helps you to know, there's
;; nothing prohibiting you from making representation-independent
;; closures in whatever representation you wish. It is just slightly
;; unfortunate to re-implement them in every different interpreter.)

;; You should use //boxes// to help implement parameter-passing
;; conventions.

;; For more about boxes and the operations you can perform with them,
;; see the [Racket
;; Documentation](http://docs.racket-lang.org/reference/boxes.html).


#| Parameter-passing Conventions |#

;; empty-env: -> Env
;; Purpose: Makes an env with no bindings; looking up any variable is an error.
(define (empty-env)
  (lambda (y) (error 'empty-env "unbound variable: ~a" y)))

;; extend-env: symbol Box Env -> Env
;; Purpose: Makes a new env that maps x to a, and defers to env for everything else.
(define (extend-env x a env)
  (lambda (y) (if (eqv? x y) a (apply-env env y))))

;; apply-env: Env symbol -> Box
;; Purpose: Looks up the box that y is bound to in env.
(define (apply-env env y)
  (env y))

(check-equal? (apply-env (extend-env 'x 1 (empty-env)) 'x) 1)
(check-equal? (apply-env (extend-env 'x 2 (extend-env 'x 1 (empty-env))) 'x) 2)
(check-equal? (apply-env (extend-env 'x 1 (extend-env 'y 2 (empty-env))) 'y) 2)

#|

1. val-of-cbv, your call-by-value interpreter. Implement this by
/boxing/ values before putting them in the environment, and add
our "`(,rator ,y) #:when (symbol? y)" line that directly retrieves its
value from the environment. This line should have the "(box (unbox
...))"  on the right-hand side. We're doing this because it'll help to
set up for the next interpreter.

|#

;; val-of-cbv: Exp Env -> Value
;; Purpose: Evaluates exp using call-by-value. Every argument is evaluated first,
;; then put in a NEW box, so a callee's set! never reaches the caller's variable.
(define (val-of-cbv exp env)
  (match exp
    [`,b #:when (boolean? b) b]
    [`,n #:when (number? n) n]
    [`,y #:when (symbol? y) (unbox (apply-env env y))]
    [`(zero? ,e) (zero? (val-of-cbv e env))]
    [`(sub1 ,e) (sub1 (val-of-cbv e env))]
    [`(* ,e1 ,e2) (* (val-of-cbv e1 env) (val-of-cbv e2 env))]
    [`(if ,t ,c ,a) (if (val-of-cbv t env)
                        (val-of-cbv c env)
                        (val-of-cbv a env))]
    [`(random ,n) (random (val-of-cbv n env))]
    [`(begin2 ,e1 ,e2) (begin (val-of-cbv e1 env) (val-of-cbv e2 env))]
    [`(set! ,x ,e) (set-box! (apply-env env x) (val-of-cbv e env))]
    ;; Extension for Q5
    [`(add1 ,e) (add1 (val-of-cbv e env))]
    [`(quote ,v) v]
    [`(null? ,e) (null? (val-of-cbv e env))]
    [`(cons ,a ,d) (cons (val-of-cbv a env) (val-of-cbv d env))]
    [`(car ,e) (car (val-of-cbv e env))]
    [`(cdr ,e) (cdr (val-of-cbv e env))]
    [`(cons^ ,a ,d) (cons (lambda () (val-of-cbv a env))
                          (lambda () (val-of-cbv d env)))]
    [`(car^ ,e) ((car (val-of-cbv e env)))]
    [`(cdr^ ,e) ((cdr (val-of-cbv e env)))]
    [`(let [(,x ,e)] ,b) (val-of-cbv b (extend-env x (box (val-of-cbv e env)) env))]
    [`(lambda (,x) ,b) (lambda (a) (val-of-cbv b (extend-env x a env)))]
    [`(,rator ,y) #:when (symbol? y)
                  ((val-of-cbv rator env) (box (unbox (apply-env env y))))]
    [`(,rator ,rand) ((val-of-cbv rator env) (box (val-of-cbv rand env)))]))

 
(check-equal? (val-of-cbv '((lambda (x) (* x x)) 7) (empty-env)) 49)
(check-equal? (val-of-cbv '(let ((x 5)) (let ((x (sub1 x))) x)) (empty-env)) 4)
(check-equal? (val-of-cbv '(let ((x 5)) (begin2 (set! x 10) x)) (empty-env)) 10)
(check-equal? (val-of-cbv '(let ((x 5)) (begin2 ((lambda (y) (set! y 99)) x) x))
                          (empty-env)) 5)

#|

2. Here, implement val-of-cbr, your call-by-reference
interpreter. This should involve only a slight change from your
val-of-cbv interpreter.

|#

;; val-of-cbr: Exp Env -> Value
;; Purpose: Evaluates exp using call-by-reference. A variable passed as an argument
;; shares its box with the parameter (same "address"), so set! in the callee is
;; visible to the caller. Any other argument gets a fresh box.
(define (val-of-cbr exp env)
  (match exp
    [`,b #:when (boolean? b) b]
    [`,n #:when (number? n) n]
    [`,y #:when (symbol? y) (unbox (apply-env env y))]
    [`(zero? ,e) (zero? (val-of-cbr e env))]
    [`(sub1 ,e) (sub1 (val-of-cbr e env))]
    [`(* ,e1 ,e2) (* (val-of-cbr e1 env) (val-of-cbr e2 env))]
    [`(if ,t ,c ,a) (if (val-of-cbr t env)
                        (val-of-cbr c env)
                        (val-of-cbr a env))]
    [`(random ,n) (random (val-of-cbr n env))]
    [`(begin2 ,e1 ,e2) (begin (val-of-cbr e1 env) (val-of-cbr e2 env))]
    [`(set! ,x ,e) (set-box! (apply-env env x) (val-of-cbr e env))]
    [`(let ((,x ,e)) ,body)
     (val-of-cbr body (extend-env x (box (val-of-cbr e env)) env))]
    [`(lambda (,x) ,body)
     (lambda (a) (val-of-cbr body (extend-env x a env)))]
    [`(,rator ,y) #:when (symbol? y)
     ((val-of-cbr rator env) (apply-env env y))]       
    [`(,rator ,rand)
     ((val-of-cbr rator env) (box (val-of-cbr rand env)))]))

(check-equal? (val-of-cbr '((lambda (x) (* x x)) 7) (empty-env)) 49)
(check-equal? (val-of-cbr '(let ((x 5)) (begin2 ((lambda (y) (set! y 99)) x) x))
                          (empty-env)) 99)
(check-equal? (val-of-cbr '(let ((x 5)) (begin2 ((lambda (y) (set! y 99)) (sub1 x)) x))
                          (empty-env)) 5)
(check-equal? (val-of-cbr '(let ((x 1)) ((lambda (f) (begin2 (f x) x)) (lambda (y) (set! y 7))))
                          (empty-env)) 7)

#|

3. Implement val-of-cbname, your call-by-name interpreter. This should
involve only a slight change from your val-of-cbr interpreter.

|#

;; val-of-cbname: Exp Env -> Value
;; Purpose: Evaluates exp using call-by-name. Arguments and let rhs are
;; delayed in thunks and re-run every time the variable is used (no sharing).
(define (val-of-cbname exp env)
  (match exp
    [`,b #:when (boolean? b) b]
    [`,n #:when (number? n) n]
    [`,y #:when (symbol? y) ((unbox (apply-env env y)))]
    [`(zero? ,e) (zero? (val-of-cbname e env))]
    [`(sub1 ,e) (sub1 (val-of-cbname e env))]
    [`(* ,e1 ,e2) (* (val-of-cbname e1 env) (val-of-cbname e2 env))]
    [`(if ,t ,c ,a) (if (val-of-cbname t env)
                        (val-of-cbname c env)
                        (val-of-cbname a env))]
    [`(random ,n) (random (val-of-cbname n env))]
    [`(let ((,x ,e)) ,body)
     (val-of-cbname body
                    (extend-env x (box (lambda () (val-of-cbname e env))) env))]
    [`(lambda (,x) ,body)
     (lambda (a) (val-of-cbname body (extend-env x a env)))]
    [`(,rator ,y) #:when (symbol? y)
     ((val-of-cbname rator env) (apply-env env y))]  
    [`(,rator ,rand)
     ((val-of-cbname rator env) (box (lambda () (val-of-cbname rand env))))]))

(define omega '((lambda (x) (x x)) (lambda (x) (x x))))
 
(check-equal? (val-of-cbname '((lambda (x) (* x x)) 7) (empty-env)) 49)
(check-equal? (val-of-cbname `((lambda (z) 7) ,omega) (empty-env)) 7)
(check-equal? (val-of-cbname `(let ((x ,omega)) 3) (empty-env)) 3)
(check-equal? (val-of-cbname '(let ((x 2)) (let ((f (lambda (e) x))) (let ((x 5)) (f 0))))
                             (empty-env)) 2)
       

#|

4. Implement val-of-cbneed, your call-by-need interpreter. This should
involve only a small change from your val-of-cbname interpreter.

|#

;; unbox/need: Box -> Value
;; Purpose: Runs the thunk in b, then overwrites b with a thunk that just returns
;; the saved answer, so later lookups reuse the result instead of recomputing it.
(define (unbox/need b)
  (let ([v ((unbox b))])
    (set-box! b (lambda () v))
    v))

;; val-of-cbneed: Exp Env -> Value
;; Purpose: Evaluates exp using cbneed, like cbname, but each delayed expression 
;; is evaluated at most once and the result is shared by every name
;; that points at that same box.
(define (val-of-cbneed exp env)
  (match exp
    [`,b #:when (boolean? b) b]
    [`,n #:when (number? n) n]
    [`,y #:when (symbol? y) (unbox/need (apply-env env y))]
    [`(zero? ,e) (zero? (val-of-cbneed e env))]
    [`(sub1 ,e) (sub1 (val-of-cbneed e env))]
    [`(* ,e1 ,e2) (* (val-of-cbneed e1 env) (val-of-cbneed e2 env))]
    [`(if ,t ,c ,a) (if (val-of-cbneed t env)
                        (val-of-cbneed c env)
                        (val-of-cbneed a env))]
    [`(random ,n) (random (val-of-cbneed n env))]
    [`(let ((,x ,e)) ,body)
     (val-of-cbneed body
                    (extend-env x (box (lambda () (val-of-cbneed e env))) env))]
    [`(lambda (,x) ,body)
     (lambda (a) (val-of-cbneed body (extend-env x a env)))]
    [`(,rator ,y) #:when (symbol? y)
     ((val-of-cbneed rator env) (apply-env env y))] 
    [`(,rator ,rand)
     ((val-of-cbneed rator env) (box (lambda () (val-of-cbneed rand env))))]))

(check-equal? (val-of-cbneed '((lambda (x) (* x x)) 7) (empty-env)) 49)
(check-equal? (val-of-cbneed `((lambda (z) 7) ,omega) (empty-env)) 7)
(check-equal? (val-of-cbneed `(let ((x ,omega)) 3) (empty-env)) 3)

#| Brainteasers |#

#|

5. ["CONS should not Evaluate its
Arguments"](http://www.cs.indiana.edu/pub/techreports/TR44.pdf), a
highly influential 1970s PL paper, points out the need for lazy data
structures. Cons that does not evaluate its arguments is easy to
implement as a macro in Racket, but you will be adding it to your
interpreter. To your "val-of-cbv" interpreter, add "cons^" that does
NOT evaluate its arguments strictly (in other words, it evaluates them
lazily). You should also create the corresponding versions of car and
cdr ("car^" and "cdr^") that operate on "cons^". You should add the
strict versions (regular "cons", "car", "cdr") to your val-of-cbv
interpreter along with add1, empty list, let, and null?. Ensure that
this cons test evaluates to '(1 2 3 4 5).

|#

 
(define cons-test
  '(let ((fix (lambda (f)
               ((lambda (x) (f (lambda (v) ((x x) v))))
                (lambda (x) (f (lambda (v) ((x x) v))))))))
      (let ((map (fix (lambda (map)
                        (lambda (f)
                          (lambda (l)
                             (if (null? l)
                                 '()
                                 (cons^ (f (car^ l))
                                        ((map f) (cdr^ l))))))))))
        (let ((take (fix (lambda (take)
                           (lambda (l)
                             (lambda (n)
                               (if (zero? n)
                                   '()
                                    (cons (car^ l)
                                          ((take (cdr^ l)) (sub1 n))))))))))
          ((take ((fix (lambda (m)
                         (lambda (i)
                           (cons^ 1 ((map (lambda (x) (add1 x))) (m i)))))) 0)) 5)))))

(check-equal? (val-of-cbv cons-test (empty-env)) '(1 2 3 4 5))
(check-equal? (val-of-cbv '(cons 1 (cons 2 '())) (empty-env)) '(1 2))
(check-equal? (val-of-cbv '(car^ (cons^ 1 ((lambda (x) (x x)) (lambda (x) (x x)))))
                          (empty-env)) 1)
(check-equal? (val-of-cbv '(null? '()) (empty-env)) #t)

#| Just Dessert |#

#|

6. To which value-of interpreter is norm, the dessert from the last
assignment, most similar? Why? For your choice of interpreter, give an
example expression where that interpreter still behaves differently
from norm.

|#

#|

Answer:

norm is most similar to call by name. When it performs a beta reduction, it passes
the argument into the body without evaluating it first, so the argument is only evaluated
if the body needs it. Since norm just copies the expression in, it gets re-evaluated
every time it's used, not shared (same as cbname).
 
The differences are on lambda exp with bodies that evaluate to a simple data type.
Ex. (lambda (x) (* 3 3)). norm would simplify the body to (lambda (x) 9) but
val-of-cbname would return a procedure without touching the body.

|#

#|

7. Loeb (and Moeb) are cool functions. Read
[this](https://github.com/quchen/articles/blob/master/loeb-moeb.md)
and do something neat with it. You could get it working in your
call-by-need interpreter, for instance. Or make a spreadsheet thingy
with it, I guess. If you have trouble with the syntax, well, then
[learn you a Haskell for great good!](http://learnyouahaskell.com).

|#

;; loeb: (listof ((natural -> any) -> any)) -> (listof any)
;; Purpose: Each formula gets "get", which looks up another cell by its position.
;; Returns every cell's final value. Cells are delayed, so the order of the
;; formulas doesn't matter, as long as nothing refers to itself in a circle.
(define (loeb formulas)
  (define cells
    (map (lambda (f) (delay (f (lambda (i) (force (list-ref cells i))))))
         formulas))
  (map force cells))

;; cell 0 = price, cell 1 = 10% VAT, cell 2 = price + VAT
(check-equal?
 (loeb (list (lambda (get) 10)
             (lambda (get) (* 1/10 (get 0)))
             (lambda (get) (+ (get 0) (get 1)))))
 '(10 1 11))

;; same sheet with the total listed first: order doesn't matter
(check-equal?
 (loeb (list (lambda (get) (+ (get 1) (get 2)))
             (lambda (get) 10)
             (lambda (get) (* 1/10 (get 1)))))
 '(11 10 1))

;; each cell is the previous one plus 1
(check-equal?
 (loeb (list (lambda (get) 1)
             (lambda (get) (+ 1 (get 0)))
             (lambda (get) (+ 1 (get 1)))))
 '(1 2 3))

