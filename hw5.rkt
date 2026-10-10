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

(define (empty-env)
  (lambda (y) (error 'empty-env "unbound variable: ~a" y)))

(define (extend-env x a env)
  (lambda (y) (if (eqv? x y) a (apply-env env y))))

(define (apply-env env y)
  (env y))

#|

1. val-of-cbv, your call-by-value interpreter. Implement this by
/boxing/ values before putting them in the environment, and add
our "`(,rator ,y) #:when (symbol? y)" line that directly retrieves its
value from the environment. This line should have the "(box (unbox
...))"  on the right-hand side. We're doing this because it'll help to
set up for the next interpreter.

|#

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



#|

2. Here, implement val-of-cbr, your call-by-reference
interpreter. This should involve only a slight change from your
val-of-cbv interpreter.

|#

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
     ((val-of-cbr rator env) (apply-env env y))]          ; <-- the change
    [`(,rator ,rand)
     ((val-of-cbr rator env) (box (val-of-cbr rand env)))]))


#|

3. Implement val-of-cbname, your call-by-name interpreter. This should
involve only a slight change from your val-of-cbr interpreter.

|#

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

#|

4. Implement val-of-cbneed, your call-by-need interpreter. This should
involve only a small change from your val-of-cbname interpreter.

|#

(define (unbox/need b)
  (let ([v ((unbox b))])
    (set-box! b (lambda () v))
    v))
 
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
every time it’s used, not shared (same as cbname).

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


