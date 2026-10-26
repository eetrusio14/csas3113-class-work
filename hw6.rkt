#lang racket

(require rackunit)
(require racket/trace)

;; Gradescope loads this file as a module and expects each required name
;; in the provide form below to exist. Replace each "not implemented"
;; expression with your solution, but keep the filename, names, and
;; argument lists unchanged.

(provide last-non-zero
         mult/cc
         my-*
         walk-cps
         times-cps
         times-cps-shortcut
         cexpt-cps
         count-syms*-cps
         cons-cell-count-cps
         ack-cps
         fib-cps
         unfold-cps
         pascal-cps
         unify-cps
         M-cps
         use-of-M-cps
         empty?-cps
         car-cps
         cdr-cps
         strange-cps
         use-of-strange-cps
         why-cps)
#| Assignment 6: Continuation-Passing Style |#

;; Say you're in the kitchen in front of the refrigerator, thinking
;; about a sandwich. You take a continuation right there and stick it
;; in your pocket. Then you get some turkey and bread out of the
;; refrigerator and make yourself a sandwich, which is now sitting on
;; the counter. You invoke the continuation in your pocket, and you
;; find yourself standing in front of the refrigerator again, thinking
;; about a sandwich. But fortunately, there's a sandwich on the
;; counter, and all the materials used to make it are gone. So you eat
;; it.

;; -- Luke Palmer


#| Assignment Guidelines |#

;; In addition to the standard Assignment Guidelines

;; When CPSing, you may treat built-in procedures such as empty?,
;; add1, assv, car, <, and the like as "simple".

;; No, you may not "simplify" or rewrite any of these programs to
;; another form and then CPS that simpler formula instead. Use the
;; method we described in class.

;; Test your CPSed procedures using the initial continuation returned
;; from the following (uncommented) empty-k. You may have seen empty-k
;; defined as

;; (define (empty-k)
;;   (λ (v) v))

;; However, the one below is much better, in that it will help you
;; better detect if you have made a mistake in cps-ing.

(define (empty-k)
  (let ((once-only #f))
    (λ (v)
      (if once-only
          (error 'empty-k "You can only invoke the empty continuation once")
          (begin (set! once-only #t) v)))))

#| let/cc |#

;; 1. Complete the following definition of last-non-zero, a function
;; which takes a list of numbers and returns the last cdr whose car is
;; 0. In other words, when starting from the right of the list, it
;; should be all numbers before the first 0 is reached. See the test
;; cases below for examples. Your solution should be naturally
;; recursive, and should not contain any calls to member-like
;; operations or last-non-zero. You must not modify the provided code
;; beyond adding a body. You may of course add newlines as needed. My
;; advice is to 1. Get it working for the base case. 2 Get it working
;; for a list without any 0s in it. 3. Get it working for a list with
;; one 0 in it. 4. Get it working for a list with more than one 0 in
;; it.

;; Signature: listof numbers -> listof numbers
;; Purpose: Returns the cdr of a list after the occurence of the last 0.
(define (last-non-zero ls)
  (let/cc k
    (letrec
      ((lnz
         (λ (ls)
           (cond
             [(empty? ls) '()] ;; if the list is empty, return an empty list
             [(zero? (car ls)) (k (lnz (cdr ls)))] ;; if the car is 0, discard front thus far and continue with the cdr
             [else (cons (car ls) (lnz (cdr ls)))])))) ;; if the car is not 0, keep it and continue with the cdr
      (lnz ls))))

(module+ test
  (require rackunit)
  
  (test-equal?
    "test for empty list
   (last-non-zero '())"
    (last-non-zero '())
    '())
  
  (test-equal?
    "test for a non-empty list with no zeroes
   (last-non-zero '(1 2 3 4 5))"
    (last-non-zero '(1 2 3 4 5))
    '(1 2 3 4 5))
  
  (test-equal?
    "test for a list with one zero in the middle
   (last-non-zero '(1 2 3 0 4 5))"
    (last-non-zero '(1 2 3 0 4 5))
    '(4 5))
  
  (test-equal?
    "test for a list with two zeroes in the middle
   (last-non-zero '(1 0 2 3 0 4 5))"
    (last-non-zero '(1 0 2 3 0 4 5))
    '(4 5)))

#| Direct vs. accumulator-passing vs. call/cc. |#

;; 2. Consider the following definitions of mult and mult/acc, a
;; function which takes a list of numbers and returns the product,
;; respectively written in direct and accumulator-passing
;; styles. Then, complete the definition below to build a third
;; version, mult/cc, which instead uses a system continuation k to
;; return with 0 if the list contains a 0. Your implementation should
;; be naturally-recursive, and should not contain any calls to
;; member-like operations or last-non-zero. You must not modify the
;; provided code beyond adding a body. You may of course add newlines
;; as needed. For this problem, you should use my-* as your
;; multiplication operation.

(define (my-* m n)
  (* m n))

#|
> (define (mult n*)
    (letrec
      ((m
         (λ (n*)
           (cond
             ((empty? n*) 1)
             ((zero? (car n*)) 0)
             (else (my-* (car n*) (m (cdr n*))))))))
      (m n*)))
> (define (mult/acc n*)
    (letrec
      ((m/acc
         (λ (n* acc)
           (cond
             ((empty? n*) acc)
             ((zero? (car n*)) 0)
             (else (m/acc (cdr n*) (my-* (car n*) acc)))))))
      (m/acc n* 1)))
|#


(define (mult/cc n*)
  (let/cc k
    (letrec
      ((m/cc
         (λ (n*)
           (cond
             [(empty? n*) 1] ;; if we've reached the empty list, return 1
             [(zero? (car n*)) (k 0)] ;; if we find a 0, invoke the continuation k with 0
             [else (my-* (car n*) (m/cc (cdr n*)))])))) ;; simply multiply the car with the recursive call on the cdr
      (m/cc n*))))

(check-equal? (mult/cc '()) 1)
(check-equal? (mult/cc '(1 2 3 0 4 5)) 0)
(check-equal? (mult/cc '(1 2 3 4 5)) 120)


;; If you require the racket trace library, and define my-* to be
;; traced, we see an interesting property. When you have a 0 in the
;; list, both the direct and accumulator passing versions perform
;; multiplications until they reach a 0, yet mult/cc performs //no//
;; multiplications in the presence of a 0. Which is neat.

#|
> (require racket/trace)
> (trace-define (my-* m n)
    (* m n))
> (mult '(1 2 3 4 0 6 7 8 9))
>(my-* 4 0)
<0
>(my-* 3 0)
<0
>(my-* 2 0)
<0
>(my-* 1 0)
<0
0
> (mult/acc '(1 2 3 4 0 6 7 8 9))
>(my-* 1 1)
<1
>(my-* 2 1)
<2
>(my-* 3 2)
<6
>(my-* 4 6)
<24
0
> (mult/cc '(1 2 3 4 0 6 7 8 9))
0
|#

#| CPS |#

#|

In this portion of the assignment, you will also have to construct and
submit your own tests. We use the explicit `λ` syntax here
because we think it may be helpful to you; of course you are not
required to do so.

|#

;; 3. Define and test a procedure walk-cps that is a CPSed version of
;; the following walk procedure:

(define walk
  (λ (v ls)
    (cond
      [(symbol? v)
       (let ((p (assv v ls)))
         (cond
           [p (walk (cdr p) ls)]
           [else v]))]
      [else v])))

;; Here are some sample calls to walk:

#|

> (walk 'a '((a . 5) (b . 6) (c . 7)))
5
> (walk 'a '((a . b) (b . c) (c . 7)))
7
> (walk 'a '((a . q) (r . s) (q . r)))
s
> (walk 'a '((a . q) (r . s) (q . r) (s . 10)))
10

|#


;; Signature: pairof (sym . value) ls continuation -> any
;; Purpose: CPSed version of walk; applies continuation k to the final value v walks to.
(define (walk-cps v ls k)
  (letrec
    ((walk-cps
       (lambda (v ls k)
         (cond
           [(symbol? v) ;; v might have a substitution in ls
            (let ((p (assv v ls)))
              (cond
                [p (walk-cps (cdr p) ls k)] ;; found one, keep walking its value with the same k
                [else (k v)]))] ;; no substitution for v, it's already a value
           [else (k v)])))) ;; v isn't a symbol, so it's already a value
    (walk-cps v ls k)))

(check-equal? (walk-cps 'a '((a . 5) (b . 6) (c . 7)) (empty-k)) 5)
(check-equal? (walk-cps 'a '((a . b) (b . c) (c . 7)) (empty-k)) 7)
(check-equal? (walk-cps 'a '((a . q) (r . s) (q . r)) (empty-k)) 's)
(check-equal? (walk-cps 'a '((a . q) (r . s) (q . r) (s . 10)) (empty-k)) 10)


;; 4. Define and test a procedure times-cps that is a CPSed version of
;; the following times procedure.

(define times
  (λ (ls)
    (cond
      [(empty? ls) 1]
      [(zero? (car ls)) 0]
      [else (* (car ls) (times (cdr ls)))])))

;; Signature: listof numbers continuation -> number
;; Purpose: CPSed version of times; applies continuation k to the product of the numbers in ls.
(define (times-cps ls k)
  (letrec
    ((times-cps
       (lambda (ls k)
         (cond
           [(empty? ls) (k 1)]
           [(zero? (car ls)) (k 0)]
           [else (times-cps (cdr ls) (lambda (v) (k (* (car ls) v))))]))))
    (times-cps ls k)))

(check-equal? (times-cps '(1 2 3 4 5) (empty-k)) 120)
(check-equal? (times-cps '(1 2 3 0 4 5) (empty-k)) 0)
(check-equal? (times-cps '() (empty-k)) 1)

;; 5. Define a modified version of your times-cps above, called
;; times-cps-shortcut that doesn't apply k in the zero case. Instead,
;; maintain the behavior of the zero? case in times - simply returning
;; the 0 and not performing further computation. While this certainly
;; violates the standard rules of CPSing the program, it provides an
;; interesting look at optimizations CPSing allows us: The
;; whole-program CPS transformation permits you the kinds of control
;; operations in languages that don't natively support them.


;; Signature: listof numbers continuation -> number
;; Purpose: Similar to times-cps, but on a 0, it returns 0 immediately without applying k.
(define (times-cps-shortcut ls k)
  (letrec
    ((times-cps-shortcut
       (lambda (ls k)
         (cond
           [(empty? ls) (k 1)] ;; nothing left, empty product is 1 so give 1 to k continuation
           [(zero? (car ls)) 0] ;; 0 times anything = 0, throw every pending multiply away
           ;; if the head (car ls) is not 0, finish the rest (cdr ls) then mult by the (car ls)
           [else (times-cps-shortcut (cdr ls)
                                     (lambda (v) (k (* (car ls) v))))]))))
    (times-cps-shortcut ls k)))

(check-equal? (times-cps-shortcut '() (empty-k)) 1)
(check-equal? (times-cps-shortcut '(1 2 3 0 4 5) (empty-k)) 0)
(check-equal? (times-cps-shortcut '(1 2 3) (empty-k)) 6)

;; 6. Define and test a procedure cexpt-cps that is a CPSed version of
;; the following cexpt procedure.

(define cexpt
  (λ (m)
    (λ (n)
      (expt m n))))

;; Here are some examples of calls to cexpt:

#|

> ((cexpt 2) 3)
8
> ((cexpt ((cexpt 2) 3)) 2)
64

|#

;; Signature: number continuation -> any
;; Purpose: CPSed version of cexpt; passed k to the result, given n and a continuation,
;; delivers m^n to that continuation k.
(define (cexpt-cps m k)
  (k (lambda (n k^) ;; cexpt returns a function, so give it to k
       (k^ (expt m n))))) ;; inner function is cpsed, so answer is handed to k^

(check-equal? (cexpt-cps 2 (lambda (f) (f 3 (empty-k)))) 8)
(check-equal?
  (cexpt-cps 2
             (lambda (f)
               (f 3 (lambda (v)
                      (cexpt-cps v
                                 (lambda (g) (g 2 (empty-k))))))))
  64)

;; 7. Define and test a procedure count-syms*-cps that is a CPSed
;; version of the following count-syms* procedure:

(define count-syms*
  (λ (ls)
    (cond
      [(empty? ls) 0]
      [(cons? (car ls)) (+ (count-syms* (car ls)) (count-syms* (cdr ls)))]
      [(symbol? (car ls)) (add1 (count-syms* (cdr ls)))]
      [else (count-syms* (cdr ls))])))

;; Here are some example calls to count-syms*

#|

> (count-syms* '(a 1 b 2 c 3))
3
> (count-syms* '((a 1) (b 2) (c 3)))
3
> (count-syms* '(1 (b (3 (d (5 e) 7) (g)) 9) ((h))))
5

|#

;; Signature: listof any continuation -> number
;; Purpose: CPSed version of count-syms*; applies continuation k to the number of symbols in ls.
(define (count-syms*-cps ls k)
  (letrec
    ((count-syms*-cps
       (lambda (ls k)
         (cond
           [(empty? ls) (k 0)] ;; no syms in an empty list, 0
           ;; car is a ls: count the car (a), then the cdr of (d), then add them
           [(cons? (car ls)) (count-syms*-cps (car ls)
                                              (lambda (a)
                                                (count-syms*-cps (cdr ls)
                                                                 (lambda (b) (k (+ a b))))))]
           ;; car is sym; add1 once the cdr's count (v) is known
           [(symbol? (car ls)) (count-syms*-cps (cdr ls) (lambda (v) (k (add1 v))))]
           ;; if the car is something else, add nothing and pass the same k continuation along
           [else (count-syms*-cps (cdr ls) k)]))))
    (count-syms*-cps ls k)))

(check-equal? (count-syms*-cps '() (empty-k)) 0)
(check-equal? (count-syms*-cps '(a 1 b 2 c 3) (empty-k)) 3)
(check-equal? (count-syms*-cps '((a 1) (b 2) (c 3)) (empty-k)) 3)
(check-equal? (count-syms*-cps '(1 (b (3 (f (5 e) 7) h))) (empty-k)) 4)

;; 8. Define and test a procedure cons-cell-count-cps that is a CPSed
;; version of the following cons-cell-count procedure:

(define cons-cell-count
  (λ (ls)
    (cond
      [(cons? ls)
       (add1 (+ (cons-cell-count (car ls)) (cons-cell-count (cdr ls))))]
      [else 0])))


;; Signature: any continuation -> number
;; Purpose: CPSed cons-cell-count; applies k to the number of cons cells in ls.
(define (cons-cell-count-cps ls k)
  (letrec
    ((cons-cell-count-cps
       (lambda (ls k)
         (cond
           ;; a pair is one cell plus the cells in its car (a) and its cdr (d);
           ;; count car, then count cdr, then give (add1 (+ a d)) to k
           [(cons? ls)
            (cons-cell-count-cps (car ls)
                                 (lambda (a) (cons-cell-count-cps (cdr ls)
                                                                  (lambda (d) (k (add1 (+ a d)))))))]
           ;; not a pair, so give 0 to k
           [else (k 0)]))))
    (cons-cell-count-cps ls k)))

(check-equal? (cons-cell-count-cps '() (empty-k)) 0)
(check-equal? (cons-cell-count-cps 'a (empty-k)) 0)
(check-equal? (cons-cell-count-cps '(a b c) (empty-k)) 3)
(check-equal? (cons-cell-count-cps '((a b) c) (empty-k)) 4)

;; 9. Define and test a procedure ack-cps that is a CPSed version of
;; the following ack
;; procedure. (http://en.wikipedia.org/wiki/Ackermann_function).
;; Warning: if you run this program with m >= 4 and n >= 2, you'll be
;; in for a long wait.

(define ack
  (λ (m n)
    (cond
      [(zero? m) (add1 n)]
      [(zero? n) (ack (sub1 m) 1)]
      [else (ack (sub1 m)
                 (ack m (sub1 n)))])))

;; Signature: natnum natnum continuation -> natnum
;; Purpose: CPSed ack; applies k to ack value of m and n.
(define (ack-cps m n k)
  (letrec
    ((ack-cps
       (lambda (m n k)
         (cond
           [(zero? m) (k (add1 n))] ;; m = 0, so return n + 1 and give it to k
           ;; tail call, nothings pending, return the same k
           [(zero? n) (ack-cps (sub1 m) 1 k)]
           ;; m and n are not 0; (ack m (sub1 n)) runs and produces v and then makes the
           ;; outer call (ack (sub1 m) v) still delivering to k
           [else (ack-cps m (sub1 n)
                          (lambda (v) (ack-cps (sub1 m) v k)))]))))
    (ack-cps m n k)))

(check-equal? (ack-cps 0 0 (empty-k)) 1)
(check-equal? (ack-cps 1 1 (empty-k)) 3)
(check-equal? (ack-cps 2 3 (empty-k)) 9)
(check-equal? (ack-cps 3 2 (empty-k)) 29)


;; 10. Define and test a procedure fib-cps that is a CPSed version of
;; the following fib procedure:


(define fib
  (λ (n)
    ((λ (fib)
       (fib fib n))
     (λ (fib n)
       (cond
         [(< n 2) n]
         [else (+ (fib fib (sub1 n)) (fib fib (sub1 (sub1 n))))])))))


;; Signature: natnum continuation -> natnum
;; Purpose: CPSed fib; applies k to the nth fibonacci number.
(define (fib-cps n k)
  ((lambda (fib)
     (fib fib n k)) ;; start self-application, carrying the caller's k
   (lambda (fib n k)
     (cond
       [(< n 2) (k n)] ;; n is 0 or 1, so fib(n) = n; give it to k
       ;; do fib(n-1) first to get v1, then fib(n-2) to get v2, add them together and give it to k
       [else (fib fib (sub1 n)
                  (lambda (v1) (fib fib (sub1 (sub1 n))
                               (lambda (v2) (k (+ v1 v2))))))]))))

(check-equal? (fib-cps 0 (empty-k)) 0)
(check-equal? (fib-cps 1 (empty-k)) 1)
(check-equal? (fib-cps 5 (empty-k)) 5)
(check-equal? (fib-cps 7 (empty-k)) 13)

;; 11. Define and test a procedure unfold-cps that is a CPSed version
;; of the following unfold procedure:

(define unfold
  (λ (p f g seed)
    ((λ (h)
       ((h h) seed '()))
     (λ (h)
       (λ (seed ans)
         (if (p seed)
             ans
             ((h h) (g seed) (cons (f seed) ans))))))))

;; An example of its use is demonstrated below:

#|

> (unfold empty? car cdr '(a b c d e))
(e d c b a)

|#

;; When testing your unfold-cps, you should consider its arguments to
;; be serious, so include the following helper definitions when
;; testing your code.


(define empty?-cps
  (λ (ls k)
    (k (empty? ls))))
(define car-cps
  (λ (pr k)
    (k (car pr))))
(define cdr-cps
  (λ (pr k)
    (k (cdr pr))))

;; added more for testing
(define zero?-cps
  (lambda (n k) (k (zero? n))))
(define sub1-cps
  (lambda (n k) (k (sub1 n))))
(define id-cps
  (lambda (x k) (k x)))
  

#|

> (unfold-cps empty?-cps car-cps cdr-cps '(a b c d e) (empty-k))
(e d c b a)

|#

;; Signature: (any continuation -> bool) (any continuation -> any) (any continuation -> any) any continuation -> list
;; Purpose: CPSed unfold; applies k to the list built by applying f to each seed and g to get the next, until p says stop.
(define (unfold-cps p f g seed k)
  ((lambda (h)
     ((h h) seed '() k)) ;; start with an empty answer list and the caller's k
   (lambda (h)
     (lambda (seed ans k)
       (p seed ;; p is CPSed, so its boolean arrives in a continuation
          (lambda (done?)
            (if done?
                (k ans) ;; p says stop, so the accumulated list is the answer; give it to k
                ;; otherwise compute the next seed with g, then the new element with f,
                ;; then loop with the same k (tail call, nothing pending)
                (g seed
                   (lambda (next)
                     (f seed
                        (lambda (fv)
                          ((h h) next (cons fv ans) k))))))))))))

(check-equal? (unfold-cps empty?-cps car-cps cdr-cps '() (empty-k)) '())
(check-equal? (unfold-cps empty?-cps car-cps cdr-cps '(a b c d e) (empty-k)) '(e d c b a))
(check-equal? (unfold-cps zero?-cps id-cps sub1-cps 3 (empty-k)) '(1 2 3))

;; 12. Define and test a procedure pascal-cps that is a CPSed version
;; of the following pascal procedure:

(define pascal
  (λ (n)
    (let ((pascal
            (λ (pascal)
              (λ (m a)
                (cond
                  [(> m n) '()]
                  [else (let ((a (+ a m)))
                          (cons a ((pascal pascal) (add1 m) a)))])))))
      ((pascal pascal) 1 0))))


;; Signature: natnum continuation -> listof natnums
;; Purpose: CPSed pascal; applies k to the list of the first n running sums 1, 1+2, 1+2+3, ...
(define (pascal-cps n k)
  (let ((pascal
         (lambda (pascal)
           (lambda (m a k)
             (cond
               [(> m n) (k '())] ;; counted past n, so no more numbers; give '() to k
               ;; otherwise bump the running total a by m, then build the rest of the list;
               ;; the pending (cons a ...) goes in the continuation, and a is the new a from the let
               [else (let ((a (+ a m)))
                       ((pascal pascal) (add1 m) a
                                        (lambda (v) (k (cons a v)))))])))))
    ((pascal pascal) 1 0 k))) ;; start at m = 1 with running total 0, carrying the caller's k

(check-equal? (pascal-cps 0 (empty-k)) '())
(check-equal? (pascal-cps 1 (empty-k)) '(1))
(check-equal? (pascal-cps 3 (empty-k)) '(1 3 6))
(check-equal? (pascal-cps 5 (empty-k)) '(1 3 6 10 15))

;; 13. Here is the definition of unify that uses the version of walk
;; given in question 3. Define and test a procedure unify-cps that
;; uses your walk-cps from question 3.


(define unify
  (λ (v w s)
    (cond
      [(eqv? v w) s]
      [(symbol? v) (cons `(,v . ,w) s)]
      [(symbol? w) (cons `(,w . ,v) s)]
      [(and (cons? v) (cons? w))
       (let ((s (unify (walk (car v) s) (walk (car w) s) s)))
         (cond
           [s (unify (walk (cdr v) s) (walk (cdr w) s) s)]
           [else #f]))]
      [(equal? v w) s]
      [else #f])))

;; Here are some example calls to unify:

#|

> (unify 'x 5 '())
((x . 5))
> (unify '(x y) '(5 6) '())
((y . 6) (x . 5))
> (unify '(x x) '(5 6) '())
#f
> (unify '(x y z) '(5 x y) '())
((z . 5) (y . 5) (x . 5))

|#


;; Signature: any any (listof pair) continuation -> (listof pair) or #f
;; Purpose: CPSed unify; applies k to the substitution that makes v and w equal, or #f if there is none.
(define (unify-cps v w s k)
  (letrec
    ((unify-cps
        (lambda (v w s k)
          (cond
            [(eqv? v w) (k s)] ;; already identical, so no new bindings; give s to k
            [(symbol? v) (k (cons `(,v . ,w) s))] ;; v is a variable, bind it to w; simple, so give it to k
            [(symbol? w) (k (cons `(,w . ,v) s))] ;; w is a variable, bind it to v
            ;; both are pairs: walk the cars, unify them (result s^), then walk the cdrs with s^ and unify those
            [(and (cons? v) (cons? w))
             (walk-cps (car v) s
                       (lambda (av)
                         (walk-cps (car w) s
                                   (lambda (aw)
                                     (unify-cps av aw s
                                                (lambda (s^)
                                                  (cond
                                                    [s^ (walk-cps (cdr v) s^ ;; cars unified, so continue with the cdrs
                                                                  (lambda (dv)
                                                                    (walk-cps (cdr w) s^
                                                                              (lambda (dw)
                                                                                (unify-cps dv dw s^ k)))))] ;; tail call, same k
                                                    [else (k #f)])))))))] ;; cars failed, so give #f to k and stop
            [(equal? v w) (k s)] ;; equal non-symbols, so nothing to bind
            [else (k #f)])))) ;; mismatch, so give #f to k
    (unify-cps v w s k)))

(check-equal? (unify-cps 'x 5 '() (empty-k)) '((x . 5)))
(check-equal? (unify-cps '(x y) '(5 6) '() (empty-k)) '((y . 6) (x . 5)))
(check-equal? (unify-cps '(x x) '(5 6) '() (empty-k)) #f)
(check-equal? (unify-cps '(x y z) '(5 x y) '() (empty-k)) '((z . 5) (y . 5) (x . 5)))

;; 14. Define and test a procedure M-cps that is a CPSed version of M,
;; which is a curried version of map. Assume for the CPSed version
;; that any f passed in will also be CPSed.

(define M
  (λ (f)
    (λ (ls)
      (cond
        ((empty? ls) '())
        (else (cons (f (car ls)) ((M f) (cdr ls))))))))

;; Signature: (any continuation -> any) continuation -> any
;; Purpose: CPSed M; applies k to a CPSed procedure that, given a list and its own continuation, maps the CPSed f over the list.
(define (M-cps f k)
  (letrec
    ((M-cps
        (lambda (f k)
          (k (lambda (ls k^) ;; M returns a function, so we "return" it by giving it to k
               (cond
                 [(empty? ls) (k^ '())] ;; nothing to map; give '() to k^ (not k)
                 ;; call f on the car (v), then get the mapper for the rest (m), run it on the cdr (d), then cons v onto d
                 [else (f (car ls)
                          (lambda (v)
                            (M-cps f
                                   (lambda (m)
                                     (m (cdr ls)
                                        (lambda (d) (k^ (cons v d))))))))]))))))
    (M-cps f k)))

(define add1-cps (lambda (n k) (k (add1 n)))) ;; CPSed f for the tests

(check-equal? (M-cps add1-cps (λ (m) (m '() (empty-k)))) '())
(check-equal? (M-cps add1-cps (λ (m) (m '(1 2 3) (empty-k)))) '(2 3 4))

;; 15. Consider the corresponding call to M, called use-of-M. Using
;; your CPSed M-cps, re-write use-of-M to call M-cps, and make all the
;; appropriate changes (including CPSing the argument). Name it
;; use-of-M-cps. Treat this like an expression, so you should have one
;; and only one use of empty k in your answer. Like use-of-M, your
;; answer will not be a λ-expression.

(define use-of-M
  ((M (λ (n) (add1 n))) '(1 2 3 4 5)))

;; rewritten use-of-m using continuation
(define use-of-M-cps
  (M-cps (lambda (n k) (k (add1 n))) ;; the argument is CPSed now: it takes k and gives the answer to it
         (lambda (m) (m '(1 2 3 4 5) (empty-k))))) ;; k receives M's mapper, which we apply to the list; the only empty-k

(check-equal? use-of-M-cps '(2 3 4 5 6))

;; 16. CPS the following program, and call it strange-cps:

(define strange
  (λ (x)
    ((λ (g) (λ (x) (g g)))
     (λ (g) (λ (x) (g g))))))


;; Signature: any continuation -> any
;; Purpose: CPSed strange; applies k to a CPSed procedure that, whatever its argument, delivers another such procedure to its continuation.
(define (strange-cps x k)
  ((lambda (g k)
     (k (lambda (x k^) (g g k^)))) ;; "return" the inner lambda by giving it to k; its body is a call to g, so it passes k^ along
   (lambda (g k)
     (k (lambda (x k^) (g g k^))))
   k)) ;; the original application becomes a CPSed call: the same two lambdas, plus the caller's k

(check-equal? (strange-cps 5 (λ (f) (procedure? f))) #t)
(check-equal? (strange-cps 5 (λ (f) (f 6 (λ (g) (procedure? g))))) #t)

;; 17. Consider the following use of strange, called
;; use-of-strange. Using your CPSed strange, re-write use-of-strange
;; to call strange-cps, and make all the appropriate changes. Name it
;; use-of-strange-cps.

(define use-of-strange
  (let ([strange^ (((strange 5) 6) 7)])
    (((strange^ 8) 9) 10)))

;; Signature: not a function; a value
;; Purpose: use-of-strange rewritten with strange-cps; evaluates to a procedure.
(define use-of-strange-cps
  (strange-cps 5
    (lambda (f1) ;; (strange 5)
      (f1 6
          (lambda (f2) ;; ((strange 5) 6)
            (f2 7
                (lambda (strange^) ;; the let binding of strange^
                  (strange^ 8
                            (lambda (f3) ;; (strange^ 8)
                              (f3 9
                                  (lambda (f4) ;; ((strange^ 8) 9)
                                    (f4 10 (empty-k))))))))))))) ;; (((strange^ 8) 9) 10); the only empty-k

(check-equal? (procedure? use-of-strange-cps) #t)

;; 18. CPS the following program, and call it why-cps:

(define why
  (λ (f)
    ((λ (g)
       (f (λ (x) ((g g) x))))
     (λ (g)
       (f (λ (x) ((g g) x)))))))

;; To get you started, you may find it useful to see the
;; following-call to why.

#|

> (define almost-length
    (λ (f)
      (λ (ls)
        (if (empty? ls)
            0
            (add1 (f (cdr ls)))))))
> ((why almost-length) '(a b c d e))
5

|#

(define (why-cps f k)
  ((lambda (g k) ;; was (λ (g) ...), now takes the caller's k
     (f (lambda (x k^) ;; the wrapper (λ (x) ((g g) x)) now takes its own continuation k^
          (g g (lambda (h) (h x k^)))) ;; (g g) is a call, so its result h is applied to x, delivering to k^
        k)) ;; f is CPSed, so it gets k and delivers the final function to it
   (lambda (g k)
     (f (lambda (x k^)
          (g g (lambda (h) (h x k^))))
        k))
   k)) ;; the original application becomes a CPSed call with the caller's k

;; CPSed version of almost-length for tests
(define almost-length-cps
  (lambda (f k)
    (k (lambda (ls k^)
         (if (empty? ls)
             (k^ 0)
             (f (cdr ls) (lambda (v) (k^ (add1 v)))))))))

(check-equal? (why-cps almost-length-cps (lambda (len) (len '() (empty-k)))) 0)
(check-equal? (why-cps almost-length-cps (lambda (len) (len '(a b c d e) (empty-k)))) 5)

#| Optional enrichment

Problem 19 is optional. Gradescope does not require or test it. It is
important preparation for reasoning about repeated CPS transformations,
and you are strongly encouraged to attempt it. It deliberately has no
starter stub.

|#

#| Just Dessert |#

;; 19. CPS why-cps, and call it why-cps-cps.