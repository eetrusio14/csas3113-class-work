#lang racket

(require rackunit)

;; Gradescope loads this file as a module and expects each required name
;; in the provide form below to exist. Replace each "not implemented"
;; expression with your solution, but keep the filename, names, and
;; argument lists unchanged.

(provide countdown
         insertR
         remv
         list-index-ofv
         filter
         zip
         map
         append
         reverse
         fact
         fib
         binary->natural
         minus
         div
         append-map
         set-difference
         cons-every)


#| Recursion and Higher-order Functional Abstraction |#

;; Recursion is the root of computation since it trades description
;; for time.

;; -- Alan Perlis

#| Assignment Guidelines |#


;; In addition to the standard Assignment Guidelines
;; (https://hemann.pl/26FA-CS3113/hw/)

;; You should write your solutions without creating explict help
;; functions. You may, however re-use your solutions to prior
;; problems.

#|

0. Read the course syllabus and assignment guidelines carefully.

|#
#|

 1. Define and test a procedure countdown that takes a natural number
and returns a list of the natural numbers less than or equal to that
number, in descending order. Our natural numbers begin at zero.

|#

;; countdown: natnum -> listof natnums
;; Purpose: Builds a list of natnums from n to 0, desc.
(define (countdown n)
  (cond
  [(zero? n) '(0)] ;; if 0, return '(0)
  ;; cons n onto recursive call of n - 1
  [else (cons n (countdown (sub1 n)))]))

(check-equal? (countdown 0) '(0))
(check-equal? (countdown 3) '(3 2 1 0))
(check-equal? (countdown 5) '(5 4 3 2 1 0))


#|

2. Define and test a procedure insertR that takes two symbols and a
list and returns a new list with the second symbol inserted after each
occurrence of the first symbol. For this and later questions, these
functions need only hold over eqv?-comparable structures.

|#

;; insertR: symbol symbol listof symbols -> listof symbols
;; Purpose: Inserts new symbol right after every occurence of old symbol in list.
(define (insertR old new ls)
  (cond
    [(empty? ls) '()] ;; if ls is '(), return '()
    ;; first element is old, keep old and cons new right after then recur on rest of ls
    [(eqv? (car ls) old) (cons old (cons new (insertR old new (cdr ls))))]
    ;; first element isn't old, keep old and recur on rest of ls
    [else (cons (car ls) (insertR old new (cdr ls)))]))

(check-equal? (insertR 'x 'y '()) '())
(check-equal? (insertR 'x 'y '(a b c)) '(a b c))
(check-equal? (insertR 'x 'y '(x b x)) '(x y b x y))
(check-equal? (insertR 'd 'e '(a b c d f g d h)) '(a b c d e f g d e h))


#|

3. Define and test a procedure remv that takes an atom and a list of
atoms and returns a list similar except its missing the first
occurrence (if any) of the input atom.

|#

;; remv: symbol listof symbols -> listof symbols
;; Purpose: Removes the first occurence of x from ls, if x exists in ls.
(define (remv x ls)
  (cond
    [(empty? ls) '()] ;; if ls is '(), return '()
    ;; first is x, return rest of ls
    [(eqv? (car ls) x) (cdr ls)]
    ;; first isn't x, keep it, and recur on rest of ls
    [else (cons (car ls) (remv x (cdr ls)))]))

(check-equal? (remv 'x '()) '())
(check-equal? (remv 'x '(a b c)) '(a b c))
(check-equal? (remv 'b '(a b c b d)) '(a c b d))
(check-equal? (remv 'a '(a b a)) '(b a))
(check-equal? (remv 'z '(x y z)) '(x y))


#|

4. Define and test a procedure list-index-ofv that takes an element
and a list containing that element and returns the (base 0) index of
that element in the list. List without that element are bad data.

|#

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

#|

5. Define and test a procedure filter that takes a predicate and a
list and returns a new list containing the elements that satisfy the
predicate. A predicate is a procedure that takes a single argument and
returns either #t or #f. The number? predicate, for example, returns
#t if its argument is a number and #f otherwise. The argument
satisfies the predicate, then, if the predicate returns #t for that
argument.

|#

;; filter: pred listof any -> listof any
;; Purpose: Keeps only the elements of ls that satisfy the given pred.
(define (filter pred ls)
  (cond
  [(empty? ls) '()] ;; if ls is '(), nothing to satisfy pred
  ;; checks if the first element of the ls satisfies the pred, if yes, then keep it
  [(pred (car ls)) (cons (car ls) (filter pred (cdr ls)))] 
  ;; first element fails pred, drop it, recur on rest of ls
  [else (filter pred (cdr ls))]))

(check-equal? (filter number? '(1 2 3 a b c)) '(1 2 3))
(check-equal? (filter even? '(1 2 3 5 8 13 21)) '(2 8))
(check-equal? (filter symbol? '(a b c d e f)) '(a b c d e f))
(check-equal? (filter positive? '(-1 0 1 -7 25)) '(1 25))
(check-equal? (filter even? '()) '()) ;; base case: nothing to filter in an empty list


#|

6. Define and test a procedure zip that takes two lists and forms a
new list, each element of which is a pair formed by combining the
corresponding elements of the two input lists. If the two lists are of
uneven length, zip will drop the tail of the longer one.

|#

;; zip: listof any listof any -> listof any
;; Purpose: Pairs corresponding elements of xs and ys, not exceeding the length of the shorter list.
(define (zip xs ys)
  (cond
    [(or (empty? xs) (empty? ys)) '()] ;; either list out of elements / one or both are empty, return '()
    ;; pair up the two first elements and recur on both rests
    [else (cons (cons (car xs) (car ys)) (zip (cdr xs) (cdr ys)))]))

(check-equal? (zip '(a c e) '(b d f)) '((a . b) (c . d) (e . f)))
(check-equal? (zip '(1 2) '(3 4 5)) '((1 . 3) (2 . 4)))
(check-equal? (zip '(a b) '(c d e f g h i)) '((a . c) (b . d)))
(check-equal? (zip '() '(a b c)) '()) ;; base case: xs empty
(check-equal? (zip '(a b c) '()) '()) ;; base case: ys empty


#|

7. Define and test a procedure map that takes a procedure p of one
argument and a list ls and returns a new list containing the results
of applying p to the elements of ls. Do not use Racket's built-in map
in your definition.

|#

;; map: procedure listof any -> listof any
;; Purpose: Applies p to every element of ls and creates a new list as result.
(define (map p ls)
  (cond
    [(empty? ls) '()] ;; if ls is '(), nothing to apply p to
    ;; apply p to first element and recur on rest
    [else (cons (p (car ls)) (map p (cdr ls)))]))

(check-equal? (map add1 '()) '())
(check-equal? (map add1 '(1 2 3 4)) '(2 3 4 5))
(check-equal? (map symbol->string '(x y z)) '("x" "y" "z"))


#|

8. Define and test a procedure append that takes a list l and any
racket datum (any old racket, be it a list or not) d, and returns a
new racket datum with the elements of l prepended. This should work
for any racket datum d, but testing against the data we have talked
about in class is sufficient.

|#

;; append: listof any datum -> listof datum
;; Purpose: Appends the elements of ls onto the front of datum.
(define (append ls datum)
  (cond
    [(empty? ls) datum] ;; if ls is '(), just return datum
    ;; keep the first element of ls and recur on rest with datum appended to the end
    [else (cons (car ls) (append (cdr ls) datum))]))

(check-equal? (append '() '(a b c)) '(a b c))
(check-equal? (append '(a b) '(c d)) '(a b c d))
(check-equal? (append '(a) 'b) '(a . b))
(check-equal? (append '(a b c) 3113) '(a b c . 3113))


#|

9. Define and test a procedure reverse that takes a list l and returns
list with the elements of l in the opposite order

|#

;; reverse: listof any -> listof any
;; Purpose: Returns the elements of ls in reverse order.
(define (reverse ls)
  (cond
    [(empty? ls) '()] ;; '() reversed is still '()
    ;; reverse the rest of ls, then append first on the end
    [else (append (reverse (cdr ls)) (list (car ls)))]))

(check-equal? (reverse '()) '())
(check-equal? (reverse '(1 2 3)) '(3 2 1))
(check-equal? (reverse '(a b c d e f)) '(f e d c b a))




#|

10. Define and test a procedure fact that takes a natural number and
computes the factorial of that number. The factorial of a number is
computed by multiplying it by the factorial of its predecessor. The
factorial of 0 is defined to be 1 (https://oeis.org/A000142).

|#

;; fact: natnum -> natnum
;; Purpose: Computes n factorial by multiple n by the factorial n - 1, terminating when n = 0.
(define (fact n)
  (cond
    [(zero? n) 1] ;; if n = 0, return 1
    ;; multiply n by the result of the recursion of the factorial n - 1
    [else (* n (fact (sub1 n)))]))

(check-equal? (fact 0) 1)
(check-equal? (fact 3) 6)
(check-equal? (fact 5) 120) 

#|

11. Define and test a procedure fib that takes a natural number n as
input and computes the nth number, starting from zero, in the
Fibonacci sequence (0, 1, 1, 2, 3, 5, 8, 13, 21, ...). Each number in
the sequence is computed by adding the two previous numbers.

|#

;; fib: natnum -> natnum
;; Purpose: Computes the nth fibonacci number by summing the preceding two numbers.
(define (fib n)
  (cond
    [(zero? n) 0] ;; 0 is 0
    [(= n 1) 1] ;; first fibonacci number is 1
    ;; add the nth - 1 fib number and nth - 2 fib number together to get the nth value
    [else (+ (fib (sub1 n)) (fib (- n 2)))]))

(check-equal? (fib 0) 0)
(check-equal? (fib 1) 1) ;; base case: the n = 1 branch, never hit by the other tests
(check-equal? (fib 3) 2)
(check-equal? (fib 8) 21)


#|

12. Define a function cons-every that takes an element x and a list l
and returns a list with x consed to the front of each element of l.

|#

;; cons-every: any listof list -> listof list
;; Purpose: Conses x onto the front of every list in ls.
(define (cons-every x ls)
  (match ls
    ['() '()] ;; if the ls of lists is '(), return '()
    [`(,first . ,rest)
     ;; Cons x onto the first list, and cons that onto the recursively processed tail
     (cons (cons x first) (cons-every x rest))]))

(check-equal? (cons-every 'a '()) '())
(check-equal? (cons-every 'a '(b c d a)) '(a b a c a d a a))
(check-equal? (cons-every 'x '(x y z)) '(x x x y x z))

#|

13. Define and test a procedure binary->natural that takes a flat list
of 0s and 1s representing an unsigned binary number in reverse bit
order and returns that number. For example:

'()      ;; 0
'(1)     ;; 1
'(0 1)   ;; 2
'(1 1)   ;; 3
'(0 0 1) ;; 4
'(1 0 1) ;; 5
'(0 1 1) ;; 6

|#

;; binary->natural: listof symbols -> natnum
;; Purpose: Reads binary bits and accumulates the natnum they represent.
;; Read left to right for bits
(define (binary->natural bits)
  (cond
    [(empty? bits) 0] ;; no bits, 0
    ;; first bit is 1, rest are scaled up by 2 per index to account for the place shift (ex. 2^0 2^1 2^2 ... 2^n for "on" bits)
    [else (+ (car bits) (* 2 (binary->natural (cdr bits))))]))

(check-equal? (binary->natural '()) 0)
(check-equal? (binary->natural '(1)) 1) ;; smallest non-empty case, straight from the problem's own examples
(check-equal? (binary->natural '(0 1)) 2)
(check-equal? (binary->natural '(1 1 1)) 7)



#|

14. Define subtraction using natural recursion. Your subtraction
function, minus, need only take nonnegative inputs where the result
will be nonnegative.

|#

;; minus: natnum natnum -> natnum
;; Purpose: Subtracts m from n by counting both downward towards zero.
(define (minus n m)
  (cond
    [(zero? m) n] ;; nothing left to subtract
    ;; m > n, result would be negative thus breaking the original contract
    [(> m n) (error "minus: Negative result")]
    ;; sub1 from both n and m and keep recurring until m = 0
    [else (minus (sub1 n) (sub1 m))]))

(check-equal? (minus 8 0) 8)
(check-equal? (minus 3 2) 1)
(check-equal? (minus 35 25) 10)



#|

15. Define division using natural recursion. Your division function,
div, need only work when the second number evenly divides the
first (that is, for the divisible abelian group that's a subgroup of
Nat). Divisions by zero is of course bad data.

|#

;; div: natnum natnum -> natnum
;; Purpose: Divides n by m by repeatedly subtracting m from n and counting how many subtractions it takes to reach zero.
(define (div n m)
  (cond
    [(zero? m) (error "div: divion by zero")] ;; bad data
    [(zero? n) 0] ;; nothing left to divide
    ;; subtract m once, add1 to the running count and keep recurring on what's left
    [else (add1 (div (minus n m) m))]))

(check-equal? (div 0 5) 0) ;; base case: dividend already 0, never hit by the other tests
(check-equal? (div 6 2) 3)
(check-equal? (div 4 2) 2)
(check-equal? (div 144 12) 12)


#|

16. Define a function append-map that, similar to map, takes both a
procedure p of one argument a list of inputs ls and applies p to each
of the elements of ls. Here, though, we mandate that the result of p
on each element of ls is a list, and we append together the
intermediate results. Do not use Racket's built-in append-map in your
definition.

|#


;; append-map: procedure listof any -> listof any
;; Purpose: Applies a list-returning procedure to a list of elements and appends.
(define (append-map p ls)
  (match ls
    ['() '()] ;; if ls is '(), return '()
    ;; if list is not empty, apply p to first then append it to the recurred tail
    [`(,first . ,rest) 
     (append (p first) (append-map p rest))]))

(check-equal? (append-map (lambda (x) (list x x)) '(1 2 3)) '(1 1 2 2 3 3))
(check-equal? (append-map (lambda (x) '()) '(1 2 3)) '())
(check-equal? (append-map (lambda (x) (list x)) '()) '())


#|

17. Define a function set-difference that takes two flat sets (lists
with no duplicate elements) s1 and s2 and returns a list containing
all the elements in s1 that are not in s2.

|#

;; set-difference: set set -> set
;; Purpose: Takes two sets of elements and returns a list of elements in s1 that are not in s2.
(define (set-difference s1 s2)
  (match s1
    ['() '()] ;; if s1 is '(), then return '()
    ;; if the head is found in s2, skip it, and recur on the rest (tail)
    [`(,first . ,rest) #:when (memv first s2) (set-difference rest s2)]
    ;; if the head is not in s2, keep it (cons) and recur on the rest (tail)
    [`(,first . ,rest) (cons first (set-difference rest s2))]))

(check-equal? (set-difference '() '(1 2 3)) '())
(check-equal? (set-difference '(a b c d) '(b c d)) '(a))
(check-equal? (set-difference '(1 2 3 4 5 1) '(1 2 3)) '(4 5))
(check-equal? (set-difference '(a 1 7 f r 14) '(14 r a)) '(1 7 f))