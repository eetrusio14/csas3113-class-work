#lang racket

;; Gradescope loads this file as a module and expects each required name
;; in the provide form below to exist. Replace each "not implemented"
;; expression with your solution, but keep the filename, names, and
;; argument lists unchanged.

(provide ack-reg-driver
         depth-reg-driver
         fact-reg-driver
         pascal-reg-driver)

#| Assignment 8: Registerization |#

;; A trampoline is strong enough to catch you before you hit the
;; ground, but not so cushy that you can live on it forever
;;
;; Thomas Friedman

#| ===== Assignment Guidelines ===== |#

;; In addition to the standard Assignment Guidelines

;; As you do the assignment, consider the following four procedures
;; and keep the following points in mind:

;; For each of the four initial programs, you should write a
;; registerized version of the original.

;; All definitions must be //representation-independent with respect
;; to continuations//. You must use a //data-structural//
;; representation of continuations.

;; You should probably consider building a separate apply-k for each
;; of the below functions, each with its own continuations. We have
;; (prematurely) made the empty-ks representation independent for you.

;; You should also construct "driver" functions, to be invoked as the
;; following examples demonstrate. We might have named these "main" in
;; class. Each of these driver programs will take the arguments taken
;; by the original, pre-CPSed program. The job of the driver will be
;; to populate the registers with initial values and call the
;; registerized program.

;; Make sure to name your drivers exactly as we describe; this is our
;; interface for testing your procedures.

;; You **should not** trampoline these procedures. Once again, you
;; should not trampoline your registerized programs.

;; Same 3 steps for every function: (1) CPS, (2) turn each lambda
;; continuation into a struct, (3) swap args for registers.
;; Watch out: every set! right side uses the old register values, so build
;; anything that needs a register before you overwrite it.
;; Each function gets its own prefixed registers so they don't clash.

;; ack

(define (ack-empty-k)
  (λ (v)
    v))

;; Bring forward your corrected ack-cps from Assignment 6. The starter
;; remains loadable before you paste it.

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

;; the lambda in the else case uses m and k, so those are the fields
;; remembers only m and k (for outer call)
(struct ack-k (m k))

;; params m, n, k plus a value for apply-k = 4 registers
(define ack-m-reg #f)
(define ack-n-reg #f)
(define ack-k-reg #f)
(define ack-v-reg #f)

;; ack-k-reg = continuation to receive the value
;; ack-v-reg = the value

(define (ack-apply-k-reg)
  (match ack-k-reg
    ;; old body: (ack-cps (sub1 m) v k). m and k come from the struct,
    ;; so these set!s can go in any order
    [(ack-k m k)
     (set! ack-m-reg (sub1 m))
     (set! ack-n-reg ack-v-reg) ;; inner result is the new n
     (set! ack-k-reg k) ;; pop the frame
     (ack-reg)]
    ;; not a struct, so it's the provided empty-k; just call it
    [else (ack-k-reg ack-v-reg)])) ;; provided contains empty-k

;; ack-m/n-reg = arguments, ack-k-reg = continuation
;; same 3 cases as ack-cps
(define (ack-reg)
  (cond
    [(zero? ack-m-reg)
     (set! ack-v-reg (add1 ack-n-reg))
     (ack-apply-k-reg)]
    [(zero? ack-n-reg)
     (set! ack-m-reg (sub1 ack-m-reg))
     (set! ack-n-reg 1)
     (ack-reg)]
    ;; frame needs old m and k, so build it before changing n
    ;; builds a continuation from old m and k, to then change n
    [else
     (set! ack-k-reg (ack-k ack-m-reg ack-k-reg))
     (set! ack-n-reg (sub1 ack-n-reg))
     (ack-reg)]))

;; ack-reg-driver: natnum natnum -> natnum
;; Purpose: Compute (ack m n) with a register machine.
;; driver loads the registers, then starts the machine
(define (ack-reg-driver m n)
  (set! ack-m-reg m)
  (set! ack-n-reg n)
  (set! ack-k-reg (ack-empty-k))
  (ack-reg))

;; depth

(define (depth-empty-k)
  (λ (v)
    v))

(define depth-cps
  (λ (ls k)
    (cond
      [(null? ls) (k 1)]
      [(pair? (car ls))
       (depth-cps (car ls)
                  (λ (l)
                    (depth-cps (cdr ls)
                               (λ (r)
                                 (let ((l (add1 l)))
                                   (if (< l r) (k r) (k l)))))))]
      [else (depth-cps (cdr ls) k)])))

;; two nested lambdas = two structs
;; inner uses l and k, outer uses ls and k
;; outer: waiting for the depth l of (car ls), then process (cdr ls)
;; inner: waiting for the depth r of (cdr ls)
(struct depth-outer-k (ls k))
(struct depth-inner-k (l k))

;; ls, k, plus a value = 3 registers
(define depth-ls-reg #f)
(define depth-k-reg #f)
(define depth-v-reg #f)

;; depth-k-reg = continuation, depth-v-reg = value
(define (depth-apply-k-reg)
  (match depth-k-reg
    ;; v-reg is l here. Go do the cdr, remembering l in an inner frame
    [(depth-outer-k ls k)
     (set! depth-ls-reg (cdr ls))
     (set! depth-k-reg (depth-inner-k depth-v-reg k))
     (depth-reg)]
    ;; v-reg is r here. Keep the bigger of (add1 l) and r
    [(depth-inner-k l k)
     (let ([l (add1 l)])
       (set! depth-v-reg (if (< l depth-v-reg) depth-v-reg l))
       (set! depth-k-reg k)
       (depth-apply-k-reg))]
    ;; provided empty-k
    [else (depth-k-reg depth-v-reg)]))

;; depth-ls-reg = list, depth-k-reg = continuation
(define (depth-reg)
  (cond
    ;; empty list has depth 1
    [(null? depth-ls-reg)
     (set! depth-v-reg 1)
     (depth-apply-k-reg)]
    ;; car is a list: save the old ls in a frame first, then go into the car
    ;; builds the continuation k from the old ls and k, then go deeper
    [(pair? (car depth-ls-reg))
     (set! depth-k-reg (depth-outer-k depth-ls-reg depth-k-reg))
     (set! depth-ls-reg (car depth-ls-reg))
     (depth-reg)]
    ;; car is an atom, skip it (cdr, not car!)
    [else
     (set! depth-ls-reg (cdr depth-ls-reg))
     (depth-reg)]))

;; depth-reg-driver: listof any -> natnum
;; Purpose: Computes the depth of the list with a register machine.
(define (depth-reg-driver ls)
  (set! depth-ls-reg ls)
  (set! depth-k-reg (depth-empty-k))
  (depth-reg))

;; fact

(define (fact-empty-k)
  (λ (v)
    v))

;; the (fact-cps fact-cps ...) self-application isn't needed once
;; fact-reg has a name
(define fact-cps
  (λ (n k)
    ((λ (fact-cps k)
       (fact-cps fact-cps n k))
     (λ (fact-cps n k)
       (cond
         [(zero? n) (k 1)]
         [else (fact-cps fact-cps (sub1 n)
                         (λ (v)
                           (k (* n v))))]))
     k)))

;; lambda uses n and k
(struct fact-k (n k))

(define fact-n-reg #f)
(define fact-k-reg #f)
(define fact-v-reg #f)

;; fact-k-reg = continuation, fact-v-reg = value
(define (fact-apply-k-reg)
  (match fact-k-reg
    ;; old body: (k (* n v))
    [(fact-k n k)
     (set! fact-v-reg (* n fact-v-reg))
     (set! fact-k-reg k)
     (fact-apply-k-reg)]
    ;; provided empty-k
    [else (fact-k-reg fact-v-reg)]))

;; fact-n-reg = input, fact-k-reg = continuation
(define (fact-reg)
  (cond
    ;; 0! = 1
    [(zero? fact-n-reg)
     (set! fact-v-reg 1)
     (fact-apply-k-reg)]
    ;; save n in the frame before decrementing, or we'd save n-1
    [else
     (set! fact-k-reg (fact-k fact-n-reg fact-k-reg)) ;; before n is changed
     (set! fact-n-reg (sub1 fact-n-reg))
     (fact-reg)]))

;; fact-reg-driver: natnum -> natnum
;; Purpose: Compute n! with a register machine.
(define (fact-reg-driver n)
  (set! fact-n-reg n)
  (set! fact-k-reg (fact-empty-k))
  (fact-reg))

;; pascal

(define (pascal-empty-k)
  (λ (v)
    v))

;; Bring forward your corrected pascal-cps from Assignment 6. The
;; starter remains loadable before you paste it.

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

;; lambda uses a and k (a is the new a from the let)
(struct pascal-k (a k))

;; n is never changed since it was a free variable in the closure
;; no closure anymore, so n gets its own register
(define pascal-n-reg #f)
(define pascal-m-reg #f)
(define pascal-a-reg #f)
(define pascal-k-reg #f)
(define pascal-v-reg #f)

;; pascal-k-reg = continuation, pascal-v-reg = value
(define (pascal-apply-k-reg)
  (match pascal-k-reg
    ;; old body: (k (cons a v))
    [(pascal-k a k)
     (set! pascal-v-reg (cons a pascal-v-reg))
     (set! pascal-k-reg k)
     (pascal-apply-k-reg)]
    ;; provided empty-k
    [else (pascal-k-reg pascal-v-reg)]))

;; pascal-n-reg is bound
;; pascal-m-reg and pascal-a-reg = current m and running total
;; pascal-k-reg = continuation
(define (pascal-reg)
  (cond
    ;; past n, so the rest of the list is empty
    [(> pascal-m-reg pascal-n-reg)
     (set! pascal-v-reg '())
     (pascal-apply-k-reg)]
    ;; order matters: a needs old m, frame needs new a, m moves last
    [else
     (set! pascal-a-reg (+ pascal-a-reg pascal-m-reg)) ;; new a, using old m
     (set! pascal-k-reg (pascal-k pascal-a-reg pascal-k-reg)) ;; new a using old k
     (set! pascal-m-reg (add1 pascal-m-reg)) ;; most recent m
     (pascal-reg)]))

;; pascal-reg-driver: natnum -> listof natnum
;; Purpose: Compute the first n running sums 1, 1+2, 1+2+3, ... with a register machine.
(define (pascal-reg-driver n)
  (set! pascal-n-reg n)
  (set! pascal-m-reg 1)
  (set! pascal-a-reg 0)
  (set! pascal-k-reg (pascal-empty-k))
  (pascal-reg))




;; Here are examples of how to call these procedures:

;; (check-true* equal?
;;   [(ack-cps 2 2 (ack-empty-k)) 7]
;;   [(depth-cps '(1 (2 (3 (4)))) (depth-empty-k)) 4]
;;   [(fact-cps 5 (fact-empty-k)) 120]
;;   [(pascal-cps 10 (pascal-empty-k)) '(1 3 6 10 15 21 28 36 45 55)])

(module+ test
  (require rackunit)

  (define-syntax check-true*
    (syntax-rules ()
      [(_ pred (actual expected) ...)
       (begin (check-true (pred actual expected)) ...)]))

  (check-true* equal?
    [(ack-reg-driver 0 1) 2]
    [(ack-reg-driver 0 9) 10]
    [(ack-reg-driver 1 1) 3]
    [(ack-reg-driver 1 3) 5]
    [(ack-reg-driver 2 1) 5]
    [(ack-reg-driver 2 2) 7]
    [(depth-reg-driver '()) 1]
    [(depth-reg-driver '(1 (2 (3 (4))))) 4]
    [(depth-reg-driver '(1 2 3 4)) 1]
    [(fact-reg-driver 0) 1]
    [(fact-reg-driver 1) 1]
    [(fact-reg-driver 5) 120]
    [(pascal-reg-driver 10) '(1 3 6 10 15 21 28 36 45 55)]
    [(pascal-reg-driver 20) '(1 3 6 10 15 21 28 36 45 55 66 78 91 105 120 136 153 171 190 210)]
    [(pascal-reg-driver 1) '(1)]))

#| Optional enrichment

Part II and Just Dessert are optional. The current Gradescope contract
tests the four registerized drivers above, not rampolining or
bi-trampolining. These exercises are important preparation for
understanding trampolines and concurrent progress, and you are strongly
encouraged to attempt them. They deliberately have no starter stubs.

|#

#| ===== Part II ===== |#

;; Trampolines can be used to execute multiple trampolinized programs
;; simultaneously. Write a trampoline-like procedure rampoline that
;; takes three thunks containing trampolinized procedure calls, and
;; executes them in random order, returning the value of the first to
;; complete. Note that the procedures may go into an infinite loop. To
;; show that rampoline works correctly, execute it against a
;; trampolined ! function.

;; (define (!-empty-k j) `(!-empty-k ,j))
;; (define (!-k n k) `(!-k ,n ,k))

;; (define (!-apply-k k v)
;;   (match k
;;     [`(!-empty-k ,j) (j v)]
;;     [`(!-k ,n ,k) (λ () (!-apply-k k (* n v)))]))

;; (define (!-cps n k)
;;   (if (zero? n)
;;       (λ () (!-apply-k k 1))
;;       (λ () (!-cps (sub1 n) (!-k n k)))))

;; (define (trampoline th)
;;   (trampoline (th)))

;; (define (main n)
;;   (let/cc jumpout
;;     (trampoline (λ () (!-cps n (!-empty-k jumpout))))))

;; ;; Use the following as a driver to your trampolinized factorial:

;; (define (!-ramp-driver n1 n2 n3)
;;   (let/cc jumpout
;;     (rampoline
;;       (λ () (!-cps n1 (!-empty-k jumpout)))
;;       (λ () (!-cps n2 (!-empty-k jumpout)))
;;       (λ () (!-cps n3 (!-empty-k jumpout))))))

#| ==== Just Dessert ==== |#

;; A trampoline can be used to interleave executions of two
;; trampolinized programs, we've seen (or can imagine) how executing
;; two such programs in a trampoline can return the first answer that
;; completes. But what if we want /both/ answers?

;; Devise a way to return both answers, wherein:

;;   * We still interleave executions of both programs with a trampoline.
;;   * We get back a list with both answers.
;;   * The answers are listed in the order they complete.
;;   * We don't redo any work after finding the first answer.

;; You will need to define a bi-trampoline, a bi-tramp-driver,
;; and a trampolinized version of trib (that generates elements of
;; the
;; [[https://en.wikipedia.org/wiki/Generalizations_of_Fibonacci_numbers#Tribonacci_numbers|tribonacci
;; sequence]]). If you attempt it, use the examples below to test
;; bi-tramp-driver with two numbers. Note: here, you do not need to
;; registerize in order to trampolinize.

;; (check-true* equal?
;;   [(bi-tramp-driver 3 4) '(2 4)]
;;   [(bi-tramp-driver 4 3) '(2 4)]
;;   [(bi-tramp-driver 6 6) '(13 13)])