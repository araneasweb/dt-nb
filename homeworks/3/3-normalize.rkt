#lang racket

;; Instructions:
;;
;; Please add pairs to this implementation of untyped normalization.
;;
;;
;; In particular, your tasks are:
;;  0. Add constructors for cons, car, and cdr to Expr
;;  1. Identify the new neutral expressions, and add the corresponding
;;     constructor(s) to Neutral
;;  2. Identify the additional values. Add the corresponding
;;     constructor(s) to Value
;;  3. Extend eval to cover the new expressions, and implement helpers for
;;     car and cdr. Your helpers should cover all values: the
;;     "Non-exhaustive patterns" message should never occur.
;;  4. Extend readBackValue and readBackNeutral for the extra constructors
;;     from tasks 1 and 2
;;  5. Extend alphaEquiv with the constructors from task 0
;;  6. Write tests that check that the following equations are respected
;;     by your implementation:
;; (car (cons a d)) = a
;; (cdr (cons a d)) = d
;; (cons a1 d1) = (cons a1 d1)
;; (car x) = (car x)
;; (cdr x) = (cdr x)
;;     As an example, tests for the first equation could be written:
     ;; test-norm-is "(car (cons 2 4)) = 2" initial-env
     ;;   `(car (cons 2 4))
     ;;   2
     ;; test-norm-is "(car (cons a d)) = a" initial-env
     ;;   `(lambda (a) (lambda (d) (car (cons a d))))
     ;;   `(lambda (a) (lambda (d) a))



;; A Name is a symbol representing the name of a variable.
(define (name? x) (symbol? x))

;; Expr is one of:
;; - a Name, representing a variable
;; - an integer, representing an integer literal
;; - `(app ,e1 ,e2), representing the application of e1 to e2
;; - `(lambda (,x) ,e), representing a function with parameter x and body e
;; - TODO Extend

;; Value is one of:
;; - an integer
;; - a closure? struct, representing a first-class function closed over its
;;   environment and awaiting the value of its parameter.
;; - a neutral? struct, representing a neutral expression
;; - TODO Extend
(struct closure (env name expr) #:transparent)

;; Neutral is a neutral? struct, whose neutral-ne element is one of:
;; - a variable
;; - `(app ,ne ,arg) where ne is a Neutral and arg is a Value
(struct neutral (ne) #:transparent)

;; Env is dict? mapping Names to Values.
(require racket/dict)
(define initial-env '())

;; Evaluate the Expr e in Env env and read back the resulting
;; value into its normal form
(define (normalize env e)
  (read-back-value (dict-keys env) (eval env e)))

;; Evaluate the Expr e in Env env to a Value
(define (eval env e)
  (match e
    [(? name?)
     (dict-ref env e)]
    [(? integer?)
     e]
    [`(lambda (,x) ,e)
     (closure env x e)]
    [`(app ,e1 ,e2)
     (do-apply (eval env e1)
               (eval env e2))]
    [_ (error "Non-exhaustic patterns")]))

(define (do-apply v1 arg)
  (match v1
    [(closure env x body)
     (eval (dict-set env x arg) body)]
    [(neutral ne)
     (neutral `(app ,ne ,arg))]
    [_ (error (string-append "Not a function" v1))]))

;; Might change this definition to produce nicer names
(define (fresh _ name)
  (gensym name))

;; Read back the Value v into an Expr
(define (read-back-value names v)
  (match v
    [(closure env x e)
     (let* ([y (fresh names x)]
            [body (do-apply v (neutral y))]
            [body-expr (read-back-value (cons y names) body)])
       `(lambda (,y) ,body-expr))]
    [(? integer?)
     v]
    [(neutral ne)
     (read-back-neutral names ne)]))

;; Read back the Neutral v into an Expr
(define (read-back-neutral names ne)
  (match ne
    [(? name?)
     ne]
    [`(app ,ne ,v)
     (let* ([rator (read-back-neutral names ne)]
            [rand (read-back-value names v)])
       `(app ,rator ,rand))]))

(define (alpha-equiv? e1 e2)
  (define (helper i xs x ys y)
    (match (cons x y)
      [(cons (? name?) (? name?))
       (let ([x? (dict-ref xs x #f)]
             [y? (dict-ref ys y #f)])
         (cond
           [(and x? y?)
            (equal? x? y?)]
           [(and (not x?) (not y?))
            (equal? x y)]
           [else false]))]
      [(cons `(app ,e1 ,e11)
             `(app ,e2 ,e22))
       (and
        (helper i xs e1 ys e2)
        (helper i xs e11 ys e22))]
      [(cons `(lambda (,x) ,e1)
             `(lambda (,y) ,e2))
       (helper (add1 i)
               (dict-set xs x i)
               e1
               (dict-set ys y i)
               e2)]
      [(cons n m)
       #:when (and (integer? n) (integer? m))
       (equal? n m)]
      [_ false]))
  (helper 0 '() e1 '() e2))

;;;; Test code
(define (define-church-nums initial-env)
  (dict-set*
   initial-env
   'zero (closure initial-env 'f `(lambda (x) x))
   'add1 (closure initial-env 'n `(lambda (f) (lambda (x) (app f (app (app n f) x)))))))

(define (define-church-add initial-env)
  (dict-set
   initial-env
   'church+ (closure initial-env 'j `(lambda (k) (lambda (f) (lambda (x) (app (app j f) (app (app k f) x))))))))

(define (to-church n)
  (match n
    [(? integer?)
     #:when (<= n 0)
     'zero]
    [e `(app add1 ,(to-church (- e 1)))]))

(module+ test
  (require rackunit)
  (define-check (check-norm-is env e n)
    (let ([an (normalize env e)])
      (with-check-info (['env env]
                      ['expr e]
                      ['expected-normal-form n]
                      ['actual-normal-form an])
      (unless (alpha-equiv? an n)
        (fail-check)))))

  (define-syntax-rule (test-norm-is name env e n)
    (test-begin name (check-norm-is env e n)))

  (test-norm-is "identity" initial-env
                `(lambda (x) x)
                `(lambda (x) x))

  (test-norm-is "shadowing" initial-env
                `(lambda (x) (lambda (x) (lambda (y) (app y x))))
                `(lambda (x) (lambda (x) (lambda (y) (app y x)))))

  (test-norm-is "3" (define-church-nums initial-env)
                (to-church 3)
                `(lambda (f)
                   (lambda (x)
                     (app f (app f (app f x))))))

  (test-norm-is "5" (define-church-add (define-church-nums initial-env))
                `(app (app church+ ,(to-church 3)) ,(to-church 2))
                `(lambda (f)
                   (lambda (x)
                     (app f
                          (app f
                               (app f
                                    (app f
                                         (app f
                                              x))))))))

  (test-norm-is "capture avoidance" initial-env
                `(lambda (x)
                   (app (lambda (y)
                          (lambda (x)
                            y))
                        x))
                `(lambda (y)
                   (lambda (z)
                     y)))

  (test-norm-is "3 = 3" initial-env 3 3)
  (test-norm-is "15 = 15" initial-env 15 15))
