#lang racket

;; A Name is a symbol representing the name of a variable.
(define (name? x) (symbol? x))

;; Expr is one of:
;; - a Name, representing a variable
;; - an integer, representing an integer literal
;; - `(app ,e1 ,e2), representing the application of e1 to e2
;; - `(lambda (,x) ,e), representing a function with parameter x and body e
;; - `(+ ,e1 ,e2), representing the addition of e1 to e2

;; Value is one of:
;; - an integer
;; - a closure? struct, representing a first-class function closed over its
;;   environment and awaiting the value of its parameter.
(struct closure (env name expr) #:transparent)

;; Env is dict? mapping Names to Values.
(require racket/dict)
(define initial-env '())

;;; Add subtraction and division to this interpreter.
(define (eval env e)
  (match e
    [(? name?)
     (dict-ref env e)]
    [(? integer?)
     (error "TODO")]
    [`(lambda (,x) ,e)
     (error "TODO")]
    [`(app ,e1 ,e2)
     (error "TODO")]
    [`(+ ,e1 ,e2)
     (error "TODO")]))

(define (do-apply v1 arg)
  (match v1
    [(closure env x body)
     (error "TODO")]
    [_ (error (string-append "Not a function" v1))]))

(define (do-plus v1 v2)
  (match (cons v1 v2)
    [(cons (? integer?) (? integer?))
     (error "TODO")]
    [_ (error (format "One of these is not an integer: ~a ~a~n" v1 v2))]))

(define (alpha-equiv e1 e2)
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
       (error "TODO")]
      [(cons `(lambda (,x) ,e1)
             `(lambda (,y) ,e2))
       (error "TODO")]
      ;; More cases are necessary in this function
      [_ false]))
  (helper 0 '() e1 '() e2))

;;;; Test code
(define (define-church-nums init-env)
  (dict-set*
   init-env
   'zero (closure init-env 'f `(lambda (x) x))
   'add1 (closure init-env 'n `(lambda (f) (lambda (x) (app f (app (app n f) x)))))))

(define (define-church-add init-env)
  (dict-set
   init-env
   'church+ (closure init-env 'j `(lambda (k) (lambda (f) (lambda (x) (app (app j f) (app (app k f) x))))))))

(define (to-church n)
  (match n
    [(? integer?)
     #:when (<= n 0)
     'zero]
    [e `(app add1 ,(to-church (- e 1)))]))

(module+ test
  (require rackunit)
  (define-check (check-val-is? f e1 e2)
    (check-equal?
     (eval (f initial-env) e1)
     e2))

  (check-val-is? identity
   '(lambda (x) x)
   (closure initial-env 'x 'x))

  (check-val-is? identity
   '(lambda (x) (lambda (x) (lambda (y) (app y x))))
   (closure initial-env 'x `(lambda (x) (lambda (y) (app y x)))))

  (check-val-is? define-church-nums
   (to-church 3)
   (closure
    (dict-set*
     initial-env
     'n (closure
         (dict-set*
          initial-env
          'n (closure
              (dict-set*
               initial-env
               'n (closure initial-env 'f `(lambda (x) x)))
              'f
              `(lambda (x) (app f (app (app n f) x)))))
         'f `(lambda (x) (app f (app (app n f) x)))))
    'f
    `(lambda (x)
      (app f (app (app n f) x)))))

  (check-val-is? define-church-nums
   `(app (app ,(to-church 3)
              (lambda (n) (+ n 1)))
         0)
   3)

  (check-true
   (alpha-equiv 'x 'x))
  (check-false
   (alpha-equiv 'x 'y))
  (check-true
   (alpha-equiv '(lambda (x) x) '(lambda (y) y)))
  (check-true
   (alpha-equiv '(lambda (y) (lambda (x) x)) '(lambda (x) (lambda (y) y))))
  (check-false
   (alpha-equiv '(lambda (y) y) '(lambda (x) y))))
