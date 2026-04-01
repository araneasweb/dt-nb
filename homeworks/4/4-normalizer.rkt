#lang racket

;; First, read and understand the type checker and implementation of typed NbE
;; 1. Add a unit type with the following grammar:
;;
;;   e ::= ...
;;       | sole
;;
;;   t ::= ...
;;       | Trivial
;;
;;   and the following rules:
;;
;;   ---------------- [TrivI]
;;    sole ⇐ Trivial
;;
;;       e : Trivial
;;   --------------------- [Triv-η]
;;     sole ≡ e : Trivial
;;
;; Paste the names of the rules next to the code that implements them in comments.
;;
;; Hint: First add type and expression constructors, then add a value
;; constructor, then update the type checker and evaluator.
;;
;; 2. What should the normal for be for
;;    `(the (-> Trivial Trivial) (lambda (x) x)) ?
;;    Write your answer here, and add it as a test:
;;
;; 3. What should the normal for be for
;;    `(the (-> Nat Nat) (lambda (x) x))?
;;    Write your answer here:
;;
;; 4. What should the normal for be for
;;    (the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (x) x))
;;    Write your answer here:
;;
;; 5. What should the normal for be for
;;    (the (-> (-> Nat Trivial) (-> Nat Trivial)) (lambda (x) x))
;;    Write your answer here, and add it as a test:
;;
;; Optional bonus problem: Using the implementation of rec-List as a
;; model, add rec-Nat to the language.


;; A Type is one of:
;; - 'Nat
;; - `(-> ,A ,B), where A and B are Types
;; - `(List ,A), where A is a Type

;; A Name is a symbol representing the name of a variable.
(define (name? x) (symbol? x))

;; Expr is one of:
;; - a Name, representing a variable
;; - `(app ,e1 ,e2), representing the application of Exprs e1 to e2
;; - `(lambda (,x) ,e), representing a function with parameter Name x and body Expr e
;; - `(the ,A ,e), representing an Expr e of Type A.
;; - `zero, representing the natural number 0
;; - `(add1 ,e), representing one more than the natural number represented by the Expr e
;; - `nil, representing the empty list
;; - `(cons ,e1 ,e2), where e1 and e2 are Exprs, representing prepending the element e1 to the list e2
;; - `(rec-List ,A ,e1 ,e2 ,e3), representing the recursive elimination of
;;   list e1 to Type A, where e2 is the case for nil and e3 is a function for
;;   the cons case.

(define (fail str . rest)
  (error (apply format str rest)))

;; Takes an Expr and returns a Type or #f representing failure
;; All elimination forms synth

(define (type-synth env e)
  (match e
    [(? symbol?)
     (dict-ref env e)]
    [`(the ,A ,e)
     (and (type-check env e A)
          A)]
    [`(app ,e1 ,e2)
     (define A (type-synth env e1))
     (match A
       [`(-> ,A ,B)
        (and (type-check env e2 A)
             B)])]
    [`(rec-List ,A ,tgt ,base ,step)
     (match (type-synth env tgt)
       [`(List ,B)
        (type-check env base A)
        (type-check env step `(-> ,B (-> (List ,B) (-> ,A ,A))))
        A]
       [_
        (fail "target of of rec-List must be a list")])]
    [_ (error "No synth rule for term" e)]))

(define type=? equal?)

;; Takes an Expr and a Type, and returns true or raises an exception
;; All introduction forms check
(define (type-check env e A)
  (define (fail-check B)
    (fail "~a expected ~a but got ~a" e B A))
  (match e
    [`zero
     (or (type=? A 'Nat)
         (fail-check 'Nat))]
    [`(add1 ,e)
     (or (and (type=? A 'Nat)
              (type-check env e 'Nat))
         (fail-check 'Nat))]
    [`nil
     (match A
       [`(List ,B)
        #t]
       [_
        (fail-check 'List)])]
    [`(cons ,e1 ,e2)
     (match A
       [`(List ,B)
        (type-check env e1 B)
        (type-check env e2 A)]
       [_ (fail-check 'List)])]
    [`(lambda (,x) ,e)
     (match A
       [`(-> ,A ,B)
        (type-check (dict-set env x A)
                    e
                    B)]
       [_
        (fail-check '->)])]
    [_
     (type=? A (type-synth env e))]))

;; Value is one of:
;; - `zero
;; - `nil
;; - `(add1 ,v), where v is a Value
;; - `(cons ,v1 ,v2), where v1 and v2 are Values
;; - a closure? struct (clos Env Name Expr), representing a first-class function closed over its
;;   environment and awaiting the value of its parameter.
;; - a neutral? struct (neutral A ne), representing a Neutral expression ne
;;   of type A
(struct closure (env name expr) #:transparent)

;; A Neutral is one of:
;; - a variable
;; - `(app ,ne ,arg) where ne is a Neutral and arg is a Normal
;; - `(rec-List ,A ,ne ,n1 ,n2) where ne is a Neutral and n1 and n2 are Normal
(struct neutral (type ne) #:transparent)

;; A Normal is a normal struct (normal A v) where A is the type of the value v.
(struct normal (type v))

;; Env is dict? mapping Names to Values.
(require racket/dict)
(define initial-env '())

;; Env -> Expr -> Value
;; Evaluate the Expr e in Env env to a Value
(define (eval env e)
  (match e
    [(? name?)
     (dict-ref env e e)]
    [(? integer?)
     e]
    [`(lambda (,x) ,e)
     (closure env x e)]
    [`(app ,e1 ,e2)
     (do-apply (eval env e1)
               (eval env e2))]
    [`zero e]
    [`(add1 ,e)
     `(add1 ,(eval env e))]
    [`nil e]
    [`(cons ,e1 ,e2)
     `(cons ,(eval env e1) ,(eval env e2))]
    [`(rec-List ,A ,tgt ,base ,step)
     (do-rec-List A (eval env tgt) (eval env base) (eval env step))]
    [`(the ,A ,e)
     (eval env e)]
    [_ (error "Non-exhaustic patterns")]))

;; Type -> Value -> Value -> Value -> Value
(define (do-rec-List A tgt base step)
  (match tgt
    [`nil
     base]
    [`(cons ,v1 ,v2)
     (do-apply (do-apply (do-apply step v1) v2)
               (do-rec-List A v2 base step))]
    [(neutral `(List ,B) ne)
     (neutral A `(rec-List ,A ,ne ,(normal A base)
                           ,(normal `(-> ,B (-> (List ,B) (-> ,A ,A)))
                                    step)))]))

;; Value -> Value -> Value
(define (do-apply v1 arg)
  (match v1
    [(closure env x body)
     (eval (dict-set env x arg) body)]
    [(neutral `(-> ,A ,B) ne)
     (neutral B `(app ,ne ,(normal A arg)))]
    [_ (error (string-append "Not a function" v1))]))

;; Might change this definition to produce nicer names
(define (fresh _ name)
  (gensym name))

(define (get-arg-name v)
  (match v
    [(closure _ x _)
     x]
    [_
     'x]))

;; (List Name) -> Type -> Value -> Expr
;; Read back the Value v into an Expr
(define (read-back-value names A v)
  (match A
    [`Nat
     (match v
       [`zero
        'zero]
       [`(add1 ,v)
        `(add1 ,(read-back-value names 'Nat v))]
       [(neutral A ne)
        (read-back-neutral names ne)])]
    [`(-> ,A ,B)
     (let* ([y (fresh names (get-arg-name v))]
            [body (do-apply v (neutral A y))]
            [body-expr (read-back-value (cons y names) B body)])
       `(lambda (,y) ,body-expr))]
    [`(List ,B)
     (match v
       ['nil
        'nil]
       [`(cons ,v1 ,v2)
        `(cons ,(read-back-value names B v1)
               ,(read-back-value names A v2))]
       [(neutral A ne)
        (read-back-neutral names ne)])]))

;; (List Name) -> Neutral -> Expr
;; Read back the Neutral v into an Expr
(define (read-back-neutral names ne)
  (match ne
    [(? name?)
     ne]
    [`(app ,ne ,(normal A v))
     (let* ([rator (read-back-neutral names ne)]
            [rand (read-back-value names A v)])
       `(app ,rator ,rand))]
    [`(rec-List ,A ,ne ,(normal bA base) ,(normal sA step))
     `(rec-List ,A ,(read-back-neutral names ne)
                ,(read-back-value names bA base)
                ,(read-back-value names sA step))]))

;; Expr -> Expr or raises an exception
;; Evaluate the Expr e in Env env and read back the resulting
;; value into its normal form
(define (normalize e)
  (define A (type-synth '() e))
  (read-back-value '() A (eval '() e)))

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
      [(cons `zero `zero) #t]
      [(cons `(add1 ,v1) `(add1 ,v2))
       (helper i xs v1 ys v2)]
      [(cons 'nil 'nil)
       #t]
      [(cons `(cons ,v1 ,tail1)
             `(cons ,v2 ,tail2))
       (and (helper i xs v1 ys v2)
            (helper i xs tail1 ys tail2))]
      [(cons `(rec-List ,A ,tgt1 ,base1 ,step1)
             `(rec-List ,B ,tgt2 ,base2 ,step2))
       (and (equal? A B)
            (helper i xs tgt1 ys tgt2)
            (helper i xs base1 ys base2)
            (helper i xs step1 ys step2))]
      [_ false]))
  (helper 0 '() e1 '() e2))

(module+ test
  (require rackunit)
  (define-check (check-norm-is e n)
    (let ([an (normalize e)])
      (with-check-info (['expr e]
                        ['expected-normal-form n]
                        ['actual-normal-form an])
      (unless (alpha-equiv? an n)
        (fail-check)))))

  (define-syntax (test-norm-is syn)
    (syntax-case syn ()
      [(_ name e n)
       (quasisyntax/loc syn
         (test-begin name #,(quasisyntax/loc syn
                             (check-norm-is e n))))]))

  (test-norm-is "identity, Nat -> Nat"
                `(the (-> Nat Nat) (lambda (f) f))
                `(lambda (f) f))

  (test-norm-is "identity, (Nat -> Nat) -> (Nat -> Nat)"
                `(the (-> (-> Nat Nat) (-> Nat Nat))
                      (lambda (f) f))
                `(lambda (f) (lambda (x) (app f x))))
  (test-norm-is "append"
                `(the
                  (-> (List Nat) (-> (List Nat) (List Nat)))
                  (lambda (xs)
                    (lambda (ys)
                      (rec-List (List Nat) xs ys
                                (lambda (z)
                                  (lambda (_)
                                    (lambda (so-far)
                                      (cons z so-far))))))))
                `(lambda (xs)
                   (lambda (ys)
                     (rec-List (List Nat) xs ys
                               (lambda (z)
                                 (lambda (_)
                                   (lambda (so-far)
                                     (cons z so-far))))))))

  (test-norm-is "append (:: 1 (:: 2 nil))"
                `(app
                  (the (-> (List Nat) (-> (List Nat) (List Nat)))
                       (lambda (xs)
                         (lambda (ys)
                           (rec-List (List Nat) xs ys
                                     (lambda (z)
                                       (lambda (_)
                                         (lambda (so-far)
                                           (cons z so-far))))))))
                  (cons (add1 zero)
                        (cons (add1 (add1 zero))
                              nil)))
                `(lambda (ys)
                   (cons (add1 zero)
                         (cons (add1 (add1 zero))
                               ys))))

  (test-norm-is "Length of nat lists"
                `(the (-> (List Nat) Nat)
                      (lambda (xs)
                        (rec-list Nat xs zero (lambda (hd) (lambda (_) (lambda
                                                                         (len) (add1 len)))))))
                `(lambda (xs)
                   (rec-list Nat xs zero (lambda (hd) (lambda (_) (lambda (len)
                                                                    (add1 len))))))))
