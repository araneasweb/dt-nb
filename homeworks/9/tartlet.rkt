#lang racket

;; This file is a type checker for a smaller relative of Pie, called Tartlet.
;;
;; Tartlet is like Pie, with the following exceptions:
;;
;;  1. There is no syntactic sugar such as -> and Pair types, or
;;     functions with multiple arguments.
;;
;;  2. The type U describes _all_ types, including itself. Thus, there
;;     is no need for the forms of judgment:
;;       * ____ is a type
;;       * ____ and ____ are the same type
;;
;;  3. Some type constructors in Pie are missing, such as Either.


;; Your tasks:
;;
;; 1. Add the type Either. Use the following grammar and rules:
;;
;;  e ::= ...
;;      | (Either e e)
;;
;;  Γ ⊢ A ⇐ U   Γ ⊢ B ⇐ U
;; ------------------------
;;   Γ ⊢ (Either A B) ⇒ U
;;
;; Remember to update alphaEquiv and readBackTyped.
;;
;; 2. Add the introduction forms for Either. Use the following grammar and rules:
;;
;;  e ::= ...
;;      | (left e)
;;      | (right e)
;;
;;          Γ ⊢ e ⇐ A
;; -----------------------------
;;  Γ ⊢ (left e) ⇐ (Either A B)
;;
;;           Γ ⊢ e ⇐ B
;; -----------------------------
;;  Γ ⊢ (right e) ⇐ (Either A B)
;;
;;
;; Each is worth 1 point (2 total for this question)
;;
;; 3. Add the elimination rule for Either. Use the following grammar and rules:
;;
;;   e ::= ...
;;       | (ind-Either e e e e)
;;
;;    Γ ⊢ tgt ⇒ (Either A B)
;;    Γ ⊢ mot ⇐ (Π ((e (Either A B))) U)
;;    Γ ⊢ ell ⇐ (Π ((a A)) (mot (left a)))
;;    Γ ⊢ are ⇐ (Π ((b B)) (mot (right b)))
;;  ----------------------------------------------
;;   Γ ⊢ (ind-Either tgt mot ell are) ⇒ (mot tgt)
;;
;; 4. Translate the definitions of evenness and oddness from the book
;;    to Tartlet. Add them to evenOddProgram, after the definition of
;;    double.
;;
;; 5. Prove that zero is even in Tartlet. Add this and the remaining
;;    definitions to evenOddProgram as well.
;;
;; 6. Prove that adding one to an even number is odd.
;;
;; 7. Prove that adding one to an odd number is even.
;;
;; 8. Prove that every natural number is either even or odd.
;;
;; Hint: To check whether your definitions work, you can load
;; this file in ghci, and evaluate
;;   > testFile evenOddProgram
;;
;; If the result is Left around a message, type checking failed. If
;; the result is Right around a list of output, then type checking
;; succeeded.
;;
;; Remember: there's no "claim" in Tartlet. Definitions and examples
;; need to be expressions for which a type can be synthesized. Use The
;; to make a checkable expression synthesizable.

(define (name? x) (symbol? x))


(define (fail str . rest)
  (error (apply format str rest)))

;; Listof Name -> Name -> Name
(define (freshen ls x)
  (gensym 'x))

;; Expr is one of:
;; - a Name, representing a variable
;; - `(Pi (,name : ,e1) ,e2), where e1 and e2 are Expr and name is a Name
;; - `(lambda (,x) ,e), representing a function with parameter Name x and body Expr e
;; - `(app ,e1 ,e2), representing the application of Exprs e1 to e2
;; - `(Sigma (,name : ,e1) ,e2), where e1 and e2 are Expr and name is a Name
;; - `(cons ,e1 ,e2), where e1 and e2 are Exprs, representing the pair e1 and e2
;; - `(car ,e), where e is an Expr, representing the first component of a pair
;; - `(cdr ,e), where e is an Expr, representing the second component of a pair
;; - `Nat
;; - `zero, representing 0
;; - `(add1 ,e), where e is an Expr, representing the natural number one greater than e
;; - `(ind-Nat ,target ,motive ,base ,step), where each subterm is an Expr
;; - `(= ,A ,e1 ,e2), representing a proof that e1 and e2 are equal terms of type A, where each subterm is an Expr
;; - 'same, representing a proof that a term is equal to itself
;; - `(replace ,target ,motive ,base), where each subterm is an Expr
;; - `Trivial
;; - 'sole
;; - 'Absurd
;; - `(ind-Absurd ,motive ,target), where each subterm is an Expr
;; - 'Atom
;; - `(tick ,string), where string is a string literal
;; - 'U
;; - `(the ,ty ,e), where each subterm is a Expr

;; Env is dict? mapping Names to Values.
(require racket/dict)
(define initial-env '())

(struct closure (env name body) #:transparent)

(struct VPi (type c) #:transparent)
(struct VLambda (c) #:transparent)
(struct VSigma (type c) #:transparent)

;; Type is an alias for Value
;;
;; Value is one of:
;; - (VPi A c), where A is a Type, and c is a closure?
;; - (VLambda c), where c is a closure?
;; - (VSigma A c), where A is a Type, and c is a closure?
;; - `(cons ,Value_1 ,Value_2)
;; - 'Nat
;; - 'zero
;; - `(add1 ,Value), where v is a value
;; - `(= ,Type ,Value ,Value)
;; - 'same
;; - 'Trivial
;; - 'sole
;; - 'Absurd
;; - 'Atom
;; - `(tick ,string)
;; - 'U
;; - (neutral ty Neutral)

(struct neutral (type ne) #:transparent)

;; Neutral is one of:
;; - a Name
;; - `(app ,Neutral ,Normal)
;; - `(car ,Neutral)
;; - `(cdr ,Neutral)
;; - `(ind-nat ,neutral ,normal_1 ,normal_2 ,normal_3)
;; - `(replace ,neutral ,normal_1 ,normal_2)
;; - `(ind-Absurd ,neutral ,normal)

;; A Normal is a normal struct (normal A v) where A is the type of the value v.
(struct normal (type v))

(struct Def (type v) #:transparent)
(struct IsA (type) #:transparent)

;; Ctx is a dict? mapping names to one of:
;; - (Def A v), where A is a Type and v is a Value
;; - (IsA A), where A is a Type

(define (ctx-define ctx name A v)
  (dict-set ctx name (Def A v)))

(define (ctx-extend ctx name A)
  (dict-set ctx name (IsA A)))

(define (lookup-type ctx name [failth (lambda () (fail "Unbound variable ~a" name))])
  (match (dict-ref ctx name failth)
    [(Def A v) A]
    [(IsA A) A]
    ;; only happens when the user specifies a different failure mode
    [e e]))

(define (mk-env ctx)
  (for/fold ([e initial-env])
            ([(k v) (in-dict ctx)])
    (match v
      [(Def type v)
       (dict-set e k v)]
      [(IsA type)
       (dict-set e k (neutral type k))])))

;; Env -> Expr -> Value
;; Evaluate the Expr e in Env env to a Value

(define (eval env e)
  (match e
    [`(Pi (,x : ,A) ,B)
     (VPi (eval env A) (closure env x B))]
    [`(lambda (,x) ,e)
     (VLambda (closure env x e))]
    [`(app ,e1 ,e2)
     (do-apply (eval env e1)
               (eval env e2))]
    [`(Sigma (,x : ,A) ,B)
     (VSigma (eval env A) (closure env x B))]
    [`(cons ,e1 ,e2)
     `(cons ,(eval env e1) ,(eval env e2))]
    [`(car ,e)
     (do-car e)]
    [`zero e]
    [`(add1 ,e)
     `(add1 ,(eval env e))]
    [`(ind-Nat ,target ,motive ,base ,step)
     (do-ind-Nat (eval env target) (eval env motive) (eval env base) (eval env step))]
    [`(= ,A ,e1 ,e2)
     `(= ,(eval env A) ,(eval env e1) ,(eval env e2))]
    ['same e]
    [`(replace ,tgt ,motive ,base)
     (do-replace (eval env tgt) (eval env motive) (eval env base))]
    ['Nat e]
    ['Trivial e]
    ['sole e]
    ['Absurd e]
    [`(ind-Absurd ,tgt ,motive)
     (do-ind-Absurd (eval env tgt) (eval env motive))]
    ['Atom e]
    [`(tick ,v) e]
    ['U e]
    [`(the ,A ,e)
     (eval env e)]
    [(? name?)
     (dict-ref env e (lambda () (fail "Missing value for ~a" e)))]
    [_ (error "Non-exhaustive patterns")]))

(define (eval-closure c v)
  (match c
    [(closure env name body)
     (eval (dict-set env name v) body)]))

(define (do-apply v1 v2)
  (match v1
    [(VLambda c)
     (eval-closure c v2)]
    [(neutral (VPi A c) neu)
     (neutral (eval-closure c v2) `(app ,neu ,(normal A v2)))]))

(define (do-car v)
  (match v
    [`(cons ,v1 ,v2)
     v1]
    [(neutral (VSigma A Bc) neu)
     (neutral A `(car ,neu))]))

(define (do-cdr v)
  (match v
    [`(cons ,v1 ,v2)
     v2]
    [(neutral (VSigma A c) neu)
     (neutral (eval-closure c (do-car v)) `(cdr ,neu))]))


(define (do-ind-Absurd v-tgt v-motive)
  (match v-tgt
    [(neutral 'Absurd neu)
     (neutral `(ind-Absurd ,neu ,(normal 'U v-motive)))]))

(define (do-replace v-tgt v-motive v-base)
  (match v-tgt
    ['same
     v-base]
    [(neutral `(= ,A ,from ,to) neu)
     (define motT (VPi A (closure '() 'x 'U)))
     (define baseT (do-apply v-motive from))
     (neutral (do-apply v-motive to)
              `(replace ,neu ,(normal motT v-motive)
                        ,(normal baseT v-base)))]))

(define (ind-Nat-step-Type mot)
  (eval (dict-set '() 'mot mot)
        '(Pi (n-1 : Nat)
             (Pi (almost : (app mot n-1))
                 (app mot (add1 n-1))))))

(define (do-ind-Nat tgt mot base step)
  (match tgt
    ['zero
     base]
    [`(add1 ,v)
      (do-apply (do-apply step v)
                (do-ind-Nat v mot base step))]
    [(neutral 'Nat neu)
     (neutral (do-apply mot tgt)
              `(ind-Nat ,neu
                        ,(normal (VPi 'Nat (closure '() 'k 'U)) mot)
                        ,(normal (do-apply mot 'zero) base)
                        ,(normal (ind-Nat-step-Type mot)
                                 step)))]))

;; Ctx -> Normal -> Expr
(define (read-back-normal ctx n)
  (match n
    [(normal A v)
     (read-back-typed ctx A v)]))

;; Ctx -> Type -> Value -> Expr
(define (read-back-typed ctx A v)
  (match A
    ['Nat
     (match v
       ['zero v]
       [`(add1 ,v)
        `(add1 ,(read-back-typed ctx A v))]
       [(neutral _ v)
        (read-back-neutral ctx v)])]
    [(VPi A Bc)
     (define x (freshen (dict-keys ctx) (closure-name Bc)))
     (define x-val (neutral A x))
     `(lambda (,x)
        ,(read-back-typed (ctx-extend ctx x A)
                          (eval-closure Bc x-val)
                          (do-apply v x-val)))]
    [(VSigma A c)
     (define car-val (do-car v))
     (define cdr-val (do-cdr v))
     `(cons
       ,(read-back-typed ctx A car-val)
       ,(read-back-typed ctx (eval-closure c car-val) cdr-val))]
    ['Trivial
     'sole]
    ['Absurd
     (match v
       [(neutral 'Absurd neu)
        `(the Absurd ,(read-back-neutral ctx neu))])]
    [`(= ,A ,from ,to)
     `(= ,(read-back-typed ctx 'U A)
         ,(read-back-typed ctx A from)
         ,(read-back-typed ctx A to))]
    ['U
     (match v
       ['Nat v]
       ['Atom v]
       ['Trivial v]
       ['Absurd v]
       [`(= ,A ,from ,to)
        `(= ,(read-back-typed ctx 'U A)
            ,(read-back-typed ctx A from)
            ,(read-back-typed ctx A to))]
       [(VSigma vA Bc)
        (define x (freshen (dict-keys ctx) (closure-name Bc)))
        (define A (read-back-typed ctx 'U vA))
        (define B (read-back-typed (ctx-extend ctx x vA)
                                   'U
                                   (eval-closure Bc (neutral vA x))))
        `(Sigma (,x : ,A) ,B)]
       [(VPi vA Bc)
        (define x (freshen (dict-keys ctx) (closure-name Bc)))
        (define A (read-back-typed ctx 'U vA))
        (define B (read-back-typed (ctx-extend ctx x vA)
                                   'U
                                   (eval-closure Bc (neutral vA x))))
        `(Pi (,x : ,A) ,B)]
       ['U v]
       [(neutral A neu)
        (read-back-neutral ctx neu)]
       [_
        (fail "Undefined typed read-back of ~a at type ~a" v A)])]
    [(neutral A neu)
     (read-back-neutral ctx neu)]
    [_
     (fail "Undefined typed read-back of ~a of at type ~a" A v)]))

;; Ctx -> Neutral -> Expr
(define (read-back-neutral ctx neu)
  (match neu
    [(? name?)
     neu]
    [`(app ,neu ,n)
     `(app ,(read-back-neutral ctx neu)
           ,(read-back-normal ctx n))]
    [`(car ,neu)
     `(car ,(read-back-neutral ctx neu))]
    [`(cdr ,neu)
     `(cdr ,(read-back-neutral ctx neu))]
    [`(ind-Nat ,neu ,mot ,base ,step)
     `(ind-Nat ,(read-back-neutral ctx neu)
               ,(read-back-normal ctx mot)
               ,(read-back-normal ctx base)
               ,(read-back-normal ctx step))]
    [`(replace ,neu ,mot ,base)
     `(replace ,(read-back-neutral ctx neu)
               ,(read-back-normal ctx mot)
               ,(read-back-normal ctx base))]
    [`(ind-Absurd ,neu ,mot)
     `(ind-Absurd (the Absurd ,(read-back-neutral ctx neu))
                  ,(read-back-normal ctx mot))]))

;; Ctx -> Expr -> Type, or raises an exception
(define (synth ctx e)
  (match e
    [`(Pi (,x : ,A) ,B)
     (check ctx A 'U)
     (check (ctx-extend ctx x (eval (mk-env ctx) A))
            B 'U)
     'U]
    [`(app ,rator ,rand)
     (define fun-ty (synth ctx rator))
     (define-values (A Bc) (is-Pi ctx fun-ty))
     (check ctx rand A)
     (eval-closure Bc (eval (mk-env ctx) rand))]
    [`(Sigma (,x : ,A) ,B)
     (check ctx A 'U)
     (check (ctx-extend ctx x (eval (mk-env ctx) A))
            B 'U)
     'U]
    [`(car ,p)
     (define Pt (synth ctx p))
     (define-values (A _) (is-Sigma ctx Pt))
     A]
    [`(cdr ,p)
     (define Pt (synth ctx p))
     (define-values (A Bc) (is-Sigma ctx Pt))
     (eval-closure Bc (do-car (eval (mk-env ctx) p)))]
    ['Nat 'U]
    [`(ind-Nat ,tgt ,mot ,base ,step)
     (define tgt-Type (synth ctx tgt))
     (is-Nat ctx tgt-Type)
     (define tgtV (eval (mk-env ctx) tgt))
     (define motTy (eval '() `(Pi (x : Nat) U)))
     (check ctx mot motTy)
     (define motV (eval (mk-env ctx) mot))
     (check ctx base (do-apply motV 'zero))
     (check ctx step (ind-Nat-step-Type motV))
     (do-apply motV tgtV)]
    [`(= ,A ,from ,to)
     (check ctx A 'U)
     (define Av (eval (mk-env ctx) A))
     (check ctx from Av)
     (check ctx to Av)
     'U]
    [`(replace ,tgt ,mot ,base)
     (define t (synth ctx tgt))
     (define-values (ty from to) (is-= ctx t))
     (define motTy (eval (dict-set '() 'ty ty)
                         '(Pi (x : ty) U)))
     (check ctx mot motTy)
     (define motV (eval (mk-env ctx) mot))
     (check ctx base (do-apply motV from))
     (do-apply motV to)]
    ['Trivial 'U]
    ['Absurd 'U]
    [`(ind-Absurd ,tgt ,mot)
     (define t (synth ctx tgt))
     (is-Absurd ctx t)
     (check ctx mot 'U)
     (eval (mk-env ctx) mot)]
    ['Atom 'U]
    ['U 'U]
    [`(the ,A ,e)
     (check ctx A 'U)
     (define Av (eval (mk-env ctx) A))
     (check ctx e Av)
     Av]
    [(? name?)
     (lookup-type ctx e)]
    [_
     (fail "Unable to synthesize a type for ~a" e)]))

;; Ctx -> Expr -> Ty -> (void), or raises an exception
(define (check ctx e ty)
  (match e
    [`(lambda (,x) ,body)
     (define-values (A Bc) (is-Pi ctx ty))
     (define Bv (eval-closure Bc (neutral A x)))
     (check (ctx-extend ctx x A) body Bv)]
    [`(cons ,a ,b)
     (define-values (A Bc) (is-Sigma ctx ty))
     (check ctx a A)
     (define Av (eval (mk-env ctx) a))
     (check ctx b (eval-closure Bc Av))]
    ['zero
     (is-Nat ctx ty)]
    [`(add1 ,n)
     (is-Nat ctx ty)
     (check ctx n 'Nat)]
    [`same
     (define-values (A from to) (is-= ctx ty))
     (convert ctx A from to)]
    ['sole
     (is-Trivial ctx ty)]
    [`(tick ,s)
     (or (string? string) (fail "Expected string literal but found ~a" string))
     (is-Atom ctx ty)]
    [_
     (define B (synth ctx e))
     (convert ctx 'U ty B)]))

;; Ctx -> Type -> Value -> Value -> (void) or raises an exception
(define (convert ctx A v1 v2)
  (define e1 (read-back-typed ctx A v1))
  (define e2 (read-back-typed ctx A v2))
  (if (alpha-equiv e1 e2)
      (void)
      (fail "~a is not the same as ~a" e1 e2)))

(define (alpha-equiv e1 e2)
  (define (alpha-equiv-helper i xs e1 ys e2)
    (match (cons e1 e2)
      [(cons (? name?)
             (? name?))
       (let ([x? (dict-ref xs e1 #f)]
             [y? (dict-ref ys e2 #f)])
         (cond
           [(and x? y?)
            (equal? x? y?)]
           [(and (not x?) (not y?))
            (equal? e1 e2)]
           [else false]))]
      [(cons `(,PiSig (,x : ,A) ,B)
             `(,PiSig (,y : ,C) ,D))
       (and (alpha-equiv-helper i xs A ys C)
            (alpha-equiv-helper (add1 i)
                                (dict-set xs x i) B
                                (dict-set ys y i) D))]
      [(cons `(lambda (,x) ,e1)
             `(lambda (,y) ,e2))
       (alpha-equiv-helper (add1 i)
                           (dict-set xs x i) e1
                           (dict-set ys y i) e2)]
      [(cons foo foo)
       #true]
      [(cons `(,op ,e1s ...)
             `(,op ,e2s ...))
       (for/and ([e1 e1s]
                 [e2 e2s])
         (alpha-equiv-helper i xs e1 ys e2))]
      [_ #false]))
  (alpha-equiv-helper 0 '() e1 '() e2))

;; Ctx -> Value -> (Values Type Closure), or fails
(define (is-Pi ctx v)
  (match v
    [(VPi A Bc)
     (values A Bc)]
    [_ (fail "Not a Pi Type ~a" v)]))

(define (is-Sigma ctx v)
  (match v
    [(VSigma A Bc)
     (values A Bc)]
    [_ (fail "Not a Sigma Type ~a" v)]))

(define (is-Nat ctx v)
  (match v
    ['Nat (void)]
    [_ (fail "Not Nat ~a" v)]))

(define (is-= ctx v)
  (match v
    [`(= ,A ,from ,to)
     (values A from to)]
    [_ (fail "Not an equality type ~a" v)]))

(define (is-Absurd ctx v)
  (match v
    ['Absurd (void)]
    [_ (fail "Not Absurd ~a" v)]))

(define (is-Trivial ctx v)
  (match v
    ['Trivial (void)]
    [_ (fail "Not Trivial ~a" v)]))

(define (is-Atom ctx v)
  (match v
    ['Atom (void)]
    [_ (fail "Not Atom ~a" v)]))

;; A Top-Level is one of:
;; - `(define ,Name ,Expr)
;; - Expr

;; Ctx -> Top-Level -> (Values (List Expr) Ctx), or fail
(define (top-level ctx cmd)
  (match cmd
    [`(define ,x ,e)
     (if (lookup-type ctx x #f)
         (fail "The name ~a is already defined" x)
         (let* ([t (synth ctx e)]
                [v (eval (mk-env ctx) e)])
           (values '() (ctx-define ctx x t v))))]
    [e
     (define t (synth ctx e))
     (define v (eval (mk-env ctx) e))
     (define e^ (read-back-typed ctx t v))
     (define t^ (read-back-typed ctx 'U t))
     (values `((the ,t^ ,e^)) ctx)]))

;; (List Top-Level) -> (Values (List Expr) Ctx), or fail
(define (process-file decls)
  (let loop ([ctx '()]
             [decls decls])
    (match decls
      ['()
       (values '() ctx)]
      [`(,cmd . ,rest)
       (define-values (out ctx^) (top-level ctx cmd))
       (define-values (more-out ctx^^) (loop ctx^ rest))
       (values (append out more-out) ctx^^)])))

;; (List Top-Level) -> (List Expr), or fail
(define (test-file decls)
  (define-values (out _) (process-file decls))
  out)

;; (List Top-Level)
(define double-program
  `(
    (define double
      (the (Pi (x : Nat) Nat)
           (lambda (x)
             (ind-Nat x (lambda (_) Nat)
                      zero
                      (lambda (_) (lambda (dbl)
                                    (add1 (add1 dbl))))))))
    ))

(define test-double-program
  `(
    ,@double-program
    (app double zero)
    (app double (add1 zero))

    ))

(module+ test
  (require rackunit)
  (define (output-alpha-equal? ls1 ls2)
    (for/and ([e1 ls1]
              [e2 ls2])
      (alpha-equiv e1 e2)))

  (check output-alpha-equal?
   (test-file test-double-program)
   `((the Nat zero)
     (the Nat (add1 (add1 zero)))))

  (check output-alpha-equal?
   (test-file
    `(
      (the (Pi (x : Trivial) Trivial)
           (lambda (x) x))
      ))
   '((the (Pi (x : Trivial) Trivial)
          (lambda (x) sole))))
  )

(define even-odd-program
  `(
    ,@double-program
    (app double (add1 (add1 zero)))
    (define cong
      (the
       (Pi (A : U)
           (Pi (B : U)
               (Pi (from : A)
                   (Pi (to : A)
                       (Pi (eq : (= A from to))
                           (Pi (f : (Pi (x : A) B))
                               (= B
                                  (app f from)
                                  (app f to))))))))
       (lambda (A)
         (lambda (B)
           (lambda (from)
             (lambda (to)
               (lambda (eq)
                 (lambda (f)
                   (replace eq (lambda (where)
                                 (= B (app f from) (app f where)))
                            same)))))))))
    ))

(module+ test
  (check output-alpha-equal?
         (test-file even-odd-program)
         `(
           (the Nat (add1 (add1 (add1 (add1 zero)))))
           )))
