#lang plait

(define-type Value
  (litV [n : Number])
  (closV [arg : Symbol]
         [body : Exp]
         [env : Env]))

(define-type Exp
  (litE [n : Number])
  (idE [s : Symbol])
  (plusE [l : Exp] 
         [r : Exp])
  (multE [l : Exp]
         [r : Exp])
  (lamE [n : Symbol]
        [body : Exp])
  (appE [fun : Exp]
        [arg : Exp]))

(define-type Binding
  (bind [name : Symbol]
        [val : Value]))

(define-type-alias Env (Listof Binding))

(define mt-env empty)
(define extend-env cons)

(module+ test
  (print-only-errors #t))

;; parse ----------------------------------------
(define parse : (S-Exp -> Exp)
  (lambda (s)
    (cond
      [(s-exp-match? `NUMBER s) (litE (s-exp->number s))]
      [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
      [(s-exp-match? `{+ ANY ANY} s)
       (plusE (parse (second (s-exp->list s)))
              (parse (third (s-exp->list s))))]
      [(s-exp-match? `{* ANY ANY} s)
       (multE (parse (second (s-exp->list s)))
              (parse (third (s-exp->list s))))]
      [(s-exp-match? `{let {[SYMBOL ANY]} ANY} s)
       (let ([bs (s-exp->list (first
                               (s-exp->list (second
                                             (s-exp->list s)))))])
         (appE (lamE (s-exp->symbol (first bs))
                     (parse (third (s-exp->list s))))
               (parse (second bs))))]
      [(s-exp-match? `{lambda {SYMBOL} ANY} s)
       (lamE (s-exp->symbol (first (s-exp->list 
                                    (second (s-exp->list s)))))
             (parse (third (s-exp->list s))))]
      [(s-exp-match? `{ANY ANY} s)
       (appE (parse (first (s-exp->list s)))
             (parse (second (s-exp->list s))))]
      [else (error 'parse "invalid input")])))

(define (parse/num [s : S-Exp]) : Exp
  (parse s))

(module+ test
  (test (parse/num `2)
        (litE 2))
  (test (parse/num `x) ; note: backquote instead of normal quote
        (idE 'x))
  (test (parse/num `{+ 2 1})
        (plusE (litE 2) (litE 1)))
  (test (parse/num `{* 3 4})
        (multE (litE 3) (litE 4)))
  (test (parse/num `{+ {* 3 4} 8})
        (plusE (multE (litE 3) (litE 4))
               (litE 8)))
  (test (parse/num `{let {[x {+ 1 2}]}
                      y})
        (appE (lamE 'x (idE 'y))
              (plusE (litE 1) (litE 2))))
  (test (parse/num `{lambda {x} 9})
        (lamE 'x (litE 9)))
  (test (parse/num `{double 9})
        (appE (idE 'double) (litE 9)))
  (test/exn (parse/num `{{+ 1 2}})
            "invalid input")
  (test/exn (parse/num `"a")
            "invalid input"))

;; interp ----------------------------------------
(define interp : (Exp Env -> Value)
  (lambda (a env)
    (type-case Exp a
      [(litE n) (litV n)]
      [(idE s) (lookup s env)]
      [(plusE l r) (num+ (interp l env) (interp r env))]
      [(multE l r) (num* (interp l env) (interp r env))]
      [(lamE n body)
       (closV n body env)]
      [(appE fun arg) (type-case Value (interp fun env)
                        [(closV n body c-env)
                         (interp body
                                 (extend-env
                                  (bind n
                                        (interp arg env))
                                  c-env))]
                        [else (error 'interp "not a function")])])))

(define (interp/num [a : Exp] [env : Env]) : Value
  (interp a env))

(module+ test
  (test (interp/num (parse/num `2) mt-env)
        (litV 2))
  (test/exn (interp/num (parse/num `x) mt-env)
            "free variable")
  (test (interp/num (parse/num `x) 
                    (extend-env (bind 'x (litV 9)) mt-env))
        (litV 9))
  (test (interp/num (parse/num `{+ 2 1}) mt-env)
        (litV 3))
  (test (interp/num (parse/num `{* 2 1}) mt-env)
        (litV 2))
  (test (interp/num (parse/num `{+ {* 2 3} {+ 5 8}})
                    mt-env)
        (litV 19))
  (test (interp/num (parse/num `{lambda {x} {+ x x}})
                    mt-env)
        (closV 'x (plusE (idE 'x) (idE 'x)) mt-env))
  (test (interp/num (parse/num `{let {[x 5]}
                                  {+ x x}})
                    mt-env)
        (litV 10))
  (test (interp/num (parse/num `{let {[x 5]}
                                  {let {[x {+ 1 x}]}
                                    {+ x x}}})
                    mt-env)
        (litV 12))
  (test (interp/num (parse/num `{let {[x 5]}
                                  {let {[y 6]}
                                    x}})
                    mt-env)
        (litV 5))
  (test (interp/num (parse/num `{{lambda {x} {+ x x}} 8})
                    mt-env)
        (litV 16))

  (test/exn (interp/num (parse/num `{1 2}) mt-env)
            "not a function")
  (test/exn (interp/num (parse/num `{+ 1 {lambda {x} x}}) mt-env)
            "not a literal")
  (test/exn (interp/num (parse/num `{let {[bad {lambda {x} {+ x y}}]}
                                      {let {[y 5]}
                                        {bad 2}}})
                        mt-env)
            "free variable"))

;; num+ and num* ----------------------------------------
(define num-op : ((Number Number -> Number)
                  Value
                  Value
                  -> Value)
  (lambda (op l r)
    (cond
      [(and (litV? l) (litV? r))
       (litV (op (litV-n l) (litV-n r)))]
      [else
       (error 'interp "not a literal")])))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

(module+ test
  (test (num+ (litV 1) (litV 2))
        (litV 3))
  (test (num* (litV 2) (litV 3))
        (litV 6)))

;; lookup ----------------------------------------
(define lookup : (Symbol Env -> Value)
  (lambda (n env)
    (cond
      [(empty? env) (error 'lookup "free variable")]
      [else (cond
              [(symbol=? n (bind-name (first env)))
               (bind-val (first env))]
              [else (lookup n (rest env))])])))

(module+ test
  (test/exn (lookup 'x mt-env)
            "free variable")
  (test (lookup 'x (extend-env (bind 'x (litV 8)) mt-env))
        (litV 8))
  (test (lookup 'x (extend-env
                    (bind 'x (litV 9))
                    (extend-env (bind 'x (litV 8)) mt-env)))
        (litV 9))
  (test (lookup 'y (extend-env
                    (bind 'x (litV 9))
                    (extend-env (bind 'y (litV 8)) mt-env)))
        (litV 8)))