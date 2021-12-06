#lang plait

(define-type Value
  (numV [n : Number])
  (closV [arg : Symbol]
         [body : Exp]
         [env : Env])
  (boolV [value : Boolean])
  (thunkV [delay : Exp]
          [force : Exp]))

(define-type Exp
  (numE [n : Number])
  (idE [s : Symbol])
  (plusE [l : Exp] 
         [r : Exp])
  (multE [l : Exp]
         [r : Exp])
  (letE [n : Symbol] 
        [rhs : Exp]
        [body : Exp])
  (lamE [n : Symbol]
        [body : Exp])
  (appE [fun : Exp]
        [arg : Exp])
  (eqE [l : Exp]
       [r : Exp])
  (ifE [cond : Exp]
       [true : Exp]
       [false : Exp])
  (boolE [s : Symbol])
  (unletE [s : Symbol]
          [exp : Exp]))

(define-type Binding
  (bind [name : Symbol]
        [val : Value]))

(define-type-alias Env (Listof Binding))

(define mt-env empty)
(define extend-env cons)

;;(module+ test
  ;;(print-only-errors #t))

;; parse ----------------------------------------
(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `true s)
     (boolE 'true)]
    [(s-exp-match? `false s)
     (boolE 'false)]
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
       (letE (s-exp->symbol (first bs))
             (parse (second bs))
             (parse (third (s-exp->list s)))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (lamE (s-exp->symbol (first (s-exp->list 
                                  (second (s-exp->list s)))))
           (parse (third (s-exp->list s))))]
    [(s-exp-match? `{unlet SYMBOL ANY} s)
     (unletE (s-exp->symbol (second (s-exp->list s)))
             (parse (third (s-exp->list s))))]
    [(s-exp-match? `{ANY ANY} s)
     (appE (parse (first (s-exp->list s)))
           (parse (second (s-exp->list s))))]
    [(s-exp-match? `{= ANY ANY} s)
     (eqE (parse (second (s-exp->list s)))
          (parse (third (s-exp->list s))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (ifE (parse (second (s-exp->list s)))
          (parse (third (s-exp->list s)))
          (parse (fourth (s-exp->list s))))]
    [else (error 'parse "invalid input")]))

(module+ test
  (test (parse `2)
        (numE 2))
  (test (parse `x)
        (idE 'x))
  (test (parse `{+ 2 1})
        (plusE (numE 2) (numE 1)))
  (test (parse `{* 3 4})
        (multE (numE 3) (numE 4)))
  (test (parse `{+ {* 3 4} 8})
        (plusE (multE (numE 3) (numE 4))
               (numE 8)))
  (test (parse `{let {[x {+ 1 2}]}
                  y})
        (letE 'x (plusE (numE 1) (numE 2))
              (idE 'y)))
  (test (parse `{lambda {x} 9})
        (lamE 'x (numE 9)))
  (test (parse `{double 9})
        (appE (idE 'double) (numE 9)))
  (test/exn (parse `{{+ 1 2}})
            "invalid input")
  (test (parse `{if {= 1 1} 1 0})
        (ifE (eqE (numE 1) (numE 1)) (numE 1) (numE 0)))
  (test (parse `{unlet x 1})
        (unletE 'x (numE 1)))
  (test (interp (parse `{unlet x 1}) mt-env)
        (numV 1))

  ;;new-tests-------------------------------------------
  (test/exn (interp (parse `{let {[x 1]}
                              {unlet x
                                     x}})
                    mt-env)
            "free variable")
  (test (interp (parse `{let {[x 1]}
                          {+ x {unlet x 1}}})
                mt-env)
        (interp (parse `2) mt-env))
  (test (interp (parse `{let {[x 1]}
                          {let {[x 2]}
                            {+ x {unlet x x}}}})
                mt-env)
        (interp (parse `3) mt-env))
  (test (interp (parse `{let {[x 1]}
                          {let {[x 2]}
                            {let {[z 3]}
                              {+ x {unlet x {+ x z}}}}}})
                mt-env)
        (interp (parse `6) mt-env))
  (test (interp (parse `{let {[f {lambda {z}
                                   {let {[z 8]}
                                     {unlet z
                                            z}}}]}
                          {f 2}})
                mt-env)
        (interp (parse `2) mt-env))
  )

;; interp ----------------------------------------
(define (interp [a : Exp] [env : Env]) : Value
  (type-case Exp a
    [(numE n) (numV n)]
    [(idE s) (if (equal? (lookup s env) (boolV #f))
                 (error 'interp "free variable")
                 (lookup s env))]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(letE n rhs body) (interp body
                               (extend-env
                                (bind n (interp rhs env))
                                env))]
    [(lamE n body) (closV n body env)]
    [(appE fun arg) (type-case Value (interp fun env)
                      [(closV n body c-env)
                       (interp body
                               (extend-env
                                (bind n
                                      (interp arg env))
                                c-env))]
                      [else (error 'interp "not a function")])]
    [(eqE l r) (if (and
                    (type-case Value (interp l env)
                      [(numV v) #t]
                      [else #f])
                    (type-case Value (interp r env)
                      [(numV v) #t]
                      [else #f]))
                   (boolV (equal? (interp l env) (interp r env)))
                   (error 'interp "not a number")
                   )                   
               ]
    [(ifE bool t f) (cond
                      [(equal? (interp bool mt-env) (boolV #t)) (interp t mt-env)]                        
                      [(equal? (interp bool mt-env) (boolV #f)) (interp f mt-env)]
                      [else (error 'interp "not a boolean")]
                      )]
    [(boolE s) (cond
                 [(equal? s 'true) (boolV #t)]                   
                 [(equal? s 'false) (boolV #f)]
                 [else (error 'interp "not a boolean")]
                 )]
    [(unletE s exp) (interp exp (skip-nearest s env))]
    ))

;;skip-nearest----------------------------------------
(define (skip-nearest [s : Symbol] [env : Env]) : Env
  (type-case Env env
    [empty env]
    [(cons fst rst) (if (equal? (bind-name fst) s)
                       rst
                       (skip-nearest s rst))])
  )

#|
(define (skip-nearest [s : Symbol] [env : Env] [expToUse : Exp] [numTimesInEnv : Value] [numTimesOccuredSoFar : Exp]) : Value
  (type-case Env env
    [empty (interp expToUse mt-env)]
    [(cons fst rst) (if (equal? (bind-name fst) s)
                        (if (equal? (num+ (interp numTimesOccuredSoFar mt-env) (numV 1)) numTimesInEnv)
                            (interp expToUse (extend-env fst env)) 
                            (skip-nearest s rst expToUse numTimesInEnv (plusE numTimesOccuredSoFar (numE 1)))
                            )
                        (skip-nearest s rst expToUse numTimesInEnv numTimesOccuredSoFar)
                        )
                    ])
  )
|#

;;count-num-times-occured------------------------------
(define (count-num-times-occured [s : Symbol] [env : Env] [num : Exp]) : Value
  (type-case Env env
    [empty (interp num env)]
    [(cons fst rst) (if (equal? s (bind-name fst))
                        (count-num-times-occured s rst  (plusE num (numE 1)))
                        (count-num-times-occured s rst num)
                        )]
    ))

(module+ test
  (test (count-num-times-occured 'x (list (bind 'x (numV 10)) (bind 'x (numV 123)) (bind 'y (numV 1))) (numE 0))
        (numV 2))
    (test (count-num-times-occured 'z (list (bind 'x (numV 10)) (bind 'x (numV 123)) (bind 'y (numV 1))) (numE 0))
        (numV 0))
    (test (count-num-times-occured 'y (list (bind 'x (numV 10)) (bind 'x (numV 123)) (bind 'y (numV 1))) (numE 0))
        (numV 1))
    (test (count-num-times-occured 'x (list (bind 'x (numV 10)) (bind 'x (numV 123)) (bind 'x (numV 1)) (bind 'x (numV 4)) (bind 'x (numV 5))) (numE 0))
        (numV 5))
  (test (count-num-times-occured 'z mt-env (numE 0))
        (numV 0))
  
  #|(test (skip-nearest 'x (list (bind 'x (numV 1)) (bind 'x (numV 2))) (plusE (idE 'x) (numE 1)) (count-num-times-occured 'x (list (bind 'x (numV 1)) (bind 'x (numV 2))) (numE 0)) (numE 0))
      (numV 3))
  (test/exn (skip-nearest 'x mt-env (plusE (idE 'x) (numE 1)) (count-num-times-occured 'x mt-env (numE 0)) (numE 0))
        "free variable")
  |#
  )
  
(module+ test
  (test (parse `{= 2 2})
        (eqE (numE 2) (numE 2)))
  (test (parse `{if true 0 1})
        (ifE (boolE 'true) (numE 0) (numE 1)))
  (test (interp (parse `{if true 0 1})
                mt-env)
        (numV 0))
  (test/exn (interp (parse `{if 1 2 3})
                    mt-env)            
            "not a boolean")
  ;;(test/exn (interp (parse `{= x 3})
    ;;                mt-env)
      ;;      "not a number")
  (test (parse `{= 3 3})
        (eqE (numE 3) (numE 3)))

  (test (interp (parse `{if {= 2 {+ 1 1}} 7 8})
                mt-env)
        (interp (parse `7)
                mt-env))

  (test (interp (parse `{if false {+ 1 {lambda {x} x}} 9})
                mt-env)
        (interp (parse `9)
                mt-env))
  (test (interp (parse `{if true 10 {+ 1 {lambda {x} x}}})
                mt-env)
        (interp (parse `10)
                mt-env))

  )

(module+ test
  (test (interp (parse `2) mt-env)
        (numV 2))
  (test/exn (interp (parse `x) mt-env)
            "free variable")
  (test (interp (parse `x) 
                (extend-env (bind 'x (numV 9)) mt-env))
        (numV 9))
  (test (interp (parse `{+ 2 1}) mt-env)
        (numV 3))
  (test (interp (parse `{* 2 1}) mt-env)
        (numV 2))
  (test (interp (parse `{+ {* 2 3} {+ 5 8}})
                mt-env)
        (numV 19))
  (test (interp (parse `{lambda {x} {+ x x}})
                mt-env)
        (closV 'x (plusE (idE 'x) (idE 'x)) mt-env))
  (test (interp (parse `{let {[x 5]}
                          {+ x x}})
                mt-env)
        (numV 10))
  (test (interp (parse `{let {[x 5]}
                          {let {[x {+ 1 x}]}
                            {+ x x}}})
                mt-env)
        (numV 12))
  (test (interp (parse `{let {[x 5]}
                          {let {[y 6]}
                            x}})
                mt-env)
        (numV 5))
  (test (interp (parse `{{lambda {x} {+ x x}} 8})
                mt-env)
        (numV 16))

  (test/exn (interp (parse `{1 2}) mt-env)
            "not a function")
  (test/exn (interp (parse `{+ 1 {lambda {x} x}}) mt-env)
            "not a number")
  (test/exn (interp (parse `{let {[bad {lambda {x} {+ x y}}]}
                              {let {[y 5]}
                                {bad 2}}})
                    mt-env)
            "free variable")

  #;
  (time (interp (parse `{let {[x2 {lambda {n} {+ n n}}]}
                          {let {[x4 {lambda {n} {x2 {x2 n}}}]}
                            {let {[x16 {lambda {n} {x4 {x4 n}}}]}
                              {let {[x256 {lambda {n} {x16 {x16 n}}}]}
                                {let {[x65536 {lambda {n} {x256 {x256 n}}}]}
                                  {x65536 1}}}}}})
                mt-env)))

;; num+ and num* ----------------------------------------
(define (num-op [op : (Number Number -> Number)] [l : Value] [r : Value]) : Value
  (cond
   [(and (numV? l) (numV? r))
    (numV (op (numV-n l) (numV-n r)))]
   [else
    (error 'interp "not a number")]))
(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

(module+ test
  (test (num+ (numV 1) (numV 2))
        (numV 3))
  (test (num* (numV 2) (numV 3))
        (numV 6)))

;; lookup ----------------------------------------
(define (lookup [n : Symbol] [env : Env]) : Value
  (type-case (Listof Binding) env
   [empty (boolV #f)]
   [(cons b rst-env) (cond
                       [(symbol=? n (bind-name b))
                        (bind-val b)]
                       [else (lookup n rst-env)])]))

(module+ test
  (test (lookup 'x mt-env)
            (boolV #f))
  (test (lookup 'x (extend-env (bind 'x (numV 8)) mt-env))
        (numV 8))
  (test (lookup 'x (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'x (numV 8)) mt-env)))
        (numV 9))
  (test (lookup 'y (extend-env
                    (bind 'x (numV 9))
                    (extend-env (bind 'y (numV 8)) mt-env)))
        (numV 8)))