#lang plait

(require "class.rkt"
         "inherit.rkt")

(define-type ClassT
  (classT [super-name : Symbol]
          [fields : (Listof (Symbol * Type))]
          [methods : (Listof (Symbol * MethodT))]))

(define-type MethodT
  (methodT [arg-type : Type]
           [env : Tenv]
           [result-type : Type]
           [body-expr : ExpI])) 

(define-type Type
  (numT)
  (objT [class-name : Symbol]))

(define-type Binding-T
  (bind-t [name : Symbol]
          [exp : ExpI]))

(define-type-alias Tenv (Listof Binding-T))


(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define (get-all-field-types class-name t-classes)
  (if (equal? class-name 'Object)
      empty        
      (type-case ClassT (find t-classes class-name)
        [(classT super-name fields methods)
         (append 
          (get-all-field-types super-name t-classes)
          (map snd fields))])))

;; ----------------------------------------

(define (make-find-in-tree class-items)
  (lambda (name class-name t-classes)
    (local [(define t-class (find t-classes class-name))
            (define items (class-items t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'Object)
          (find items name)
          (try (find items name)
               (lambda ()
                 ((make-find-in-tree class-items)
                  name 
                  super-name
                  t-classes)))))))

(define find-field-in-tree
  (make-find-in-tree classT-fields))

(define find-method-in-tree
  (make-find-in-tree classT-methods))

;; ----------------------------------------

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(equal? name1 name2) #t]
    [(equal? name1 'Object) #f]
    [else
     (type-case ClassT (find t-classes name1)
       [(classT super-name fields methods)
        (is-subclass? super-name name2 t-classes)])]))

(define (is-subtype? t1 t2 t-classes)
  (type-case Type t1
    [(objT name1)
     (type-case Type t2 
       [(objT name2)
        (is-subclass? name1 name2 t-classes)]
       [else #f])]
    [else (equal? t1 t2)]))

(module+ test
  (define a-t-class (values 'A (classT 'Object empty empty)))
  (define b-t-class (values 'B (classT 'A empty empty)))

  (test (is-subclass? 'Object 'Object empty)
        #t)
  (test (is-subclass? 'A 'B (list a-t-class b-t-class))
        #f)
  (test (is-subclass? 'B 'A (list a-t-class b-t-class))
        #t)

  (test (is-subtype? (numT) (numT) empty)
        #t)
  (test (is-subtype? (numT) (objT 'Object) empty)
        #f)
  (test (is-subtype? (objT 'Object) (numT) empty)
        #f)
  (test (is-subtype? (objT 'A) (objT 'B) (list a-t-class b-t-class))
        #f)
  (test (is-subtype? (objT 'B) (objT 'A) (list a-t-class b-t-class))
        #t))

;; ----------------------------------------

(define typecheck-expr : (ExpI Tenv (Listof (Symbol * ClassT)) Type Type -> Type)
  (lambda (expr env t-classes this-type arg-type)
    (local [(define (recur expr)
              (typecheck-expr expr env t-classes this-type arg-type ))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [(numT)
                 (type-case Type (recur r)
                   [(numT) (numT)]
                   [else (type-error r "num")])]
                [else (type-error l "num")]))]
      (type-case ExpI expr
        [(numI n) (numT)]
        [(plusI l r) (typecheck-nums l r)]
        [(multI l r) (typecheck-nums l r)]
        [(if0I cond tr fls) (local [(define tru (recur tr))]
                              (local [(define flse (recur fls))]
                              (if (equal? (recur cond) (numT))
                                (if (or (is-subtype? tru flse t-classes)
                                        (is-subtype? flse tru t-classes))
                                    tru
                                    (type-error tru "num"))
                                (type-error tru "num"))))]
        [(letI a rhs body) (typecheck-expr body
                                           (extend-env
                                            (bind-t a rhs)
                                            env)
                                           t-classes this-type arg-type)]
        [(idI a) (recur (lookup a env))]
        [(argI) arg-type]
        [(thisI) this-type]
        [(newI class-name exprs)
         (local [(define arg-types (map recur exprs))
                 (define field-types
                   (get-all-field-types class-name t-classes))]
           (if (and (= (length arg-types) (length field-types))
                    (foldl (lambda (b r) (and r b))
                           #t
                           (map2 (lambda (t1 t2) 
                                   (is-subtype? t1 t2 t-classes))
                                 arg-types
                                 field-types)))
               (objT class-name)
               (type-error expr "field type mismatch")))]
        [(getI obj-expr field-name)
         (type-case Type (recur obj-expr)
           [(objT class-name)
            (find-field-in-tree field-name
                                class-name
                                t-classes)]
           [else (type-error obj-expr "object")])]
        [(sendI obj-expr method-name arg-expr)
         (local [(define obj-type (recur obj-expr))
                 (define arg-type (recur arg-expr))]
           (type-case Type obj-type
             [(objT class-name)
              (typecheck-send class-name method-name
                              arg-expr arg-type
                              t-classes)]
             [else
              (type-error obj-expr "object")]))]
        [(superI method-name arg-expr)
         (local [(define arg-type (recur arg-expr))
                 (define this-class
                   (find t-classes (objT-class-name this-type)))]
           (typecheck-send (classT-super-name this-class)
                           method-name
                           arg-expr arg-type
                           t-classes))]))))

(define (lookup [n : Symbol] [env : Tenv]) : ExpI
  (type-case (Listof Binding-T) env
   [empty (error 'lookup "free variable")]
   [(cons b rst-env) (cond
                       [(symbol=? n (bind-t-name b))
                        (bind-t-exp b)]
                       [else (lookup n rst-env)])]))

(define (typecheck-send [class-name : Symbol]
                        [method-name : Symbol]
                        [arg-expr : ExpI]
                        [arg-type : Type]
                        [t-classes : (Listof (Symbol * ClassT))])
  (type-case MethodT (find-method-in-tree
                      method-name
                      class-name
                      t-classes)
    [(methodT arg-type-m env result-type body-expr)
     (if (is-subtype? arg-type arg-type-m t-classes)
         result-type
         (type-error arg-expr (to-string arg-type-m)))]))

(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : (Listof (Symbol * ClassT))]) : ()
  (type-case MethodT method
    [(methodT arg-type env result-type body-expr)
     (if (is-subtype? (typecheck-expr body-expr env t-classes
                                      this-type arg-type)
                      result-type
                      t-classes)
         (values)
         (type-error body-expr (to-string result-type)))]))

(define (check-override [method-name : Symbol]
                        [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : (Listof (Symbol * ClassT))])
  (local [(define super-name 
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (find-method-in-tree method-name
                                  super-name
                                  t-classes)
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             (equal? (methodT-result-type method)
                     (methodT-result-type super-method)))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string method-name))))))

(define (typecheck-class [class-name : Symbol]
                         [t-class : ClassT]
                         [t-classes : (Listof (Symbol * ClassT))])
  (type-case ClassT t-class
    [(classT super-name fields methods)
     (map (lambda (m)
            (begin
              (typecheck-method (snd m) (objT class-name) t-classes)
              (check-override (fst m) (snd m) t-class t-classes)))
          methods)]))

(define (typecheck [a : ExpI]
                   [env : Tenv]
                   [t-classes : (Listof (Symbol * ClassT))]) : Type
  (begin
    (map (lambda (tc)
           (typecheck-class (fst tc) (snd tc) t-classes))
         t-classes)
    (typecheck-expr a env t-classes (objT 'Object) (numT))))

;; ----------------------------------------

(module+ test
  (test/exn (typecheck (letI 'x (numI 2) (plusI (idI 'y) (idI 'x)))
                   mt-env
                   empty)
        "free variable")
  (test (typecheck (letI 'x (numI 2) (plusI (idI 'x) (idI 'x)))
             mt-env
             empty)
        (numT))
  (test (typecheck (letI 'x (thisI) (idI 'x))
             mt-env
             empty)
        (objT 'Object))
  (define posn-t-class
    (values 'Posn
            (classT 'Object
                    (list (values 'x (numT)) (values 'y (numT)))
                    (list (values 'mdist
                                  (methodT (numT) mt-env (numT) 
                                           (plusI (getI (thisI) 'x) (getI (thisI) 'y))))
                          (values 'addDist
                                  (methodT (objT 'Posn) mt-env (numT)
                                           (plusI (sendI (thisI) 'mdist (numI 0))
                                                  (sendI (argI) 'mdist (numI 0)))))))))

  (define posn3D-t-class 
    (values 'Posn3D
            (classT 'Posn
                    (list (values 'z (numT)))
                    (list (values 'mdist
                                  (methodT (numT) mt-env (numT)
                                           (plusI (getI (thisI) 'z) 
                                                  (superI 'mdist (argI)))))))))

  (define square-t-class 
    (values 'Square
            (classT 'Object
                    (list (values 'topleft (objT 'Posn)))
                    (list))))

  (define (typecheck-posn a)
    (typecheck a mt-env
               (list posn-t-class posn3D-t-class square-t-class)))
  
  (define new-posn27 (newI 'Posn (list (numI 2) (numI 7))))
  (define new-posn531 (newI 'Posn3D (list (numI 5) (numI 3) (numI 1))))

  (test (typecheck-posn (sendI new-posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI new-posn531 'mdist (numI 0)))
        (numT))  
  (test (typecheck-posn (sendI new-posn531 'addDist new-posn27))
        (numT))  
  (test (typecheck-posn (sendI new-posn27 'addDist new-posn531))
        (numT))

  (test (typecheck-posn (newI 'Square (list (newI 'Posn (list (numI 0) (numI 1))))))
        (objT 'Square))
  (test (typecheck-posn (newI 'Square (list (newI 'Posn3D (list (numI 0) (numI 1) (numI 3))))))
        (objT 'Square))
  
  (test (typecheck (multI (numI 1) (numI 2))
                   mt-env
                   empty)
        (numT))
  (test (typecheck (if0I (numI 2) (numI 1) (numI 2))
                   mt-env
                   empty)
        (numT))
  (test/exn (typecheck (if0I (newI 'Object empty) (numI 1) (numI 2))
                       mt-env
                   empty)
        "no type")
  (test (typecheck (if0I (numI 2) (newI 'Object empty) (newI 'Object empty))
                   mt-env
                   empty)
        (objT 'Object))
  
  (test/exn (typecheck (if0I (numI 2) (numI 10) (newI 'Object empty))
                       mt-env
                   empty)
        "no type")
  
  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI new-posn27 'mdist new-posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object empty))
                       mt-env
                       empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'Object empty) (numI 1))
                       mt-env
                       empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'Object (list (numI 1))))
                       mt-env
                       empty)
            "no type")
  (test/exn (typecheck (getI (numI 1) 'x)
                       mt-env
                       empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       mt-env
                       (list posn-t-class
                             (values 'Other
                                     (classT 'Posn
                                             (list)
                                             (list (values 'mdist
                                                           (methodT (objT 'Object) mt-env (numT)
                                                                    (numI 10))))))))
            "bad override")
  (test/exn (typecheck-method (methodT (numT) mt-env (objT 'Object) (numI 0)) (objT 'Object) empty)
            "no type")
  (test (typecheck (idI 'x)
             (list (bind-t 'x (numI 1)))
             empty)
        (numT))
  (test (typecheck (plusI (idI 'x) (numI 1))
             (list (bind-t 'x (numI 2)))
             empty)
        (numT))
  (test/exn (typecheck (numI 0)
                       mt-env
                       (list square-t-class
                             (values 'Cube
                                     (classT 'Square
                                             empty
                                             (list
                                              (values 'm
                                                      (methodT (numT) mt-env (numT)
                                                               ;; No such method in superclass:
                                                               (superI 'm (numI 0)))))))))
            "not found"))

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [(classT super-name fields methods)
       (classI
        super-name
        (map fst fields)
        (map (lambda (m)
               (values (fst m)
                       (type-case MethodT (snd m)
                         [(methodT arg-type mt-env xrresult-type body-expr)
                          body-expr])))
             methods))])))
  
(define interp-t : (ExpI (Listof (Symbol * ClassT)) -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map (lambda (c)
                     (values (fst c) (strip-types (snd c))))
                   t-classes))))

(module+ test
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))
  
  (test (interp-t-posn (sendI new-posn27 'mdist (numI 0)))
        (numV 9))  
  (test (interp-t-posn (sendI new-posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI new-posn531 'addDist new-posn27))
        (numV 18))
  (test (interp-t-posn (sendI new-posn27 'addDist new-posn531))
        (numV 18)))

