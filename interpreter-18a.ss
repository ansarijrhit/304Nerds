;;  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;;-------------------+
;;                   |
;;    DATATYPES      |
;;                   |
;;-------------------+

;; parsed expression.  You'll probably want to replace this 
;; code with your expression datatype from A11b

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lambda-exp
   (ids (list-of symbol?))
   (bodies (list-of expression?))]
  [improper-lambda-exp
   (ids (list-of symbol?))
   (extra-id symbol?)
   (bodies (list-of expression?))]
  [app-exp
   (rator expression?)
   (rands (list-of expression?))]
  [set!-exp
   (id symbol?)
   (val expression?)]
  [lit-exp 
   (val (lambda (val) #t))]
  [if-exp
   (condition expression?)
   (true expression?)
   (false expression?)]
  [one-armed-if-exp
   (condition expression?)
   (true expression?)]
  [let-exp
   (ids (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]
  [named-let-exp
   (name symbol?)
   (ids (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]
  [let*-exp
   (ids (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]
  [letrec-exp
   (ids (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]
  [cond-exp
   (tuples (list-of (list-of scheme-value?)))]
  [begin-exp
   (bodies (list-of expression?))]
  [or-exp
   (bodies (list-of expression?))]
  [and-exp
   (bodies (list-of expression?))]
  [while-exp
   (test expression?)
   (bodies (list-of expression?))]
  [define-exp
    (id symbol?)
    (val expression?)])


;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals vector?)
   (env environment?)])


;; datatype for procedures.  At first there is only one
;; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (ids (list-of symbol?))
   (bodies (list-of scheme-value?))
   (env environment?)]
  [improper-closure
   (ids (list-of symbol?))
   (extra-id symbol?)
   (bodies (list-of scheme-value?))
   (env environment?)])

(define-datatype reference reference?
  [local-ref
   (vec vector?)
   (index integer?)]
  [global-ref
   (name symbol?)])

;; datatype CPS

(define-datatype continuation continuation?
  [init-k]
  [apply-env-k
   (vals vector?)
   (env environment?)
   (sym symbol?)
   (k continuation?)]
  [apply-env-ref-k
   (vals vector?)
   (env environment?)
   (sym symbol?)
   (k continuation?)]
  [top-level-eval-k
   (id symbol?)
   (bodies (list-of expression?))
   (helper procedure?)
   (k continuation?)]
  [top-level-eval-k2
   (id symbol?)
   (k continuation?)]
  [eval-app-exp-k
   (rands (list-of expression?))
   (env environment?)
   (k continuation?)]
  [eval-app-exp-k2
   (proc-val proc-val?)
   (k continuation?)]
  [eval-if-exp-k
   (true expression?)
   (false expression?)
   (env environment?)
   (k continuation?)]
  [eval-one-armed-if-exp-k
   (true expression?)
   (env environment?)
   (k continuation?)]
  [eval-set!-exp-k
   (env environment?)
   (id symbol?)
   (k continuation?)]
  [eval-set!-exp-k2
   (evaled-val scheme-value?)
   (k continuation?)]
  [map-cps-k
   (proc-cps procedure?)
   (L list?)
   (k continuation?)]
  [map-cps-k2
   (proced-car scheme-value?)
   (k continuation?)]
  [eval-bodies-k
   (bodies (list-of expression?))
   (env environment?)
   (k continuation?)])

(define (apply-k k v)
  (cases continuation k
         [init-k () v]
         [apply-env-k (vals env sym k)
                      (if (number? v)
	                  (apply-k k (vector-ref vals v))
	                  (apply-env env sym k))]
         [apply-env-ref-k (vals env sym k)
                          (if v
      	                      (apply-k k (local-ref vals v))
                              (apply-env-ref env sym k))]
         [top-level-eval-k (id bodies helper k)
                           (hashtable-set! global-env
                                           id
                                           v)
                           (helper (cdr bodies) k)]
         [top-level-eval-k2 (id k)
                            (hashtable-set! global-env id v)]
         [eval-app-exp-k (rands env k)
                         (eval-rands rands
                                     env
                                     (eval-app-exp-k2 v k))]
         [eval-app-exp-k2 (proc-val k)
                          (apply-proc proc-val v k)]
         [eval-if-exp-k (true false env k)
                        (if v
                            (eval-exp true env k)
                            (eval-exp false env k))]
         [eval-one-armed-if-exp-k (true env k)
                                  (if v
                                      (eval-exp true env k)
                                      (apply-k k (void)))]
         [eval-set!-exp-k (env id k)
                          (apply-env-ref env id
                                         (eval-set!-exp-k2 v k))]
         [eval-set!-exp-k2 (evaled-val k)
                           (apply-k k (set-ref! v evaled-val))]
         [map-cps-k (proc-cps L k)
                    (map-cps proc-cps
                             (cdr L)
                             (map-cps-k2 v k))]
         [map-cps-k2 (proced-car k)
                     (apply-k k (cons proced-car v))]
         [eval-bodies-k (bodies env k)
                        (eval-bodies (cdr bodies) env k)]))

;;-------------------+
;;                   |
;;    PARSER         |
;;                   |
;;-------------------+


;; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

;; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;; Again, you'll probably want to use your code form A11b

(define (improper-split ls)
  (let helper ([ls ls] [acc '()])
    (if (pair? ls)
        (helper (cdr ls) (cons (car ls) acc))
        (list (reverse acc) ls))))

(define parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(lit? datum) 
      (if (and (pair? datum) (eqv? 'quote (car datum)))
          (lit-exp (2nd datum))
          (lit-exp datum))]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda)
        (if (null? (cddr datum))
            (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)
            (if (list? (2nd datum))
                (if (andmap symbol? (2nd datum))
                    (lambda-exp (2nd  datum) (map parse-exp (cddr datum)))
                    (eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum))
                (let ([split (improper-split (2nd datum))])
                  (improper-lambda-exp (car split)
                                       (cadr split)
                                       (map parse-exp (cddr datum))))))]
       [(eqv? (car datum) 'set!)
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp
                        "set! expression ~s does not have (only) variable and expression" datum)
            (set!-exp (2nd datum)
                      (parse-exp (3rd datum))))]
       [(eqv? (car datum) 'define)
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp
                        "define expression ~s does not have (only) variable and expression" datum)
            (define-exp (2nd datum)
              (parse-exp (3rd datum))))]
       [(eqv? (car datum) 'if)
        (cond
         [(= (length datum) 4)
          (if-exp (parse-exp (2nd datum))
                  (parse-exp (3rd datum))
                  (parse-exp (4th datum)))]
         [(= (length datum) 3)
          (one-armed-if-exp (parse-exp (2nd datum))
                            (parse-exp (3rd datum)))]
         [else (eopl:error 'parse-exp
                           "if-expression ~s does not have correct number of arguments" datum)])]
       [(eqv? (car datum) 'cond)
        (cond-exp (cdr datum))]
       [(eqv? (car datum) 'begin)
        (begin-exp (map parse-exp (cdr datum)))]
       [(eqv? (car datum) 'or)
        (or-exp (map parse-exp (cdr datum)))]
       [(eqv? (car datum) 'and)
        (and-exp (map parse-exp (cdr datum)))]
       [(eqv? (car datum) 'while)
        (while-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
       [(eqv? (car datum) 'let )
        (if (symbol? (2nd datum))
            (named-let-exp (2nd datum)
                           (map 1st (3rd datum))
                           (map parse-exp (map 2nd (3rd datum)))
                           (map parse-exp (cdddr datum)))
            (let ((error (check-lets datum)))
              (if error
                  error
                  (let-exp (map 1st (2nd datum))
                           (map parse-exp (map 2nd (2nd datum)))
                           (map parse-exp (cddr datum))))))]
       [(eqv? (car datum) 'let* )
        (let  ((error (check-lets datum)))
          (if error
              error
              (let*-exp (map 1st (2nd datum))
                        (map parse-exp (map 2nd (2nd datum)))
                        (map parse-exp (cddr datum)))))]
       [(eqv? (car datum) 'letrec )
        (let  ((error (check-lets datum)))
          (if error
              error
              (letrec-exp (map 1st (2nd datum))
                          (map parse-exp (map 2nd (2nd datum)))
                          (map parse-exp (cddr datum)))))]
       [else (if (list? datum)
                 (app-exp  (parse-exp (1st datum))
		           (map parse-exp (cdr datum)))
                 (eopl:error 'parse-exp "expression ~s is not a proper list" datum))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define (check-lets exp)
  (cond [(null? (cddr exp)) (eopl:error 'parse-exp "~s-expression has incorrect length ~s" exp)]
        [(not (list? (2nd exp)))
         (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" exp)]
        [(ormap (lambda (x)
                  (or (not (pair? x))
                      (null? (cdr x))
                      (not (pair? (cdr x)))
                      (not (null? (cddr x)))))
                (2nd exp))
         (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list of length 2 ~s" exp)]
        [(not (andmap symbol? (map car (2nd exp))))
         (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" exp)]
        [else #f]))

;;-------------------+
;;                   |
;;   ENVIRONMENTS    |
;;                   |
;;-------------------+

;; Environment definitions for CSSE 304 Scheme interpreter.  
;; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

(define list-find-position
  (lambda (sym los k)
    (let loop ([los los] [pos 0] [k k])
      (cond [(null? los) (apply-k k #f)]
	    [(eq? sym (car los)) (apply-k k pos)]
	    [else (loop (cdr los) (add1 pos) k)]))))

(define apply-env
  (lambda (env sym k) 
    (cases environment env 
           [empty-env-record ()
                             (apply-k k (apply-global-env sym))]
           [extended-env-record (syms vals env)
                                (list-find-position sym
                                                    syms
                                                    (apply-env-k vals env sym k))])))

(define (apply-env-ref env sym k)
  (cases environment env 
         [empty-env-record ()
                           (apply-k k (apply-global-env-ref sym))]
         [extended-env-record (syms vals env)
                              (list-find-position sym
                                                  syms
                                                  (apply-env-ref-k vals env sym k))]))

(define (deref ref)
  (cases reference ref
         [local-ref (vec index)
                    (vector-ref vec index)]
         [global-ref (name)
                     (hashtable-ref global-env name #f)]))

(define (set-ref! ref value)
  (cases reference ref
         [local-ref (vec index)
                    (vector-set! vec index value)]
         [global-ref (name)
                     (hashtable-set! global-env name value)]))

(define (apply-global-env-ref sym)
  (if (hashtable-contains? global-env sym)
      (global-ref sym)
      (eopl:error 'apply-global-env-ref "Global environment does not contain symbol ~a" sym)))

(define apply-global-env
  (lambda (sym)
    (let ([result (hashtable-ref global-env sym #f)])
      (if result
          result
          (eopl:error 'apply-global-env "Global environment does not contain symbol ~a" sym)))))

;;-----------------------+
;;                       |
;;   SYNTAX EXPANSION    |
;;                       |
;;-----------------------+

(define (syntax-expand exp)
  (cases expression exp
         [lit-exp (datum) exp]
         [var-exp (id) exp]
         [app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]
         [if-exp (condition true false)
                 (if-exp (syntax-expand condition)
                         (syntax-expand true)
                         (syntax-expand false))]
         [one-armed-if-exp (condition true)
                           (one-armed-if-exp (syntax-expand condition)
                                             (syntax-expand true))]
         [lambda-exp (ids bodies)
                     (lambda-exp ids
                                 (map syntax-expand bodies))]
         [improper-lambda-exp (ids extra-id bodies)
                              (improper-lambda-exp ids extra-id (map syntax-expand bodies))]
         [cond-exp (tuples)
                   (cond
                    [(null? (cdr tuples))
                     (if (eq? (caar tuples) 'else)
                         (syntax-expand (parse-exp (cadar tuples)))
                         (one-armed-if-exp (syntax-expand (parse-exp (caar tuples)))
                                           (syntax-expand (parse-exp (cadar tuples)))))]
                    [else (if-exp (syntax-expand (parse-exp (caar tuples)))
                                  (syntax-expand (parse-exp (cadar tuples)))
                                  (syntax-expand (cond-exp (cdr tuples))))])]
         [let-exp (ids vals bodies)
                  (app-exp
                   (lambda-exp ids (map syntax-expand bodies))
                   (map syntax-expand vals))]
         [named-let-exp (name ids vals bodies)
                        (letrec-exp (list name)
                                    (list (lambda-exp ids (map syntax-expand bodies)))
                                    (list (app-exp (var-exp name) (map syntax-expand vals))))]
         [letrec-exp (ids vals bodies)
                     (letrec-exp
                      ids
                      (map syntax-expand vals)
                      (map syntax-expand bodies))]
         [begin-exp (bodies)
                    (app-exp (lambda-exp '() (map syntax-expand bodies)) '())]
         [or-exp (bodies)
                 (let ([t (gensym)])
                   (syntax-expand
                    (if (null? bodies)
                        (lit-exp #f)
                        (let-exp (list t)
                                 (list (syntax-expand (1st bodies)))
                                 (list (if-exp (var-exp t)
                                               (var-exp t)
                                               (or-exp (cdr bodies))))))))]
         [and-exp (bodies)
                  (let ([t (gensym)])
                    (syntax-expand
                     (cond
                      [(null? bodies) (lit-exp #t)]
                      [(null? (cdr bodies))
                       (let-exp (list t)
                                (list (syntax-expand (1st bodies)))
                                (list (if-exp (var-exp t)
                                              (var-exp t)
                                              (lit-exp #f))))]
                      [else
                       (if-exp (syntax-expand (car bodies))
                               (syntax-expand (and-exp (cdr bodies)))
                               (lit-exp #f))])))]
         [let*-exp (ids vals bodies)
                   (syntax-expand
                    (if (null? ids)
                        (let-exp '()
                                 '()
                                 bodies)
                        (let-exp (list (1st ids))
                                 (list (1st vals))
                                 (list (let*-exp (cdr ids)
                                                 (cdr vals)
                                                 bodies)))))]
         [while-exp (test bodies)
                    (let ([t (gensym)])
                      (letrec-exp (list t)
                                  (list
                                   (lambda-exp '()
                                               (list
                                                (one-armed-if-exp
                                                 (syntax-expand test)
                                                 (syntax-expand
                                                  (begin-exp
                                                   (append (map syntax-expand bodies)
                                                           (list (app-exp (var-exp t) '())))))))))
                                  (list (app-exp (var-exp t) '()))))]
         [set!-exp (id val)
                   (set!-exp id (syntax-expand val))]
         [else exp#;(eopl:error 'syntax-expand "Bad abstract syntax: ~a" exp)]))

;;--------------------------------------+
;;                                      |
;;   CONTINUATION DATATYPE and APPLY-K  |
;;                                      |
;;--------------------------------------+

;; To be added in assignment 18a.


;;-------------------+
;;                   |
;;   INTERPRETER     |
;;                   |
;;-------------------+
(define (lit? x)
  (or
   (number? x)
   (string? x)
   (symbol? x)
   (boolean? x)
   (char? x)
   (and (pair? x)
        (eqv? 'quote (car x)))))

;; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form k)
    ;; later we may add things that are not expressions.
    (cases expression form
           [begin-exp (bodies)
                      (let helper ([bodies bodies] [k k])
                        (if (null? bodies)
                            (apply-k (void))
                            (cases expression (car bodies)
                                   [define-exp (id val)
                                     (eval-exp (syntax-expand val) (empty-env)
                                               (top-level-eval-k id bodies helper k))]
                                   [else (eval-exp (syntax-expand (begin-exp bodies))
                                                   (empty-env) k)])))]
           [define-exp (id val)
             (eval-exp (syntax-expand val) (empty-env)
                       (top-level-eval-k2 id k))]
           [else
            (eval-exp (syntax-expand form) (empty-env) k)])))

;; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env k)
    (cases expression exp
           [lit-exp (datum) (apply-k k datum)]
           [var-exp (id)
	            (apply-env env id k)]
           [app-exp (rator rands)
                    (eval-exp rator
                              env
                              (eval-app-exp-k rands env k))]
           ;; (let ([proc-value (eval-exp rator env)]
           ;;       [args (eval-rands rands env)])
           ;;  (apply-proc proc-value args))]
           [if-exp (condition true false)
                   (eval-exp condition env
                             (eval-if-exp-k true false env k))]
           [one-armed-if-exp (condition true)
                             (eval-exp condition env
                                       (eval-one-armed-if-exp-k true env k))]
           [lambda-exp (ids bodies)
                       (apply-k k (closure ids bodies env))]
           [improper-lambda-exp (ids extra-id bodies)
                                (apply-k k (improper-closure ids extra-id bodies env))]
           [letrec-exp (ids vals bodies)
                       (eval-bodies bodies
                                    (extend-env-recursively ids
                                                            vals
                                                            env)
                                    k)]
           [set!-exp (id val)
                     (eval-exp val
                               env
                               (eval-set!-exp-k env id k))]
           [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

;; evaluate the list of operands, putting results into a list

(define (extend-env-recursively ids vals old-env)
  (let ([len (length ids)])
    (let ([vec (make-vector len)])
      (let ([env (extended-env-record ids
                                      vec
                                      old-env)])
        (for-each (lambda (index lambda-ids lambda-bodies)
                    (vector-set! vec
                                 index
                                 (closure lambda-ids lambda-bodies env)))
                  (iota len)
                  (map 2nd vals)
                  (map 3rd vals))
        env))))

(define (map-cps proc-cps L k)
  (if (null? L)
      (apply-k k '())
      (proc-cps (car L)
                (map-cps-k proc-cps L k))))

(define eval-rands
  (lambda (rands env k)
    (map-cps (lambda (rand k2) (eval-exp rand env k2))
             rands
             k)))

(define eval-bodies
  (lambda (bodies env k)
    (if (null? (cdr bodies))
        (eval-exp (car bodies) env k)
        (eval-exp (car bodies)
                  env
                  (eval-bodies-k bodies env k)))))

;;  Apply a procedure to its arguments.
;;  At this point, we only have primitive procedures.  
;;  User-defined procedures will be added later.

(define (group-extras ls n)
  (if (= 0 n)
      (list ls)
      (cons (car ls) (group-extras (cdr ls) (1- n)))))

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
           [prim-proc (op) (apply-prim-proc op args k)]
           [closure (ids bodies env)
                    (eval-bodies bodies (extend-env ids args env) k)]
           [improper-closure (ids extra-id bodies env)
                             (eval-bodies bodies
                                          (extend-env (append ids (list extra-id))
                                                      (group-extras args (length ids)) env)
                                          k)]
           [else (eopl:error 'apply-proc
                             "Attempt to apply bad procedure: ~s" 
                             proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 1+ 1- zero? not = < > <= >= cons car cdr list null?
                              assq eq? equal? atom? length list->vector list? pair? procedure?
                              vector->list vector make-vector vector-ref vector? number? symbol?
                              set-car! set-cdr! vector-set! display newline caar cadr cdar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr map apply quotient
                              negative? positive? eqv? append list-tail newline display printf
                              pretty-print))

(define init-env
  (make-eq-hashtable))
(for-each
 (lambda (name)
   (hashtable-set! init-env name (prim-proc name)))
 *prim-proc-names*)

(define global-env init-env)

(define (reset-global-env)
  (set! global-env init-env))

;; Usually an interpreter must define each 
;; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args k)
    #;(cond
    [(list-find-position prim-proc '(+ - * / = < > <= >= list vector))
    (apply (eval prim-proc) args)]
    [(list-find-position prim-proc '(cons assq eq? equal? make-vector vector-ref set-car! set-cdr!))
    ((eval prim-proc) (1st args) (2nd args))]
    [(equal? prim-proc 'vector-set!)
    (vector-set! (1st args) (2nd args) (3rd args))]
    [(equal? prim-proc 'newline)
    (newline)]
    [(equal? prim-proc 'procedure?)
    (proc-val? (1st args))]
    [else
    ((eval prim-proc) (1st args))])
    (case prim-proc
      [(map)
       (apply map (cons (lambda x (apply-proc (1st args) x k)) (cdr args)))]
      [(apply) (apply-proc (1st args) (2nd args) k)]

      [(+) (apply-k k (apply + args))]
      [(-) (apply-k k (apply - args))]
      [(*) (apply-k k (apply * args))]
      [(/) (apply-k k (apply / args))]
      [(=) (apply-k k (apply = args))]
      [(<) (apply-k k (apply < args))]
      [(>) (apply-k k (apply > args))]
      [(<=) (apply-k k (apply <= args))]
      [(>=) (apply-k k (apply >= args))]
      [(list) (apply-k k args)]
      [(vector) (apply-k k (apply vector args))]
      [(append) (apply-k k (apply append args))]

      [(quotient) (apply-k k (quotient (1st args) (2nd args)))]
      [(cons) (apply-k k (cons (1st args) (2nd args)))]
      [(assq) (apply-k k (assq (1st args) (2nd args)))]
      [(eq?) (apply-k k (eq? (1st args) (2nd args)))]
      [(equal?) (apply-k k (equal? (1st args) (2nd args)))]
      [(make-vector) (apply-k k (make-vector (1st args) (2nd args)))]
      [(vector-ref) (apply-k k (vector-ref (1st args) (2nd args)))]
      [(set-car!) (apply-k k (set-car! (1st args) (2nd args)))]
      [(set-cdr!) (apply-k k (set-cdr! (1st args) (2nd args)))]
      [(eqv?) (apply-k k (eqv? (1st args) (2nd args)))]
      [(list-tail) (apply-k k (list-tail (1st args) (2nd args)))]
      
      [(vector-set!) (apply-k k (vector-set! (1st args) (2nd args) (3rd args)))]
      
      [(newline) (apply-k k (newline))]

      [(procedure?) (apply-k k (proc-val? (1st args)))]

      [(add1) (apply-k k (+ (1st args) 1))]
      [(sub1) (apply-k k (- (1st args) 1))]
      [(1+) (apply-k k (+ (1st args) 1))]
      [(1-) (apply-k k (- (1st args) 1))]
      
      [(positive?) (apply-k k (positive? (1st args)))]
      [(negative?) (apply-k k (negative? (1st args)))]
      [(zero?) (apply-k k (zero? (1st args)))]
      [(not) (apply-k k (not (1st args)))]
      [(car) (apply-k k (car (1st args)))]
      [(cdr) (apply-k k (cdr (1st args)))]
      [(null?) (apply-k k (null? (1st args)))]
      [(atom?) (apply-k k (atom? (1st args)))]
      [(length) (apply-k k (length (1st args)))]
      [(list->vector) (apply-k k (list->vector (1st args)))]
      [(list?) (apply-k k (list? (1st args)))]
      [(pair?) (apply-k k (pair? (1st args)))]
      [(vector->list) (apply-k k (vector->list (1st args)))]
      [(vector?) (apply-k k (vector? (1st args)))]
      [(number?) (apply-k k (number? (1st args)))]
      [(symbol?) (apply-k k (symbol? (1st args)))]
      [(display) (apply-k k (display (1st args)))]
      [(caar) (apply-k k (caar (1st args)))]
      [(cadr) (apply-k k (cadr (1st args)))]
      [(cdar) (apply-k k (cdar (1st args)))]
      [(cddr) (apply-k k (cddr (1st args)))]
      [(caaar) (apply-k k (caaar (1st args)))]
      [(caadr) (apply-k k (caadr (1st args)))]
      [(cadar) (apply-k k (cadar (1st args)))]
      [(cdaar) (apply-k k (cdaar (1st args)))]
      [(caddr) (apply-k k (caddr (1st args)))]
      [(cdadr) (apply-k k (cdadr (1st args)))]
      [(cddar) (apply-k k (cddar (1st args)))]
      [(cdddr) (apply-k k (cdddr (1st args)))]

      [(newline) (apply-k k (newline))]
      [(display) (apply-k k (display (1st args)))]
      [(printf) (apply-k k (apply printf args))]
      [(pretty-print) (apply-k k (pretty-print (1st args)))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep ;; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([input (read)])
      (if (equal? input '(exit))
          (void)
          (let ([answer (top-level-eval (parse-exp input))])
            ;; TODO: are there answers that should display differently?
            (cond
             [(proc-val? answer)
              (cases proc-val answer
                     [prim-proc (name) (printf "~d\n" (string-append "#<procedure " (symbol->string name) ">" ))]
                     [else (printf "~d\n" "#<procedure>" )])]
             [(eq? answer (void))]
             [else (eopl:pretty-print answer)])
            (rep))))))  ;; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x) (init-k))))
