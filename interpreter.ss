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
   (tuples (list-of (list-of scheme-value?)))])


;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
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
       [(eqv? (car datum) 'let )
        (let ((error (check-lets datum)))
          (if error
              error
              (if (symbol? (2nd datum))
                  (named-let-exp (2nd datum)
                                 (map 1st (3rd datum))
                                 (map parse-exp (map 2nd (3rd datum)))
                                 (map parse-exp (cdddr datum)))
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
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
	    [(eq? sym (car los)) pos]
	    [else (loop (cdr los) (add1 pos))]))))

(define apply-env
  (lambda (env sym) 
    (cases environment env 
           [empty-env-record ()      
                             (apply-global-env sym)]
           [extended-env-record (syms vals env)
	                        (let ((pos (list-find-position sym syms)))
      	                          (if (number? pos)
	                              (list-ref vals pos)
	                              (apply-env env sym)))])))

(define apply-global-env
  (lambda (sym) 
    (cases environment global-env 
           [empty-env-record ()
                             (eopl:error 'apply-global-env
                                         "Exception: global environment is empty")]

           
           [extended-env-record (syms vals global-env)
	                        (let ((pos (list-find-position sym syms)))
      	                          (if (number? pos)
	                              (list-ref vals pos)
                                      (eopl:error 'apply-global-env
                                                  "Exception: variable ~a is not bound" sym)))])))

;;-----------------------+
;;                       |
;;   SYNTAX EXPANSION    |
;;                       |
;;-----------------------+

(define (syntax-expand exp)
  (cases expression exp
         [lit-exp (datum) exp]
         [var-exp (id) exp]
         [app-exp (rator rands) exp]
         #;          [if-exp (condition true false)
         (if (eval-exp condition env) (eval-exp true env) (eval-exp false env))]
         #;        [one-armed-if-exp (condition true)
         (if (eval-exp condition env) (eval-exp true env) (void))]
         #;      [lambda-exp (ids bodies)
         (closure ids bodies env)]
         #;    [improper-lambda-exp (ids extra-id bodies)
         (improper-closure ids extra-id bodies env)]
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
  (lambda (form)
    ;; later we may add things that are not expressions.
    (eval-exp (syntax-expand form) (empty-env))))

;; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
           [lit-exp (datum) datum]
           [var-exp (id)
	            (apply-env env id)]
           [app-exp (rator rands)
                    (let ([proc-value (eval-exp rator env)]
                          [args (eval-rands rands env)])
                      (apply-proc proc-value args))]
           [if-exp (condition true false)
                   (if (eval-exp condition env) (eval-exp true env) (eval-exp false env))]
           [one-armed-if-exp (condition true)
                             (if (eval-exp condition env) (eval-exp true env) (void))]
           [lambda-exp (ids bodies)
                       (closure ids bodies env)]
           [improper-lambda-exp (ids extra-id bodies)
                                (improper-closure ids extra-id bodies env)]
           [let-exp (ids vals bodies)
                    (let ([evaled-vals (map (lambda (v) (eval-exp v env)) vals)])
                      (eval-bodies
                       bodies
                       (extend-env ids
                                   evaled-vals
                                   env)))]
           [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

;; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (rand) (eval-exp rand env)) rands)))

(define eval-bodies
  (lambda (bodies env)
    (if (null? (cdr bodies))
        (eval-exp (car bodies) env)
        (begin
          (eval-exp (car bodies) env)
          (eval-bodies (cdr bodies) env)))))

;;  Apply a procedure to its arguments.
;;  At this point, we only have primitive procedures.  
;;  User-defined procedures will be added later.

(define (group-extras ls n)
  (if (= 0 n)
      (list ls)
      (cons (car ls) (group-extras (cdr ls) (1- n)))))

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
           [prim-proc (op) (apply-prim-proc op args)]
           [closure (ids bodies env)
                    (eval-bodies bodies (extend-env ids args env))]
           [improper-closure (ids extra-id bodies env)
                             (eval-bodies bodies
                                          (extend-env (append ids (list extra-id))
                                                      (group-extras args (length ids)) env))]
           [else (eopl:error 'apply-proc
                             "Attempt to apply bad procedure: ~s" 
                             proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 1+ 1- zero? not = < > <= >= cons car cdr list null?
                              assq eq? equal? atom? length list->vector list? pair? procedure?
                              vector->list vector make-vector vector-ref vector? number? symbol?
                              set-car! set-cdr! vector-set! display newline caar cadr cdar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr map apply))

(define init-env         ;; for now, our initial global environment only contains 
  (extend-env            ;; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

(define global-env init-env)

;; Usually an interpreter must define each 
;; built-in procedure individually.  We are "cheating" a little bit.

(proc-val? map)

(define apply-prim-proc
  (lambda (prim-proc args)
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
      [(map) (apply map (cons (lambda x (apply-proc (1st args) x)) (cdr args)))]
      [(apply) (apply-proc (1st args) (2nd args))]

      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(=) (apply = args)]
      [(<) (apply < args)]
      [(>) (apply > args)]
      [(<=) (apply <= args)]
      [(>=) (apply >= args)]
      [(list) args]
      [(vector) (apply vector args)]
      [(cons) (cons (1st args) (2nd args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      
      [(newline) (newline)]

      [(procedure?) (proc-val? (1st args))]

      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(1+) (+ (1st args) 1)]
      [(1-) (- (1st args) 1)]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(null?) (null? (1st args))]
      [(atom?) (atom? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(display) (display (1st args))]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cdar) (cdar (1st args))]
      [(cddr) (cddr (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdddr) (cdddr (1st args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ;; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (if (proc-val? answer)
          (cases proc-val answer
                 [prim-proc (name) (printf "~d\n" (string-append "#<procedure " (symbol->string name) ">" ))]
                 [else (printf "~d\n" "#<procedure>" )])
          (eopl:pretty-print answer))
      (newline)
      (rep))))  ;; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
