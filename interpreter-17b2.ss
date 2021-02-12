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
  [lex-exp 
    (depth integer?)
    (pos integer?)]
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
   (id expression?)
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
            (set!-exp (var-exp (2nd datum))
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
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
	    [(eq? sym (car los)) pos]
	    [else (loop (cdr los) (add1 pos))]))))

; (define apply-env
;   (lambda (env sym) 
;     (cases environment env 
;            [empty-env-record ()      
;                              (apply-global-env sym)]
;            [extended-env-record (syms vals env)
; 	                        (let ((pos (list-find-position sym syms)))
;       	                          (if (number? pos)
; 	                              (vector-ref vals pos)
; 	                              (apply-env env sym)))])))

(define apply-env
  (lambda (env depth pos)
    (cases environment env
      [empty-env-record () 
        (eopl:error 'apply-env "It's not like I like you or anything, BAKA")]
      [extended-env-record (syms vals env)
        (if (> depth 0)
          (apply-env env (- depth 1) pos)
          (vector-ref vals pos)       
        )
      ]
    )
  )
)

(define (apply-env-ref env sym)
  (cases environment env 
         [empty-env-record ()
                           (apply-global-env-ref sym)]
         [extended-env-record (syms vals env)
	                      (let ((pos (list-find-position sym syms)))
                                (if pos
      	                            (local-ref vals pos)
                                    (apply-env-ref env sym)))]))

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
;;    LEXICAL ADDRESS    |
;;                       |
;;-----------------------+

(define lexical-address
  (lambda (exp)
    (let recur ([E exp] [boundvars '()])
    ; (pretty-print E)
      (cases expression E
          [var-exp (id) 
            (let ([adr (symbol-address id boundvars)])
              ; (pretty-print boundvars)
              (if adr
                (lex-exp (1st adr) (2nd adr))
                E
              )
            )
          ]
          [lambda-exp (ids bodies) (lambda-exp ids 
            (map (lambda (ex) (recur ex (cons ids boundvars))) bodies))]
          [improper-lambda-exp (ids extra-id bodies) (improper-lambda-exp id extra-id
            (map (lambda (ex) (recur ex (cons (append ids (list extra-id)) boundvars))) bodies))]
          [letrec-exp (ids vals bodies) (letrec-exp ids
            (map (lambda (ex) (recur ex (cons ids boundvars))) vals)
            (map (lambda (ex) (recur ex (cons ids boundvars))) bodies))]
          [app-exp (rator rands) (app-exp (recur rator boundvars)
            (map (lambda (ex) (recur ex boundvars)) rands))]
          [set!-exp (id val) (set!-exp (recur id boundvars) (recur val boundvars))]
          [if-exp (condition true false) (if-exp 
            (recur condition boundvars)
            (recur true boundvars)
            (recur false boundvars))]
          [one-armed-if-exp (condition true) (one-armed-if-exp 
            (recur condition boundvars)
            (recur true boundvars))]
          [else E]
      )
    )
  )
)

(define firsts
  (lambda (ls)
    (if (null? ls)
      '()
      (cons (car (car ls)) (firsts (cdr ls)))
    )
  )
)

(define symbol-address
  (lambda (E boundvars)
    (let recur ([boundvars boundvars] [d 0])
      (if (null? boundvars)
        #f
        (or (let recur2 ([boundvars (car boundvars)] [p 0])
                ; (pretty-print (list (car boundvars) E))
                (cond 
                  ((null? boundvars) #f)
                  ((equal? (car boundvars) E)(list d p))
                  (else (recur2 (cdr boundvars) (+ p 1))))
                )
              (recur (cdr boundvars) (+ d 1))
        )
      )
    )
  )
)


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
    (cases expression form
           [begin-exp (bodies)
                      (let helper ([bodies bodies])
                        (if (null? bodies)
                            (void)
                            (cases expression (car bodies)
                                   [define-exp (id val)
                                     (hashtable-set! global-env
                                                     id
                                                     (eval-exp (lexical-address (syntax-expand val)) (empty-env)))
                                     (helper (cdr bodies))]
                                   [else (eval-exp (lexical-address (syntax-expand (begin-exp bodies)))
                                                   (empty-env))])))]
           [define-exp (id val)
             (hashtable-set! global-env id (eval-exp (lexical-address (syntax-expand val)) (empty-env)))]
           [else
            (eval-exp (lexical-address (syntax-expand form)) (empty-env))])))

;; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
           [lex-exp (depth pos) (apply-env env depth pos)]
           [lit-exp (datum) datum]
           [var-exp (id) (apply-global-env id)]
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
           [letrec-exp (ids vals bodies)
                       (eval-bodies bodies
                                    (extend-env-recursively ids
                                                            vals
                                                            env))]
           [set!-exp (id val) 
            (cases expression id
              [lex-exp (depth pos) (change-lex-pointer! env depth pos (eval-exp (syntax-expand val) env))]
              [var-exp (id) (set-ref! (apply-global-env-ref id) (eval-exp (syntax-expand val) env))]
              [else (eopl:error 'eval-exp "set failed")]
            )
           ]
                    ;  (let ([ref (apply-env-ref env id)])
                    ;    (set-ref! ref (eval-exp (syntax-expand val) env)))]
           [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

;; evaluate the list of operands, putting results into a list

(define change-lex-pointer!
  (lambda (env depth pos val)
    (cases environment env
      [empty-env-record () (void)]
      [extended-env-record (syms vals env) 
        (if (> depth 0)
          (change-lex-pointer! env (- depth 1) pos val)
          (vector-set! vals pos val)
        )
      ]
    )
  )
)


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
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr map apply quotient
                              negative? positive? eqv? append list-tail))

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
      [(append) (apply append args)]

      [(quotient) (quotient (1st args) (2nd args))]
      [(cons) (cons (1st args) (2nd args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      
      [(newline) (newline)]

      [(procedure?) (proc-val? (1st args))]

      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(1+) (+ (1st args) 1)]
      [(1-) (- (1st args) 1)]
      
      [(positive?) (positive? (1st args))]
      [(negative?) (negative? (1st args))]
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
  (lambda (x) (top-level-eval (parse-exp x))))
