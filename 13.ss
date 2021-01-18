;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

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
    (val (lambda (val) #t))
    ]
  [if-exp
   (condition expression?)
   (true expression?)
   (false expression?)]
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
   (bodies (list-of expression?))])
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

; Again, you'll probably want to use your code form A11b

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
        (lit-exp datum)
      )
      ]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda )
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
       [(eqv? (car datum) 'set! )
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp
                        "set! expression ~s does not have (only) variable and expression" datum)
            (set!-exp (2nd datum)
                      (parse-exp (3rd datum))))]
       [(eqv? (car datum) 'if )
        (if (= (length datum) 4)
            (if-exp (parse-exp (2nd datum))
                    (parse-exp (3rd datum))
                    (parse-exp (4th datum)))
            (eopl:error 'parse-exp
                        "if-expression ~s does not have (only) test, then, and else" datum))]
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
       [else (if  (list? datum)
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








;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

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
        (eopl:error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (list-ref vals pos)
	      (apply-env env sym)))])))


;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

; To be added in assignment 14.

;--------------------------------------+
;                                      |
;   CONTINUATION DATATYPE and APPLY-K  |
;                                      |
;--------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+
(define (lit? x)
  (or
   (number? x)
   (string? x)
   (symbol? x)
   (boolean? x)
   (char? x)
   (and (pair? x)
        (eqv? 'quote (car x)))))

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
	(apply-env init-env id)]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator)]
              [args (eval-rands rands)])
          (apply-proc proc-value args))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map eval-exp rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons =))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (1st args) (2nd args))]
      [(-) (- (1st args) (2nd args))]
      [(*) (* (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))









