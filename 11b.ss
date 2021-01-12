(load "chez-init.ss")

(define (lit? x)
  (or
   (number? x)
   (string? x)
   (symbol? x)
   (boolean? x)
   (char? x)
   (and (pair? x)
        (eqv? 'quote (car x)))))

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
   (val lit?)]
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
   (bodies (list-of expression?))]
)

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

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
      (lit-exp datum)]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda )
            (if (null? (cddr datum))
                (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)
                (if (list? (2nd datum))
                    (if (andmap symbol? (2nd datum))
                      (lambda-exp (2nd  datum)
                                (map parse-exp (cddr datum)))
                      (eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum))
                    (let ([split (improper-split (2nd datum))])
                      (improper-lambda-exp (car split)
                                          (cadr split)
                                          (map parse-exp (cddr datum))))))]
       [(eqv? (car datum) 'set! )
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum)
            (set!-exp (2nd datum)
                      (parse-exp (3rd datum))))]
       [(eqv? (car datum) 'if )
        (if (= (length datum) 4)
            (if-exp (parse-exp (2nd datum))
                    (parse-exp (3rd datum))
                    (parse-exp (4th datum)))
            (eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum))]
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
        [(not (list? (2nd exp))) (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" exp)]
        [(ormap (lambda (x) (or (not (pair? x)) (null? (cdr x)) (not (pair? cdr)) (not (null? (cddr x))))) (2nd exp))
          (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list of length 2 ~s" exp)]
        [(not (andmap symbol? (map car (2nd exp)))) (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" exp)]
        [else #f]))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lambda-exp (ids bodies) (append (list 'lambda ids) (map unparse-exp bodies))]
      [improper-lambda-exp (ids extra-id bodies) 
       (append (list 'lambda 
          (if (null? ids)
            extra-id
            (improper-snoc ids extra-id)
          )
        ) 
        (map unparse-exp bodies))
      ]
      [app-exp (rator rands) (map unparse-exp (cons rator rands))]
      [set!-exp (id val) (list 'set! id (unparse-exp val))]
      [lit-exp (val) val]
      [if-exp (condition true false) (cons 'if (map unparse-exp (list condition true false)))]
      [let-exp (ids vals bodies) 
        (append (list 'let (map list ids (map unparse-exp vals))) (map unparse-exp bodies))]
      [named-let-exp (name ids vals bodies)
        (append (list 'let name (map list ids (map unparse-exp vals))) (map unparse-exp bodies))
      ]
      [let*-exp (ids vals bodies)
        (append (list 'let* (map list ids (map unparse-exp vals))) (map unparse-exp bodies))
      ]
      [letrec-exp (ids vals bodies)
        (append (list 'letrec (map list ids (map unparse-exp vals))) (map unparse-exp bodies))
      ]
    )
  )
)

(define improper-snoc
  (lambda (l c)
    (if (null? l)
      c
      (cons (car l) (improper-snoc (cdr l) c))
    )
  )
)