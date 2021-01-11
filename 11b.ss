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
   (bodies (list-of expression?))])

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
     [(lit? datum) (lit-exp datum)]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda)
        (if (list? (2nd datum))
	    (lambda-exp (2nd  datum)
                        (map parse-exp (cddr datum)))
            (let ([split (improper-split (2nd datum))])
              (improper-lambda-exp (car split)
                                   (cadr split)
                                   (map parse-exp (cddr datum)))))]
       [(eqv? (car datum) 'set!)
        (set!-exp (2nd datum)
                  (parse-exp (3rd datum)))]
       [(eqv? (car datum) 'if)
        (if-exp (parse-exp (2nd datum))
                (parse-exp (3rd datum))
                (parse-exp (4th datum)))]
       [(eqv? (car datum) 'let)
        (if (symbol? (2nd datum))
            (named-let-exp (2nd datum)
                           (map 1st (3rd datum))
                           (map parse-exp (map 2nd (3rd datum)))
                           (map parse-exp (cdddr datum)))
            (let-exp (map 1st (2nd datum))
                     (map parse-exp (map 2nd (2nd datum)))
                     (map parse-exp (cddr datum))))]
       [(eqv? (car datum) 'let*)
        (let*-exp (map 1st (2nd datum))
                 (map parse-exp (map 2nd (2nd datum)))
                 (map parse-exp (cddr datum)))]
       [(eqv? (car datum) 'letrec)
        (letrec-exp (map 1st (2nd datum))
                 (map parse-exp (map 2nd (2nd datum)))
                 (map parse-exp (cddr datum)))]
       [else (app-exp (parse-exp (1st datum))
		      (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

;; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
           [var-exp (id) #t]
           [else #f])))
