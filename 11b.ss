(load "chez-init.ss")

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lambda-exp
   (id (list-of symbol?))
   (body (list-of expression?))]
  [app-exp
   (rator expression?)
   (rand expression?)]
  [set!-exp
   (id symbol?)
   (val expression?)]
  [lit-exp
   (val number?)])

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(number? datum) (lit-exp datum)]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda)
	(lambda-exp (2nd  datum)
		    (map parse-exp (cddr datum)))]
       [(eqv? (car datum) 'set!)
        (set!-exp (2nd datum)
                  (parse-exp (3rd datum)))]
       [else (app-exp (parse-exp (1st datum))
		      (parse-exp (2nd datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

;; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
           [var-exp (id) #t]
           [else #f])))

(parse-exp '(lambda (x y z) a (lambda (t) z) c))
(parse-exp '(set! x 3))
