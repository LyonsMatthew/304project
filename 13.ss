;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "C:/304project/chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
	[var-exp
		(id symbol?)]
	[tiny-list-exp
		(body expression?)]
	[lit-exp
		(datum (lambda (x) (ormap (lambda (pred) (pred x)) (list number? vector? boolean? symbol? string? pair? null?))))]
	[lambda-exp-improper-arg
		(ids symbol?)
		(body (list-of expression?))]
	[lambda-exp
		(ids list?)
		(body (list-of expression?))]
	[let-exp
		(vars list?)
		(vals (list-of expression?))
		(body (list-of expression?))]
	[let*-exp
		(vars list?)
		(vals (list-of expression?))
		(body (list-of expression?))]
	[letrec-exp
		(vars list?)
		(vals (list-of expression?))
		(body (list-of expression?))]
	[vector-exp
		(id vector?)]
	[set!-exp
		(var symbol?)
		(val expression?)]
	[if-exp
		(condition expression?)
		(body-true expression?)
		(body-false expression?)]
	[app-exp
		(body (list-of expression?))])

	
	

;; environment type definitions

(define scheme-value?
	(lambda (x) #t))
  
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc
		(name symbol?)])
	 

(define-datatype environment environment?
	(empty-env-record)
	(extended-env-record
		(syms (list-of symbol?))
		(vals (list-of scheme-value?))
		(env environment?)))


	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
	(lambda (datum)
		(cond
			[(symbol? datum) (var-exp datum)]
			[(lambda (x) (ormap (lambda (pred) (pred x)) (list number? vector? boolean? symbol? string? pair? null?))) (lit-exp datum)]
			[(list? datum)
				(cond
					[(eqv? (car datum) 'lambda)
						(cond
							[(null? (cddr datum)) (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
							[else (if (symbol? (2nd datum))
									(lambda-exp-improper-arg (2nd datum) (map parse-exp (cddr datum)))
									(if (not (andmap symbol? (2nd datum)))
										(eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum)
										(lambda-exp (2nd datum) (map parse-exp (cddr datum)))))])]
					[(eqv? (car datum) 'let)
						(cond
							[(null? (cddr datum)) (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
							[(not (list? (2nd datum))) (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
							[(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
							[(not (andmap (lambda (x) (= x 2)) (map length (2nd datum)))) (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
							[(not (andmap symbol? (map car (2nd datum)))) (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
							[else (let-exp (map car (2nd datum)) (map parse-exp (map cadr (2nd datum))) (map parse-exp (cddr datum)))])]
					[(eqv? (car datum) 'let*)
						(cond
							[(null? (cddr datum)) (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
							[(not (list? (2nd datum))) (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
							[(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
							[(not (andmap (lambda (x) (= x 2)) (map length (2nd datum)))) (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
							[(not (andmap symbol? (map car (2nd datum)))) (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
							[else (let*-exp (map car (2nd datum)) (map parse-exp (map cadr (2nd datum))) (map parse-exp (cddr datum)))])]
					[(eqv? (car datum) 'letrec)
						(cond
							[(null? (cddr datum)) (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
							[(not (list? (2nd datum))) (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
							[(not (andmap list? (2nd datum))) (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
							[(not (andmap (lambda (x) (= x 2)) (map length (2nd datum)))) (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
							[(not (andmap symbol? (map car (2nd datum)))) (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
							[else (letrec-exp (map car (2nd datum)) (map parse-exp (map cadr (2nd datum))) (map parse-exp (cddr datum)))])]
					[(eqv? (car datum) 'set!)
						(cond
							[(not (= (length datum) 3)) (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum)]
							[(not (expression? (3rd datum))) (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum)]
							[else (set!-exp (2nd datum) (3rd datum))])]
					[(eqv? (car datum) 'if)
						(cond
							[(not (= (length datum) 4)) (eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum)]
							[else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))])]
					[else 
						(if (null? (cdr datum))
							(tiny-list-exp (parse-exp (1st datum)))
							(app-exp (map parse-exp datum)))])]
			[(vector? datum) (vector-exp datum)]
			[else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
	(lambda (exp)
		(cases expression exp
			[var-exp (id) id]
			[tiny-list-exp (body) (list (unparse-exp body))]
			[lit-exp (id) id]
			[lambda-exp-improper-arg (id body) (append (list 'lambda id) (map unparse-exp body))]
			[lambda-exp (id body) (append (list 'lambda id) (map unparse-exp body))]
			[let-exp (vars vals body) (append (list 'let (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[let*-exp (vars vals body) (append (list 'let* (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[letrec-exp (vars vals body) (append (list 'letrec (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[vector-exp (id) id]
			[set!-exp (var val) (list 'set! var val)]
			[if-exp (condition body-true body-false) (list 'if (unparse-exp condition) (unparse-exp body-true) (unparse-exp body-false))]
			[app-exp (body) (map unparse-exp body)])))








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
		(list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
	(lambda (pred ls)
		(cond
			[(null? ls) #f]
			[(pred (car ls)) 0]
			[else 
				(let ([list-index-r (list-index pred (cdr ls))])
					(if (number? list-index-r) 
						(+ 1 list-index-r) 
						#f))])))

(define apply-env
	(lambda (env sym succeed fail)
		(cases environment env
			[empty-env-record ()
				(fail)]
			[extended-env-record (syms vals env)
				(let ([pos (list-find-position sym syms)])
					(if (number? pos)
						(succeed (list-ref vals pos))
						(apply-env env sym succeed fail)))])))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+


(define global-env init-env)

; top-level-eval evaluates a form in the global environment
(define top-level-eval
	(lambda (form)
		(eval-exp form (empty-env))))

; eval-exp is the main component of the interpreter

(define eval-exp
	(let ([identity-proc (lambda (x) x)])
		(lambda (exp env)
			(cases expression exp
				[lit-exp (datum)
					(if (list? datum)
						(cadr datum)
						datum)]
				[var-exp (id)
					(apply-env env
						id
						identity-proc
						(lambda ()
							(apply-env global-env
								id
								identity-proc
								(lambda ()
									(error 'apply-env "variable ~s is not bound" id)))))]
				[app-exp (body)
					(let ([proc-value (eval-exp (car body) env)] 
						[args (eval-rands (cdr body) env)])
						(apply-proc proc-value args))]
				[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(map (lambda (e) (eval-exp e env) )
			rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
			[prim-proc (op) (apply-prim-proc op args)]
			[else (eopl:error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons =))

(define init-env         ; for now, our initial global environment only contains 
	(extend-env 
		*prim-proc-names*
		(map prim-proc *prim-proc-names*)
		(empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
	(lambda (prim-proc args)
		(case prim-proc
			[(+) (apply + args)]
			[(-) (apply - args)]
			[(*) (apply * args)]
			[(add1) (+ (1st args) 1)]
			[(sub1) (- (1st args) 1)]
			[(cons) (cons (1st args) (2nd args))]
			[(=) (= (1st args) (2nd args))]
			[else (error 'apply-prim-proc "Bad primitive procedure name: ~s" prim-proc)])))

(define rep      ; "read-eval-print" loop.
	(lambda ()
		(display "--> ") ;; notice that we don't save changes to the environment...
		(let ([answer (top-level-eval (parse-exp (read)))])
			(eopl:pretty-print answer)
			(newline)
			(rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
	(lambda (x)
		(top-level-eval (parse-exp x))))









