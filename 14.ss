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
	[quote-exp
		(body expression?)]
	[lit-exp
		(datum (lambda (x) (ormap (lambda (pred) (pred x)) (list number? vector? boolean? symbol? string? pair? null? (lambda (x) (equal? (void) x))))))]
	[lambda-exp-vararg
		(ids symbol?)
		(body (list-of expression?))]
	[lambda-exp-improper
		(ids (list-of symbol?))
		(more-ids symbol?)
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
	[if-pirate-exp
		(condition expression?)
		(body-true expression?)]
	[cond-exp
		(conditions (list-of expression?))
		(bodies (list-of expression?))]
	[begin-exp
		(bodies (list-of expression?))]
	[and-exp
		(conditions (list-of expression?))]
	[or-exp
		(conditions (list-of expression?))]
	[case-exp
		(val expression?)
		(conditions (list-of expression?))
		(bodies (list-of expression?))]
	[while-exp
		(condition expression?)
		(bodies (list-of expression?))]
	[app-exp
		(body (list-of expression?))])




;; environment type definitions

(define scheme-value?
	(lambda (x) #t))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype environment environment?
	(empty-env-record)
	(extended-env-record
		(syms (list-of symbol?))
		(vals (list-of scheme-value?))
		(env environment?)))

(define-datatype proc-val proc-val?
	[prim-proc
		(name symbol?)]
	[closure
		(ids (list-of symbol?))
		(body (list-of expression?))
		(env environment?)]
	[closure-varargs
		(ids symbol?)
		(body (list-of expression?))
		(env environment?)]
	[closure-improper
		(ids (list-of symbol?))
		(more-ids symbol?)
		(body (list-of expression?))
		(env environment?)])




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

(define get-proper-part
	(lambda (ls)
		(if (not (pair? ls))
			'()
			(cons (car ls) (get-proper-part (cdr ls))))))

(define get-improper-part
	(lambda (ls)
		(if (not (pair? ls))
			ls
			(get-improper-part (cdr ls)))))

(define parse-exp
	(lambda (datum)
		(cond
			[(symbol? datum) (var-exp datum)]
			[(list? datum)
				(cond
					[(eqv? (car datum) 'lambda)
						(cond
							[(null? (cddr datum)) (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
							[else (cond
									[(symbol? (2nd datum)) (lambda-exp-vararg (2nd datum) (map parse-exp (cddr datum)))]
									[(list? (2nd datum)) (if (not (andmap symbol? (2nd datum)))
										(eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum)
										(lambda-exp (2nd datum) (map parse-exp (cddr datum))))]
									[else (lambda-exp-improper (get-proper-part (2nd datum)) (get-improper-part (2nd datum)) (map parse-exp (cddr datum)))])])]
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
							[(not (= (length datum) 4))
								(if (= (length datum) 3)
									(if-pirate-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))
									(eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum))]
							[else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))])]
					[(eqv? (car datum) 'cond)
						(if (= (length datum) 1)
							(eopl:error 'parse-exp "cond-expression ~s does not have bodies" datum)
							(cond-exp
								(map (lambda (x)
									(if (equal? (car x) 'else)
										(parse-exp #t)
										(parse-exp (car x))))
								(cdr datum))
								(map (lambda (x)
									(parse-exp (2nd x)))
								(cdr datum))))]
					[(eqv? (car datum) 'begin)
						(begin-exp (map parse-exp (cdr datum)))]
					[(eqv? (car datum) 'and)
						(and-exp (map parse-exp (cdr datum)))]
					[(eqv? (car datum) 'or)
						(or-exp (map parse-exp (cdr datum)))]
					[(eqv? (car datum) 'case)
						(case-exp (parse-exp (2nd datum))
							(map (lambda (x)
								(parse-exp (car x)))
							(cddr datum))
							(map (lambda (x)
								(parse-exp (2nd x)))
							(cddr datum)))]
					[(eqv? (car datum) 'while)
						(while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
					[(eqv? (car datum) 'quote)
						(if (null? (cadr datum))
							(lit-exp '())
							(quote-exp (lit-exp (cadr datum))))]
					[else
						(if (null? (cdr datum))
							(tiny-list-exp (parse-exp (1st datum)))
							(app-exp (map parse-exp datum)))])]
			[(lambda (x) (ormap (lambda (pred) (pred x)) (list number? vector? boolean? symbol? string? pair? null?))) (lit-exp datum)]
			[(vector? datum) (vector-exp datum)]
			[else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
	(lambda (exp)
		(cases expression exp
			[var-exp (id) id]
			[tiny-list-exp (body) (list (unparse-exp body))]
			[lit-exp (id) id]
			[lambda-exp-vararg (id body) (append (list 'lambda id) (map unparse-exp body))]
			[lambda-exp-improper (ids more-ids body) (append (list 'lambda (build-improper-lambda ids more-ids)) (map unparse-exp body))]
			[lambda-exp (id body) (append (list 'lambda id) (map unparse-exp body))]
			[let-exp (vars vals body) (append (list 'let (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[let*-exp (vars vals body) (append (list 'let* (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[letrec-exp (vars vals body) (append (list 'letrec (map list vars (map unparse-exp vals))) (map unparse-exp body))]
			[vector-exp (id) id]
			[set!-exp (var val) (list 'set! var val)]
			[if-exp (condition body-true body-false) (list 'if (unparse-exp condition) (unparse-exp body-true) (unparse-exp body-false))]
			[if-pirate-exp (condition body-true) (list 'if (unparse-exp condition) (unparse-exp body-true))]
			[cond-exp (conditions bodies) (append (list 'cond) (map (lambda (x y)
				(if (boolean? (unparse-exp x))
					(list 'else (unparse-exp y))
					(list (unparse-exp x) (unparse-exp y))))
				conditions bodies))]
			[begin-exp (bodies) (append (list 'begin) (map unparse-exp bodies))]
			[and-exp (bodies) (append (list 'and) (map unparse-exp bodies))]
			[or-exp (bodies) (append (list 'or) (map unparse-exp bodies))]
			[case-exp (val conditions bodies) (append (list 'case (unparse-exp val))
				(map (lambda (x y)
					(list (unparse-exp x) (unparse-exp y)))
				conditions
				bodies))]
			[while-exp (condition bodies) (append (list 'while (unparse-exp condition)) (map unparse-exp bodies))]
			[quote-exp (body) (unparse-exp body)]
			[app-exp (body) (map unparse-exp body)])))

(define build-improper-lambda
	(lambda (ids more-ids)
		(if (null? ids)
			more-ids
			(cons (car ids) (build-improper-lambda (cdr ids) more-ids)))))








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

(define get-condition
	(lambda (condition)
		(cases expression condition
			[app-exp (body)
				body]
			;[var-exp (body) (list body)]
			[else (list condition)])))

(define case-to-if
	(lambda (val conditions bodies)
			(indv-case-to-if val conditions bodies (get-condition (car conditions)))))

(define indv-case-to-if
	(lambda (val conditions bodies icondition-list)
		(let ([icondition (car icondition-list)] [ibody (car bodies)])
			(if (null? (cdr conditions))
				(if (null? (cdr icondition-list))
					(if (equal? (parse-exp 'else) (car icondition-list))
						(if-pirate-exp (parse-exp #t) ibody)
						(if-exp (get-equality-exp icondition val) ibody (void)))
					(if-exp (get-equality-exp icondition val) ibody (indv-case-to-if val conditions bodies (cdr icondition-list))))
				(if (null? (cdr icondition-list))
					(if-exp (get-equality-exp icondition val) ibody (case-to-if val (cdr conditions) (cdr bodies)))
					(if-exp (get-equality-exp icondition val) ibody (indv-case-to-if val conditions bodies (cdr icondition-list))))))))

(define get-equality-exp
	(lambda (icondition val)
		(app-exp (list (parse-exp 'equal?) icondition val))))


(define let*-builder
	(lambda (vars vals body)
		(if (null? (cdr vars))
			(let-exp (list (car vars)) (list (car vals)) body)
			(let-exp (list (car vars)) (list (car vals)) (list (let*-builder (cdr vars) (cdr vals) body))))))


; To be added later
(define syntax-expand
	(lambda (exp)
		(cases expression exp
			[cond-exp (conditions bodies)
				(let cond-to-if ([conditions (map syntax-expand conditions)] [bodies (map syntax-expand bodies)])
					(if (null? (cdr conditions))
						(if-pirate-exp (car conditions) (car bodies))
						(if-exp (car conditions) (car bodies) (cond-to-if (cdr conditions) (cdr bodies)))))]
			[let-exp (vars vals body)
				(app-exp (append (list (lambda-exp vars (map syntax-expand body))) vals))]
			[let*-exp (vars vals body)
				(syntax-expand (let*-builder vars vals body))]
			[begin-exp (bodies)
				(app-exp (list (lambda-exp '() bodies)))]
			[and-exp (conditions)
				(if (null? conditions)
					(parse-exp #t)
					(let and-to-if ([conditions conditions])
						(if (null? (cdr conditions))
							(syntax-expand (if-exp (car conditions) (car conditions) (lit-exp #f)))
							(syntax-expand (if-exp (car conditions) (and-to-if (cdr conditions)) (lit-exp #f))))))]
			[or-exp (conditions)
				(if (null? conditions)
					(parse-exp #f)
					(let or-to-if ([conditions conditions])
						(if (null? (cdr conditions))
                            (syntax-expand (let-exp (list (parse-exp 'result)) (list (car conditions))
                                (list (if-exp (parse-exp 'result) (parse-exp 'result) (lit-exp #f)))))
                            (syntax-expand (let-exp (list (parse-exp 'result)) (list (car conditions))
                                (list (if-exp (parse-exp 'result) (parse-exp 'result) (or-to-if (cdr conditions)))))))))]
			[app-exp (bodies) (app-exp (map syntax-expand bodies))]
			[lambda-exp (ids body) (lambda-exp ids (map syntax-expand body))]
			[if-exp (condition body-true body-false) (if-exp (syntax-expand condition) (syntax-expand body-true) (syntax-expand body-false))]
			[if-pirate-exp (condition body-true) (if-pirate-exp (syntax-expand condition) (syntax-expand body-true))]
			[case-exp (val conditions bodies)
				(case-to-if val conditions bodies)]
			[else exp])))









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+

(define *prim-proc-names* '(+ - * / add1 sub1 cons = eq? eqv? equal? length list->vector vector->list >= <= car cdr caar cadr cadar caddr list null? list? pair? vector? number? symbol? procedure? zero? not set-car! set-cdr! map apply vector-ref list-ref vector > < vector-set! quotient display newline))

(define init-env         ; for now, our initial global environment only contains
	(extend-env
		*prim-proc-names*
		(map prim-proc *prim-proc-names*)
		(empty-env)))

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
				[lit-exp (datum) datum]
				[quote-exp (body) (eval-exp body env)]
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
				[tiny-list-exp (body) body]
				[if-exp (condition body-true body-false)
					(if (eval-exp condition env)
						(eval-exp body-true env)
						(eval-exp body-false env))]
				[if-pirate-exp (condition body-true)
					(if (eval-exp condition env)
						(eval-exp body-true env))]
				[app-exp (body)
					(let ([proc-value (eval-exp (car body) env)]
						[args (eval-rands (cdr body) env)])
						(apply-proc proc-value args))]
				[let-exp (vars vals body)
					(eval-body body
						(extend-env vars (eval-rands vals env) env))]
				[lambda-exp (ids body)
					(closure ids body env)]
				[lambda-exp-vararg (ids body)
					(closure-varargs ids body env)]
				[lambda-exp-improper (ids more-ids body)
					(closure-improper ids more-ids body env)]
				[while-exp (condition bodies)
					(let while ()
						(if (eval-exp condition env)
							(begin
								(map (lambda (b) (eval-exp b env)) bodies)
								(while))
							(void)))]
				[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(map (lambda (e) (eval-exp e env) )
			rands)))

(define eval-body
	(lambda (body env)
		(if (null? (cdr body))
			(eval-exp (car body) env)
			(begin
				(eval-exp (car body) env)
				(eval-body (cdr body) env)))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
			[prim-proc (op) (apply-prim-proc op args)]
			[closure (ids body env)
				(eval-body body (extend-env ids args env))]
			[closure-varargs (ids body env)
				(eval-body body (extend-env (list ids) (list args) env))]
			[closure-improper (ids more-ids body env)
				(eval-body body (extend-env (append ids (list more-ids)) (append (get-proper-args (length ids) args) (list (get-improper-args (length ids) args))) env))]
			[else (eopl:error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)])))

(define get-proper-args
	(lambda (num args)
		(if (= num 0)
			'()
			(cons (car args) (get-proper-args (- num 1) (cdr args))))))

(define get-improper-args
	(lambda (num args)
		(if (= num 0)
			args
			(get-improper-args (- num 1) (cdr args)))))

; Usually an interpreter must define each
; built-in procedure individually.  We are "cheating" a little bit.

(define custom-map
	(lambda (proc vals)
		(if (null? vals)
			'()
			(cons (apply-proc proc (list (car vals))) (custom-map proc (cdr vals))))))

(define apply-prim-proc
	(lambda (prim-proc args)
		(case prim-proc
			[(+) (apply + args)]
			[(-) (apply - args)]
			[(*) (apply * args)]
			[(/) (apply / args)]
			[(add1) (+ (1st args) 1)]
			[(sub1) (- (1st args) 1)]
			[(cons) (cons (1st args) (2nd args))]
			[(=) (= (1st args) (2nd args))]
			[(eq?) (eq? (1st args) (2nd args))]
			[(eqv?) (eqv? (1st args) (2nd args))]
			[(equal?) (equal? (1st args) (2nd args))]
			[(length) (length (1st args))]
			[(list->vector) (list->vector (1st args))]
			[(vector->list) (vector->list (1st args))]
			[(>=) (>= (1st args) (2nd args))]
			[(<=) (<= (1st args) (2nd args))]
			[(car) (car (1st args))]
			[(cdr) (cdr (1st args))]
			[(caar) (caar (1st args))]
			[(cadr) (cadr (1st args))]
			[(cadar) (cadar (1st args))]
			[(caddr) (caddr (1st args))]
			[(list) (apply list args)]
			[(null?) (null? (1st args))]
			[(list?) (list? (1st args))]
			[(pair?) (list? (1st args))]
			[(vector?) (vector? (1st args))]
			[(number?) (number? (1st args))]
			[(symbol?) (symbol? (1st args))]
			[(procedure?) (proc-val? (1st args))]
			[(zero?) (zero? (1st args))]
			[(not) (not (1st args))]
			[(set-car!) (set-car! (1st args) (2nd args))]
			[(set-cdr!) (set-cdr! (1st args) (2nd args))]
			[(map) (custom-map (1st args) (2nd args))]
			[(apply) (apply apply-proc (1st args) (cdr args))]
			[(list-ref) (list-ref (1st args) (2nd args))]
			[(vector-ref) (vector-ref (1st args) (2nd args))]
			[(vector) (apply vector args)]
			[(<) (< (1st args) (2nd args))]
			[(>) (> (1st args) (2nd args))]
			[(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
			[(quotient) (quotient (1st args) (2nd args))]
			[(display) (display (1st args))]
			[(newline) (newline)]
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
		(top-level-eval (syntax-expand (parse-exp x)))))









