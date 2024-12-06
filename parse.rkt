#lang racket
(provide parse parse-e parse-define)
(require "ast.rkt")

;; S-Expr ... -> Prog
(define (parse . s)
  (match s
    [(cons (and (cons 'define _) d) s)
     (match (apply parse s)
       [(Prog ds e)
        (Prog (cons (parse-define d) ds) e)])]
    [(cons e '()) (Prog '() (parse-e e))]
    [_ (error "program parse error")]))

;; S-Expr -> Defn
(define (parse-define s)
  (match s
    [(list 'define (? symbol? f)
           (cons 'case-lambda cs))
     (Defn f (FunCase (parse-case-lambda-clauses cs)))]    
    [(list 'define (cons (? symbol? f) xs) e)
     (if (all symbol? xs)
         (Defn f (parse-param-list xs e))
         (error "parse definition error"))]
    [_ (error "Parse defn error" s)]))

;; like andmap, but work on improper lists too
(define (all p? xs)
  (match xs
    ['() #t]
    [(cons x xs) (and (p? x) (all p? xs))]
    [x (p? x)]))

;; S-Expr -> [Listof FunCaseClause]
(define (parse-case-lambda-clauses cs)
  (match cs
    ['() '()]
    [(cons c cs)
     (cons (parse-case-lambda-clause c)
           (parse-case-lambda-clauses cs))]
     [_
      (error "parse case-lambda error")]))

;; S-Expr -> FunRest
(define (parse-case-lambda-clause c)
  (match c
    [(list (? symbol? x) e)
     (FunRest '() x (parse-e e))]
    [(list xs e)
     (parse-param-list xs e)]))    

;; S-Expr S-Expr -> FunPlain or FunRest
(define (parse-param-list xs e)
  (match xs
    ['() (FunPlain '() (parse-e e))]
    [(cons x xs)
     (match (parse-param-list xs e)
       [(FunPlain xs e) (FunPlain (cons x xs) e)]
       [(FunRest xs y e) (FunRest (cons x xs) y e)])]
    [(? symbol? xs)
     (FunRest '() xs (parse-e e))]
    [_
     (error "parse parameter list error")]))

;; S-Expr -> Expr
(define (parse-e s)
  (match s
    [(? datum?)               (Lit s)]
    ['eof                     (Eof)]
    [(? symbol?)              (Var s)]
    [(list 'quote (list))     (Lit '())]
    [(list (? op0? p0))       (Prim0 p0)]
    [(list (? op1? p1) e)     (Prim1 p1 (parse-e e))]
    [(list (? op2? p2) e1 e2) (Prim2 p2 (parse-e e1) (parse-e e2))]
    [(list (? op3? p3) e1 e2 e3)
     (Prim3 p3 (parse-e e1) (parse-e e2) (parse-e e3))]
    [(list 'begin e1 e2)
     (Begin (parse-e e1) (parse-e e2))]
    [(list 'if e1 e2 e3)
     (If (parse-e e1) (parse-e e2) (parse-e e3))]
    [(list 'let (list (list (? symbol? x) e1)) e2)
     (Let x (parse-e e1) (parse-e e2))]
    [(cons 'apply (cons (? symbol? f) es))
     (parse-apply f es)]
    [(cons (? symbol? f) es)
     (App f (map parse-e es))]
    [_ (error "Parse error" s)]))

;; Id S-Expr -> Expr
(define (parse-apply f es)
  (match es
    [(list e) (Apply f '() (parse-e e))]
    [(cons e es)
     (match (parse-apply f es)
       [(Apply f es e0)
        (Apply f (cons (parse-e e) es) e0)])]
    [_ (error "parse apply error")]))

;; Any -> Boolean
(define (datum? x)
  (or (exact-integer? x)
      (boolean? x)
      (char? x)
      (string? x)))

;; Any -> Boolean
(define (op0? x)
  (memq x '(read-byte peek-byte void)))

(define (op1? x)
  (memq x '(add1 sub1 zero? char? integer->char char->integer
                 write-byte eof-object?
                 box unbox empty? cons? box? car cdr
                 vector? vector-length string? string-length)))

(define (op2? x)
  (memq x '(+ - < = eq? cons
              make-vector vector-ref make-string string-ref)))

(define (op3? x)
  (memq x '(vector-set!)))

