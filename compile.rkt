#lang racket
(provide (all-defined-out))
(require "ast.rkt")
(require "compile-ops.rkt")
(require "types.rkt")
(require "parse.rkt")
(require a86)
(current-objs (list "runtime.o"))
(require a86/ast)

(define rax 'rax)
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r15 'r15) ; stack pad (non-volatile)

;; Prog -> Asm
(define (compile p)
  (match p
    [(Prog ds e)
     (prog (Global 'entry)
           (Extern 'peek_byte)
           (Extern 'read_byte)
           (Extern 'write_byte)
           (Extern 'raise_error)
           (Label 'entry)
           (Push rbx)    ; save callee-saved register
           (Push r15)
           (Mov rbx rdi) ; recv heap pointer

           (compile-e e '())
           (Pop r15)     ; restore callee-save register
           (Pop rbx)
           (Ret)
           (compile-defines ds)
           (Label 'err)
           pad-stack
           (Call 'raise_error))]))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-define d)
          (compile-defines ds))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f fun)
     (compile-fun f fun)]))

;; Id Fun -> Asm
(define (compile-fun f fun)
  (match fun
    [(FunPlain xs e)
     (seq (Label (symbol->label f))
          ;; TODO: check arity
          (Cmp 'r11 (length xs)) ;; loads args len and compares
          (Jne 'err) ;; if not matching, err

          (compile-e e (reverse xs))
          (Add rsp (* 8 (length xs)))
          (Ret))]
    [(FunRest req_args xs e)
      (let ((loop (gensym)) (empty_case (gensym)))
      (seq (Label (symbol->label f))
           (Cmp 'r11 (length req_args)) ;; checking that has required args
           (Jl 'err) ;; not enough args

           (Mov rax (value->bits '())) ;; end list w '()
                                       ;; builds list backwords
           (Sub 'r11 (length req_args)) ;; find out how many are in rest xs list
           (Cmp 'r11 0) ;; empty application jump past loop
           (Jle empty_case)

           (Label loop)
           (Mov (Offset rbx 0) rax) ;; moves ptr into cdr
           (Pop rax) ;; get next element
           (Mov (Offset rbx 8) rax) ;; moves into car of cons
           (Mov rax rbx) ;; gets cdr ptr again
           (Or rax type-cons) ;; cons tags it
           
           (Add rbx 16) ;; increment heap ptr
           
           (Sub 'r11 1)
           (Cmp 'r11 0) ;; uses r11 as our counter
           (Jg loop) ;; will end loop with last cdr ptr/ptr to list
           
           (Label empty_case)

           (Push rax) ;; pushes list ptr to stack to add to env
           (compile-e e (cons xs (reverse req_args)))
           (Add rsp (* 8 (+ 1 (length req_args)))) ;; restores stack
           (Ret)))]
    [(FunCase clauses)
      (seq (Label (symbol->label f)) ;; places main func label
           (compile-lambda clauses (gensym)))] ;; generates random label for first case
    [_
     (seq)]))

(define (compile-lambda clauses l1)
  (match clauses
        ['() (seq)] ;; end/empty list case
        [(cons func rest)
          (let ((next (gensym))) ;; used to "skip" funcs w/ not enough args
          (match func ;; diff types have diff match conditions
            [(FunPlain args e) ;; matches iff arg lens match
              (seq (Cmp 'r11 (length args)) ;; will compare given arg list w/ case
                     (Jne next) ;; does not match arg len, skips to next function
                     (compile-fun (gensym) func) ;; compile current function
                     (Label next)
                     (compile-lambda rest (gensym)) ;; recursively compile other clauses
                     )]
            [(FunRest args xs e) ;; matchs if arg len is at least req_args len
                (seq (Cmp 'r11 (length args)) ;; will compare given arg list w/ case
                     (Jl next) ;; not enough req args, skips to next function
                     (compile-fun (gensym) func) ;; compile current function
                     (Label next)
                     (compile-lambda rest (gensym)) ;; recursively compile other clauses
                     )]
          ))
          ])
)



;; type CEnv = (Listof [Maybe Id])

;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(Lit d) (compile-value d)]
    [(Eof) (compile-value eof)]
    [(Var x) (compile-variable x c)]
    [(Prim0 p) (compile-prim0 p)]
    [(Prim1 p e) (compile-prim1 p e c)]
    [(Prim2 p e1 e2) (compile-prim2 p e1 e2 c)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c)]
    [(If e1 e2 e3)
     (compile-if e1 e2 e3 c)]
    [(Begin e1 e2)
     (compile-begin e1 e2 c)]
    [(Let x e1 e2)
     (compile-let x e1 e2 c)]
    [(App f es)
     (compile-app f es c)]
    [(Apply f es e)
     (compile-apply f es e c)]))

;; Value -> Asm
(define (compile-value v)
  (cond [(string? v) (compile-string v)]
        [else        (Mov rax (value->bits v))]))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))
    (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Or rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 -> Asm
(define (compile-prim0 p)
  (compile-op0 p))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
  (seq (compile-e e c)
       (compile-op1 p)))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (compile-op2 p)))

;; Op3 Expr Expr Expr CEnv -> Asm
(define (compile-prim3 p e1 e2 e3 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (Push rax)
       (compile-e e3 (cons #f (cons #f c)))
       (compile-op3 p)))
;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c)
         (Cmp rax (value->bits #f))
         (Je l1)
         (compile-e e2 c)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c)
         (Label l2))))
;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8)))

;; Id [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app f es c)
  (let ((r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (compile-es es (cons #f c))
         (Mov 'r11 (length es)) ;; loads the arg len into r11, no other func should use r11
         (Jmp (symbol->label f))
         (Label r))))

;; Id [Listof Expr] Expr CEnv -> Asm
(define (compile-apply f es e c)
  (let ((return (gensym)) (done (gensym)) (loop (gensym)))
    (seq (Lea rax return)
         (Push rax) ;; load return address onto stack
         (compile-es es (cons #f c)) ;; compile explicit args, puts on stack
         ;(compile-e e (cons #f c)) ;; compiles the 'e' part
         (compile-e e (make-env c (+ 1 (length es))))

         (Mov 'r11 (length es)) ;; inits r11 with explicit args len
         (Mov 'r8 rax) ;; time to check result of compiling e
         (And 'r8 ptr-mask) ;; isolates ptr mask
         (Cmp 'r8 0) ;; checking empty list
         (Je done) ;; skip to end and call func
         (Cmp 'r8 type-cons) ;; make sure it is a list
         
         (Je loop)
         (Add rsp (* 8 (length (cons #f es)))) ;; error case, remove all params
         (Jmp 'err) ;; jump to err

         (Label loop)
         (Xor rax type-cons) ;; untags ptr
         
         
         (Mov 'r9 (Offset rax 8)) ;; will move car val first
         (Push 'r9) ;; now onto stack
         (Add 'r11 1) ;; increment arg count

         (Mov 'r9 (Offset rax 0)) ;; gets cdr ptr
         (Mov rax 'r9)
         (Cmp rax (value->bits '())) ;; checks for empty list
         (Jne loop) ;; reached end case, nothing left to push
         
         ;(Jmp loop)

         (Label done)
         (Jmp (symbol->label f)) ;; call to func
         ;(Mov 'r9 (Offset rsp 0))
         ;(Mov rax 'r9)
         ;(Add rsp (* 8 (+ 1 (length (cons #f es)))))
         (Label return)

    )))

; (define (compile-lst) ;; rax has lst
;   (seq (Cmp rax ))
; )

(define (make-env lst num) ;; adds 'num' amount of #f onto env
  (match num
    [0 lst]
    [_ (cons #f (make-env lst (- num 1)))]))

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c)
          (Push rax) 
          (compile-es es (cons #f c))
          )]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

