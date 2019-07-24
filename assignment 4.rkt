#lang pl 

   (define-type BIT = (U 0 1))
   (define-type Bit-List = (Listof BIT))


   (define-type
    RegE
    [Reg Bit-List]
    [And RegE RegE]
    [Or RegE RegE]
    [Shl RegE]
    [IdFROL Symbol]
    [WithFROL Symbol RegE RegE]
    [Bool Boolean]
    [Geq RegE RegE]
    [Maj RegE]
    [If RegE RegE RegE]
    [FunFROL Symbol RegE]
    [CallFROL RegE RegE])


   (: list->bit-list : (Listof Any) -> Bit-List)
   (define (list->bit-list lst)
     (cond
      [(null? lst) null]
      [(eq? (first lst) 1) (cons 1 (list->bit-list (rest lst)))]
      [else (cons 0 (list->bit-list (rest lst)))]))
   (: parse-sexprFROL : Sexpr -> RegE)
   (define (parse-sexprFROL sexpr)
     (match
      sexpr
      [(list 'reg-len '= (number: n) body)
       (if (<= n 0)
         (error 'parse-sexprFROL "Register length must be at least 1")
         (parse-sexpr-RegL body n))]
      [else (error 'parse-sexprFROL "bad syntax in ~s" sexpr)]))



   (: parse-sexpr-RegL : Sexpr Number -> RegE)
   (define (parse-sexpr-RegL sexpr reg-len)
     (match
      sexpr
      [(list (and a (or 1 0)) ...)
       (if (eq? (length a) reg-len)
         (Reg (list->bit-list a))
         (error 'parse-sexprFROL "wrong number of bits in ~s" a))]
      [(list 'and sexpr1 sexpr2)
       (And
        (parse-sexpr-RegL sexpr1 reg-len)
        (parse-sexpr-RegL sexpr2 reg-len))]
      [(list 'or sexpr1 sexpr2)
       (Or (parse-sexpr-RegL sexpr1 reg-len) (parse-sexpr-RegL sexpr2 reg-len))]
      [(list 'shl sexpr1) (Shl (parse-sexpr-RegL sexpr1 reg-len))]
      ['false (Bool #f)]
      ['true (Bool #t)]
      [(symbol: name) (IdFROL name)]
      [(list 'with (list (symbol: name) named) body)
       (WithFROL
        name
        (parse-sexpr-RegL named reg-len)
        (parse-sexpr-RegL body reg-len))]
      [(list 'geq? sexpr1 sexpr2)
       (Geq
        (parse-sexpr-RegL sexpr1 reg-len)
        (parse-sexpr-RegL sexpr2 reg-len))]
      [(list 'maj? sexpr1) (Maj (parse-sexpr-RegL sexpr1 reg-len))]
      [(list 'if sexpr1 sexpr2 sexpr3)
       (If
        (parse-sexpr-RegL sexpr1 reg-len)
        (parse-sexpr-RegL sexpr2 reg-len)
        (parse-sexpr-RegL sexpr3 reg-len))]
      [(cons 'fun x)
       (match
        sexpr
        [(list 'fun (list (symbol: var)) body-exp)
         (FunFROL var (parse-sexpr-RegL body-exp reg-len))]
        [else (error 'parse-sexpr-RegL "bad `fun' syntax in ~s" sexpr)])]
      [(list 'call fun args)
       (CallFROL
        (parse-sexpr-RegL fun reg-len)
        (parse-sexpr-RegL args reg-len))]
      [else (error 'parse-sexprFROL "bad syntax in ~s" sexpr)]))
   (: parseFROL : String -> RegE)
   (define (parseFROL str) (parse-sexprFROL (string->sexpr str)))


   (test (parse-sexpr-RegL (string->sexpr "{1 1 1 1}") 4) => (Reg '(1 1 1 1)))
   (test (parse-sexpr-RegL (string->sexpr "{0 0 0}") 3) => (Reg '(0 0 0)))
   (test (parseFROL "{ reg-len =  4  {1 0 0 0}}") => (Reg '(1 0 0 0)))
   
   (define-type RES
     [RegV Bit-List]
     [boolean-res Boolean]
     [H-Fun Symbol RegE])



   (: substFROL : RegE Symbol RegE -> RegE)
   (define (substFROL expr-reg from to)
     (cases
      expr-reg
      [(Reg lst) expr-reg]
      [(And l r) (And (substFROL l from to) (substFROL r from to))]
      [(Or l r) (Or (substFROL l from to) (substFROL r from to))]
      [(Shl reg) (Shl (substFROL reg from to))]
      [(IdFROL name) (if (eq? name from) to expr-reg)]
      [(WithFROL bound-id named-expr bound-body)
       (WithFROL
        bound-id
        (substFROL named-expr from to)
        (if (eq? bound-id from) bound-body (substFROL bound-body from to)))]
      [(If l m r)
       (If (substFROL l from to) (substFROL m from to) (substFROL r from to))]
      [(Maj l) (Maj (substFROL l from to))]
      [(Geq l r) (Geq (substFROL l from to) (substFROL r from to))]
      [(Bool b) expr-reg]
      [(CallFROL l r) (CallFROL (substFROL l from to) (substFROL r from to))]
      [(FunFROL bound-id bound-body)
       (if (eq? bound-id from)
         expr-reg
         (FunFROL bound-id (substFROL bound-body from to)))]))
   (: evalFROL : RegE -> RES)
   (define (evalFROL expr)
     (cases
      expr
      [(Reg reg) (RegV reg)]
      [(And l r) (reg-arith-op bit-and (evalFROL l) (evalFROL r))]
      [(Or l r) (reg-arith-op bit-or (evalFROL l) (evalFROL r))]
      [(Shl l) (RegV (shift-left (RegV->bit-list (evalFROL l))))]
      [(IdFROL name) (error 'evalFROL "free identifier: ~s" name)]
      [(WithFROL bound-id named-expr bound-body)
       (evalFROL
        (substFROL bound-body bound-id
         (cases
          (evalFROL named-expr)
          [(boolean-res b) (Bool b)]
          [(RegV regv) (Reg regv)]
          [(H-Fun bound-id bound-body) (FunFROL bound-id bound-body)])))]
      [(FunFROL bound-id bound-body) (H-Fun bound-id bound-body)]
      [(Bool b) (boolean-res b)]
      [(Geq l r)
       (boolean-res
        (geq-bitlists?
         (RegV->bit-list (evalFROL l))
         (RegV->bit-list (evalFROL r))))]
      [(Maj l) (boolean-res (majority? (RegV->bit-list (evalFROL l))))]
      [(If b l r)
       (cases
        (evalFROL b)
        [(boolean-res b) (if b (evalFROL l) (evalFROL r))]
        [(RegV list) (if list (evalFROL l) (evalFROL r))]
        [(H-Fun bound-id bound-body)
         (if (evalFROL bound-body) (evalFROL l) (evalFROL r))])]
      [(CallFROL fun-expression arg-expression)
       (cases
        (evalFROL fun-expression)
        [(H-Fun bound-id bound-body)
         (evalFROL
          (substFROL bound-body bound-id
           (cases
            (evalFROL arg-expression)
            [(boolean-res b) (Bool b)]
            [(RegV reg) (Reg reg)]
            [(H-Fun bound-id bound-body) (FunFROL bound-id bound-body)])))]
        [else
         (error
          'eval
          "`call' expects a function, got: ~s"
          (evalFROL fun-expression))])]))





   (: RegV->bit-list : RES -> Bit-List)
   (define (RegV->bit-list reg)
     (cases
      reg
      [(boolean-res rb)
       (error 'RegV->bit-list "have to return a bit-list ~s" rb)]
      [(RegV b) b]
      [(H-Fun Symbol RegE) (error 'RegV->bit-list "Not Reg ~s" reg)]))




   (test (RegV->bit-list (RegV '(0 0))) => '(0 0))
   (test (RegV->bit-list (RegV '(0 1))) => '(0 1))
   (test (RegV->bit-list (RegV '(1 0))) => '(1 0))
   (test (RegV->bit-list (RegV '(1 1))) => '(1 1))
   (test (RegV->bit-list (RegV '(1 1 1 0))) => '(1 1 1 0))
   (: bit-and : BIT BIT -> BIT)
   (define (bit-and a b) (if (and (= a 1) (= b 1)) 1 0))
   (test (bit-and 0 0) => 0)
   (test (bit-and 0 1) => 0)
   (test (bit-and 1 0) => 0)
   (test (bit-and 1 1) => 1)
   (: bit-or : BIT BIT -> BIT)
   (define (bit-or a b) (if (or (= a 1) (= b 1)) 1 0))
   (test (bit-or 0 0) => 0)
   (test (bit-or 0 1) => 1)
   (test (bit-or 1 0) => 1)
   (test (bit-or 1 1) => 1)
   (: reg-arith-op : (BIT BIT -> BIT) RES RES -> RES)
   (define (reg-arith-op op reg1 reg2)
     (: bit-arith-op : Bit-List Bit-List -> Bit-List)
     (define (bit-arith-op bl1 bl2)
       (cond
        [(and (null? bl1) (null? bl2)) '()]
        [(or (null? bl1) (null? bl2)) (error 'bit-arith-op "different length")]
        [else
         (cons
          (op (first bl1) (first bl2))
          (bit-arith-op (rest bl1) (rest bl2)))]))
     (RegV (bit-arith-op (RegV->bit-list reg1) (RegV->bit-list reg2))))
   (test (reg-arith-op bit-and (RegV '(0 0)) (RegV '(0 0))) => (RegV '(0 0)))
   (test
    (reg-arith-op bit-and (RegV '(0 1 1 1)) (RegV '(1 0 1 1)))
    =>
    (RegV '(0 0 1 1)))
   (test
    (reg-arith-op bit-and (RegV '(1 1 1 1 1)) (RegV '(0 0 0 0 0)))
    =>
    (RegV '(0 0 0 0 0)))
   (test
    (reg-arith-op bit-and (RegV '(1)) (RegV '(0 0)))
    =error>
    "bit-arith-op: different length")
   (test
    (reg-arith-op bit-and (RegV '(1 1)) (RegV '(0 0 0)))
    =error>
    "bit-arith-op: different length")
   (test (reg-arith-op bit-or (RegV '(1)) (RegV '(0))) => (RegV '(1)))
   (test (reg-arith-op bit-or (RegV '(0 0)) (RegV '(0 0))) => (RegV '(0 0)))
   (test
    (reg-arith-op bit-or (RegV '(0 1 1 1)) (RegV '(1 0 1 1)))
    =>
    (RegV '(1 1 1 1)))
   (test
    (reg-arith-op bit-or (RegV '(1)) (RegV '(0 0)))
    =error>
    "bit-arith-op: different length")
   (test
    (reg-arith-op bit-or (RegV '(1 1)) (RegV '(0 0 0)))
    =error>
    "bit-arith-op: different length")






   (: majority? : Bit-List -> Boolean)
   (define (majority? bl)
     (: mag-help : Bit-List Integer Integer -> Boolean)
     (define (mag-help bl n1 n2)
       (cond
        [(null? bl) (if (or (> n1 n2) (= n1 n2)) true false)]
        [else
         (if (eq? (first bl) 1)
           (mag-help (rest bl) (+ n1 1) n2)
           (mag-help (rest bl) n1 (+ n2 1)))]))
     (mag-help bl 0 0))


   (test (majority? '(1)) => true)
   (test (majority? '(1 1)) => true)
   (test (majority? '(0)) => false)
   (test (majority? '(1 1)) => true)
   (test (majority? '(1 1 0 0 0 0 0 1 1 1 1 1 0 0 0)) => false)
   (test (majority? '(0 1 0 1)) => true)
   (test (majority? '(0 1 1 1 1 1 1)) => true)
   (test (majority? '()) => true)
   (test (majority? '(1 1 1 0 0 0)) => true)



   (: geq-bitlists? : Bit-List Bit-List -> Boolean)
   (define (geq-bitlists? bl1 bl2)
     (cond
      [(and (eq? bl1 null) (eq? bl2 null)) true]
      [(or (eq? bl1 null) (eq? bl2 null))
       (error 'geq-bitlists? "different length")]
      [(> (first bl1) (first bl2)) true]
      [(< (first bl1) (first bl2)) false]
      [else (geq-bitlists? (rest bl1) (rest bl2))]))



   (test (geq-bitlists? '(0 0 0) '(0 0 1)) => false)
   (test (geq-bitlists? '(0) '(0)) => true)
   (test (geq-bitlists? '(1 1 1) '(1 0 1)) => true)
   (test (geq-bitlists? '(1 1 1 0) '(1 1 1 1)) => false)
   (test (geq-bitlists? '(0 0 0 0 0) '(0 0 0 1 0)) => false)
   (test (geq-bitlists? '(1 1 1 1 1) '(1 0 1 1 0)) => true)
   (test (geq-bitlists? '(0 1 1 0 1) '(1 1 0 1 1)) => false)
   (test (geq-bitlists? '(1) '(1)) => true)
   (test (geq-bitlists? '() '(1)) =error> "geq-bitlists?: different length")
   (test (geq-bitlists? '(1 1 1 0 1) '(1 1 0 1 1)) => true)
   (test
    (geq-bitlists? '(0 0) '(0 0 1))
    =error>
    "geq-bitlists?: different length")
   (test (geq-bitlists? '() '()) => true)
   (test
    (geq-bitlists? '(0 1 0 0 0) '(0 1 0 0 0 1))
    =error>
    "geq-bitlists?: different length")
   (test (geq-bitlists? '(1 1 1 1) '(1 1 1 0)) => true)



   (: shift-left : Bit-List -> Bit-List)
   (define (shift-left bl) (append (rest bl) (list (first bl))))


   (test (shift-left '(0 0)) => '(0 0))
   (test (shift-left '(0 1 1 1 1)) => '(1 1 1 1 0))
   (test (shift-left '(1 1 1)) => '(1 1 1))
   (test (shift-left '(1 0 0)) => '(0 0 1))
   (test (shift-left '(0 1)) => '(1 0))
   (test (shift-left '(0 1 0 1 0 1)) => '(1 0 1 0 1 0))
   (test (shift-left '(0 1 0)) => '(1 0 0))
   (test (shift-left '(0 0 0 0 0 0 0 1)) => '(0 0 0 0 0 0 1 0))
   (test (shift-left '(0 1 0 0 1 0 0 1)) => '(1 0 0 1 0 0 1 0))
   (test (shift-left '(1 1 1 0)) => '(1 1 0 1))
   (test (shift-left '(0 1 1 0)) => '(1 1 0 0))
   (test (shift-left '(0 0 0 0)) => '(0 0 0 0))
   (: runFROL : String -> Bit-List)
   (define (runFROL string)
     (RegV->bit-list (evalFROL (parseFROL string))))


   (test (runFROL "{ reg-len =  4  {1 0 0 0}}") => '(1 0 0 0))
   (test
    (runFROL "{ reg-len =  3  {1 0 0 0}}")
    =error>
    "wrong number of bits in (1 0 0 0)")
   (test (runFROL "{ reg-len =  5  {1 0 0 0 0}}") => '(1 0 0 0 0))
   (test (runFROL "{ reg-len = 4  {shl {1 0 0 0}}}") => '(0 0 0 1))
   (test (runFROL "{ reg-len = 4  {shl {0 1 0 0}}}") => '(1 0 0 0))
   (test (runFROL "{ reg-len = 4  {shl {1 1 0 0}}}") => '(1 0 0 1))
  
   (define-type
    FLANG
    [Num Number]
    [Add FLANG FLANG]
    [Sub FLANG FLANG]
    [Mul FLANG FLANG]
    [Div FLANG FLANG]
    [Id Symbol]
    [With Symbol FLANG FLANG]
    [Fun Symbol FLANG]
    [Call FLANG FLANG])
   (: parse-sexpr : Sexpr -> FLANG)
   (define (parse-sexpr sexpr)
     (match
      sexpr
      [(number: n) (Num n)]
      [(symbol: name) (Id name)]
      [(cons 'with more)
       (match
        sexpr
        [(list 'with (list (symbol: name) named) body)
         (With name (parse-sexpr named) (parse-sexpr body))]
        [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
      [(cons 'fun more)
       (match
        sexpr
        [(list 'fun (list (symbol: name)) body) (Fun name (parse-sexpr body))]
        [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
      [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list 'call fun arg) (Call (parse-sexpr fun) (parse-sexpr arg))]
      [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))
   (: parse : String -> FLANG)
   (define (parse str) (parse-sexpr (string->sexpr str)))
   (: subst : FLANG Symbol FLANG -> FLANG)
   (define (subst expr from to)
     (cases
      expr
      [(Num n) expr]
      [(Add l r) (Add (subst l from to) (subst r from to))]
      [(Sub l r) (Sub (subst l from to) (subst r from to))]
      [(Mul l r) (Mul (subst l from to) (subst r from to))]
      [(Div l r) (Div (subst l from to) (subst r from to))]
      [(Id name) (if (eq? name from) to expr)]
      [(With bound-id named-expr bound-body)
       (With
        bound-id
        (subst named-expr from to)
        (if (eq? bound-id from) bound-body (subst bound-body from to)))]
      [(Call l r) (Call (subst l from to) (subst r from to))]
      [(Fun bound-id bound-body)
       (if (eq? bound-id from)
         expr
         (Fun bound-id (subst bound-body from to)))]))
   (: arith-op : (Number Number -> Number) FLANG FLANG -> FLANG)
   (define (arith-op op expr1 expr2)
     (: Num->number : FLANG -> Number)
     (define (Num->number e)
       (cases
        e
        [(Num n) n]
        [else (error 'arith-op "expects a number, got: ~s" e)]))
     (Num (op (Num->number expr1) (Num->number expr2))))
   (: eval : FLANG -> FLANG)
   (define (eval expr)
     (cases
      expr
      [(Num n) expr]
      [(Add l r) (arith-op + (eval l) (eval r))]
      [(Sub l r) (arith-op - (eval l) (eval r))]
      [(Mul l r) (arith-op * (eval l) (eval r))]
      [(Div l r) (arith-op / (eval l) (eval r))]
      [(With bound-id named-expr bound-body)
       (eval (subst bound-body bound-id (eval named-expr)))]
      [(Id name) (error 'eval "free identifier: ~s" name)]
      [(Fun bound-id bound-body) expr]
      [(Call fun-expr arg-expr)
       (let ([fval (eval fun-expr)])
         (cases
          fval
          [(Fun bound-id bound-body)
           (eval (subst bound-body bound-id (eval arg-expr)))]
          [else (error 'eval "`call' expects a function, got: ~s" fval)]))]))
   (: run : String -> Number)
   (define (run str)
     (let ([result (eval (parse str))])
       (cases
        result
        [(Num n) n]
        [else (error 'run "evaluation returned a non-number: ~s" result)])))
   (test (run "{call {fun {x} {+ x 1}} 4}") => 5)
   (test (run "{with {add3 {fun {x} {+ x 3}}}{call add3 1}}") => 4)
   (test
    (run
     "{with {add3 {fun {x} {+ x 3}}}{with {add1 {fun {x} {+ x 1}}}{with {x 3}{call add1 {call add3 x}}}}}")
    =>
    7)
   (test
    (run
     "{with {identity {fun {x} x}}{with {foo {fun {x} {+ x 1}}}{call {call identity foo} 123}}}")
    =>
    124)
   (test
    (run "{call {call {fun {x} {call x 1}}{fun {x} {fun {y} {+ x y}}}}123}")
    =>
    124)
   (define-type SubstCache = (Listof (List Symbol FLANG)))
   (: empty-subst : SubstCache)
   (define empty-subst null)
   (: extend : Symbol FLANG SubstCache -> SubstCache)
   (define (extend name val sc) (cons (list name val) sc))
   (: lookup : Symbol SubstCache -> FLANG)
   (define (lookup name sc)
     (let ([cell (assq name sc)])
       (if cell (second cell) (error 'lookup "no binding for ~s" name))))
   (: counterx : Natural)
   (define counterx 0)
   (: evalSC : FLANG SubstCache -> FLANG)
   (define (evalSC expr sc)
     (set! counterx (add1 counterx))
     (if (> counterx 500)
       (error 'eval "exceeded 500 times")
       (cases
        expr
        [(Num n) expr]
        [(Add l r) (arith-op + (evalSC l sc) (evalSC r sc))]
        [(Sub l r) (arith-op - (evalSC l sc) (evalSC r sc))]
        [(Mul l r) (arith-op * (evalSC l sc) (evalSC r sc))]
        [(Div l r) (arith-op / (evalSC l sc) (evalSC r sc))]
        [(With bound-id named-expr bound-body)
         (evalSC bound-body (extend bound-id (evalSC named-expr sc) sc))]
        [(Id name) (lookup name sc)]
        [(Fun bound-id bound-body) expr]
        [(Call fun-expr arg-expr)
         (let ([fval (evalSC fun-expr sc)])
           (cases
            fval
            [(Fun bound-id bound-body)
             (evalSC bound-body (extend bound-id (evalSC arg-expr sc) sc))]
            [else
             (error 'evalSC "`call' expects a function, got: ~s" fval)]))])))
   (: runSC : String -> Number)
   (define (runSC str)
     (let ([result (evalSC (parse str) empty-subst)])
       (cases
        result
        [(Num n) n]
        [else (error 'runSC "evaluation returned a non-number: ~s" result)])))
   (: Function-Help-countFreeSingle : FLANG Symbol Natural -> Natural)
   (: countFreeSingle : FLANG Symbol -> Natural)
   (define (countFreeSingle Flang x) (Function-Help-countFreeSingle Flang x 0))
   (define (Function-Help-countFreeSingle flang-exp from count)
     (cases
      flang-exp
      [(Num n) 0]
      [(Add l r)
       (+
        (Function-Help-countFreeSingle l from count)
        (Function-Help-countFreeSingle r from count))]
      [(Sub l r)
       (+
        (Function-Help-countFreeSingle l from count)
        (Function-Help-countFreeSingle r from count))]
      [(Mul l r)
       (+
        (Function-Help-countFreeSingle l from count)
        (Function-Help-countFreeSingle r from count))]
      [(Div l r)
       (+
        (Function-Help-countFreeSingle l from count)
        (Function-Help-countFreeSingle r from count))]
      [(Id name) (if (eq? name from) 1 0)]
      [(With bound-id named-expr bound-body)
       (+
        (Function-Help-countFreeSingle named-expr from count)
        (if (eq? bound-id from)
          count
          (Function-Help-countFreeSingle bound-body from count)))]
      [(Call l r)
       (+
        (Function-Help-countFreeSingle l from count)
        (Function-Help-countFreeSingle r from count))]
      [(Fun bound-id bound-body)
       (if (eq? bound-id from)
         0
         (Function-Help-countFreeSingle bound-body from count))]))
   (: CFSingle : String Symbol -> Natural)
   (define (CFSingle expr name) (countFreeSingle (parse expr) name))
   (test (CFSingle "{+ r r}" 'r) => 2)
   (test (CFSingle "{+ r e}" 'r) => 1)
   (test (CFSingle "{+ r e}" 'z) => 0)
   (test (CFSingle "{fun {r} {+ r e}}" 'e) => 1)
   (test (CFSingle "{fun {x} {+ e r}}" 'e) => 1)
   (test (CFSingle "{fun {r} {+ r e}}" 'r) => 0)
   (test (CFSingle "{fun {r} {+ r e}}" 'z) => 0)
   (test (CFSingle "{fun {r} {- r e}}" 'e) => 1)
   (test (CFSingle "{fun {r} {* r e}}" 'e) => 1)
   (test (CFSingle "{fun {r} {/ r e}}" 'e) => 1)
   (test (CFSingle "{fun {r} {+ r e}}" 'r) => 0)
   (test (CFSingle "{fun {x} {+ e r}}" 'r) => 1)
   (test (CFSingle "{with {e {+ e r}} {fun {x} {+ e r}}}" 'r) => 2)


   (define loop
     "{with {Maor-cohen {fun {z} {call foo z}}} {with {foo {fun {z} {call Maor-cohen z}}} {call Maor-cohen foo}}}")
   (test (runSC loop) =error> "exceeded 500 times")
   (test (run loop) =error> "free identifier: f")
 