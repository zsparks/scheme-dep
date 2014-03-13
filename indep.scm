(load "pmatch.scm")

; First language
;
; TermInf ::=
;   (ann TermCheck Type)
; | (bound Int)
; | (free Name)
; | (@ TermInf TermCheck)
;
; TermCheck ::= 
;   (inf TermInf)
; | (lambda TermCheck)
;
; Name ::=
;   (global String)
; | (local Int)
; | (quot Int)
;
; Type ::=
;   (tfree Name)
; | (-> Type Type)
;
; Value ::=
;   (vlambda F) ; F is a function from Values to Values
; | (vneutral Neutral)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)

(define perror
  (lambda (x)
    (error x x)))

; vfree :: Name -> Value
(define vfree
  (lambda (Name)
    `(vneutral (nfree ,Name))))

(define lookup-nth
  (lambda (xs i)
    (pmatch `(,xs ,i)
      [((,x . ,xs) 0) x]
      [((,x . ,xs) ,i) (lookup-nth xs (sub1 i))])))

; An Env is just a list of Values

; evalInf :: TermInf -> Env -> Value
(define evalInf
  (lambda (TermInf Env)
    (pmatch TermInf
      [(ann ,TermCheck ,Type) (evalCheck TermCheck Env)]
      [(free ,Name) (vfree Name)]
      [(bound ,Int) (lookup-nth Env Int)]
      [(@ ,TermInf ,TermCheck)
         (vapp (evalInf TermInf Env) (evalCheck TermCheck Env))])))

(define vapp
  (lambda (Value1 Value2)
    (pmatch Value1
      [(vlambda ,F) (F Value2)]
      [(vneutral ,Neutral) `(vneutral (napp ,Neutral ,Value2))])))

(define evalCheck
  (lambda (TermCheck Env)
    (pmatch TermCheck
      [(inf ,TermInf) (evalInf TermInf Env)]
      [(lambda ,TermCheck)
         `(vlambda ,(lambda (x) (evalCheck TermCheck (cons x Env))))])))

; Kind ::=
;   star
;
; Info ::=
;   (hasKind Kind)
; | (hasType Type)
;
; Context is a list of (Name, Info) pairs


; kind-check :: Context -> Type -> Kind -> void
(define kind-check
  (lambda (Context Type Kind)
    (pmatch `(,Type ,Kind)
      [((tfree ,Name) star)
          (pmatch (assoc Name Context)
            [(,key . (hasKind star)) (void)]
            [#f (perror "unknown identifier (in kinds)")])]
      [((-> ,Type1 ,Type2) star)
        (begin
          (kind-check Context Type1 'star)
          (kind-check Context Type2 'star))])))

; type-infer :: Int -> Context -> TermInf -> Type
(define type-infer
  (lambda (Int Context TermInf)
    (pmatch TermInf
      [(ann ,TermCheck ,Type)
        (begin
          (kind-check Context Type 'star)
          (type-check Int Context TermCheck Type)
          Type)]
      [(free ,Name)
        (pmatch (assoc Name Context)
          [(,key . (hasType ,Type)) Type]
          [#f (perror "unknown identifier (in types)")])]
      [(@ ,TermInf ,TermCheck)
        (pmatch (type-infer Int Context TermInf)
          [(-> ,Type1 ,Type2)
            (begin
              (type-check Int Context TermCheck Type1)
              Type2)]
          [,else (perror "illegal application")])])))

(define type-check
  (lambda (Int Context TermCheck Type)
    (pmatch TermCheck
      [(inf ,TermInf)
       (let ([Type^ (type-infer Int Context TermInf)])
         (if (equal? Type Type^) (void) (perror "type mismatch (invalid arg)")))]
      [(lambda ,TermCheck)
        (pmatch Type
          [(-> ,Type1 ,Type2)
            (type-check
              (add1 Int)
              (cons `((local ,Int) . (hasType ,Type1)) Context)
              (subst-check 0 `(free (local ,Int)) TermCheck)
              Type2)]
          [,else (perror "type mismatch (non-function being called)")])]
      [,else (error "type mismatch (not a checkable term): ~s" TermCheck)])))

(define subst-inf
  (lambda (Int TermInf1 TermInf2)
    (pmatch TermInf2
        [(ann ,e ,t) `(Ann ,(subst Int TermInf1 e) ,t)]
        [(bound ,j) (if (eq? Int j) TermInf1 TermInf2)]
        [(free ,Var) TermInf2]
        [(@ ,TermInf ,TermCheck) `(@ ,(subst-inf Int TermInf1 TermInf)
                                     ,(subst-check Int TermInf1 TermCheck))])))

(define subst-check
  (lambda (Int TermInf TermCheck)
    (pmatch TermCheck
      [(inf ,e) `(inf ,(subst-inf Int TermInf e))]
      [(lambda ,body) `(lambda ,(subst-check (add1 Int) TermInf body))])))

(define quot0
  (lambda (Value)
    (quot 0 Value)))

(define quot
  (lambda (Int Value)
    (pmatch Value
      [(vlambda ,f) `(lambda ,(quot (add1 Int) (f (vfree `(quot ,Int)))))]
      [(vneutral ,n) `(inf ,(neutral-quot Int n))])))

(define neutral-quot
  (lambda (Int Neutral)
    (pmatch Neutral
      [(nfree ,x) (bound-free Int x)]
      [(napp ,n ,v) `(@ ,(neutral-quot Int n) ,(quot Int v))])))

(define bound-free
  (lambda (Int Name)
    (pmatch Name
      [(quot ,k) `(bound (- (- Int k) 1))]
      [,x `(free ,x)])))

; A reminder for parsing
;
; TermInf ::=
;   (ann TermCheck Type)
; | (bound Int)
; | (free Name)
; | (@ TermInf TermCheck)
;
; TermCheck ::= 
;   (inf TermInf)
; | (lambda TermCheck)
;
; Name ::=
;   (global Symbol)
; | (local Int)
; | (quot Int)
;
; Type ::=
;   (tfree Name)
; | (-> Type Type)
;
; Value ::=
;   (vlambda F) ; F is a function from Values to Values
; | (vneutral Neutral)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)

(define find-depth
  (lambda (i xs y)
    (pmatch xs
      [() #f]
      [(,x . ,xs) (if (eq? x y) i (find-depth (add1 i) xs y))])))

(define parse-inf
  (lambda (ctx e)
    (pmatch e
      [(: ,TermCheck ,Type) `(ann ,(parse-check ctx TermCheck)
                                  ,(parse-type Type))]
      [,x (guard (symbol? x))
          (pmatch (find-depth 0 ctx x)
            [#f `(free (global ,x))]
            [,i `(bound ,i)])]
      [(,e1 ,e2) `(@ ,(parse-inf ctx e1) ,(parse-check ctx e2))])))

(define parse-check
  (lambda (ctx e)
    (pmatch e
      [(lambda (,x) ,body) `(lambda ,(parse-check (cons x ctx) body))]
      [,e `(inf ,(parse-inf ctx e))])))

(define parse-type
  (lambda (t)
    (pmatch t
      [(-> ,t1 ,t2) `(-> ,(parse-type t1) ,(parse-type t2))]
      [,x (guard (symbol? x)) `(tfree (global ,x))])))


(define unparse-inf
  (lambda (ctx TermInf)
    (pmatch TermInf
      [(ann ,TermCheck ,Type)
       `(: ,(unparse-check ctx TermCheck) ,(unparse-type ctx Type))]
      [(bound ,Int) (lookup-nth ctx Int)]
      [(free ,Name) (unparse-name ctx Name)]
      [(@ ,TermInf ,TermCheck)
       `(,(unparse-inf ctx TermInf) ,(unparse-check ctx TermCheck))])))

(define unparse-check
  (lambda (ctx TermCheck)
    (pmatch TermCheck
      [(inf ,TermInf) (unparse-inf ctx TermInf)]
      [(lambda ,TermCheck)
       (let ([x (gensym)])
         `(lambda (,x) ,(unparse-check (cons x ctx) TermCheck)))])))

(define unparse-type
  (lambda (ctx Type)
    (pmatch Type
      [(tfree ,Name) (unparse-name ctx Name)]
      [(-> ,Type1 ,Type2)
       `(-> ,(unparse-type ctx Type1) ,(unparse-type ctx Type2))])))

(define unparse-name
  (lambda (ctx Name)
    (pmatch Name
      [(global ,x) x]
      [(local ,Int) (lookup-nth ctx Int)])))

; for testing
(define : (lambda (x y) x))
(define x 'x)
(define y 'y)
(define a 'a)
(define -> (lambda (x y) `(-> ,x ,y)))

(define default-context
  '( ((global x) . (hasType (tfree (global a))))
     ((global y) . (hasType (tfree (global a))))
     ((global a) . (hasKind star)) )
  )
(define default-dyn '( (x . x) (y . y) ))

; list of lists of terms, their expected types, static ctxs, and dynamic ctxs
(define tests
  (list
    `(((: (lambda (x) x) (-> a a)) x) a ,default-context ,default-dyn)
    `((( (: (lambda (x) (lambda (y) x)) (-> a (-> a a))) x) y)
      a
      ,default-context
      ,default-dyn)
    )
  )

(define run-test
  (lambda (test)
    (pmatch test
      [(,e ,t ,s ,d)
       (let*
         ([TermInf (parse-inf '() e)]
          [OutType (type-infer 0 s TermInf)])
         (if (not (equal? OutType (parse-type t)))
           "type mismatch, oh no"
           (let*
             ([OutVal (evalInf TermInf d)]
              [OutExp (quot0 OutVal)]
              [OutSchemeExp (unparse-check '() OutExp)])
             (if (equal? (eval e) (eval OutSchemeExp))
               (void)
               "oh no, evaluation failure!"))))])))



