(load "pmatch.scm")

; Dependent language
;
; TermInf ::=
;   (ann TermCheck TermCheck)
; | star
; | (pi TermCheck TermCheck)
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
; Value ::=
;   (vlambda F) ; F is a function from Values to Values
; | vstar
; | (vpi Value F)
; | (vneutral Neutral)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)
;
; Type := Value
;
; Context is a list of (Name, Type) pairs

(define perror
  (lambda (x)
    (error x "")))

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

; eval-inf :: TermInf -> Env -> Value
(define eval-inf
  (lambda (TermInf Env)
    (pmatch TermInf
      [(ann ,TermCheck ,Type) (eval-check TermCheck Env)]
      [star 'vstar]
      [(pi ,TermCheck1 ,TermCheck2)
       `(vpi ,(eval-check TermCheck1 Env)
             ,(lambda (x) (eval-check TermCheck2 (cons x Env))))]
      [(free ,Name) (vfree Name)]
      [(bound ,Int) (lookup-nth Env Int)]
      [(@ ,TermInf ,TermCheck)
         (vapp (eval-inf TermInf Env) (eval-check TermCheck Env))])))

(define vapp
  (lambda (Value1 Value2)
    (pmatch Value1
      [(vlambda ,F) (F Value2)]
      [(vneutral ,Neutral) `(vneutral (napp ,Neutral ,Value2))])))

(define eval-check
  (lambda (TermCheck Env)
    (pmatch TermCheck
      [(inf ,TermInf) (eval-inf TermInf Env)]
      [(lambda ,TermCheck)
         `(vlambda ,(lambda (x) (eval-check TermCheck (cons x Env))))])))

; type-infer :: Int -> Context -> TermInf -> Type
(define type-infer
  (lambda (Int Context TermInf)
    (pmatch TermInf
      [(ann ,TermCheck ,Type)
        (begin
          (type-check Int Context Type 'vstar)
          (let
            ([vtype (eval-check Type '())])
            (type-check Int Context TermCheck vtype)
            vtype))]
      [(free ,Name)
        (pmatch (assoc Name Context)
          [(,key . ,Type) Type]
          [#f (perror "unknown identifier (in types)")])]
      [star 'vstar]
      [(pi ,TermCheck1 ,TermCheck2)
       (begin
         (type-check Int Context TermCheck1 'vstar)
         (let
           ([vtype (eval-check TermCheck1 '())])
           (type-check (add1 Int)
                       (cons `((local ,Int) . ,vtype) Context)
                       (subst-check 0 `(free (local ,Int)) TermCheck2)
                       'vstar)
           'vstar))]
      [(@ ,TermInf ,TermCheck)
        (pmatch (type-infer Int Context TermInf)
          [(vpi ,vtype1 ,vtype2)
            (begin
              (type-check Int Context TermCheck vtype1)
              (vtype2 (eval-check TermCheck '())))]
          [,els (error "illegal application" els)])])))

(define type-check
  (lambda (Int Context TermCheck Type)
    (pmatch TermCheck
      [(inf ,TermInf)
       (let ([Type^ (type-infer Int Context TermInf)])
         (if (equal? (quot0 Type) (quot0 Type^))
           (void)
           (perror "type mismatch (invalid arg)")))]
      [(lambda ,TermCheck)
        (pmatch Type
          [(vpi ,Type1 ,Type2)
            (type-check
              (add1 Int)
              (cons `((local ,Int) . ,Type1) Context)
              (subst-check 0 `(free (local ,Int)) TermCheck)
              (Type2 (vfree `(local ,Int))))]
          [,else (perror "type mismatch (non-function being called)")])]
      [,else (error "type mismatch (not a checkable term): ~s" TermCheck)])))

(define subst-inf
  (lambda (Int TermInf1 TermInf2)
    (pmatch TermInf2
        [(ann ,e ,t)
         `(ann ,(subst-inf Int TermInf1 e) ,(subst-check Int TermInf1 t))]
        [star 'star]
        [(pi ,TermCheck1 ,TermCheck2)
         `(pi ,(subst-check Int TermInf1 TermCheck1)
              ,(subst-check (add1 Int) TermInf1 TermCheck2))]
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
      [vstar `(inf star)]
      [(vpi ,Value ,f)
       `(inf (pi ,(quot Int Value)
                 ,(quot (add1 Int) (f (vfree `(quot ,Int))))))]
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
;   (ann TermCheck TermCheck)
; | star
; | (pi TermCheck TermCheck)
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
; Value ::=
;   (vlambda F) ; F is a function from Values to Values
; | vstar
; | (vpi Value F)
; | (vneutral Neutral)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)
;
; Type := Value
;
; Context is a list of (Name, Type) pairs

(define find-depth
  (lambda (i xs y)
    (pmatch xs
      [() #f]
      [(,x . ,xs) (if (eq? x y) i (find-depth (add1 i) xs y))])))

(define parse-inf
  (lambda (ctx e)
    (pmatch e
      [(: ,TermCheck ,Type) `(ann ,(parse-check ctx TermCheck)
                                  ,(parse-check ctx Type))]
      [star 'star]
      ; treating (-> a b) as sugar for (pi (: _ a) b) where _ does not bind
      [(-> ,TermCheck1 ,TermCheck2)
       `(pi ,(parse-check ctx TermCheck1)
            ,(parse-check (cons (void) ctx) TermCheck2))]
      [(pi (: ,x ,TermCheck1) ,TermCheck2)
       `(pi ,(parse-check ctx TermCheck1)
            ,(parse-check (cons x ctx) TermCheck2))]
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
(define t 't) ; heh
(define star 'star)
(define pi (lambda (x y) `(pi ,x ,y)))

(define default-context
  `( ((global x) . ,(vfree '(global a)))
     ((global y) . ,(vfree '(global a)))
     ((global a) . vstar) )
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
    `( (((: (lambda (t) (lambda (x) x)) (pi (: t star) (-> t t))) a) x)
       a ,default-context ,default-dyn
      )
    )
  )

(define run-test
  (lambda (test)
    (pmatch test
      [(,e ,t ,s ,d)
       (let*
         ([TermInf (parse-inf '() e)]
          [OutType (type-infer 0 s TermInf)]
          [OutQuotType (quot0 OutType)]
          [ExpType (parse-inf s t)])
         (if (not (equal? OutQuotType (parse-check s t)))
           `("type mismatch, oh no" ,OutQuotType ,ExpType)
           (let*
             ([OutVal (eval-inf TermInf d)]
              [OutExp (quot0 OutVal)]
              [OutSchemeExp (unparse-check '() OutExp)])
             (if (equal? (eval e) (eval OutSchemeExp))
               (void)
               "oh no, evaluation failure!"))))])))



