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
; ; Extensions to the language: not gonna add datatypes
;
; | nat
; | (nat-elim TermCheck TermCheck TermCheck TermCheck)
; | zero
; | (succ TermCheck)
;
; | (vec TermCheck TermCheck)
; | (nil TermCheck)
; | (cons TermCheck TermCheck TermCheck TermCheck)
; | (vec-elim TermCheck TermCheck TermCheck TermCheck TermCheck TermCheck)
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
; | vnat
; | vzero
; | (vsucc Value)
;
; | (vnil Value)
; | (vcons Value Value Value Value)
; | (vvec Value Value)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)
;
; | (nnat-elim Value Value Value Neutral)
;
; | (nvec-elim Value Value Value Value Value Neutral)
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

; get the nth element out of a list
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
         (vapp (eval-inf TermInf Env) (eval-check TermCheck Env))]
      [nat 'vnat]
      [zero 'vzero]
      [(succ ,TermCheck) `(vsucc ,(eval-check TermCheck Env))]
      [(nat-elim ,motiv ,base ,ind ,n)
       (letrec
         ([base-val (eval-check base Env)]
          [ind-val  (eval-check ind Env)]
          [rec
            (lambda (n-val)
              (pmatch n-val
                [vzero base-val]
                [(vsucc ,pred) (vapp (vapp ind-val pred) (rec pred))]
                [(vneutral ,vn) `(vneutral (nnat-elim ,(eval-check motiv Env)
                                                      ,base-val
                                                      ,ind-val
                                                      ,vn))]))])
         (rec (eval-check n Env)))]
      [(nil ,type) `(vnil ,(eval-check type Env))]
      [(cons ,type ,len ,x ,xs)
       `(vcons
          ,(eval-check type Env)
          ,(eval-check len Env)
          ,(eval-check x Env)
          ,(eval-check xs Env)
          )
       ]
      [(vec ,type ,len) `(vvec ,(eval-check type Env) ,(eval-check len Env))]
      [(vec-elim ,type ,motiv ,base ,ind ,len ,vec)
       (letrec
         ([base-val (eval-check base Env)]
          [ind-val  (eval-check ind Env)]
          [rec
            (lambda (len-val vec-val)
              (pmatch vec-val
                [(vnil ,_) base-val]
                [(vcons ,_ ,new-len ,x ,xs)
                 (vapp* ind-val new-len x xs (rec new-len xs))]
                [(vneutral ,Neutral)
                 `(vneutral (nvec-elim ,(eval-check type Env)
                                       ,(eval-check motiv Env)
                                       ,base-val
                                       ,ind-val
                                       ,len-val
                                       ,Neutral))]))])
         (rec (eval-check len Env) (eval-check vec Env)))]
      )))

; shorthand for applying values to one another
; apply the HOAS function if there is one, otherwise put it in the neutral term
(define vapp
  (lambda (Value1 Value2)
    (pmatch Value1
      [(vlambda ,F) (F Value2)]
      [(vneutral ,Neutral) `(vneutral (napp ,Neutral ,Value2))])))

; n-ary form of vapp
(define vapp*
  (lambda args
    (fold-left vapp (car args) (cdr args))))

(define eval-check
  (lambda (TermCheck Env)
    (pmatch TermCheck
      [(inf ,TermInf) (eval-inf TermInf Env)]
      [(lambda ,TermCheck)
         `(vlambda ,(lambda (x) (eval-check TermCheck (cons x Env))))])))

; Helper function for creating values of (non-dependent) function type
(define arrow
  (lambda (x y)
    `(vpi ,x ,(lambda (whatever) y))))

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
          [#f (error "unknown identifier (in types) ~s" Name)])]
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
          [,els (error "illegal application" els)])]
      
     [nat 'vstar]
     [zero 'vnat]
     [(succ ,TermCheck)
      (begin
        (type-check Int Context TermCheck 'vnat)
        'vnat)]
     [(nat-elim ,motivator ,base ,ind ,nat)
      (begin
        (type-check Int Context motivator (arrow 'vnat 'vstar))
        (let ([vmotiv (eval-check motivator '())])
          (type-check Int Context base (vapp vmotiv 'vzero))
          (type-check Int Context ind
                      `(vpi 'vnat 
                            ,(lambda (l) 
                               (arrow (vapp vmotiv l)
                                      (vapp vmotiv `(vsucc ,l))))))
          (type-check Int Context nat 'vnat)
          (let ([vnat (eval-check nat '())])
            (vapp vmotiv vnat))))]
    [(vec ,type ,len)
     (begin
       (type-check Int Context type 'vstar)
       (type-check Int Context len 'vnat)
       'vstar)]
    [(nil ,type)
     (begin
       (type-check Int Context type 'vstar)
       `(vvec ,(eval-check type '()) vzero))]
    [(cons ,type ,len ,x ,xs)
     (begin
       (type-check Int Context type 'vstar)
       (type-check Int Context len 'vnat)
       (let
         ([type-val (eval-check type '())]
          [len-val  (eval-check len '())])
         (type-check Int Context x type-val)
         (type-check Int Context xs `(vvec ,type-val ,len-val))
         `(vvec ,type-val (vsucc ,len-val))))]
    [(vec-elim ,type ,motiv ,base ,ind ,len ,vec)
     (let
       ([type-val (eval-check type '())]
        [motiv-val (eval-check motiv '())]
        [len-val (eval-check len '())]
        [vec-val (eval-check vec '())])
       (type-check Int Context motiv
                   `(vpi vnat
                         ,(lambda (len)
                            `(vpi (vvec ,type-val ,len)
                                  ,(lambda (wev)
                                    'vstar)))))
       (type-check Int Context base (vapp* motiv-val 'vzero `(vnil ,type-val)))
       (type-check Int Context ind
                   ; noooooooooooooooo
                   `(vpi vnat
                         ,(lambda (len)
                            `(vpi ,type-val
                                  ,(lambda (y)
                                     `(vpi (vvec ,type-val ,len)
                                           ,(lambda (ys)
                                             `(vpi ,(vapp* motiv-val len ys)
                                                   ,(lambda (wev)
                                                      (vapp* motiv-val
                                                             `(vsucc ,len)
                                                             `(vcons ,type-val
                                                                     ,len
                                                                     ,y
                                                                     ,ys)
                                                             ))))))))))
       (type-check Int Context len 'vnat)
       (type-check Int Context vec `(vvec ,type-val ,len-val))
       (vapp* motiv-val len-val vec-val))]
      )))

(define type-check
  (lambda (Int Context TermCheck Type)
    (pmatch TermCheck
      [(inf ,TermInf)
       (let* ([Type^ (type-infer Int Context TermInf)]
              [qt1 (quot0 Type)]
              [qt2 (quot0 Type^)])
         (if (equal? qt1 qt2)
           (void)
           (begin
             (display qt1)
             (newline)
             (display qt2)
             (newline)
             (display TermCheck)
             (newline)
             (perror "type mismatch (invalid arg)"))))]
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
         `(ann ,(subst-check Int TermInf1 e) ,(subst-check Int TermInf1 t))]
        [star 'star]
        [(pi ,TermCheck1 ,TermCheck2)
         `(pi ,(subst-check Int TermInf1 TermCheck1)
              ,(subst-check (add1 Int) TermInf1 TermCheck2))]
        [(bound ,j) (if (eq? Int j) TermInf1 TermInf2)]
        [(free ,Var) TermInf2]
        [(@ ,TermInf ,TermCheck) `(@ ,(subst-inf Int TermInf1 TermInf)
                                     ,(subst-check Int TermInf1 TermCheck))]
        [nat 'nat]
        [zero 'zero]
        [(succ ,TermCheck) `(succ ,(subst-check Int TermInf1 TermCheck))]
        [(nat-elim ,tc1 ,tc2 ,tc3 ,tc4)
         `(nat-elim
            ,(subst-check Int TermInf1 tc1)
            ,(subst-check Int TermInf1 tc2)
            ,(subst-check Int TermInf1 tc3)
            ,(subst-check Int TermInf1 tc4))]
        [(vec ,TermCheck1 ,TermCheck2)
         `(vec ,(subst-check Int TermInf1 TermCheck1)
               ,(subst-check Int TermInf1 TermCheck2))]
        [(nil ,TermCheck) `(nil ,(subst-check Int TermInf1 TermCheck))]
        [(cons ,TC1 ,TC2 ,TC3 ,TC4)
         `(cons
            ,(subst-check Int TermInf1 TC1)
            ,(subst-check Int TermInf1 TC2)
            ,(subst-check Int TermInf1 TC3)
            ,(subst-check Int TermInf1 TC4))]
        [(vec-elim ,TC1 ,TC2 ,TC3 ,TC4 ,TC5 ,TC6)
         `(vec-elim
            ,(subst-check Int TermInf1 TC1)
            ,(subst-check Int TermInf1 TC2)
            ,(subst-check Int TermInf1 TC3)
            ,(subst-check Int TermInf1 TC4)
            ,(subst-check Int TermInf1 TC5)
            ,(subst-check Int TermInf1 TC6)
            )]
        )))

(define subst-check
  (lambda (Int TermInf TermCheck)
    (pmatch TermCheck
      [(inf ,e) `(inf ,(subst-inf Int TermInf e))]
      [(lambda ,body) `(lambda ,(subst-check (add1 Int) TermInf body))])))

;; quot0 : Value -> TermCheck
;; wrapper around quot
(define quot0
  (lambda (Value)
    (quot 0 Value)))

;; quot : Int -> Value -> TermCheck
;; quote a value into an inspectable term
(define quot
  (lambda (Int Value)
    (pmatch Value
      [(vlambda ,f) `(lambda ,(quot (add1 Int) (f (vfree `(quot ,Int)))))]
      [vstar `(inf star)]
      [(vpi ,Value ,f)
       `(inf (pi ,(quot Int Value)
                 ,(quot (add1 Int) (f (vfree `(quot ,Int))))))]
      [(vneutral ,n) `(inf ,(neutral-quot Int n))]
      [vnat `(inf nat)]
      [vzero `(inf zero)]
      [(vsucc ,v) `(inf (succ ,(quot Int v)))]
      [(vnil ,v) `(inf (nil ,(quot Int v)))]
      [(vcons ,v1 ,v2 ,v3 ,v4)
       `(inf (cons
               ,(quot Int v1)
               ,(quot Int v2)
               ,(quot Int v3)
               ,(quot Int v4)
               ))]
      [(vvec ,v1 ,v2)
       `(inf (vec
               ,(quot Int v1)
               ,(quot Int v2)
               ))]
      )))

;; neutral-quot : Int -> Neutral -> TermInf
(define neutral-quot
  (lambda (Int Neutral)
    (pmatch Neutral
      [(nfree ,x) (bound-free Int x)]
      [(napp ,n ,v) `(@ ,(neutral-quot Int n) ,(quot Int v))]
      [(nnat-elim ,v1 ,v2 ,v3 ,n)
       `(nat-elim ,(quot Int v1) ,(quot Int v2) ,(quot Int v3)
                  (inf ,(neutral-quot Int n)))]
      [(nvec-elim ,v1 ,v2 ,v3 ,v4 ,v5 ,n)
       `(vec-elim ,(quot Int v1)
                  ,(quot Int v2)
                  ,(quot Int v3)
                  ,(quot Int v4)
                  ,(quot Int v5)
                  (inf ,(neutral-quot Int n)))]
      )))

(define bound-free
  (lambda (Int Name)
    (pmatch Name
      [(quot ,k) `(bound ,(- (- Int k) 1))]
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
; ; Extensions to the language: not gonna add datatypes
;
; | nat
; | (nat-elim TermCheck TermCheck TermCheck TermCheck)
; | zero
; | (succ TermCheck)
;
; | (vec TermCheck TermCheck)
; | (nil TermCheck)
; | (cons TermCheck TermCheck TermCheck TermCheck)
; | (vec-elim TermCheck TermCheck TermCheck TermCheck TermCheck TermCheck)
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
; | vnat
; | vzero
; | (vsucc Value)
;
; | (vnil Value)
; | (vcons Value Value Value Value)
; | (vvec Value Value)
;
; Neutral ::=
;   (nfree Name)
; | (napp Neutral Value)
;
; | (nnat-elim Value Value Value Neutral)
;
; | (nvec-elim Value Value Value Value Value Neutral)
;
; Type := Value
;
; Context is a list of (Name, Type) pairs

(define unparse-check
  (lambda (term ctx)
    (pmatch term
      [(inf ,ti) (unparse-inf ti ctx)]
      [(lambda ,tc)
       (let ([x (gensym)])
         `(lambda (,x) ,(unparse-check tc (cons x ctx))))])))

(define unparse-name
  (lambda (name ctx)
    (pmatch name
      [(global ,s) s]
      [(local ,i) (lookup-nth ctx i)])))

(define unparse-inf
  (lambda (term ctx)
    (pmatch term
      [(ann ,tc1 ,tc2) `(: ,(unparse-check tc1 ctx) ,(unparse-check tc2 ctx))]
      [star 'star]
      [(pi ,tc1 ,tc2)
       (let ([x (gensym)])
         `(pi (: ,x ,(unparse-check tc1 ctx))
              ,(unparse-check tc2 (cons x ctx))))]
      [(bound ,i) (lookup-nth ctx i)]
      [(free ,name) (unparse-name name ctx)]
      [(@ ,ti ,tc) `(,(unparse-inf ti ctx) ,(unparse-check tc ctx))]
      [nat 'nat]
      [zero 'zero]
      [(succ ,tc) `(succ ,(unparse-check tc ctx))]
      [(nat-elim ,tc1 ,tc2 ,tc3 ,tc4)
       `(nat-elim 
          ,(unparse-check tc1 ctx)
          ,(unparse-check tc2 ctx)
          ,(unparse-check tc3 ctx)
          ,(unparse-check tc4 ctx))]
      [(vec ,tc1 ,tc2) `(vec ,(unparse-check tc1 ctx) ,(unparse-check tc2 ctx))]
      [(nil ,tc) `(nil ,(unparse-check tc ctx))]
      [(cons ,tc1 ,tc2 ,tc3 ,tc4)
       `(cons 
          ,(unparse-check tc1 ctx)
          ,(unparse-check tc2 ctx)
          ,(unparse-check tc3 ctx)
          ,(unparse-check tc4 ctx))]
      [(vec-elim ,tc1 ,tc2 ,tc3 ,tc4 ,tc5 ,tc6)
       `(vec-elim 
          ,(unparse-check tc1 ctx)
          ,(unparse-check tc2 ctx)
          ,(unparse-check tc3 ctx)
          ,(unparse-check tc4 ctx)
          ,(unparse-check tc5 ctx)
          ,(unparse-check tc6 ctx))])))

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
      [nat 'nat]
      [zero 'zero]
      [(succ ,TermCheck) `(succ ,(parse-check ctx TermCheck))]
      [(nat-elim ,tc1 ,tc2 ,tc3 ,tc4) `(nat-elim
                                         ,(parse-check ctx tc1)
                                         ,(parse-check ctx tc2)
                                         ,(parse-check ctx tc3)
                                         ,(parse-check ctx tc4))]
      [(nil ,tc1) `(nil ,(parse-check ctx tc1))]
      [(vec ,tc1 ,tc2) `(vec ,(parse-check ctx tc1) ,(parse-check ctx tc2))]
      [(cons ,tc1 ,tc2 ,tc3 ,tc4) `(cons
                                         ,(parse-check ctx tc1)
                                         ,(parse-check ctx tc2)
                                         ,(parse-check ctx tc3)
                                         ,(parse-check ctx tc4))]
      [(vec-elim ,tc1 ,tc2 ,tc3 ,tc4 ,tc5 ,tc6)
       `(vec-elim
          ,(parse-check ctx tc1)
          ,(parse-check ctx tc2)
          ,(parse-check ctx tc3)
          ,(parse-check ctx tc4)
          ,(parse-check ctx tc5)
          ,(parse-check ctx tc6)
          )
       ]
      [,x (guard (symbol? x))
          (pmatch (find-depth 0 ctx x)
            [#f `(free (global ,x))]
            [,i `(bound ,i)])]
      [(,e1 ,e2) `(@ ,(parse-inf ctx e1) ,(parse-check ctx e2))]
      )))

(define parse-check
  (lambda (ctx e)
    (pmatch e
      [(lambda (,x) ,body) `(lambda ,(parse-check (cons x ctx) body))]
      [,e `(inf ,(parse-inf ctx e))])))

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

(define plus
  '(:
     (lambda (n1)
       (lambda (n2)
         ((nat-elim
            (lambda (x) (-> nat nat))
            (lambda (x) n2)
            (lambda (k) (lambda (rec) (lambda (n) (succ (rec n)))))
            n1)
          n2)))
    (-> nat (-> nat nat))))

(define append
  `(:
     (lambda (t)
       (lambda (l1)
         (lambda (l2)
           (lambda (xs)
             (lambda (ys)
               (vec-elim
                 t ; elem type
                 (lambda (len)
                   (lambda (vector)
                     (vec t ((,plus len) l2)))); motivator
                 ys ; base case
                 (lambda (len)
                   (lambda (x)
                     (lambda (xs)
                       (lambda (zs)
                         (cons t ((,plus len) l2) x zs))))); inductive step
                 l1 ; length
                 xs ; vector
                 ))))))
     (pi (: t star) (pi (: l1 nat) (pi (: l2 nat)
       (-> (vec t l1) (-> (vec t l2) (vec t ((,plus l1) l2)))))))))

; Take a raw term, parse it, infer its type in the default environment, then
; quote the type to print back out
(define ti
  (lambda (x)
    (unparse-check (quot0 (type-infer 0 default-context (parse-inf '() x))) '())))

; Take a raw term, evaluate it (assuming it typechecks) in the default
; environment, then quote the result to print back out
(define ei
  (lambda (x)
    (unparse-check (quot0 (eval-inf (parse-inf '() x) default-dyn)) '())))

; Typecheck something and run it, and return both
(define run-dep
  (lambda (x)
    (list (ti x) (ei x))))

; Run and check a test
(define run-test
  (lambda (test)
    (pmatch test
      [(,e ,t ,s ,d)
       (let*
         ([TermInf (parse-inf '() e)]
          [OutType (type-infer 0 s TermInf)]
          [OutQuotType (quot0 OutType)]
          [ExpType (parse-check '() t)])
         (if (not (equal? OutQuotType (parse-check '() t)))
           `("type mismatch, oh no" ,OutQuotType ,ExpType)
           (let*
             ([OutVal (eval-inf TermInf d)]
              [OutExp (quot0 OutVal)]
              [OutSchemeExp (unparse-check OutExp '())])
             (if (equal? (eval e) (eval OutSchemeExp))
               (void)
               "oh no, evaluation failure!"))))])))
