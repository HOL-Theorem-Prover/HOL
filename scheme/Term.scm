(module Term mzscheme
  
  (require (prefix Feedback: "Feedback.scm")
           (prefix Lib: "Lib.scm")
           (prefix KernelTypes: "KernelTypes.scm")
           (prefix Type: "Type.scm")
           (prefix Subst: "Subst.scm")
           (prefix Lexis: "Lexis.scm")
           "Sig.scm"
           "0Records.scm"
           "PreKernelRecords.scm"
           "records.scm")
  
  (require (lib "unit.ss")
           (lib "etc.ss")
           (lib "plt-match.ss")
           (lib "compare.ss" "srfi" "67")
           ;(lib "hash.ss" "srfi" "69")
           (only (lib "13.ss" "srfi")
                 string-prefix?))
  
  (require (prefix HOLset: (planet "set.scm" ("soegaard" "galore.plt" 2 2)))
           (prefix Binarymap: (planet "finite-map.scm" ("soegaard" "galore.plt" 2 2))))
  
  (provide (all-defined-except
            key
            table_size
            genvar_prefix
            PREFIX))
  
  (define ERR
    (lambda (x y)
      (Feedback:mk_HOL_ERR "Term" x y)))
  
  (define WARN
    (lambda (x y)
      (Feedback:HOL_WARNING "Term" x y)))
  
  (define key
    (match-lambda
      ((struct Const ((vector r _)))
       r)
      (_
       (raise (ERR "key" "not a constant")))))
  (define table_size 1999)
  
  (define-values/invoke-unit
    (id_of
     insert
     delete
     lookup
     resolve
     add_witness
     app
     slice
     filter
     scope
     del_segment
     anachronize
     all_entries)
    SIG
    TermSig
    key
    ERR
    table_size)
  
  (define-values (eqc hil imp)
    (let ((eq_const
           (make-Const
            (vector (KernelTypes:mk_id "=" "min")
                    (make-POLY (Type:--> Type:alpha
                                         (Type:--> Type:alpha Type:bool))))))
          (hil_const
           (make-Const
            (vector (KernelTypes:mk_id "@" "min")
                    (make-POLY (Type:--> (Type:--> Type:alpha Type:bool)
                                         Type:alpha)))))
          (imp_const
           (make-Const
            (vector (KernelTypes:mk_id "==>" "min")
                    (make-GRND (Type:--> Type:bool
                                         (Type:--> Type:bool Type:bool)))))))
      (values (vector-ref (TermSig:insert eq_const) 0)
              (vector-ref (TermSig:insert hil_const) 0)
              (vector-ref (TermSig:insert imp_const) 0))))
  
  (define mk_clos
    (match-lambda
      ((vector s (struct Bv (i)))
       (match (Subst:exp_rel (vector s i))
         ((vector 0 (struct SOME (t)))
          t)
         ((vector k (struct SOME (t)))
          (mk_clos (Subst:shift (vector (vector k Subst:id)) t)))
         ((vector v 'NONE)
          (make-Bv v))))
      ((vector s (? Fv? t))
       t)
      ((vector s (? Const? t))
       t)
      ((vector s (struct Clos (Env Body)))
       (make-Clos (Subst:comp mk_clos (vector s Env)) Body))
      ((vector s t)
       (make-Clos s t))))
  
  (define push_clos
    (match-lambda
      ((struct Clos (E (struct Comb (f x))))
       (make-Comb (mk_clos (vector E f))
                  (mk_clos (vector E x))))
      ((struct Clos (E (struct Abs (v M))))
       (make-Abs v (mk_clos (vector (Subst:lift (vector 1 E)) M))))
      (_
       (raise (ERR "push_clos" "not a subst")))))
  
  (define type_of
    (letrec ((lookup list-ref)
             (ty_of
              (match-lambda*
                ((list (struct Fv (_ Ty)) _)
                 Ty)
                ((list (struct Const ((vector _ (struct GRND (Ty))))) _)
                 Ty)
                ((list (struct Const ((vector _ (struct POLY (Ty))))) _)
                 Ty)
                ((list (struct Bv (i)) E)
                 (lookup i E))
                ((list (struct Comb (Rator _)) E)
                 (Lib:snd (Type:dom_rng (ty_of Rator E))))
                ((list (? Clos? t) E)
                 (ty_of (push_clos t) E))
                ((list (struct Abs ((struct Fv (_ Ty)) Body)) E)
                 (Type:--> Ty (ty_of Body (cons Ty E))))
                ((list _ _)
                 (raise (ERR "type_of" "term construction"))))))
      (lambda (tm)
        (ty_of tm ()))))
  
  (define is_bvar Bv?)
  (define is_var Fv?)
  (define is_const Const?)
  (define is_comb
    (match-lambda
      ((struct Comb (_ _))
       #t)
      ((struct Clos (_ (struct Comb (_ _))))
       #t)
      (_
       #F)))
  (define is_abs
    (match-lambda
      ((struct Abs (_ _))
       #t)
      ((struct Clos (_ (struct Abs (_ _))))
       #t)
      (_
       #F)))
  
  (define type_vars_in_term
    (letrec ((tyV
              (match-lambda*
                ((list (struct Fv (_ Ty)) k)
                 (k (Type:type_vars Ty)))
                ((list (struct Bv (_)) k)
                 (k ()))
                ((list (struct Const ((vector _ (struct GRND (_))))) k)
                 (k ()))
                ((list (struct Const ((vector _ (struct POLY (Ty))))) k)
                 (k (Type:type_vars Ty)))
                ((list (struct Comb (Rator Rand)) k)
                 (tyV Rand
                      (lambda (q1)
                        (tyV Rator
                             (lambda (q2)
                               (k (Lib:union q2 q1)))))))
                ((list (struct Abs (Bvar Body)) k)
                 (tyV Body
                      (lambda (q1)
                        (tyV Bvar
                             (lambda (q2)
                               (k (Lib:union q2 q1)))))))
                ((list t k)
                 (tyV (push_clos t) k)))))
      (lambda (tm)
        (tyV tm Lib:I))))
  
  (define free_vars
    (letrec ((FV
              (match-lambda*
                ((list (? Fv? v) A k)
                 (k (Lib:insert v A)))
                ((list (struct Comb (f x)) A k)
                 (FV f A (lambda (q) (FV x q k))))
                ((list (struct Abs (_ Body)) A k)
                 (FV Body A k))
                ((list (? Clos? t) A k)
                 (FV (push_clos t) A k))
                ((list _ A k)
                 (k A)))))
      (lambda (tm)
        (FV tm () Lib:I))))
  
  (define free_vars_lr
    (letrec ((FV
              (match-lambda*
                ((list (list-rest (? Fv? v) t) A)
                 (FV t (Lib:insert v A)))
                ((list (list-rest (? Bv? _) t) A)
                 (FV t A))
                ((list (list-rest (? Const? _) t) A)
                 (FV t A))
                ((list (list-rest (struct Comb (M N)) t) A)
                 (FV (list* M N t) A))
                ((list (list-rest (struct Abs (_ M)) t) A)
                 (FV (cons M t) A))
                ((list (list-rest (? Clos? M) t) A)
                 (FV (push_clos (cons M t)) A))
                ((list (list) A)
                 (reverse A)))))
      (lambda (tm)
        (FV (list tm) ()))))
  
  (define all_vars
    (letrec ((vars
              (match-lambda*
                ((list (? Fv? v) A)
                 (Lib:insert v A))
                ((list (struct Comb (Rator Rand)) A)
                 (vars Rand (vars Rator A)))
                ((list (struct Abs (Bvar Body)) A)
                 (vars Body (vars Bvar A)))
                ((list (? Clos? t) A)
                 (vars (push_clos t) A))
                ((list _ A)
                 A))))
      (lambda (tm)
        (vars tm ()))))
  
  (define (free_varsl tm_list)
    (Lib:itlist (compose Lib:union free_vars) tm_list ()))
  (define (all_varsl tm_list)
    (Lib:itlist (compose Lib:union all_vars) tm_list ()))
  
  (define var_compare
    (match-lambda
      ((vector (struct Fv (s1 ty1))
               (struct Fv (s2 ty2)))
       (match (string-compare s1 s2)
         (0 (Type:compare (vector ty1 ty2)))
         (x x)))
      (_
       (raise (ERR "var_compare" "variables required")))))
  
  (define empty_varset
    (HOLset:empty (lambda (x y) (var_compare (vector x y)))))
  
  (define (compare p)
    (if (eq? (vector-ref p 0)
             (vector-ref p 1))
        0
        (match p
          ((vector (? Clos? t1) t2)
           (compare (vector (push_clos t1) t2)))
          ((vector t1 (? Clos? t2))
           (compare (vector t1 (push_clos t2))))
          ((vector (? Fv? u) (? Fv? v))
           (var_compare p))
          ((vector (? Fv? _) _)
           -1)
          ((vector (? Bv? _) (? Fv? _))
           1)
          ((vector (struct Bv (i)) (struct Bv (j)))
           (integer-compare i j))
          ((vector (? Bv? _) _)
           -1)
          ((vector (? Const? _) (? Fv? _))
           1)
          ((vector (? Const? _) (? Bv? _))
           1)
          ((vector (struct Const ((vector c1 ty1)))
                   (struct Const ((vector c2 ty2))))
           (match (KernelTypes:compare (vector c1 c2))
             (0
              (Type:compare (vector (KernelTypes:to_hol_type ty1)
                                    (KernelTypes:to_hol_type ty2))))
             (x x)))
          ((vector (? Const? _) _)
           -1)
          ((vector (struct Comb (M N))
                   (struct Comb (P Q)))
           (match (compare (vector M P))
             (0
              (compare N Q))
             (x x)))
          ((vector (? Comb? _) (? Abs? _))
           -1)
          ((vector (? Comb? _) _)
           1)
          ((vector (struct Abs ((struct Fv (_ ty1)) M))
                   (struct Abs ((struct Fv (_ ty2)) N)))
           (match (Type:compare ty1 ty2)
             (0
              (compare (vector M N)))
             (x x)))
          ((vector (? Abs? _) _)
           1))))
  
  (define empty_tmset
    (HOLset:empty (lambda (x y) (compare (vector x y)))))
  (define (term_eq t1 t2)
    (zero? (compare (vector t1 t2))))
  
  (define FVL
    (match-lambda*
      ((list (list) A)
       A)
      ((list (list-rest (? Fv? v) rst) A)
       (FVL rst (HOLset:insert v A)))
      ((list (list-rest (struct Comb (Rator Rand)) rst) A)
       (FVL (list* Rator Rand rst) A))
      ((list (list-rest (struct Abs(_ Body)) rst) A)
       (FVL (cons Body rst) A))
      ((list (list-rest (? Clos? t) rst) A)
       (FVL (push_clos (cons t rst)) A))
      ((list (list-rest _ rst) A)
       (FVL rst A))))
  
  (define (free_in tm t)
    (letrec ((f1
              (match-lambda
                ((struct Comb(Rator Rand))
                 (or (free_in Rator)
                     (free_in Rand)))
                ((struct Abs (_ Body))
                 (free_in Body))
                ((? Clos? t)
                 (free_in (push_clos t)))
                (_
                 #f)))
             (f2 
              (lambda (t)
                (or (term_eq t tm)
                    (f1 t)))))
      (f2 t)))
  
  (define (var_occurs M t)
    (with-handlers ((error_record?
                     (raise (ERR "var_occurs" "not a variable"))))
      (letrec ((v
                (match M
                  ((struct Fv (v1 v2)) (vector v1 v2))
                  (_ (raise (ERR "" "")))))
               (occ
                (match-lambda
                  ((struct Fv (u1 u2))
                   (equal? v (vector u1 u2)))
                  ((? Bv? _)
                   #f)
                  ((? Const? _)
                   #f)
                  ((struct Comb (Rator Rand))
                   (or (occ Rand)
                       (occ Rator)))
                  ((struct Abs (_ Body))
                   (occ Body))
                  ((? Clos? t)
                   (occ (push_clos t))))))
        (occ t))))
  
  (define mk_var make-Fv)
  
  (define (inST s)
    (not (null? (TermSig:resolve s))))
  
  (define (mk_primed_var t)
    (let ((Name (vector-ref t 0))
          (Ty (vector-ref t 1)))
      (letrec ((next (Lexis:nameStrm Name))
               (spin (lambda (s)
                       (if (inST s)
                           (spin (next))
                           s))))
        (mk_var (spin Name) Ty))))
  
  (define genvar_prefix "%%genvar%%")  
  (define (genvar ty)
    (let* ((num2name
            (lambda (i)
              (string-append genvar_prefix
                             (number->string i))))
           (nameStrm
            (Lib:mk_istream add1 0 num2name)))
      (make-Fv (Lib:state (Lib:next nameStrm)) ty)))  
  (define (genvars ty n)
    (define (gen acc n)
      (if (<= n 0)
          (reverse acc)
          (gen (genvar (cons ty acc)) (sub1 n))))
    (gen () n))  
  (define is_genvar
    (match-lambda
      ((struct Fv (Name _))
       (string-prefix? genvar_prefix Name))
      (_ #f)))
  
  (define gen_variant
    (let ((var_name
           (match-lambda*
             ((list _ (struct Fv (Name _)))
              Name)
             ((list caller _)
              (raise (ERR caller "not a variable"))))))
      (lambda (P caller)
        (match-lambda*
          ((list vlist (struct Fv (Name Ty)))
           (letrec ((next (Lexis:nameStrm Name))
                    (L (map (lambda (t) (var_name caller t)) vlist))
                    (away
                     (lambda (s)
                       (if (member s L)
                           (away (next))
                           s)))
                    (loop
                     (lambda (name)
                       (let ((s (away name)))
                         (if (P s)
                             (loop (next))
                             s)))))
             (mk_var (loop Name) Ty)))
          ((list _ _)
           (raise (ERR caller "2nd argument should be a variable")))))))
  
  (define variant
    (gen_variant inST "variant"))
  (define prim_variant
    (gen_variant (Lib:K false) "prim_variant"))
  
  (define (decls t)
    (map (compose (lambda (v) (vector-ref v 0)) TermSig:resolve) t))
  
  (define (prim_mk_const t)
    (let ((Name (vector-ref t 0))
          (Thy (vector-ref t 1)))
      (match (TermSig:lookup t)
        ((struct SOME ((vector const ...)))
         const)
        ('NONE
          (raise (ERR "prim_mk_const"
                      (string-append (Lib:stringquote Name)
                                     " not found in theory "
                                     (Lib:stringquote Thy))))))))
  
  (define (ground x)
    (Lib:all (match-lambda
               ((vector redex residue)
                (not (Type:polymorphic residue))))
             x))
  
  (define create_const
    (match-lambda*
      ((list errstr (and const (struct Const ((vector _ (struct GRND (pat)))))) Ty)
       (if (equal? Ty pat)
           const
           (raise (ERR "create_const" "not a type match"))))
      ((list errstr (and const (struct Const ((vector r (struct POLY (pat)))))) Ty)
       (with-handlers ((error_record?
                        (lambda ()
                          (raise (ERR errstr
                                      (string-append "Not a type instance: "
                                                     (KernelTypes:id_to_string r)))))))
         (match (Type:raw_match_type pat Ty (vector () ()))
           ((vector (list) _)
            const)
           ((vector S (list))
            (make-Const r (if (ground S)
                              (make-GRND Ty)
                              (make-POLY Ty))))
           ((vector S _)
            (make-Const r (make-POLY Ty))))))
      ((list errstr _ _)
       (raise (ERR errstr "non-constant in signature")))))
  
  (define (mk_thy_const t)
    (let ((Thy (vector-ref t 0))
          (Name (vector-ref t 1))
          (Ty (vector-ref t 2)))
      (match (TermSig:lookup (vector Name Thy))
        ('NONE
          (raise (ERR "mk_thy_const"
                      (string-append (KernelTypes:fullname (vector Name Thy))
                                     " not found"))))
        ((struct SOME ((vector const ...)))
         (create_const "mk_thy_const" const Ty)))))
  
  (define (first_decl fname Name)
    (match (TermSig:resolve Name)
      ((list)
       (raise (ERR fname
                   (string-append Name " not found"))))
      ((list (vector const ...))
       const)
      ((list-rest (vector const ...) _)
       (WARN fname
             (string-append (Lib:stringquote Name)
                            ": more than one possibility"))
       const)))
  
  (define (current_const Name)
    (first_decl "current_const" Name))
  
  (define (mk_const t)
    (let ((Name (vector-ref t 0))
          (Ty (vector-ref t 1)))
      (create_const "mk_const"
                    (first_decl "mk_const" Name)
                    Ty)))
  
  (define (all_consts t)
    (map (compose (lambda (t) (vector-ref t 0))
                  TermSig:all_entries)
         t))
  (define (thy_consts t)
    (map (compose (lambda (t) (vector-ref t 0))
                  TermSig:slice)
         t))
  
  (define same_const
    (match-lambda*
      ((list (struct Const ((vector id1 _)))
             (struct Const ((vector id2 _))))
       (KernelTypes:same_id (vector id1 id2)))
      ((list _ _)
       #f)))
  
  (define-values (mk_comb list_mk_comb)
    (letrec ((INCOMPAT_TYPES
              (lambda (t)
                (Lib:C ERR "incompatible types" t)))
             (lmk_comb
              (lambda (err)
                (letrec ((loop
                          (match-lambda*
                            ((list (vector A _) (list))
                             A)
                            ((list (vector A typ) (list-rest tm rst))
                             (match (Lib:with_exn (Type:dom_rng typ) err)
                               ((vector ty1 ty2)
                                (if (equal? (type_of tm) ty1)
                                    (loop (vector (make-Comb A tm) ty2) rst)
                                    (raise err))))))))
                  (match-lambda
                    ((vector f L)
                     (loop (vector f (type_of f)) L))))))
             (mk_comb0
              (lmk_comb (INCOMPAT_TYPES "mk_comb"))))
      (values
       (match-lambda
         ((vector (and r (struct Abs ((struct Fv (_ Ty)) _))) Rand)
          (if (equal? (type_of Rand) Ty)
              (make-Comb r)
              (raise (INCOMPAT_TYPES "mk_comb"))))
         ((vector (and r (struct Clos (_ (struct Abs ((struct Fv (_ Ty)) _))))) Rand)
          (if (equal? (type_of Rand) Ty)
              (make-Comb r)
              (raise (INCOMPAT_TYPES "mk_comb"))))
         ((vector Rator Rand)
          (mk_comb0 (vector Rator (list Rand)))))
       (lmk_comb (INCOMPAT_TYPES "list_mk_comb")))))
  
  (define dest_var
    (match-lambda
      ((struct Fv (v1 v2))
       (vector v1 v2))
      (_
       (raise (ERR "dest_var" "not a var")))))
  
  (define (rename_bvar s t)
    (match t
      ((struct Abs ((struct Fv (_ Ty)) Body))
       (make-Abs (make-Fv s Ty) Body))
      ((struct Clos (_ (? Abs? _)))
       (rename_bvar s (push_clos t)))
      (_
       (raise (ERR "rename_bvar" "not an abstraction")))))
  
  (define (aconv t1 t2)
    (or (eq? t1 t2)
        (match (vector t1 t2)
          ((vector (struct Comb (M N))
                   (struct Comb (P Q)))
           (and (aconv N Q)
                (aconv M P)))
          ((vector (struct Abs ((struct Fv (_ ty1)) M))
                   (struct Abs ((struct Fv (_ ty2)) N)))
           (and (equal? ty1 ty2)
                (aconv M N)))
          ((vector (struct Clos (e1 b1))
                   (struct Clos (e2 b2)))
           (or (and (eq? e1 e2)
                    (eq? b1 b2))
               (aconv (push_clos t1) (push_clos t2))))
          ((vector (? Clos? _) _)
           (aconv (push_clos t1) t2))
          ((vector _ (? Clos? _))
           (aconv t1 (push_clos t2)))
          ((vector M N)
           (equal? M N)))))
  
  (define beta_conv
    (match-lambda
      ((struct Comb ((struct Abs (_ Body)) (struct Bv (0))))
       Body)
      ((struct Comb ((struct Abs (_ Body)) Rand))
       (letrec ((subs
                 (match-lambda
                   ((vector (and tm (struct Bv (j))) i)
                    (if (equal? i j)
                        Rand
                        tm))
                   ((vector (struct Comb (Rator Rand)) i)
                    (make-Comb (subs (vector Rator i)) (subs (vector Rand i))))
                   ((vector (struct Abs (v Body)) i)
                    (make-Abs v (subs (vector Body (add1 i)))))
                   ((vector (? Clos? tm) i)
                    (subs (vector (push_clos tm) i)))
                   ((vector tm _)
                    tm))))
         (subs (vector Body 0))))
      ((struct Comb ((? Clos? x) Rand))
       (beta_conv (vector (make-Comb (push_clos x) Rand))))
      ((? Clos? x)
       (beta_conv (push_clos x)))
      (_
       (raise (ERR "beta_conv" "not a beta-redex")))))
  
  (define lazy_beta_conv
    (match-lambda
      ((struct Comb ((struct Abs (_ Body)) Rand))
       (mk_clos (vector (make-Cons Subst:id Rand) Body)))
      ((struct Comb ((struct Clos (Env (struct Abs (_ Body)))) Rand))
       (mk_clos (vector (make-Cons Env Rand) Body)))
      ((? Clos? t)
       (lazy_beta_conv (push_clos t)))
      (_
       (raise (ERR "lazy_beta_conv" "not a beta-redex")))))
  
  (define eta_conv
    (letrec ((pop
              (match-lambda
                ((vector (and tm (? Bv? i)) k)
                 (if (equal? i k)
                     (raise (ERR "eta_conv" "not an eta-redex"))
                     tm))
                ((vector (struct Comb (Rator Rand)) k)
                 (make-Comb (pop (vector Rator k))
                            (pop (vector Rand k))))
                ((vector (struct Abs (v Body)) k)
                 (make-Abs v (pop (vector Body (add1 k)))))
                ((vector (? Clos? tm) k)
                 (pop (vector (push_clos tm) k)))
                ((vector tm k)
                 tm)))
             (eta_body
              (match-lambda 
                ((struct Comb (Rator (struct Bv (0))))
                 (pop (vector Rator 0)))
                ((? Clos? tm)
                 (eta_body (push_clos tm)))
                (_
                 (raise (ERR "eta_conv" "not an eta-redex"))))))
      (match-lambda
        ((struct Abs (_ Body))
         (eta_body Body))
        ((? Clos? tm)
         (eta_conv (push_clos tm)))
        (_
         (raise (ERR "eta_conv" "not an eta-redex"))))))
  
  (define emptysubst
    (Binarymap:empty (lambda (x y) (compare (vector x y)))))
  
  (define subst
    (letrec ((addb
              (match-lambda*
                ((list (list) A)
                 A)
                ((list (list-rest (vector redex residue) t)
                       (vector A b))
                 (addb t
                       (if (equal? (type_of redex)
                                   (type_of residue))
                           (vector (Binarymap:insert residue A redex)
                                   (and (is_var redex)
                                        b))
                           (raise (ERR "subst" "redex has different type than residue"))))))))
      (match-lambda
        ((list)
         Lib:I)
        (theta
         (match (addb theta (vector emptysubst #t))
           ((vector fmap b)
            (letrec ((vsubs
                      (match-lambda
                        ((? Fv? v)
                         (match (Binarymap:get v fmap)
                           (#f v)
                           ((list-rest key ele) ele)))
                        ((struct Comb (Rator Rand))
                         (make-Comb (vsubs Rator) (vsubs Rand)))
                        ((struct Abs (Bvar Body))
                         (make-Abs Bvar (vsubs Body)))
                        ((? Clos? c)
                         (vsubs (push_clos c)))
                        (tm
                         tm)))
                     (subs
                      (lambda (tm)
                        (match (Binarymap:get tm fmap)
                          ((list-rest key residue)
                           residue)
                          (#f
                           (match tm
                             ((struct Comb (Rator Rand))
                              (make-Comb (subs Rator) (subs Rand)))
                             ((struct Abs (Bvar Body))
                              (make-Abs Bvar (subs Body)))
                             ((? Clos? _)
                              (subs (push_clos tm)))
                             (_
                              tm)))))))
              (if b vsubs subs))))))))
  
  (define inst
    (match-lambda*
      ((list (list) tm)
       tm)
      ((list theta tm)
       (letrec ((inst1
                 (match-lambda
                   ((? Bv? bv)
                    bv)
                   ((and c (struct Const ((vector _ (? GRND? _)))))
                    c)
                   ((and c (struct Const ((vector r (struct POLY (Ty))))))
                    (match (Type:ty_sub theta Ty)
                      ('SAME c)
                      ((struct Lib:DIFF (ty))
                       (make-Const r 
                                   ((if (Type:polymorphic ty)
                                        make-POLY
                                        make-GRND)
                                    ty)))))
                   ((and v (struct Fv (Name Ty)))
                    (match (Type:ty_sub theta Ty)
                      ('SAME v)
                      ((struct Lib:DIFF (ty))
                       (make-Fv Name ty))))
                   ((struct Comb (Rator Rand))
                    (make-Comb (inst1 Rator) (inst1 Rand)))
                   ((struct Abs (Bvar Body))
                    (make-Abs (inst1 Bvar) (inst1 Body)))
                   ((? Clos? t)
                    (inst1 (push_clos t))))))
         (inst1 tm)))))
  
  (define dest_comb
    (match-lambda
      ((struct Comb (r1 r2))
       (vector r1 r2))
      ((? Clos? t)
       (dest_comb (push_clos t)))
      (_
       (raise (ERR "dest_comb" "not a comb")))))
  
  (define list_mk_binder
    (let* ((FORMAT
            (lambda (s)
              (ERR "list_mk_binder" s)))
           (check_opt
            (match-lambda
              ('NONE
                Lib:I)
              ((struct SOME (c))
               (if (not (is_const c))
                   (lambda (s) (raise (FORMAT s)))
                   (match (Lib:total (compose Lib:fst Type:dom_rng Lib:fst Type:dom_rng type_of) c)
                     ('NONE
                       (lambda (s) (raise (FORMAT s))))
                     ((struct SOME (ty))
                      (lambda (abs)
                        (let ((dom
                               (Lib:fst (Type:dom_rng (type_of abs)))))
                          (mk_comb (vector (inst (list (Lib:||-> ty dom)) c) abs)))))))))))
      (lambda (opt)
        (let ((f (check_opt opt)))
          (match-lambda
            ((vector vlist tm)
             (if (not (Lib:all is_var vlist))
                 (raise (ERR "list_mk_binder" ""))
                 (with-handlers (((lambda (e) #t)
                                  (lambda (e) (raise (Feedback:wrap_exn "Term" "list_mk_binder" e)))))
                   (letrec ((varmap
                             (make-hash-table 'equal))
                            (enum
                             (match-lambda*
                               ((list (list) _ A)
                                A)
                               ((list (list-rest h t) i A)
                                (hash-table-put! varmap h i)
                                (enum t (sub1 i) (cons h A)))))
                            (rvlist
                             (enum vlist (sub1 (length vlist)) ()))
                            (lookup
                             (lambda (v vmap)
                               (match (hash-table-get vmap v
                                                      (lambda () 'NONE))
                                 ('NONE v)
                                 (i (make-Bv i)))))
                            (increment
                             (lambda (vmap)
                               (let ((new (make-hash-table 'equal)))
                                 (hash-table-for-each vmap
                                                      (lambda (key d)
                                                        (hash-table-put! new key (add1 d))))
                                 new)))
                            (bind
                             (match-lambda*
                               ((list (? Fv? v) vmap k)
                                (k (lookup v vmap)))
                               ((list (struct Comb (M N)) vmap k)
                                (bind M vmap
                                      (lambda (m)
                                        (bind N vmap
                                              (lambda (n)
                                                (k (make-Comb m n)))))))
                               ((list (struct Abs (v M)) vmap k)
                                (bind M (increment vmap)
                                      (lambda (q)
                                        (k (make-Abs v q)))))
                               ((list (? Clos? t) vmap k)
                                (bind (push_clos t) vmap k))
                               ((list tm vmap k)
                                (k tm)))))
                     (Lib:rev_itlist (lambda (v)
                                       (lambda (M)
                                         (f (make-Abs v M))))
                                     rvlist
                                     (bind tm varmap Lib:I)))))))))))
  
  (define list_mk_abs
    (list_mk_binder 'NONE))
  
  (define mk_abs
    (match-lambda
      ((vector (? Fv? Bvar) Body)
       (letrec ((bind
                 (match-lambda*
                   ((list (? Fv? v) i)
                    (if (equal? v Bvar)
                        (make-Bv i)
                        v))
                   ((list (struct Comb (Rator Rand)) i)
                    (make-Comb (bind Rator i) (bind Rand i)))
                   ((list (struct Abs (Bvar Body)) i)
                    (make-Abs Bvar (bind Body (add1 i))))
                   ((list (? Clos? t) i)
                    (bind (push_clos t) i))
                   ((list tm _)
                    tm))))
         (make-Abs Bvar (bind Body 0))))
      (_
       (raise (ERR "mk_abs" "Bvar not a variable")))))
  
  (define-struct PREFIX (i))
  
  (define strip_binder
    (letrec ((peel
              (match-lambda*
                ((list f (? Clos? t) A)
                 (peel f (push_clos t) A))
                ((list f tm A)
                 (match (f tm)
                   ((struct SOME ((struct Abs (v M))))
                    (peel f M (cons v A)))
                   (otherwise
                    (vector A tm))))))
             (array_to_revlist
              (lambda (A)
                (letrec ((top (sub1 (vector-length A)))
                         (For
                          (lambda (i B)
                            (if (> i top)
                                B
                                (For (add1 i) (cons (vector-ref A i) B))))))
                  (For 0 ()))))
             (vi_empty
              (HOLset:empty
               (match-lambda
                 ((vector (vector v1 i1)
                          (vector v2 i2))
                  (var_compare (vector v1 v2))))))
             (add_vi
              (lambda (viset vi)
                (if (HOLset:member? vi viset)
                    viset
                    (HOLset:insert vi viset))))
             (trypush_clos
              (match-lambda
                ((? Clos? x)
                 (push_clos x))
                (t
                 t))))
      (lambda (opt)
        (let ((f
               (match opt
                 ('NONE
                   (match-lambda
                     ((? Abs? t)
                      (make-SOME t))
                     ((and t (struct Clos (_ (? Abs? _))))
                      (make-SOME (push_clos t)))
                     (other
                      'NONE)))
                 ((struct SOME (c))
                  (lambda (t)
                    (match (dest_comb t)
                      ((vector rator rand)
                       (with-handlers ((error_record?
                                        'NONE))
                         (if (same_const rator c)
                             (make-SOME (trypush_clos rand))
                             'NONE)))))))))
          (lambda (tm)
            (letrec-values (((prefixl body)
                             (let ((temp (peel f tm ())))
                               (values (vector-ref temp 0)
                                       (vector-ref temp 1))))
                            ((prefix)
                             (vector->list prefixl))
                            ((vmap)
                             (lambda (x)
                               (vector-ref prefix x)))
                            ((insertAVbody insertAVprefix lookAV dupls)
                             (letrec ((AV
                                       (make-hash-table 'equal))
                                      (insertl
                                       (match-lambda*
                                         ((list (list) _ dupls)
                                          dupls)
                                         ((list (list-rest x rst) i dupls)
                                          (let ((n (Lib:fst (dest_var x))))
                                            (cond ((hash-table-get AV n #f)
                                                   (insertl rst (add1 i) (cons (vector x i) dupls)))
                                                  (else
                                                   (hash-table-put! AV n (make-PREFIX i))
                                                   (insertl rst (add1 i) dupls)))))))
                                      (dupls
                                       (insertl prefixl 0 ())))
                               (values (lambda (s) (hash-table-put! AV s 'BODY))
                                       (match-lambda
                                         ((vector s i)
                                          (hash-table-put! AV s (make-PREFIX i))))
                                       (lambda (s)
                                         (with-handlers ((exn:fail:contract?
                                                          (lambda (e) 'NONE)))
                                           (make-SOME (hash-table-get AV s))))
                                       dupls)))
                            ((variantAV)
                             (lambda (n)
                               (letrec ((next
                                         (Lexis:nameStrm n))
                                        (loop
                                         (lambda (s)
                                           (match (lookAV s)
                                             ('NONE
                                               s)
                                             ((? SOME? _)
                                              (loop (next)))))))
                                 (loop n))))
                            ((CVs)
                             (match-lambda*
                               ((list (and v (struct Fv (n _))) capt k)
                                (match (lookAV n)
                                  ((struct SOME ((struct PREFIX (i))))
                                   (k (add_vi capt (vector (vmap i) i))))
                                  ((struct SOME ('BODY))
                                   (k capt))
                                  ('NONE
                                    (insertAVbody n)
                                    (k capt))))
                               ((list (struct Comb (M N)) capt k)
                                (CVs N capt (lambda (c) (CVs M c k))))
                               ((list (struct Abs (_ M)) capt k)
                                (CVs M capt k))
                               ((list (? Clos? t) capt k)
                                (CVs (push_clos t) capt k))
                               ((list tm capt k)
                                (k capt))))
                            ((unclash)
                             (match-lambda*
                               ((list insert (list))
                                ())
                               ((list insert (list-rest (vector v i) rst))
                                (let* ((temp2
                                        (dest_var v))
                                       (n
                                        (vector-ref temp2 0))
                                       (ty
                                        (vector-ref temp2 1))
                                       (n1
                                        (variantAV n))
                                       (v1
                                        (mk_var (vector n1 ty))))
                                  (vector-set! prefix i v1)
                                  (insert (vector n1 i))
                                  (unclash insert rst)))))
                            ((unbind)
                             (match-lambda*
                               ((list (and v (struct Bv (i))) j k)
                                (k
                                 (with-handlers (((lambda (x) #t)
                                                  (lambda (x) v)))
                                   (vmap (- i j)))))
                               ((list (struct Comb (M N)) j k)
                                (unbind M j
                                        (lambda (m)
                                          (unbind N j
                                                  (lambda (n)
                                                    (k (make-Comb m n)))))))
                               ((list (struct Abs (v M)) j k)
                                (unbind M (add1 j)
                                        (lambda (q)
                                          (k (make-Abs v q)))))
                               ((list (? Clos? t) j k)
                                (unbind (push_clos t) j k))
                               ((list tm j k)
                                (k tm)))))
              (unclash insertAVprefix (reverse dupls))
              (unclash (compose insertAVbody Lib:fst)
                       (HOLset:elements (CVs body vi_empty Lib:I)))
              (vector (array_to_revlist prefix)
                      (unbind body 0 Lib:I))))))))
  
  (define strip_abs
    (strip_binder 'NONE))
  
  (define dest_abs
    (match-lambda
      ((struct Abs ((and Bvar (struct Fv (Name Ty))) Body))
       (letrec ((dest
                 (match-lambda
                   ((vector (and v (struct Bv (j))) i)
                    (if (equal? i j)
                        Bvar
                        v))
                   ((vector (and v (struct Fv (s _))) _)
                    (if (equal? Name s)
                        (raise 'CLASH)
                        v))
                   ((vector (struct Comb (Rator Rand)) i)
                    (make-Comb (dest (vector Rator i))
                               (dest (vector Rand i))))
                   ((vector (struct Abs (Bvar Body)) i)
                    (make-Abs Bvar (dest (vector Body (add1 i)))))
                   ((vector (? Clos? t) i)
                    (dest (vector (push_clos t) i)))
                   ((vector tm _)
                    tm))))
         (with-handlers (((lambda (x)
                            (eq? x 'CLASH))
                          (lambda (x)
                            (dest_abs (make-Abs (variant (free_vars Body) Bvar) Body)))))
           (vector Bvar (dest (vector Body 0))))))
      ((? Clos? t)
       (dest_abs (push_clos t)))
      (_
       (raise (ERR "dest_abs" "not a lambda abstraction")))))
  
  (define break_abs
    (match-lambda
      ((struct Abs (_ Body))
       Body)
      ((? Clos? t)
       (break_abs (push_clos t)))
      (_
       (raise (ERR "break_abs" "not an abstraction")))))
  
  (define dest_thy_const
    (match-lambda
      ((struct Const ((vector id ty)))
       (match (KernelTypes:dest_id id)
         ((vector name thy)
          (vector thy name (KernelTypes:to_hol_type ty)))))
      (_
       (raise (ERR"dest_thy_const" "not a const")))))
  
  (define break_const
    (match-lambda
      ((struct Const (p))
       ((Lib:|##| Lib:I KernelTypes:to_hol_type) p))
      (_
       (raise (ERR "break_const" "not a const")))))
  
  (define dest_const
    (match-lambda
      ((struct Const ((vector id ty)))
       (vector (KernelTypes:name_of id) (KernelTypes:to_hol_type ty)))
      (_
       (raise (ERR "dest_const" "not a const")))))
  
  (define rator
    (match-lambda
      ((struct Comb (Rator _))
       Rator)
      ((struct Clos (Env (struct Comb (Rator _))))
       (mk_clos (vector Env Rator)))
      (_
       (raise (ERR "rator" "not a comb")))))
  
  (define rand
    (match-lambda
      ((struct Comb (_ Rand))
       Rand)
      ((struct Clos (Env (struct Comb (_ Rand))))
       (mk_clos (vector Env Rand)))
      (_
       (raise (ERR "rand" "not a comb")))))
  
  (define bvar
    (compose Lib:fst dest_abs))
  (define body
    (compose Lib:snd dest_abs))
  
  (define RM
    (letrec ((MERR
              (lambda (s)
                (raise (ERR "raw_match_term error" s))))
             (free
              (match-lambda*
                ((list (struct Bv (i)) n)
                 (< i n))
                ((list (struct Comb (Rator Rand)) n)
                 (and (free Rand n)
                      (free Rator n)))
                ((list (struct Abs (_ Body)) n)
                 (free Body (add1 n)))
                ((list (? Clos? t) n)
                 (free (push_clos t) n))
                ((list _ _)
                 #t)))
             (lookup
              (match-lambda*
                ((list x ids (list))
                 (if (HOLset:member? x ids)
                     (make-SOME x)
                     'NONE))
                ((list x ids (list-rest (vector redex residue) t))
                 (if (equal? x redex)
                     (make-SOME residue)
                     (lookup x ids t)))))
             (bound_by_scope
              (lambda (scoped M)
                (if scoped
                    (not (free M 0))
                    #f)))
             (tymatch
              Type:raw_match_type))
      (match-lambda*
        ((list (list) theta)
         theta)
        ((list (list-rest (vector (and v (struct Fv (_ Ty))) tm scoped) rst)
               (vector (and S1 (vector tmS Id)) tyS))
         (if (bound_by_scope scoped tm)
             (MERR "variable bound by scope")
             (RM rst
                 (vector (match (lookup v Id tmS)
                           ('NONE
                             (if (equal? v tm)
                                 (vector tmS (HOLset:insert v Id))
                                 (vector (cons (Lib:||-> v tm) tmS) Id)))
                           ((struct SOME (tm1))
                            (if (aconv tm1 tm)
                                S1
                                (MERR "double bind on variable"))))
                         (tymatch Ty (type_of tm) tyS)))))
        ((list (list-rest (vector (struct Const ((vector c1 ty1)))
                                  (struct Const ((vector c2 ty2)))
                                  _)
                          rst)
               (vector tmS tyS))
         (RM rst
             (if (not (equal? c1 c2))
                 (MERR "different constants")
                 (match (vector ty1 ty2)
                   ((vector (? GRND? _) (? POLY? _))
                    (MERR "ground const vs. polymorphic const"))
                   ((vector (struct GRND (pat)) (struct GRND (obj)))
                    (if (equal? pat obj)
                        (vector tmS tyS)
                        (MERR "const-const with different (ground) types")))
                   ((vector (struct POLY (pat)) (struct GRND (obj)))
                    (vector tmS (tymatch pat obj tyS)))
                   ((vector (struct POLY (pat)) (struct POLY (obj)))
                    (vector tmS (tymatch pat obj tyS)))))))
        ((list (list-rest (vector (struct Abs ((struct Fv (_ ty1)) M))
                                  (struct Abs ((struct Fv (_ ty2)) N))
                                  _)
                          rst)
               (vector tmS tyS))
         (RM (cons (vector M N #t) rst)
             (vector tmS (tymatch ty1 ty2 tyS))))
        ((list (list-rest (vector (struct Comb (M N))
                                  (struct Comb (P Q))
                                  s)
                          rst)
               S)
         (RM (list* (vector M P s)
                    (vector N Q s)
                    rst)
             S))
        ((list (list-rest (vector (struct Bv (i)) (struct Bv (j)) _) rst) S)
         (if (equal? i j)
             (RM rst S)
             (MERR "Bound var. depth")))
        ((list (list-rest (vector (? Clos? pat) ob s) t) S)
         (RM (cons (vector (push_clos pat) ob s) t) S))
        ((list (list-rest (vector pat (? Clos? ob) s) t) S)
         (RM (cons (vector pat (push_clos ob) s) t) S))
        ((list all others)
         (MERR "different constructors")))))
  
  (define raw_match
    (match-lambda*
      ((list tyfixed tmfixed pat ob (vector tmS tyS))
       (RM (list (vector pat ob #f))
           (vector (vector tmS tmfixed)
                   (vector tyS tyfixed))))))
  
  (define norm_subst
    (match-lambda
      ((vector (vector tmS _) (vector tyS _))
       (letrec ((Theta
                 (lambda (t)
                   (inst tyS t)))
                (del
                 (match-lambda*
                   ((list A (list))
                    A)
                   ((list A (list-rest (vector redex residue) rst))
                    (del (let ((redex1
                                (Theta redex)))
                           (if (equal? residue redex1)
                               A
                               (cons (Lib:||-> redex1 residue) A)))
                         rst)))))
         (vector (del () tmS) tyS)))))
  
  (define (match_terml tyfixed tmfixed pat ob)
    (norm_subst (raw_match tyfixed tmfixed pat ob (vector () ()))))
  
  (define match_term
    (match_terml () empty_varset))
  
  (define (prim_mk_eq ty tm1 tm2)
    (make-Comb (make-Comb (inst (list (Lib:||-> Type:alpha ty)) eqc) tm1) tm2))
  
  (define (prim_mk_imp tm1 tm2)
    (make-Comb (make-Comb imp tm1) tm2))
  
  (define dest_eq_ty
    (let ((err (ERR "dest_eq_ty" "")))
      (lambda (t)
        (match (Lib:with_exn (compose (Lib:|##| dest_comb Lib:I) dest_comb) t err)
          ((vector (vector c M) N)
           (if (same_const c eqc)
               (vector M N (Lib:fst (Type:dom_rng (type_of c))))
               (raise err)))))))
  
  (define norm_clos
    (letrec ((subs_comp
              (lambda (t1 t2)
                (Subst:comp mk_clos t1 t2)))
             (vars_sigma_norm
              (match-lambda
                ((vector s t)
                 (match t
                   ((struct Comb (Rator Rand))
                    (make-Comb (vars_sigma_norm (vector s Rator))
                               (vars_sigma_norm (vector s Rand))))
                   ((struct Bv (i))
                    (match (Subst:exp_rel (vector s i))
                      ((vector 0 (struct SOME (v)))
                       (vars_sigma_norm (vector Subst:id v)))
                      ((vector lams (struct SOME (v)))
                       (vars_sigma_norm (vector (Subst:shift (vector lams Subst:id)) v)))
                      ((vector lams 'NONE)
                       (make-Bv lams))))
                   ((struct Abs (Bvar Body))
                    (make-Abs Bvar
                              (vars_sigma_norm (vector (Subst:lift (vector 1 s)) Body))))
                   ((? Fv? _)
                    t)
                   ((struct Clos (Env Body))
                    (vars_sigma_norm (vector (subs_comp (vector s Env)) Body)))
                   (_
                    t))))))
      (lambda (tm)
        (vars_sigma_norm (vector Subst:id tm)))))
  
  (define (trav f t)
    (letrec ((trv
              (match-lambda
                ((? Fv? a)
                 (f a))
                ((? Const? a)
                 (f a))
                ((struct Comb (Rator Rand))
                 (trv Rator)
                 (trv Rand))
                ((struct Abs (Bvar Body))
                 (trv Bvar)
                 (trv Body))
                (_
                 ()))))
      (trv (norm_clos t))))
  
  (define dot ".")
  (define dollar "$")
  (define percent "%")
  
  ;(definde (pp_raw_term index pps tm)
    
  )