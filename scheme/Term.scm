(module Term mzscheme
  
  (require (prefix Feedback: "Feedback.scm")
           (prefix Lib: "Lib.scm")
           (prefix KernelTypes: "KernelTypes.scm")
           (prefix Type: "Type.scm")
           (prefix Subst: "Subst.scm")
           "Sig.scm"
           "0Records.scm"
           "records.scm")
  
  (require (lib "unit.ss")
           (lib "etc.ss")
           (lib "plt-match.ss"))
  
  (require (prefix HOLset: (planet "set.scm" ("soegaard" "galore.plt" 2 2))))
  
  (provide (all-defined-except
            key
            table_size
            ))
  
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
       (cond ((string=? s1 s2)
              (Type:compare (vector ty1 ty2)))
             ((string>? s1 s2)
              'GREATER)
             (else
              'LESS)))
      (_
       (raise (ERR "var_compare" "variables required")))))
  
  (define empty_varset
    (HOLset:empty var_compare)) ;???
  
  (define (compare p)
    (if (eq? (vector-ref p 0)
             (vector-ref p 1))
        'EQUAL
        (match p
          ((vector (? Clos? t1) t2)
           (compare (vector (push_clos t1) t2)))
          ((vector t1 (? Clos? t2))
           (compare (vector t1 (push_clos t2))))
          ((vector (? Fv? u) (? Fv? v))
           (var_compare p))
          ((vector (? Fv? _) _)
           'LESS)
          ((vector (? Bv? _) (? Fv? _))
           'GREATER)
          ((vector (struct Bv (i)) (struct Bv (j)))
           (cond ((= i j)
                  'EQUAL)
                 ((< i j)
                  'LESS)
                 (else
                  'GREATER)))
          ((vector (? Bv? _) _)
           'LESS)
          ((vector (? Const? _) (? Fv? _))
           'GREATER)
          ((vector (? Const? _) (? Bv? _))
           'GREATER)
          ((vector (struct Const ((vector c1 ty1)))
                   (struct Const ((vector c2 ty2))))
           (match (KernelTypes:compare (vector c1 c2))
             ('EQUAL
               (Type:compare (vector (KernelTypes:to_hol_type ty1)
                                     (KernelTypes:to_hol_type ty2))))
             (x x)))
          ((vector (? Const? _) _)
           'LESS)
          ((vector (struct Comb (M N))
                   (struct Comb (P Q)))
           (match (compare (vector M P))
             ('EQUAL
               (compare N Q))
             (x x)))
          ((vector (? Comb? _) (? Abs? _))
           'LESS)
          ((vector (? Comb? _) _)
           'GREATER)
          ((vector (struct Abs ((struct Fv (_ ty1)) M))
                   (struct Abs ((struct Fv (_ ty2)) N)))
           (match (Type:compare ty1 ty2)
             ('EQUAL
               (compare (vector M N)))
             (x x)))
          ((vector (? Abs? _) _)
           'GREATER))))
  
  (define empty_tmset
    (HOLset:empty compare))
  (define (term_eq t1 t2)
    (eq? (compare (vector t1 t2)) 'EQUAL))
  
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
  )
