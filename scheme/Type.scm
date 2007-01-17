(module Type mzscheme
  
  (require (prefix Feedback: "Feedback.scm")
           (prefix Lib: "Lib.scm")
           (prefix KernelTypes: "KernelTypes.scm")
           "Sig.scm"
           "0Records.scm"
           "records.scm"
           (prefix Lexis: "Lexis.scm"))
  
  (require (lib "unit.ss")
           (lib "compare.ss" "srfi" "67")
           (lib "plt-match.ss")
           (only (lib "13.ss" "srfi")
                 string-prefix?))
  
  (provide (all-defined-except
            key
            table_size
            equal
            gen_tyvar_prefix
            num2name
            nameStrm))
  
  (define ERR
    (lambda (x y)
      (Feedback:mk_HOL_ERR "Type" x y)))
  
  (define WARN
    (lambda (x y)
      (Feedback:HOL_WARNING "Type" x y)))
  
  (define (key x)
    (vector-ref x 0))
  (define table_size 311)
  
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
   TypeSig
   key
   ERR
   table_size)
  
  (define fun_tyc
    (vector-ref (INITIAL-entry (TypeSig:insert (vector (KernelTypes:mk_id (vector "fun" "min")) 2))) 0))
  (define bool_tyc
    (vector-ref (INITIAL-entry (TypeSig:insert (vector (KernelTypes:mk_id (vector "bool" "min")) 0))) 0))
  (define ind_tyc
    (vector-ref (INITIAL-entry (TypeSig:insert (vector (KernelTypes:mk_id (vector "ind" "min")) 0))) 0))
  
  (define bool
    (make-Tyapp bool_tyc '()))
  (define ind
    (make-Tyapp ind_tyc '()))
  
  (define (--> x y)
    (make-Tyapp fun_tyc (list x y)))
  
  (define dom_rng
    (match-lambda
      ((struct Tyapp (tyc (list x y)))
       (if (equal? fun_tyc fun_tyc)
           (vector x y)
           (raise (ERR "dom_rng" "not a function type"))))
      (_
       (raise (ERR "dom_rng" "not a function type")))))
  
  (define make_type
    (match-lambda*
      ((list tyc Args (vector fnstr name))
       (let ((arity (vector-ref tyc 1)))
         (if (equal? arity
                     (length Args))
             (make-Tyapp tyc Args)
             (raise (ERR fnstr
                         (string-append name
                                        " needs "
                                        (number->string arity)
                                        " arguments, but was given "
                                        (number->string (length Args))))))))))
  
  (define mk_thy_type
    (match-lambda
      ((vector Thy Tyop Args)
       (match (TypeSig:lookup Tyop Thy)
         ((struct SOME ((vector const ...)))
          (make_type const Args
                     (vector "mk_thy_type" (KernelTypes:fullname Tyop Thy))))
         ('NONE
           (raise (ERR "mk_thy_type"
                       (string-append "the type operator "
                                      (Lib:stringquote Tyop)
                                      " has not been declared in theory "
                                      (Lib:stringquote Thy)))))))))
  
  (define (decls a1)
    (map (lambda (e)
           (let* ((temp (vector-ref e 0))
                  (c (vector-ref temp 0)))
             (vector (KernelTypes:name_of c) (KernelTypes:seg_of c))))
         (TypeSig:resolve a1)))
  
  (define (first_decl fname Tyop)
    (match (TypeSig:resolve Tyop)
      ((list)
       (raise (ERR fname
                   (string-append (Lib:stringquote Tyop)
                                  " has not been declared"))))
      ((list (vector const ...))
       const)
      ((list (vector const ...) ...)
       (WARN fname "more than one possibility")
       const)))
  
  (define (mk_type Tyop Args)
    (make_type (first_decl "mk_type" Tyop) Args (vector "mk_type" Tyop)))
  
  ;currently unused
  ;(define (current_tyops s)
  
  (define break_type
    (match-lambda
      ((struct Tyapp (p q)) ;non _ in ML
       (vector p q))
      (_
       (raise (ERR "break_type" "")))))
  
  (define dest_thy_type
    (match-lambda*
      ((list (struct Tyapp ((vector tyc _) A)))
       (vector (KernelTypes:seg_of tyc) (KernelTypes:name_of tyc) A))
      (_
       (raise (ERR "dest_thy_type" "")))))
  
  (define dest_type
    (match-lambda*
      ((list (struct Tyapp ((vector tyc _) A)))
       (vector (KernelTypes:name_of tyc) A))
      (_
       (raise (ERR "dest_type" "")))))
  
  (define op_arity
    (match-lambda
      ((vector Thy Tyop)
       (match (TypeSig:lookup (vector Thy Tyop))
         ((struct SOME ((vector (vector id a) ...)))
          (make-SOME a))
         ('NONE
           'NONE)))))
  
  (define thy_types
    (let ((xlate
           (match-lambda
             ((vector (vector id arity) witness utd)
              (vector (KernelTypes:name_of id) arity)))))
      (lambda (s)
        (map xlate (TypeSig:slice s)))))
  
  (define alpha (make-Tyv "'a"))
  (define beta (make-Tyv "'b"))
  (define gamma (make-Tyv "'c"))
  (define delta (make-Tyv "'d"))
  (define etyvar (make-Tyv "'e"))
  (define ftyvar (make-Tyv "'f"))
  
  (define mk_vartype
    (match-lambda
      ("'a" alpha)
      ("'b" beta)
      ("'c" gamma)
      ("'d" delta)
      ("'e" etyvar)
      ("'f" ftyvar)
      (s
       (unless (Lexis:allowed_user_type_var s)
         (WARN "mk_vartype" "non-standard syntax"))
       (make-Tyv s))))
  
  (define dest_vartype
    (match-lambda
      ((struct Tyv (s))
       s)
      (_
       (raise (ERR "dest_vartype" "not a type variable")))))
  
  (define is_vartype Tyv?)
  
  (define (is_type x)
    (not (is_vartype x)))
  
  (define-values (type_vars type_varsl)
    (letrec ((tyvars
              (match-lambda*
                ((list (struct Tyapp (_ Args)) vlist)
                 (tyvarsl Args vlist))
                ((list v vlist)
                 (Lib:insert v vlist))))
             (tyvarsl
              (lambda (L vlist)
                (Lib:rev_itlist tyvars L vlist))))
      (values (lambda (ty) (reverse (tyvars ty ())))
              (lambda (L) (reverse (tyvarsl L ()))))))
  
  (define (exists_tyvar P w)
    (define occ
      (match-lambda
        ((? Tyv? w)
         (P w))
        ((struct Tyapp (_ Args))
         (Lib:exists occ Args))))
    (occ w))
  
  (define (equal v)
    (equal? (vector-ref v 0)
            (vector-ref v 1)))
  
  (define (type_var_in v)
    (if (is_vartype v)
        (exists_tyvar equal v)
        (raise (ERR "type_var_occurs" "not a type variable"))))
  
  (define ty_sub
    (match-lambda*
      ((list (list) _)
       'SAME)
      ((list theta (struct Tyapp (tyc Args)))
       (match (Lib:delta_map (ty_sub theta) Args)
         ('SAME
           'SAME)
         ((struct Lib:DIFF (Args1))
          (Lib:make-DIFF (make-Tyapp tyc Args1)))))
      ((list theta v)
       (match (Lib:subst_assoc (equal v) theta)
         ('NONE 'SAME)
         ((struct SOME (ty))
          (Lib:make-DIFF ty))))))
  
  (define (type_subst theta)
    (Lib:delta_apply (ty_sub theta)))
  
  (define polymorphic
    (match-lambda
      ((struct Tyv (_))
       #t)
      ((struct Tyapp (_ Args))
       (Lib:exists polymorphic Args))))
  
  (define tymatch
    (letrec ((MERR
              (lambda (s)
                (raise (ERR "raw_match_type" s))))
             (lookup
              (match-lambda*
                ((list x ids (list))
                 (if (Lib:mem x ids)
                     (make-SOME x)
                     'NONE))
                ((list x ids (list-rest (vector redex residue) t))
                 (if (equal? x redex)
                     (make-SOME residue)
                     (lookup x ids t))))))
      (match-lambda*
        ((list (list) (list) Sids)
         Sids)
        ((list (list-rest (? Tyv? v) ps)
               (list-rest ty obs)
               (vector S ids))
         (tymatch ps obs
                  (match (lookup v ids S)
                    ('NONE
                      (if (equal? v ty)
                          (vector S (cons v ids))
                          (vector (cons (Lib:||-> v ty) S) ids)))
                    ((struct SOME (ty1))
                     (if (equal? ty1 ty)
                         (vector S ids)
                         (MERR "double bind"))))))
        ((list (list-rest (struct Tyapp (c1 A1)) ps)
               (list-rest (struct Tyapp (c2 A2)) obs)
               Sids)
         (if (equal? c1 c2)
             (tymatch (append A1 ps) (append A2 obs) Sids)
             (MERR "different tyops")))
        ((list any other thing)
         (MERR "different constructors")))))
  
  (define (raw_match_type pat ob Sids)
    (tymatch (list pat) (list ob) Sids))
  
  (define (match_type_restr fixed pat ob)
    (Lib:fst (raw_match_type pat ob (vector () fixed))))
  
  (define (match_type_in_context pat ob S)
    (Lib:fst (raw_match_type pat ob (vector S ()))))
  
  (define (match_type pat ob)
    (match_type_in_context pat ob ()))
  
  (define compare
    (match-lambda*
      ((list (struct Tyv (s1))
             (struct Tyv (s2)))
       (string-compare s1 s2))
      ((list (struct Tyv (s1)) _)
       -1)
      ((list (struct Tyapp (_ _))
             (struct Tyv (_)))
       1)
      ((list (struct Tyapp ((vector c1 _) A1))
             (struct Tyapp ((vector c2 _) A2)))
       (match (KernelTypes:compare (vector c1 c2))
         (0 (Lib:list_compare compare (vector A1 A2)))
         (x x)))))
  
  
  (define gen_tyvar_prefix "%%gen_tyvar%%")
  (define (num2name i)
    (string-append gen_tyvar_prefix
                   (number->string i)))
  (define nameStrm
    (Lib:mk_istream add1 0 num2name))
  
  (define (gen_tyvar)
    (make-Tyv (Lib:state (Lib:next nameStrm))))
  (define is_gen_tyvar
    (match-lambda
      ((struct Tyv (name))
       (string-prefix? gen_tyvar_prefix name))
      (_
       #f)))
  
  )