(module 0Records mzscheme
  
  (provide (all-defined))
  
  (define-struct Cons (s x))
  (define-struct Shift (k s))
  (define-struct Lift (k s))
  
  (define-struct Tyv (Tyv_string) #f)
  (define-struct Tyapp (tyconst hol_type) #f)
  
  (define-struct GRND (hol_type) #f)
  (define-struct POLY (hol_type) #f)
  
  (define-struct Fv (Fv_string hol_type) #f)
  (define-struct Bv (Bv_int) #f)
  (define-struct Const (tmconst) #f)
  (define-struct Comb (term1 term2) #f)
  (define-struct Abs (term1 term2) #f)
  (define-struct Clos (term_subs term) #f)
  
  (define-struct TAG (string_list string_ref_list) #f)
  (define-struct THM (tag term_set term) #f)
  
  (define-struct TERM (TERM) #f)
  (define-struct THEOREM (thm) #f)
  
  (define-struct INITIAL (entry) #f)
  (define-struct CLOBBER (entry) #f)
  
  )
  