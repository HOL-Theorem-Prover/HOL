(module ml mzscheme
  
  (require (all-except "mlsig.scm" struct))
  
  (provide struct
           (all-from "mlsig.scm"))
  
  (define-syntax (struct stx)
    (syntax-case stx ()
      ((_ name (c ...))
       #`(#,(cadr (syntax-local-value (syntax name))) c ...))))
  )


