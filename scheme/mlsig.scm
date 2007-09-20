(module mlsig (lib "plt-mzscheme.ss" "lang")
  
  (require (lib "plt-match.ss")
           (lib "unit.ss"))
  
  (provide define-signature
           define-structure
           (rename define-values/invoke-unit/infer ml-open)
           ml-dot
           (all-from (lib "plt-match.ss"))
           (all-from (lib "plt-mzscheme.ss" "lang")))
  
  (define-syntax define-structure
    (syntax-rules ()
      ((_ name sig body ...)
       (define-unit-binding name
         (invoke-unit
          (unit
            (import)
            (export)
            body ...
            (unit-from-context sig)))
         (import)
         (export sig)))))
  
  (define-syntax ml-dot
    (syntax-rules ()
      ((_ str id)
       (let () (define-values/invoke-unit/infer str) id))))
  
  )