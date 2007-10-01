(module mlsig (lib "plt-mzscheme.ss" "lang")
  
  (require (lib "plt-match.ss")
           (lib "unit.ss")
           (only (lib "list.ss") foldl foldr)
           (only (lib "etc.ss") compose)
           (only (lib "13.ss" "srfi") string-concatenate))
  
  (provide struct
           define-signature
           define-structure
           (rename define-values/invoke-unit/infer ml-open)
           ml-dot
           (all-from (lib "plt-match.ss"))
           (all-from (lib "plt-mzscheme.ss" "lang"));to do remove something in Scheme but not in SML
           string-concatenate
           foldl foldr
           char->string
           !=
           compose
           )
  
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
  
  (define (!= a b)
    (not (eqv? a b)))
  
  (define (char->string c)
    (list->string (list c)))
  )