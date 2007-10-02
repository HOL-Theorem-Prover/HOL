(module mlsig (lib "plt-mzscheme.ss" "lang")
  
  (require (lib "plt-match.ss")
           (lib "unit.ss")
           (only (lib "list.ss") foldl foldr)
           (only (lib "etc.ss") compose)
           (only (lib "13.ss" "srfi") string-concatenate))
  
  (provide (all-defined)
           struct
           define-signature
           (rename define-values/invoke-unit/infer ml-open)
           (all-from (lib "plt-match.ss"))
           (all-from (lib "plt-mzscheme.ss" "lang"));to do remove something in Scheme but not in SML
           string-concatenate
           foldl foldr
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
  
    (define-struct NONE ())
  (define-struct SOME (content))
  (define-struct LESS ())
  (define-struct EQUAL ())
  (define-struct GREATER ())
  (define-struct QUOTE ());?
  (define-struct ANTIQUOTE ());?
  (define-struct Out_of_memory ())
  (define-struct Invalid_argument ())
  (define-struct Graphic ())
  (define-struct Interrupt ())
  (define-struct Overflow ())
  (define-struct Fail ())
  (define-struct Ord ())
  (define-struct Match ());?
  (define-struct Bind ())
  (define-struct Size ())
  (define-struct Div ())
  (define-struct SysErr ())
  (define-struct Subscript ())
  (define-struct Chr ())
  (define-struct Io ())
  (define-struct Domain ())
  )