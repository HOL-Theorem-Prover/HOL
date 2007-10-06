(module Strbase-sig (lib "mlsig.scm" "lang")
  (provide Strbase^)
  (require)
  (define-signature
   Strbase^
   (maxlen
     dropl
     dropr
     takel
     taker
     splitl
     splitr
     translate
     tokens
     fields
     foldl
     fromMLescape
     toMLescape
     fromCescape
     toCescape
     fromCString)))
