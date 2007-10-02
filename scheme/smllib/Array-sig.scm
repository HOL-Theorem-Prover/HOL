(module Array-sig (lib "mlsig.scm" "lang")
  (provide Array^)
  (define-signature Array^
    (maxLen
     array
     fromList
     tabulate
     length
     sub
     update
     extract
     copy
     copyVec
     appi
     app
     foldli
     foldri
     foldl
     foldr
     modifyi
     modify
     )
    )
  )