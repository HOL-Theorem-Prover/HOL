Theory loadBNFPrelims[bare]
Ancestors
  bnfPrelims
Libs
  HolKernel bnfBase

Theorem foo = boolTheory.TRUTH

val db = bnfBase.fullDB()
val _ = app (fn knm => ignore $ Lib.assert isSome $ bnfBase.pure_lookup db knm)
  [{Name = "sum", Thy = "sum"},
   {Name = "prod", Thy = "pair"},
   {Name = "fun", Thy = "min"},
   {Name = "option", Thy = "option"}
  ]
