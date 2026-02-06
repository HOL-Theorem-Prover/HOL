Theory loadBNFPrelims[bare]
Ancestors
  bnfPrelims
Libs
  bnfBase

Theorem foo = boolTheory.TRUTH

val _ = Lib.assert isSome (bnfBase.pure_lookup (bnfBase.fullDB()) “:'a1 + 'a2”)
