Theory SGAUnicodeMergeA2[bare]
Libs
  HolKernel Parse boolLib

Definition INTER_def[nocompute]:
  INTER P Q x <=> P x /\ Q x
End

val _ = Unicode.unicode_version { u = "∩", tmnm = "INTER"};

Definition FUNION_def[nocompute]:
  FUNION f1 f2 x <=> f1 x \/ f2 x
End

val funion_symbol = UTF8.chr 0x228C
val _ = set_fixity funion_symbol (Infixl 500)
val _ = overload_on (funion_symbol, ``FUNION``)

