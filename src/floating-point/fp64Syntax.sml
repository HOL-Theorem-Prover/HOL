structure fp64Syntax :> fpSyntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp64"
             val ty = wordsSyntax.mk_int_word_type 64)
