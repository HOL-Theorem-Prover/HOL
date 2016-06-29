structure fp32Syntax :> fpSyntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp32"
             val ty = wordsSyntax.mk_int_word_type 32)
