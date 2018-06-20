structure fp16Syntax :> fpSyntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp16"
             val ty = wordsSyntax.mk_int_word_type 16)
