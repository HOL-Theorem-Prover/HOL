open HolKernel optionSyntax testutils

val alpha_option_ty = mk_option alpha
val alphanone_t = mk_thy_const{Thy = "option", Name = "NONE", Ty = alpha_option_ty}

val _ = tprint "dest_none returns unwrapped type"
val ty = dest_none alphanone_t
val _ = if Type.compare(ty, alpha) = EQUAL then print "OK\n"
        else die "FAILED!"
