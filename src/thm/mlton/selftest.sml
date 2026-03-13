val ty = Type.mk_vartype "'a"
val tm = Term.mk_var ("x", ty)
val th = Thm.REFL tm
val () = print "OK: kernel built and REFL proved with MLton.\n"
