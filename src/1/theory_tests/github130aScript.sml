Theory github130a[bare]
Libs
  HolKernel Parse boolLib github130Lib

Definition foo_def[nocompute]: foo f x = f x
End
val _ = export_gh130 "foo_def"
val _ = Feedback.WARNINGs_as_ERRs := false
val _ = delete_const "foo"


