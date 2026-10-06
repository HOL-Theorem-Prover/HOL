open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
val refused =
  ((Refute.export_registrations [Parse.Type [QUOTE ":persist_cross"]]; false)
   handle HOL_ERR e =>
     String.isSubstring "exporting theory" (Feedback.message_of e) andalso
     String.isSubstring "persist_cross" (Feedback.message_of e) andalso
     String.isSubstring "incompatible" (Feedback.message_of e))
val _ = tprint "cross-kind sibling history cannot be hidden by replacement"
val _ = if refused then OK () else die "cross-kind history was lost"
