open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
val refused =
  ((Refute.export_registrations [Parse.Type [QUOTE ":persist_old"]]; false)
   handle HOL_ERR e =>
     String.isSubstring "refutePersistBadVersion" (Feedback.message_of e)
     andalso String.isSubstring "unsupported format version 2"
       (Feedback.message_of e))
val _ = tprint "unsupported imported formats remain unusable"
val _ = if refused then OK () else die "unsupported version was hidden"
