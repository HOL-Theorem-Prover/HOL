open HolKernel Parse testutils
val _ = Thm.setCT "scratch"
val rejected_conflict =
  ((Refute.export_registrations [Parse.Type [QUOTE ":persist_old"]]; false)
   handle HOL_ERR e =>
     String.isSubstring "refutePersistWrapper" (Feedback.message_of e)
     andalso String.isSubstring "persist_old" (Feedback.message_of e)
     andalso String.isSubstring "incompatible" (Feedback.message_of e))
val _ = tprint "import conflicts with an incompatible explicit registration"
val _ = if rejected_conflict then OK () else die "conflict was hidden"
