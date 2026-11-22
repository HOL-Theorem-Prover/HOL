Theory cvftbrokenuse
Ancestors
  cvftleft cvftbroken
Libs
  cv_transLib

(* Premises are not proved when translations are compared, so
   cvftbroken's translation of colour still differs from cvftleft's, and
   using colour is an error *)

val _ = assert (fn ty => (cv_typeLib.from_term_for ty; false)
                         handle HOL_ERR e =>
                           String.isSubstring "cv_from_to_delete"
                                              (Feedback.message_of e))
               “:colour”
