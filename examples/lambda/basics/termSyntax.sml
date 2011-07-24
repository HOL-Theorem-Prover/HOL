structure termSyntax :> termSyntax =
struct

open HolKernel Abbrev termTheory

fun ERR f msg = mk_HOL_ERR "termSyntax" f msg

val string_ty = stringSyntax.string_ty
val term_ty = mk_thy_type {Tyop = "term", Thy = "term", Args = []}

val VAR_t = mk_thy_const{Name = "VAR", Thy = "term", Ty = string_ty --> term_ty}
val APP_t = mk_thy_const{Name = "APP", Thy = "term",
                         Ty = term_ty --> term_ty --> term_ty}
val LAM_t = mk_thy_const{Name = "LAM", Thy = "term",
                         Ty = string_ty --> term_ty --> term_ty}
val SUB_t = mk_thy_const{Name = "SUB", Thy = "term",
                         Ty = term_ty --> string_ty --> term_ty --> term_ty}

fun mk_VAR t = mk_comb(VAR_t, t)
fun mk_APP (t1,t2) = list_mk_comb(APP_t, [t1,t2])
fun mk_LAM (t1,t2) = list_mk_comb(LAM_t, [t1,t2])
fun mk_SUB (t1,t2,t3) = list_mk_comb(SUB_t, [t1,t2,t3])

fun dest2 f nm t = let
  val (f', args) = strip_comb t
in
  if length args = 2 andalso aconv f f' then (hd args, hd (tl args))
  else raise ERR ("dest_"^nm) ("Term is not "^nm)
end

val dest_LAM = dest2 LAM_t "LAM"
val dest_APP = dest2 APP_t "APP"
val is_LAM = can dest_LAM
val is_APP = can dest_APP

fun dest_VAR t = let
  val (f,x) = dest_comb t
in
  if aconv f VAR_t then x
  else raise ERR "dest_VAR" "Term is not VAR"
end handle HOL_ERR _ => raise ERR "dest_VAR" "Term is not VAR"
val is_VAR = can dest_VAR

fun dest_SUB t = let
  val (f, args) = strip_comb t
in
  if aconv f SUB_t andalso length args = 3 then (hd args,
                                                 hd (tl args),
                                                 hd (tl (tl args)))
  else raise ERR "dest_SUB" "Term is not SUB"
end
val is_SUB = can dest_SUB

end (* struct *)
