structure stringSyntax :> stringSyntax =
struct

open HolKernel boolLib stringTheory numSyntax;   infix |->;

val ERR = mk_HOL_ERR "stringSyntax";

(*---------------------------------------------------------------------------
        Characters
 ---------------------------------------------------------------------------*)

val char_ty = mk_thy_type  {Tyop="char", Thy="string",Args=[]}

val chr_tm  = prim_mk_const{Name="CHR", Thy="string"}
val ord_tm  = prim_mk_const{Name="ORD", Thy="string"}

val mk_chr = C (with_exn (curry mk_comb chr_tm)) (ERR "mk_chr" "")
val mk_ord = C (with_exn (curry mk_comb ord_tm)) (ERR "mk_ord" "")

val dest_chr = dest_monop chr_tm (ERR "dest_chr" "")
val dest_ord = dest_monop ord_tm (ERR "dest_ord" "")

val is_chr = Lib.can dest_chr
val is_ord = Lib.can dest_ord

val fromMLchar =
 C (with_exn (mk_chr o mk_numeral o Arbnum.fromInt o Char.ord))
   (ERR "fromMLchar" "")

val fromHOLchar =
 C (with_exn (Char.chr o Arbnum.toInt o dest_numeral o dest_chr))
   (ERR "fromHOLchar" "");


(*---------------------------------------------------------------------------
        Strings
 ---------------------------------------------------------------------------*)

val stri = inst [alpha |-> char_ty]

val string_ty = mk_thy_type {Tyop="list", Thy="list", Args=[char_ty]}

val implode_tm     = prim_mk_const{Name="IMPLODE",     Thy="string"}
val explode_tm     = prim_mk_const{Name="EXPLODE",     Thy="string"}
val emptystring_tm = mk_thy_const{Name="NIL", Thy="list", Ty = string_ty}
val string_tm      = mk_thy_const{Name="CONS", Thy="list",
                                  Ty = char_ty --> string_ty --> string_ty}
val string_case_tm = inst [beta |-> alpha]
                          (stri (prim_mk_const{Name="list_case", Thy="list"}))
val strlen_tm      = stri (prim_mk_const{Name="LENGTH",    Thy="list"})
val strcat_tm      = stri (prim_mk_const{Name="APPEND",    Thy="list"})
val isprefix_tm    = stri (prim_mk_const{Name="isPREFIX",  Thy="list"});

val mk_implode = C (with_exn (curry mk_comb implode_tm)) (ERR "mk_implode" "")
val mk_explode = C (with_exn (curry mk_comb explode_tm)) (ERR "mk_explode" "")
fun mk_string (c,s) =
  with_exn list_mk_comb (string_tm,[c,s]) (ERR "mk_string" "")
fun mk_string_case (e,f,s) =
  with_exn list_mk_comb (inst [alpha |-> type_of e]string_case_tm, [e,f,s])
           (ERR "mk_string_case" "")
val mk_strlen = C (with_exn (curry mk_comb strlen_tm)) (ERR "mk_strlen" "")
fun mk_strcat (s1,s2) =
  with_exn list_mk_comb (strcat_tm,[s1,s2]) (ERR "mk_strcat" "")
fun mk_isprefix (s1,s2) =
  with_exn list_mk_comb (isprefix_tm,[s1,s2]) (ERR "mk_isprefix" "")

val dest_implode     = dest_monop implode_tm     (ERR "dest_implode"  "")
val dest_explode     = dest_monop explode_tm     (ERR "dest_explode"  "")
val dest_string      = dest_binop string_tm      (ERR "dest_string"   "")
val dest_strlen      = dest_monop strlen_tm      (ERR "dest_strlen"   "")
val dest_strcat      = dest_binop strcat_tm      (ERR "dest_strcat"   "")
val dest_isprefix    = dest_binop isprefix_tm    (ERR "dest_isprefix" "")
val dest_string_case = dest_triop string_case_tm (ERR "dest_string_case" "")

val is_implode     = can dest_implode
val is_explode     = can dest_explode;
val is_emptystring = equal emptystring_tm
val is_string      = can dest_string
val is_string_case = can dest_string_case
val is_strlen      = can dest_strlen
val is_strcat      = can dest_strcat
val is_isprefix    = can dest_isprefix

val fromMLstring =
   Literal.mk_string_lit
        {mk_string=mk_string,
         fromMLchar=fromMLchar,
         emptystring=emptystring_tm}

val fromHOLstring = Literal.dest_string_lit
val is_string_literal = Literal.is_string_lit
val is_char_literal = Literal.is_char_lit

(*---------------------------------------------------------------------------*)
(* For support of ML execution                                               *)
(*---------------------------------------------------------------------------*)

fun lift_char ty c = fromMLchar c
fun lift_string ty s = fromMLstring s;

end
