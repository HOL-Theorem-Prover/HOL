structure stringSyntax :> stringSyntax =
struct

open HolKernel boolLib stringTheory numSyntax;

infix |->;

val ERR = Feedback.mk_HOL_ERR "stringSyntax";

(*---------------------------------------------------------------------------
        Characters and Strings
 ---------------------------------------------------------------------------*)

val char_ty = Type.mk_thy_type {Tyop = "char", Thy = "string", Args = []}
val string_ty = Type.mk_thy_type {Tyop = "list", Thy = "list", Args = [char_ty]}

val monop =
   HolKernel.syntax_fns "string" 1 HolKernel.dest_monop (Lib.curry Term.mk_comb)

val binop =
   HolKernel.syntax_fns "string" 2 HolKernel.dest_binop HolKernel.mk_binop

val (chr_tm,mk_chr,dest_chr,is_chr) = monop "CHR"
val (ord_tm,mk_ord,dest_ord,is_ord) = monop "ORD"
val (tochar_tm,mk_tochar,dest_tochar,is_tochar) = monop "TOCHAR"
val (implode_tm,mk_implode,dest_implode,is_implode) = monop "IMPLODE"
val (explode_tm,mk_explode,dest_explode,is_explode) = monop "EXPLODE"
val (islower_tm,mk_islower,dest_islower,is_islower) = monop "isLower"
val (isupper_tm,mk_isupper,dest_isupper,is_isupper) = monop "isUpper"
val (isdigit_tm,mk_isdigit,dest_isdigit,is_isdigit) = monop "isDigit"
val (isalpha_tm,mk_isalpha,dest_isalpha,is_isalpha) = monop "isAlpha"
val (isprint_tm,mk_isprint,dest_isprint,is_isprint) = monop "isPrint"
val (isspace_tm,mk_isspace,dest_isspace,is_isspace) = monop "isSpace"
val (isgraph_tm,mk_isgraph,dest_isgraph,is_isgraph) = monop "isGraph"
val (ispunct_tm,mk_ispunct,dest_ispunct,is_ispunct) = monop "isPunct"
val (isascii_tm,mk_isascii,dest_isascii,is_isascii) = monop "isAscii"
val (iscntrl_tm,mk_iscntrl,dest_iscntrl,is_iscntrl) = monop "isCntrl"
val (ishexdigit_tm,mk_ishexdigit,dest_ishexdigit,is_ishexdigit) =
   monop "isHexDigit"
val (isalphanum_tm,mk_isalphanum,dest_isalphanum,is_isalphanum) =
   monop "isAlphaNum"
val (tolower_tm,mk_tolower,dest_tolower,is_tolower) = monop "toLower"
val (toupper_tm,mk_toupper,dest_toupper,is_toupper) = monop "toUpper"
val (sub_tm,mk_sub,dest_sub,is_sub) = monop "SUB"
val (str_tm,mk_str,dest_str,is_str) = monop "STR"
val (substring_tm,mk_substring,dest_substring,is_substring) = monop "SUBSTRING"
val (extract_tm,mk_extract,dest_extract,is_extract) = monop "EXTRACT"
val (dest_string_tm,mk_dest_string,dest_dest_string,is_dest_string) =
   monop "DEST_STRING"

val (char_lt_tm,mk_char_lt,dest_char_lt,is_char_lt) = binop "char_lt"
val (char_gt_tm,mk_char_gt,dest_char_gt,is_char_gt) = binop "char_gt"
val (char_le_tm,mk_char_le,dest_char_le,is_char_le) = binop "char_le"
val (char_ge_tm,mk_char_ge,dest_char_ge,is_char_ge) = binop "char_ge"
val (string_lt_tm,mk_string_lt,dest_string_lt,is_string_lt) = binop "string_lt"
val (string_gt_tm,mk_string_gt,dest_string_gt,is_string_gt) = binop "string_gt"
val (string_le_tm,mk_string_le,dest_string_le,is_string_le) = binop "string_le"
val (string_ge_tm,mk_string_ge,dest_string_ge,is_string_ge) = binop "string_ge"
val (fields_tm,mk_fields,dest_fields,is_fields) = binop "FIELDS"
val (tokens_tm,mk_tokens,dest_tokens,is_tokens) = binop "TOKENS"
val (translate_tm,mk_translate,dest_translate,is_translate) = binop "TRANSLATE"

val fromMLchar =
 C (with_exn (mk_chr o mk_numeral o Arbnum.fromInt o Char.ord))
   (ERR "fromMLchar" "")

val fromHOLchar =
 C (with_exn (Char.chr o Arbnum.toInt o dest_numeral o dest_chr))
   (ERR "fromHOLchar" "");

(*---------------------------------------------------------------------------
        Strings as lists
 ---------------------------------------------------------------------------*)

val stri = inst [alpha |-> char_ty]

val emptystring_tm = mk_thy_const{Name="NIL", Thy="list", Ty = string_ty}
val string_tm      = mk_thy_const{Name="CONS", Thy="list",
                                  Ty = char_ty --> string_ty --> string_ty}
val string_case_tm = inst [beta |-> alpha] (stri listSyntax.list_case_tm)
val strlen_tm      = stri (prim_mk_const{Name="LENGTH",    Thy="list"})
val strcat_tm      = stri (prim_mk_const{Name="APPEND",    Thy="list"})
val isprefix_tm    = stri (prim_mk_const{Name="isPREFIX",  Thy="list"});


val mk_implode = C (with_exn (curry mk_comb implode_tm)) (ERR "mk_implode" "")
val mk_explode = C (with_exn (curry mk_comb explode_tm)) (ERR "mk_explode" "")
fun mk_string (c,s) =
  with_exn list_mk_comb (string_tm,[c,s]) (ERR "mk_string" "")
fun mk_string_case (e,f,s) =
  with_exn list_mk_comb (inst [alpha |-> type_of e]string_case_tm, [s,e,f])
           (ERR "mk_string_case" "")
val mk_strlen = C (with_exn (curry mk_comb strlen_tm)) (ERR "mk_strlen" "")
fun mk_strcat (s1,s2) =
  with_exn list_mk_comb (strcat_tm,[s1,s2]) (ERR "mk_strcat" "")
fun mk_isprefix (s1,s2) =
  with_exn list_mk_comb (isprefix_tm,[s1,s2]) (ERR "mk_isprefix" "")

val dest_string      = dest_binop string_tm      (ERR "dest_string"   "")
val dest_strlen      = dest_monop strlen_tm      (ERR "dest_strlen"   "")
val dest_strcat      = dest_binop strcat_tm      (ERR "dest_strcat"   "")
val dest_isprefix    = dest_binop isprefix_tm    (ERR "dest_isprefix" "")
fun dest_string_case t = let
  val (s,e,f) = dest_triop string_case_tm (ERR "dest_string_case" "") t
in
  (e,f,s)
end

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
