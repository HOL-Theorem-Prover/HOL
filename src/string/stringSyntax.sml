structure stringSyntax :> stringSyntax =
struct

open HolKernel boolLib stringTheory numSyntax;

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

val string_ty = mk_thy_type {Tyop="string", Thy="string", Args=[]}

val implode_tm     = prim_mk_const{Name="IMPLODE",     Thy="string"}
val explode_tm     = prim_mk_const{Name="EXPLODE",     Thy="string"}
val emptystring_tm = prim_mk_const{Name="EMPTYSTRING", Thy="string"}
val string_tm      = prim_mk_const{Name="STRING",      Thy="string"}

fun mk_string (c,s) = 
  with_exn list_mk_comb (string_tm,[c,s]) (ERR "mk_string" "")

val mk_implode = C (with_exn (curry mk_comb implode_tm)) (ERR "mk_implode" "")
val mk_explode = C (with_exn (curry mk_comb explode_tm)) (ERR "mk_explode" "")

val dest_string  = dest_binop string_tm  (ERR "dest_string" "")
val dest_implode = dest_monop implode_tm (ERR "dest_implode" "")
val dest_explode = dest_monop explode_tm (ERR "dest_explode" "")

val is_string  = can dest_string
val is_implode = can dest_implode
val is_explode = can dest_explode;
val is_emptystring = equal emptystring_tm

val fromMLstring = 
   Literal.mk_string_lit
        {mk_string=mk_string,
         fromMLchar=fromMLchar,
         emptystring=emptystring_tm}

val fromHOLstring = Literal.dest_string_lit

end
