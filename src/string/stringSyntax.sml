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

val mk_chr = curry mk_comb chr_tm
val mk_ord = curry mk_comb ord_tm

val dest_chr = dest_monop ("CHR","string") (ERR "dest_chr" "")
val dest_ord = dest_monop ("ORD","string") (ERR "dest_ord" "")

val is_chr = Lib.can dest_chr 
val is_ord = Lib.can dest_ord

fun fromMLchar ch  = mk_chr (mk_numeral (Arbnum.fromInt (Char.ord ch)))
fun fromHOLchar ch = Char.chr (Arbnum.toInt(dest_numeral (dest_chr ch)))


(*---------------------------------------------------------------------------
        Strings
 ---------------------------------------------------------------------------*)

val string_ty = mk_thy_type {Tyop="string", Thy="string", Args=[]}

val implode_tm     = prim_mk_const{Name="IMPLODE",    Thy="string"}
val explode_tm     = prim_mk_const{Name="EXPLODE",    Thy="string"}
val emptystring_tm = prim_mk_const{Name="EMPTYSTRING",Thy="string"}
val string_tm      = prim_mk_const{Name="STRING",     Thy="string"}

fun mk_string (c,s) = list_mk_comb(string_tm,[c,s])
val mk_implode = curry mk_comb implode_tm
val mk_explode = curry mk_comb explode_tm

val dest_string  = dest_binop ("STRING","string")  (ERR "dest_string" "")
val dest_implode = dest_monop ("IMPLODE","string") (ERR "dest_implode" "")
val dest_explode = dest_monop ("EXPLODE","string") (ERR "dest_explode" "")

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
