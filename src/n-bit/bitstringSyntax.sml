structure bitstringSyntax :> bitstringSyntax =
struct

open Abbrev HolKernel wordsSyntax bitstringTheory

val ERR = mk_HOL_ERR "bitstringSyntax"

(* ----------------------------------------------------------------------- *)

val s = HolKernel.syntax_fns1 "bitstring"

val (n2v_tm, mk_n2v, dest_n2v, is_n2v) = s "n2v"
val (v2n_tm, mk_v2n, dest_v2n, is_v2n) = s "v2n"
val (s2v_tm, mk_s2v, dest_s2v, is_s2v) = s "s2v"
val (v2s_tm, mk_v2s, dest_v2s, is_v2s) = s "v2s"
val (bnot_tm, mk_bnot, dest_bnot, is_bnot) = s "bnot"
val (w2v_tm, mk_w2v, dest_w2v, is_w2v) = s "w2v"

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val (v2w_tm, mk_v2w, dest_v2w, is_v2w) =
   HolKernel.syntax_fns
   {n = 1,
    dest = fn tm1 => fn e => fn w =>
             (HolKernel.dest_monop tm1 e w, wordsSyntax.dim_of w),
    make = fn tm => fn (v, ty) =>
              Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, v)}
   "bitstring" "v2w"

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val s = HolKernel.syntax_fns2 "bitstring"

val (zero_extend_tm, mk_zero_extend, dest_zero_extend, is_zero_extend) =
  s "zero_extend"

val (sign_extend_tm, mk_sign_extend, dest_sign_extend, is_sign_extend) =
  s "sign_extend"

val (fixwidth_tm, mk_fixwidth, dest_fixwidth, is_fixwidth) = s "fixwidth"
val (bitify_tm, mk_bitify, dest_bitify, is_bitify) = s "bitify"
val (boolify_tm, mk_boolify, dest_boolify, is_boolify) = s "boolify"
val (testbit_tm, mk_testbit, dest_testbit, is_testbit) = s "testbit"
val (shiftl_tm, mk_shiftl, dest_shiftl, is_shiftl) = s "shiftl"
val (shiftr_tm, mk_shiftr, dest_shiftr, is_shiftr) = s "shiftr"
val (rotate_tm, mk_rotate, dest_rotate, is_rotate) = s "rotate"
val (modify_tm, mk_modify, dest_modify, is_modify) = s "modify"
val (add_tm, mk_add, dest_add, is_add) = s "add"
val (bor_tm, mk_bor, dest_bor, is_bor) = s "bor"
val (band_tm, mk_band, dest_band, is_band) = s "band"
val (bxor_tm, mk_bxor, dest_bxor, is_bxor) = s "bxor"
val (replicate_tm, mk_replicate, dest_replicate, is_replicate) = s "replicate"

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val s = HolKernel.syntax_fns3 "bitstring"

val (field_tm, mk_field, dest_field, is_field) = s "field"
val (bitwise_tm, mk_bitwise, dest_bitwise, is_bitwise) = s "bitwise"

(* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . *)

val s = HolKernel.syntax_fns4 "bitstring"

val (field_insert_tm, mk_field_insert, dest_field_insert, is_field_insert) =
   s "field_insert"

(* ----------------------------------------------------------------------- *)

local
   fun bitlist_to_num a l =
      case l of
        [] => a
      | (true::r) => bitlist_to_num (Arbnum.plus1 (Arbnum.times2 a)) r
      | (false::r) => bitlist_to_num (Arbnum.times2 a) r
in
   val bitlist_to_num = bitlist_to_num Arbnum.zero
end

local
   fun bitlist_to_hex a =
      fn [] => a
       | (b1 :: b2 :: b3 :: b4 :: r) =>
           let
              val c = [b1, b2, b3, b4]
           in
              bitlist_to_hex (a ^ Arbnum.toHexString (bitlist_to_num c)) r
           end
       | _ => raise ERR "bitlist_to_hex" "length must be multiple of four"
in
   val bitlist_to_hex = bitlist_to_hex ""
end

fun char_of_bool b = if b then #"1" else #"0"

fun bool_of_term t =
   boolLib.Teq t orelse not (boolLib.Feq t) andalso raise ERR "bool_of_term" ""

val char_of_term = char_of_bool o bool_of_term
val list_of_term = fst o listSyntax.dest_list

val bitlist_of_term = List.map bool_of_term o list_of_term
val binstring_of_term = String.implode o List.map char_of_term o list_of_term
val hexstring_of_term = bitlist_to_hex o bitlist_of_term
val num_of_term = bitlist_to_num o bitlist_of_term
fun mk_fixedwidth (tm, n) = mk_v2w (tm, fcpSyntax.mk_int_numeric_type n)

(* ----------------------------------------------------------------------- *)

val bitstring_ty = listSyntax.mk_list_type Type.bool

fun term_of_bool b = if b then boolSyntax.T else boolSyntax.F

val term_of_char =
   fn #"1" => boolSyntax.T
    | #"T" => boolSyntax.T
    | #"0" => boolSyntax.F
    | #"F" => boolSyntax.F
    | _ => raise ERR "term_of_char" ""

val bitstring_of_bitlist = listSyntax.lift_list bitstring_ty term_of_bool

val bitstring_of_binstring =
   listSyntax.lift_list bitstring_ty term_of_char o String.explode

fun fixedwidth_of_bitlist (l, i) = mk_fixedwidth (bitstring_of_bitlist l, i)
fun fixedwidth_of_binstring (s, i) = mk_fixedwidth (bitstring_of_binstring s, i)
fun bitvector_of_bitlist l = fixedwidth_of_bitlist (l, List.length l)
fun bitvector_of_binstring s = fixedwidth_of_binstring (s, String.size s)

local
   fun boolify a n =
      if n = Arbnum.zero then a
      else let
              val (q, r) = Arbnum.divmod (n, Arbnum.two)
           in
              boolify ((r = Arbnum.one) :: a) q
           end

   val removeWS =
      String.translate (fn c => if Char.isSpace c then "" else String.str c)

   fun hexSize s =
      let
         val n = String.size s * 4
      in
         if String.isPrefix "0x" s then n - 8 else n
      end
in
   fun num_to_bitlist n = if n = Arbnum.zero then [false] else boolify [] n

   val bitstring_of_num = bitstring_of_bitlist o num_to_bitlist
   fun fixedwidth_of_num (i, j) = mk_fixedwidth (bitstring_of_num i, j)
   val bitvector_of_num = bitvector_of_bitlist o num_to_bitlist

   fun bitstring_of_hexstring s =
      let
         val s = removeWS s
         val l = num_to_bitlist (Arbnum.fromHexString s)
         val l = List.tabulate (hexSize s - List.length l, K false) @ l
      in
         bitstring_of_bitlist l
      end

   fun bitvector_of_hexstring s =
      mk_fixedwidth (bitstring_of_hexstring s, hexSize s)

   fun fixedwidth_of_hexstring (s, i) =
      mk_fixedwidth (bitstring_of_hexstring s, i)
end

fun padded_fixedwidth_of_num (m, n) =
   let
      val u = num_to_bitlist m
      val u = String.implode (List.map (fn true => #"1" | false => #"0") u)
      val p = StringCvt.padLeft #"0" n u
   in
      fixedwidth_of_binstring (p, n)
   end

(* ----------------------------------------------------------------------- *)

fun dest_b tm =
   if boolLib.Teq tm
      then true
   else if boolLib.Feq tm
      then false
   else raise ERR "dest_b" ""

fun mk_b b = if b then boolSyntax.T else boolSyntax.F

fun mk_bit n = Term.mk_var ("b" ^ Int.toString n, Type.bool)

(* Make term ``[b(n+w); ... ; b(n)]`` *)
fun mk_bstring w n =
   listSyntax.mk_list
      (List.tabulate (w, fn i => mk_bit (w - i - 1 + n)), Type.bool)

(* Make term ``v2w [b(n+w); ... ; b(n)] : w word`` *)
fun mk_vec w n = mk_v2w (mk_bstring w n, fcpSyntax.mk_int_numeric_type w)

(* Make term ``v2n [b(n+w); ... ; b(n)]`` *)
fun mk_nvec w n = mk_v2n (mk_bstring w n)

(* ----------------------------------------------------------------------- *)

end
