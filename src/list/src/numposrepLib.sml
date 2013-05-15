structure numposrepLib :> numposrepLib =
struct

open HolKernel Parse boolLib computeLib;
open bitLib numposrepTheory

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars numposrepTheory.numposrep_grammars
end
open Parse

(* ------------------------------------------------------------------------- *)

local
   val thm = Thm.CONJUNCT2 l2n_pow2_compute
   val rule = simpLib.SIMP_RULE numLib.std_ss []
   val f = numSyntax.mk_numeral o Arbnum.log2 o Arbnum.fromInt
   fun l2n_pow2 i = rule (Thm.SPEC (f i) thm)
   fun n2l_pow2 i = rule (Thm.SPEC (f i) n2l_pow2_compute)
   val sizes = [2, 8, 16, 256]
   val thms =
      [numLib.SUC_RULE BOOLIFY_def, l2n_def, n2l_def, l2n_2_thms,
       num_from_bin_list_def, num_from_oct_list_def, num_from_dec_list_def,
       num_from_hex_list_def,
       num_to_bin_list_def, num_to_oct_list_def, num_to_dec_list_def,
       num_to_hex_list_def] @
      List.map l2n_pow2 (tl sizes) @ List.map n2l_pow2 sizes
in
   fun add_numposrep_compset cmp = computeLib.add_thms thms cmp
end

val () = add_numposrep_compset computeLib.the_compset

(* ------------------------------------------------------------------------- *)

(* Testing...

open numposrepLib

val tst = Count.apply EVAL

tst ``BOOLIFY 11 123 [T]``;
tst ``l2n 2 []``;
tst ``l2n 2 [1;0;1;1;1;1;0;0;0;1;1]``;
tst ``l2n 3 [2;1;0;1;2]``;
tst ``n2l 3 194``;
tst ``num_from_bin_list [1;0;1;1;0]``;
tst ``num_from_oct_list [7;2;1;4;0]``;
tst ``num_from_dec_list [7;2;1;4;9]``;
tst ``num_from_hex_list [11;2;1;15;9]``;
tst ``num_to_bin_list 0b110111``;
tst ``num_to_oct_list 123``;
tst ``num_to_dec_list 23768``;
tst ``num_to_hex_list 0xAAFF11``;

*)

end
