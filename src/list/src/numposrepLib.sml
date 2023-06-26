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
   val srule = simpLib.SIMP_RULE numLib.std_ss
   val rule = srule []
   val rule0 = srule [bitTheory.DIVMOD_2EXP_def, boolTheory.LET_THM]
   val n_tm =
     Term.mk_comb (numSyntax.numeral_tm, Term.mk_var ("n", numSyntax.num))
   fun zero_num_rule th =
     CONJ (rule0 (Q.SPEC `0n` th)) (rule (Thm.SPEC n_tm th))
   fun log_spec (th1, th2) i =
     let
       val a = Arbnum.fromInt i
       val lga = Arbnum.log2 a
     in
       if Arbnum.pow (Arbnum.two, lga) = a then
         Thm.SPEC (numSyntax.mk_numeral lga) th1
       else
         Thm.SPEC (numSyntax.mk_numeral a) th2
     end
   val l2n_rule =
     rule o log_spec (Thm.CONJUNCT2 l2n_pow2_compute, Thm.CONJUNCT2 l2n_def)
   val n2l_rule =
     zero_num_rule o
     log_spec (n2l_pow2_compute, Conv.CONV_RULE Conv.SWAP_FORALL_CONV n2l_def)
   val sizes = [2, 8, 10, 16, 256]
   val thms =
      [numLib.SUC_RULE BOOLIFY_def, Thm.CONJUNCT1 l2n_def, l2n_2_thms,
       num_from_bin_list_def, num_from_oct_list_def, num_from_dec_list_def,
       num_from_hex_list_def,
       num_to_bin_list_def, num_to_oct_list_def, num_to_dec_list_def,
       num_to_hex_list_def] @
      List.map l2n_rule (tl sizes) @ List.map n2l_rule sizes
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
