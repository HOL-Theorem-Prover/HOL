(* ========================================================================= *)
(* FILE          : fcpLib.sml                                                *)
(* DESCRIPTION   : Tools for fcpTheory.                                      *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

structure fcpLib :> fcpLib =
struct

open HolKernel Parse boolLib bossLib
open fcpTheory fcpSyntax

(* ------------------------------------------------------------------------- *)

val index_type   = fcpSyntax.mk_numeric_type
val index_to_num = fcpSyntax.dest_numeric_type

fun index_compset () =
   let
      open numeral_bitTheory
      val compset = reduceLib.num_compset()
      val rule = REWRITE_RULE [arithmeticTheory.TIMES2, GSYM numeralTheory.iDUB]
      val () = computeLib.add_thms
                 [index_sum, index_one, rule index_bit0, rule index_bit1,
                  finite_sum, finite_one, finite_bit0, finite_bit1,
                  numeral_bitTheory.iDUB_NUMERAL] compset
   in
      compset
   end

val INDEX_CONV = Conv.CHANGED_CONV (computeLib.CBV_CONV (index_compset()))

local
   fun conv n = INDEX_CONV o Term.inst [Type.alpha |-> index_type n]
in
   fun DIMINDEX n = conv n (fcpSyntax.mk_dimindex Type.alpha)
   fun FINITE n =
      Type.alpha
      |> pred_setSyntax.mk_univ
      |> pred_setSyntax.mk_finite
      |> conv n
      |> Drule.EQT_ELIM
end

fun SIZE n =
   PURE_REWRITE_RULE [DIMINDEX n]
      (Thm.MP (Thm.INST_TYPE [Type.alpha |-> index_type n]
                  fcpTheory.card_dimindex)
              (FINITE n))

val FCP_ss =
  simpLib.rewrites [fcpTheory.FCP_BETA, fcpTheory.FCP_ETA, fcpTheory.CART_EQ]

val notify_on_length_guess = ref true

val () = Feedback.register_btrace
            ("notify FCP length guesses", notify_on_length_guess)

local
   fun t2s t = String.extract (Hol_pp.type_to_string t, 1, NONE)
   fun infer_fcp_type tm =
      case Lib.total (fst o listSyntax.dest_list o fcpSyntax.dest_l2v) tm of
         SOME l =>
            let
               val ty = snd (fcpSyntax.dest_cart_type (Term.type_of tm))
               val _ = Type.polymorphic ty orelse raise ERR "infer_fcp_type" ""
            in
               ty |-> index_type (Arbnum.fromInt (List.length l))
            end
       | NONE => raise ERR "infer_fcp_type" ""
in
   fun inst_fcp_lengths tm =
      case total (HolKernel.find_term (Lib.can infer_fcp_type)) tm of
         NONE => tm
       | SOME subtm =>
          let
             val theinst as {redex, residue} = infer_fcp_type subtm
             val _ = if !Globals.interactive andalso !notify_on_length_guess
                        then Feedback.HOL_MESG
                                (String.concat ["assigning FCP length: ",
                                                t2s redex, " <- ", t2s residue])
                     else ()
          in
             inst_fcp_lengths (Term.inst [theinst] tm)
          end
end

end
