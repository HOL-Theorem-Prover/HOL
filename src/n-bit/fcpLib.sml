(* ========================================================================= *)
(* FILE          : fcpLib.sml                                                *)
(* DESCRIPTION   : Tools for fcpTheory.                                      *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

structure fcpLib :> fcpLib =
struct

(* interactive use:
  app load ["fcpTheory"];
*)

open HolKernel Parse boolLib bossLib;
open Q computeLib fcpTheory;

(* ------------------------------------------------------------------------- *)

fun index_type n =
  let open Arbnum in
    if mod2 n = zero then
      if n = zero then
        raise ERR "mk_index" "index size must be non-zero"
      else
        mk_type("bit0", [index_type (div2 n)])
    else
      if n = one then
        mk_type("one", [])
      else
        mk_type("bit1", [index_type (div2 (less1 n))])
  end;

local
  fun index2num typ =
  case dest_type typ of
    ("one", []) => SOME Arbnum.one
  | ("bool",[]) => SOME Arbnum.two
  | ("num", []) => NONE
  | ("int", []) => NONE
  | ("string", []) => NONE
  | ("list", [t]) => NONE
  | ("bit0", [t]) => (case index2num t of
                        SOME x => SOME (Arbnum.times2 x)
                      | _ => NONE)
  | ("bit1", [t]) => (case index2num t of
                        SOME x => SOME (Arbnum.plus1 (Arbnum.times2 x))
                      | _ => NONE)
  | ("sum",  [t,p]) => (case (index2num t, index2num p) of
                          (SOME x, SOME y) => SOME (Arbnum.+(x, y))
                        | _ => NONE)
  | ("prod", [t,p]) => (case (index2num t, index2num p) of
                          (SOME x, SOME y) => SOME (Arbnum.*(x, y))
                        | _ => NONE)
  | ("fun",  [t,p]) => (case (index2num p, index2num t) of
                          (SOME x, SOME y) => SOME (Arbnum.pow(x, y))
                        | _ => NONE)
  | ("cart", [t,p]) => (case (index2num t, index2num p) of
                          (SOME x, SOME y) => SOME (Arbnum.pow(x, y))
                        | _ => NONE)
  | _ => failwith ("Can't compute size of type " ^ type_to_string typ);
in
  fun index_to_num typ = case index2num typ of SOME x => x | NONE => Arbnum.one
end;

fun index_compset () =
  let val compset = reduceLib.num_compset()
      val rule = REWRITE_RULE [arithmeticTheory.TIMES2, GSYM numeralTheory.iDUB]
      val _ = add_thms [index_sum,index_one,rule index_bit0, rule index_bit1,
                        finite_sum,finite_one,finite_bit0,finite_bit1,
                        numeral_bitTheory.iDUB_NUMERAL] compset
in
  compset
end;

val INDEX_CONV = CHANGED_CONV (CBV_CONV (index_compset()));

fun conv n = INDEX_CONV o inst [alpha |-> index_type n];

fun DIMINDEX n = conv n ``dimindex(:'a)``;

fun FINITE n = (EQT_ELIM o conv n) ``FINITE(UNIV:'a->bool)``;

fun SIZE n = PURE_REWRITE_RULE [DIMINDEX n]
               (MP (Thm.INST_TYPE [alpha |-> index_type n] card_dimindex)
                   (FINITE n));

val FCP_ss = rewrites [FCP_BETA,FCP_ETA,CART_EQ];

val notify_on_length_guess = ref true;

val _ = Feedback.register_btrace("notify FCP length guesses",
                                  notify_on_length_guess);

local
  fun t2s t = String.extract(Hol_pp.type_to_string t, 1, NONE)

  val L2V_tm = prim_mk_const{Name="L2V",Thy="fcp"}

  fun dest_L2V tm =
      let
        val (c,a) = dest_comb tm
        val _ = same_const c L2V_tm orelse raise ERR "dest_L2V" ""
        val ty = type_of tm
        val b = hd (tl (snd (dest_type ty)))
      in
        (a,b)
      end;

  fun list_length tm =
      if listSyntax.is_nil tm then 0
      else if listSyntax.is_cons tm then 1 + list_length (rand tm)
      else raise ERR "list_length" "";

  fun infer_fcp_type tm =
      let
        val (l,ty) = dest_L2V tm
        val _ = Type.polymorphic ty orelse raise ERR "infer_fcp_type" ""
        val n = list_length l
        val ty' = index_type (Arbnum.fromInt n)
      in
        ty |-> ty'
      end;
in
  fun inst_fcp_lengths tm =
      case total (find_term (can infer_fcp_type)) tm of
        NONE => tm
      | SOME subtm =>
          let val (theinst as {redex,residue}) = infer_fcp_type subtm
              val _ = if !Globals.interactive andalso !notify_on_length_guess
                      then
                        Feedback.HOL_MESG
                          (String.concat ["assigning FCP length: ",
                                          t2s redex, " <- ", t2s residue])
                      else
                        ()
          in
            inst_fcp_lengths (Term.inst [theinst] tm)
          end
end;

end
