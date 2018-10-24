(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure CCSLib :> CCSLib =
struct

open HolKernel Parse boolLib bossLib;

(******************************************************************************)
(*                                                                            *)
(*      Backward compatibility and utility tactic/tacticals (17 oct 2017)     *)
(*                                                                            *)
(******************************************************************************)

(* from Brian Campbell. No uses of (Q.)PAT_ASSUM !! *)
local
    val PAT_X_ASSUM = PAT_ASSUM;
    open Tactical
in
    val PAT_X_ASSUM = PAT_X_ASSUM;
end;

local
    val PAT_X_ASSUM = Q.PAT_ASSUM;
    open Q;
in
    val qpat_x_assum = PAT_X_ASSUM;
end;

(** Q.GENL generalises in wrong order #428, fixed on June 27, 2017 *)
fun Q_GENL qs th = List.foldr (fn (q, th) => Q.GEN q th) th qs;

(* Tacticals for better expressivity *)
fun fix   ts = MAP_EVERY Q.X_GEN_TAC ts;        (* from HOL Light *)
fun set   ts = MAP_EVERY Q.ABBREV_TAC ts;       (* from HOL mizar mode *)
fun take  ts = MAP_EVERY Q.EXISTS_TAC ts;       (* from HOL mizar mode *)
val Know     = Q_TAC KNOW_TAC;                  (* from util_prob *)
val Suff     = Q_TAC SUFF_TAC;                  (* from util_prob *)
fun K_TAC _  = ALL_TAC;                         (* from util_prob *)
val KILL_TAC = POP_ASSUM_LIST K_TAC;            (* from util_prob *)
fun wrap   a = [a];                             (* from util_prob *)
val art      = ASM_REWRITE_TAC;
val Rewr     = DISCH_THEN (REWRITE_TAC o wrap); (* from util_prob *)
val Rewr'    = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val Rev      = Tactical.REVERSE;                (* REVERSE has different meaning
                                                   in rich_listTheory *)

fun PRINT_TAC s gl =                            (* from cardinalTheory *)
  (print ("** " ^ s ^ "\n"); ALL_TAC gl);

fun COUNT_TAC tac g =                           (* from Konrad Slind *)
   let val res as (sg, _) = tac g
       val _ = print ("subgoals: " ^ Int.toString (List.length sg) ^ "\n")
   in res end;

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th >> CONJ_TAC
end;

(* directly remove an assumption by its index *)
fun X_TAC n = (NTAC n (POP_ASSUM MP_TAC)) \\    (* n = last - target *)
              POP_ASSUM K_TAC >> (NTAC n DISCH_TAC);

(* signatures:

  val PAT_X_ASSUM               : term -> thm_tactic -> tactic
  val qpat_x_assum              : Q.tmquote -> thm_tactic -> tactic
  val Q_GENL                    : Q.tmquote list -> thm -> thm
  val fix                       : Q.tmquote list -> tactic
  val set                       : Q.tmquote list -> tactic
  val take                      : Q.tmquote list -> tactic
  val Know                      : Q.tmquote -> tactic
  val Suff                      : Q.tmquote -> tactic
  val K_TAC                     : 'a -> tactic
  val KILL_TAC                  : tactic
  val wrap                      : 'a -> 'a list
  val art                       : thm list -> tactic
  val Rewr                      : tactic
  val Rewr'                     : tactic
  val Rev                       : tactic -> tactic
  val PRINT_TAC                 : string -> tactic
  val COUNT_TAC                 : tactic -> tactic
  val STRONG_CONJ_TAC           : tactic
  val X_TAC                     : int -> tactic

   end of signatures *)

(******************************************************************************)
(*                                                                            *)
(*       Basic rules and tactics for particular forms of rewriting            *)
(*                                                                            *)
(******************************************************************************)

(* Rule for rewriting only the right-hand side on an equation once. *)
val ONCE_REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the right-hand side on an equation (pure version). *)
val PURE_REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the right-hand side on an equation
   (basic rewrites included) *)
val REWRITE_RHS_RULE =
    GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Tactic for rewriting only the right-hand side on an equation once. *)
val ONCE_REWRITE_RHS_TAC =
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Tactic for rewriting only the right-hand side on an equation. *)
val REWRITE_RHS_TAC =
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Rule for rewriting only the left-hand side on an equation once. *)
val ONCE_REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the left-hand side on an equation (pure version). *)
val PURE_REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) empty_rewrites;

(* Rule for rewriting only the left-hand side on an equation
   (basic rewrites included). *)
val REWRITE_LHS_RULE =
    GEN_REWRITE_RULE (RATOR_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Tactic for rewriting only the left-hand side on an equation once. *)
val ONCE_REWRITE_LHS_TAC =
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites;

(* Tactic for rewriting only the left-hand side on an equation. *)
val REWRITE_LHS_TAC =
    GEN_REWRITE_TAC (RATOR_CONV o TOP_DEPTH_CONV) (implicit_rewrites ());

(* Rule for rewriting only the left-hand side of an equation once with the
   assumptions. *)
fun ONCE_ASM_REWRITE_LHS_RULE thl th =
    ONCE_REWRITE_LHS_RULE ((map ASSUME (hyp th)) @ thl) th;

(* Tactic for rewriting only the left-hand side of an equation once with the
   assumptions. *)
fun ONCE_ASM_REWRITE_LHS_TAC thl =
    ASSUM_LIST (fn asl => ONCE_REWRITE_LHS_TAC (asl @ thl));

(* Conversion to swap two universally quantified variables. *)
fun SWAP_FORALL_CONV tm = let
    val (v1, body) = dest_forall tm;
    val v2 = fst (dest_forall body);
    val tl1 = [v1, v2] and tl2 = [v2, v1];
    val th1 = GENL tl2 (SPECL tl1 (ASSUME tm));
    val th2 = GENL tl1 (SPECL tl2 (ASSUME (concl th1)))
in
    IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th2)
end;

(* provided by Michael Norrish *)
fun STRIP_FORALL_RULE f th =
  let
      val (vs, _) = strip_forall (concl th)
  in
      GENL vs (f (SPEC_ALL th))
  end;

(* The rule EQ_IMP_LR returns the implication from left to right of a given
   equational theorem. *)
val EQ_IMP_LR = STRIP_FORALL_RULE (fst o EQ_IMP_RULE);

(* The rule EQ_IMP_RL returns the implication from right to left of a given
   equational theorem. *)
val EQ_IMP_RL = STRIP_FORALL_RULE (snd o EQ_IMP_RULE);

(* Functions to get the left and right hand side of the equational conclusion
   of a theorem. *)
val lconcl = fst o dest_eq o concl o SPEC_ALL;
val rconcl = snd o dest_eq o concl o SPEC_ALL;

(* Define args_thm as a function that, given a theorem |- f t1 t2, returns (t1, t2). *)
fun args_thm thm = let
    val (f, [t1, t2]) = strip_comb (concl thm)
in
    (t1, t2)
end;

fun lhs_tm thm = (fst o args_thm) thm;
fun rhs_tm thm = (snd o args_thm) thm;

(* Define args_equiv as a function that, given a tm "p t1 t2", returns (p, t1, t2) *)
fun args_equiv tm = let
    val (p, [t1, t2]) = strip_comb tm
in
    (p, t1, t2)
end;

(* Auxiliary functions (on lists and terms) to find repeated occurrences of a
   summand to be then deleted by applying the idempotence law for summation. *)
local
    fun helper (h:term, nil) = nil
      | helper (h, t::l) = if h = t then l else t :: (helper (h, l))
in
    fun elim h l = helper (h, l)
end;

(* Function for applying a list of tactics to a list of subgoals. *)
fun list_apply_tac _ [] = []
  | list_apply_tac (f: 'a -> tactic) (actl : 'a list) : tactic list =
    (f (hd actl)) :: (list_apply_tac f (tl actl));

end (* struct *)

(* last updated: May 7, 2017 *)
