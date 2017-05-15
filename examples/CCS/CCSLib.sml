(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure CCSLib :> CCSLib =
struct

open HolKernel Parse boolLib bossLib;

(******************************************************************************)
(*                                                                            *)
(*            Backward compatibility and utility tactic/tacticals             *)
(*                                                                            *)
(******************************************************************************)

local
    val PAT_X_ASSUM = PAT_ASSUM;
    val qpat_x_assum = Q.PAT_ASSUM;
    open Tactical
in
    (* Backward compatibility with Kananaskis 11 *)
    val PAT_X_ASSUM = PAT_X_ASSUM;
    val qpat_x_assum = qpat_x_assum;

    (* Tacticals for better expressivity *)
    fun fix  ts = MAP_EVERY Q.X_GEN_TAC ts;	(* from HOL Light *)
    fun set  ts = MAP_EVERY Q.ABBREV_TAC ts;	(* from HOL mizar mode *)
    fun take ts = MAP_EVERY Q.EXISTS_TAC ts;	(* from HOL mizar mode *)
    val op // = op REPEAT			(* from Matita *)
end;

(******************************************************************************)
(*                                                                            *)
(*                      Minimal grammar support for CCS                       *)
(*                                                                            *)
(******************************************************************************)

fun add_rules_for_ccs_terms () = let
in
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0, TOK "->",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

    add_rule { term_name = "WEAK_TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "==", HardSpace 0, TM, HardSpace 0, TOK "=>>",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

    overload_on ("+", ``sum``); (* priority: 500 *)

    set_mapped_fixity { fixity = Infix(LEFT, 600), tok = "||", term_name = "par" };

    add_rule { term_name = "prefix", fixity = Infix(RIGHT, 700),
	pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) }
end;

fun remove_rules_for_ccs_terms () = let
in
    remove_rules_for_term	"prefix";
    remove_rules_for_term	"par";
    clear_overloads_on		"sum";
    remove_rules_for_term	"TRANS";
    remove_rules_for_term	"WEAK_TRANS"
end;

(******************************************************************************)
(*                                                                            *)
(*         Basic rules and tactics for particular forms of rewriting          *)
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
