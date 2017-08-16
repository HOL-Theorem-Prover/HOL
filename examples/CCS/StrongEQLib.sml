(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure StrongEQLib :> StrongEQLib =
struct

open HolKernel Parse boolLib bossLib;

open IndDefRules;
open CCSLib CCSTheory CCSSyntax StrongEQTheory;

infixr 0 S_THENC S_ORELSEC;

(******************************************************************************)
(*									      *)
(*	Basic functions and conversions for rewriting with		      *)
(*	  the CCS laws for strong equivalence (basic_fun.ml)		      *)
(*									      *)
(******************************************************************************)

(* Define S_SYM such that, when given a theorem A |- STRONG_EQUIV t1 t2,
   returns the theorem A |- STRONG_EQUIV t2 t1. *)
fun S_SYM thm = MATCH_MP STRONG_EQUIV_SYM thm;

(* Define S_TRANS such that, when given the theorems thm1 and thm2, applies
   STRONG_EQUIV_TRANS on them, if possible. *)
fun S_TRANS thm1 thm2 =
    if rhs_tm thm1 = lhs_tm thm2 then
       MATCH_MP STRONG_EQUIV_TRANS (CONJ thm1 thm2)
    else
       failwith "transitivity of strong equivalence not applicable";

(* When applied to a term "t: CCS", the conversion S_ALL_CONV returns the
   theorem: |- STRONG_EQUIV t t *)
fun S_ALL_CONV t = ISPEC t STRONG_EQUIV_REFL;

fun op S_THENC ((c1, c2) :conv * conv) :conv =
  fn t => let
      val thm1 = c1 t;
      val thm2 = c2 (rhs_tm thm1)
  in
      S_TRANS thm1 thm2
  end;

fun op S_ORELSEC ((c1, c2) :conv * conv) :conv =
  fn t => c1 t handle HOL_ERR _ => c2 t;

fun S_REPEATC (c :conv) (t :term) :thm =
  ((c S_THENC (S_REPEATC c)) S_ORELSEC S_ALL_CONV) t;

(* Convert a conversion for the application of the laws for STRONG_EQUIV to a tactic. *)
fun S_LHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``STRONG_EQUIV``) then
	  let val thm = c t1;
	      val (t1', t') = args_thm thm (* t1' = t1 *)
	  in
	      if (t' = t2) then
		  ([], fn [] => S_TRANS thm (ISPEC t' STRONG_EQUIV_REFL))
	      else
		  ([(asl, ``STRONG_EQUIV ^t' ^t2``)],
		   fn [thm'] => S_TRANS thm thm')
	  end
      else
	  failwith "the goal is not a STRONG_EQUIV relation"
  end;

fun S_RHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``STRONG_EQUIV``) then
	  let val thm = c t2;
	      val (t2', t'') = args_thm thm (* t2' = t2 *)
	  in
	      if (t'' = t1) then
		  ([], fn [] => S_SYM thm)
	      else
		  ([(asl, ``STRONG_EQUIV ^t1 ^t''``)],
		   fn [thm'] => S_TRANS thm' (S_SYM thm))
	  end
      else
	  failwith "the goal is not a STRONG_EQUIV relation"
  end;

(******************************************************************************)
(*									      *)
(*          Basic conversions and tactics for applying the laws for	      *)
(*                strong equivalence					      *)
(*									      *)
(******************************************************************************)

fun S_SUB_CONV (c :conv) tm =
  if is_prefix tm then
      let val (u, P) = args_prefix tm;
	  val thm = c P
      in
	  ISPEC u (MATCH_MP STRONG_EQUIV_SUBST_PREFIX thm)
      end
  else if is_sum tm then
      let val (t1, t2) = args_sum tm;
	  val thm1 = c t1
	  and thm2 = c t2
      in
	  MATCH_MP STRONG_EQUIV_PRESD_BY_SUM (CONJ thm1 thm2)
      end
  else if is_par tm then
      let val (t1, t2) = args_par tm;
	  val thm1 = c t1
	  and thm2 = c t2
      in
	  MATCH_MP STRONG_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2)
      end
  else if is_restr tm then
      let val (P, L) = args_restr tm;
	  val thm = c P
      in
	  ISPEC L (MATCH_MP STRONG_EQUIV_SUBST_RESTR thm)
      end
  else if is_relab tm then
      let val (P, rf) = args_relab tm;
	  val thm = c P
      in
	  ISPEC rf (MATCH_MP STRONG_EQUIV_SUBST_RELAB thm)
      end
  else
      S_ALL_CONV tm;

fun S_DEPTH_CONV (c :conv) t =
  S_SUB_CONV ((S_DEPTH_CONV c) S_THENC (S_REPEATC c)) t;

fun S_TOP_DEPTH_CONV (c :conv) t =
   ((S_REPEATC c) S_THENC
    (S_SUB_CONV (S_TOP_DEPTH_CONV c)) S_THENC
    ((c S_THENC (S_TOP_DEPTH_CONV c)) S_ORELSEC S_ALL_CONV))
   t;

(* Define the function S_SUBST for substitution in STRONG_EQUIV terms. *)
fun S_SUBST thm tm :thm = let
    val (ti, ti') = args_thm thm
in
    if (tm = ti) then thm
    else if is_prefix tm then
	let val (u, t) = args_prefix tm;
	    val thm1 = S_SUBST thm t
	in
	    ISPEC u (MATCH_MP STRONG_EQUIV_SUBST_PREFIX thm1)
	end
    else if is_sum tm then
	let val (t1, t2) = args_sum tm;
	    val thm1 = S_SUBST thm t1
	    and thm2 = S_SUBST thm t2
	in
	    MATCH_MP STRONG_EQUIV_PRESD_BY_SUM (CONJ thm1 thm2)
	end
    else if is_par tm then
	let val (t1, t2) = args_par tm;
	    val thm1 = S_SUBST thm t1
	    and thm2 = S_SUBST thm t2
	in
	    MATCH_MP STRONG_EQUIV_PRESD_BY_PAR (CONJ thm1 thm2)
	end
    else if is_restr tm then
	let val (t, L) = args_restr tm;
	    val thm1 = S_SUBST thm t
	in
	    ISPEC L (MATCH_MP STRONG_EQUIV_SUBST_RESTR thm1)
	end
    else if is_relab tm then
	let val (t, rf) = args_relab tm;
	    val thm1 = S_SUBST thm t
	in
	    ISPEC rf (MATCH_MP STRONG_EQUIV_SUBST_RELAB thm1)
	end
    else
	S_ALL_CONV tm
end;

(* Define the tactic S_LHS_SUBST1_TAC: thm_tactic which substitutes a theorem
   in the left-hand side of a strong equivalence. *)
fun S_LHS_SUBST1_TAC thm :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``STRONG_EQUIV``) then
	  let val thm' = S_SUBST thm t1;
	      val (t1', t') = args_thm thm' (* t1' = t1 *)
	  in
	      if (t' = t2) then
		  ([], fn [] => S_TRANS thm' (ISPEC t' STRONG_EQUIV_REFL))
	      else
		  ([(asl, ``STRONG_EQUIV ^t' ^t2``)],
		   fn [thm''] => S_TRANS thm' thm'')
	  end
      else
	  failwith "the goal is not a STRONG_EQUIV relation"
  end;

(* The tactic S_LHS_SUBST_TAC substitutes a list of theorems in the left-hand
   side of a strong equivalence. *)
fun S_LHS_SUBST_TAC thmlist = EVERY (map S_LHS_SUBST1_TAC thmlist);

(* The tactic S_RHS_SUBST1_TAC substitutes a theorem in the right-hand side of
   a strong equivalence. *)
fun S_RHS_SUBST1_TAC thm =
    REPEAT GEN_TAC
 >> RULE_TAC STRONG_EQUIV_SYM
 >> S_LHS_SUBST1_TAC thm
 >> RULE_TAC STRONG_EQUIV_SYM;

(* The tactic S_RHS_SUBST_TAC substitutes a list of theorems in the right-hand
   side of a strong equivalence. *)
fun S_RHS_SUBST_TAC thmlist =
    REPEAT GEN_TAC
 >> RULE_TAC STRONG_EQUIV_SYM
 >> S_LHS_SUBST_TAC thmlist
 >> RULE_TAC STRONG_EQUIV_SYM;

(* The tactic S_SUBST1_TAC (S_SUBST_TAC) substitutes a (list of) theorem(s) in
   both sides of a strong equivalence. *)
fun S_SUBST1_TAC thm =
    S_LHS_SUBST1_TAC thm
 >> S_RHS_SUBST1_TAC thm;

fun S_SUBST_TAC thmlist =
    S_LHS_SUBST_TAC thmlist
 >> S_RHS_SUBST_TAC thmlist;

end (* struct *)

(* last updated: May 14, 2017 *)
