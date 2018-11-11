(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure ObsCongrLib :> ObsCongrLib =
struct

open HolKernel Parse boolLib bossLib;

open CCSLib CCSTheory CCSSyntax;
open StrongEQTheory StrongEQLib;
open WeakEQTheory WeakEQLib;
open ObsCongrTheory;

infix 0 OC_THENC OC_ORELSEC;

(******************************************************************************)
(*                                                                            *)
(*             Basic functions and conversions for rewriting with             *)
(*                 the CCS laws for observation congruence                    *)
(*                                                                            *)
(******************************************************************************)

(* Define OC_SYM such that, when given a theorem A |- OBS_CONGR t1 t2,
   returns the theorem A |- OBS_CONGR t2 t1.
 *)
fun OC_SYM thm = MATCH_MP OBS_CONGR_SYM thm;

(* Define OC_TRANS such that, when given the theorems thm1 and thm2, applies
   OBS_CONGR_TRANS on them, if possible. *)
fun OC_TRANS thm1 thm2 =
  if (rhs_tm thm1 = lhs_tm thm2) then
      MATCH_MP OBS_CONGR_TRANS (CONJ thm1 thm2)
  else
      failwith "transitivity of observation congruence not applicable";

(* When applied to a term "t: CCS", the conversion OC_ALL_CONV returns the
   theorem: |- OBS_CONGR t t *)
fun OC_ALL_CONV t = ISPEC t OBS_CONGR_REFL;

(* Define the function OC_THENC. *)
fun op OC_THENC ((c1, c2) :conv * conv) :conv =
  fn t => let
      val thm1 = c1 t;
      val thm2 = c2 (rhs_tm thm1)
  in OC_TRANS thm1 thm2 end;

(* Define the function OC_ORELSEC. *)
fun op OC_ORELSEC ((c1, c2) :conv * conv) :conv =
  fn t => c1 t handle HOL_ERR _ => c2 t;

(* Define the function OC_REPEATC. *)
fun OC_REPEATC (c: conv) (t :term) :thm =
  ((c OC_THENC (OC_REPEATC c)) OC_ORELSEC OC_ALL_CONV) t;

(* Convert a conversion for the application of the laws for OBS_CONGR to a
   tactic. *)
fun OC_LHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_CONGR``) then
          let val thm = c t1;
              val (t1', t') = args_thm thm (* t1' = t1 *)
          in
              if (t' = t2) then
                  ([], fn [] => OC_TRANS thm (ISPEC t' OBS_CONGR_REFL))
              else
                  ([(asl, ``OBS_CONGR ^t' ^t2``)],
                   fn [thm'] => OC_TRANS thm thm')
          end
      else
          failwith "the goal is not an OBS_CONGR relation"
  end;

fun OC_RHS_CONV_TAC (c :conv) :tactic =
  fn (asl, w) => let
      val (opt, t1, t2) = args_equiv w
  in
      if (opt = ``OBS_CONGR``) then
          let val thm = c t2;
              val (t2', t'') = args_thm thm (* t2' = t2 *)
          in
              if (t'' = t1) then
                  ([], fn [] => OC_SYM thm)
              else
                  ([(asl, ``OBS_CONGR ^t1 ^t''``)],
                   fn [thm'] => OC_TRANS thm' (OC_SYM thm))
          end
      else
          failwith "the goal is not an OBS_CONGR relation"
  end;

val STRONG_IMP_OBS_CONGR_RULE =
    STRIP_FORALL_RULE (MATCH_MP STRONG_IMP_OBS_CONGR);

val OBS_CONGR_IMP_WEAK_EQUIV_RULE =
    STRIP_FORALL_RULE (MATCH_MP OBS_CONGR_IMP_WEAK_EQUIV);

end (* struct *)

(* last updated: Jun 24, 2017 *)
