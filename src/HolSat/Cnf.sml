(*****************************************************************************)
(* A CNF converter from Joe Hurd                                             *)
(*****************************************************************************)

(*
app load ["BasicProvers", "simpLib"];
*)

local

open Parse;
open BasicProvers;
open simpLib;
open Tactical;
open Term;
open Thm;
open Rewrite;
open boolTheory;
open Conv;
infix THENC ORELSEC;

in

(* --------------------------------- *)
(* A simple-minded CNF conversion.   *)
(* --------------------------------- *)

local

local
  open simpLib
  infix ++
in
  val EXPAND_COND_CONV =
    SIMP_CONV (pureSimps.pure_ss ++ boolSimps.COND_elim_ss) []
end

local
  val EQ_IFF = prove
    (``!a b. ((a:bool) = b) = ((a ==> b) /\ (b ==> a))``,
     BasicProvers.PROVE_TAC [])
in
  val EQ_IFF_CONV = PURE_REWRITE_CONV [EQ_IFF]
end;

local
  val IMP_DISJ = prove
    (``!a b. ((a:bool) ==> b) = ~a \/ b``,
     BasicProvers.PROVE_TAC [])
in
  val IMP_DISJ_CONV = PURE_REWRITE_CONV [IMP_DISJ]
end;

local
  val NEG_NEG = CONJUNCT1 NOT_CLAUSES
  val DE_MORGAN1
    = CONJUNCT1 (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) DE_MORGAN_THM)
  val DE_MORGAN2
    = CONJUNCT2 (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) DE_MORGAN_THM)
in
  val NNF_CONV = (REPEATC o CHANGED_CONV)
    (REWRITE_CONV [NEG_NEG, DE_MORGAN1, DE_MORGAN2]
     THENC DEPTH_CONV (NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))
end;

val EXISTS_OUT_CONV = (REPEATC o CHANGED_CONV o DEPTH_CONV)
  (LEFT_AND_EXISTS_CONV
   ORELSEC RIGHT_AND_EXISTS_CONV
   ORELSEC LEFT_OR_EXISTS_CONV
   ORELSEC RIGHT_OR_EXISTS_CONV
   ORELSEC CHANGED_CONV SKOLEM_CONV);

val ANDS_OUT_CONV = (REPEATC o CHANGED_CONV o DEPTH_CONV)
  (FORALL_AND_CONV
   ORELSEC REWR_CONV LEFT_OR_OVER_AND
   ORELSEC REWR_CONV RIGHT_OR_OVER_AND)

val FORALLS_OUT_CONV = (REPEATC o CHANGED_CONV o DEPTH_CONV)
  (LEFT_OR_FORALL_CONV
   ORELSEC RIGHT_OR_FORALL_CONV);

in

val CNF_CONV =
  DEPTH_CONV BETA_CONV
  THENC EXPAND_COND_CONV
  THENC EQ_IFF_CONV
  THENC IMP_DISJ_CONV
  THENC NNF_CONV
  THENC EXISTS_OUT_CONV
  THENC ANDS_OUT_CONV
  THENC FORALLS_OUT_CONV
  THENC REWRITE_CONV [GSYM DISJ_ASSOC, GSYM CONJ_ASSOC];

(*
val CNF_RULE = CONV_RULE CNF_CONV;
*)

end
end

