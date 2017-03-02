(*---------------------------------------------------------------------------*
 * The "boss" library. This provides a collection of proof routines.         *
 * They provide                                                              *
 *                                                                           *
 *    1. Automatic maintenance of the usual products of a datatype           *
 *       definition.                                                         *
 *                                                                           *
 *    2. Some tools that work using that information.                        *
 *                                                                           *
 *    3. Some basic automation support.                                      *
 *                                                                           *
 *---------------------------------------------------------------------------*)

structure bossLib :> bossLib =
struct

open HolKernel Parse boolLib pairLib simpLib metisLib pred_setLib
     boolSimps quantHeuristicsLib

(* This makes the dependency on listTheory and optionTheory explicit.
   Without it, the theories can change, and bossLib won't get recompiled.
   This is because the listSimps and optionSimps signatures do not change
   in the event of listTheory and optionTheory changing. *)

local open listTheory optionTheory
           combinSyntax listSyntax optionSyntax numSyntax oneSyntax sumSyntax
           (* EvalRef Lift; *)
in end;

val ERR = mk_HOL_ERR "bossLib";

val new_specification = pairLib.new_specification;

(*---------------------------------------------------------------------------*
            Datatype definition
 *---------------------------------------------------------------------------*)

fun type_rws ty = #rewrs (TypeBase.simpls_of ty)

val Hol_datatype = Datatype.Hol_datatype
val Datatype = Datatype.Datatype


(*---------------------------------------------------------------------------
            Function definition
 ---------------------------------------------------------------------------*)

val xDefine    = TotalDefn.xDefine
val tDefine    = TotalDefn.tDefine
val Define     = TotalDefn.Define
val zDefine    = Lib.with_flag (computeLib.auto_import_definitions,false) Define
val Hol_defn   = Defn.Hol_defn
val Hol_reln   = IndDefLib.Hol_reln
val xHol_reln   = IndDefLib.xHol_reln
val Hol_coreln  = CoIndDefLib.Hol_coreln
val xHol_coreln = CoIndDefLib.xHol_coreln
val export_mono = IndDefLib.export_mono
val WF_REL_TAC = TotalDefn.WF_REL_TAC


(*---------------------------------------------------------------------------
            Automated proof operations
 ---------------------------------------------------------------------------*)

val PROVE           = BasicProvers.PROVE
val PROVE_TAC       = BasicProvers.PROVE_TAC
val prove_tac       = BasicProvers.PROVE_TAC
val METIS_PROVE     = metisLib.METIS_PROVE
val METIS_TAC       = metisLib.METIS_TAC
val metis_tac       = METIS_TAC
val RW_TAC          = BasicProvers.RW_TAC
val SRW_TAC         = BasicProvers.SRW_TAC
val rw_tac          = BasicProvers.RW_TAC
val srw_tac         = BasicProvers.SRW_TAC
val srw_tac         = BasicProvers.srw_tac
val srw_ss          = BasicProvers.srw_ss
val augment_srw_ss  = BasicProvers.augment_srw_ss
val diminish_srw_ss = BasicProvers.diminish_srw_ss
val export_rewrites = BasicProvers.export_rewrites

val EVAL           = computeLib.EVAL_CONV;
val EVAL_RULE      = computeLib.EVAL_RULE
val EVAL_TAC       = computeLib.EVAL_TAC

val QI_TAC = quantHeuristicsLib.QUANT_INSTANTIATE_TAC [std_qp]
val ASM_QI_TAC = quantHeuristicsLib.ASM_QUANT_INSTANTIATE_TAC [std_qp]
fun GEN_EXISTS_TAC v i = quantHeuristicsLib.QUANT_TAC [(v, i, [])]

val op && = simpLib.&&;

(*---------------------------------------------------------------------------
     The following simplification sets will be applied in a context
     that extends that loaded by bossLib. They are intended to be used
     by RW_TAC. The choice of which simpset to use depends on factors
     such as running time.  For example, RW_TAC with arith_ss (and thus
     with list_ss) may take a long time on some goals featuring arithmetic
     terms (since the arithmetic decision procedure may be invoked). In
     such cases, it may be worth dropping down to use std_ss,
     supplying whatever arithmetic theorems are required, so that
     simplification is quick.
 ---------------------------------------------------------------------------*)

local open sumTheory pred_setTheory
      infix ++
in

val QI_ss = quantHeuristicsLib.QUANT_INST_ss [std_qp]
val pure_ss = pureSimps.pure_ss
val bool_ss = boolSimps.bool_ss
val std_ss = numLib.std_ss
val arith_ss = numLib.arith_ss
val old_arith_ss = std_ss ++ numSimps.old_ARITH_ss
val ARITH_ss = numSimps.ARITH_ss
val old_ARITH_ss = numSimps.old_ARITH_ss
val list_ss  = arith_ss ++ listSimps.LIST_ss
                        ++ rewrites [IN_INSERT, NOT_IN_EMPTY, IN_UNION]
end

val DECIDE = numLib.DECIDE;
val DECIDE_TAC = numLib.DECIDE_TAC;
val decide_tac = DECIDE_TAC

fun ZAP_TAC ss thl =
   BasicProvers.STP_TAC ss
      (tautLib.TAUT_TAC
          ORELSE DECIDE_TAC
          ORELSE BasicProvers.GEN_PROVE_TAC 0 12 1 thl);

fun kall_tac x = Tactical.all_tac
val cheat:tactic = fn g => ([], fn _ => Thm.mk_oracle_thm "cheat" g)

(*---------------------------------------------------------------------------
    Single step interactive proof operations
 ---------------------------------------------------------------------------*)


val Cases     = BasicProvers.Cases
val Induct    = BasicProvers.Induct
val recInduct = Induction.recInduct

val Cases_on          = BasicProvers.Cases_on
val Induct_on         = BasicProvers.Induct_on
val PairCases_on      = pairLib.PairCases_on;
val completeInduct_on = numLib.completeInduct_on
val measureInduct_on  = numLib.measureInduct_on;

val SPOSE_NOT_THEN    = BasicProvers.SPOSE_NOT_THEN
val spose_not_then    = BasicProvers.SPOSE_NOT_THEN

val op by             = BasicProvers.by; (* infix 8 by *)
val op suffices_by    = BasicProvers.suffices_by

val CASE_TAC          = BasicProvers.CASE_TAC;

(*---------------------------------------------------------------------------*)
(* Working with abbreviations.                                               *)
(*---------------------------------------------------------------------------*)

val Abbr = markerLib.Abbr
val UNABBREV_ALL_TAC = markerLib.UNABBREV_ALL_TAC
val REABBREV_TAC = markerLib.REABBREV_TAC
val WITHOUT_ABBREVS = markerLib.WITHOUT_ABBREVS

(* ----------------------------------------------------------------------
    convenient simplification aliases
   ---------------------------------------------------------------------- *)

open simpLib
fun stateful f ssfl thm : tactic =
  let
    val ss = List.foldl (simpLib.++ o Lib.swap) (srw_ss()) ssfl
  in
    f ss thm
  end

val ARITH_ss = numSimps.ARITH_ss
val fsrw_tac = stateful full_simp_tac
val rfsrw_tac = stateful rev_full_simp_tac

val let_arith_list = [boolSimps.LET_ss, ARITH_ss]
val simp = stateful asm_simp_tac let_arith_list
val dsimp = stateful asm_simp_tac (boolSimps.DNF_ss :: let_arith_list)
val csimp = stateful asm_simp_tac (boolSimps.CONJ_ss :: let_arith_list)

val lrw = srw_tac let_arith_list
val lfs = fsrw_tac let_arith_list
val lrfs = rfsrw_tac let_arith_list

val rw = srw_tac let_arith_list
val fs = fsrw_tac let_arith_list
val rfs = rfsrw_tac let_arith_list

  (* useful quotation-based tactics (from Q) *)
  val qx_gen_tac : term quotation -> tactic = Q.X_GEN_TAC
  val qx_choose_then = Q.X_CHOOSE_THEN
  val qexists_tac : term quotation -> tactic = Q.EXISTS_TAC
  val qsuff_tac : term quotation -> tactic = Q_TAC SUFF_TAC
  val qspec_tac = Q.SPEC_TAC
  val qid_spec_tac : term quotation -> tactic = Q.ID_SPEC_TAC
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic = Q.SPEC_THEN
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic =
     Q.SPECL_THEN
  val qpat_assum : term quotation -> thm_tactic -> tactic = Q.PAT_ASSUM
  val qpat_abbrev_tac : term quotation -> tactic = Q.PAT_ABBREV_TAC
  val qmatch_abbrev_tac : term quotation -> tactic = Q.MATCH_ABBREV_TAC
  val qho_match_abbrev_tac : term quotation -> tactic = Q.HO_MATCH_ABBREV_TAC
  val qmatch_rename_tac : term quotation -> tactic =
     Q.MATCH_RENAME_TAC
  val qmatch_assum_abbrev_tac : term quotation -> tactic =
     Q.MATCH_ASSUM_ABBREV_TAC
  val qmatch_assum_rename_tac : term quotation -> tactic =
     Q.MATCH_ASSUM_RENAME_TAC
  val qmatch_asmsub_rename_tac = Q.MATCH_ASMSUB_RENAME_TAC
  val qmatch_goalsub_rename_tac = Q.MATCH_GOALSUB_RENAME_TAC
  val rename1 = Q.RENAME1_TAC
  val rename = Q.RENAME_TAC

  val qabbrev_tac : term quotation -> tactic = Q.ABBREV_TAC
  val qunabbrev_tac : term quotation -> tactic = Q.UNABBREV_TAC
  val unabbrev_all_tac : tactic = markerLib.UNABBREV_ALL_TAC

  val qx_genl_tac = map_every qx_gen_tac
  fun qx_choosel_then [] ttac = ttac
    | qx_choosel_then (q::qs) ttac = qx_choose_then q (qx_choosel_then qs ttac)


end
