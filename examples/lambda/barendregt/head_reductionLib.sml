(* ========================================================================== *)
(* FILE    : head_reductionLib                                                *)
(* TITLE   : Tactics for head normal form decomposition (HNF_TAC)             *)
(*                                                                            *)
(* AUTHORS : 2023-2024 The Australian National University (Chun TIAN)         *)
(* ========================================================================== *)

structure head_reductionLib :> head_reductionLib =
struct

open HolKernel Parse boolLib bossLib;

open hurdUtils head_reductionTheory solvableTheory;

structure Parse = struct
  val (Type,Term) = parse_from_grammars solvableTheory.solvable_grammars
end
open Parse;

(* Given a hnf ‘M0’ and a shared (by multiple terms) binding variable list ‘vs’,
   HNF_TAC adds the following abbreviation and new assumptions:

   Abbrev (M1 = principle_hnf (M0 @* MAP VAR (TAKE (LAMl_size M0) vs)))
   M0 = LAMl (TAKE (LAMl_size M0) vs) (VAR y @* args)
   M1 = VAR y @* args

   where the names "M1", "y" and "args" can be chosen from inputs.

   NOTE: HNF_TAC expects that there's already an abbreviation for M1, which is
   re-defined as above with ‘TAKE’ involved. In case of single term who fully
   owns ‘vs’, the following tactics can be followed to eliminate ‘TAKE’:

  ‘TAKE n vs = vs’ by rw [] >> POP_ASSUM (rfs o wrap)

   NOTE: Since the symbol behind M1 is always presented in assumptions, it's
   recommended to use Q_TAC together, in the following form:

   Q_TAC (HNF_TAC (“M0 :term”, “vs :string list”,
                   “y :string”, “args :term list”)) ‘M1’

   This doesn't save much in number of letters, just putting ‘M1’ special in a
   sense that its abbreviation will be updated (deleted and re-defined).
 *)
fun HNF_TAC (M0, vs, y, args) M1 = let
    val n = “LAMl_size ^M0” in
    qunabbrev_tac ‘^M1’
 >> qabbrev_tac ‘^M1 = principle_hnf (^M0 @* MAP VAR (TAKE ^n ^vs))’
 >> Know ‘?^y ^args. ^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
 >- (‘hnf ^M0’ by PROVE_TAC [hnf_principle_hnf, hnf_principle_hnf'] \\
     irule (iffLR hnf_cases_shared) >> rw [])
 >> STRIP_TAC
 >> Know ‘^M1 = VAR ^y @* ^args’
 >- (qunabbrev_tac ‘^M1’ \\
     Q.PAT_ASSUM ‘^M0 = LAMl (TAKE ^n ^vs) (VAR ^y @* ^args)’
        (fn th => REWRITE_TAC [Once th]) \\
     MATCH_MP_TAC principle_hnf_beta_reduce >> rw [hnf_appstar])
 >> DISCH_TAC
end;

(* Remove all ‘T’ assumptions *)
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);

(* Provided by Michael Norrish. It is roughly equivalent to RW_TAC std_ss ths
   (which eliminates LET and creates abbreviations) but does not do STRIP_TAC
   on the goal.
 *)
fun UNBETA_TAC ths tm = let
    val P = genvar (type_of tm --> bool)
in
    CONV_TAC (UNBETA_CONV tm)
 >> qmatch_abbrev_tac ‘^P _’
 >> RW_TAC bool_ss ths (* LET-elimination and abbreviation creation *)
 >> ASM_SIMP_TAC std_ss [Abbr ‘^P’]
end;

end (* struct *)
