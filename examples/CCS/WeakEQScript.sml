(*
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open stringTheory pred_setTheory relationTheory listTheory;
open CCSLib CCSTheory StrongEQTheory StrongEQLib;

val _ = new_theory "WeakEQ";

(******************************************************************************)
(*                                                                            *)
(*                             Weak transitions                               *)
(*                                                                            *)
(******************************************************************************)

val epsilon_def = Define `epsilon = []`;
val _ = Unicode.unicode_version { u = UTF8.chr 0x03B5, tmnm = "epsilon"};
val _ = TeX_notation { hol = UTF8.chr 0x03B5,
                       TeX = ("\\HOLepsilon", 1) };

(* val _ = type_abbrev ("trace", ``:Label list``); *)

val (TRACE_rules, TRACE_ind, TRACE_cases) = Hol_reln `
    (!E.                               TRACE E epsilon E) /\
    (!E E' l. TRANS E (label l) E' ==> TRACE E [l] E') /\
    (!E1 E2 E3 l1 l2.
              TRACE E1 l1 E2 /\
              TRACE E2 l2 E3 ==> TRACE E1 (l1 ++ l2) E3)`;

val (WEAK_TRACE_rules, WEAK_TRACE_ind, WEAK_TRACE_cases) = Hol_reln `
    (!E.                               WEAK_TRACE E epsilon E) /\
    (!E E'.   TRANS E tau E'       ==> WEAK_TRACE E epsilon E') /\
    (!E E' l. TRANS E (label l) E' ==> WEAK_TRACE E [l] E') /\
    (!E1 E2 E3 l1 l2.
              WEAK_TRACE E1 l1 E2 /\
              WEAK_TRACE E2 l2 E3 ==> WEAK_TRACE E1 (l1 ++ l2) E3)`;

(* Weak trace relation with single action, not recursive *)
val (EPS1_rules, EPS1_ind, EPS1_cases) = Hol_reln `
    (!E E'. TRANS E tau E' ==> EPS1 E E')`;

val EPS_def = Define `EPS = RTC EPS1`;

val (WEAK_TRANS_rules, WEAK_TRANS_ind, WEAK_TRANS_cases) = Hol_reln `
    (!E E' E1 E2 u. EPS E E1 /\ TRANS E1 u E2 /\ EPS E2 E' ==> WEAK_TRANS E u E')`;

val _ =
    add_rule { term_name = "WEAK_TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "==", HardSpace 0, TM, HardSpace 0, TOK "=>>",
			BreakSpace(1,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

(******************************************************************************)
(*                                                                            *)
(*                 Weak bisimulation and weak bisimularity                    *)
(*                                                                            *)
(******************************************************************************)

(* Define the weak bisimulation relation on CCS processes. *)
val WEAK_BISIM = new_definition ("WEAK_BISIM",
  ``WEAK_BISIM (Wbsm: CCS -> CCS -> bool) =
    (!E E'.
       Wbsm E E' ==>
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               (?E2. WEAK_TRANS E' (label l) E2 /\ Wbsm E1 E2)) /\
         (!E2. TRANS E' (label l) E2 ==>
               (?E1. WEAK_TRANS E  (label l) E1 /\ Wbsm E1 E2))) /\
       (!E1. TRANS E  tau E1 ==> (?E2. EPS E' E2 /\ Wbsm E1 E2)) /\
       (!E2. TRANS E' tau E2 ==> (?E1. EPS E  E1 /\ Wbsm E1 E2)))``);

(* An equivalent WEAK_EQUIV definition based on HOL's coinductive relation *)
val (WEAK_EQUIV_rules, WEAK_EQUIV_coind, WEAK_EQUIV_cases) = Hol_coreln `
    (!E E'.
       (!l.
         (!E1. TRANS E  (label l) E1 ==>
               (?E2. WEAK_TRANS E' (label l) E2 /\ WEAK_EQUIV E1 E2)) /\
         (!E2. TRANS E' (label l) E2 ==>
               (?E1. WEAK_TRANS E  (label l) E1 /\ WEAK_EQUIV E1 E2))) /\
       (!E1. TRANS E  tau E1 ==> (?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2)) /\
       (!E2. TRANS E' tau E2 ==> (?E1. EPS E  E1 /\ WEAK_EQUIV E1 E2))
      ==> WEAK_EQUIV E E')`;

(* "Weak bisimilarity is a weak bisimulation" *)
val WEAK_EQUIV_IS_WEAK_BISIM = store_thm (
   "WEAK_EQUIV_IS_WEAK_BISIM", ``WEAK_BISIM WEAK_EQUIV``,
    PURE_ONCE_REWRITE_TAC [WEAK_BISIM]
 >> REPEAT GEN_TAC
 >> DISCH_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM WEAK_EQUIV_cases]
 >> ASM_REWRITE_TAC []);

(* Alternative definition of WEAK_EQUIV, similar with STRONG_EQUIV (definition).
   "Weak bisimilarity contains all weak bisimulations (thus maximal)"
 *)
val WEAK_EQUIV = store_thm ("WEAK_EQUIV",
  ``!E E'. WEAK_EQUIV E E' = (?Wbsm. Wbsm E E' /\ WEAK_BISIM Wbsm)``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      EXISTS_TAC ``WEAK_EQUIV`` \\
      ASM_REWRITE_TAC [WEAK_EQUIV_IS_WEAK_BISIM],
      (* goal 2 (of 2) *)
      Q.SPEC_TAC (`E'`, `E'`) \\
      Q.SPEC_TAC (`E`, `E`) \\
      HO_MATCH_MP_TAC WEAK_EQUIV_coind \\ (* co-induction used here! *)
      METIS_TAC [WEAK_BISIM] ]);

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
			    tok = "~~~", term_name = "WEAK_EQUIV" };

val _ = Unicode.unicode_version { u = UTF8.chr 0x2248, tmnm = "WEAK_EQUIV"};
val _ = TeX_notation { hol = UTF8.chr 0x2248,
                       TeX = ("\\HOLTokenWeakEquiv", 1) };

(******************************************************************************)
(*                                                                            *)
(*                         Rooted weak bisimularity                           *)
(*                                                                            *)
(******************************************************************************)

(* Rooted weak bisimilarity (observation congruence) is based on WEAK_EQUIV *)
val OBS_CONGR = new_definition ("OBS_CONGR",
  ``OBS_CONGR E E' =
       (!u.
         (!E1. TRANS E u E1 ==>
               (?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2)) /\
         (!E2. TRANS E' u E2 ==>
               (?E1. WEAK_TRANS E  u E1 /\ WEAK_EQUIV E1 E2)))``);

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
			    tok = "~~c", term_name = "OBS_CONGR" };

val _ = Unicode.unicode_version { u = UTF8.chr 0x2248 ^ UTF8.chr 0x02B3, tmnm = "OBS_CONGR"};
val _ = TeX_notation { hol = UTF8.chr 0x2248 ^ UTF8.chr 0x02B3, (* double-tilde ^ r *)
                       TeX = ("\\HOLTokenRootedWeakEquiv", 1) };

val _ = export_theory ();
val _ = DB.html_theory "WeakEQ";

(* last updated: May 14, 2017 *)
