(* ========================================================================== *)
(* FILE          : pi_agentScript.sml                                         *)
(* DESCRIPTION   : Nominal type for process (agent) of pi-calculus            *)
(*                                                                            *)
(* Copyright 2025  The Australian National University (Author: Chun Tian)     *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

val _ = new_theory "pi_agent";

(* ----------------------------------------------------------------------
   Pi-calculus as a nominal datatype in HOL4

   HOL4 syntax ('free and 'bound are special type variables (alias of string)

   Nominal_datatype :

           name = Name string

           pi   = Nil                      (* 0 *)
                | Tau pi                   (* tau.P *)
                | Input name ''name pi     (* a(x).P *)
                | Output name name pi      (* {a}b.P *)
                | Match name name pi       (* [a == b] P *)
                | Mismatch name name pi    (* [a <> b] P *)
                | Sum pi pi                (* P + Q *)
                | Par pi pi                (* P | Q *)
                | Res ''name pi            (* nu x. P *)

       residual = TauR pi
                | InputS name ''name pi      (* Input *)
                | BoundOutput name ''name pi (* Bound output *)
                | FreeOutput name name pi    (* Free output *)
   End

   NOTE: Replication ("!") is not need so far.
   ---------------------------------------------------------------------- *)

val tyname0 = "name";
val tyname1 = "pi";
val tyname2 = "residual";

(* "Name" is under GVAR (of type 0); There's an extra "Var" under type 1 *)
val unit_t = “:unit”;
val u_tm = mk_var("u", unit_t);
val vp = “(\n ^u_tm. n = 0)”;

Datatype:
  repcode = rNil | rTau | rInput | rOutput | rMatch | rMismatch | rSum
          | rPar | rRes
          | rTauR | rInputS | rBoundOutput | rFreeOutput
End

(* type 0 = name; 1 = pi; 2 = residual *)
val rep_t = “:repcode”
val d_tm = mk_var("d", rep_t);
val lp =
  “(\n d tns uns.
     n = 1 /\ d = rNil ∧ tns = [] ∧ uns = [] \/
     n = 1 /\ d = rTau ∧ tns = [] /\ uns = [1] \/
     n = 1 /\ d = rInput ∧ tns = [1] /\ uns = [0] \/
     n = 1 /\ d = rOutput ∧ tns = [] /\ uns = [0; 0; 1] \/
     n = 1 /\ d = rMatch ∧ tns = [] /\ uns = [0; 0; 1] \/
     n = 1 /\ d = rMismatch ∧ tns = [] /\ uns = [0; 0; 1] \/
     n = 1 /\ d = rSum ∧ tns = [] /\ uns = [1; 1] \/
     n = 1 /\ d = rPar ∧ tns = [] /\ uns = [1; 1] \/
     n = 1 /\ d = rRes ∧ tns = [1] /\ uns = [] \/

     n = 2 /\ d = rTauR ∧ tns = [] ∧ uns = [1] \/
     n = 2 /\ d = rInputS ∧ tns = [1] /\ uns = [0] \/
     n = 2 /\ d = rBoundOutput ∧ tns = [1] /\ uns = [0] \/
     n = 2 /\ d = rFreeOutput ∧ tns = [] /\ uns = [0; 0; 1]
    )”;

(* This is often useful for debugging purposes *)
Overload LP = lp;

(* type 0 (:name) *)
val {term_ABS_pseudo11 = term_ABS_pseudo11_0,
     term_REP_11 = term_REP_11_0,
     genind_term_REP = genind_term_REP0,
     genind_exists = genind_exists0,
     termP = termP0,
     absrep_id = absrep_id0,
     repabs_pseudo_id = repabs_pseudo_id0,
     term_REP_t = term_REP_t0,
     term_ABS_t = term_ABS_t0,
     newty = newty0, ...} = new_type_step1 tyname0 0 [] {vp = vp, lp = lp};

(* type 1 (:pi) *)
val {term_ABS_pseudo11 = term_ABS_pseudo11_1,
     term_REP_11 = term_REP_11_1,
     genind_term_REP = genind_term_REP1,
     genind_exists = genind_exists1,
     termP = termP1,
     absrep_id = absrep_id1,
     repabs_pseudo_id = repabs_pseudo_id1,
     term_REP_t = term_REP_t1,
     term_ABS_t = term_ABS_t1,
     newty = newty1, ...} = new_type_step1 tyname1 1 [] {vp = vp, lp = lp};

(* type 2 (:residual) *)
val {term_ABS_pseudo11 = term_ABS_pseudo11_2,
     term_REP_11 = term_REP_11_2,
     genind_term_REP = genind_term_REP2,
     genind_exists = genind_exists2,
     termP = termP2,
     absrep_id = absrep_id2,
     repabs_pseudo_id = repabs_pseudo_id2,
     term_REP_t = term_REP_t2,
     term_ABS_t = term_ABS_t2,
     newty = newty2, ...} =
     new_type_step1 tyname2 2 [genind_exists0, genind_exists1] {vp = vp, lp = lp};

(* ----------------------------------------------------------------------
    Pi-calculus operators
   ---------------------------------------------------------------------- *)

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS;

Theorem GLAM_NIL_ELIM[local]:
  GLAM u bv [] ts = GLAM ARB bv [] ts
Proof
  simp[GLAM_NIL_EQ]
QED

(* "Name" of type 0 (:name) *)
val Name_t = mk_var("Name", “:string -> ^newty0”);
val Name_def = new_definition(
   "Name_def", “^Name_t s = ^term_ABS_t0 (GVAR s ())”);
val Name_termP = prove(
    mk_comb(termP0, Name_def |> SPEC_ALL |> concl |> rhs |> rand),
    srw_tac [][genind_rules]);
val Name_t = defined_const Name_def;

(* Nil *)
val Nil_t = mk_var("Nil", “:^newty1”);
val Nil_def = new_definition(
   "Nil_def",
  “^Nil_t = ^term_ABS_t1 (GLAM ARB rNil [] [])”);
val Nil_termP = prove(
   “^termP1 (GLAM x rNil [] [])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Nil_t = defined_const Nil_def;
val Nil_def' = prove(
  “^term_ABS_t1 (GLAM v rNil [] []) = ^Nil_t”,
    srw_tac [][Nil_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Nil_termP]);

(* Tau prefix *)
val Tau_t = mk_var("Tau", “:^newty1 -> ^newty1”);
val Tau_def = new_definition(
   "Tau_def",
  “^Tau_t P = ^term_ABS_t1 (GLAM ARB rTau [] [^term_REP_t1 P])”);
val Tau_termP = prove(
   “^termP1 (GLAM x rTau [] [^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Tau_t = defined_const Tau_def;
val Tau_def' = prove(
  “^term_ABS_t1 (GLAM v rTau [] [^term_REP_t1 P]) = ^Tau_t P”,
    srw_tac [][Tau_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Tau_termP]);

(* Input prefix *)
val Input_t = mk_var("Input", “:^newty0 -> string -> ^newty1 -> ^newty1”);
val Input_def = new_definition(
   "Input_def",
  “^Input_t a x P =
   ^term_ABS_t1 (GLAM x rInput [^term_REP_t1 P] [^term_REP_t0 a])”);
val Input_termP = prove(
    mk_comb(termP1, Input_def |> SPEC_ALL |> concl |> rhs |> rand),
    match_mp_tac glam >> srw_tac [][genind_term_REP0, genind_term_REP1]);
val Input_t = defined_const Input_def;

(* Output prefix *)
val Output_t = mk_var("Output", “:^newty0 -> ^newty0 -> ^newty1 -> ^newty1”);
val Output_def = new_definition(
   "Output_def",
  “^Output_t a b P =
   ^term_ABS_t1 (GLAM ARB rOutput [] [^term_REP_t0 a; ^term_REP_t0 b;
                                      ^term_REP_t1 P])”);
val Output_termP = prove(
   “^termP1
      (GLAM x rOutput [] [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP0,genind_term_REP1]);
val Output_t = defined_const Output_def;
val Output_def' = prove(
  “^term_ABS_t1
     (GLAM v rOutput [] [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P]) =
   ^Output_t a b P”,
  srw_tac [][Output_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Output_termP]);

(* Match *)
val Match_t = mk_var("Match", “:^newty0 -> ^newty0 -> ^newty1 -> ^newty1”);
val Match_def = new_definition(
   "Match_def",
  “^Match_t a b P =
   ^term_ABS_t1 (GLAM ARB rMatch [] [^term_REP_t0 a; ^term_REP_t0 b;
                                     ^term_REP_t1 P])”);
val Match_termP = prove(
  “^termP1 (GLAM x rMatch [] [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP0,genind_term_REP1]);
val Match_t = defined_const Match_def;
val Match_def' = prove(
  “^term_ABS_t1 (GLAM v rMatch [] [^term_REP_t0 a; ^term_REP_t0 b;
                                   ^term_REP_t1 P]) = ^Match_t a b P”,
    srw_tac [][Match_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Match_termP]);

(* Mismatch *)
val Mismatch_t = mk_var("Mismatch", “:^newty0 -> ^newty0 -> ^newty1 -> ^newty1”);
val Mismatch_def = new_definition(
   "Mismatch_def",
  “^Mismatch_t a b P =
   ^term_ABS_t1 (GLAM ARB rMismatch []
                          [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”);
val Mismatch_termP = prove(
   “^termP1 (GLAM x rMismatch []
                          [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP0,genind_term_REP1]);
val Mismatch_t = defined_const Mismatch_def;
val Mismatch_def' = prove(
  “^term_ABS_t1 (GLAM v rMismatch []
                          [^term_REP_t0 a;
                           ^term_REP_t0 b;
                           ^term_REP_t1 P]) = ^Mismatch_t a b P”,
    srw_tac [][Mismatch_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Mismatch_termP]);

(* Sum (Choice) *)
val Sum_t = mk_var("Sum", “:^newty1 -> ^newty1 -> ^newty1”);
val Sum_def = new_definition(
   "Sum_def",
  “^Sum_t P Q =
   ^term_ABS_t1 (GLAM ARB rSum [] [^term_REP_t1 P; ^term_REP_t1 Q])”);
val Sum_termP = prove(
   “^termP1 (GLAM x rSum [] [^term_REP_t1 P; ^term_REP_t1 Q])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Sum_t = defined_const Sum_def;
val Sum_def' = prove(
  “^term_ABS_t1 (GLAM v rSum [] [^term_REP_t1 P; ^term_REP_t1 Q]) = ^Sum_t P Q”,
    srw_tac [][Sum_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Sum_termP]);

(* Parallel Composition *)
val Par_t = mk_var("Par", “:^newty1 -> ^newty1 -> ^newty1”);
val Par_def = new_definition(
   "Par_def",
  “^Par_t P Q =
   ^term_ABS_t1 (GLAM ARB rPar [] [^term_REP_t1 P; ^term_REP_t1 Q])”);
val Par_termP = prove(
   “^termP1 (GLAM x rPar [] [^term_REP_t1 P; ^term_REP_t1 Q])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Par_t = defined_const Par_def;
val Par_def' = prove(
  “^term_ABS_t1 (GLAM v rPar [] [^term_REP_t1 P; ^term_REP_t1 Q]) = ^Par_t P Q”,
    srw_tac [][Par_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Par_termP]);

(* Restriction *)
val Res_t = mk_var("Res", “:string -> ^newty1 -> ^newty1”);
val Res_def = new_definition(
   "Res_def",
  “^Res_t v P =
   ^term_ABS_t1 (GLAM v rRes [^term_REP_t1 P] [])”);
val Res_tm = Res_def |> concl |> strip_forall |> snd |> rhs |> rand;
val Res_termP = prove(
    mk_comb (termP1, Res_tm),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Res_t = defined_const Res_def;

(* TauR *)
val TauR_t = mk_var("TauR", “:^newty1 -> ^newty2”);
val TauR_def = new_definition(
   "TauR_def",
  “^TauR_t P =
   ^term_ABS_t2 (GLAM ARB rTauR [] [^term_REP_t1 P])”);
val TauR_tm = TauR_def |> concl |> strip_forall |> snd |> rhs |> rand;
val TauR_termP = prove(
   “^termP2 (GLAM x rTauR [] [^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val TauR_t = defined_const TauR_def;
val TauR_def' = prove(
  “^term_ABS_t2 (GLAM v rTauR [] [^term_REP_t1 P]) = ^TauR_t P”,
    srw_tac [][TauR_def, GLAM_NIL_EQ, term_ABS_pseudo11_2, TauR_termP]);

(* Bound output (residual) *)
val BoundOutput_t =
    mk_var("BoundOutput", “:^newty0 -> string -> ^newty1 -> ^newty2”);
val BoundOutput_def = new_definition(
   "BoundOutput_def",
  “^BoundOutput_t a x P =
   ^term_ABS_t2 (GLAM x rBoundOutput [^term_REP_t1 P] [^term_REP_t0 a])”);
val BoundOutput_termP = prove(
    mk_comb(termP2, BoundOutput_def |> SPEC_ALL |> concl |> rhs |> rand),
    match_mp_tac glam >> srw_tac [][genind_term_REP0, genind_term_REP1]);
val BoundOutput_t = defined_const BoundOutput_def;

(* Input residual *)
val InputS_t = mk_var("InputS", “:^newty0 -> string -> ^newty1 -> ^newty2”);
val InputS_def = new_definition(
   "InputS_def",
  “^InputS_t a x P =
   ^term_ABS_t2 (GLAM x rInputS [^term_REP_t1 P] [^term_REP_t0 a])”);
val InputS_termP = prove(
    mk_comb(termP2, InputS_def |> SPEC_ALL |> concl |> rhs |> rand),
    match_mp_tac glam >> srw_tac [][genind_term_REP0, genind_term_REP1]);
val InputS_t = defined_const InputS_def;

(* Free output (residual) *)
val FreeOutput_t =
    mk_var("FreeOutput", “:^newty0 -> ^newty0 -> ^newty1 -> ^newty2”);
val FreeOutput_def = new_definition(
   "FreeOutput_def",
  “^FreeOutput_t a b P =
   ^term_ABS_t2 (GLAM ARB rFreeOutput []
                      [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”);
val FreeOutput_termP = prove(
   “^termP2 (GLAM x rFreeOutput
                    [] [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP0, genind_term_REP1]);
val FreeOutput_t = defined_const FreeOutput_def;
val FreeOutput_def' = prove(
  “^term_ABS_t2 (GLAM v rFreeOutput
                        [] [^term_REP_t0 a; ^term_REP_t0 b; ^term_REP_t1 P]) =
   ^FreeOutput_t a b P”,
    srw_tac [][FreeOutput_def, GLAM_NIL_EQ, term_ABS_pseudo11_2,
               FreeOutput_termP]);

(* ----------------------------------------------------------------------
    npm - permutation of pi-calculus names
   ---------------------------------------------------------------------- *)

val ncons_info = [{con_termP = Name_termP, con_def = Name_def}];
val npm_name_pfx = "n";

val {tpm_thm = npm_thm,
     term_REP_tpm = term_REP_npm,
     t_pmact_t = n_pmact_t,
     tpm_t = npm_t} =
    define_permutation {name_pfx = npm_name_pfx, name = tyname0,
                        term_REP_t = term_REP_t0,
                        term_ABS_t = term_ABS_t0,
                        absrep_id = absrep_id0,
                        repabs_pseudo_id = repabs_pseudo_id0,
                        cons_info = ncons_info,
                        newty = newty0,
                        genind_term_REP = genind_term_REP0};

Theorem npm_eqr :
    t = npm pi u <=> npm (REVERSE pi) t = (u :name)
Proof
    METIS_TAC [pmact_inverse]
QED

Theorem npm_eql :
    npm pi t = u <=> t = npm (REVERSE pi) (u :name)
Proof
    simp[npm_eqr]
QED

Theorem npm_CONS :
    npm ((x,y)::pi) (t :name) = npm [(x,y)] (npm pi t)
Proof
    SRW_TAC [][GSYM pmact_decompose]
QED

(* ----------------------------------------------------------------------
    tpm - permutation of pi-calculus binding variables
   ---------------------------------------------------------------------- *)

val cons_info =
    [{con_termP = Nil_termP,      con_def = SYM Nil_def'},
     {con_termP = Tau_termP,      con_def = SYM Tau_def'},
     {con_termP = Input_termP,    con_def = Input_def},
     {con_termP = Output_termP,   con_def = SYM Output_def'},
     {con_termP = Match_termP,    con_def = SYM Match_def'},
     {con_termP = Mismatch_termP, con_def = SYM Mismatch_def'},
     {con_termP = Sum_termP,      con_def = SYM Sum_def'},
     {con_termP = Par_termP,      con_def = SYM Par_def'},
     {con_termP = Res_termP,      con_def = Res_def}];

val tpm_name_pfx = "t";
val {tpm_thm, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation {name_pfx = tpm_name_pfx, name = tyname1,
                        term_REP_t = term_REP_t1,
                        term_ABS_t = term_ABS_t1,
                        absrep_id = absrep_id1,
                        repabs_pseudo_id = repabs_pseudo_id1,
                        cons_info = cons_info,
                        newty = newty1,
                        genind_term_REP = genind_term_REP1};

Theorem tpm_thm[allow_rebind] =
        tpm_thm |> REWRITE_RULE [GSYM term_REP_npm, GSYM Input_def, Output_def',
                                 Match_def', Mismatch_def'];

Theorem tpm_eqr :
    t = tpm pi u <=> tpm (REVERSE pi) t = (u :pi)
Proof
    METIS_TAC [pmact_inverse]
QED

Theorem tpm_eql :
    tpm pi t = u <=> t = tpm (REVERSE pi) (u :pi)
Proof
    simp[tpm_eqr]
QED

Theorem tpm_CONS :
    tpm ((x,y)::pi) (t :pi) = tpm [(x,y)] (tpm pi t)
Proof
    SRW_TAC [][GSYM pmact_decompose]
QED

(* ----------------------------------------------------------------------
    rpm - permutation of pi-calculus residuals
   ---------------------------------------------------------------------- *)

val rcons_info =
    [{con_termP = TauR_termP,        con_def = SYM TauR_def'},
     {con_termP = BoundOutput_termP, con_def = BoundOutput_def},
     {con_termP = InputS_termP,      con_def = InputS_def},
     {con_termP = FreeOutput_termP,  con_def = SYM FreeOutput_def'}];

val rpm_name_pfx = "r";

val {tpm_thm = rpm_thm,
     term_REP_tpm = term_REP_rpm,
     t_pmact_t = r_pmact_t,
     tpm_t = rpm_t} =
    define_permutation {name_pfx = rpm_name_pfx, name = tyname2,
                        term_REP_t = term_REP_t2,
                        term_ABS_t = term_ABS_t2,
                        absrep_id = absrep_id2,
                        repabs_pseudo_id = repabs_pseudo_id2,
                        cons_info = rcons_info,
                        newty = newty2,
                        genind_term_REP = genind_term_REP2};

Theorem rpm_thm[allow_rebind] =
        rpm_thm
     |> REWRITE_RULE [GSYM term_REP_npm, GSYM term_REP_tpm, TauR_def',
                      GSYM BoundOutput_def, GSYM InputS_def, FreeOutput_def']

Theorem rpm_eqr :
    t = rpm pi u <=> rpm (REVERSE pi) t = (u :residual)
Proof
    METIS_TAC [pmact_inverse]
QED

Theorem rpm_eql :
    rpm pi t = u <=> t = rpm (REVERSE pi) (u :residual)
Proof
    simp[rpm_eqr]
QED

Theorem rpm_CONS :
    rpm ((x,y)::pi) (t :residual) = rpm [(x,y)] (rpm pi t)
Proof
    SRW_TAC [][GSYM pmact_decompose]
QED

(* ----------------------------------------------------------------------
    support (supp) and FV (for type :name)
   ---------------------------------------------------------------------- *)

val name_REP_eqv = prove(
   “support (fn_pmact ^n_pmact_t gt_pmact) ^term_REP_t0 {}”,
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_npm, pmact_sing_inv]);

val supp_name_REP = prove(
   “supp (fn_pmact ^n_pmact_t gt_pmact) ^term_REP_t0 = {}”,
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][name_REP_eqv]);

val npm_def' =
    term_REP_npm |> AP_TERM term_ABS_t0 |> PURE_REWRITE_RULE [absrep_id0];

val t = mk_var("t", newty0);

val supp_npm_support = prove(
   “support ^n_pmact_t ^t (supp gt_pmact (^term_REP_t0 ^t))”,
    srw_tac [][support_def, npm_def', supp_fresh, absrep_id0]);

val supp_npm_apart = prove(
   “x IN supp gt_pmact (^term_REP_t0 ^t) /\ y NOTIN supp gt_pmact (^term_REP_t0 ^t)
    ==> ^npm_t [(x,y)] ^t <> ^t”,
    srw_tac [][npm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t0)
 >> srw_tac [][repabs_pseudo_id0, genind_gtpm_eqn, genind_term_REP0, supp_apart]);

val supp_npm = prove(
   “supp ^n_pmact_t ^t = supp gt_pmact (^term_REP_t0 ^t)”,
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supp_npm_support, supp_npm_apart, FINITE_GFV]);

val _ = overload_on ("FV", “supp ^n_pmact_t”);

val _ = set_fixity "#" (Infix(NONASSOC, 450));
val _ = overload_on ("#", “\v (P :name). v NOTIN FV P”);

Theorem FINITE_FV_name[simp] :
    FINITE (FV (n :name))
Proof
    srw_tac [][supp_npm, FINITE_GFV]
QED

Theorem FV_EMPTY_name :
    FV n = {} <=> !v. v NOTIN FV (n :name)
Proof
    SIMP_TAC (srw_ss()) [EXTENSION]
QED

fun nsupp_clause {con_termP, con_def} = let
  val t = mk_comb(“supp ^n_pmact_t”, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_npm, con_def, MATCH_MP repabs_pseudo_id0 con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_npm]
    |> GEN_ALL
end

Theorem FV_name_thm[simp] = LIST_CONJ (map nsupp_clause ncons_info)

Theorem FV_npm[simp] = “x IN FV (npm p (n :name))”
                       |> REWRITE_CONV [perm_supp, pmact_IN]
                       |> GEN_ALL

(* ----------------------------------------------------------------------
    support (supp) and FV (for type :pi)
   ---------------------------------------------------------------------- *)

val term_REP_eqv = prove(
   “support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t1 {}”,
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]);

val supp_term_REP = prove(
   “supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t1 = {}”,
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][term_REP_eqv]);

val tpm_def' =
    term_REP_tpm |> AP_TERM term_ABS_t1 |> PURE_REWRITE_RULE [absrep_id1];

val t = mk_var("t", newty1);

val supp_tpm_support = prove(
   “support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t1 ^t))”,
    srw_tac [][support_def, tpm_def', supp_fresh, absrep_id1]);

val supp_tpm_apart = prove(
   “x IN supp gt_pmact (^term_REP_t1 ^t) /\ y NOTIN supp gt_pmact (^term_REP_t1 ^t)
    ==> ^tpm_t [(x,y)] ^t <> ^t”,
    srw_tac [][tpm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t1)
 >> srw_tac [][repabs_pseudo_id1, genind_gtpm_eqn, genind_term_REP1, supp_apart]);

val supp_tpm = prove(
   “supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t1 ^t)”,
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supp_tpm_support, supp_tpm_apart, FINITE_GFV]);

val _ = overload_on ("FV", “supp ^t_pmact_t”);
val _ = overload_on ("#", “\v (P :pi). v NOTIN FV P”);

Theorem FINITE_FV[simp] :
    FINITE (FV (t :pi))
Proof
    srw_tac [][supp_tpm, FINITE_GFV]
QED

Theorem FV_EMPTY :
    FV t = {} <=> !v. v NOTIN FV (t :pi)
Proof
    SIMP_TAC (srw_ss()) [EXTENSION]
QED

fun supp_clause {con_termP, con_def} = let
  val t = mk_comb(“supp ^t_pmact_t”, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id1 con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm, GSYM supp_npm]
    |> GEN_ALL
end

Theorem FV_thm[simp] = LIST_CONJ (map supp_clause cons_info)

Theorem FV_tpm[simp] = “x IN FV (tpm p (t :pi))”
                       |> REWRITE_CONV [perm_supp, pmact_IN]
                       |> GEN_ALL

(* ----------------------------------------------------------------------
    support (supp) and FV (for type :residual)
   ---------------------------------------------------------------------- *)

val residual_REP_eqv = prove(
   “support (fn_pmact ^r_pmact_t gt_pmact) ^term_REP_t2 {}”,
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_rpm, pmact_sing_inv]);

val supp_residual_REP = prove(
   “supp (fn_pmact ^r_pmact_t gt_pmact) ^term_REP_t2 = {}”,
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][residual_REP_eqv]);

val rpm_def' =
    term_REP_rpm |> AP_TERM term_ABS_t2 |> PURE_REWRITE_RULE [absrep_id2];

val t = mk_var("t", newty2);

val supp_rpm_support = prove(
   “support ^r_pmact_t ^t (supp gt_pmact (^term_REP_t2 ^t))”,
    srw_tac [][support_def, rpm_def', supp_fresh, absrep_id2]);

val supp_rpm_apart = prove(
   “x IN supp gt_pmact (^term_REP_t2 ^t) /\ y NOTIN supp gt_pmact (^term_REP_t2 ^t)
    ==> ^rpm_t [(x,y)] ^t <> ^t”,
    srw_tac [][rpm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t2)
 >> srw_tac [][repabs_pseudo_id2, genind_gtpm_eqn, genind_term_REP2, supp_apart]);

val supp_rpm = prove(
   “supp ^r_pmact_t ^t = supp gt_pmact (^term_REP_t2 ^t)”,
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supp_rpm_support, supp_rpm_apart, FINITE_GFV]);

val _ = overload_on ("FV", “supp ^r_pmact_t”);
val _ = overload_on ("#", “\v (P :residual). v NOTIN FV P”);

Theorem FINITE_FV_residual[simp] :
    FINITE (FV (t :residual))
Proof
    srw_tac [][supp_rpm, FINITE_GFV]
QED

Theorem FV_EMPTY_residual :
    FV t = {} <=> !v. v NOTIN FV (t :residual)
Proof
    SIMP_TAC (srw_ss()) [EXTENSION]
QED

fun rsupp_clause {con_termP, con_def} = let
  val t = mk_comb(“supp ^r_pmact_t”, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_rpm, con_def, MATCH_MP repabs_pseudo_id2 con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm, GSYM supp_npm]
    |> GEN_ALL
end

Theorem FV_residual_thm[simp] = LIST_CONJ (map rsupp_clause rcons_info)

Theorem FV_rpm[simp] = “x IN FV (rpm p (t :residual))”
                       |> REWRITE_CONV [perm_supp, pmact_IN]
                       |> GEN_ALL

(* ----------------------------------------------------------------------
    term induction
   ---------------------------------------------------------------------- *)

fun genit th = let
  val (_, args) = strip_comb (concl th)
  val (tm, x) = case args of [x,y] => (x,y) | _ => raise Fail "Bind"
  val ty = type_of tm
  val t = mk_var("t", ty)
in
  th |> INST [tm |-> t] |> GEN x |> GEN t
end

val LIST_REL_CONS1 = listTheory.LIST_REL_CONS1;
val LIST_REL_NIL = listTheory.LIST_REL_NIL;

val term_ind =
    bvc_genind
        |> INST_TYPE [alpha |-> rep_t, beta |-> unit_t]
        |> Q.INST [‘vp’ |-> ‘^vp’, ‘lp’ |-> ‘^lp’]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPECL [‘\n t0 x. n = 1 ==> Q t0 x’, ‘fv’]
        |> UNDISCH |> Q.SPEC ‘1’ |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists0,
                      genind_exists1,
                      genind_exists2,
                      LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [‘Q’ |-> ‘\t. P (^term_ABS_t1 t)’]
        |> SIMP_RULE std_ss [absrep_id1,
                             GSYM Name_def,
                             Nil_def', Tau_def', GSYM Input_def,
                             Output_def', Match_def', Mismatch_def',
                             Sum_def', Par_def', GSYM Res_def]
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, GSYM supp_npm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                  [ASSUME “!x:'c. FINITE (fv x:string set)”]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GENL [‘P’, ‘fv’];

fun mkX_ind th = th |> Q.SPECL [‘\t x. Q t’, ‘\x. X’]
                    |> SIMP_RULE std_ss [] |> Q.GEN ‘X’
                    |> Q.INST [‘Q’ |-> ‘P’] |> Q.GEN ‘P’;

(* NOTE: not recommended unless in generated theorems *)
Theorem nc_INDUCTION[local] = mkX_ind term_ind

(* The recommended induction theorem containing correctly namedbinding variables. *)
Theorem nc_INDUCTION2 :
    !P X.
        P Nil /\ (!E. P E ==> P (Tau E)) /\
        (!a x E. P E /\ x NOTIN X /\ x # a ==> P (Input a x E)) /\
        (!a b E. P E ==> P (Output a b E)) /\
        (!a b E. P E ==> P (Match a b E)) /\
        (!a b E. P E ==> P (Mismatch a b E)) /\
        (!E E'. P E /\ P E' ==> P (Sum E E')) /\
        (!E E'. P E /\ P E' ==> P (Par E E')) /\
        (!x E. P E /\ x NOTIN X ==> P (Res x E)) /\ FINITE X ==> !E. P E
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘X’ >> rw []
QED

(* |- !P. P Nil /\ (!E. P E ==> P (Tau E)) /\
          (!a x E. P E /\ x # a ==> P (Input a x E)) /\
          (!a b E. P E ==> P (Output a b E)) /\
          (!a b E. P E ==> P (Match a b E)) /\
          (!a b E. P E ==> P (Mismatch a b E)) /\
          (!E E'. P E /\ P E' ==> P (Sum E E')) /\
          (!E E'. P E /\ P E' ==> P (Par E E')) /\
          (!y E. P E ==> P (Res y E)) ==>
          !E. P E
 *)
Theorem simple_induction =
    nc_INDUCTION2 |> Q.SPECL [‘P’, ‘{}’]
                  |> REWRITE_RULE [FINITE_EMPTY, NOT_IN_EMPTY]
                  |> Q.GEN ‘P’

(* |- !u v t1 t2.
        Res u t1 = Res v t2 <=>
        u = v /\ t1 = t2 \/ u <> v /\ u # t2 /\ t1 = tpm [(u,v)] t2
 *)
Theorem Res_eq_thm =
  “(Res u t1 = Res v t2 :pi)”
     |> SIMP_CONV (srw_ss()) [Res_def, Res_termP, term_ABS_pseudo11_1,
                              GLAM_eq_thm, term_REP_11_1, GSYM term_REP_tpm,
                              GSYM supp_tpm]
     |> Q.GENL [‘u’, ‘v’, ‘t1’, ‘t2’]

Theorem Res_tpm_ALPHA :
    v # (u :pi) ==> Res x u = Res v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][Res_eq_thm, pmact_flip_args]
QED

(* |- !a b x y t1 t2.
        Input a x t1 = Input b y t2 <=>
        x = y /\ t1 = t2 /\ a = b \/
        x <> y /\ x # t2 /\ t1 = tpm [(x,y)] t2 /\ a = b
 *)
Theorem Input_eq_thm =
  “Input a x t1 = Input b y (t2 :pi)”
     |> SIMP_CONV (srw_ss()) [Input_def, Input_termP, term_ABS_pseudo11_1,
                              GLAM_eq_thm, term_REP_11_0, term_REP_11_1,
                              GSYM term_REP_tpm, GSYM supp_tpm]
     |> Q.GENL [‘a’, ‘b’, ‘x’, ‘y’, ‘t1’, ‘t2’]

Theorem Input_tpm_ALPHA :
    v # (u :pi) ==> Input a x u = Input a v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][Input_eq_thm, pmact_flip_args]
QED

(* |- !a b x y t1 t2.
        InputS a x t1 = InputS b y t2 <=>
        x = y /\ t1 = t2 /\ a = b \/
        x <> y /\ x # t2 /\ t1 = tpm [(x,y)] t2 /\ a = b
 *)
Theorem InputS_eq_thm =
  “InputS a x t1 = InputS b y (t2 :pi)”
     |> SIMP_CONV (srw_ss()) [InputS_def, InputS_termP, term_ABS_pseudo11_2,
                              GLAM_eq_thm,
                              term_REP_11_0, term_REP_11_1, term_REP_11_2,
                              GSYM term_REP_tpm, GSYM term_REP_rpm,
                              GSYM supp_tpm, GSYM supp_rpm]
     |> Q.GENL [‘a’, ‘b’, ‘x’, ‘y’, ‘t1’, ‘t2’]

Theorem InputS_tpm_ALPHA :
    v # (u :pi) ==> InputS a x u = InputS a v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][InputS_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    term recursion
   ---------------------------------------------------------------------- *)

(* NOTE: all 3 types have the same repty *)
val (_, repty) = dom_rng (type_of term_REP_t0);
val repty' = ty_antiq repty;

val termP_elim0 = prove(
   “(!g. ^termP0 g ==> P g) <=> (!t. P (^term_REP_t0 t))”,
    srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP0]
 >> first_x_assum (qspec_then ‘^term_ABS_t0 g’ mp_tac)
 >> srw_tac [][repabs_pseudo_id0]);

val termP_removal0 =
    nomdatatype.termP_removal {
      elimth = termP_elim0, absrep_id = absrep_id0,
      tpm_def = AP_TERM term_ABS_t0 term_REP_npm |> REWRITE_RULE [absrep_id0],
      termP = termP0, repty = repty};

val termP_elim1 = prove(
   “(!g. ^termP1 g ==> P g) <=> (!t. P (^term_REP_t1 t))”,
    srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP1]
 >> first_x_assum (qspec_then ‘^term_ABS_t1 g’ mp_tac)
 >> srw_tac [][repabs_pseudo_id1]);

val termP_removal1 =
    nomdatatype.termP_removal {
      elimth = termP_elim1, absrep_id = absrep_id1,
      tpm_def = AP_TERM term_ABS_t1 term_REP_tpm |> REWRITE_RULE [absrep_id1],
      termP = termP1, repty = repty};

val termP_elim2 = prove(
   “(!g. ^termP2 g ==> P g) <=> (!t. P (^term_REP_t2 t))”,
    srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP2]
 >> first_x_assum (qspec_then ‘^term_ABS_t2 g’ mp_tac)
 >> srw_tac [][repabs_pseudo_id2]);

val termP_removal2 =
    nomdatatype.termP_removal {
      elimth = termP_elim2, absrep_id = absrep_id2,
      tpm_def = AP_TERM term_ABS_t2 term_REP_rpm |> REWRITE_RULE [absrep_id2],
      termP = termP2, repty = repty};

val termP' = prove(
   “genind ^vp ^lp n t <=>
      ^termP0 t /\ n = 0 \/
      ^termP1 t /\ n = 1 \/
      ^termP2 t /\ n = 2”,
    EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac >> rw []
 >> qsuff_tac ‘n = 0 \/ n = 1 \/ n = 2’ >- (strip_tac >> srw_tac [][])
 >> pop_assum mp_tac
 >> Q.ISPEC_THEN ‘t’ STRUCT_CASES_TAC gterm_cases
 >> srw_tac [][genind_GVAR, genind_GLAM_eqn]);

(* “tvf :string -> 'q -> 'r” *)
val tvf = “λ(s :string) (u :unit) (p :'q). tvf s p :'r”; (* Name *)

(* Type of constants (all constructors are included) occurring in tlf:

   Nil:    “tnf :('q -> 'r)”
   Tau:    “ttf :('q -> 'r) -> pi -> ('q -> 'r)”
   Input:  “tif :('q -> 'r) -> string -> ('q -> 'r) ->
                 name -> pi -> ('q -> 'r)”
   Output: “tof :('q -> 'r) -> ('q -> 'r) -> ('q -> 'r) ->
                 name -> name -> pi -> ('q -> 'r)”
   Match:  “tmf :('q -> 'r) -> ('q -> 'r) -> ('q -> 'r) ->
                 name -> name -> pi -> ('q -> 'r)”
   Mismatch: “tuf :('q -> 'r) -> ('q -> 'r) -> ('q -> 'r) ->
                   name -> name -> pi -> ('q -> 'r)”
   Sum:    “tsf :('q -> 'r) -> ('q -> 'r) -> pi -> pi -> ('q -> 'r)”
   Par:    “tpf :('q -> 'r) -> ('q -> 'r) -> pi -> pi -> ('q -> 'r)”
   Res:    “tcf :string -> ('q -> 'r) -> pi -> ('q -> 'r)”

   TauR:        “taf :('q -> 'r) -> pi -> ('q -> 'r)”
   InputS:      “trf :('q -> 'r) -> string -> ('q -> 'r) ->
                      name -> pi -> ('q -> 'r)”
   BoundOutput: “tbf :('q -> 'r) -> string -> ('q -> 'r) ->
                      name -> pi -> ('q -> 'r)”
   FreeOutput:  “tff :('q -> 'r) -> ('q -> 'r) -> ('q -> 'r) ->
                      name -> name -> pi -> ('q -> 'r)”

   NOTE: ds1 is the list of (bounded) recursive parameters as functions ('q -> 'r).
         ts1 is the list of (bounded) actual arguments in the same position.
         ds2 is the list of (unbounded) recursive parameters as functions ('q -> 'r).
         ts2 is the list of (unbounded) actual arguments in the same position.
         non-recursive parameters are taken from the corresponding position of u.
        "if conditions" identify the constructor.
         v is the only binding variable.
 *)
val u_tm = mk_var("u", rep_t);

(* tlf's ty :string ->
             'a ->
             ('q -> 'c) list ->
             ('q -> 'c) list ->
             ('a, 'b) gterm list -> ('a, 'b) gterm list -> 'q -> 'c)
 *)
val tlf =
   “λ(v :string) ^u_tm (ds1 :('q -> 'r) list) (ds2 :('q -> 'r) list)
                       (ts1 :^repty' list) (ts2 :^repty' list) (p :'q).
      case u of
        rNil => tnf p : 'r
      | rTau => ttf (HD ds2) (^term_ABS_t1 (HD ts2)) p :'r
      | rInput => tif (HD ds2) v (HD ds1)
                      (^term_ABS_t0 (HD ts2)) (^term_ABS_t1 (HD ts1)) p :'r
      | rOutput => tof (HD ds2) (HD (TL ds2)) (HD (TL (TL ds2)))
                       (^term_ABS_t0 (HD ts2))
                       (^term_ABS_t0 (HD (TL ts2)))
                       (^term_ABS_t1 (HD (TL (TL ts2)))) p :'r
      | rMatch => tmf (HD ds2) (HD (TL ds2)) (HD (TL (TL ds2)))
                      (^term_ABS_t0 (HD ts2))
                      (^term_ABS_t0 (HD (TL ts2)))
                      (^term_ABS_t1 (HD (TL (TL ts2)))) p :'r
      | rMismatch => tuf (HD ds2) (HD (TL ds2)) (HD (TL (TL ds2)))
                         (^term_ABS_t0 (HD ts2))
                         (^term_ABS_t0 (HD (TL ts2)))
                         (^term_ABS_t1 (HD (TL (TL ts2)))) p :'r
      | rSum => tsf (HD ds2) (HD (TL ds2))
                    (^term_ABS_t1 (HD ts2))
                    (^term_ABS_t1 (HD (TL ts2))) p :'r
      | rPar => tpf (HD ds2) (HD (TL ds2))
                    (^term_ABS_t1 (HD ts2))
                    (^term_ABS_t1 (HD (TL ts2))) p :'r
      | rRes => tcf v (HD ds1) (^term_ABS_t1 (HD ts1)) p :'r
      | rTauR => taf (HD ds2) (^term_ABS_t1 (HD ts2)) p :'r
      | rInputS => trf (HD ds2) v (HD ds1)
                       (^term_ABS_t0 (HD ts2)) (^term_ABS_t1 (HD ts1)) p :'r
      | rBoundOutput =>
          tbf (HD ds2) v (HD ds1)
              (^term_ABS_t0 (HD ts2)) (^term_ABS_t1 (HD ts1)) p :'r
      | rFreeOutput => tof (HD ds2) (HD (TL ds2)) (HD (TL (TL ds2)))
                           (^term_ABS_t0 (HD ts2))
                           (^term_ABS_t0 (HD (TL ts2)))
                           (^term_ABS_t1 (HD (TL (TL ts2)))) p :'r”;

Overload TLF = tlf

val FN = mk_var("FN", “:(repcode,unit) gterm -> ρ -> 'r”)
val fn0_def_t = “fn0 = λn. ^FN (name_REP n)”
val fn1_def_t = “fn1 = λp. ^FN (pi_REP p)”
val fn2_def_t = “fn2 = λr. ^FN (residual_REP r)”

val testcase = [(fn0_def_t, repabs_pseudo_id0, [Name_def]),
                (fn1_def_t, repabs_pseudo_id1,
                 [SYM Nil_def', Input_def, SYM Output_def', SYM Tau_def',
                  SYM Match_def', SYM Mismatch_def', SYM Sum_def', SYM Par_def',
                  Res_def]),
                (fn2_def_t, repabs_pseudo_id2,
                 [InputS_def, SYM FreeOutput_def', BoundOutput_def,
                  SYM TauR_def'])]

fun case1 (tm_def, repabs, defs) =
  let
    val c = lhs tm_def

    fun def1 d =
        let
          val (_, eq) = strip_forall (concl d)
          val tactic =
            ASSUME_TAC d >>
            asm_simp_tac bool_ss [GLAM_NIL_ELIM] >> AP_TERM_TAC >>
            SYM_TAC >> MATCH_MP_TAC repabs >>
            simp_tac bool_ss [genind_GLAM_eqn, genind_GVAR,
                              TypeBase.distinct_of “:repcode”,
                              LIST_REL_NIL, LIST_REL_CONS1, PULL_EXISTS,
                              CONS_11, genind_term_REP1, genind_term_REP0,
                              genind_term_REP2]
          val goal =
                mk_eq (mk_comb(FN, rand (rhs eq)), mk_comb (c, lhs eq))
        in
          TAC_PROOF(([tm_def], goal), tactic)
        end
  in
    map def1 defs
  end

val fn_rewrites = map case1 testcase

Theorem parameter_tm_recursion0 =
  parameter_gtm_recursion
      |> INST_TYPE [alpha |-> rep_t, beta |-> unit_t, gamma |-> “:'r”]
      |> Q.INST [‘lf’ |-> ‘^tlf’, ‘vf’ |-> ‘^tvf’, ‘vp’ |-> ‘^vp’,
                 ‘lp’ |-> ‘^lp’]
      |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                               GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                               GSYM RIGHT_EXISTS_AND_THM,
                               GSYM LEFT_EXISTS_AND_THM,
                               GSYM LEFT_FORALL_IMP_THM,
                               LIST_REL_CONS1, genind_GVAR,
                               genind_GLAM_eqn, sidecond_def,
                               NEWFCB_def, relsupp_def,
                               LENGTH_NIL_SYM, LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP']
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2, LENGTH_NIL]
      |> CONV_RULE (DEPTH_CONV termP_removal0)
      |> CONV_RULE (DEPTH_CONV termP_removal1)
      |> CONV_RULE (DEPTH_CONV termP_removal2)
      |> SIMP_RULE (srw_ss()) [GSYM supp_npm, SYM term_REP_npm,
                               GSYM supp_tpm, SYM term_REP_tpm,
                               GSYM supp_rpm, SYM term_REP_rpm]
      |> UNDISCH
      |> rpt_hyp_dest_conj

val rwt0 =
  EQ_MP (SCONV [Once FUN_EQ_THM] fn0_def_t) (ASSUME fn0_def_t) |> GSYM
val rwt1 =
  EQ_MP (SCONV [Once FUN_EQ_THM] fn1_def_t) (ASSUME fn1_def_t) |> GSYM
val rwt2 =
  EQ_MP (SCONV [Once FUN_EQ_THM] fn2_def_t) (ASSUME fn2_def_t) |> GSYM

val (exv, body) = dest_exists (concl parameter_tm_recursion0)
val cs = CONJUNCTS (ASSUME (body |> subst[exv |-> FN]))


val cs' = map (SIMP_RULE bool_ss (rwt0:: rwt1:: rwt2:: GLAM_NIL_ELIM ::
                                  List.concat fn_rewrites)) cs

val th0 = LIST_CONJ cs'
val eqns = List.filter is_eq (hyp th0)
val th1 = itlist Prim_rec.EXISTS_EQUATION eqns th0
val th = CHOOSE (FN, parameter_tm_recursion0) th1

th |> DISCH_ALL |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                          [ASSUME “FINITE (A:string set)”,
                                            ASSUME “∀p:'q. FINITE (supp ppm p)”]
   |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST [‘tvf’ |-> ‘vr’, (* Name? *)
                 ‘tnf’ |-> ‘f0’, (* Nil *)
                 ‘ttf’ |-> ‘f1’, (* Tau *)
                 ‘tif’ |-> ‘f2’, (* Input *)
                 ‘tof’ |-> ‘f3’, (* Output *)
                 ‘tmf’ |-> ‘f4’, (* Match *)
                 ‘tuf’ |-> ‘f5’, (* Mismatch *)
                 ‘tsf’ |-> ‘f6’, (* Sum *)
                 ‘tpf’ |-> ‘f7’, (* Par *)
                 ‘trf’ |-> ‘f8’, (* Res *)
                 ‘dpm’ |-> ‘apm’]
      |> CONV_RULE (REDEPTH_CONV sort_uvars)

(* use Prim_rec.EXISTS_EQUATION to eliminate "definitions" of fn0, fn1, fn2 *)

(*
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id2,
                          term_REP_t = term_REP_t2,
                          cons_info = rcons_info}
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id1,
                          term_REP_t = term_REP_t1,
                          cons_info = cons_info}
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id0,
                          term_REP_t = term_REP_t0,
                          cons_info = ncons_info}
      |> DISCH_ALL
      |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                [ASSUME ``FINITE (A:string set)``,
                                 ASSUME ``!p :'q. FINITE (supp ppm p)``]
      |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST [‘tvf’ |-> ‘vr’, (* Name? *)
                 ‘tnf’ |-> ‘f0’, (* Nil *)
                 ‘ttf’ |-> ‘f1’, (* Tau *)
                 ‘tif’ |-> ‘f2’, (* Input *)
                 ‘tof’ |-> ‘f3’, (* Output *)
                 ‘tmf’ |-> ‘f4’, (* Match *)
                 ‘tuf’ |-> ‘f5’, (* Mismatch *)
                 ‘tsf’ |-> ‘f6’, (* Sum *)
                 ‘tpf’ |-> ‘f7’, (* Par *)
                 ‘trf’ |-> ‘f8’, (* Res *)
                 ‘dpm’ |-> ‘apm’]
      |> CONV_RULE (REDEPTH_CONV sort_uvars)

Theorem tm_recursion =
  parameter_tm_recursion
      |> Q.INST_TYPE [‘:'q’ |-> ‘:unit’]
      |> Q.INST [‘ppm’ |-> ‘discrete_pmact’,
                  ‘vr’ |-> ‘\s u. vru s’,
                  ‘pf’ |-> ‘\r a t u. pfu (r()) a t’,
                  ‘sm’ |-> ‘\r1 r2 t1 t2 u. smu (r1()) (r2()) t1 t2’,
                  ‘pr’ |-> ‘\r1 r2 t1 t2 u. pru (r1()) (r2()) t1 t2’,
                  ‘rs’ |-> ‘\r L t u. rsu (r()) L t’,
                  ‘rl’ |-> ‘\r t rf u. rlu (r()) t rf’,
                  ‘re’ |-> ‘\r v t u. reu (r()) v t’]
      |> SIMP_RULE (srw_ss()) [oneTheory.FORALL_ONE, oneTheory.FORALL_ONE_FN,
                               oneTheory.EXISTS_ONE_FN, fnpm_def]
      |> SIMP_RULE (srw_ss() ++ CONJ_ss) [supp_unitfn]
      |> Q.INST [‘vru’ |-> ‘vr’,
                 ‘pfu’ |-> ‘pf’,
                 ‘smu’ |-> ‘sm’,
                 ‘pru’ |-> ‘pr’,
                 ‘rsu’ |-> ‘rs’,
                 ‘rlu’ |-> ‘rl’,
                 ‘reu’ |-> ‘re’]
*)
val _ = export_theory ();
val _ = html_theory "pi_agent";
