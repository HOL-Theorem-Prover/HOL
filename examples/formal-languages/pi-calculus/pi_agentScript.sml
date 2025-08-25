(* ========================================================================== *)
(* FILE          : pi_agentScript.sml                                         *)
(* DESCRIPTION   : Nominal type for process (agent) of pi-calculus            *)
(*                                                                            *)
(* Copyright 2025  Michael Norrish and Chun Tian                              *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory listTheory listLib hurdUtils;

open basic_swapTheory generic_termsTheory binderLib nomsetTheory nomdatatype;

(* only for its syntax of SUB *)
local open termTheory in end;

val _ = new_theory "pi_agent";

(* ----------------------------------------------------------------------
   Pi-calculus as a nominal datatype in HOL4

   HOL4 syntax ('free and 'bound are special type variables (alias of string)

   Nominal_datatype :

           pi   = Nil                      (* 0 *)
                | Tau pi                   (* tau.P *)
                | Input 'free 'bound pi    (* a(x).P *)
                | Output 'free 'free pi    (* {a}b.P *)
                | Match 'free 'free pi     (* [a == b] P *)
                | Mismatch 'free 'free pi  (* [a <> b] P *)
                | Sum pi pi                (* P + Q *)
                | Par pi pi                (* P | Q *)
                | Res 'bound pi            (* nu x. P *)

       residual = TauR pi
                | InputS 'free 'bound pi      (* Input *)
                | BoundOutput 'free 'bound pi (* Bound output *)
                | FreeOutput 'free 'free pi   (* Free output *)
   End

   NOTE: Replication ("!") is not needed so far, but can be supported later.
   ---------------------------------------------------------------------- *)

Datatype:
  repcode = rNil | rTau | rInput | rOutput | rMatch | rMismatch | rSum
          | rPar | rRes
          | rTauR | rInputS | rBoundOutput | rFreeOutput
End

val tyname1 = "pi";
val tyname2 = "residual";

(* type 0 = name; 1 = pi; 2 = residual *)
val rep_t = “:repcode”
val d_tm = mk_var("d", rep_t);
val lp =
  “(\n lfvs d tns uns.
     n = 1 /\ lfvs = 0 /\ d = rNil ∧ tns = [] ∧ uns = [] \/
     n = 1 /\ lfvs = 0 /\ d = rTau ∧ tns = [] /\ uns = [1] \/
     n = 1 /\ lfvs = 1 /\ d = rInput ∧ tns = [1] /\ uns = [] \/
     n = 1 /\ lfvs = 2 /\ d = rOutput ∧ tns = [] /\ uns = [1] \/
     n = 1 /\ lfvs = 2 /\ d = rMatch ∧ tns = [] /\ uns = [1] \/
     n = 1 /\ lfvs = 2 /\ d = rMismatch ∧ tns = [] /\ uns = [1] \/
     n = 1 /\ lfvs = 0 /\ d = rSum ∧ tns = [] /\ uns = [1; 1] \/
     n = 1 /\ lfvs = 0 /\ d = rPar ∧ tns = [] /\ uns = [1; 1] \/
     n = 1 /\ lfvs = 0 /\ d = rRes ∧ tns = [1] /\ uns = [] \/

     n = 2 /\ lfvs = 0 /\ d = rTauR ∧ tns = [] ∧ uns = [1] \/
     n = 2 /\ lfvs = 1 /\ d = rInputS ∧ tns = [1] /\ uns = [] \/
     n = 2 /\ lfvs = 1 /\ d = rBoundOutput ∧ tns = [1] /\ uns = [] \/
     n = 2 /\ lfvs = 2 /\ d = rFreeOutput ∧ tns = [] /\ uns = [1]
    )”;

(* This is often useful for debugging purposes *)
Overload LP = lp;

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
     newty = newty1, ...} = new_type_step1 tyname1 1 [] {lp = lp};

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
     new_type_step1 tyname2 2 [genind_exists1] {lp = lp};

(* ----------------------------------------------------------------------
    Pi-calculus operators
   ---------------------------------------------------------------------- *)

val glam = genind_lam
Overload pilp[local] = “genind ^lp”
fun toArb t = subst [“uu:string” |-> “ARB:string”] t

(* Nil *)
val Nil_t = mk_var("Nil", “:^newty1”);
val Nil_pattern = “GLAM uu [] rNil [][]”;
val Nil_def = new_definition(
   "Nil_def",
  “^Nil_t = ^term_ABS_t1 ^(toArb Nil_pattern)”);
val Nil_termP = prove(
    mk_comb(termP1, Nil_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Nil_t = defined_const Nil_def;
val Nil_def' = prove(
  “^term_ABS_t1 ^Nil_pattern = ^Nil_t”,
    srw_tac [][Nil_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Nil_termP]);

(* Tau prefix *)
val Tau_t = mk_var("Tau", “:^newty1 -> ^newty1”);
val Tau_pattern = “GLAM uu [] rTau [] [^term_REP_t1 P]”;
val Tau_def = new_definition(
   "Tau_def",
  “^Tau_t P = ^term_ABS_t1 ^(toArb Tau_pattern)”);
val Tau_termP = prove(
    mk_comb(termP1, Tau_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Tau_t = defined_const Tau_def;
val Tau_def' = prove(
  “^term_ABS_t1 ^Tau_pattern = ^Tau_t P”,
    srw_tac [][Tau_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Tau_termP]);

(* Input prefix *)
val Input_t = mk_var("Input", “:string -> string -> ^newty1 -> ^newty1”);
val Input_pattern = “GLAM x [a] rInput [^term_REP_t1 P] []”;
val Input_def = new_definition(
   "Input_def",
  “^Input_t a x P = ^term_ABS_t1 ^Input_pattern”);
val Input_termP = prove(
    mk_comb(termP1, Input_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Input_t = defined_const Input_def;

(* Output prefix *)
val Output_t = mk_var("Output", “:string -> string -> ^newty1 -> ^newty1”);
val Output_pattern = “GLAM uu [a; b] rOutput [] [^term_REP_t1 P]”;
val Output_def = new_definition(
   "Output_def",
  “^Output_t a b P = ^term_ABS_t1 ^(toArb Output_pattern)”);
val Output_termP = prove(
    mk_comb(termP1, Output_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Output_t = defined_const Output_def;
val Output_def' = prove(
  “^term_ABS_t1 ^Output_pattern = ^Output_t a b P”,
    srw_tac [][Output_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Output_termP]);

(* Match *)
val Match_t = mk_var("Match", “:string -> string -> ^newty1 -> ^newty1”);
val Match_pattern = “GLAM uu [a; b] rMatch [] [^term_REP_t1 P]”;
val Match_def = new_definition(
   "Match_def",
  “^Match_t a b P = ^term_ABS_t1 ^(toArb Match_pattern)”);
val Match_termP = prove(
    mk_comb(termP1, Match_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Match_t = defined_const Match_def;
val Match_def' = prove(
  “^term_ABS_t1 ^Match_pattern = ^Match_t a b P”,
    srw_tac [][Match_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Match_termP]);

(* Mismatch *)
val Mismatch_t = mk_var("Mismatch", “:string -> string -> ^newty1 -> ^newty1”);
val Mismatch_pattern = “GLAM uu [a; b] rMismatch [] [^term_REP_t1 P]”;
val Mismatch_def = new_definition(
   "Mismatch_def",
  “^Mismatch_t a b P = ^term_ABS_t1 ^(toArb Mismatch_pattern)”);
val Mismatch_termP = prove(
    mk_comb(termP1, Mismatch_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Mismatch_t = defined_const Mismatch_def;
val Mismatch_def' = prove(
  “^term_ABS_t1 ^Mismatch_pattern = ^Mismatch_t a b P”,
    srw_tac [][Mismatch_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Mismatch_termP]);

(* Sum (Choice) *)
val Sum_t = mk_var("Sum", “:^newty1 -> ^newty1 -> ^newty1”);
val Sum_pattern = “GLAM uu [] rSum [] [^term_REP_t1 P; ^term_REP_t1 Q]”;
val Sum_def = new_definition(
   "Sum_def",
  “^Sum_t P Q = ^term_ABS_t1 ^(toArb Sum_pattern)”);
val Sum_termP = prove(
    mk_comb(termP1, Sum_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Sum_t = defined_const Sum_def;
val Sum_def' = prove(
  “^term_ABS_t1 ^Sum_pattern = ^Sum_t P Q”,
    srw_tac [][Sum_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Sum_termP]);

(* Parallel Composition *)
val Par_t = mk_var("Par", “:^newty1 -> ^newty1 -> ^newty1”);
val Par_pattern = “GLAM uu [] rPar [] [^term_REP_t1 P; ^term_REP_t1 Q]”;
val Par_def = new_definition(
   "Par_def",
  “^Par_t P Q = ^term_ABS_t1 ^(toArb Par_pattern)”);
val Par_termP = prove(
    mk_comb(termP1, Par_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Par_t = defined_const Par_def;
val Par_def' = prove(
  “^term_ABS_t1 ^Par_pattern = ^Par_t P Q”,
    srw_tac [][Par_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Par_termP]);

(* Restriction *)
val Res_t = mk_var("Res", “:string -> ^newty1 -> ^newty1”);
val Res_pattern = “GLAM v [] rRes [^term_REP_t1 P] []”;
val Res_def = new_definition(
   "Res_def",
  “^Res_t v P = ^term_ABS_t1 ^Res_pattern”);
val Res_termP = prove(
    mk_comb (termP1, Res_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Res_t = defined_const Res_def;

(* TauR *)
val TauR_t = mk_var("TauR", “:^newty1 -> ^newty2”);
val TauR_pattern = “GLAM uu [] rTauR [] [^term_REP_t1 P]”;
val TauR_def = new_definition(
   "TauR_def",
  “^TauR_t P = ^term_ABS_t2 ^(toArb TauR_pattern)”);
val TauR_termP = prove(
    mk_comb(termP2, TauR_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val TauR_t = defined_const TauR_def;
val TauR_def' = prove(
  “^term_ABS_t2 ^TauR_pattern = ^TauR_t P”,
    srw_tac [][TauR_def, GLAM_NIL_EQ, term_ABS_pseudo11_2, TauR_termP]);

(* Bound output (residual) *)
val BoundOutput_t =
    mk_var("BoundOutput", “:string -> string -> ^newty1 -> ^newty2”);
val BoundOutput_pattern = “GLAM x [a] rBoundOutput [^term_REP_t1 P] []”;
val BoundOutput_def = new_definition(
   "BoundOutput_def",
  “^BoundOutput_t a x P = ^term_ABS_t2 ^BoundOutput_pattern”);
val BoundOutput_termP = prove(
    mk_comb(termP2, BoundOutput_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val BoundOutput_t = defined_const BoundOutput_def;

(* Input residual *)
val InputS_t = mk_var("InputS", “:string -> string -> ^newty1 -> ^newty2”);
val InputS_pattern = “GLAM x [a] rInputS [^term_REP_t1 P] []”;
val InputS_def = new_definition(
   "InputS_def",
  “^InputS_t a x P = ^term_ABS_t2 ^InputS_pattern”);
val InputS_termP = prove(
    mk_comb(termP2, InputS_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val InputS_t = defined_const InputS_def;

(* Free output (residual) *)
val FreeOutput_t =
    mk_var("FreeOutput", “:string -> string -> ^newty1 -> ^newty2”);
val FreeOutput_pattern = “GLAM uu [a; b] rFreeOutput [] [^term_REP_t1 P]”;
val FreeOutput_def = new_definition(
   "FreeOutput_def",
  “^FreeOutput_t a b P = ^term_ABS_t2 ^(toArb FreeOutput_pattern)”);
val FreeOutput_termP = prove(
    mk_comb(termP2, FreeOutput_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val FreeOutput_t = defined_const FreeOutput_def;
val FreeOutput_def' = prove(
  “^term_ABS_t2 ^FreeOutput_pattern = ^FreeOutput_t a b P”,
    srw_tac [][FreeOutput_def, GLAM_NIL_EQ, term_ABS_pseudo11_2,
               FreeOutput_termP]);

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

(* |- (!pi. tpm pi Nil = Nil) /\ (!pi P. tpm pi (Tau P) = Tau (tpm pi P)) /\
      (!x pi a P.
         tpm pi (Input a x P) =
         Input (lswapstr pi a) (lswapstr pi x) (tpm pi P)) /\
      (!pi b a P.
         tpm pi (Output a b P) =
         Output (lswapstr pi a) (lswapstr pi b) (tpm pi P)) /\
      (!pi b a P.
         tpm pi (Match a b P) =
         Match (lswapstr pi a) (lswapstr pi b) (tpm pi P)) /\
      (!pi b a P.
         tpm pi (Mismatch a b P) =
         Mismatch (lswapstr pi a) (lswapstr pi b) (tpm pi P)) /\
      (!pi Q P. tpm pi (Sum P Q) = Sum (tpm pi P) (tpm pi Q)) /\
      (!pi Q P. tpm pi (Par P Q) = Par (tpm pi P) (tpm pi Q)) /\
      !v pi P. tpm pi (Res v P) = Res (lswapstr pi v) (tpm pi P)
 *)
Theorem tpm_thm[allow_rebind] =
        tpm_thm |> REWRITE_RULE [GSYM Input_def, Output_def',
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

(* |- (!pi P. rpm pi (TauR P) = TauR (tpm pi P)) /\
      (!x pi a P.
         rpm pi (BoundOutput a x P) =
         BoundOutput (lswapstr pi a) (lswapstr pi x) (tpm pi P)) /\
      (!x pi a P.
         rpm pi (InputS a x P) =
         InputS (lswapstr pi a) (lswapstr pi x) (tpm pi P)) /\
      !pi b a P.
        rpm pi (FreeOutput a b P) =
        FreeOutput (lswapstr pi a) (lswapstr pi b) (tpm pi P)
 *)
Theorem rpm_thm[allow_rebind] =
        rpm_thm
     |> REWRITE_RULE [GSYM term_REP_tpm, TauR_def',
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
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, LIST_TO_SET, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm]
    |> GEN_ALL
end

(* |- FV Nil = {} /\ (!P. FV (Tau P) = FV P) /\
      (!x a P. FV (Input a x P) = FV P DELETE x UNION {a}) /\
      (!b a P. FV (Output a b P) = FV P UNION {a; b}) /\
      (!b a P. FV (Match a b P) = FV P UNION {a; b}) /\
      (!b a P. FV (Mismatch a b P) = FV P UNION {a; b}) /\
      (!Q P. FV (Sum P Q) = FV P UNION FV Q) /\
      (!Q P. FV (Par P Q) = FV P UNION FV Q) /\
      !v P. FV (Res v P) = FV P DELETE v
 *)
Theorem FV_thm[simp] = LIST_CONJ (map supp_clause cons_info)

(* |- !x t p. x IN FV (tpm p t) <=> lswapstr (REVERSE p) x IN FV t *)
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
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, LIST_TO_SET, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm]
    |> GEN_ALL
end

(* |- (!P. FV (TauR P) = FV P) /\
      (!x a P. FV (BoundOutput a x P) = FV P DELETE x UNION {a}) /\
      (!x a P. FV (InputS a x P) = FV P DELETE x UNION {a}) /\
      !b a P. FV (FreeOutput a b P) = FV P UNION {a; b}
 *)
Theorem FV_residual_thm[simp] = LIST_CONJ (map rsupp_clause rcons_info)

(* |- !x t p. x IN FV (rpm p t) <=> lswapstr (REVERSE p) x IN FV t *)
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

val term_ind1 =
    bvc_genind
        |> INST_TYPE [alpha |-> rep_t]
        |> Q.INST [‘lp’ |-> ‘^lp’]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPECL [‘\n t0 x. n = 1 ==> Q t0 x’, ‘fv’]
        |> UNDISCH |> Q.SPEC ‘1’ |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm, LENGTH_NIL,
                      LENGTH1, LENGTH2,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists1,
                      genind_exists2,
                      LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [‘Q’ |-> ‘\t. P (^term_ABS_t1 t)’]
        |> SIMP_RULE std_ss [absrep_id1,
                             Nil_def', Tau_def', GSYM Input_def,
                             Output_def', Match_def', Mismatch_def',
                             Sum_def', Par_def', GSYM Res_def,
                             LENGTH_NIL]
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                  [ASSUME “!x:'b. FINITE (fv x:string set)”]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GENL [‘P’, ‘fv’];

fun mkX_ind th = th |> Q.SPECL [‘\t x. Q t’, ‘\x. X’]
                    |> SIMP_RULE std_ss [] |> Q.GEN ‘X’
                    |> Q.INST [‘Q’ |-> ‘P’] |> Q.GEN ‘P’;

(* NOTE: not recommended unless in generated theorems *)
Theorem nc_INDUCTION[local] = mkX_ind term_ind1

(* The recommended induction theorem containing correctly namedbinding variables. *)
Theorem nc_INDUCTION2 :
    !P X.
        P Nil /\ (!E. P E ==> P (Tau E)) /\
        (!a x E. P E /\ x NOTIN X ==> P (Input a x E)) /\
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
          (!a x E. P E ==> P (Input a x E)) /\
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

val term_ind2 =
    bvc_genind
        |> INST_TYPE [alpha |-> rep_t]
        |> Q.INST [‘lp’ |-> ‘^lp’]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPECL [‘\n t0 x. n = 2 ==> Q t0 x’, ‘fv’]
        |> UNDISCH |> Q.SPEC ‘2’ |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm, LENGTH_NIL,
                      LENGTH1, LENGTH2,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists1,
                      genind_exists2,
                      LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [‘Q’ |-> ‘\t. P (^term_ABS_t2 t)’]
        |> SIMP_RULE std_ss [absrep_id1, absrep_id2,
                             Nil_def', Tau_def', GSYM Input_def,
                             Output_def', Match_def', Mismatch_def',
                             Sum_def', Par_def', GSYM Res_def,
                             GSYM BoundOutput_def,
                             GSYM InputS_def,
                             TauR_def', FreeOutput_def']
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, GSYM supp_rpm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV_residual}
                                  [ASSUME “!x:'b. FINITE (fv x:string set)”]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GENL [‘P’, ‘fv’];

Theorem residual_INDUCTION[local] = mkX_ind term_ind2

Theorem residual_INDUCTION2 :
    !P X.
        (!E. P (TauR E)) /\
        (!a x E. x NOTIN X ==> P (BoundOutput a x E)) /\
        (!a x E. x NOTIN X ==> P (InputS a x E)) /\
        (!a b E. P (FreeOutput a b E)) /\ FINITE X ==> !E. P E
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC residual_INDUCTION
 >> Q.EXISTS_TAC ‘X’ >> rw []
QED

(* |- !P. (!E. P (TauR E)) /\ (!a x E. P (BoundOutput a x E)) /\
          (!a x E. x # a ==> P (InputS a x E)) /\
          (!a b E. P (FreeOutput a b E)) ==>
          !E. P E
 *)
Theorem simple_induction_residual =
    residual_INDUCTION2 |> Q.SPECL [‘P’, ‘{}’]
                        |> REWRITE_RULE [FINITE_EMPTY, NOT_IN_EMPTY]
                        |> Q.GEN ‘P’

(* ----------------------------------------------------------------------
    Alpha conversions of constructors involving bound names
   ---------------------------------------------------------------------- *)

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

Theorem tpm_ALPHA_Res :
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
                              GLAM_eq_thm, term_REP_11_1,
                              GSYM term_REP_tpm, GSYM supp_tpm]
     |> Q.GENL [‘a’, ‘b’, ‘x’, ‘y’, ‘t1’, ‘t2’]

Theorem tpm_ALPHA_Input :
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
                              term_REP_11_1, term_REP_11_2,
                              GSYM term_REP_tpm, GSYM term_REP_rpm,
                              GSYM supp_tpm, GSYM supp_rpm]
     |> Q.GENL [‘a’, ‘b’, ‘x’, ‘y’, ‘t1’, ‘t2’]

Theorem tpm_ALPHA_InputS :
    v # (u :pi) ==> InputS a x u = InputS a v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][InputS_eq_thm, pmact_flip_args]
QED

(* |- !a b x y t1 t2.
        BoundOutput a x t1 = BoundOutput b y t2 <=>
        x = y /\ t1 = t2 /\ a = b \/
        x <> y /\ x # t2 /\ t1 = tpm [(x,y)] t2 /\ a = b
 *)
Theorem BoundOutput_eq_thm =
  “BoundOutput a x t1 = BoundOutput b y (t2 :pi)”
     |> SIMP_CONV (srw_ss()) [BoundOutput_def, BoundOutput_termP, term_ABS_pseudo11_2,
                              GLAM_eq_thm,
                              term_REP_11_1, term_REP_11_2,
                              GSYM term_REP_tpm, GSYM term_REP_rpm,
                              GSYM supp_tpm, GSYM supp_rpm]
     |> Q.GENL [‘a’, ‘b’, ‘x’, ‘y’, ‘t1’, ‘t2’]

Theorem tpm_ALPHA_BoundOutput :
    v # (u :pi) ==> BoundOutput a x u = BoundOutput a v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][BoundOutput_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    cases, distinct and one-one theorems
   ---------------------------------------------------------------------- *)

Theorem pi_cases :
    !t. (t = Nil) \/ (?P. t = Tau P) \/
        (?a x P. t = Input a x P) \/ (?a b P. t = Output a b P) \/
        (?a b P. t = Match a b P) \/ (?a b P. t = Mismatch a b P) \/
        (?P Q. t = Sum P Q) \/ (?P Q. t = Par P Q) \/
         ?v P. t = Res v P
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [][] (* 216 subgoals here *)
 >> METIS_TAC []
QED

Theorem residual_cases :
    !t. (?P. t = TauR P) \/
        (?a x P. t = BoundOutput a x P) \/
        (?a b P. t = FreeOutput a b P) \/
        (?a x P. t = InputS a x P)
Proof
    HO_MATCH_MP_TAC simple_induction_residual
 >> SRW_TAC [][] (* 4 subgoals here *)
 >> METIS_TAC []
QED

Theorem pi_distinct[simp] :
    (Nil <> Tau P) /\
    (Nil <> Input a x P) /\
    (Nil <> Output a b P) /\
    (Nil <> Match a b P) /\
    (Nil <> Mismatch a b P) /\
    (Nil <> Sum P Q) /\
    (Nil <> Par P Q) /\
    (Nil <> Res v P) /\
    (Tau P <> Input a x Q) /\
    (Tau P <> Output a b Q) /\
    (Tau P <> Match a b Q) /\
    (Tau P <> Mismatch a b Q) /\
    (Tau P <> Sum P1 P2) /\
    (Tau P <> Par P1 P2) /\
    (Tau P <> Res v Q) /\
    (Input a x P <> Output b y Q) /\
    (Input a x P <> Match b c Q) /\
    (Input a x P <> Mismatch b c Q) /\
    (Input a x P <> Sum P1 P2) /\
    (Input a x P <> Par P1 P2) /\
    (Input a x P <> Res v Q) /\
    (Output a b P <> Match c d Q) /\
    (Output a b P <> Mismatch c d Q) /\
    (Output a b P <> Sum P1 P2) /\
    (Output a b P <> Par P1 P2) /\
    (Output a b P <> Res v Q) /\
    (Match a b P <> Mismatch c d Q) /\
    (Match a b P <> Sum P1 P2) /\
    (Match a b P <> Par P1 P2) /\
    (Match a b P <> Res v Q) /\
    (Mismatch a b P <> Sum P1 P2) /\
    (Mismatch a b P <> Par P1 P2) /\
    (Mismatch a b P <> Res v Q) /\
    (Sum P1 P2 <> Par P3 P4) /\
    (Sum P1 P2 <> Res v Q) /\
    (Par P1 P2 <> Res v Q)
Proof
    rw [Nil_def, Nil_termP, Tau_def, Tau_termP,
        Input_def, Input_termP, Output_def, Output_termP,
        Match_def, Match_termP, Mismatch_def, Mismatch_termP,
        Sum_def, Sum_termP, Par_def, Par_termP,
        Res_def, Res_termP,
        term_ABS_pseudo11_1, GLAM_eq_thm]
QED

Theorem residual_distinct[simp] :
    (TauR P <> BoundOutput a x Q) /\
    (TauR P <> InputS a x Q) /\
    (TauR P <> FreeOutput a b Q) /\
    (BoundOutput a x P <> InputS b y Q) /\
    (BoundOutput a x P <> FreeOutput b c Q) /\
    (InputS a x P <> FreeOutput b c Q)
Proof
    rw [TauR_def, TauR_termP, BoundOutput_def, BoundOutput_termP,
        InputS_def, InputS_termP, FreeOutput_def, FreeOutput_termP,
        term_ABS_pseudo11_2, GLAM_eq_thm]
QED

Theorem pi_one_one[simp] :
    (!P Q. Tau P = Tau Q <=> P = Q) /\
    (!a b P c d Q. Output a b P = Output c d Q <=> a = c /\ b = d /\ P = Q) /\
    (!a b P c d Q. Match a b P = Match c d Q <=> a = c /\ b = d /\ P = Q) /\
    (!a b P c d Q. Mismatch a b P = Mismatch c d Q <=> a = c /\ b = d /\ P = Q) /\
    (!P1 P2 Q1 Q2. Sum P1 P2 = Sum Q1 Q2 <=> P1 = Q1 /\ P2 = Q2) /\
    (!P1 P2 Q1 Q2. Par P1 P2 = Par Q1 Q2 <=> P1 = Q1 /\ P2 = Q2)
Proof
    srw_tac [] [Tau_def, Tau_termP, Output_def, Output_termP,
                Match_def, Match_termP, Mismatch_def, Mismatch_termP,
                Sum_def, Sum_termP, Par_def, Par_termP,
                term_ABS_pseudo11_1, gterm_11, term_REP_11_1]
 >> rw [CONJ_ASSOC]
QED

Theorem residual_one_one[simp] :
    (!P Q. TauR P = TauR Q <=> P = Q) /\
    (!a b P c d Q. FreeOutput a b P = FreeOutput c d Q <=> a = c /\ b = d /\ P = Q)
Proof
    srw_tac [] [TauR_def, TauR_termP, FreeOutput_def, FreeOutput_termP,
                term_ABS_pseudo11_2, gterm_11,
                term_REP_11_1, term_REP_11_2]
 >> rw [CONJ_ASSOC]
QED

Theorem pi_distinct_exists :
    !(p :pi). ?q. q <> p
Proof
    Q.X_GEN_TAC ‘p’
 >> MP_TAC (Q.SPEC ‘p’ pi_cases) >> rw []
 >- (Q.EXISTS_TAC ‘Tau P’ >> rw [])
 >> Q.EXISTS_TAC ‘Nil’
 >> rw [pi_distinct]
QED

Theorem pi_distinct_exists_FV :
    !X (p :pi). FINITE X ==> ?q. q <> p /\ DISJOINT (FV q) X
Proof
    rpt STRIP_TAC
 >> Q_TAC (NEW_TAC "z") ‘X’
 >> MP_TAC (Q.SPEC ‘p’ pi_cases) >> rw []
 >- (Q.EXISTS_TAC ‘Tau Nil’ >> rw [])
 >> Q.EXISTS_TAC ‘Nil’
 >> rw [pi_distinct]
QED

val _ = overload_on ("+", “Sum”); (* priority: 500 *)
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };
val _ = set_mapped_fixity {fixity = Infixl 600,
                           tok = "||", term_name = "Par"};
val _ = TeX_notation { hol = "||", TeX = ("\\ensuremath{\\mid}", 1) };

Theorem Sum_acyclic :
    !t1 t2 :pi. t1 <> t1 + t2 /\ t1 <> t2 + t1
Proof
    HO_MATCH_MP_TAC simple_induction >> SRW_TAC [][]
QED

Theorem Par_acyclic :
    !t1 t2 :pi. t1 <> t1 || t2 /\ t1 <> t2 || t1
Proof
    HO_MATCH_MP_TAC simple_induction >> SRW_TAC [][]
QED

Theorem FORALL_TERM :
    (!(t :pi). P t) <=> P Nil /\
    (!E. P (Tau E)) /\ (!a x E. P (Input a x E)) /\
    (!a b E. P (Output a b E)) /\
    (!a b E. P (Match a b E)) /\
    (!a b E. P (Mismatch a b E)) /\
    (!t1 t2. P (t1 + t2)) /\ (!t1 t2. P (t1 || t2)) /\
    (!v E. P (Res v E))
Proof
    EQ_TAC >> SRW_TAC [][]
 >> Q.SPEC_THEN ‘t’ STRUCT_CASES_TAC pi_cases >> SRW_TAC [][]
QED

(* ----------------------------------------------------------------------
    term recursion
   ---------------------------------------------------------------------- *)

(* NOTE: all 3 types have the same repty *)
val (_, repty) = dom_rng (type_of term_REP_t1);
val repty' = ty_antiq repty;

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
   “genind ^lp n t <=>
      ^termP1 t /\ n = 1 \/
      ^termP2 t /\ n = 2”,
    EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac >> rw []
 >> qsuff_tac ‘n = 1 \/ n = 2’ >- (strip_tac >> srw_tac [][])
 >> pop_assum mp_tac
 >> Q.ISPEC_THEN ‘t’ STRUCT_CASES_TAC gterm_cases
 >> srw_tac [][genind_GLAM_eqn]);

(* Type of constants (all constructors are included) occurring in tlf:

   Nil:    “tnf :('q -> 'r)”
   Tau:    “ttf :('q -> 'r) -> pi -> ('q -> 'r)”
   Input:  “tif :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   Output: “tof :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   Match:  “tmf :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   Mismatch: “tuf :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   Sum:    “tsf :('q -> 'r) -> ('q -> 'r) -> pi -> pi -> ('q -> 'r)”
   Par:    “tpf :('q -> 'r) -> ('q -> 'r) -> pi -> pi -> ('q -> 'r)”
   Res:    “tcf :string -> ('q -> 'r) -> pi -> ('q -> 'r)”

   TauR:        “taf :('q -> 'r) -> pi -> ('q -> 'r)”
   InputS:      “trf :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   BoundOutput: “tbf :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”
   FreeOutput:  “tff :string -> string -> ('q -> 'r) -> pi -> ('q -> 'r)”

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
   “λ(v :string) (fvs :string list) ^u_tm
     (ds1 :('q -> 'r) list) (ds2 :('q -> 'r) list)
     (ts1 :^repty' list) (ts2 :^repty' list) (p :'q).
      case u of
        rNil => tnf p : 'r
      | rTau => ttf (HD ds2) (^term_ABS_t1 (HD ts2)) p :'r
      | rInput => tif (HD fvs) v (HD ds1)
                      (^term_ABS_t1 (HD ts1)) p :'r
      | rOutput => tof (HD fvs) (HD (TL fvs)) (HD ds2)
                       (^term_ABS_t1 (HD ts2)) p :'r
      | rMatch => tmf (HD fvs) (HD (TL fvs)) (HD ds2)
                      (^term_ABS_t1 (HD ts2)) p :'r
      | rMismatch => tuf (HD fvs) (HD (TL fvs)) (HD ds2)
                         (^term_ABS_t1 (HD ts2)) p :'r
      | rSum => tsf (HD ds2) (HD (TL ds2))
                    (^term_ABS_t1 (HD ts2))
                    (^term_ABS_t1 (HD (TL ts2))) p :'r
      | rPar => tpf (HD ds2) (HD (TL ds2))
                    (^term_ABS_t1 (HD ts2))
                    (^term_ABS_t1 (HD (TL ts2))) p :'r
      | rRes => tcf v (HD ds1) (^term_ABS_t1 (HD ts1)) p :'r
      | rTauR => taf (HD ds2) (^term_ABS_t1 (HD ts2)) p :'r
      | rInputS => trf (HD fvs) v (HD ds1)
                       (^term_ABS_t1 (HD ts1)) p :'r
      | rBoundOutput => tbf (HD fvs) v (HD ds1)
                            (^term_ABS_t1 (HD ts1)) p :'r
      | rFreeOutput => tff (HD fvs) (HD (TL fvs)) (HD ds2)
                           (^term_ABS_t1 (HD ts2)) p :'r”;

Overload TLF = tlf

val FN = mk_var("FN", “:repcode gterm -> 'q -> 'r”)
val fn1_def_t = “fn1 = λp. ^FN (pi_REP p)”
val fn2_def_t = “fn2 = λr. ^FN (residual_REP r)”

val testcase = [(fn1_def_t, repabs_pseudo_id1,
                 [SYM Nil_def', Input_def, SYM Output_def', SYM Tau_def',
                  SYM Match_def', SYM Mismatch_def', SYM Sum_def', SYM Par_def',
                  Res_def]),
                (fn2_def_t, repabs_pseudo_id2,
                 [InputS_def, SYM FreeOutput_def', BoundOutput_def,
                  SYM TauR_def'])]

Theorem GLAM_NIL_ELIM[local]:
  GLAM u fvs bv [] ts = GLAM ARB fvs bv [] ts
Proof
  simp[GLAM_NIL_EQ]
QED

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
            simp_tac list_ss [genind_GLAM_eqn,
                              TypeBase.distinct_of “:repcode”,
                              LIST_REL_NIL, LIST_REL_CONS1, PULL_EXISTS,
                              CONS_11, genind_term_REP1, genind_term_REP2]
          val goal =
                mk_eq (mk_comb(FN, rand (rhs eq)), mk_comb (c, lhs eq))
        in
          TAC_PROOF(([tm_def], goal), tactic)
        end
  in
    map def1 defs
  end

val fn_rewrites = map case1 testcase

val parameter_tm_recursion0 =
  parameter_gtm_recursion
      |> INST_TYPE [alpha |-> rep_t, gamma |-> “:'r”]
      |> Q.INST [‘lf’ |-> ‘^tlf’, ‘lp’ |-> ‘^lp’]
      |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                               GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                               GSYM RIGHT_EXISTS_AND_THM,
                               GSYM LEFT_EXISTS_AND_THM,
                               GSYM LEFT_FORALL_IMP_THM,
                               LIST_REL_CONS1,
                               genind_GLAM_eqn, sidecond_def,
                               NEWFCB_def, relsupp_def,
                               LENGTH_NIL_SYM, LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP']
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2, LENGTH_NIL]
      |> CONV_RULE (DEPTH_CONV termP_removal1)
      |> CONV_RULE (DEPTH_CONV termP_removal2)
      |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, SYM term_REP_tpm,
                               GSYM supp_rpm, SYM term_REP_rpm,
                               relsupp_def]
      |> UNDISCH
      |> rpt_hyp_dest_conj

val rwt1 =
  EQ_MP (SCONV [Once FUN_EQ_THM] fn1_def_t) (ASSUME fn1_def_t) |> GSYM
val rwt2 =
  EQ_MP (SCONV [Once FUN_EQ_THM] fn2_def_t) (ASSUME fn2_def_t) |> GSYM

val (exv, body) = dest_exists (concl parameter_tm_recursion0)
val cs = CONJUNCTS (ASSUME (body |> subst[exv |-> FN]))

val cs' = map (SIMP_RULE bool_ss (rwt1:: rwt2:: GLAM_NIL_ELIM ::
                                  List.concat fn_rewrites)) cs

val th0 = LIST_CONJ cs'
val eqns = List.filter is_eq (hyp th0)
val th1 = itlist Prim_rec.EXISTS_EQUATION eqns th0
val th = CHOOSE (FN, parameter_tm_recursion0) th1

Theorem parameter_tm_recursion = th
      |> DISCH_ALL
      |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                [ASSUME “FINITE (A:string set)”,
                                 ASSUME “∀p:'q. FINITE (supp ppm p)”]
      |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST
      [‘tnf’ |-> ‘f0’, (* Nil :'q->'r *)
       ‘ttf’ |-> ‘f1’, (* Tau :('q->'r) -> pi -> 'q->'r *)
       ‘tif’ |-> ‘f2’, (* Input :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tof’ |-> ‘f3’, (* Output :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tmf’ |-> ‘f4’, (* Match :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tuf’ |-> ‘f5’, (* Mismatch :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tsf’ |-> ‘f6’, (* Sum :('q->'r) -> ('q->'r) -> pi -> pi -> 'q->'r *)
       ‘tpf’ |-> ‘f7’, (* Par :('q->'r) -> ('q->'r) -> pi -> pi -> 'q->'r *)
       ‘tcf’ |-> ‘f8’, (* Res :string -> ('q->'r) -> pi -> 'q->'r *)
       ‘taf’ |-> ‘f9’, (* TauR :('q->'r) -> pi -> 'q->'r *)
       ‘trf’ |-> ‘f10’, (* InputS :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tbf’ |-> ‘f11’, (* BoundOutput :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘tff’ |-> ‘f12’, (* FreeOutput :string->string -> ('q->'r) -> pi -> 'q->'r *)
       ‘dpm’ |-> ‘apm’]
      |> CONV_RULE (REDEPTH_CONV sort_uvars)

(* (fn1 :pi -> 'r) (fn2 :residual -> 'r) *)
Theorem tm_recursion =
  parameter_tm_recursion
      |> Q.INST_TYPE [‘:'q’ |-> ‘:unit’]
      |> Q.INST [‘ppm’ |-> ‘discrete_pmact’,
                  ‘f0’ |-> ‘\u. g0’,
                  ‘f1’ |-> ‘\r t u. g1 (r()) t’,
                  ‘f2’ |-> ‘\a x r t u. g2 a x (r()) t’,
                  ‘f3’ |-> ‘\a b r t u. g3 a b (r()) t’,
                  ‘f4’ |-> ‘\a b r t u. g4 a b (r()) t’,
                  ‘f5’ |-> ‘\a b r t u. g5 a b (r()) t’,
                  ‘f6’ |-> ‘\r1 r2 t1 t2 u. g6 (r1()) (r2()) t1 t2’,
                  ‘f7’ |-> ‘\r1 r2 t1 t2 u. g7 (r1()) (r2()) t1 t2’,
                  ‘f8’ |-> ‘\s r t u. g8 s (r()) t’,
                  ‘f9’ |-> ‘\r t u. g9 (r()) t’,
                 ‘f10’ |-> ‘\a x r t u. g10 a x (r()) t’,
                 ‘f11’ |-> ‘\a x r t u. g11 a x (r()) t’,
                 ‘f12’ |-> ‘\a b r t u. g12 a b (r()) t’]
      |> SIMP_RULE (srw_ss()) [oneTheory.FORALL_ONE, oneTheory.FORALL_ONE_FN,
                               oneTheory.EXISTS_ONE_FN, fnpm_def]
      |> SIMP_RULE (srw_ss() ++ CONJ_ss) [supp_unitfn]
      |> Q.INST [ ‘g0’ |-> ‘f0’,
                  ‘g1’ |-> ‘f1’,
                  ‘g2’ |-> ‘f2’,
                  ‘g3’ |-> ‘f3’,
                  ‘g4’ |-> ‘f4’,
                  ‘g5’ |-> ‘f5’,
                  ‘g6’ |-> ‘f6’,
                  ‘g7’ |-> ‘f7’,
                  ‘g8’ |-> ‘f8’,
                  ‘g9’ |-> ‘f9’,
                 ‘g10’ |-> ‘f10’,
                 ‘g11’ |-> ‘f11’,
                 ‘g12’ |-> ‘f12’]

(* ----------------------------------------------------------------------
    Establish substitution function
   ---------------------------------------------------------------------- *)

Theorem tpm_COND[local] :
    tpm pi (if P then x else y) = if P then tpm pi x else tpm pi y
Proof
    SRW_TAC [][]
QED

Theorem rpm_COND[local] :
    rpm pi (if P then x else y) = if P then rpm pi x else rpm pi y
Proof
    SRW_TAC [][]
QED

Theorem tpm_apart :
    !(t :pi). x # t /\ y IN FV t ==> tpm [(x,y)] t <> t
Proof
    metis_tac[supp_apart, pmact_flip_args]
QED

Theorem rpm_apart :
    !(t :residual). x # t /\ y IN FV t ==> rpm [(x,y)] t <> t
Proof
    metis_tac[supp_apart, pmact_flip_args]
QED

Theorem tpm_fresh :
    !(t :pi) x y. x # t /\ y # t ==> tpm [(x,y)] t = t
Proof
    srw_tac [][supp_fresh]
QED

Theorem rpm_fresh :
    !(t :residual) x y. x # t /\ y # t ==> rpm [(x,y)] t = t
Proof
    srw_tac [][supp_fresh]
QED

Theorem tpm_Nil[simp] :
    tpm pi Nil = Nil
Proof
    Induct_on ‘pi’ >- rw []
 >> Q.X_GEN_TAC ‘h’
 >> Cases_on ‘h’
 >> rw [Once tpm_CONS]
 >> MATCH_MP_TAC tpm_fresh >> rw []
QED

Theorem rewrite_pairing[local] :
    (?f :pi -> (string # string) -> pi. P f) <=>
    (?f :string -> string -> pi -> pi. P (\M (x,y). f y x M))
Proof
    EQ_TAC >> strip_tac
 >| [ (* goal 1 (of 2) *)
      qexists_tac ‘\y x M. f M (x,y)’ >> srw_tac [][] \\
      CONV_TAC (DEPTH_CONV pairLib.PAIRED_ETA_CONV) \\
      srw_tac [ETA_ss][],
      (* goal 2 (of 2) *)
      qexists_tac ‘\M (x,y). f y x M’ >> srw_tac [][] ]
QED

Overload NilR[local] = “TauR Nil” (* A closed term of :residual *)

Overload I1[local] = “\(p :pi). (p,NilR)”
Overload I2[local] = “\(r :residual). (Nil,r)”
Overload O1[local] = “\(z :pi # residual). FST z”
Overload O2[local] = “\(z :pi # residual). SND z”

Definition subst_def :
   subst ((k,v) :string # string) (s :string) =
   if s = k then v else k
End
Overload SUB = “\v k s. subst (k,v) s”

Theorem subst_swapstr[simp] :
    swapstr x y ([E/u] e) = ([swapstr x y E/swapstr x y u] (swapstr x y e))
Proof
    rw [subst_def, swapstr_def] >> METIS_TAC []
QED

val subst_exists =
    parameter_tm_recursion
        |> INST_TYPE [“:'q” |-> “:string # string” (* (key,value) *),
                      “:'r” |-> “:pi # residual”]
        |> SPEC_ALL
        |> Q.INST [
              ‘A’ |-> ‘{}’, (* NOTE: only possible when closed term exists *)
            ‘ppm’ |-> ‘pair_pmact string_pmact string_pmact’,
            ‘apm’ |-> ‘pair_pmact pi_pmact residual_pmact’,
            (* f0 ~ f8 is for the type :pi *)
             ‘f0’ |-> ‘\u. I1 Nil’,
             ‘f1’ |-> ‘\r t u. I1 (Tau (O1 (r u)))’,
             ‘f2’ |-> ‘\a x r t u. I1 (Input (subst u a) x (O1 (r u)))’,
             ‘f3’ |-> ‘\a b r t u. I1 (Output (subst u a) (subst u b) (O1 (r u)))’,
             ‘f4’ |-> ‘\a b r t u. I1 (Match (subst u a) (subst u b) (O1 (r u)))’,
             ‘f5’ |-> ‘\a b r t u. I1 (Mismatch (subst u a) (subst u b) (O1 (r u)))’,
             ‘f6’ |-> ‘\r1 r2 t1 t2 u. I1 (Sum (O1 (r1 u)) (O1 (r2 u)))’,
             ‘f7’ |-> ‘\r1 r2 t1 t2 u. I1 (Par (O1 (r1 u)) (O1 (r2 u)))’,
             ‘f8’ |-> ‘\s r t u. I1 (Res s (O1 (r u)))’,
            (* f9 ~ f12 is for the type :residual *)
             ‘f9’ |-> ‘\r t u. I2 (TauR (O1 (r u)))’,
            ‘f10’ |-> ‘\a x r t u. I2 (InputS (subst u a) x (O1 (r u)))’,
            ‘f11’ |-> ‘\a x r t u. I2 (BoundOutput (subst u a) x (O1 (r u)))’,
            ‘f12’ |-> ‘\a b r t u. I2 (FreeOutput (subst u a) (subst u b)
                                                  (O1 (r u)))’]
        |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD]))
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def,
                                 tpm_COND, tpm_fresh, pmact_sing_inv,
                                 rpm_COND, rpm_fresh, rpm_thm, tpm_thm,
                                 basic_swapTheory.swapstr_eq_left,
                                 SYM term_REP_tpm, SYM term_REP_rpm,
                                 GSYM InputS_def, GSYM BoundOutput_def]
        |> SIMP_RULE (srw_ss()) [rewrite_pairing, pairTheory.FORALL_PROD]
        |> CONV_RULE (DEPTH_CONV (rename_vars [("p_1", "u"), ("p_2", "E")]))
     (* NOTE: The first ppm represents the two nominal types being constructed,
        and it should be always like this for any recursive function on multiple
        nominal types. (This part should be automated.)

        The second ppm represents the parameters of the recursive function. In
        this case it's from string to string. It varies among different recursive
        functions being constructed.
      *)
        |> prove_alpha_fcbhyp {ppms = [“pair_pmact pi_pmact residual_pmact”,
                                       “pair_pmact string_pmact string_pmact”],
                               rwts = [],
                               alphas = [tpm_ALPHA_Res, tpm_ALPHA_Input,
                                         tpm_ALPHA_InputS,
                                         tpm_ALPHA_BoundOutput]};

val SUB12 = new_specification
  ("SUB12", ["SUB1", "SUB2"], subst_exists);

(* “[E/u] P” aka “P [u |-> E]” *)
Definition pi_sub_def :
    pi_sub E u P = O1 (SUB1 P (u,E))
End
Overload SUB = “pi_sub”

Definition residual_sub_def :
    residual_sub E u P = O2 (SUB2 P (u,E))
End
Overload SUB = “residual_sub”

val ths = CONJUNCTS SUB12;

(* debug
val n = List.length ths; (* 15 here *)
val th = el 1 (CONJUNCTS SUB12);
 *)

(* This function returns the conclusion ignoring antecedents *)
fun concl1 th =
    let val tm = concl (SPEC_ALL th) in
        if is_imp tm then snd (dest_imp tm) else tm
    end;

(* This function takes “f b” or “f a b” and returns “f” *)
fun rator2 tm =
    let val tm1 = rator tm in
        if is_comb tm1 then rator tm1 else tm1
    end;

fun has_term sub_tm th =
    let val (l,r) = dest_eq (concl1 th) in
       (aconv (rator2 l) sub_tm) orelse
       (aconv (rator2 r) sub_tm)
    end;
val has_sub1 = has_term “SUB1”;
val has_sub2 = has_term “SUB2”;

val th1s = map (underAIs (SRULE [GSYM pi_sub_def] o
                          BETA_RULE o AP_TERM “O1”))
               (filter has_sub1 ths);

val th2s = map (underAIs (SRULE [GSYM residual_sub_def, GSYM pi_sub_def] o
                          BETA_RULE o AP_TERM “O2”))
               (filter has_sub2 ths);

Theorem pi_sub_thm[simp]       = LIST_CONJ th1s
Theorem residual_sub_thm[simp] = LIST_CONJ th2s

Theorem tpm_subst :
    !pi E u t. tpm pi ([E/u] t) = [lswapstr pi E/lswapstr pi u] (tpm pi t)
Proof
    Induct_on ‘pi’
 >> simp [FORALL_PROD, Once tpm_CONS]
 >> rpt STRIP_TAC
 >> Suff ‘tpm ((p_1,p_2)::pi) t = tpm [(p_1,p_2)] (tpm pi t)’ >- rw []
 >> simp [Once tpm_CONS]
QED

Theorem rpm_subst :
    !pi E u t. rpm pi ([E/u] t) = [lswapstr pi E/lswapstr pi u] (rpm pi t)
Proof
    Induct_on ‘pi’
 >> simp [FORALL_PROD, Once rpm_CONS]
 >> rpt STRIP_TAC
 >> Suff ‘rpm ((p_1,p_2)::pi) t = rpm [(p_1,p_2)] (rpm pi t)’ >- rw []
 >> simp [Once rpm_CONS]
QED

val _ = export_theory ();
val _ = html_theory "pi_agent";
