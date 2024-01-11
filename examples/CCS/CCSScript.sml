(* ========================================================================== *)
(* FILE          : CCSScript.sml                                              *)
(* DESCRIPTION   : A formalization of the process algebra CCS in HOL          *)
(*                                                                            *)
(* COPYRIGHTS    : 1991-1995 University of Cambridge, UK (Monica Nesi)        *)
(*                 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(*                 2018-2019 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 The Australian National University (Chun Tian)   *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib
     rich_listTheory finite_mapTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

local open termTheory; in end; (* for SUB's syntax only *)

val _ = new_theory "CCS";

val set_ss = std_ss ++ PRED_SET_ss;

(* ----------------------------------------------------------------------
    Labels and Actions
   ---------------------------------------------------------------------- *)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
Datatype: Label = name 'a | coname 'a
End

(* Define structural induction on labels
   !P. (!s. P (name s)) /\ (!s. P (coname s)) ==> !L. P L
 *)
val Label_induction = TypeBase.induction_of ``:'a Label``;

(* The structural cases theorem for the type Label
   !LL. (?s. LL = name s) \/ ?s. LL = coname s
 *)
val Label_cases = TypeBase.nchotomy_of ``:'a Label``;

(* The distinction and injectivity theorems for the type Label
   !a' a. name a <> coname a'
   (!a a'. (name a = name a') <=> (a = a')) /\
       !a a'. (coname a = coname a') <=> (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:'a Label``;
val Label_distinct' = save_thm ("Label_distinct'", GSYM Label_distinct);

(* |- !a' a. name a = coname a' <=> F *)
val Label_not_eq = save_thm (
   "Label_not_eq", STRIP_FORALL_RULE EQF_INTRO Label_distinct);

(* |- !a' a. coname a' = name a <=> F *)
val Label_not_eq' = save_thm (
   "Label_not_eq'", STRIP_FORALL_RULE
                        (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``])
                        Label_not_eq);

(* |- (!a a'. name a = name a' <=> a = a') /\
       !a a'. coname a = coname a' <=> a = a' *)
val Label_11 = TypeBase.one_one_of ``:'a Label``;

(* NEW: define the set of actions as the OPTION of Label *)
Type Action[pp] = ``:'a Label option``;

val _ = overload_on ("tau",   ``NONE :'a Action``);
val _ = overload_on ("label", ``SOME :'a Label -> 'a Action``);

val _ = Unicode.unicode_version { u = UnicodeChars.tau, tmnm = "tau" };
val _ = TeX_notation { hol = "tau", TeX = ("\\ensuremath{\\tau}", 1) };

(* The compact representation for (visible) input and output actions, is
   suggested by Michael Norrish *)
val _ = overload_on ("In", ``\a. label (name a)``);
val _ = overload_on ("Out", ``\a. label (coname a)``);

val _ = TeX_notation { hol = "In",  TeX = ("\\HOLTokenInputAct", 1) };
val _ = TeX_notation { hol = "Out", TeX = ("\\HOLTokenOutputAct", 1) };

(* Define structural induction on actions
   !P. P tau /\ (!L. P (label L)) ==> !A. P A
 *)
val Action_induction = save_thm (
   "Action_induction", INST_TYPE [``:'a`` |-> ``:'a Label``] option_induction);

(* The structural cases theorem for the type Action
   !AA. (AA = tau) \/ ?L. AA = label L
 *)
val Action_cases = save_thm (
   "Action_cases", INST_TYPE [``:'a`` |-> ``:'a Label``] option_nchotomy);

(* The distinction and injectivity theorems for the type Action
   !a. tau <> label a
   !a a'. (label a = label a') <=> (a = a')
 *)
val Action_distinct = save_thm (
   "Action_distinct", INST_TYPE [``:'a`` |-> ``:'a Label``] NOT_NONE_SOME);

val Action_distinct_label = save_thm (
   "Action_distinct_label", INST_TYPE [``:'a`` |-> ``:'a Label``] NOT_SOME_NONE);

val Action_11 = save_thm (
   "Action_11", INST_TYPE [``:'a`` |-> ``:'a Label``] SOME_11);

(* !A. A <> tau ==> ?L. A = label L *)
val Action_no_tau_is_Label = save_thm (
   "Action_no_tau_is_Label",
    Q.GEN `A` (DISJ_IMP (Q.SPEC `A` Action_cases)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val _ = overload_on ("LABEL", ``THE :'a Label option -> 'a Label``);

(* |- !x. LABEL (label x) = x *)
val LABEL_def = save_thm (
   "LABEL_def", INST_TYPE [``:'a`` |-> ``:'a Label``] THE_DEF);

(* |- (!x. IS_SOME (label x) <=> T) /\ (IS_SOME 't <=> F) *)
val IS_LABEL_def = save_thm (
   "IS_LABEL_def", INST_TYPE [``:'a`` |-> ``:'a Label``] IS_SOME_DEF);

val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_LAB_def = Define `(COMPL_LAB (name (s :'a)) = (coname s)) /\
                            (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm
  ("coname_COMPL", ``!(s :'a). coname s = COMPL (name s)``,
    REWRITE_TAC [COMPL_LAB_def]);

val COMPL_COMPL_LAB = store_thm (
   "COMPL_COMPL_LAB", ``!(l :'a Label). COMPL_LAB (COMPL_LAB l) = l``,
    Induct >> REWRITE_TAC [COMPL_LAB_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label (l: 'a Label)) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;

val _ = overload_on ("COMPL", ``COMPL_ACT``);
val _ = export_rewrites ["COMPL_ACT_def"];

Theorem COMPL_COMPL_ACT :
    !(a :'a Action). COMPL_ACT (COMPL_ACT a) = a
Proof
    Induct_on `a`
 >- REWRITE_TAC [COMPL_ACT_def]
 >> REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB]
QED

(* auxiliary theorem about complementary labels. *)
Theorem COMPL_THM :
    !(l :'a Label) s. (l <> name s ==> COMPL l <> coname s) /\
                      (l <> coname s ==> COMPL l <> name s)
Proof
    Induct_on `l`
 >| [ (* case 1 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_11, COMPL_LAB_def],
        REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'] ] ,
      (* case 2 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'],
        REWRITE_TAC [Label_11, COMPL_LAB_def] ] ]
QED

(* Relabeling function is subtype of `:'a Label -> 'a Label *)
val Is_Relabeling_def = Define `
    Is_Relabeling (f: 'a Label -> 'a Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling",
  ``?(f: 'a Label -> 'a Label). Is_Relabeling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabeling_def]
 >> BETA_TAC
 >> REWRITE_TAC [COMPL_LAB_def]);

(* |- ?rep. TYPE_DEFINITION Is_Relabeling rep *)
val Relabeling_TY_DEF = new_type_definition ("Relabeling", EXISTS_Relabeling);

(* |- (!a. ABS_Relabeling (REP_Relabeling a) = a) /\
       !r. Is_Relabeling r <=> (REP_Relabeling (ABS_Relabeling r) = r)
 *)
val Relabeling_ISO_DEF =
    define_new_type_bijections {ABS  = "ABS_Relabeling",
                                REP  = "REP_Relabeling",
                                name = "Relabeling_ISO_DEF",
                                tyax =  Relabeling_TY_DEF};

(* ABS_Relabeling_one_one =
   !r r'.
      Is_Relabeling r ==> Is_Relabeling r' ==>
      ((ABS_Relabeling r = ABS_Relabeling r') <=> (r = r'))

   ABS_Relabeling_onto =
   !a. ?r. (a = ABS_Relabeling r) /\ Is_Relabeling r

   REP_Relabeling_one_one =
   !a a'. (REP_Relabeling a = REP_Relabeling a') <=> (a = a')

   REP_Relabeling_onto =
   !r. Is_Relabeling r <=> ?a. r = REP_Relabeling a
 *)
val [ABS_Relabeling_one_one, ABS_Relabeling_onto,
     REP_Relabeling_one_one, REP_Relabeling_onto] =
    map (fn f => f Relabeling_ISO_DEF)
        [prove_abs_fn_one_one, prove_abs_fn_onto,
         prove_rep_fn_one_one, prove_rep_fn_onto];

Theorem REP_Relabeling_THM :
    !rf :'a Relabeling. Is_Relabeling (REP_Relabeling rf)
Proof
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []
QED

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `
   (relabel (rf :'a Relabeling) tau = tau) /\
   (relabel rf (label l) = label (REP_Relabeling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
Theorem Relab_label :
    !(rf :'a Relabeling) u l. (relabel rf u = label l) ==> ?l'. u = label l'
Proof
    Induct_on `u`
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``a :'a Label``
 >> REWRITE_TAC []
QED

(* If the renaming of an action is tau, that action is tau. *)
Theorem Relab_tau :
    !(rf :'a Relabeling) u. (relabel rf u = tau) ==> (u = tau)
Proof
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]
QED

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: ('a Label # 'a Label) list) l = l) /\
   (Apply_Relab ((newold: 'a Label # 'a Label) :: ls) l =
          if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

Theorem Apply_Relab_COMPL_THM :
    !labl (s: 'a). Apply_Relab labl (coname s) =
            COMPL (Apply_Relab labl (name s))
Proof
    Induct >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> rpt GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'a Label # 'a Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM >> art []
QED

Theorem IS_RELABELING :
    !labl :('a Label # 'a Label) list. Is_Relabeling (Apply_Relab labl)
Proof
    Induct
 >- REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def, COMPL_LAB_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'a Label # 'a Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> art [Apply_Relab_COMPL_THM]
QED

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label) list -> Relabeling
 *)
val RELAB_def = Define `
    RELAB (labl :('a Label # 'a Label) list) = ABS_Relabeling (Apply_Relab labl)`;

(* !labl labl'.
     (RELAB labl = RELAB labl') <=> (Apply_Relab labl = Apply_Relab labl')
 *)
val APPLY_RELAB_THM = save_thm (
   "APPLY_RELAB_THM",
    Q.GENL [`labl`, `labl'`]
      (REWRITE_RULE [GSYM RELAB_def]
        (MATCH_MP (MATCH_MP ABS_Relabeling_one_one
                            (Q.SPEC `labl` IS_RELABELING))
                  (Q.SPEC `labl` IS_RELABELING))));

(******************************************************************************)
(*                                                                            *)
(*             Syntax of pure CCS (general formalization)                     *)
(*                                                                            *)
(******************************************************************************)

(* The (equivalent) old way (no alpha conversion)
Datatype: CCS = nil
              | var string
              | prefix ('a Action) CCS
              | sum CCS CCS
              | par CCS CCS
              | restr ('a Label set) CCS
              | relab CCS ('a Relabeling)
              | rec string CCS
End
 *)

(* The new way based on "examples/lambda/basics/generic_termsTheory

   NOTE: it defines “:'a CCS” where 'a is 'b of the old “:('a,'b) CCS”.
 *)
val tyname = "CCS";

(* ‘GVAR s vv’ corresponds to ‘var 'a’ *)
val vp = “(\n u:unit. n = 0)”;                                  (* 0. var *)

val rep_t = “:unit + 'a Action + unit + unit + 'a Label set + 'a Relabeling + unit”;
val d_tm = mk_var("d", rep_t);

(* ‘GLAM v bv ts us’ corresponds to everything else. *)
val lp =
  “(\n ^d_tm tns uns.
     n = 0 /\ ISL d /\ tns = [] ∧ uns = []  \/                  (* 1. nil *)
     n = 0 /\ ISR d /\ ISL (OUTR d) /\ tns = [] /\ uns = [0] \/ (* 2. prefix *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISL (OUTR (OUTR d)) /\
              tns = [] /\ uns = [0;0] \/                        (* 3. sum *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISL (OUTR (OUTR (OUTR d))) /\
              tns = [] /\ uns = [0;0] \/                        (* 4. par *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISL (OUTR (OUTR (OUTR (OUTR d)))) /\
              tns = [] ∧ uns = [0] \/                           (* 5. restr *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISR (OUTR (OUTR (OUTR (OUTR d)))) /\
              ISL (OUTR (OUTR (OUTR (OUTR (OUTR d))))) /\
              tns = [] /\ uns = [0] \/                          (* 6. relab *)
     n = 0 /\ ISR d /\ ISR (OUTR d) /\ ISR (OUTR (OUTR d)) /\
              ISR (OUTR (OUTR (OUTR d))) /\
              ISR (OUTR (OUTR (OUTR (OUTR d)))) /\
              ISR (OUTR (OUTR (OUTR (OUTR (OUTR d))))) /\
              tns = [0] ∧ uns = [])”;                           (* 7. rec *)

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t, newty, ...} =
    new_type_step1 tyname 0 {vp = vp, lp = lp};

(* ----------------------------------------------------------------------
    CCS operators
   ---------------------------------------------------------------------- *)

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS;

(* var *)
val var_t = mk_var("var", “:string -> ^newty”)
val var_def = new_definition(
   "var_def", “^var_t s = ^term_ABS_t (GVAR s ())”);
val var_termP = prove(
  mk_comb(termP, var_def |> SPEC_ALL |> concl |> rhs |> rand),
  srw_tac [][genind_rules]);
val var_t = defined_const var_def;

(* nil *)
val nil_t = mk_var("nil", “:^newty”);
val nil_def = new_definition(
   "nil_def", “^nil_t = ^term_ABS_t (GLAM ARB (INL ()) [] [])”);
val nil_termP = prove(“^termP (GLAM x (INL ()) [] [])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val nil_t = defined_const nil_def;
val nil_def' = prove(“^term_ABS_t (GLAM v (INL ()) [] []) = ^nil_t”,
    srw_tac [][nil_def, GLAM_NIL_EQ, term_ABS_pseudo11, nil_termP]);

val _ = TeX_notation { hol = "nil", TeX = ("\\ensuremath{\\mathbf{0}}", 1) };

(* prefix *)
val prefix_t = mk_var("prefix", “:'a Action -> ^newty -> ^newty”);
val prefix_def = new_definition(
   "prefix_def",
  “^prefix_t u E = ^term_ABS_t (GLAM ARB (INR (INL u)) [] [^term_REP_t E])”);
val prefix_termP = prove(
  “^termP (GLAM x (INR (INL u)) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val prefix_t = defined_const prefix_def;
val prefix_def' = prove(
  “^term_ABS_t (GLAM v (INR (INL u)) [] [^term_REP_t E]) = ^prefix_t u E”,
    srw_tac [][prefix_def, GLAM_NIL_EQ, term_ABS_pseudo11, prefix_termP]);

(* sum *)
val sum_t = mk_var("sum", “:^newty -> ^newty -> ^newty”);
val sum_def = new_definition(
   "sum_def",
  “^sum_t E1 E2 = ^term_ABS_t (GLAM ARB (INR (INR (INL ()))) []
                                        [^term_REP_t E1; ^term_REP_t E2])”);
val sum_termP = prove(
  “^termP (GLAM x (INR (INR (INL ()))) [] [^term_REP_t E1; ^term_REP_t E2])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val sum_t = defined_const sum_def;
val sum_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INL ()))) []
                       [^term_REP_t E1; ^term_REP_t E2]) = ^sum_t E1 E2”,
    srw_tac [][sum_def, GLAM_NIL_EQ, term_ABS_pseudo11, sum_termP]);

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };

(* par *)
val par_t = mk_var("par", “:^newty -> ^newty -> ^newty”);
val par_def = new_definition(
   "par_def",
  “^par_t E1 E2 = ^term_ABS_t (GLAM ARB (INR (INR (INR (INL ())))) []
                                        [^term_REP_t E1; ^term_REP_t E2])”);
val par_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INL ())))) []
                  [^term_REP_t E1; ^term_REP_t E2])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val par_t = defined_const par_def;
val par_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INL ())))) []
                       [^term_REP_t E1; ^term_REP_t E2]) = ^par_t E1 E2”,
    srw_tac [][par_def, GLAM_NIL_EQ, term_ABS_pseudo11, par_termP]);

val _ = set_mapped_fixity {fixity = Infixl 600,
                           tok = "||", term_name = "par"};

(* val _ = Unicode.unicode_version {u = UTF8.chr 0x007C, tmnm = "par"}; *)
val _ = TeX_notation { hol = "||", TeX = ("\\ensuremath{\\mid}", 1) };

(* restr *)
val restr_t = mk_var("restr", “:'a Label set -> ^newty -> ^newty”);
val restr_def = new_definition(
   "restr_def",
  “^restr_t L E = ^term_ABS_t (GLAM ARB (INR (INR (INR (INR (INL L))))) []
                                        [^term_REP_t E])”);
val restr_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INR (INL L))))) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val restr_t = defined_const restr_def;
val restr_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INR (INL L))))) [] [^term_REP_t E]) =
   ^restr_t L E”,
    srw_tac [][restr_def, GLAM_NIL_EQ, term_ABS_pseudo11, restr_termP]);

(* compact representation for single-action restriction *)
val _ = overload_on("nu", “λ(n :'a) P. restr {name n} P”);

val _ = add_rule {term_name = "nu", fixity = Closefix,
                  pp_elements = [TOK ("(" ^ UnicodeChars.nu), TM, TOK ")"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

(* relab *)
val relab_t = mk_var("relab", “:^newty -> 'a Relabeling -> ^newty”);
val relab_def = new_definition(
   "relab_def",
  “^relab_t E rf =
   ^term_ABS_t (GLAM ARB (INR (INR (INR (INR (INR (INL rf)))))) []
                         [^term_REP_t E])”);
val relab_termP = prove(
  “^termP (GLAM x (INR (INR (INR (INR (INR (INL rf)))))) [] [^term_REP_t E])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val relab_t = defined_const relab_def;
val relab_def' = prove(
  “^term_ABS_t (GLAM v (INR (INR (INR (INR (INR (INL rf)))))) []
                       [^term_REP_t E]) =
   ^relab_t E rf”,
    srw_tac [][relab_def, GLAM_NIL_EQ, term_ABS_pseudo11, relab_termP]);

(* rec *)
val rec_t = mk_var("rec", “:string -> ^newty -> ^newty”);
val rec_def = new_definition(
   "rec_def",
  “^rec_t X E =
   ^term_ABS_t (GLAM X (INR (INR (INR (INR (INR (INR ()))))))
                       [^term_REP_t E] [])”);
val rec_termP = prove(
  “^termP (GLAM X (INR (INR (INR (INR (INR (INR ())))))) [^term_REP_t E] [])”,
    match_mp_tac glam >> srw_tac [][genind_term_REP]);
val rec_t = defined_const rec_def;

val _ =
    add_rule { term_name = "prefix", fixity = Infixr 700,
        pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "..", TeX = ("\\ensuremath{\\ldotp}", 1) };

(* ----------------------------------------------------------------------
    tpm (permutation of CCS recursion variables)
   ---------------------------------------------------------------------- *)

val cons_info =
    [{con_termP = var_termP,    con_def = var_def},
     {con_termP = nil_termP,    con_def = SYM nil_def'},
     {con_termP = prefix_termP, con_def = SYM prefix_def'},
     {con_termP = sum_termP,    con_def = SYM sum_def'},
     {con_termP = par_termP,    con_def = SYM par_def'},
     {con_termP = restr_termP,  con_def = SYM restr_def'},
     {con_termP = relab_termP,  con_def = SYM relab_def'},
     {con_termP = rec_termP,    con_def = rec_def}];

val tpm_name_pfx = "t";
val {tpm_thm, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation {name_pfx = tpm_name_pfx, name = tyname,
                        term_REP_t = term_REP_t,
                        term_ABS_t = term_ABS_t,
                        absrep_id = absrep_id,
                        repabs_pseudo_id = repabs_pseudo_id,
                        cons_info = cons_info, newty = newty,
                        genind_term_REP = genind_term_REP};

Theorem tpm_eqr :
    t = tpm pi u <=> tpm (REVERSE pi) t = (u :'a CCS)
Proof
    METIS_TAC [pmact_inverse]
QED

Theorem tpm_eql :
    tpm pi t = u <=> t = tpm (REVERSE pi) (u :'a CCS)
Proof
    simp[tpm_eqr]
QED

Theorem tpm_CONS :
    tpm ((x,y)::pi) (t :'a CCS) = tpm [(x,y)] (tpm pi t)
Proof
  SRW_TAC [][GSYM pmact_decompose]
QED

(* ----------------------------------------------------------------------
    support and FV
   ---------------------------------------------------------------------- *)

val term_REP_eqv = prove(
   “support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t {}”,
    srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]);

val supp_term_REP = prove(
   “supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t = {}”,
    REWRITE_TAC [GSYM SUBSET_EMPTY]
 >> MATCH_MP_TAC (GEN_ALL supp_smallest)
 >> srw_tac [][term_REP_eqv]);

val tpm_def' =
    term_REP_tpm |> AP_TERM term_ABS_t |> PURE_REWRITE_RULE [absrep_id];

val t = mk_var("t", newty);

val supptpm_support = prove(
   “support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t ^t))”,
    srw_tac [][support_def, tpm_def', supp_fresh, absrep_id]);

val supptpm_apart = prove(
   “x IN supp gt_pmact (^term_REP_t ^t) /\ y NOTIN supp gt_pmact (^term_REP_t ^t)
    ==> ^tpm_t [(x,y)] ^t <> ^t”,
    srw_tac [][tpm_def']
 >> DISCH_THEN (MP_TAC o AP_TERM term_REP_t)
 >> srw_tac [][repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP, supp_apart]);

val supp_tpm = prove(
   “supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t ^t)”,
    match_mp_tac (GEN_ALL supp_unique_apart)
 >> srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV]);

val _ = overload_on ("FV", “supp ^t_pmact_t”);

val _ = set_fixity "#" (Infix(NONASSOC, 450));
val _ = overload_on ("#", “\X (E :'a CCS). X NOTIN FV E”);

Theorem FINITE_FV[simp] :
    FINITE (FV (t :'a CCS))
Proof
    srw_tac [][supp_tpm, FINITE_GFV]
QED

Theorem FV_EMPTY :
    FV t = {} <=> !v. v NOTIN FV (t :'a CCS)
Proof
    SIMP_TAC (srw_ss()) [EXTENSION]
QED

fun supp_clause {con_termP, con_def} = let
  val t = mk_comb(“supp ^t_pmact_t”, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm]
    |> GEN_ALL
end

Theorem FV_thm[simp] = LIST_CONJ (map supp_clause cons_info)
Theorem FV_def = FV_thm

val [FV_var, FV_nil, FV_prefix, FV_sum, FV_par,
     FV_restr, FV_relab, FV_rec] =
    map save_thm
        (combine (["FV_var", "FV_nil", "FV_prefix", "FV_sum", "FV_par",
                   "FV_restr", "FV_relab", "FV_rec"], CONJUNCTS FV_thm));

(* |- !x t p. x IN FV (tpm p t) <=> lswapstr (REVERSE p) x IN FV t *)
Theorem FV_tpm[simp] = “x IN FV (tpm p (t :'a CCS))”
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
        |> INST_TYPE [alpha |-> rep_t, beta |-> “:unit”]
        |> Q.INST [‘vp’ |-> ‘^vp’, ‘lp’ |-> ‘^lp’]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPECL [‘\n t0 x. Q t0 x’, ‘fv’]
        |> UNDISCH |> Q.SPEC ‘0’ |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists, LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [‘Q’ |-> ‘\t. P (^term_ABS_t t)’]
        |> SIMP_RULE std_ss [GSYM var_def, GSYM nil_def, nil_def', prefix_def',
                             sum_def', par_def', restr_def', relab_def',
                             GSYM rec_def, absrep_id]
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                  [ASSUME “!x:'c. FINITE (fv x:string set)”]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GENL [‘P’, ‘fv’];

fun mkX_ind th = th |> Q.SPECL [‘\t x. Q t’, ‘\x. X’]
                    |> SIMP_RULE std_ss [] |> Q.GEN ‘X’
                    |> Q.INST [‘Q’ |-> ‘P’] |> Q.GEN ‘P’;

(* NOTE: not recommended unless in generated theorems *)
Theorem nc_INDUCTION[local] = mkX_ind term_ind

(* The recommended induction theorem containing correctly named
   binding variables (L, rf, y, etc.)
 *)
Theorem nc_INDUCTION2 :
    !P X.
        (!s. P (var s)) /\ P nil /\ (!u E. P E ==> P (u..E)) /\
        (!E1 E2. P E1 /\ P E2 ==> P (E1 + E2)) /\
        (!E1 E2. P E1 /\ P E2 ==> P (E1 || E2)) /\
        (!L E. P E ==> P (restr L E)) /\
        (!E rf. P E ==> P (relab E rf)) /\
        (!y E. P E /\ y NOTIN X ==> P (rec y E)) /\ FINITE X ==>
        !t. P t
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘X’ >> rw []
QED

Theorem simple_induction =
    nc_INDUCTION2 |> Q.SPECL [‘P’, ‘{}’]
                  |> REWRITE_RULE [FINITE_EMPTY, NOT_IN_EMPTY]
                  |> Q.GEN ‘P’

Theorem rec_eq_thm =
  “(rec u t1 = rec v t2 :'a CCS)”
     |> SIMP_CONV (srw_ss()) [rec_def, rec_termP, term_ABS_pseudo11,
                              GLAM_eq_thm, term_REP_11, GSYM term_REP_tpm,
                              GSYM supp_tpm]
     |> Q.GENL [‘u’, ‘v’, ‘t1’, ‘t2’]

Theorem tpm_ALPHA :
    v # (u :'a CCS) ==> rec x u = rec v (tpm [(v,x)] u)
Proof
    SRW_TAC [boolSimps.CONJ_ss][rec_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    term recursion
   ---------------------------------------------------------------------- *)

val (_, repty) = dom_rng (type_of term_REP_t);
val repty' = ty_antiq repty;

val termP_elim = prove(
   “(!g. ^termP g ==> P g) <=> (!t. P (^term_REP_t t))”,
    srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP]
 >> first_x_assum (qspec_then ‘^term_ABS_t g’ mp_tac)
 >> srw_tac [][repabs_pseudo_id]);

val termP_removal =
    nomdatatype.termP_removal {
      elimth = termP_elim, absrep_id = absrep_id,
      tpm_def = AP_TERM term_ABS_t term_REP_tpm |> REWRITE_RULE [absrep_id],
      termP = termP, repty = repty};

val termP0 = prove(
   “genind ^vp ^lp n t <=> ^termP t ∧ (n = 0)”,
    EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac
 >> qsuff_tac ‘n = 0’ >- (strip_tac >> srw_tac [][])
 >> pop_assum mp_tac
 >> Q.ISPEC_THEN ‘t’ STRUCT_CASES_TAC gterm_cases
 >> srw_tac [][genind_GVAR, genind_GLAM_eqn]);

(* “tvf :string -> 'q -> 'r” *)
val tvf = “λ(s:string) (u:unit) (p:ρ). tvf s p : 'r”; (* var *)

(* Type of constants occurring in tlf:

   nil:    “tnf :'q -> 'r”
   prefix: “tff :('q -> 'r) -> 'a Action -> 'a CCS -> 'q -> 'r”
   sum:    “tsf :('q -> 'r) -> ('q -> 'r) -> 'a CCS -> 'a CCS -> 'q -> 'r”
   par:    “tpf :('q -> 'r) -> ('q -> 'r) -> 'a CCS -> 'a CCS -> 'q -> 'r”
   restr:  “trf :('q -> 'r) -> ('a Label -> bool) -> 'a CCS -> 'q -> 'r”
   relab:  “tlf :('q -> 'r) -> 'a CCS -> 'a Relabeling -> 'q -> 'r”
   rec:    “tcf :('q -> 'r) -> string -> 'a CCS -> 'q -> 'r”
 *)
val u_tm = mk_var("u", rep_t);
val tlf =
   “λ(v:string) ^u_tm (ds1:('q -> 'r) list) (ds2:('q -> 'r) list)
                      (ts1:^repty' list) (ts2:^repty' list) (p :'q).
       if ISL u then
         tnf p :'r
       else if ISL (OUTR u) then
         tff (HD ds2) (OUTL (OUTR u)) (^term_ABS_t (HD ts2)) p :'r
       else if ISL (OUTR (OUTR u)) then
         tsf (HD ds2) (HD (TL ds2))
             (^term_ABS_t (HD ts2)) (^term_ABS_t (HD (TL ts2))) p :'r
       else if ISL (OUTR (OUTR (OUTR u))) then
         tpf (HD ds2) (HD (TL ds2))
             (^term_ABS_t (HD ts2)) (^term_ABS_t (HD (TL ts2))) p :'r
       else if ISL (OUTR (OUTR (OUTR (OUTR u)))) then
         trf (HD ds2) (OUTL (OUTR (OUTR (OUTR (OUTR u)))))
             (^term_ABS_t (HD ts2)) p :'r
       else if ISL (OUTR (OUTR (OUTR (OUTR (OUTR u))))) then
         tlf (HD ds2) (^term_ABS_t (HD ts2))
             (OUTL (OUTR (OUTR (OUTR (OUTR (OUTR u)))))) p :'r
       else
         tcf (HD ds1) v (^term_ABS_t (HD ts1)) p :'r”;

Theorem parameter_tm_recursion =
  parameter_gtm_recursion
      |> INST_TYPE [alpha |-> rep_t, beta |-> “:unit”, gamma |-> “:'r”]
      |> Q.INST [‘lf’ |-> ‘^tlf’, ‘vf’ |-> ‘^tvf’, ‘vp’ |-> ‘^vp’,
                 ‘lp’ |-> ‘^lp’, ‘n’ |-> ‘0’]
      |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                               GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                               GSYM RIGHT_EXISTS_AND_THM,
                               GSYM LEFT_EXISTS_AND_THM,
                               GSYM LEFT_FORALL_IMP_THM,
                               LIST_REL_CONS1, genind_GVAR,
                               genind_GLAM_eqn, sidecond_def,
                               NEWFCB_def, relsupp_def,
                               LENGTH_NIL_SYM, LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP0]
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2, LENGTH_NIL]
      |> CONV_RULE (DEPTH_CONV termP_removal)
      |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, SYM term_REP_tpm]
      |> UNDISCH
      |> rpt_hyp_dest_conj
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id,
                          term_REP_t = term_REP_t,
                          cons_info = cons_info}
      |> DISCH_ALL
      |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                [ASSUME ``FINITE (A:string set)``,
                                 ASSUME ``!p:ρ. FINITE (supp ppm p)``]
      |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST [‘tvf’ |-> ‘vr’, (* var *)
                 ‘tnf’ |-> ‘nl’, (* nil *)
                 ‘tff’ |-> ‘pf’, (* prefix *)
                 ‘tsf’ |-> ‘sm’, (* sum *)
                 ‘tpf’ |-> ‘pr’, (* par *)
                 ‘trf’ |-> ‘rs’, (* restr *)
                 ‘tlf’ |-> ‘rl’, (* relab *)
                 ‘tcf’ |-> ‘re’, (* rec *)
                 ‘dpm’ |-> ‘apm’]
      |> CONV_RULE (REDEPTH_CONV sort_uvars)

Theorem tm_recursion =
  parameter_tm_recursion
      |> Q.INST_TYPE [‘:'q’ |-> ‘:unit’]
      |> Q.INST [‘ppm’ |-> ‘discrete_pmact’,
                  ‘vr’ |-> ‘\s u. vru s’,
                  ‘nl’ |-> ‘\u. nlu’,
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
                 ‘nlu’ |-> ‘nl’,
                 ‘pfu’ |-> ‘pf’,
                 ‘smu’ |-> ‘sm’,
                 ‘pru’ |-> ‘pr’,
                 ‘rsu’ |-> ‘rs’,
                 ‘rlu’ |-> ‘rl’,
                 ‘reu’ |-> ‘re’]

(* ----------------------------------------------------------------------
    cases, distinct and one-one theorems
   ---------------------------------------------------------------------- *)

Theorem CCS_cases :
    !t. (t :'a CCS) = nil \/ (?a. t = var a) \/ (?u E. t = prefix u E) \/
        (?E1 E2. t = sum E1 E2) \/ (?E1 E2. t = par E1 E2) \/
        (?L E. t = restr L E) \/ (?E rf. t = relab E rf) \/
         ?X E. t = rec X E
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [][] (* 161 subgoals here *)
 >> METIS_TAC []
QED

Theorem CCS_distinct[simp] :
    (nil <> var X :'a CCS) /\
    (nil <> prefix u E :'a CCS) /\
    (nil <> E1 + E2 :'a CCS) /\
    (nil <> E1 || E2 :'a CCS) /\
    (nil <> restr L E :'a CCS) /\
    (nil <> relab E rf :'a CCS) /\
    (nil <> rec X E :'a CCS) /\
    (var X <> prefix u E :'a CCS) /\
    (var X <> E1 + E2 :'a CCS) /\
    (var X <> E1 || E2 :'a CCS) /\
    (var X <> restr L E :'a CCS) /\
    (var X <> relab E rf :'a CCS) /\
    (var X <> rec Y E :'a CCS) /\
    (prefix u E <> E1 + E2 :'a CCS) /\
    (prefix u E <> E1 || E2 :'a CCS) /\
    (prefix u E <> restr L E' :'a CCS) /\
    (prefix u E <> relab E' rf :'a CCS) /\
    (prefix u E <> rec X E' :'a CCS) /\
    (E1 + E2 <> E3 || E4 :'a CCS) /\
    (E1 + E2 <> restr L E :'a CCS) /\
    (E1 + E2 <> relab E rf :'a CCS) /\
    (E1 + E2 <> rec X E :'a CCS) /\
    (E1 || E2 <> (restr L) E :'a CCS) /\
    (E1 || E2 <> relab E rf :'a CCS) /\
    (E1 || E2 <> rec X E :'a CCS) /\
    (restr L E <> relab E' rf :'a CCS) /\
    (restr L E <> rec X E' :'a CCS) /\
     relab E rf <> rec X E' :'a CCS
Proof
    rw [nil_def, nil_termP, var_def, var_termP, prefix_def, prefix_termP,
        sum_def, sum_termP, par_def, par_termP, restr_def, restr_termP,
        relab_def, relab_termP, rec_def, rec_termP,
        term_ABS_pseudo11, gterm_distinct, GLAM_eq_thm]
QED

local
    val thm = CONJUNCTS CCS_distinct;
    val CCS_distinct_LIST = thm @ (map GSYM thm);
in
    val CCS_distinct' = save_thm
      ("CCS_distinct'", LIST_CONJ CCS_distinct_LIST);
end

Theorem CCS_distinct_exists :
    !(p :'a CCS). ?q. q <> p
Proof
    Q.X_GEN_TAC ‘p’
 >> MP_TAC (Q.SPEC ‘p’ CCS_cases) >> rw []
 >- (Q.EXISTS_TAC ‘nil + nil’ >> rw [CCS_distinct'])
 >> Q.EXISTS_TAC ‘nil’
 >> rw [CCS_distinct]
QED

Theorem CCS_distinct_exists_FV :
    !X (p :'a CCS). ?q. q <> p /\ DISJOINT (FV q) X
Proof
    rw []
 >> MP_TAC (Q.SPEC ‘p’ CCS_cases) >> rw []
 >- (Q.EXISTS_TAC ‘prefix a nil’ >> rw [CCS_distinct'])
 >> Q.EXISTS_TAC ‘nil’
 >> rw [CCS_distinct]
QED

(* cf. rec_eq_thm for “rec X E = rec X' E'” *)
Theorem CCS_one_one[simp] :
    (!X X'. var X = var X' :'a CCS <=> X = X') /\
    (!u E u' E' :'a CCS. prefix u E = prefix u' E' <=> u = u' /\ E = E') /\
    (!E1 E2 E1' E2' :'a CCS. E1 + E2 = E1' + E2' <=> E1 = E1' /\ E2 = E2') /\
    (!E1 E2 E1' E2' :'a CCS. E1 || E2 = E1' || E2' <=> E1 = E1' /\ E2 = E2') /\
    (!L E L' E' :'a CCS. restr L E = restr L' E' <=> L = L' /\ E = E') /\
    (!(E :'a CCS) rf E' rf'. relab E rf = relab E' rf' <=> E = E' /\ rf = rf')
Proof
    srw_tac [] [nil_def, nil_termP, var_def, var_termP,
                prefix_def, prefix_termP, sum_def, sum_termP,
                par_def, par_termP, restr_def, restr_termP,
                relab_def, relab_termP,
                term_ABS_pseudo11, gterm_11, term_REP_11]
 >> rw [Once CONJ_COMM]
QED

Theorem sum_acyclic :
    !t1 t2 :'a CCS. t1 <> t1 + t2 /\ t1 <> t2 + t1
Proof
    HO_MATCH_MP_TAC simple_induction >> SRW_TAC [][]
QED

Theorem par_acyclic :
    !t1 t2 :'a CCS. t1 <> t1 || t2 /\ t1 <> t2 || t1
Proof
    HO_MATCH_MP_TAC simple_induction >> SRW_TAC [][]
QED

Theorem FORALL_TERM :
    (!(t :'a CCS). P t) <=>
    P nil /\ (!s. P (var s)) /\ (!u t. P (prefix u t)) /\
    (!t1 t2. P (t1 + t2)) /\ (!t1 t2. P (t1 || t2)) /\
    (!L t. P (restr L t)) /\ (!t rf. P (relab t rf)) /\
    (!v t. P (rec v t))
Proof
    EQ_TAC >> SRW_TAC [][]
 >> Q.SPEC_THEN ‘t’ STRUCT_CASES_TAC CCS_cases >> SRW_TAC [][]
QED

(* ----------------------------------------------------------------------
    Establish substitution function
   ---------------------------------------------------------------------- *)

Theorem tpm_COND[local] :
    tpm pi (if P then x else y) = if P then tpm pi x else tpm pi y
Proof
    SRW_TAC [][]
QED

Theorem tpm_apart :
    !(t :'a CCS). x NOTIN FV t /\ y IN FV t ==> tpm [(x,y)] t <> t
Proof
    metis_tac[supp_apart, pmact_flip_args]
QED

Theorem tpm_fresh :
    !(t :'a CCS) x y. x NOTIN FV t /\ y NOTIN FV t ==> tpm [(x,y)] t = t
Proof
    srw_tac [][supp_fresh]
QED

val rewrite_pairing = prove(
   “(?f: 'a CCS -> (string # 'a CCS) -> 'a CCS. P f) <=>
    (?f: 'a CCS -> string -> 'a CCS -> 'a CCS. P (\M (x,N). f N x M))”,
  EQ_TAC >> strip_tac >| [
    qexists_tac ‘\N x M. f M (x,N)’ >> srw_tac [][] \\
    CONV_TAC (DEPTH_CONV pairLib.PAIRED_ETA_CONV) \\
    srw_tac [ETA_ss][],
    qexists_tac ‘\M (x,N). f N x M’ >> srw_tac [][]
  ]);

val subst_exists =
    parameter_tm_recursion
        |> INST_TYPE [“:'r” |-> “:'a CCS”,
                      “:'q” |-> “:string # 'a CCS”]
        |> SPEC_ALL
        |> Q.INST [‘A’ |-> ‘{}’, ‘apm’ |-> ‘^t_pmact_t’,
                   ‘ppm’ |-> ‘pair_pmact string_pmact ^t_pmact_t’,
                   ‘vr’ |-> ‘\s (x,N). if s = x then N else var s’,
                   ‘nl’ |-> ‘\r. nil’,
                   ‘pf’ |-> ‘\r x t p. prefix x (r p)’,
                   ‘sm’ |-> ‘\r1 r2 t1 t2 p. r1 p + r2 p’,
                   ‘pr’ |-> ‘\r1 r2 t1 t2 p. r1 p || r2 p’,
                   ‘rs’ |-> ‘\r L t p. restr L (r p)’,
                   ‘rl’ |-> ‘\r t rf p. relab (r p) rf’,
                   ‘re’ |-> ‘\r s t p. rec s (r p)’]
        |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD]))
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def,
                                 tpm_COND, tpm_fresh, pmact_sing_inv,
                                 basic_swapTheory.swapstr_eq_left]
        |> SIMP_RULE (srw_ss()) [rewrite_pairing, pairTheory.FORALL_PROD]
        |> CONV_RULE (DEPTH_CONV (rename_vars [("p_1", "u"), ("p_2", "E")]))
        |> prove_alpha_fcbhyp {ppm = ``pair_pmact string_pmact ^t_pmact_t``,
                               rwts = [],
                               alphas = [tpm_ALPHA]};

val SUB_DEF = new_specification("SUB_DEF", ["SUB"], subst_exists);

Overload SUB = “SUB”; (* use the syntax already defined in termTheory *)

val SUB_THMv = prove(
  “([N/x](var x) = (N :'a CCS)) /\ (x <> y ==> [N/y](var x) = var x)”,
  SRW_TAC [][SUB_DEF]);

Theorem SUB_COMM = prove(
   “!N x x' y (t :'a CCS).
        x' <> x /\ x' # N ∧ y <> x /\ y # N ==>
        (tpm [(x',y)] ([N/x] t) = [N/x] (tpm [(x',y)] t))”,
  srw_tac [][SUB_DEF, supp_fresh]);

val SUB_THM = save_thm("SUB_THM",
  let val (eqns,_) = CONJ_PAIR SUB_DEF
  in
    CONJ (REWRITE_RULE [GSYM CONJ_ASSOC]
                       (LIST_CONJ (SUB_THMv :: tl (CONJUNCTS eqns))))
         SUB_COMM
  end);
val _ = export_rewrites ["SUB_THM"];

(* |- !Y X E. [E/X] (var Y) = if Y = X then E else var Y *)
Theorem SUB_VAR = hd (CONJUNCTS SUB_DEF) |> Q.SPECL [‘Y’, ‘X’] |> GEN_ALL

(* |- !Y X E' E. Y <> X /\ Y # E' ==> [E'/X] (rec Y E) = rec Y ([E'/X] E) *)
Theorem SUB_REC = List.nth (CONJUNCTS SUB_DEF, 7)
               |> Q.SPECL [‘Y’, ‘X’, ‘E'’, ‘E’] |> GEN_ALL

(* ----------------------------------------------------------------------
    Results about substitution
   ---------------------------------------------------------------------- *)

Theorem fresh_tpm_subst :
    !t. u # (t :'a CCS) ==> (tpm [(u,v)] t = [var u/v] t)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC ‘{u;v}’
 >> SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem tpm_subst :
    !N :'a CCS. tpm pi ([M/v] N) = [tpm pi M/lswapstr pi v] (tpm pi N)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘v INSERT FV M’
 >> SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem tpm_subst_out :
    [M/v] (tpm pi (N :'a CCS)) =
    tpm pi ([tpm (REVERSE pi) M/lswapstr (REVERSE pi) v] N)
Proof
    SRW_TAC [][tpm_subst]
QED

Theorem lemma14a[simp] :
    !t. [var v/v] t = (t :'a CCS)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC ‘{v}’
 >> SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma14b :
    !M. v # M ==> [N/v] M = (M :'a CCS)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC ‘v INSERT FV N’
 >> SRW_TAC [][SUB_THM, SUB_VAR]
QED

(* Note: this is the opposite direction of lemma14b *)
Theorem SUB_FIX_IMP_NOTIN_FV :
    !x t. (!u. [u/x] t = t) ==> x NOTIN FV t
Proof
    rpt GEN_TAC
 >> Suff ‘(?u. u # t /\ [var u/x] t = t) ==> x # t’
 >- (rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q_TAC (NEW_TAC "z") ‘FV t’ \\
     Q.EXISTS_TAC ‘z’ >> rw [])
 >> simp [PULL_EXISTS]
 >> Q.X_GEN_TAC ‘u’
 >> Q.ID_SPEC_TAC ‘t’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘{x;u}’ >> rw [rec_eq_thm]
 >> CCONTR_TAC >> fs []
QED

Theorem lemma14b_ext1 :
    !v M. v # M <=> !N. ([N/v] M = M)
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [lemma14b]
 >> DISCH_TAC
 >> rw [SUB_FIX_IMP_NOTIN_FV]
QED

Theorem SUB_EQ_IMP_NOTIN_FV :
    !x t. (!t1 t2. [t1/x] t = [t2/x] t) ==> x NOTIN FV t
Proof
    rpt GEN_TAC
 >> Suff ‘(?u u'. u <> u' /\ u # t /\ u' # t /\
                  [var u/x] t = [var u'/x] t) ==> x # t’
 >- (rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q_TAC (NEW_TAC "z") ‘FV t’ \\
     Q.EXISTS_TAC ‘z’ >> rw [] \\
     Q_TAC (NEW_TAC "z'") ‘{z} UNION FV t’ \\
     Q.EXISTS_TAC ‘z'’ >> rw [])
 >> simp [PULL_EXISTS]
 >> rpt GEN_TAC
 >> Q.ID_SPEC_TAC ‘t’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘{x;u;u'}’ >> rw [rec_eq_thm]
 >> CCONTR_TAC >> fs []
QED

Theorem lemma14b_ext2 :
    !v M. v # M <=> !N1 N2. [N1/v] M = [N2/v] M
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [lemma14b]
 >> rw [SUB_EQ_IMP_NOTIN_FV]
QED

Theorem lemma14c :
    !t x u :'a CCS. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘x INSERT FV t’
 >> SRW_TAC [][SUB_THM, SUB_VAR, EXTENSION]
 >> METIS_TAC [lemma14b]
QED

Theorem FV_SUB :
    !(t :'a CCS) u v. FV ([t/v] u) =
                      if v IN FV u then FV t UNION (FV u DELETE v) else FV u
Proof
    PROVE_TAC [lemma14b, lemma14c]
QED

Theorem lemma15a :
    !M :'a CCS. v # M ==> [N/v] ([var v/x] M) = [N/x] M
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC ‘{x;v} UNION FV N’
 >> SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma15b :
    v # (M :'a CCS) ==> [var u/v] ([var v/u] M) = M
Proof
    SRW_TAC [][lemma15a]
QED

Theorem SUB_TWICE_ONE_VAR :
    !M :'a CCS. [x/v] ([y/v] M) = [[x/v] y/v] M
Proof
    HO_MATCH_MP_TAC nc_INDUCTION
 >> SRW_TAC [][SUB_THM, SUB_VAR]
 >> Q.EXISTS_TAC ‘v INSERT FV x UNION FV y’
 >> SRW_TAC [][SUB_THM]
 >> Cases_on ‘v IN FV y’
 >> SRW_TAC [][SUB_THM, lemma14c, lemma14b]
QED

Theorem swap_eq_3substs :
    z # (M :'a CCS) /\ x <> z /\ y <> z ==>
    tpm [(x,y)] M = [var y/z] ([var x/y] ([var z/x] M))
Proof
    SRW_TAC [][GSYM fresh_tpm_subst]
 >> ‘tpm [(x,y)] (tpm [(z,x)] M) =
     tpm [(swapstr x y z, swapstr x y x)] (tpm [(x,y)] M)’
     by (SRW_TAC [][Once (GSYM pmact_sing_to_back), SimpLHS] \\
         SRW_TAC [][])
 >> POP_ASSUM SUBST_ALL_TAC
 >> SRW_TAC [][pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    alpha-convertibility results
   ---------------------------------------------------------------------- *)

Theorem SIMPLE_ALPHA :
    y # (u :'a CCS) ==> !x. rec x u = rec y ([var y/x] u)
Proof
    SRW_TAC [][GSYM fresh_tpm_subst]
 >> SRW_TAC [boolSimps.CONJ_ss][rec_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    size function
   ---------------------------------------------------------------------- *)

val size_exists =
    tm_recursion
        |> INST_TYPE [“:'r” |-> “:num”]
        |> SPEC_ALL
        |> Q.INST [‘A’ |-> ‘{}’, ‘apm’ |-> ‘discrete_pmact’,
                   ‘vr’ |-> ‘\s. 1’,
                   ‘nl’ |-> ‘1’,
                   ‘pf’ |-> ‘\m u E. m + 1’,
                   ‘sm’ |-> ‘\m n t1 t2. m + n + 1’,
                   ‘pr’ |-> ‘\m n t1 t2. m + n + 1’,
                   ‘rs’ |-> ‘\m L t. m + 1’,
                   ‘rl’ |-> ‘\m t rf. m + 1’,
                   ‘re’ |-> ‘\m v t. m + 1’]
        |> SIMP_RULE (srw_ss()) []

val size_def = new_specification("CCS_size_def", ["CCS_size"], size_exists);

Theorem size_thm[simp] = CONJUNCT1 size_def

Theorem size_tpm[simp] = GSYM (CONJUNCT2 size_def)

Theorem size_nonzero :
    !t :'a CCS. 0 < CCS_size t
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [ARITH_ss][]
QED

(* |- !t. CCS_size t <> 0 *)
Theorem size_nz =
    REWRITE_RULE [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] size_nonzero

Theorem size_vsubst[simp]:
    !M :'a CCS. CCS_size ([var v/u] M) = CCS_size M
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC ‘{u;v}’
 >> SRW_TAC [][SUB_VAR, SUB_THM]
QED

(* ----------------------------------------------------------------------
    CCS_Subst
   ---------------------------------------------------------------------- *)

Definition CCS_Subst :
    CCS_Subst E E' X = [E'/X] (E :'a CCS)
End

(* NOTE: “Y # E'” is additionally required in case of ‘rec’ *)
Theorem CCS_Subst_def :
   (CCS_Subst nil          E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2)  E' X = sum (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (par E1 E2)  E' X = par (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr L E)  E' X = restr L (CCS_Subst E E' X)) /\
   (CCS_Subst (relab E rf) E' X = relab   (CCS_Subst E E' X) rf) /\
   (CCS_Subst (var Y)      E' X = if (Y = X) then E' else (var Y)) /\
   (Y <> X /\ Y # E' ==>
    CCS_Subst (rec Y E)    E' X = rec Y (CCS_Subst E E' X))
Proof
    rw [CCS_Subst]
QED

val [CCS_Subst_nil,   CCS_Subst_prefix, CCS_Subst_sum, CCS_Subst_par,
     CCS_Subst_restr, CCS_Subst_relab,  CCS_Subst_var, CCS_Subst_rec] =
    map save_thm
        (combine (["CCS_Subst_nil",   "CCS_Subst_prefix",
                   "CCS_Subst_sum",   "CCS_Subst_par",
                   "CCS_Subst_restr", "CCS_Subst_relab",
                   "CCS_Subst_var",   "CCS_Subst_rec"],
                  CONJUNCTS CCS_Subst_def));

(* 1st fixed point of CCS_Subst *)
Theorem CCS_Subst_rec_fix[simp] :
    !X E E'. CCS_Subst (rec X E) E' X = rec X E
Proof
    rw [CCS_Subst] >> MATCH_MP_TAC lemma14b >> rw []
QED

(* 2nd fixed point of CCS_Subst *)
Theorem CCS_Subst_var_fix[simp] :
    !X E. CCS_Subst (var X) E X = E
Proof
    rw [CCS_Subst_var]
QED

(* 3rd fixed point of CCS_Subst *)
Theorem CCS_Subst_self[simp] :
    !X E. CCS_Subst E (var X) X = E
Proof
    rw [CCS_Subst]
QED

(* !t1 t2. (if T then t1 else t2) = t1) /\ (if F then t1 else t2) = t2) *)
Theorem CCS_COND_CLAUSES = INST_TYPE [“:'a” |-> “:'a CCS”] COND_CLAUSES

Theorem FV_SUBSET :
    !X E E'. FV (CCS_Subst E E' X) SUBSET (FV E) UNION (FV E')
Proof
    rw [CCS_Subst, FV_SUB]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV E’
 >> SET_TAC []
QED

Theorem FV_SUBSET' :
    !X E E'. FV (CCS_Subst E E' X) SUBSET (FV E DELETE X) UNION (FV E')
Proof
    rw [CCS_Subst, FV_SUB]
 >> ASM_SET_TAC []
QED

Theorem FV_SUBSET_REC :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E)
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] FV_SUBSET)
 >> ASM_SET_TAC [FV_thm]
QED

(* NOTE: this theorem is key to prove TRANS_FV *)
Theorem FV_SUBSET_REC' :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E DELETE X)
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] FV_SUBSET')
 >> ASM_SET_TAC [FV_thm]
QED

Theorem CCS_Subst_elim :
    !X E. X # E ==> !E'. (CCS_Subst E E' X = E)
Proof
    rw [CCS_Subst]
 >> MATCH_MP_TAC lemma14b >> art []
QED

Theorem CCS_Subst_FIX_IMP_NOTIN_FV :
    !X E. (!E'. CCS_Subst E E' X = E) ==> X NOTIN (FV E)
Proof
    rw [CCS_Subst]
 >> MATCH_MP_TAC SUB_FIX_IMP_NOTIN_FV >> rw []
QED

(* If E[t/X] = E[t'/X] for all t t', X must not be free in E *)
Theorem CCS_Subst_EQ_IMP_NOTIN_FV :
    !X E. (!E1 E2. CCS_Subst E E1 X = CCS_Subst E E2 X) ==> X NOTIN (FV E)
Proof
    rw [CCS_Subst]
 >> MATCH_MP_TAC SUB_EQ_IMP_NOTIN_FV >> rw []
QED

Theorem FV_REC_PREF :
    !X E u E'. FV (CCS_Subst E (rec X (prefix u E')) X) =
               FV (CCS_Subst E (rec X E') X)
Proof
    rw [CCS_Subst, FV_SUB]
QED

Theorem FV_REC_SUM :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 + E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    rw [CCS_Subst, FV_SUB] >> SET_TAC []
QED

Theorem FV_REC_PAR :
    !X E E1 E2. FV (CCS_Subst E (rec X (par E1 E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    rw [CCS_Subst, FV_SUB] >> SET_TAC []
QED

Theorem FV_SUBSET_lemma :
    !P X Y. FV P SUBSET {X} /\ Y <> X ==> Y # P
Proof
    rpt STRIP_TAC
 >> ‘Y IN {X}’ by METIS_TAC [SUBSET_DEF]
 >> fs []
QED

(* i.e. closed term *)
Definition IS_PROC_def :
    IS_PROC E <=> (FV E = EMPTY)
End

Overload closed = “IS_PROC”
Theorem closed_def = IS_PROC_def

Definition ALL_PROC_def :
    ALL_PROC Es <=> EVERY IS_PROC Es
End

Theorem IS_PROC_EL :
    !Es n. ALL_PROC Es /\ n < LENGTH Es ==> IS_PROC (EL n Es)
Proof
    RW_TAC list_ss [ALL_PROC_def, EVERY_MEM, MEM_EL]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> art []
QED

Theorem closed_nil[simp] :
    closed nil
Proof
    rw [closed_def]
QED

Theorem not_closed_var[simp] :
    ~closed (var X)
Proof
    rw [closed_def]
QED

Theorem IS_PROC_prefix[simp] :
    !P u. IS_PROC (prefix u P) <=> IS_PROC P
Proof
    RW_TAC std_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_sum[simp] :
    !P Q. IS_PROC (sum P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_par[simp] :
    !P Q. IS_PROC (par P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_restr[simp] :
    !P L. IS_PROC (restr L P) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

Theorem IS_PROC_relab[simp] :
    !P rf. IS_PROC (relab P rf) <=> IS_PROC P
Proof
    RW_TAC set_ss [IS_PROC_def, FV_thm]
QED

val PREF_ACT_exists =
    tm_recursion
        |> INST_TYPE [“:'r” |-> “:'a Action”]
        |> SPEC_ALL
        |> Q.INST [‘A’ |-> ‘{}’, ‘apm’ |-> ‘discrete_pmact’,
                   ‘vr’ |-> ‘\s. tau’,
                   ‘nl’ |-> ‘tau’,
                   ‘pf’ |-> ‘\m u E. u’, (* here *)
                   ‘sm’ |-> ‘\m n t1 t2. tau’,
                   ‘pr’ |-> ‘\m n t1 t2. tau’,
                   ‘rs’ |-> ‘\m L t. tau’,
                   ‘rl’ |-> ‘\m t rf. tau’,
                   ‘re’ |-> ‘\m v t. tau’]
        |> SIMP_RULE (srw_ss()) [];

local val lemma = Q.prove (‘?f. !u E. f (u..E) = u’,
                           METIS_TAC [PREF_ACT_exists]);
in
(* !u E. PREF_ACT (u..E) = u *)
val PREF_ACT_def = new_specification
  ("PREF_ACT_def", ["PREF_ACT"], lemma);
end

val PREF_PROC_exists =
    tm_recursion
        |> INST_TYPE [“:'r” |-> “:'a CCS”]
        |> SPEC_ALL
        |> Q.INST [‘A’ |-> ‘{}’,
                   ‘apm’ |-> ‘^t_pmact_t’,
                   ‘ppm’ |-> ‘pair_pmact string_pmact ^t_pmact_t’,
                   ‘vr’ |-> ‘\s. nil’,
                   ‘nl’ |-> ‘nil’,
                   ‘pf’ |-> ‘\m u E. E’, (* here *)
                   ‘sm’ |-> ‘\m n t1 t2. nil’,
                   ‘pr’ |-> ‘\m n t1 t2. nil’,
                   ‘rs’ |-> ‘\m L t. nil’,
                   ‘rl’ |-> ‘\m t rf. nil’,
                   ‘re’ |-> ‘\m v t. nil’]
        |> SIMP_RULE (srw_ss()) [];

local val lemma = Q.prove (‘?f. !u E. f (u..E) = E’,
                           METIS_TAC [PREF_PROC_exists]);
in
(* |- !u E. PREF_PROC (u..E) = E *)
val PREF_PROC_def = new_specification
  ("PREF_PROC_def", ["PREF_PROC"], lemma);
end

(* ----------------------------------------------------------------------
    Simultaneous substitution (using a finite map) - much more interesting
   ---------------------------------------------------------------------- *)

Overload fmFV = “supp (fm_pmact string_pmact ^t_pmact_t)”
Overload tmsFV = “supp (set_pmact ^t_pmact_t)”
Overload fmtpm = “fmpm string_pmact term_pmact”

Theorem strterm_fmap_supp:
    fmFV fmap = FDOM fmap ∪ tmsFV (FRANGE fmap)
Proof
    SRW_TAC [][fmap_supp]
QED

Theorem FINITE_strterm_fmap_supp[simp]:
    FINITE (fmFV fmap)
Proof
    SRW_TAC [][strterm_fmap_supp, supp_setpm] >> SRW_TAC [][]
QED

val lem1 = prove(
  ``∃a. ~(a ∈ supp (fm_pmact string_pmact ^t_pmact_t) fm)``,
  Q_TAC (NEW_TAC "z") `supp (fm_pmact string_pmact ^t_pmact_t) fm` THEN
  METIS_TAC []);

val supp_FRANGE = prove(
  ``~(x ∈ supp (set_pmact ^t_pmact_t) (FRANGE fm)) =
   ∀y. y ∈ FDOM fm ==> ~(x ∈ FV (fm ' y))``,
  SRW_TAC [][supp_setpm, finite_mapTheory.FRANGE_DEF] >> METIS_TAC []);

fun ex_conj1 thm = let
  val (v,c) = dest_exists (concl thm)
  val c1 = CONJUNCT1 (ASSUME c)
  val fm = mk_exists(v,concl c1)
in
  CHOOSE (v, thm) (EXISTS(fm,v) c1)
end

val supp_EMPTY = prove(
  ``(supp (set_pmact apm) {} = {})``,
  srw_tac [][EXTENSION] >> match_mp_tac notinsupp_I >>
  qexists_tac `{}` >> srw_tac [][support_def]);

Theorem lem2[local] :
    ∀fm. FINITE (tmsFV (FRANGE fm))
Proof
    srw_tac [][supp_setpm] >> srw_tac [][]
QED

val ordering = prove(
  ``(∃f. P f) <=> (∃f. P (combin$C f))``,
  srw_tac [][EQ_IMP_THM] >-
    (qexists_tac `λx y. f y x` >> srw_tac [ETA_ss][combinTheory.C_DEF]) >>
  metis_tac [])

Theorem notin_frange:
    v ∉ tmsFV (FRANGE p) <=> ∀y. y ∈ FDOM p ==> v ∉ FV (p ' y)
Proof
    srw_tac [][supp_setpm, EQ_IMP_THM, finite_mapTheory.FRANGE_DEF]
 >> metis_tac []
QED

val ssub_exists =
    parameter_tm_recursion
        |> INST_TYPE [“:'r” |-> “:'a CCS”, “:'q” |-> “:string |-> 'a CCS”]
        |> Q.INST [‘A’ |-> ‘{}’, ‘apm’ |-> ‘^t_pmact_t’,
                   ‘ppm’ |-> ‘fm_pmact string_pmact ^t_pmact_t’,
                   ‘vr’ |-> ‘\s fm. if s IN FDOM fm then fm ' s else var s’,
                   ‘re’ |-> ‘\r v t fm. rec v (r fm)’,
                   ‘nl’ |-> ‘\r. nil’,
                   ‘pf’ |-> ‘\r u t fm. prefix u (r fm)’,
                   ‘sm’ |-> ‘\r1 r2 t1 t2 fm. r1 fm + r2 fm’,
                   ‘pr’ |-> ‘\r1 r2 t1 t2 fm. r1 fm || r2 fm’,
                   ‘rs’ |-> ‘\r L t fm. restr L (r fm)’,
                   ‘rl’ |-> ‘\r t rf fm. relab (r fm) rf’]
        |> SIMP_RULE (srw_ss()) [tpm_COND, strterm_fmap_supp, lem2,
                                 FAPPLY_eqv_lswapstr, supp_fresh,
                                 pmact_sing_inv, fnpm_def,
                                 fmpm_FDOM, notin_frange]
        |> SIMP_RULE (srw_ss()) [Once ordering]
        |> CONV_RULE (DEPTH_CONV (rename_vars [("p", "fm")]))
        |> prove_alpha_fcbhyp {ppm = “fm_pmact string_pmact ^t_pmact_t”,
                               rwts = [notin_frange, strterm_fmap_supp],
                               alphas = [tpm_ALPHA]};

val ssub_def = new_specification ("ssub_def", ["ssub"], ssub_exists)

(* |- (!s fm. ssub fm (var s) = if s IN FDOM fm then fm ' s else var s) /\
      (!fm. ssub fm nil = nil) /\ (!x fm t. ssub fm (x..t) = x..ssub fm t) /\
      (!fm t t'. ssub fm (t' + t) = ssub fm t' + ssub fm t) /\
      (!fm t t'. ssub fm (t' || t) = ssub fm t' || ssub fm t) /\
      (!x fm t. ssub fm (restr x t) = restr x (ssub fm t)) /\
      (!x fm t. ssub fm (relab t x) = relab (ssub fm t) x) /\
      !v fm t.
        v NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> v # fm ' y) ==>
        ssub fm (rec v t) = rec v (ssub fm t)
 *)
Theorem ssub_thm[simp] = CONJUNCT1 ssub_def

val _ = overload_on ("'", “ssub”);

val tpm_ssub = save_thm("tpm_ssub", CONJUNCT2 ssub_def);

Theorem single_ssub :
    !N. (FEMPTY |+ (s,M)) ' N = [M/s] N
Proof
    HO_MATCH_MP_TAC nc_INDUCTION >> Q.EXISTS_TAC `s INSERT FV M`
 >> SRW_TAC [][SUB_VAR, SUB_THM]
QED

Theorem in_fmap_supp:
    x IN fmFV fm <=> x IN FDOM fm \/ ?y. y IN FDOM fm /\ x IN FV (fm ' y)
Proof
    SRW_TAC [][strterm_fmap_supp, nomsetTheory.supp_setpm]
 >> SRW_TAC [boolSimps.DNF_ss][finite_mapTheory.FRANGE_DEF]
 >> METIS_TAC []
QED

Theorem not_in_fmap_supp[simp]:
    x NOTIN fmFV fm <=> x NOTIN FDOM fm /\ !y. y IN FDOM fm ==> x NOTIN FV (fm ' y)
Proof
    METIS_TAC [in_fmap_supp]
QED

Theorem ssub_14b:
    !t. DISJOINT (FV t) (FDOM phi) ==> (phi : string |-> 'a CCS) ' t = t
Proof
    HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘fmFV phi’
 >> SRW_TAC [][DISJOINT_DEF, SUB_THM, SUB_VAR, pred_setTheory.EXTENSION]
 >> METIS_TAC []
QED

Theorem ssub_value :
    FV t = EMPTY ==> (phi : string |-> 'a CCS) ' t = t
Proof
    SRW_TAC [][ssub_14b]
QED

(* |- !t phi. closed t ==> phi ' t = t *)
Theorem ssub_value' =
        ssub_value |> REWRITE_RULE [GSYM closed_def] |> GEN_ALL

Theorem ssub_FEMPTY[simp]:
    !t. (FEMPTY :string |-> 'a CCS) ' t = t
Proof
    HO_MATCH_MP_TAC simple_induction >> SRW_TAC [][]
QED

Theorem FV_ssub :
    !fm N. (!y. y IN FDOM fm ==> FV (fm ' y) = {}) ==>
           FV (fm ' N) = FV N DIFF FDOM fm
Proof
    rpt STRIP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [SUB_VAR, SUB_THM, ssub_thm]
 >> SET_TAC []
QED

Theorem fresh_ssub:
    !N. y NOTIN FV N /\ (!k :string. k IN FDOM fm ==> y # fm ' k) ==> y # fm ' N
Proof
    ho_match_mp_tac nc_INDUCTION
 >> qexists ‘fmFV fm’ >> rw [] >> metis_tac[]
QED

Theorem ssub_SUBST :
    !M. (!k. k IN FDOM fm ==> v # fm ' k) /\ v NOTIN FDOM fm ==>
        fm ' ([N/v] M) = [fm ' N/v] (fm ' M)
Proof
    ho_match_mp_tac nc_INDUCTION
 >> qexists ‘fmFV fm UNION {v} UNION FV N’
 >> rw [] >> rw [lemma14b, SUB_VAR]
 >> gvs [DECIDE “~p \/ q <=> p ==> q”, PULL_FORALL]
 >> rename1 ‘y # N’
 >> ‘y # fm ' N’ suffices_by simp[SUB_THM]
 >> irule fresh_ssub >> simp []
QED

(* |- !v fm t.
        v NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> v # fm ' y) ==>
        fm ' (rec v t) = rec v (fm ' t)
 *)
Theorem ssub_rec = List.nth(CONJUNCTS ssub_thm, 7)

Theorem ssub_update_apply_SUBST :
    !M. (!k. k IN FDOM fm ==> v # fm ' k) /\ v NOTIN FDOM fm /\
        DISJOINT (FDOM fm) (FV N) ==>
        (fm |+ (v,N)) ' M = fm ' ([N/v] M)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘v INSERT fmFV fm UNION FV M UNION FV N’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM ssub_14b) \\
     rw [GSYM DISJOINT_DEF, Once DISJOINT_SYM])
 >> rename1 ‘y # N’
 >> Suff ‘(fm |+ (v,N)) ' (rec y M') = rec y ((fm |+ (v,N)) ' M')’ >- rw []
 >> MATCH_MP_TAC ssub_rec
 >> rw [FAPPLY_FUPDATE_THM]
QED

(* A combined version of ssub_update_apply_SUBST and ssub_SUBST *)
Theorem ssub_update_apply_SUBST' :
    !M. (!k. k IN FDOM fm ==> v # fm ' k) /\ v NOTIN FDOM fm /\
        DISJOINT (FDOM fm) (FV N) ==>
        (fm |+ (v,N)) ' M = [fm ' N/v] (fm ' M)
Proof
    rpt STRIP_TAC
 >> Know ‘[fm ' N/v] (fm ' M) = fm ' ([N/v] M)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ]  \\
     MATCH_MP_TAC ssub_SUBST >> art [])
 >> Rewr'
 >> MATCH_MP_TAC ssub_update_apply_SUBST >> art []
QED

Theorem FEMPTY_update_apply :
    !M. (FEMPTY |+ (v,N)) ' M = [N/v] M
Proof
    Q.X_GEN_TAC ‘M’
 >> ‘[N/v] M = FEMPTY ' ([N/v] M)’ by rw []
 >> POP_ORW
 >> MATCH_MP_TAC ssub_update_apply_SUBST
 >> rw []
QED

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

Type transition[pp] = “:'a CCS -> 'a Action -> 'a CCS -> bool”

(* Inductive definition of the transition relation TRANS for CCS.
   TRANS: CCS -> Action -> CCS -> bool
 *)
Inductive TRANS :
    (!E u.                           TRANS (prefix u E) u E) /\         (* PREFIX *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E E') u E1) /\          (* SUM1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E' E) u E1) /\          (* SUM2 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E E') u (par E1 E')) /\ (* PAR1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E' E) u (par E' E1)) /\ (* PAR2 *)
    (!E l E1 E' E2. TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2
                ==> TRANS (par E E') tau (par E1 E2)) /\                (* PAR3 *)
    (!E u E' l L.   TRANS E u E' /\ ((u = tau) \/
                                     ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
                ==> TRANS (restr L E) u (restr L E')) /\                (* RESTR *)
    (!E u E' rf.    TRANS E u E'
                ==> TRANS (relab E rf) (relabel rf u) (relab E' rf)) /\ (* RELABELING *)
    (!E u X E1.     TRANS (CCS_Subst E (rec X E) X) u E1
                ==> TRANS (rec X E) u E1)                               (* REC *)
End

val _ =
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
        pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0,
                        TOK "->", BreakSpace(1,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "--", TeX = ("\\HOLTokenTransBegin", 1) };
val _ = TeX_notation { hol = "->", TeX = ("\\HOLTokenTransEnd", 1) };

(* The rules for the transition relation TRANS as individual theorems. *)
val [PREFIX, SUM1, SUM2, PAR1, PAR2, PAR3, RESTR, RELABELING, REC] =
    map save_thm
        (combine (["PREFIX", "SUM1", "SUM2", "PAR1", "PAR2", "PAR3", "RESTR",
                   "RELABELING", "REC"],
                  CONJUNCTS TRANS_rules));

(* Use SUB instead of CCS_Subst *)
Theorem REC' = REWRITE_RULE [CCS_Subst] REC

val TRANS_IND = save_thm ("TRANS_IND",
    TRANS_ind |> (Q.SPEC `P`) |> GEN_ALL);

(* The process nil has no transitions.
   !u E. ~TRANS nil u E
 *)
Theorem NIL_NO_TRANS =
    TRANS_cases |> Q.SPECL [‘nil’, ‘u’, ‘E’]
                |> REWRITE_RULE [CCS_distinct]
                |> Q.GENL [‘u’, ‘E’]

(* !u E. nil --u-> E <=> F *)
val NIL_NO_TRANS_EQF = save_thm (
   "NIL_NO_TRANS_EQF",
    Q.GENL [`u`, `E`] (EQF_INTRO (SPEC_ALL NIL_NO_TRANS)));

(* If a process can do an action, the process is not `nil`. *)
Theorem TRANS_IMP_NO_NIL :
    !E u E'. TRANS E u E' ==> E <> nil
Proof
    PROVE_TAC [NIL_NO_TRANS]
QED

(* An recursion variable has no transition.
   !X u E. ~TRANS (var X) u E
 *)
Theorem VAR_NO_TRANS =
    TRANS_cases |> Q.SPECL [`var X`, `u`, `E`]
                |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                |> Q.GENL [`X`, `u`, `E`]

(*---------------------------------------------------------------------------*
 *  The "I combinator" of CCS
 *---------------------------------------------------------------------------*)

val _ = hide "I";

(* cf. chap2Theory (examples/lambda/barendregt) *)
Definition I_def :
    I = rec "s" (var "s")
End

Theorem FV_I[simp] :
    FV I = {}
Proof
    SRW_TAC [][I_def]
QED

Theorem I_thm :
    !X. I = rec X (var X)
Proof
    rw [I_def, Once EQ_SYM_EQ]
 >> Cases_on ‘X = "s"’ >> rw [rec_eq_thm]
QED

Theorem SUB_I[simp] :
    [N/v] I = I
Proof
    rw [lemma14b]
QED

Theorem ssub_I :
    ssub fm I = I
Proof
    rw [ssub_value]
QED

Theorem I_cases :
    !Y P. I = rec Y P ==> P = var Y
Proof
    rw [I_def]
 >> qabbrev_tac ‘X = "x"’
 >> Cases_on ‘X = Y’ >> fs [rec_eq_thm]
QED

(* TRANSn is the labelled version of TRANS. *)
Inductive TRANSn :
    (!E u.            TRANSn 0 (prefix u E) u E) /\
    (!n E u E1 E'.    TRANSn n E u E1 ==> TRANSn (SUC n) (sum E E') u E1) /\
    (!n E u E1 E'.    TRANSn n E u E1 ==> TRANSn (SUC n) (sum E' E) u E1) /\
    (!n E u E1 E'.    TRANSn n E u E1 ==> TRANSn (SUC n) (par E E') u (par E1 E')) /\
    (!n E u E1 E'.    TRANSn n E u E1 ==> TRANSn (SUC n) (par E' E) u (par E' E1)) /\
    (!n E l E1 E' E2. TRANSn n E (label l) E1 /\ TRANSn n' E' (label (COMPL l)) E2
                  ==> TRANSn (SUC (MAX n n')) (par E E') tau (par E1 E2)) /\
    (!n E u E' l L.   TRANSn n E u E' /\ ((u = tau) \/
                                          ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
                  ==> TRANSn (SUC n) (restr L E) u (restr L E')) /\
    (!n E u E' rf.    TRANSn n E u E'
                  ==> TRANSn (SUC n) (relab E rf) (relabel rf u) (relab E' rf)) /\
    (!n E u X E1.     TRANSn n (CCS_Subst E (rec X E) X) u E1
                  ==> TRANSn (SUC n) (rec X E) u E1)
End

(* The rules for the transition relation TRANS as individual theorems. *)
val [PREFIXn, SUM1n, SUM2n, PAR1n, PAR2n, PAR3n, RESTRn, RELABELINGn, RECn] =
    map save_thm
        (combine (["PREFIXn", "SUM1n", "SUM2n", "PAR1n", "PAR2n", "PAR3n",
                   "RESTRn", "RELABELINGn", "RECn"],
                  CONJUNCTS TRANSn_rules));

Theorem TRANS0_cases :
    !E u E0. TRANSn 0 E u E0 <=> E = prefix u E0
Proof
    rw [Once TRANSn_cases]
QED

Theorem RECn_cases_EQ =
    TRANSn_cases |> Q.SPECL [‘n’, `rec X E`]
                 |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                 |> Q.SPECL [`u`, `E'`]
                 |> Q.GENL [‘n’, `X`, `E`, `u`, `E'`]

Theorem RECn_cases = EQ_IMP_LR RECn_cases_EQ

Theorem TRANS0_REC_EQ :
    !X E u E'. TRANSn 0 (rec X E) u E' <=> F
Proof
    rw [TRANS0_cases]
QED

Theorem TRANSn_REC_EQ :
    !n X E u E'. TRANSn (SUC n) (rec X E) u E' <=>
                 TRANSn n (CCS_Subst E (rec X E) X) u E'
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- PURE_ONCE_REWRITE_TAC [RECn]
 >> PURE_ONCE_REWRITE_TAC [RECn_cases_EQ]
 >> rpt STRIP_TAC
 >> fs [rec_eq_thm, CCS_Subst]
 >> rename1 ‘X <> Y’
 >> rename1 ‘X # P’
 >> Q.PAT_X_ASSUM ‘n = n'’ (fs o wrap o SYM)
 (* stage work *)
 >> rw [fresh_tpm_subst]
 >> Q.ABBREV_TAC ‘E = [var X/Y] P’
 >> Know ‘rec X E = rec Y ([var Y/X] E)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA \\
     rw [Abbr ‘E’, FV_SUB])
 >> Rewr'
 >> rw [Abbr ‘E’]
 >> Know ‘[var Y/X] ([var X/Y] P) = P’
 >- (MATCH_MP_TAC lemma15b >> art [])
 >> Rewr'
 >> Suff ‘[rec Y P/X] ([var X/Y] P) = [rec Y P/Y] P’
 >- rw []
 >> MATCH_MP_TAC lemma15a >> art []
QED

Theorem TRANSn_REC_EQ' = REWRITE_RULE [CCS_Subst] TRANSn_REC_EQ

Theorem I_NO_TRANSn_lemma[local] :
    !X u E n. ~TRANSn n (rec X (var X)) u E
Proof
    Induct_on ‘n’
 >- rw [TRANS0_REC_EQ]
 >> rw [TRANSn_REC_EQ']
QED

(* |- !u E n. ~TRANSn n I u E *)
Theorem I_NO_TRANSn = REWRITE_RULE [GSYM I_thm] I_NO_TRANSn_lemma

Theorem TRANS_imp_TRANSn :
    !E u E'. TRANS E u E' ==> ?n. TRANSn n E u E'
Proof
    HO_MATCH_MP_TAC TRANS_ind >> rw [] (* 10 subgoals *)
 >- (Q.EXISTS_TAC ‘0’ >> rw [PREFIXn])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [SUM1n])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [SUM2n])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [PAR1n])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [PAR2n])
 >- (Q.EXISTS_TAC ‘SUC (MAX n n')’ \\
     MATCH_MP_TAC PAR3n >> Q.EXISTS_TAC ‘l’ >> rw [])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [RESTRn])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [RESTRn])
 >- (Q.EXISTS_TAC ‘SUC n’ >> rw [RELABELINGn])
 >> (Q.EXISTS_TAC ‘SUC n’ >> rw [RECn])
QED

Theorem TRANSn_imp_TRANS :
    !n E u E'. TRANSn n E u E' ==> TRANS E u E'
Proof
    HO_MATCH_MP_TAC TRANSn_ind >> rw [] (* 10 subgoals *)
 >- (rw [PREFIX])
 >- (rw [SUM1])
 >- (rw [SUM2])
 >- (rw [PAR1])
 >- (rw [PAR2])
 >- (MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC ‘l’ >> rw [])
 >- (rw [RESTR])
 >- (rw [RESTR])
 >- (rw [RELABELING])
 >> (rw [REC])
QED

Theorem TRANS_iff_TRANSn :
    !E u E'. TRANS E u E' <=> ?n. TRANSn n E u E'
Proof
    rpt GEN_TAC >> EQ_TAC
 >- rw [TRANS_imp_TRANSn]
 >> STRIP_TAC
 >> MATCH_MP_TAC TRANSn_imp_TRANS
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

(* NOTE: This proof method based on ‘TRANSn’ is learnt from Ian Shillito. *)
Theorem I_NO_TRANS :
    !X u E. ~TRANS I u E
Proof
    rw [TRANS_iff_TRANSn, I_NO_TRANSn]
QED

(******************************************************************************)
(*                                                                            *)
(*                The transitions of prefixed term                            *)
(*                                                                            *)
(******************************************************************************)

(* !u E u' E'. TRANS (prefix u E) u' E' <=> (u' = u) /\ (E' = E) *)
Theorem TRANS_PREFIX_EQ =
        TRANS_cases |> Q.SPECL [‘prefix u E’, ‘u'’, ‘E'’]
                    |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                    |> ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]
                    |> Q.GENL [‘u’, ‘E’, ‘u'’, ‘E'’]

(* !u E u' E'. u..E --u'-> E' ==> (u' = u) /\ (E' = E) *)
val TRANS_PREFIX = save_thm (
   "TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

(* !P P' u P''.
         P + P' --u-> P'' <=>
         (?E E'. (P = E /\ P' = E') /\ E --u-> P'') \/
          ?E E'. (P = E' /\ P' = E) /\ E --u-> P''
 *)
Theorem SUM_cases_EQ =
        TRANS_cases |> Q.SPECL [‘sum P P'’, ‘u’, ‘P''’]
                    |> REWRITE_RULE [CCS_distinct', CCS_one_one]
                    |> Q.GENL [‘P’, ‘P'’, ‘u’, ‘P''’]

val SUM_cases = save_thm (
   "SUM_cases", EQ_IMP_LR SUM_cases_EQ);

Theorem TRANS_SUM_EQ :
    !E E' u E''. TRANS (sum E E') u E'' <=> TRANS E u E'' \/ TRANS E' u E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC SUM_cases >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* 2 sub-goals here *)
      [ MATCH_MP_TAC SUM1 >> art [],
        MATCH_MP_TAC SUM2 >> art [] ] ]
QED

(* for CCS_TRANS_CONV *)
val TRANS_SUM_EQ' = store_thm (
   "TRANS_SUM_EQ'",
  ``!E1 E2 u E. TRANS (sum E1 E2) u E <=> TRANS E1 u E \/ TRANS E2 u E``,
    REWRITE_TAC [TRANS_SUM_EQ]);

val TRANS_SUM = save_thm (
   "TRANS_SUM", EQ_IMP_LR TRANS_SUM_EQ);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' <=> TRANS (sum E' E) u E''``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM2, MATCH_MP_TAC SUM1 ] \\
      art [] ]);

val TRANS_ASSOC_EQ = store_thm ("TRANS_ASSOC_EQ",
  ``!E E' E'' E1 u. TRANS (sum (sum E E') E'') u E1 <=> TRANS (sum E (sum E' E'')) u E1``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM1 ] \\
        art [],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC SUM2 >> MATCH_MP_TAC SUM2 \\
        art [] ],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM >|
      [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1 \\
        art [],
        IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
        [ MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1,
          MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2,
          MATCH_MP_TAC SUM2 ] >> art [] ] ]);

val TRANS_ASSOC_RL = save_thm (
   "TRANS_ASSOC_RL", EQ_IMP_RL TRANS_ASSOC_EQ);

val TRANS_SUM_NIL_EQ = store_thm (
   "TRANS_SUM_NIL_EQ",
  ``!E u E'. TRANS (sum E nil) u E' <=> TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM \\
      IMP_RES_TAC NIL_NO_TRANS,
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

(* !E u E'. E + nil --u-> E' ==> E --u-> E' *)
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL", EQ_IMP_LR TRANS_SUM_NIL_EQ);

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM,
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

val TRANS_P_SUM_P = save_thm
  ("TRANS_P_SUM_P", EQ_IMP_LR TRANS_P_SUM_P_EQ);

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
    Q.GENL [`P`, `P'`, `u`, `P''`]
        (REWRITE_RULE [CCS_distinct', CCS_one_one]
                      (Q.SPECL [`par P P'`, `u`, `P''`] TRANS_cases)));

val PAR_cases = save_thm ("PAR_cases", EQ_IMP_LR PAR_cases_EQ);

(* NOTE: the shape of this theorem can be easily derived from above definition
   by replacing REWRITE_RULE with SIMP_RULE, however the inner existential
   variable (E1) has a different name. *)
Theorem TRANS_PAR_EQ :
    !E E' u E''. TRANS (par E E') u E'' <=>
                 (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
                 (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
                 (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
                            TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2)
Proof
    rpt GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC PAR_cases >| (* 3 sub-goals here *)
      [ (* goal 1.1 *)
        DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.2 *)
        DISJ2_TAC >> DISJ1_TAC \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 1.3 *)
        DISJ2_TAC >> DISJ2_TAC \\
        take [`E1`, `E2`, `l`] >> art [] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] (* 3 sub-goals, same initial tactics *)
   >| [ MATCH_MP_TAC PAR1 >> art [],
        MATCH_MP_TAC PAR2 >> art [],
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ] ]
QED

val TRANS_PAR = save_thm ("TRANS_PAR", EQ_IMP_LR TRANS_PAR_EQ);

val TRANS_PAR_P_NIL = store_thm ("TRANS_PAR_P_NIL",
  ``!E u E'. TRANS (par E nil) u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ Q.EXISTS_TAC `E1` >> art [],
      IMP_RES_TAC NIL_NO_TRANS,
      IMP_RES_TAC NIL_NO_TRANS ]);

val TRANS_PAR_NO_SYNCR = store_thm ("TRANS_PAR_NO_SYNCR",
  ``!(l :'a Label) l'. l <> COMPL l' ==>
        !E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E'')``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR (* 3 sub-goals here *)
 >| [ IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_11 \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM (ASSUME ``(l'' :'a Label) = l``),
                       SYM (ASSUME ``COMPL (l'' :'a Label) = l'``), COMPL_COMPL_LAB]
                      (ASSUME ``~(l = COMPL (l' :'a Label))``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm (
   "RESTR_cases_EQ",
    Q.GENL [`P'`, `u`, `L`, `P`]
           (REWRITE_RULE [CCS_distinct', CCS_one_one, Action_distinct, Action_11]
                         (Q.SPECL [`restr L P`, `u`, `P'`] TRANS_cases)));

val RESTR_cases = save_thm (
   "RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

Theorem TRANS_RESTR_EQ :
    !E L u E'.
     TRANS (restr L E) u E' <=>
     ?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
             ((u = tau) \/ ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
Proof
  let val a1 = ASSUME ``(u :'a Action) = tau``
      and a2 = ASSUME ``u = label (l :'a Label)``
      and a3 = ASSUME ``TRANS E'' u E'''``
      and a4 = ASSUME ``TRANS E u E''``
  in
    rpt GEN_TAC
 >> EQ_TAC >| (* two goals here *)
    [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC RESTR_cases \\ (* two sub-goals here, first two steps are shared *)
      take [`E'''`, `l`] >|
      [ (* goal 1.1 *)
        art [REWRITE_RULE [a1] a3],
        (* goal 1.2 *)
        art [REWRITE_RULE [a2] a3] ],
      (* case 2 (RL) *)
      STRIP_TAC >> art [] >| (* two sub-goals here *)
      [ (* sub-goal 2.1 *)
        MATCH_MP_TAC RESTR \\
        art [REWRITE_RULE [a1] a4],
        (* sub-goal 2.2 *)
        MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` \\
        art [REWRITE_RULE [a2] a4] ] ]
  end
QED

val TRANS_RESTR = save_thm (
   "TRANS_RESTR", EQ_IMP_LR TRANS_RESTR_EQ);

val TRANS_P_RESTR = store_thm (
   "TRANS_P_RESTR",
  ``!E u E' L. TRANS (restr L E) u (restr L E') ==> TRANS E u E'``,
  let
      val thm = REWRITE_RULE [CCS_one_one]
                  (ASSUME ``restr (L :'a Label set) E' = restr L E''``)
  in
      rpt STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'a Action) = tau``) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'a Action) = label l``) [thm]
      ]
  end);

val RESTR_NIL_NO_TRANS = store_thm ("RESTR_NIL_NO_TRANS",
  ``!(L :'a Label set) u E. ~(TRANS (restr L nil) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR (* two sub-goals here, but same proofs *)
 >> IMP_RES_TAC NIL_NO_TRANS);

val TRANS_IMP_NO_RESTR_NIL = store_thm ("TRANS_IMP_NO_RESTR_NIL",
  ``!E u E'. TRANS E u E' ==> !L. ~(E = restr L nil)``,
    rpt STRIP_TAC
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L nil``]
                             (ASSUME ``TRANS E u E'``))
 >> IMP_RES_TAC RESTR_NIL_NO_TRANS);

val TRANS_RESTR_NO_NIL = store_thm ("TRANS_RESTR_NO_NIL",
  ``!E L u E'. TRANS (restr L E) u (restr L E') ==> ~(E = nil)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RESTR
 >> ASSUME_TAC (REWRITE_RULE [ASSUME ``E = nil``]
                             (ASSUME ``TRANS E u E''``))
 >> IMP_RES_TAC NIL_NO_TRANS);

val RESTR_LABEL_NO_TRANS = store_thm ("RESTR_LABEL_NO_TRANS",
  ``!(l :'a Label) L. (l IN L) \/ ((COMPL l) IN L) ==>
                      (!E u E'. ~(TRANS (restr L (prefix (label l) E)) u E'))``,
    rpt STRIP_TAC (* 2 goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'a Action) = label l``)),
        (* goal 1.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'a Action) = label l'``, Action_11]
                              (ASSUME ``(u :'a Action) = label l``)]
                (ASSUME ``~((l' :'a Label) IN L)``))
              (ASSUME ``(l :'a Label) IN L``)) ],
      (* goal 2 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'a Action) = label l``)),
        (* goal 2.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'a Action) = label l'``, Action_11]
                              (ASSUME ``(u :'a Action) = label l``)]
                (ASSUME ``~((COMPL (l' :'a Label)) IN L)``))
              (ASSUME ``(COMPL (l :'a Label)) IN L``)) ] ]);

(* |- !E rf u P.
         relab E rf --u-> P <=>
         ?E' u' E'' rf'.
             ((E = E') /\ (rf = rf')) /\ (u = relabel rf' u') /\
             (P = relab E'' rf') /\ E' --u'-> E''
 *)
val RELAB_cases_EQ = save_thm
  ("RELAB_cases_EQ",
    TRANS_cases |> (Q.SPEC `relab E rf`)
                |> (REWRITE_RULE [CCS_distinct', CCS_one_one])
                |> (Q.SPECL [`u`, `P`])
                |> (Q.GENL [`E`, `rf`, `u`, `P`]));

val RELAB_cases = save_thm ("RELAB_cases", EQ_IMP_LR RELAB_cases_EQ);

Theorem TRANS_RELAB_EQ :
    !E rf u E'. TRANS (relab E rf) u E' <=>
                ?u' E''. (u = relabel rf u') /\
                         (E' = relab E'' rf) /\ TRANS E u' E''
Proof
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC RELAB_cases \\
      take [`u'`, `E'''`] >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC RELABELING \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]
QED

val TRANS_RELAB = save_thm ("TRANS_RELAB", EQ_IMP_LR TRANS_RELAB_EQ);

val TRANS_RELAB_labl = save_thm ("TRANS_RELAB_labl",
    Q.GENL [`E`, `labl`] (Q.SPECL [`E`, `RELAB labl`] TRANS_RELAB));

val RELAB_NIL_NO_TRANS = store_thm ("RELAB_NIL_NO_TRANS",
  ``!(rf :'a Relabeling) u E. ~(TRANS (relab nil rf) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RELAB
 >> IMP_RES_TAC NIL_NO_TRANS);

(* |- !X E u E'.
         rec X E --u-> E' <=>
         ?E'' X'. ((X = X') /\ (E = E'')) /\ [rec X' E''/X'] E'' --u-> E'
 *)
val REC_cases_EQ = save_thm
  ("REC_cases_EQ",
    TRANS_cases |> (Q.SPEC `rec X E`)
                |> (REWRITE_RULE [CCS_distinct', CCS_one_one])
                |> (Q.SPECL [`u`, `E'`])
                |> (Q.GENL [`X`, `E`, `u`, `E'`]));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

Theorem TRANS_REC_EQ :
    !X E u E'. TRANS (rec X E) u E' <=> TRANS (CCS_Subst E (rec X E) X) u E'
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- PURE_ONCE_REWRITE_TAC [REC]
 >> PURE_ONCE_REWRITE_TAC [REC_cases_EQ]
 >> rpt STRIP_TAC
 >> fs [rec_eq_thm, CCS_Subst]
 >> rename1 ‘X <> Y’
 >> rename1 ‘X # P’
 (* stage work *)
 >> rw [fresh_tpm_subst]
 >> Q.ABBREV_TAC ‘E = [var X/Y] P’
 >> Know ‘rec X E = rec Y ([var Y/X] E)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA \\
     rw [Abbr ‘E’, FV_SUB])
 >> Rewr'
 >> rw [Abbr ‘E’]
 >> Know ‘[var Y/X] ([var X/Y] P) = P’
 >- (MATCH_MP_TAC lemma15b >> art [])
 >> Rewr'
 >> Suff ‘[rec Y P/X] ([var X/Y] P) = [rec Y P/Y] P’
 >- rw []
 >> MATCH_MP_TAC lemma15a >> art []
QED

(* |- !X E u E'. rec X E --u-> E' <=> [rec X E/X] E --u-> E' *)
Theorem TRANS_REC_EQ' = REWRITE_RULE [CCS_Subst] TRANS_REC_EQ

(* |- !X E u E'. rec X E --u-> E' ==> CCS_Subst E (rec X E) X --u-> E' *)
Theorem TRANS_REC = EQ_IMP_LR TRANS_REC_EQ

(* |- !X E u E'. rec X E --u-> E' ==> [rec X E/X] E --u-> E' *)
Theorem TRANS_REC' = EQ_IMP_LR TRANS_REC_EQ'

Theorem REC_VAR_NO_TRANS :
    !X Y u E. ~TRANS (rec X (var Y)) u E
Proof
    rpt GEN_TAC
 >> Cases_on ‘X = Y’
 >- rw [GSYM I_thm, I_NO_TRANS]
 >> rw [TRANS_REC_EQ', VAR_NO_TRANS]
QED

(* NOTE: This is the *ONLY* theorem for which the induction principle of
  ‘TRANS’ is needed. And this theorem (and the next TRANS_PROC) is only needed
   in MultivariateScript.sml (so even the univariate "Unique solution" theorems
   do not need this theorem). Thus, if ‘TRANS’ were defined by CoInductive,
  "almost all" CCS theorems in this work, still hold.  -- Chun Tian, 11 gen 2024
 *)
Theorem TRANS_FV :
    !E u E'. TRANS E u E' ==> FV E' SUBSET (FV E)
Proof
    HO_MATCH_MP_TAC TRANS_IND (* strongind is useless *)
 >> RW_TAC set_ss [FV_thm] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `FV (CCS_Subst E (rec X E) X)`
 >> ASM_REWRITE_TAC [FV_SUBSET_REC']
QED

Theorem TRANS_PROC :
    !E u E'. TRANS E u E' /\ IS_PROC E ==> IS_PROC E'
Proof
    RW_TAC std_ss [IS_PROC_def]
 >> `FV E' SUBSET FV E` by PROVE_TAC [TRANS_FV]
 >> rfs []
QED

(* A modern name after ‘IS_PROC’ has been overloaded on ‘closed’. *)
Theorem TRANS_closed = TRANS_PROC

(* ----------------------------------------------------------------------
    Set up the recursion functionality in binderLib
   ---------------------------------------------------------------------- *)

val lemma = prove(
   “(!x y t. pmact apm [(x,y)] (h t) = h (tpm [(x,y)] t)) <=>
     !pi t. pmact apm pi (h t) = h (tpm pi t)”,
    simp_tac (srw_ss()) [EQ_IMP_THM]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> strip_tac >> Induct_on ‘pi’
 >> asm_simp_tac (srw_ss()) [pmact_nil, pairTheory.FORALL_PROD]
 >> srw_tac [][Once tpm_CONS] >> srw_tac [][GSYM pmact_decompose]);

Theorem tm_recursion_nosideset =
  tm_recursion |> Q.INST [‘A’ |-> ‘{}’] |> SIMP_RULE (srw_ss()) [lemma]

val term_info_string =
    "local\n\
    \fun k |-> v = {redex = k, residue = v}\n\
    \open binderLib\n\
    \val term_info = \n\
    \   {nullfv = “rec \"\" (var \"\") :'a CCS”,\n\
    \    pm_rewrites = [],\n\
    \    pm_constant = “(nomset$mk_pmact CCS$raw_tpm) :'a CCS pmact”,\n\
    \    fv_rewrites = [],\n\
    \    recursion_thm = SOME tm_recursion_nosideset,\n\
    \    binders = [(“CCS$rec :string -> 'a CCS -> 'a CCS”, 0, tpm_ALPHA)]}\n\
    \val _ = binderLib.type_db :=\n\
    \          Binarymap.insert(!binderLib.type_db,\n\
    \                           {Thy=\"CCS\", Name = \"CCS\"},\n\
    \                           binderLib.NTI term_info)\n\
    \in end;\n";

val _ = adjoin_after_completion (fn _ => PP.add_string term_info_string);

val _ = export_theory ();
val _ = html_theory "CCS";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).

 *)
