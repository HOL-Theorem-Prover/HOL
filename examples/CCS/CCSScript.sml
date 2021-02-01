(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib relationTheory optionTheory listTheory CCSLib;

local open termTheory; in end; (* for SUB's syntax only *)

val _ = new_theory "CCS";

val lset_ss = std_ss ++ PRED_SET_ss;

(******************************************************************************)
(*                                                                            *)
(*                           Labels and Actions                               *)
(*                                                                            *)
(******************************************************************************)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
Datatype: Label = name 'b | coname 'b
End

(* Define structural induction on labels
   !P. (!s. P (name s)) /\ (!s. P (coname s)) ==> !L. P L
 *)
val Label_induction = TypeBase.induction_of ``:'b Label``;

(* The structural cases theorem for the type Label
   !LL. (?s. LL = name s) \/ ?s. LL = coname s
 *)
val Label_cases = TypeBase.nchotomy_of ``:'b Label``;

(* The distinction and injectivity theorems for the type Label
   !a' a. name a <> coname a'
   (!a a'. (name a = name a') <=> (a = a')) /\
       !a a'. (coname a = coname a') <=> (a = a')
 *)
val Label_distinct = TypeBase.distinct_of ``:'b Label``;
val Label_distinct' = save_thm ("Label_distinct'", GSYM Label_distinct);

val Label_not_eq = save_thm (
   "Label_not_eq", STRIP_FORALL_RULE EQF_INTRO Label_distinct);

val Label_not_eq' = save_thm (
   "Label_not_eq'", STRIP_FORALL_RULE
                        (PURE_REWRITE_RULE [SYM_CONV ``name s = coname s'``])
                        Label_not_eq);

val Label_11 = TypeBase.one_one_of ``:'b Label``;

(* NEW: define the set of actions as the OPTION of Label *)
Type Action[pp] = ``:'b Label option``;

val _ = overload_on ("tau",   ``NONE :'b Action``);
val _ = overload_on ("label", ``SOME :'b Label -> 'b Action``);

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
   "Action_induction", INST_TYPE [``:'a`` |-> ``:'b Label``] option_induction);

(* The structural cases theorem for the type Action
   !AA. (AA = tau) \/ ?L. AA = label L
 *)
val Action_cases = save_thm (
   "Action_cases", INST_TYPE [``:'a`` |-> ``:'b Label``] option_nchotomy);

(* The distinction and injectivity theorems for the type Action
   !a. tau <> label a
   !a a'. (label a = label a') <=> (a = a')
 *)
val Action_distinct = save_thm (
   "Action_distinct", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_NONE_SOME);

val Action_distinct_label = save_thm (
   "Action_distinct_label", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_SOME_NONE);

val Action_11 = save_thm (
   "Action_11", INST_TYPE [``:'a`` |-> ``:'b Label``] SOME_11);

(* !A. A <> tau ==> ?L. A = label L *)
val Action_no_tau_is_Label = save_thm (
   "Action_no_tau_is_Label",
    Q.GEN `A` (DISJ_IMP (Q.SPEC `A` Action_cases)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val _ = overload_on ("LABEL", ``THE :'b Label option -> 'b Label``);

(* |- !x. LABEL (label x) = x *)
val LABEL_def = save_thm (
   "LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] THE_DEF);

(* |- (!x. IS_SOME (label x) <=> T) /\ (IS_SOME 't <=> F) *)
val IS_LABEL_def = save_thm (
   "IS_LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] IS_SOME_DEF);

val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_LAB_def = Define `(COMPL_LAB (name (s :'b)) = (coname s)) /\
                            (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm
  ("coname_COMPL", ``!(s :'b). coname s = COMPL (name s)``,
    REWRITE_TAC [COMPL_LAB_def]);

val COMPL_COMPL_LAB = store_thm (
   "COMPL_COMPL_LAB", ``!(l :'b Label). COMPL_LAB (COMPL_LAB l) = l``,
    Induct >> REWRITE_TAC [COMPL_LAB_def]);

(* Extend the complement to actions, COMPL_ACT: Action -> Action. *)
val COMPL_ACT_def = Define `
   (COMPL_ACT (label (l: 'b Label)) = label (COMPL l)) /\
   (COMPL_ACT tau = tau)`;

val _ = overload_on ("COMPL", ``COMPL_ACT``);
val _ = export_rewrites ["COMPL_ACT_def"];

Theorem COMPL_COMPL_ACT :
    !(a :'b Action). COMPL_ACT (COMPL_ACT a) = a
Proof
    Induct_on `a`
 >- REWRITE_TAC [COMPL_ACT_def]
 >> REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB]
QED

(* auxiliary theorem about complementary labels. *)
Theorem COMPL_THM :
    !(l :'b Label) s. (l <> name s ==> COMPL l <> coname s) /\
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

(* Relabeling function is subtype of `:'b Label -> 'b Label *)
val Is_Relabeling_def = Define `
    Is_Relabeling (f: 'b Label -> 'b Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling",
  ``?(f: 'b Label -> 'b Label). Is_Relabeling f``,
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
    !rf :'b Relabeling. Is_Relabeling (REP_Relabeling rf)
Proof
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> Q.EXISTS_TAC `rf`
 >> REWRITE_TAC []
QED

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `
   (relabel (rf :'b Relabeling) tau = tau) /\
   (relabel rf (label l) = label (REP_Relabeling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
Theorem Relab_label :
    !(rf :'b Relabeling) u l. (relabel rf u = label l) ==> ?l'. u = label l'
Proof
    Induct_on `u`
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``a :'b Label``
 >> REWRITE_TAC []
QED

(* If the renaming of an action is tau, that action is tau. *)
Theorem Relab_tau :
    !(rf :'b Relabeling) u. (relabel rf u = tau) ==> (u = tau)
Proof
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]
QED

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: ('b Label # 'b Label) list) l = l) /\
   (Apply_Relab ((newold: 'b Label # 'b Label) :: ls) l =
          if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

Theorem Apply_Relab_COMPL_THM :
    !labl (s: 'b). Apply_Relab labl (coname s) =
            COMPL (Apply_Relab labl (name s))
Proof
    Induct >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> rpt GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'b Label # 'b Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM >> art []
QED

Theorem IS_RELABELING :
    !labl :('b Label # 'b Label) list. Is_Relabeling (Apply_Relab labl)
Proof
    Induct
 >- REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def, COMPL_LAB_def]
 >> GEN_TAC
 >> REWRITE_TAC [Is_Relabeling_def, Apply_Relab_def]
 >> GEN_TAC
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'b Label # 'b Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> art [Apply_Relab_COMPL_THM]
QED

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label) list -> Relabeling
 *)
val RELAB_def = Define `
    RELAB (labl :('b Label # 'b Label) list) = ABS_Relabeling (Apply_Relab labl)`;

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
(*             Syntax of pure CCS ('a, 'b) (general formalization)            *)
(*                                                                            *)
(******************************************************************************)

(* Define the type of (pure) CCS agent expressions. *)
Datatype: CCS = nil
              | var 'a
              | prefix ('b Action) CCS
              | sum CCS CCS
              | par CCS CCS
              | restr (('b Label) set) CCS
              | relab CCS ('b Relabeling)
              | rec 'a CCS
End

val _ = TeX_notation { hol = "nil", TeX = ("\\ensuremath{\\mathbf{0}}", 1) };

(* compact representation for single-action restriction *)
val _ = overload_on ("nu", ``\(n :'b) P. restr {name n} P``);
val _ = overload_on ("nu", ``restr``);

val _ = add_rule {term_name = "nu", fixity = Closefix,
                  pp_elements = [TOK ("(" ^ UnicodeChars.nu), TM, TOK ")"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val _ = TeX_notation { hol = "(" ^ UnicodeChars.nu,
                       TeX = ("\\ensuremath{(\\nu}", 1) };

(* TODO: send to HOL's boolTheory *)
val _ = TeX_notation { hol = "(", TeX = ("\\ensuremath{(}", 1) };
val _ = TeX_notation { hol = ")", TeX = ("\\ensuremath{)}", 1) };
val _ = TeX_notation { hol = "=", TeX = ("\\ensuremath{=}", 1) };

(* disabled: this "\mu" is conflict with the \mu action used in CCS papers
val _ = overload_on ("mu", ``rec``);
val _ = Unicode.unicode_version { u = UnicodeChars.mu, tmnm = "mu" };
val _ = TeX_notation { hol = "mu", TeX = ("\\ensuremath{\\mu}", 1) };
 *)

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = TeX_notation { hol = "+", TeX = ("\\ensuremath{+}", 1) };

val _ = set_mapped_fixity { fixity = Infix(LEFT, 600),
                            tok = "||", term_name = "par" };

(* val _ = Unicode.unicode_version {u = UTF8.chr 0x007C, tmnm = "par"}; *)
val _ = TeX_notation { hol = "||", TeX = ("\\ensuremath{\\mid}", 1) };

val _ =
    add_rule { term_name = "prefix", fixity = Infix(RIGHT, 700),
        pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
        paren_style = OnlyIfNecessary,
        block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

val _ = TeX_notation { hol = "..", TeX = ("\\ensuremath{\\ldotp}", 1) };

(* Define structural induction on CCS agent expressions. *)
val CCS_induct = TypeBase.induction_of ``:('a, 'b) CCS``;

(* The structural cases theorem for the type CCS. *)
val CCS_cases = TypeBase.nchotomy_of ``:('a, 'b) CCS``;

(* Prove that the constructors of the type CCS are distinct. *)
val CCS_distinct = TypeBase.distinct_of ``:('a, 'b) CCS``;

(* size definition *)
val (CCS_size_tm, CCS_size_def) = TypeBase.size_of ``:('a, 'b) CCS``;

local
    val thm = CONJUNCTS CCS_distinct;
    val CCS_distinct_LIST = thm @ (map GSYM thm);
in
    val CCS_distinct' = save_thm ("CCS_distinct'", LIST_CONJ CCS_distinct_LIST);
end

Theorem CCS_distinct_exists :
    !p :('a, 'b) CCS. ?q. q <> p
Proof
    GEN_TAC >> Cases_on `p` >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `prefix a nil` >> REWRITE_TAC [CCS_distinct'])
 >> Q.EXISTS_TAC `nil`
 >> REWRITE_TAC [CCS_distinct]
QED

(* Prove that the constructors of the type CCS are one-to-one. *)
val CCS_11 = TypeBase.one_one_of ``:('a, 'b) CCS``;

(* Given any agent expression, define the substitution of an agent expression
   E' for an agent variable X.

   This works under the hypothesis that the Barendregt convention holds. *)
Definition CCS_Subst_def :
   (CCS_Subst nil          E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2)  E' X = sum (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (par E1 E2)  E' X = par (CCS_Subst E1 E' X)
                                      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr L E)  E' X = restr L (CCS_Subst E E' X)) /\
   (CCS_Subst (relab E rf) E' X = relab   (CCS_Subst E E' X) rf) /\
   (CCS_Subst (var Y)      E' X = if (Y = X) then E' else (var Y)) /\
   (CCS_Subst (rec Y E)    E' X = if (Y = X) then (rec Y E)
                                  else (rec Y (CCS_Subst E E' X)))
End

val [CCS_Subst_nil,   CCS_Subst_prefix, CCS_Subst_sum, CCS_Subst_par,
     CCS_Subst_restr, CCS_Subst_relab,  CCS_Subst_var, CCS_Subst_rec] =
    map save_thm
        (combine (["CCS_Subst_nil",   "CCS_Subst_prefix",
                   "CCS_Subst_sum",   "CCS_Subst_par",
                   "CCS_Subst_restr", "CCS_Subst_relab",
                   "CCS_Subst_var",   "CCS_Subst_rec"],
                  CONJUNCTS CCS_Subst_def));

(* `[E'/X] E`, learnt from <holdir>/examples/lambda/basics/termScript.sml *)
val _ = overload_on ("SUB", ``\E' X E. CCS_Subst E E' X``);

val _ = TeX_notation { hol = "[", TeX = ("\\ensuremath{[}", 1) };
val _ = TeX_notation { hol = "/", TeX = ("\\ensuremath{/}", 1) };
val _ = TeX_notation { hol = "]", TeX = ("\\ensuremath{]}", 1) };

(* Note that in the rec clause, if Y = X then all occurrences of Y in E are X
   and bound, so there exist no free variables X in E to be replaced with E'.
   Hence, the term rec Y E is returned.

   Below are two typical cases by CCS_Subst: *)

(* !X E E'. CCS_Subst (rec X E) E' X = rec X E (1st fixed point of CCS_Subst) *)
val CCS_Subst_rec_fix = save_thm (
   "CCS_Subst_rec_fix[simp]",
    Q.GENL [`X`, `E`, `E'`]
           (REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (rec X E) E' X``));

(* !X E. CCS_Subst (var X) E X = E             (2nd fixed point of CCS_Subst) *)
val CCS_Subst_var_fix = save_thm (
   "CCS_Subst_var_fix[simp]",
    Q.GENL [`X`, `E`]
           (REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (var X) E X``));

Theorem CCS_Subst_self[simp] :                    (* (3rd fixed point of CCS_Subst) *)
    !X E. CCS_Subst E (var X) X = E
Proof
    GEN_TAC >> Induct_on `E` >> RW_TAC std_ss [CCS_Subst_def]
QED

(* !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2) *)
val CCS_COND_CLAUSES = save_thm (
   "CCS_COND_CLAUSES", INST_TYPE [``:'a`` |-> ``:('a, 'b) CCS``] COND_CLAUSES);

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

val _ = type_abbrev_pp ("transition",
      ``:('a, 'b) CCS -> 'b Action -> ('a, 'b) CCS -> bool``);

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

val TRANS_IND = save_thm ("TRANS_IND",
    TRANS_ind |> (Q.SPEC `P`) |> GEN_ALL);

(* The process nil has no transitions.
   !u E. ~TRANS nil u E
 *)
val NIL_NO_TRANS = save_thm ("NIL_NO_TRANS",
    Q.GENL [`u`, `E`]
           (REWRITE_RULE [CCS_distinct]
                         (SPECL [``nil``, ``u :'b Action``, ``E :('a, 'b) CCS``] TRANS_cases)));

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
val VAR_NO_TRANS = save_thm ("VAR_NO_TRANS",
    Q.GENL [`X`, `u`, `E`]
           (REWRITE_RULE [CCS_distinct', CCS_11]
                         (Q.SPECL [`var X`, `u`, `E`] TRANS_cases)));

(* !u E u' E'. TRANS (prefix u E) u' E' = (u' = u) /\ (E' = E) *)
val TRANS_PREFIX_EQ = save_thm (
   "TRANS_PREFIX_EQ",
  ((Q.GENL [`u`, `E`, `u'`, `E'`]) o
   (ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]) o
   SPEC_ALL o
   (REWRITE_RULE [CCS_distinct', CCS_11]))
      (SPECL [``prefix (u :'b Action) E``, ``u' :'b Action``, ``E' :('a, 'b) CCS``]
             TRANS_cases));

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
val SUM_cases_EQ = save_thm (
   "SUM_cases_EQ",
    Q.GENL [`P`, `P'`, `u`, `P''`]
         (REWRITE_RULE [CCS_distinct', CCS_11]
                       (SPECL [``sum P P'``, ``u :'b Action``, ``P'' :('a, 'b) CCS``]
                              TRANS_cases)));

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
        (REWRITE_RULE [CCS_distinct', CCS_11]
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
  ``!(l :'b Label) l'. l <> COMPL l' ==>
        !E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E'')``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR (* 3 sub-goals here *)
 >| [ IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_distinct,
      IMP_RES_TAC TRANS_PREFIX >> IMP_RES_TAC Action_11 \\
      CHECK_ASSUME_TAC
        (REWRITE_RULE [SYM (ASSUME ``(l'' :'b Label) = l``),
                       SYM (ASSUME ``COMPL (l'' :'b Label) = l'``), COMPL_COMPL_LAB]
                      (ASSUME ``~(l = COMPL (l' :'b Label))``)) \\
      RW_TAC bool_ss [] ]);

val RESTR_cases_EQ = save_thm (
   "RESTR_cases_EQ",
    Q.GENL [`P'`, `u`, `L`, `P`]
           (REWRITE_RULE [CCS_distinct', CCS_11, Action_distinct, Action_11]
                         (Q.SPECL [`restr L P`, `u`, `P'`] TRANS_cases)));

val RESTR_cases = save_thm (
   "RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

Theorem TRANS_RESTR_EQ :
    !E L u E'.
     TRANS (restr L E) u E' <=>
     ?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
             ((u = tau) \/ ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
Proof
  let val a1 = ASSUME ``(u :'b Action) = tau``
      and a2 = ASSUME ``u = label (l :'b Label)``
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
      val thm = REWRITE_RULE [CCS_11] (ASSUME ``restr (L :'b Label set) E' = restr L E''``)
  in
      rpt STRIP_TAC \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'b Action) = tau``) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => t !~ ``(u :'b Action) = label l``) [thm]
      ]
  end);

val RESTR_NIL_NO_TRANS = store_thm ("RESTR_NIL_NO_TRANS",
  ``!(L :'b Label set) u E. ~(TRANS (restr L nil) u E)``,
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
  ``!(l :'b Label) L. (l IN L) \/ ((COMPL l) IN L) ==>
                      (!E u E'. ~(TRANS (restr L (prefix (label l) E)) u E'))``,
    rpt STRIP_TAC (* 2 goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'b Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'b Action) = label l``)),
        (* goal 1.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'b Action) = label l'``, Action_11]
                              (ASSUME ``(u :'b Action) = label l``)]
                (ASSUME ``~((l' :'b Label) IN L)``))
              (ASSUME ``(l :'b Label) IN L``)) ],
      (* goal 2 *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (REWRITE_RULE [ASSUME ``(u :'b Action) = tau``, Action_distinct]
                        (ASSUME ``(u :'b Action) = label l``)),
        (* goal 2.2 *)
        IMP_RES_TAC TRANS_PREFIX \\
        CHECK_ASSUME_TAC
          (MP (REWRITE_RULE
                [REWRITE_RULE [ASSUME ``(u :'b Action) = label l'``, Action_11]
                              (ASSUME ``(u :'b Action) = label l``)]
                (ASSUME ``~((COMPL (l' :'b Label)) IN L)``))
              (ASSUME ``(COMPL (l :'b Label)) IN L``)) ] ]);

(* |- !E rf u P.
         relab E rf --u-> P <=>
         ?E' u' E'' rf'.
             ((E = E') /\ (rf = rf')) /\ (u = relabel rf' u') /\
             (P = relab E'' rf') /\ E' --u'-> E''
 *)
val RELAB_cases_EQ = save_thm
  ("RELAB_cases_EQ",
    TRANS_cases |> (Q.SPEC `relab E rf`)
                |> (REWRITE_RULE [CCS_distinct', CCS_11])
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
  ``!(rf :'b Relabeling) u E. ~(TRANS (relab nil rf) u E)``,
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
                |> (REWRITE_RULE [CCS_distinct', CCS_11])
                |> (Q.SPECL [`u`, `E'`])
                |> (Q.GENL [`X`, `E`, `u`, `E'`]));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

Theorem TRANS_REC_EQ :
    !X E u E'. TRANS (rec X E) u E' <=> TRANS (CCS_Subst E (rec X E) X) u E'
Proof
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC_cases_EQ] \\
      rpt STRIP_TAC \\
      PURE_ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC] ]
QED

val TRANS_REC = save_thm ("TRANS_REC", EQ_IMP_LR TRANS_REC_EQ);

(**********************************************************************)
(*              Free and bound (recursion) variables                  *)
(**********************************************************************)

(* ('a, 'b) CCS -> 'a set (set of free variables) *)
Definition FV_def :
   (FV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (FV (prefix u p)        = FV p) /\
   (FV (sum p q)           = (FV p) UNION (FV q)) /\
   (FV (par p q)           = (FV p) UNION (FV q)) /\
   (FV (restr L p)         = FV p) /\
   (FV (relab p rf)        = FV p) /\
   (FV (var X)             = {X}) /\
   (FV (rec X p)           = (FV p) DELETE X)
End

(* broken into separate theorems *)
val [FV_nil,   FV_prefix, FV_sum, FV_par,
     FV_restr, FV_relab,  FV_var, FV_rec] =
    map save_thm
        (combine (["FV_nil",   "FV_prefix",
                   "FV_sum",   "FV_par",
                   "FV_restr", "FV_relab",
                   "FV_var",   "FV_rec"], CONJUNCTS FV_def));

Theorem FV_SUBSET :
    !X E E'. FV (CCS_Subst E E' X) SUBSET (FV E) UNION (FV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [FV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

(* This stronger result doesn't lead to a simpler proof
   of TRANS_FV, as FV_SUBSET_REC cannot be further improved *)
Theorem FV_SUBSET_PRO :
    !X E E'. FV (CCS_Subst E E' X) SUBSET ((FV E) DELETE X) UNION (FV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [FV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

Theorem FV_SUBSET_REC :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E)
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] FV_SUBSET)
 >> ASM_SET_TAC [FV_def]
QED

Theorem NOTIN_FV_lemma :
    !X E E'. X NOTIN FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def]
QED

Theorem FV_SUBSET_REC_PRO :
    !X E. FV (CCS_Subst E (rec X E) X) SUBSET (FV E) DELETE X
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`] FV_SUBSET_REC)
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `E`] NOTIN_FV_lemma)
 >> ASM_SET_TAC []
QED

Theorem TRANS_FV :
    !E u E'. TRANS E u E' ==> FV E' SUBSET (FV E)
Proof
    HO_MATCH_MP_TAC TRANS_IND (* strongind is useless *)
 >> RW_TAC lset_ss [FV_def] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `FV (CCS_Subst E (rec X E) X)`
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [FV_SUBSET_REC_PRO]
QED

Theorem CCS_Subst_elim :
    !X E. X NOTIN (FV E) ==> !E'. (CCS_Subst E E' X = E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def] (* one left *)
 >> Cases_on `a = X` >- fs []
 >> RES_TAC >> ASM_SIMP_TAC std_ss []
QED

Theorem CCS_Subst_elim_IMP_NOTIN :
    !X E. (!E'. CCS_Subst E E' X = E) ==> X NOTIN (FV E)
Proof
    GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def] (* 2 goals left *)
 >- (CCONTR_TAC >> fs [] \\
     PROVE_TAC [Q.SPEC `var a` CCS_distinct_exists])
 >> Cases_on `X = a` >- fs []
 >> DISJ1_TAC >> fs []
QED

(* if E[t/X] = E[t'/X] for all t t', X must not be free in E *)
Theorem CCS_Subst_IMP_NOTIN_FV :
    !X E. (!E1 E2. CCS_Subst E E1 X = CCS_Subst E E2 X) ==> X NOTIN (FV E)
Proof
    Suff `!X E. X IN (FV E) ==> ?E1 E2. CCS_Subst E E1 X <> CCS_Subst E E2 X`
 >- METIS_TAC []
 >> GEN_TAC >> Induct_on `E` (* 8 subgoals *)
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def] (* 5 subgoals left *)
 >- (Q.EXISTS_TAC `nil` >> METIS_TAC [CCS_distinct_exists]) >>
 RES_TAC >> take [`E1`, `E2`] >> art []
QED

Theorem FV_REC_PREF :
    !X E u E'. FV (CCS_Subst E (rec X (prefix u E')) X) =
               FV (CCS_Subst E (rec X E') X)
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def]
QED

Theorem FV_REC_SUM :
    !X E E1 E2. FV (CCS_Subst E (rec X (E1 + E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FV_REC_PAR :
    !X E E1 E2. FV (CCS_Subst E (rec X (par E1 E2)) X) =
               (FV (CCS_Subst E (rec X E1) X)) UNION (FV (CCS_Subst E (rec X E2) X))
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def] (* 4 subgoals *)
 >> SET_TAC []
QED

Theorem FINITE_FV :
    !E. FINITE (FV E)
Proof
    Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, FV_def]
QED

(* ('a, 'b) CCS -> 'a set (set of bound variables) *)
Definition BV_def :
   (BV (nil :('a, 'b) CCS) = (EMPTY :'a set)) /\
   (BV (prefix u p)        = BV p) /\
   (BV (sum p q)           = (BV p) UNION (BV q)) /\
   (BV (par p q)           = (BV p) UNION (BV q)) /\
   (BV (restr L p)         = BV p) /\
   (BV (relab p rf)        = BV p) /\
   (BV (var X)             = EMPTY) /\
   (BV (rec X p)           = X INSERT (BV p))
End

(* broken into separate theorems *)
val [BV_nil,   BV_prefix, BV_sum, BV_par,
     BV_restr, BV_relab,  BV_var, BV_rec] =
    map save_thm
        (combine (["BV_nil",   "BV_prefix",
                   "BV_sum",   "BV_par",
                   "BV_restr", "BV_relab",
                   "BV_var",   "BV_rec"], CONJUNCTS BV_def));

Theorem BV_SUBSET :
    !X E E'. BV (CCS_Subst E E' X) SUBSET (BV E) UNION (BV E')
Proof
    GEN_TAC >> Induct_on `E`
 >> RW_TAC lset_ss [BV_def, CCS_Subst_def]
 >> ASM_SET_TAC []
QED

Theorem BV_SUBSET_REC :
    !X E. BV (CCS_Subst E (rec X E) X) SUBSET (X INSERT (BV E))
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (Q.SPECL [`X`, `E`, `rec X E`] BV_SUBSET)
 >> ASM_SET_TAC [BV_def]
QED

Theorem TRANS_BV :
    !E u E'. TRANS E u E' ==> BV E' SUBSET BV E
Proof
    HO_MATCH_MP_TAC TRANS_ind
 >> RW_TAC lset_ss [BV_def] (* 7 subgoals *)
 >> TRY (ASM_SET_TAC []) (* 1 - 6 *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BV (CCS_Subst E (rec X E) X)` >> art []
 >> fs [BV_SUBSET_REC]
QED

Theorem BV_REC :
    !X E. X IN BV (rec X E)
Proof
    RW_TAC std_ss [BV_def, IN_INSERT]
QED

Theorem BV_SUBSET_rules :
    !X E E'. (BV E)  SUBSET (BV (rec X E)) /\
             (BV E)  SUBSET (BV (sum E E')) /\
             (BV E') SUBSET (BV (sum E E')) /\
             (BV E)  SUBSET (BV (par E E')) /\
             (BV E') SUBSET (BV (par E E'))
Proof
    rpt GEN_TAC >> SET_TAC [BV_def]
QED

Theorem FINITE_BV :
    !E. FINITE (BV E)
Proof
    Induct_on `E`
 >> RW_TAC lset_ss [CCS_Subst_def, BV_def]
QED

Definition IS_PROC_def :
    IS_PROC E <=> (FV E = EMPTY)
End

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

Theorem IS_PROC_prefix :
    !P u. IS_PROC (prefix u P) <=> IS_PROC P
Proof
    RW_TAC std_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_sum :
    !P Q. IS_PROC (sum P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC lset_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_par :
    !P Q. IS_PROC (par P Q) <=> IS_PROC P /\ IS_PROC Q
Proof
    RW_TAC lset_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_restr :
    !P L. IS_PROC (restr L P) <=> IS_PROC P
Proof
    RW_TAC lset_ss [IS_PROC_def, FV_def]
QED

Theorem IS_PROC_relab :
    !P rf. IS_PROC (relab P rf) <=> IS_PROC P
Proof
    RW_TAC lset_ss [IS_PROC_def, FV_def]
QED

Theorem TRANS_PROC :
    !E u E'. TRANS E u E' /\ IS_PROC E ==> IS_PROC E'
Proof
    RW_TAC std_ss [IS_PROC_def]
 >> `FV E' SUBSET FV E` by PROVE_TAC [TRANS_FV]
 >> rfs []
QED

(**********************************************************************)
(*                Free and bound names (sorts) ('b)                   *)
(**********************************************************************)

(* To be moved to rich_listTheory *)
Definition DELETE_ELEMENT :
    (DELETE_ELEMENT e [] = []) /\
    (DELETE_ELEMENT e (x :: l) = if (e = x) then DELETE_ELEMENT e l
                                 else x :: DELETE_ELEMENT e l)
End

Theorem NOT_IN_DELETE_ELEMENT :
    !e L. ~MEM e (DELETE_ELEMENT e L)
Proof
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT, MEM]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
QED

Theorem DELETE_ELEMENT_FILTER :
    !e L. DELETE_ELEMENT e L = FILTER ((<>) e) L
Proof
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT, FILTER]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT, FILTER]
 >> Cases_on `e = h` >> fs []
QED

Theorem LENGTH_DELETE_ELEMENT_LEQ :
    !e L. LENGTH (DELETE_ELEMENT e L) <= LENGTH L
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> MP_TAC (Q.SPECL [`\y. e <> y`, `\y. T`] LENGTH_FILTER_LEQ_MONO)
 >> BETA_TAC >> simp []
QED

Theorem LENGTH_DELETE_ELEMENT_LE :
    !e L. MEM e L ==> LENGTH (DELETE_ELEMENT e L) < LENGTH L
Proof
    rpt GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [MEM]
 >> GEN_TAC >> REWRITE_TAC [MEM, DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
 >> MP_TAC (Q.SPECL [`h`, `L`] LENGTH_DELETE_ELEMENT_LEQ)
 >> KILL_TAC >> RW_TAC arith_ss []
QED

Theorem EVERY_DELETE_ELEMENT :
    !e L P. P e /\ EVERY P (DELETE_ELEMENT e L) ==> EVERY P L
Proof
    GEN_TAC >> Induct_on `L`
 >- RW_TAC std_ss [DELETE_ELEMENT]
 >> rpt GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT]
 >> Cases_on `e = h` >> fs []
QED

Theorem DELETE_ELEMENT_APPEND :
    !a L L'. DELETE_ELEMENT a (L ++ L') =
             DELETE_ELEMENT a L ++ DELETE_ELEMENT a L'
Proof
    REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> REWRITE_TAC [GSYM FILTER_APPEND_DISTRIB]
QED

(* Learnt from Robert Beers (not used so far) *)
Definition ALL_IDENTICAL :
    ALL_IDENTICAL t = ?x. !y. MEM y t ==> (y = x)
End

(* (FN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val FN_definition = `
   (FN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J = l INSERT (FN p J)) /\   (* here! *)
   (FN (prefix tau p) J       = FN p J) /\
   (FN (sum p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (par p q) J            = (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J          = (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J         = IMAGE (REP_Relabeling rf) (FN p J)) /\ (* here *)
   (FN (var X) J              = EMPTY) /\
   (FN (rec X p) J            = if (MEM X J) then
                                    FN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* (BN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val BN_definition = `
   (BN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (BN (prefix u p) J         = BN p J) /\
   (BN (sum p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (par p q) J            = (BN p J) UNION (BN q J)) /\
   (BN (restr L p) J          = (BN p J) UNION L) /\ (* here *)
   (BN (relab p rf) J         = BN p J) /\
   (BN (var X) J              = EMPTY) /\
   (BN (rec X p) J            = if (MEM X J) then
                                    BN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
                                else EMPTY)`;

(* This is how we get the correct tactics (FN_tac):
 - val FN_defn = Hol_defn "FN" FN_definition;
 - Defn.tgoal FN_defn;
 *)
local
  val tactic = (* the use of `($< LEX $<)` is learnt from Ramana Kumar *)
      WF_REL_TAC `inv_image ($< LEX $<)
                            (\x. (LENGTH (SND x), ^CCS_size_tm (\x. 0) (\x. 0) (FST x)))`
   >> rpt STRIP_TAC >- (IMP_RES_TAC LENGTH_DELETE_ELEMENT_LE >> art [])
   >> REWRITE_TAC [CCS_size_def]
   >> simp [];
in
  val FN_def = TotalDefn.tDefine "FN" FN_definition tactic;
  val BN_def = TotalDefn.tDefine "BN" BN_definition tactic;
end;

(* (free_names :('a, 'b) CCS -> 'b Label set) collects all visible
   labels (also called "sorts") as the prefix, w.r.t relabeling operators. *)
val free_names_def = Define
   `free_names p = FN p (SET_TO_LIST (BV p))`;

(* (bound_names :('a, 'b) CCS -> 'b Label set) collects all visible
   labels by the restriction operator. *)
val bound_names_def = Define
   `bound_names p = BN p (SET_TO_LIST (BV p))`;

val FN_UNIV1 = store_thm ("FN_UNIV1",
  ``!p. free_names p <> (UNIV :'b Label set) ==> ?a. a NOTIN free_names p``,
    PROVE_TAC [EQ_UNIV]);

val FN_UNIV2 = store_thm ("FN_UNIV2",
  ``!p q. free_names p UNION free_names q <> (UNIV :'b Label set) ==>
          ?a. a NOTIN free_names p /\ a NOTIN free_names q``,
    PROVE_TAC [EQ_UNIV, IN_UNION]);

val _ = export_theory ();
val _ = html_theory "CCS";
