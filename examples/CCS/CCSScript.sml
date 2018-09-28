(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory optionTheory listTheory finite_mapTheory;
open CCSLib;

val _ = new_theory "CCS";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*                           Labels and Actions                               *)
(*                                                                            *)
(******************************************************************************)

(* Define the set of labels as the union of names (`in`) (strings) and
   co-names (`out`) (complement of names) *)
val _ = Datatype `Label = name 'b | coname 'b`;

(* Define structural induction on labels
   |- ∀P. (∀s. P (name s)) ∧ (∀s. P (coname s)) ⇒ ∀L. P L
 *)
val Label_induction = TypeBase.induction_of ``:'b Label``;

(* The structural cases theorem for the type Label
   |- ∀LL. (∃s. LL = name s) ∨ ∃s. LL = coname s
 *)
val Label_nchotomy = TypeBase.nchotomy_of ``:'b Label``;

(* The distinction and injectivity theorems for the type Label
   |- ∀a' a. name a ≠ coname a'
   |- (∀a a'. (name a = name a') ⇔ (a = a')) ∧
       ∀a a'. (coname a = coname a') ⇔ (a = a')
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
val _ = type_abbrev ("Action", ``:'b Label option``);

val _ = overload_on ("tau",   ``NONE :'b Action``);
val _ = overload_on ("label", ``SOME :'b Label -> 'b Action``);

val _ = Unicode.unicode_version { u = UnicodeChars.tau, tmnm = "tau"};
val _ = TeX_notation { hol = "tau", TeX = ("\\ensuremath{\\tau}", 1) };

(* The compact representation for (visible) input and output actions, suggested by Michael Norrish *)
val _ = overload_on ("In", ``\a. label (name a)``);
val _ = overload_on ("Out", ``\a. label (coname a)``);

(* Define structural induction on actions
   |- ∀P. P tau ∧ (∀L. P (label L)) ⇒ ∀A. P A
 *)
val Action_induction = save_thm (
   "Action_induction", INST_TYPE [``:'a`` |-> ``:'b Label``] option_induction);

(* The structural cases theorem for the type Action
   |- ∀AA. (AA = tau) ∨ ∃L. AA = label L
 *)
val Action_nchotomy = save_thm (
   "Action_nchotomy", INST_TYPE [``:'a`` |-> ``:'b Label``] option_nchotomy);

(* The distinction and injectivity theorems for the type Action
   |- ∀a. tau ≠ label a
   |- ∀a a'. (label a = label a') ⇔ (a = a')
 *)
val Action_distinct = save_thm (
   "Action_distinct", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_NONE_SOME);

val Action_distinct_label = save_thm (
   "Action_distinct_label", INST_TYPE [``:'a`` |-> ``:'b Label``] NOT_SOME_NONE);

val Action_11 = save_thm (
   "Action_11", INST_TYPE [``:'a`` |-> ``:'b Label``] SOME_11);

(* |- ∀A. A ≠ tau ⇒ ∃L. A = label L *)
val Action_no_tau_is_Label = save_thm (
   "Action_no_tau_is_Label",
    Q.GEN `A` (DISJ_IMP (Q.SPEC `A` Action_nchotomy)));

(* Extract the label from a visible action, LABEL: Action -> Label. *)
val _ = overload_on ("LABEL", ``THE :'b Label option -> 'b Label``);
val    LABEL_def = save_thm (
      "LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] THE_DEF);

val IS_LABEL_def = save_thm (
   "IS_LABEL_def", INST_TYPE [``:'a`` |-> ``:'b Label``] IS_SOME_DEF);
val _ = export_rewrites ["LABEL_def", "IS_LABEL_def"];

(* Define the complement of a label, COMPL: Label -> Label. *)
val COMPL_LAB_def = Define `(COMPL_LAB (name (s :'b)) = (coname s)) /\
			    (COMPL_LAB (coname s) = (name s))`;

val _ = overload_on ("COMPL", ``COMPL_LAB``);
val _ = export_rewrites ["COMPL_LAB_def"];

val coname_COMPL = store_thm ("coname_COMPL",
  ``!(s :'b). coname s = COMPL (name s)``,
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

val COMPL_COMPL_ACT = store_thm (
   "COMPL_COMPL_ACT", ``!(a :'b Action). COMPL_ACT (COMPL_ACT a) = a``,
    Induct
 >| [ REWRITE_TAC [COMPL_ACT_def],
      REWRITE_TAC [COMPL_ACT_def, COMPL_COMPL_LAB] ]);

(* Auxiliary theorem about complementary labels. *)
val COMPL_THM = store_thm ("COMPL_THM",
  ``!(l :'b Label) s. (~(l = name s) ==> ~(COMPL l = coname s)) /\
	  (~(l = coname s) ==> ~(COMPL l = name s))``,
    Induct_on `l`
 >| [ (* case 1 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_11, COMPL_LAB_def],
        REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'] ] ,
      (* case 2 *)
      rpt GEN_TAC >> CONJ_TAC >|
      [ REWRITE_TAC [Label_distinct, COMPL_LAB_def, Label_distinct'],
        REWRITE_TAC [Label_11, COMPL_LAB_def] ] ]);

val Is_Relabeling_def = Define `
    Is_Relabeling (f: 'b Label -> 'b Label) = (!s. f (coname s) = COMPL (f (name s)))`;

val EXISTS_Relabeling = store_thm ("EXISTS_Relabeling",
  ``?(f: 'b Label -> 'b Label). Is_Relabeling f``,
    Q.EXISTS_TAC `\a. a`
 >> PURE_ONCE_REWRITE_TAC [Is_Relabeling_def]
 >> BETA_TAC
 >> REWRITE_TAC [COMPL_LAB_def]);

(* Relabeling_TY_DEF =
   |- ∃rep. TYPE_DEFINITION Is_Relabeling rep
 *)
val Relabeling_TY_DEF = new_type_definition ("Relabeling", EXISTS_Relabeling);

(* Relabeling_ISO_DEF =
   |- (∀a. ABS_Relabeling (REP_Relabeling a) = a) ∧
       ∀r. Is_Relabeling r ⇔ (REP_Relabeling (ABS_Relabeling r) = r)
 *)
val Relabeling_ISO_DEF = define_new_type_bijections
			      { ABS  = "ABS_Relabeling",
				REP  = "REP_Relabeling",
				name = "Relabeling_ISO_DEF",
				tyax =  Relabeling_TY_DEF };

(* ABS_Relabeling_one_one =
   |- ∀r r'.
      Is_Relabeling r ⇒ Is_Relabeling r' ⇒
      ((ABS_Relabeling r = ABS_Relabeling r') ⇔ (r = r'))

   ABS_Relabeling_onto =
   |- ∀a. ∃r. (a = ABS_Relabeling r) ∧ Is_Relabeling r

   REP_Relabeling_one_one =
   |- ∀a a'. (REP_Relabeling a = REP_Relabeling a') ⇔ (a = a')

   REP_Relabeling_onto =
   |- ∀r. Is_Relabeling r ⇔ ∃a. r = REP_Relabeling a
 *)
val [ABS_Relabeling_one_one,
     ABS_Relabeling_onto,
     REP_Relabeling_one_one,
     REP_Relabeling_onto] =
    map (fn f => f Relabeling_ISO_DEF)
	[prove_abs_fn_one_one,
	 prove_abs_fn_onto,
	 prove_rep_fn_one_one,
	 prove_rep_fn_onto];

val REP_Relabeling_THM = store_thm ("REP_Relabeling_THM",
  ``!rf :'b Relabeling. Is_Relabeling (REP_Relabeling rf)``,
    GEN_TAC
 >> REWRITE_TAC [REP_Relabeling_onto]
 >> EXISTS_TAC ``rf :'b Relabeling``
 >> REWRITE_TAC []);

(* Relabeling labels is extended to actions by renaming tau as tau. *)
val relabel_def = Define `(relabel (rf :'b Relabeling) tau = tau) /\
			  (relabel rf (label l) = label (REP_Relabeling rf l))`;

(* If the renaming of an action is a label, that action is a label. *)
val Relab_label = store_thm ("Relab_label",
  ``!(rf :'b Relabeling) u l. (relabel rf u = label l) ==> ?l'. u = label l'``,
    Induct_on `u`
 >- REWRITE_TAC [relabel_def, Action_distinct]
 >> REWRITE_TAC [relabel_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``a :'b Label``
 >> REWRITE_TAC []);

(* If the renaming of an action is tau, that action is tau. *)
val Relab_tau = store_thm ("Relab_tau",
  ``!(rf :'b Relabeling) u. (relabel rf u = tau) ==> (u = tau)``,
    Induct_on `u`
 >> REWRITE_TAC [relabel_def, Action_distinct_label]);

(* Apply_Relab: ((Label # Label) list) -> Label -> Label
   (SND of any pair is a name, FST can be either name or coname)
 *)
val Apply_Relab_def = Define `
   (Apply_Relab ([]: ('b Label # 'b Label) list) l = l) /\
   (Apply_Relab (CONS (newold: 'b Label # 'b Label) ls) l =
	  if (SND newold = l)         then (FST newold)
     else if (COMPL (SND newold) = l) then (COMPL (FST newold))
     else (Apply_Relab ls l))`;

val Apply_Relab_COMPL_THM = store_thm ("Apply_Relab_COMPL_THM",
  ``!labl (s: 'b). Apply_Relab labl (coname s) = COMPL (Apply_Relab labl (name s))``,
    Induct
 >- REWRITE_TAC [Apply_Relab_def, COMPL_LAB_def]
 >> rpt GEN_TAC
 >> REWRITE_TAC [Apply_Relab_def]
 >> COND_CASES_TAC
 >- art [Label_distinct', COMPL_LAB_def, COMPL_COMPL_LAB]
 >> ASM_CASES_TAC ``SND (h :'b Label # 'b Label) = name s``
 >- art [COMPL_LAB_def]
 >> IMP_RES_TAC COMPL_THM
 >> art []);

val IS_RELABELING = store_thm (
   "IS_RELABELING",
  ``!labl :('b Label # 'b Label) list. Is_Relabeling (Apply_Relab labl)``,
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
 >> art [Apply_Relab_COMPL_THM]);

(* Defining a relabelling function through substitution-like notation.
   RELAB: (Label # Label) list -> Relabeling
 *)
val RELAB_def = Define `
    RELAB (labl :('b Label # 'b Label) list) = ABS_Relabeling (Apply_Relab labl)`;

(* |- ∀labl' labl.
     (RELAB labl' = RELAB labl) ⇔ (Apply_Relab labl' = Apply_Relab labl)
 *)
val APPLY_RELAB_THM = save_thm ("APPLY_RELAB_THM",
    Q_GENL [`labl'`, `labl`]
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
val _ = Datatype `CCS = nil
		      | var 'a
		      | prefix ('b Action) CCS
		      | sum CCS CCS
		      | par CCS CCS
		      | restr (('b Label) set) CCS
		      | relab CCS ('b Relabeling)
		      | rec 'a CCS `;

(* compact representation for single-action restriction *)
val _ = overload_on ("nu", ``\(n :'b) P. restr {name n} P``);
val _ = overload_on ("nu", ``restr``);
val _ = Unicode.unicode_version { u = UnicodeChars.nu, tmnm = "nu" };
val _ = TeX_notation { hol = "nu",
		       TeX = ("\\ensuremath{\\nu}", 1) };

val _ = overload_on ("+", ``sum``); (* priority: 500 *)
val _ = TeX_notation { hol = "+",
		       TeX = ("\\ensuremath{+}", 1) };

val _ = set_mapped_fixity { fixity = Infix(LEFT, 600), tok = "||", term_name = "par" };
val _ = TeX_notation { hol = "||",
		       TeX = ("\\ensuremath{\\parallel}", 1) };
val _ =
    add_rule { term_name = "prefix", fixity = Infix(RIGHT, 700),
	pp_elements = [ BreakSpace(0,0), TOK "..", BreakSpace(0,0) ],
	paren_style = OnlyIfNecessary,
	block_style = (AroundSamePrec, (PP.CONSISTENT, 0)) };

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

(* Prove that the constructors of the type CCS are one-to-one. *)
val CCS_11 = TypeBase.one_one_of ``:('a, 'b) CCS``;

(* Given any agent expression, define the substitution of an agent expression
   E' for an agent variable X.

   This works under the hypothesis that the Barendregt convention holds. *)
val CCS_Subst_def = Define `
   (CCS_Subst nil	   E' X = nil) /\
   (CCS_Subst (prefix u E) E' X = prefix u (CCS_Subst E E' X)) /\
   (CCS_Subst (sum E1 E2)  E' X = sum (CCS_Subst E1 E' X)
				      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (par E1 E2)  E' X = par (CCS_Subst E1 E' X)
				      (CCS_Subst E2 E' X)) /\
   (CCS_Subst (restr L E)  E' X = restr L (CCS_Subst E E' X)) /\
   (CCS_Subst (relab E f)  E' X = relab   (CCS_Subst E E' X) f) /\
   (CCS_Subst (var Y)      E' X = if (Y = X) then E' else (var Y)) /\
   (CCS_Subst (rec Y E)    E' X = if (Y = X) then (rec Y E)
					     else (rec Y (CCS_Subst E E' X)))`;

(* Note that in the rec clause, if Y = X then all occurrences of Y in E are X
   and bound, so there exist no free variables X in E to be replaced with E'.
   Hence, the term rec Y E is returned.

   Below are two typical cases by CCS_Subst: *)

(* |- ∀X E E'. CCS_Subst (rec X E) E' X = rec X E (1st fixed point of CCS_Subst) *)
val CCS_Subst_rec = save_thm (
   "CCS_Subst_rec", Q_GENL [`X`, `E`, `E'`]
			(REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (rec X E) E' X``));

(* |- ∀X E. CCS_Subst (var X) E X = E		  (2nd fixed point of CCS_Subst) *)
val CCS_Subst_var = save_thm (
   "CCS_Subst_var", Q_GENL [`X`, `E`]
			(REWRITE_CONV [CCS_Subst_def] ``CCS_Subst (var X) E X``));

(* |- !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2) *)
val CCS_COND_CLAUSES = save_thm (
   "CCS_COND_CLAUSES", INST_TYPE [``:'a`` |-> ``:('a, 'b) CCS``] COND_CLAUSES);

(******************************************************************************)
(*                                                                            *)
(*            Definition of the transition relation for pure CCS              *)
(*                                                                            *)
(******************************************************************************)

val _ = type_abbrev ("transition",
		    ``:('a, 'b) CCS -> 'b Action -> ('a, 'b) CCS -> bool``);

(* Inductive definition of the transition relation TRANS for CCS.
   TRANS: CCS -> Action -> CCS -> bool

   NOTE: noticed that, the theorem TRANS_ind is never needed, thus even we define
   TRANS co-inductively (i.e. by Hol_coreln), the whole formalization still works.
 *)
val (TRANS_rules, TRANS_ind, TRANS_cases) = Hol_reln `
    (!E u.                           TRANS (prefix u E) u E) /\		(* PREFIX *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E E') u E1) /\		(* SUM1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (sum E' E) u E1) /\		(* SUM2 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E E') u (par E1 E')) /\	(* PAR1 *)
    (!E u E1 E'.    TRANS E u E1 ==> TRANS (par E' E) u (par E' E1)) /\	(* PAR2 *)
    (!E l E1 E' E2. TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2
		==> TRANS (par E E') tau (par E1 E2)) /\		(* PAR3 *)
    (!E u E' l L.   TRANS E u E' /\ ((u = tau) \/
				     ((u = label l) /\ l NOTIN L /\ (COMPL l) NOTIN L))
		==> TRANS (restr L E) u (restr L E')) /\		(* RESTR *)
    (!E u E' rf.    TRANS E u E'
		==> TRANS (relab E rf) (relabel rf u) (relab E' rf)) /\	(* RELABELING *)
    (!E u X E1.     TRANS (CCS_Subst E (rec X E) X) u E1
		==> TRANS (rec X E) u E1) `;				(* REC *)

val _ =
    add_rule { term_name = "TRANS", fixity = Infix (NONASSOC, 450),
	pp_elements = [ BreakSpace(1,0), TOK "--", HardSpace 0, TM, HardSpace 0, TOK "->",
			BreakSpace(1,0) ],
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

(* The process nil has no transitions.
   |- ∀u E. ¬TRANS nil u E
 *)
val NIL_NO_TRANS = save_thm ("NIL_NO_TRANS",
    Q_GENL [`u`, `E`]
	   (REWRITE_RULE [CCS_distinct]
			 (SPECL [``nil``, ``u :'b Action``, ``E :('a, 'b) CCS``] TRANS_cases)));

(* |- ∀u E. nil --u-> E ⇔ F *)
val NIL_NO_TRANS_EQF = save_thm (
   "NIL_NO_TRANS_EQF",
    Q_GENL [`u`, `E`] (EQF_INTRO (SPEC_ALL NIL_NO_TRANS)));

(* Prove that if a process can do an action, then the process is not nil.
   |- ∀E u E'. TRANS E u E' ⇒ E ≠ nil:
 *)
val TRANS_IMP_NO_NIL = store_thm ("TRANS_IMP_NO_NIL",
  ``!E u E'. TRANS E u E' ==> ~(E = nil)``,
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [TRANS_cases]
 >> rpt STRIP_TAC
 >> PROVE_TAC [CCS_distinct']);

(* Above proof could be easier using TRANS_ind for the only time in this project
val TRANS_IMP_NO_NIL' = store_thm ("TRANS_IMP_NO_NIL'",
  ``!E u E'. TRANS E u E' ==> ~(E = nil)``,
    HO_MATCH_MP_TAC TRANS_ind
 >> REWRITE_TAC [CCS_distinct']);
 *)

(* An agent variable has no transitions.
   |- !X u E'. ~TRANS (var X) u E'
 *)
val VAR_NO_TRANS = save_thm ("VAR_NO_TRANS",
    Q_GENL [`X`, `u`, `E`]
	   (REWRITE_RULE [CCS_distinct', CCS_11]
			 (Q.SPECL [`var X`, `u`, `E`] TRANS_cases)));

(* |- !u E u' E'. TRANS (prefix u E) u' E' = (u' = u) /\ (E' = E) *)
val TRANS_PREFIX_EQ = save_thm (
   "TRANS_PREFIX_EQ",
  ((Q_GENL [`u`, `E`, `u'`, `E'`]) o
   (ONCE_REWRITE_RHS_RULE [EQ_SYM_EQ]) o
   SPEC_ALL o
   (REWRITE_RULE [CCS_distinct', CCS_11]))
      (SPECL [``prefix (u :'b Action) E``, ``u' :'b Action``, ``E' :('a, 'b) CCS``]
	     TRANS_cases));

(* |- ∀u E u' E'. u..E --u'-> E' ⇒ (u' = u) ∧ (E' = E) *)
val TRANS_PREFIX = save_thm (
   "TRANS_PREFIX", EQ_IMP_LR TRANS_PREFIX_EQ);

(******************************************************************************)
(*                                                                            *)
(*                The transitions of a binary summation                       *)
(*                                                                            *)
(******************************************************************************)

val SUM_cases_EQ = save_thm (
   "SUM_cases_EQ",
    Q_GENL [`D`, `D'`, `u`, `D''`]
	 (REWRITE_RULE [CCS_distinct', CCS_11]
		       (SPECL [``sum D D'``, ``u :'b Action``, ``D'' :('a, 'b) CCS``]
			      TRANS_cases)));

val SUM_cases = save_thm (
   "SUM_cases", EQ_IMP_LR SUM_cases_EQ);

val TRANS_SUM_EQ = store_thm ("TRANS_SUM_EQ",
  ``!E E' u E''. TRANS (sum E E') u E'' = TRANS E u E'' \/ TRANS E' u E''``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC SUM_cases >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC >| (* 2 sub-goals here *)
      [ MATCH_MP_TAC SUM1 >> art [],
        MATCH_MP_TAC SUM2 >> art [] ] ]);

(* for CCS_TRANS_CONV *)
val TRANS_SUM_EQ' = store_thm (
   "TRANS_SUM_EQ'",
  ``!E1 E2 u E. TRANS (sum E1 E2) u E = TRANS E1 u E \/ TRANS E2 u E``,
    REWRITE_TAC [TRANS_SUM_EQ]);

val TRANS_SUM = save_thm (
   "TRANS_SUM", EQ_IMP_LR TRANS_SUM_EQ);

val TRANS_COMM_EQ = store_thm ("TRANS_COMM_EQ",
  ``!E E' E'' u. TRANS (sum E E') u E'' = TRANS (sum E' E) u E''``,
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
  ``!E E' E'' E1 u. TRANS (sum (sum E E') E'') u E1 = TRANS (sum E (sum E' E'')) u E1``,
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
  ``!E u E'. TRANS (sum E nil) u E' = TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM \\
      IMP_RES_TAC NIL_NO_TRANS,
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

(* |- ∀E u E'. E + nil --u-> E' ⇒ E --u-> E' *)
val TRANS_SUM_NIL = save_thm ("TRANS_SUM_NIL", EQ_IMP_LR TRANS_SUM_NIL_EQ);

val TRANS_P_SUM_P_EQ = store_thm ("TRANS_P_SUM_P_EQ",
  ``!E u E'. TRANS (sum E E) u E' = TRANS E u E'``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ DISCH_TAC \\
      IMP_RES_TAC TRANS_SUM,
      DISCH_TAC \\
      MATCH_MP_TAC SUM1 >> art [] ]);

val TRANS_P_SUM_P = save_thm ("TRANS_P_SUM_P", EQ_IMP_LR TRANS_P_SUM_P_EQ);

val PAR_cases_EQ = save_thm ("PAR_cases_EQ",
    Q_GENL [`D`, `D'`, `u`, `D''`]
	(REWRITE_RULE [CCS_distinct', CCS_11]
		      (Q.SPECL [`par D D'`, `u`, `D''`] TRANS_cases)));

val PAR_cases = save_thm ("PAR_cases", EQ_IMP_LR PAR_cases_EQ);

(* NOTE: the shape of this theorem can be easily got from above definition by replacing
         REWRITE_RULE to SIMP_RULE, however the inner existential variable (E1) has a
         different name. *)
val TRANS_PAR_EQ = store_thm ("TRANS_PAR_EQ",
  ``!E E' u E''. TRANS (par E E') u E'' =
		 (?E1. (E'' = par E1 E') /\ TRANS E u E1) \/
		 (?E1. (E'' = par E E1) /\ TRANS E' u E1) \/
		 (?E1 E2 l. (u = tau) /\ (E'' = par E1 E2) /\
			    TRANS E (label l) E1 /\ TRANS E' (label (COMPL l)) E2)``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* case 1 (LR) *)
      STRIP_TAC \\
      IMP_RES_TAC PAR_cases >| (* 3 sub-goals here *)
      [ (* goal 1.1 *)
	DISJ1_TAC \\
	Q.EXISTS_TAC `E1` >> art [],
	(* goal 1.2 *)
	DISJ2_TAC \\
	DISJ1_TAC \\
	Q.EXISTS_TAC `E1` >> art [],
	(* goal 1.3 *)
	DISJ2_TAC \\
	DISJ2_TAC \\
	take [`E1`, `E2`, `l`] >> art [] ],
      (* case 2 (RL) *)
      STRIP_TAC (* 3 sub-goals here, but they share the first and last steps *)
   >> art []
   >| [ MATCH_MP_TAC PAR1 >> art [],
        MATCH_MP_TAC PAR2 >> art [],
        MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ] ]);

val TRANS_PAR = save_thm ("TRANS_PAR", EQ_IMP_LR TRANS_PAR_EQ);

val TRANS_PAR_P_NIL = store_thm ("TRANS_PAR_P_NIL",
  ``!E u E'. TRANS (par E nil) u E' ==> (?E''. TRANS E u E'' /\ (E' = par E'' nil))``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_PAR
 >| [ Q.EXISTS_TAC `E1` >> art [],
      IMP_RES_TAC NIL_NO_TRANS,
      IMP_RES_TAC NIL_NO_TRANS ]);

val TRANS_PAR_NO_SYNCR = store_thm ("TRANS_PAR_NO_SYNCR",
  ``!(l :'b Label) l'. ~(l = COMPL l') ==>
	   (!E E' E''. ~(TRANS (par (prefix (label l) E) (prefix (label l') E')) tau E''))``,
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
    Q_GENL [`D'`, `u`, `L`, `D`]
	   (REWRITE_RULE [CCS_distinct', CCS_11, Action_distinct, Action_11]
			 (Q.SPECL [`restr L D`, `u`, `D'`] TRANS_cases)));

val RESTR_cases = save_thm (
   "RESTR_cases", EQ_IMP_LR RESTR_cases_EQ);

val TRANS_RESTR_EQ = store_thm ("TRANS_RESTR_EQ",
  ``!E L u E'.
     TRANS (restr L E) u E' =
     (?E'' l. (E' = restr L E'') /\ TRANS E u E'' /\
	      ((u = tau) \/ ((u = label l) /\ ~(l IN L) /\ ~((COMPL l) IN L))))``,
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
      Q.EXISTS_TAC `E'''` \\
      Q.EXISTS_TAC `l` >|
      [ (* goal 1.1 *)
	art [REWRITE_RULE [a1] a3],
	(* goal 1.2 *)
	art [REWRITE_RULE [a2] a3] ],
      (* case 2 (RL) *)
      STRIP_TAC >| (* two sub-goals here *)
      [ (* sub-goal 2.1 *)
	art [] \\
	MATCH_MP_TAC RESTR \\
	art [REWRITE_RULE [a1] a4],
	(* sub-goal 2.2 *)
	art [] \\
	MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` \\
	art [REWRITE_RULE [a2] a4] ] ]
  end);

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
      [ FILTER_ASM_REWRITE_TAC (fn t => not (t = ``(u :'b Action) = tau``)) [thm],
        FILTER_ASM_REWRITE_TAC (fn t => not (t = ``(u :'b Action) = label l``)) [thm] ]
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

val RELAB_cases_EQ = save_thm ("RELAB_cases_EQ",
    Q_GENL [`E`, `rf`]
	   (REWRITE_RULE [CCS_distinct', CCS_11] (SPEC ``relab E rf`` TRANS_cases)));

val RELAB_cases = save_thm ("RELAB_cases", EQ_IMP_LR RELAB_cases_EQ);

val TRANS_RELAB_EQ = store_thm ("TRANS_RELAB_EQ",
  ``!E rf u E'. TRANS (relab E rf) u E' =
		(?u' E''. (u = relabel rf u') /\
			  (E' = relab E'' rf) /\ TRANS E u' E'')``,
    rpt GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      DISCH_TAC	\\
      IMP_RES_TAC RELAB_cases \\
      take [`u'`, `E'''`] >> art [],
      (* goal 2 (of 2) *)
      STRIP_TAC \\
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC RELABELING \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]);

val TRANS_RELAB = save_thm ("TRANS_RELAB", EQ_IMP_LR TRANS_RELAB_EQ);

val TRANS_RELAB_labl = save_thm ("TRANS_RELAB_labl",
    Q_GENL [`E`, `labl`] (Q.SPECL [`E`, `RELAB labl`] TRANS_RELAB));

val RELAB_NIL_NO_TRANS = store_thm ("RELAB_NIL_NO_TRANS",
  ``!(rf :'b Relabeling) u E. ~(TRANS (relab nil rf) u E)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC TRANS_RELAB
 >> IMP_RES_TAC NIL_NO_TRANS);

val REC_cases_EQ = save_thm ("REC_cases_EQ",
    Q_GENL [`X`, `E`, `u`, `E''`]
	 (Q.SPECL [`u`, `E''`]
		  (REWRITE_RULE [CCS_distinct', CCS_11]
				(SPEC ``rec X E`` TRANS_cases))));

val REC_cases = save_thm ("REC_cases", EQ_IMP_LR REC_cases_EQ);

val TRANS_REC_EQ = store_thm ("TRANS_REC_EQ",
  ``!X E u E'. TRANS (rec X E) u E' = TRANS (CCS_Subst E (rec X E) X) u E'``,
    rpt GEN_TAC
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC_cases_EQ] \\
      rpt STRIP_TAC \\
      PURE_ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [REC] ]);

val TRANS_REC = save_thm ("TRANS_REC", EQ_IMP_LR TRANS_REC_EQ);

(******************************************************************************)
(*                                                                            *)
(*                     Variables and Names (Labels) in CCS                    *)
(*                                                                            *)
(******************************************************************************)

(* ('a, 'b) CCS -> 'a set (set of free variables) *)
val FV_def = Define `
   (FV (nil :('a, 'b) CCS)    = (EMPTY :'a set)) /\
   (FV (prefix u p)	      = FV p) /\
   (FV (sum p q)	      = (FV p) UNION (FV q)) /\
   (FV (par p q)	      = (FV p) UNION (FV q)) /\
   (FV (restr L p)	      = FV p) /\
   (FV (relab p rf)	      = FV p) /\
   (FV (var X)		      = {X}) /\
   (FV (rec X p)	      = (FV p) DIFF {X}) `;

(* ('a, 'b) CCS -> 'a set (set of bound variables) *)
val BV_def = Define `
   (BV (nil :('a, 'b) CCS)    = (EMPTY :'a set)) /\
   (BV (prefix u p)	      = BV p) /\
   (BV (sum p q)	      = (BV p) UNION (BV q)) /\
   (BV (par p q)	      = (BV p) UNION (BV q)) /\
   (BV (restr L p)	      = BV p) /\
   (BV (relab p rf)	      = BV p) /\
   (BV (var X)		      = EMPTY) /\
   (BV (rec X p)	      = X INSERT (BV p)) `;

val IS_PROC_def = Define `
    IS_PROC E = (FV E = EMPTY)`;

val ALL_PROC_def = Define `
    ALL_PROC ES = EVERY IS_PROC ES`;

(* The use of finite_mapTheory (to get rid of substitution orders) is
   suggested by Konrad Slind. *)
val CCS_Subst1_def = Define `
   (CCS_Subst1 nil	   (fm :'a |-> ('a, 'b) CCS) = nil) /\
   (CCS_Subst1 (prefix u E) fm = prefix u (CCS_Subst1 E fm)) /\
   (CCS_Subst1 (sum E1 E2)  fm = sum (CCS_Subst1 E1 fm)
				     (CCS_Subst1 E2 fm)) /\
   (CCS_Subst1 (par E1 E2)  fm = par (CCS_Subst1 E1 fm)
				     (CCS_Subst1 E2 fm)) /\
   (CCS_Subst1 (restr L E)  fm = restr L (CCS_Subst1 E fm)) /\
   (CCS_Subst1 (relab E rf) fm = relab   (CCS_Subst1 E fm) rf) /\
   (CCS_Subst1 (var Y)      fm = if (Y IN FDOM fm) then (FAPPLY fm Y)
				 else (var Y)) /\
   (CCS_Subst1 (rec Y E)    fm = if (Y IN FDOM fm) then (rec Y E)
				 else (rec Y (CCS_Subst1 E fm)))`;

(* :('a, 'b) CCS list -> ('a |-> ('a, 'b) CCS) -> ('a, 'b) CCS list *)
val CCS_Subst2_def = Define `
    CCS_Subst2 ES fm = MAP (\e. CCS_Subst1 e fm) ES`;

val DELETE_ELEMENT_def = Define `
   (DELETE_ELEMENT e [] = []) /\
   (DELETE_ELEMENT e (x :: l) =
    if (e = x) then DELETE_ELEMENT e l else x :: DELETE_ELEMENT e l)`;

val NOT_IN_DELETE_ELEMENT = store_thm (
   "NOT_IN_DELETE_ELEMENT", 
  ``!e L. ~MEM e (DELETE_ELEMENT e L)``,
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT_def, MEM]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []);

val DELETE_ELEMENT_FILTER = store_thm (
   "DELETE_ELEMENT_FILTER", 
  ``!e L. DELETE_ELEMENT e L = FILTER ((<>) e) L``,
    GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [DELETE_ELEMENT_def, FILTER]
 >> GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def, FILTER]
 >> Cases_on `e = h` >> fs []);

val LENGTH_DELETE_ELEMENT_LEQ = store_thm (
   "LENGTH_DELETE_ELEMENT_LEQ",
  ``!e L. LENGTH (DELETE_ELEMENT e L) <= LENGTH L``,
    rpt GEN_TAC
 >> REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> MP_TAC (Q.SPECL [`\y. e <> y`, `\y. T`] LENGTH_FILTER_LEQ_MONO)
 >> BETA_TAC >> simp []
 >> STRIP_TAC
 >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `L`))
 >> Know `FILTER (\y. T) L = L`
 >- ( KILL_TAC \\
      Induct_on `L` >- REWRITE_TAC [FILTER] \\
      GEN_TAC >> REWRITE_TAC [FILTER] >> simp [] )
 >> DISCH_TAC >> fs []);

val LENGTH_DELETE_ELEMENT_LE = store_thm (
   "LENGTH_DELETE_ELEMENT_LE",
  ``!e L. MEM e L ==> LENGTH (DELETE_ELEMENT e L) < LENGTH L``,
    rpt GEN_TAC >> Induct_on `L`
 >- REWRITE_TAC [MEM]
 >> GEN_TAC >> REWRITE_TAC [MEM, DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []
 >> MP_TAC (Q.SPECL [`h`, `L`] LENGTH_DELETE_ELEMENT_LEQ)
 >> KILL_TAC >> RW_TAC arith_ss []);

val EVERY_DELETE_ELEMENT = store_thm (
   "EVERY_DELETE_ELEMENT",
  ``!e L P. P e /\ EVERY P (DELETE_ELEMENT e L) ==> EVERY P L``,
    GEN_TAC >> Induct_on `L`
 >- RW_TAC std_ss [DELETE_ELEMENT_def]
 >> rpt GEN_TAC >> REWRITE_TAC [DELETE_ELEMENT_def]
 >> Cases_on `e = h` >> fs []);

val DELETE_ELEMENT_APPEND = store_thm (
   "DELETE_ELEMENT_APPEND",
  ``!a L L'. DELETE_ELEMENT a (L ++ L') = DELETE_ELEMENT a L ++ DELETE_ELEMENT a L'``,
    REWRITE_TAC [DELETE_ELEMENT_FILTER]
 >> REWRITE_TAC [GSYM FILTER_APPEND_DISTRIB]);

(* not used so far, learnt from Robert Beers *)
val ALL_IDENTICAL_def = Define `
    ALL_IDENTICAL t = ?x. !y. MEM y t ==> (y = x)`;

(*
You might define the sublist relation: (from Michael Norrish)
Sublist [] l = T
  Sublist _ [] = F
  Sublist (h1::t1) (h2::t2) = if h1 = h2 then Sublist t1 t2 else Sublist (h1::t1) t2

And show that

  Sublist (DELETE_ELEMENT e l) l
*)

(* (size :(α, β) CCS -> num) *)
val size_def = Define `
    size (p :('a, 'b) CCS) = ^CCS_size_tm (\x. 0) (\x. 0) p`;

(* (FN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val FN_definition = `
   (FN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (FN (prefix (label l) p) J = l INSERT (FN p J)) /\	(* here! *)
   (FN (prefix tau p) J	      = FN p J) /\
   (FN (sum p q) J	      = (FN p J) UNION (FN q J)) /\
   (FN (par p q) J	      = (FN p J) UNION (FN q J)) /\
   (FN (restr L p) J	      = (FN p J) DIFF (L UNION (IMAGE COMPL_LAB L))) /\
   (FN (relab p rf) J	      = IMAGE (REP_Relabeling rf) (FN p J)) /\
   (FN (var X) J	      = EMPTY) /\
   (FN (rec X p) J	      = if (MEM X J) then
				    FN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
				else EMPTY)`;

(* (BN :('a, 'b) CCS -> 'a list -> 'b Label set) *)
val BN_definition = `
   (BN (nil :('a, 'b) CCS) J  = (EMPTY :'b Label set)) /\
   (BN (prefix u p) J	      = BN p J) /\
   (BN (sum p q) J	      = (BN p J) UNION (BN q J)) /\
   (BN (par p q) J	      = (BN p J) UNION (BN q J)) /\
   (BN (restr L p) J	      = (BN p J) UNION L) /\	(* here! *)
   (BN (relab p rf) J	      = BN p J) /\
   (BN (var X) J	      = EMPTY) /\
   (BN (rec X p) J	      = if (MEM X J) then
				    FN (CCS_Subst p (rec X p) X) (DELETE_ELEMENT X J)
				else EMPTY)`;

(* This is how we get the correct tactics (FN_tac):
 - val FN_defn = Hol_defn "FN" FN_definition;
 - Defn.tgoal FN_defn;
 *)
local
    val tactic = (* the use of `($< LEX $<)` is learnt from Ramana Kumar *)
	WF_REL_TAC `inv_image ($< LEX $<) (\x. (LENGTH (SND x), size (FST x)))`
     >> rpt STRIP_TAC >- ( IMP_RES_TAC LENGTH_DELETE_ELEMENT_LE >> art [] )
     >> REWRITE_TAC [size_def, CCS_size_def]
     >> simp [];
in
    val FN_def = TotalDefn.tDefine "FN" FN_definition tactic;
    val BN_def = TotalDefn.tDefine "BN" BN_definition tactic;
end;

(* (free_names :('a, 'b) CCS -> 'b Label set) collects all visible labels in the prefix *)
val free_names_def = Define ` (* also called "sorts" by Robin Milner *)
    free_names p = FN p (SET_TO_LIST (BV p))`;

(* (bound_names :('a, 'b) CCS -> 'b Label set) collects all visible labels in the restr *)
val bound_names_def = Define `
    bound_names p = BN p (SET_TO_LIST (BV p))`;

val FN_UNIV1 = store_thm ("FN_UNIV1",
  ``!p. free_names p <> (UNIV :'b Label set) ==> ?a. a NOTIN free_names p``,
    PROVE_TAC [EQ_UNIV]);

val FN_UNIV2 = store_thm ("FN_UNIV2",
  ``!p q. free_names p UNION free_names q <> (UNIV :'b Label set) ==>
	  ?a. a NOTIN free_names p /\ a NOTIN free_names q``,
    PROVE_TAC [EQ_UNIV, IN_UNION]);

val _ = export_theory ();
val _ = html_theory "CCS";

(* last updated: Oct 24, 2017 *)
