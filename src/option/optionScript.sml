(* =======================================================================*)
(* FILE		: mk_option.ml						  *)
(* DESCRIPTION  : Creates a theory of SML like options         	          *)
(* WRITES FILES	: option.th						  *)
(*									  *)
(* AUTHOR	: (c) D. Syme 1988					  *)
(* DATE		: 95.04.25						  *)
(* REVISED	: (Konrad Slind) Oct 9.97 to eliminate usage of           *)
(*                recursive types package. Follows the development of     *)
(*                Elsa Gunter in her formalization of partial functions.  *)
(*                                                                        *)
(*                Dec.1998, in order to fit in with Datatype scheme       *)
(* =======================================================================*)

open HolKernel Parse basicHol90Lib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;

(* Make sure that oneTheory is loaded. *)

local open sumTheory oneTheory in end;

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "option";

(*---------------------------------------------------------------------------*
 * Define the new type. The representing type is 'a + one. The development   *
 * is adapted from Elsa Gunter's development of an option type in her        *
 * holML formalization (she called it "lift").                               *
 *---------------------------------------------------------------------------*)

val option_TY_DEF =
    new_type_definition
    {name = "option",
     pred = Term`\x:'a + one. T`,
     inhab_thm = prove(Term`?x:'a + one. (\x.T) x`,
		       BETA_TAC THEN EXISTS_TAC(--`x:'a + one`--) THEN
		       ACCEPT_TAC TRUTH)};

(*---------------------------------------------------------------------------*
 *  val option_REP_ABS_DEF =                                                 *
 *     |- (!a. option_ABS (option_REP a) = a) /\                             *
 *        (!r. (\x. T) r = option_REP (option_ABS r) = r)                    *
 *---------------------------------------------------------------------------*)
val option_REP_ABS_DEF =
     define_new_type_bijections
     {name = "option_REP_ABS_DEF",
      ABS = "option_ABS", REP = "option_REP",
      tyax = option_TY_DEF};

fun reduce thm = REWRITE_RULE[](BETA_RULE thm);

(*---------------------------------------------------------------------------*
 * option_ABS_ONE_ONE = |- !r r'. (option_ABS r = option_ABS r') = r = r'    *
 * option_ABS_ONTO = |- !a. ?r. a = option_ABS r                             *
 * option_REP_ONE_ONE = |- !a a'. (option_REP a = option_REP a') = a = a'    *
 * option_REP_ONTO = |- !r. ?a. r = option_REP a                             *
 *---------------------------------------------------------------------------*)

val option_ABS_ONE_ONE = reduce(prove_abs_fn_one_one option_REP_ABS_DEF);
val option_ABS_ONTO    = reduce(prove_abs_fn_onto option_REP_ABS_DEF);
val option_REP_ONE_ONE = prove_rep_fn_one_one option_REP_ABS_DEF;
val option_REP_ONTO    = reduce(prove_rep_fn_onto option_REP_ABS_DEF);

val SOME_DEF = new_definition("SOME_DEF",Term`!x. SOME x = option_ABS(INL x)`);
val NONE_DEF = new_definition("NONE_DEF",Term`NONE = option_ABS(INR one)`);

val option_CASES_orig = prove
(Term`!opt. (?x. opt = SOME x) \/ (opt = NONE)`,
GEN_TAC THEN PURE_REWRITE_TAC[SOME_DEF,NONE_DEF] 
 THEN PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL option_REP_ONE_ONE)] 
 THEN PURE_ONCE_REWRITE_TAC[reduce(option_REP_ABS_DEF)] 
 THEN STRIP_ASSUME_TAC (ISPEC (--`option_REP opt`--) sumTheory.ISL_OR_ISR) 
 THENL
 [DISJ1_TAC THEN IMP_RES_TAC sumTheory.INL THEN POP_ASSUM (SUBST1_TAC o SYM) 
      THEN EXISTS_TAC (--`OUTL (option_REP opt)`--) THEN REFL_TAC,
  DISJ2_TAC THEN IMP_RES_TAC sumTheory.INR THEN POP_ASSUM (SUBST1_TAC o SYM) 
      THEN ONCE_REWRITE_TAC[oneTheory.one] THEN REFL_TAC]);

val option_Axiom_orig = prove
(Term`!(f:'a -> 'b) e. 
           ?!fn. (!x. fn (SOME x) = f x) /\ (fn NONE = e)`,
REPEAT GEN_TAC
  THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
  [PURE_REWRITE_TAC[SOME_DEF,NONE_DEF] 
     THEN STRIP_ASSUME_TAC (EXISTENCE (BETA_RULE
        (ISPECL [--`\x. f x`--, --`\x:one.(e:'b)`--] 
                (INST_TYPE [Type`:'b` |-> Type`:one`] sumTheory.sum_Axiom))))
     THEN EXISTS_TAC (--`\x:'a option. h(option_REP x):'b`--) THEN BETA_TAC 
     THEN ASM_REWRITE_TAC[reduce option_REP_ABS_DEF],
   REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
    THEN STRIP_ASSUME_TAC (SPEC (Term`o':'a option`) option_CASES_orig) 
    THEN ASM_REWRITE_TAC[]]);

val option_Induct_orig = Prim_rec.prove_induction_thm option_Axiom_orig;

val option_induction = save_thm ("option_induction",
  ONCE_REWRITE_RULE [CONJ_SYM] option_Induct_orig);

val SOME_11 = store_thm("SOME_11",
  Term`!x y :'a. (SOME x = SOME y) = (x=y)`,
  REWRITE_TAC [SOME_DEF,option_ABS_ONE_ONE,sumTheory.INR_INL_11]);

val (NOT_NONE_SOME,NOT_SOME_NONE) = 
 let val thm = TAC_PROOF(([], Term`!x:'a. ~(NONE = SOME x)`),
                  REWRITE_TAC [SOME_DEF,NONE_DEF,
                               option_ABS_ONE_ONE,sumTheory.INR_neq_INL])
 in
   (save_thm("NOT_NONE_SOME", thm),
    save_thm("NOT_SOME_NONE", GSYM thm))
  end;

val option_nchotomy = save_thm("option_nchotomy",
 ONCE_REWRITE_RULE [DISJ_SYM] option_CASES_orig);

val option_Axiom = save_thm("option_Axiom",
 let val V = fst(strip_forall(concl option_Axiom_orig))
 in GENL (rev V) 
      (ONCE_REWRITE_RULE [CONJ_SYM] (SPEC_ALL option_Axiom_orig))
 end);

val option_case_def = 
 new_recursive_definition 
    {name="option_case_def",
     fixity=Term.Prefix,
     rec_axiom=option_Axiom,
     def = Term`(option_case u f NONE = u) /\
                (option_case (u:'b) f (SOME (x:'a)) = f x)`};

val option_APPLY_DEF = 
 new_recursive_definition {name="option_APPLY_DEF", fixity=Term.Prefix,
    rec_axiom=option_Axiom_orig,
    def = 
    Term`(option_APPLY (f:'a->'b) (SOME x) = SOME (f x)) /\ 
         (option_APPLY f NONE = NONE)`};

val IS_SOME_DEF = 
 new_recursive_definition {name="IS_SOME_DEF", fixity=Term.Prefix,
    rec_axiom=option_Axiom_orig,
    def = Term`(IS_SOME (SOME x) = T) 
            /\ (IS_SOME NONE = F)`};

val IS_NONE_DEF = 
 new_recursive_definition {name="IS_NONE_DEF", fixity=Term.Prefix,
    rec_axiom=option_Axiom_orig,
    def = Term`(IS_NONE (SOME x) = F) 
            /\ (IS_NONE NONE = T)`};

val THE_DEF = 
 new_recursive_definition {name="THE_DEF", fixity=Term.Prefix,
    rec_axiom=option_Axiom_orig,
    def = Term `THE (SOME x) = x`};

val option_rws = 
    [IS_SOME_DEF, THE_DEF, IS_NONE_DEF, option_nchotomy,
     NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, option_case_def,
     option_APPLY_DEF];

val ex1_rw = prove(Term`!x. (?y. x = y) /\ (?y. y = x)`,
   GEN_TAC THEN CONJ_TAC THEN EXISTS_TAC (Term`x`) THEN REFL_TAC);

fun OPTION_CASES_TAC t = STRUCT_CASES_TAC (ISPEC t option_nchotomy);

val IS_NONE_EQ_NONE = prove(
(--`!x. IS_NONE x = (x = NONE)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val NOT_IS_SOME_EQ_NONE = prove((--`!x. ~(IS_SOME x) = (x = NONE)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_EQ_EXISTS = prove(
(--`!x. IS_SOME x = (?v. x = SOME v)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC (ex1_rw::option_rws)
);


val IS_SOME_IMP_SOME_THE_CANCEL = prove(
(--`!x:'a option. IS_SOME x ==> (SOME (THE x) = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val option_case_ID = prove(
(--`!x:'a option. option_case NONE SOME x = x`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_option_case_SOME = prove(
(--`!x:'a option. IS_SOME x ==> (option_case e SOME x = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val option_case_SOME_ID = prove(
(--`!x:'a option. (option_case x SOME x = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_option_case = prove(
(--`!x:'a option. IS_SOME x ==> (option_case e (f:'a->'b) x = f (THE x))`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);


val IS_NONE_option_case = prove(
(--`!x:'a option. IS_NONE x ==> (option_case e f x = (e:'b))`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_REWRITE_TAC option_rws
);


val option_CLAUSES = save_thm("option_CLAUSES", 
     LIST_CONJ ([SOME_11,THE_DEF,NOT_NONE_SOME,NOT_SOME_NONE]@
                (CONJUNCTS IS_SOME_DEF)@
                [IS_NONE_EQ_NONE,
                 NOT_IS_SOME_EQ_NONE,
                 IS_SOME_IMP_SOME_THE_CANCEL,
                 option_case_ID,
                 option_case_SOME_ID,
                 IS_NONE_option_case,
                 IS_SOME_option_case,
                 IS_SOME_option_case_SOME]@
                (CONJUNCTS option_case_def)@
                (CONJUNCTS option_APPLY_DEF)));

val option_case_cong = 
  save_thm("option_case_cong", 
      Prim_rec.case_cong_thm option_nchotomy option_case_def);

val _ = adjoin_to_theory
{sig_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in
    S "val option_Induct : thm"; NL();
    S "val option_CASES : thm"
  end),
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in
    S "val _ = TypeBase.write";            NL();
    S "  (TypeBase.mk_tyinfo";             NL();
    S "     {ax=option_Axiom,";            NL();
    S "      case_def=option_case_def,";   NL();
    S "      case_cong=option_case_cong,"; NL();
    S "      induction=option_induction,"; NL();
    S "      nchotomy=option_nchotomy,";   NL();
    S "      size=NONE,";                  NL();
    S "      one_one=SOME SOME_11,";       NL();
    S "      distinct=SOME NOT_NONE_SOME});"; NL();
    NL();
    S "val option_Induct = Rewrite.ONCE_REWRITE_RULE "; NL();
    S "                      [boolTheory.CONJ_SYM] option_induction"; NL();
    S "val option_CASES = Rewrite.ONCE_REWRITE_RULE "; NL();
    S "                      [boolTheory.DISJ_SYM] option_nchotomy"
  end)};

val _ = export_theory();
