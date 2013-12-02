(* file HS/Ord/totoScript.sml, created 12/21-30/09 as TotOrdScript, L. Morris *)
(* Revised to make part of efficient-set-represetation project Feb.14 2012 *)
(* Revised for PIN directory April 14 2013; revised for intto Sept 23 2013 *)
(* Revised to narrow interface with wotTheory Sept 27 2013. *)

(* ******************************************************************  *)
(* Basic theory of total orders modeled not as in relation theory, but *)
(* rather in imitation of ML's facilities stemming from the 3-element  *)
(* "order" type - here called "cpn" for "comparison". It is believed   *)
(* that total orders done this way will lead to more efficient         *)
(* conversions implementing the common algorithms and data structures  *)
(* based on a total order.                                             *)
(* ******************************************************************  *)

structure totoScript = struct

(* app load ["wotTheory", "stringTheory", "intLib"]; *)

open HolKernel boolLib Parse;

val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory pairTheory;
open bossLib PairRules arithmeticTheory numeralTheory Defn;
open stringTheory listTheory intLib;

val _ = new_theory "toto";

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val _ = intLib.deprecate_int (); (* at least unti intto, actually throughout *)

val _ = Defn.def_suffix := ""; (* replacing default "_def" *)

(* ***************************************************************** *)
(* Following switch, BigSig, allows "maybe_thm" to act either as     *)
(* store_thm or as prove, thus maximizing or minimizing the output   *)
(* from print_theory and the stuff known to DB.match, DB.find        *)
(* ***************************************************************** *)

val BigSig = false;

fun maybe_thm (s, tm, tac) = if BigSig then store_thm (s, tm, tac)
                                       else prove (tm, tac);

val _ = type_abbrev ("reln", Type`:'a->'a->bool`);

(* **************************************************************** *)
(* Make our one appeal to wotTheory. To condense all its goodness   *)
(* into one theorem, wotTheory proves that, at any type, some reln. *)
(* satisfies both StrongLinearOrder and WF. Here we only need the   *)
(* StrongLinearOrder part, which might be supplied from elsewhere.  *)
(* **************************************************************** *)

val StrongLinearOrderExists = maybe_thm ("StrongLinearOrderExists",
``?R:'a reln. StrongLinearOrder R``,
METIS_TAC [wotTheory.StrongWellOrderExists]);

(* Define cpn: *)

val _ = Hol_datatype `cpn = LESS | EQUAL | GREATER`;

val cpn_distinct = theorem "cpn_distinct";
(*  |- LESS <> EQUAL /\ LESS <> GREATER /\ EQUAL <> GREATER *)

val cpn_case_def = theorem "cpn_case_def";

(* cpn_case_def =
|- (!v0 v1 v2. (case LESS of LESS => v0 | EQUAL => v1 | GREATER => v2) = v0) /\
   (!v0 v1 v2. (case EQUAL of LESS => v0 | EQUAL => v1 | GREATER => v2) = v1) /\
   !v0 v1 v2. (case GREATER of LESS => v0 | EQUAL => v1 | GREATER => v2) = v2 *)

val cpn_nchotomy = theorem "cpn_nchotomy";

(* Define being a (cpn-valued) total order: *)

val _ = type_abbrev ("comp", Type`:'a->'a->cpn`);

val TotOrd = Define`TotOrd (c: 'a comp) =
   (!x y. (c x y = EQUAL) <=> (x = y)) /\
   (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
   (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z = LESS))`;

val TO_of_LinearOrder = Define
 `TO_of_LinearOrder (r:'a->'a->bool) x y =
   if x = y then EQUAL else if r x y then LESS
                                     else GREATER`;

(* lemma to ease use of "trichotomous" and work with disjunctions *)

val trichotomous_ALT = maybe_thm ("trichotomous_ALT", Term`!R:'a->'a->bool.
   trichotomous R <=> !x y. ~R x y /\ ~R y x ==> (x = y)`,
REWRITE_TAC [trichotomous, IMP_DISJ_THM, DE_MORGAN_THM, GSYM DISJ_ASSOC]);

val TotOrd_TO_of_LO = maybe_thm ("TotOrd_TO_of_LO",Term`!r:'a->'a->bool.
                 LinearOrder r ==> TotOrd (TO_of_LinearOrder r)`,
RW_TAC (srw_ss ()) [LinearOrder, Order, antisymmetric_def,
    transitive_def, TO_of_LinearOrder, TotOrd, trichotomous_ALT] THEN
METIS_TAC [cpn_distinct]);

(* Utility theorem for equality of pairs: *)

val SPLIT_PAIRS = maybe_thm ("SPLIT_PAIRS",
 Term`!x y:'a#'b. (x = y) <=> (FST x = FST y) /\ (SND x = SND y)`,
REPEAT GEN_TAC THEN
CONV_TAC (LAND_CONV (BINOP_CONV (REWR_CONV (GSYM PAIR)))) THEN 
REWRITE_TAC [PAIR_EQ]);

(* cpn_nchotomy = |- !a. (a = LESS) \/ (a = EQUAL) \/ (a = GREATER) *)

(* cpn_distinct |- LESS <> EQUAL /\ LESS <> GREATER /\ EQUAL <> GREATER *)

val all_cpn_distinct = save_thm ("all_cpn_distinct",
CONJ cpn_distinct (GSYM cpn_distinct));

(* We now follow boilerplate from S-K Chin, aclFoundationScript *)

val TO_exists = maybe_thm ("TO_exists", Term`?x:'a comp. TotOrd x`,
STRIP_ASSUME_TAC StrongLinearOrderExists THEN
Q.EXISTS_TAC `TO_of_LinearOrder R` THEN
MATCH_MP_TAC TotOrd_TO_of_LO THEN
METIS_TAC [StrongLinearOrder, LinearOrder, StrongOrd_Ord]);

val toto_type_definition = new_type_definition ("toto", TO_exists);
(* toto_type_definition =
|- ?(rep :'x toto -> 'x comp). TYPE_DEFINITION (TotOrd :'x comp -> bool) rep*)

(* but we call the representation function "apto", rather than rep_anything,
   because we always need it when applying an a' toto to arguments. *)

val to_bij = define_new_type_bijections
     {name="to_bij", ABS="TO", REP="apto", tyax=toto_type_definition};

val [TO_apto_ID, TO_apto_TO_ID] = map2 (curry save_thm)
    ["TO_apto_ID", "TO_apto_TO_ID"]
    (CONJUNCTS to_bij);

(* TO_apto_ID = |- !(a :'x toto). TO (apto a) = a : thm
   TO_apto_TO_ID = |- !(r :'x comp). TotOrd r <=> (apto (TO r) = r) *)

val TO_11 = save_thm ("TO_11", prove_abs_fn_one_one to_bij);

(* TO_11 = |- !(r :'x comp) (r' :'x comp).
              TotOrd r ==> TotOrd r' ==> ((TO r = TO r') <=> (r = r')) *)

val onto_apto = save_thm ("onto_apto", prove_rep_fn_onto to_bij);

(* onto_apto = |- !(r :'x comp). TotOrd r <=> ?(a :'x toto). r = apto a *)

val TO_onto = save_thm ("TO_onto", prove_abs_fn_onto to_bij);

(* TO_onto = |- !(a :'x toto). ?(r :'x comp). (a = TO r) /\ TotOrd r *)

(* With introduction of 'a toto, we should now have "... c:'a toto ..."
   wherever was previously "TotOrd (c:'a comp) ==> ... c ... . *)

val TotOrd_apto = store_thm ("TotOrd_apto", Term`!c:'a toto. TotOrd (apto c)`,
GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 (ISPEC (Term`apto (c:'a toto)`)
                      (REWRITE_RULE [EQ_IMP_THM] onto_apto))) THEN
EXISTS_TAC (Term`c:'a toto`) THEN REFL_TAC);

val TO_apto_TO_IMP = save_thm ("TO_apto_TO_IMP",
GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL TO_apto_TO_ID))));

(* TO_apto_TO_IMP = |- !r. TotOrd r ==> (apto (TO r) = r) *)

val toto_thm = maybe_thm ("toto_thm", Term
`!c:'a toto. (!x y. (apto c x y = EQUAL) <=> (x = y)) /\
             (!x y. (apto c x y = GREATER) <=> (apto c y x = LESS)) /\
(!x y z. (apto c x y = LESS) /\ (apto c y z = LESS) ==> (apto c x z = LESS))`,
MATCH_ACCEPT_TAC (REWRITE_RULE [TotOrd] TotOrd_apto));

val TO_equal_eq = maybe_thm ("TO_equal_eq",
Term`!c:'a comp. TotOrd c ==> (!x y. (c x y = EQUAL) <=> (x = y))`,
REWRITE_TAC [TotOrd] THEN REPEAT STRIP_TAC THEN AR);

val toto_equal_eq = store_thm ("toto_equal_eq",
Term`!c:'a toto x y. (apto c x y = EQUAL) <=> (x = y)`,
REWRITE_TAC [toto_thm]);

val toto_equal_imp_eq = store_thm ("toto_equal_imp_eq",
Term`!c:'a toto x y. (apto c x y = EQUAL) ==> (x = y)`,
REWRITE_TAC [toto_equal_eq]);

val TO_refl = store_thm ("TO_refl",
Term`!c:'a comp. TotOrd c ==> (!x. c x x = EQUAL)`,
REPEAT STRIP_TAC THEN
IMP_RES_THEN (MATCH_MP_TAC o snd o EQ_IMP_RULE o SPEC_ALL) TO_equal_eq THEN
REFL_TAC);

val toto_refl = store_thm ("toto_refl",
Term`!c:'a toto x. apto c x x = EQUAL`,
REWRITE_TAC [toto_thm]);

val toto_equal_sym = store_thm ("toto_equal_sym",
Term`!c:'a toto x y. (apto c x y = EQUAL) <=> (apto c y x = EQUAL)`,
REWRITE_TAC [toto_equal_eq] THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);

val TO_antisym = maybe_thm ("TO_antisym",
Term`!c:'a comp. TotOrd c ==> (!x y. (c x y = GREATER) <=> (c y x = LESS))`,
REWRITE_TAC [TotOrd] THEN REPEAT STRIP_TAC THEN AR);

val toto_antisym = store_thm ("toto_antisym",
Term`!c:'a toto x y. (apto c x y = GREATER) <=> (apto c y x = LESS)`,
REWRITE_TAC [toto_thm]);

val toto_not_less_refl = store_thm ("toto_not_less_refl",
``!cmp:'a toto h. (apto cmp h h = LESS) <=> F``,
RW_TAC (srw_ss ()) [toto_antisym, toto_refl]);

val toto_swap_cases = store_thm ("toto_swap_cases",
Term`!c:'a toto x y. apto c y x =
  case apto c x y of LESS => GREATER | EQUAL => EQUAL | GREATER => LESS`,
REPEAT GEN_TAC THEN Cases_on `apto c x y` THEN
REWRITE_TAC [cpn_case_def] THENL
[IMP_RES_TAC toto_antisym
,IMP_RES_TAC toto_equal_sym
,IMP_RES_TAC toto_antisym]);

val toto_glneq = store_thm ("toto_glneq", Term
`(!c x y:'a. (apto c x y = LESS) ==> x <> y) /\
 (!c x y:'a. (apto c x y = GREATER) ==> x <> y)`,
CONJ_TAC THEN REPEAT GEN_TAC THEN
SUBST1_TAC (SYM (SPEC_ALL toto_equal_eq)) THEN
DISCH_TAC THEN ASM_REWRITE_TAC [all_cpn_distinct]);

val toto_cpn_eqn = save_thm ("toto_cpn_eqn",CONJ toto_equal_imp_eq toto_glneq);

(* toto_cpn_eqn = |- (!c x y. (apto c x y = EQUAL) ==> (x = y)) /\
                     (!c x y. (apto c x y = LESS) ==> x <> y) /\
                      !c x y. (apto c x y = GREATER) ==> x <> y    *)

val TO_cpn_eqn = maybe_thm ("TO_cpn_eqn", Term
`!c. TotOrd c ==> (!x y:'a. (c x y = LESS) ==> x <> y) /\
                  (!x y:'a. (c x y = GREATER) ==> x <> y) /\
                  (!x y:'a. (c x y = EQUAL) ==> (x = y))`,
GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
IMP_RES_THEN (SUBST1_TAC o SYM o SPEC_ALL) TO_equal_eq THEN
DISCH_TAC THEN ASM_REWRITE_TAC [all_cpn_distinct]);

val NOT_EQ_LESS_IMP = store_thm ("NOT_EQ_LESS_IMP",
``!cmp:'a toto x y. apto cmp x y <> LESS ==> (x = y) \/ (apto cmp y x = LESS)``,
METIS_TAC [cpn_nchotomy, toto_equal_eq, toto_antisym]);

(* Seven forms of transitivity: *)

val totoEEtrans = store_thm ("totoEEtrans", Term`!c:'a toto x y z.
 ((apto c x y = EQUAL) /\ (apto c y z = EQUAL) ==> (apto c x z = EQUAL)) /\
 ((apto c x y = EQUAL) /\ (apto c z y = EQUAL) ==> (apto c x z = EQUAL))`,
REPEAT GEN_TAC THEN REWRITE_TAC [toto_equal_eq] THEN REPEAT STRIP_TAC THEN AR);

val totoLLtrans = store_thm ("totoLLtrans", Term`!c:'a toto x y z.
 (apto c x y = LESS) /\ (apto c y z = LESS) ==> (apto c x z = LESS)`,
REWRITE_TAC [toto_thm]);

val totoLGtrans = store_thm ("totoLGtrans", Term`!c:'a toto x y z.
 (apto c x y = LESS) /\ (apto c z y = GREATER) ==> (apto c x z = LESS)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC toto_antisym THEN IMP_RES_TAC totoLLtrans);

val totoGGtrans = store_thm ("totoGGtrans", Term`!c:'a toto x y z.
 (apto c y x = GREATER) /\ (apto c z y = GREATER) ==> (apto c x z = LESS)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC toto_antisym THEN IMP_RES_TAC totoLLtrans);

val totoGLtrans = store_thm ("totoGLtrans", Term`!c:'a toto x y z.
 (apto c y x = GREATER) /\ (apto c y z = LESS) ==> (apto c x z = LESS)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC toto_antisym THEN IMP_RES_TAC totoLLtrans);

val totoLEtrans = store_thm ("totoLEtrans", Term`!c:'a toto x y z.
 (apto c x y = LESS) /\ (apto c y z = EQUAL) ==> (apto c x z = LESS)`,
REWRITE_TAC [toto_equal_eq] THEN
PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REPEAT STRIP_TAC THEN AR);

val totoELtrans = store_thm ("totoELtrans", Term`!c:'a toto x y z.
 (apto c x y = EQUAL) /\ (apto c y z = LESS) ==> (apto c x z = LESS)`,
REWRITE_TAC [toto_equal_eq] THEN REPEAT STRIP_TAC THEN AR);

val toto_trans_less = save_thm ("toto_trans_less",
              CONJ totoLLtrans (CONJ totoLGtrans (CONJ totoGGtrans
                (CONJ totoGLtrans (CONJ totoLEtrans totoELtrans)))));

val WeakLinearOrder_of_TO =
 Define`WeakLinearOrder_of_TO (c:'a comp) x y = 
        case c x y of LESS => T | EQUAL => T | GREATER => F`;

val StrongLinearOrder_of_TO =
 Define`StrongLinearOrder_of_TO (c:'a comp) x y =
        case c x y of LESS => T | EQUAL => F | GREATER => F`;

(* TO_of_LinearOrder is defined in totoTheory. *)

val toto_of_LinearOrder = Define
`toto_of_LinearOrder (r:'a reln) = TO (TO_of_LinearOrder r)`;

val Weak_Weak_of = maybe_thm ("Weak_Weak_of",
Term`!c:'a toto. WeakLinearOrder (WeakLinearOrder_of_TO (apto c))`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [WeakLinearOrder, WeakOrder, reflexive_def, antisymmetric_def,
             transitive_def, trichotomous, WeakLinearOrder_of_TO] THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
[REWRITE_TAC [toto_refl, cpn_case_def]
,Cases_on `apto c x y` THENL
 [IMP_RES_TAC toto_antisym THEN ASM_REWRITE_TAC [cpn_case_def]
 ,IMP_RES_TAC toto_equal_eq THEN AR
 ,IMP_RES_TAC toto_antisym THEN ASM_REWRITE_TAC [cpn_case_def]
 ]
,Cases_on `apto c x y` THEN REWRITE_TAC [cpn_case_def] THENL
 [Cases_on `apto c y z` THEN REWRITE_TAC [cpn_case_def] THENL
  [IMP_RES_TAC totoLLtrans THEN ASM_REWRITE_TAC [cpn_case_def]
  ,IMP_RES_TAC totoLEtrans THEN ASM_REWRITE_TAC [cpn_case_def]
  ]
 ,Cases_on `apto c y z` THEN REWRITE_TAC [cpn_case_def] THENL
  [IMP_RES_TAC totoELtrans THEN ASM_REWRITE_TAC [cpn_case_def]
  ,IMP_RES_TAC toto_equal_eq THEN ASM_REWRITE_TAC [toto_refl, cpn_case_def]
 ]]
,Cases_on `apto c a b` THEN IMP_RES_TAC toto_antisym THEN
 IMP_RES_TAC toto_equal_sym THEN ASM_REWRITE_TAC [cpn_case_def]
]);

(* repeated from wotTheory (should be in relationTheory): *)

val STRORD_trich = prove (
``!R:'a reln. trichotomous R <=> trichotomous (STRORD R)``,
RW_TAC (srw_ss ()) [STRORD, trichotomous] THEN METIS_TAC []);

val STRORD_SLO = maybe_thm ("STRORD_SLO", Term`!R:'a reln.
                      WeakLinearOrder R ==> StrongLinearOrder (STRORD R)`,
RW_TAC bool_ss [WeakLinearOrder, StrongLinearOrder, GSYM STRORD_trich] THEN
METIS_TAC [WeakOrd_Ord, STRORD_Strong]);

val Strongof_toto_STRORD = maybe_thm ("Strongof_toto_STRORD", Term`!c:'a toto.
StrongLinearOrder_of_TO (apto c) = STRORD (WeakLinearOrder_of_TO (apto c))`,
REPEAT STRIP_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [StrongLinearOrder_of_TO, STRORD, WeakLinearOrder_of_TO] THEN
Cases_on `apto c x x'` THEN ASM_REWRITE_TAC [cpn_case_def] THEN
ONCE_REWRITE_TAC [GSYM toto_equal_eq] THEN ASM_REWRITE_TAC [cpn_distinct]);

(* Previous three theorems all to avoid duplicating the Weak_Weak_of
   proof for Strong_Strong_of *)

val Strong_Strong_of = maybe_thm ("Strong_Strong_of", Term`!c:'a toto.
         StrongLinearOrder (StrongLinearOrder_of_TO (apto c))`,
GEN_TAC THEN REWRITE_TAC [Strongof_toto_STRORD] THEN
MATCH_MP_TAC STRORD_SLO THEN MATCH_ACCEPT_TAC Weak_Weak_of);

val Strong_Strong_of_TO = maybe_thm ("Strong_Strong_of_TO", Term`!c:'a comp.
        TotOrd c ==> StrongLinearOrder (StrongLinearOrder_of_TO c)`,
REPEAT STRIP_TAC THEN
IMP_RES_THEN (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o GSYM)
             TO_apto_TO_IMP THEN
MATCH_ACCEPT_TAC Strong_Strong_of);

val TotOrd_TO_of_Weak = maybe_thm("TotOrd_TO_of_Weak", Term`!r:'a reln.
                 WeakLinearOrder r ==> TotOrd (TO_of_LinearOrder r)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC TotOrd_TO_of_LO THEN
IMP_RES_TAC WeakLinearOrder THEN ASM_REWRITE_TAC [LinearOrder] THEN
IMP_RES_TAC WeakOrd_Ord);

val TotOrd_TO_of_Strong = maybe_thm("TotOrd_TO_of_Strong",Term`!r:'a reln.
                 StrongLinearOrder r ==> TotOrd (TO_of_LinearOrder r)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC TotOrd_TO_of_LO THEN
IMP_RES_TAC StrongLinearOrder THEN ASM_REWRITE_TAC [LinearOrder] THEN
IMP_RES_TAC StrongOrd_Ord);

val toto_Weak_thm = maybe_thm ("toto_Weak_thm", Term
`!c:'a toto. toto_of_LinearOrder (WeakLinearOrder_of_TO (apto c)) = c`,
GEN_TAC THEN REWRITE_TAC [toto_of_LinearOrder] THEN
CONV_TAC (RAND_CONV (REWR_CONV (GSYM TO_apto_ID))) THEN AP_TERM_TAC THEN
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [TO_of_LinearOrder, WeakLinearOrder_of_TO] THEN
Cases_on `x:'a = x'` THEN AR THENL
[ASM_REWRITE_TAC [toto_refl]
,Cases_on `apto c x x'` THEN ASM_REWRITE_TAC [cpn_case_def] THEN
 IMP_RES_TAC toto_equal_eq]);

val toto_Strong_thm = maybe_thm ("toto_Strong_thm", Term
`!c:'a toto. toto_of_LinearOrder (StrongLinearOrder_of_TO (apto c)) = c`,
GEN_TAC THEN REWRITE_TAC [toto_of_LinearOrder] THEN
CONV_TAC (RAND_CONV (REWR_CONV (GSYM TO_apto_ID))) THEN AP_TERM_TAC THEN
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [TO_of_LinearOrder, StrongLinearOrder_of_TO] THEN
Cases_on `x:'a = x'` THEN AR THENL
[ASM_REWRITE_TAC [toto_refl]
,Cases_on `apto c x x'` THEN ASM_REWRITE_TAC [cpn_case_def] THEN
 IMP_RES_TAC toto_equal_eq]);

val Weak_toto_thm = maybe_thm ("Weak_toto_thm",
Term`!r:'a reln. WeakLinearOrder r ==>
 (WeakLinearOrder_of_TO (apto (toto_of_LinearOrder r)) = r)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC TotOrd_TO_of_Weak THEN
IMP_RES_TAC WeakLinearOrder THEN IMP_RES_TAC WeakOrder THEN
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [toto_of_LinearOrder, WeakLinearOrder_of_TO] THEN
IMP_RES_THEN (REWRITE_TAC o ulist) TO_apto_TO_IMP THEN
REWRITE_TAC [TO_of_LinearOrder] THEN
Cases_on `x:'a = x'` THEN ASM_REWRITE_TAC [cpn_case_def] THENL
[IMP_RES_TAC reflexive_def THEN AR
,Cases_on `(r:'a reln) x x'` THEN AR THEN
 REWRITE_TAC [cpn_case_def]]);

val Strong_toto_thm = maybe_thm ("Strong_toto_thm",
Term`!r:'a reln. StrongLinearOrder r ==>
 (StrongLinearOrder_of_TO (apto (toto_of_LinearOrder r)) = r)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC TotOrd_TO_of_Strong THEN
IMP_RES_TAC StrongLinearOrder THEN IMP_RES_TAC StrongOrder THEN
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [toto_of_LinearOrder, StrongLinearOrder_of_TO] THEN
IMP_RES_THEN (REWRITE_TAC o ulist) TO_apto_TO_IMP THEN
REWRITE_TAC [TO_of_LinearOrder] THEN
Cases_on `x:'a = x'` THEN ASM_REWRITE_TAC [cpn_case_def] THENL
[IMP_RES_TAC irreflexive_def THEN AR
,Cases_on `(r:'a reln) x x'` THEN AR THEN
 REWRITE_TAC [cpn_case_def]]);

(* Converse of a total order; its correspondence to inv for relations. *)

val TO_inv = Define`TO_inv (c:'a comp) x y = c y x`;

val TotOrd_inv = maybe_thm ("TotOrd_inv", Term
`!c:'a comp. TotOrd c ==> TotOrd (TO_inv c)`,
GEN_TAC THEN REWRITE_TAC [TotOrd, TO_inv] THEN
REPEAT STRIP_TAC THEN AR THENL [MATCH_ACCEPT_TAC EQ_SYM_EQ, RES_TAC]);

val toto_inv = Define`toto_inv (c:'a toto) = TO (TO_inv (apto c))`;

val inv_TO = maybe_thm ("inv_TO", Term
`!r:'a comp. TotOrd r ==> (toto_inv (TO r) = TO (TO_inv r))`,
REPEAT STRIP_TAC THEN IMP_RES_TAC TO_apto_TO_IMP THEN
ASM_REWRITE_TAC [toto_inv]);

val apto_inv = maybe_thm ("apto_inv", Term
`!c:'a toto. apto (toto_inv c) = TO_inv (apto c)`,
METIS_TAC [TotOrd_apto, TO_apto_ID, TotOrd_inv, inv_TO, TO_apto_TO_IMP]);

val Weak_toto_inv = maybe_thm ("Weak_toto_inv", Term
`!c:'a toto. WeakLinearOrder_of_TO (apto (toto_inv c)) =
                                   inv (WeakLinearOrder_of_TO (apto c))`,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [WeakLinearOrder_of_TO, toto_inv, inv_DEF] THEN
ASSUME_TAC (SPEC_ALL TotOrd_apto) THEN IMP_RES_TAC TotOrd_inv THEN
IMP_RES_TAC TO_apto_TO_IMP THEN ASM_REWRITE_TAC [TO_inv]);

val Strong_toto_inv = maybe_thm ("Strong_toto_inv", Term
`!c:'a toto. StrongLinearOrder_of_TO (apto (toto_inv c)) =
                           inv (StrongLinearOrder_of_TO (apto c))`,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [StrongLinearOrder_of_TO, toto_inv, inv_DEF] THEN
ASSUME_TAC (SPEC_ALL TotOrd_apto) THEN IMP_RES_TAC TotOrd_inv THEN
IMP_RES_TAC TO_apto_TO_IMP THEN ASM_REWRITE_TAC [TO_inv]);

val TO_inv_TO_inv = maybe_thm ("TO_inv_TO_inv",
Term`!c:'a comp. TO_inv (TO_inv c) = c`,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [TO_inv]);

val toto_inv_toto_inv = maybe_thm ("toto_inv_toto_inv",
Term`!c:'a toto. toto_inv (toto_inv c) = c`,
REWRITE_TAC [toto_inv, apto_inv, TO_inv_TO_inv, TO_apto_ID]);

val TO_inv_Ord = maybe_thm ("TO_inv_Ord", Term`!r:'a reln.
 (TO_of_LinearOrder (inv r) = TO_inv (TO_of_LinearOrder r))`,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [TO_inv, inv_DEF, TO_of_LinearOrder] THEN
CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV EQ_SYM_EQ))) THEN REFL_TAC);

(* **** Translation of TotOrd cpn values back to relation truth values. **** *)

val TO_of_less_rel = maybe_thm ("TO_of_less_rel", Term
`!r:'a reln. StrongLinearOrder r ==>
 !x y. ((TO_of_LinearOrder r x y = LESS) <=> r x y)`,
REWRITE_TAC
 [StrongLinearOrder, StrongOrder, irreflexive_def, TO_of_LinearOrder] THEN
REPEAT STRIP_TAC THEN 
Cases_on `x=y` THEN ASM_REWRITE_TAC [all_cpn_distinct] THEN
Cases_on `r x y` THEN ASM_REWRITE_TAC [all_cpn_distinct]);

val TO_of_greater_ler = maybe_thm ("TO_of_greater_ler", Term
`!r:'a reln. StrongLinearOrder r ==>
 !x y. ((TO_of_LinearOrder r x y = GREATER) <=> r y x)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC TotOrd_TO_of_Strong THEN
IMP_RES_THEN (REWRITE_TAC o ulist) TO_antisym THEN
IMP_RES_THEN (REWRITE_TAC o ulist) TO_of_less_rel);

(* Consequences of TO_of_LenearOrder, toto_of_LinearOrder definitions,
   tailor-made for use by toto_CONV. *)

val toto_equal_imp = store_thm ("toto_equal_imp", Term
`!cmp:'a toto phi. LinearOrder phi /\ (cmp = toto_of_LinearOrder phi) ==>
                   !x y. ((x = y) = T) ==> (apto cmp x y = EQUAL)`,
REPEAT GEN_TAC THEN REWRITE_TAC [toto_of_LinearOrder] THEN
STRIP_TAC THEN AR THEN
IMP_RES_TAC TotOrd_TO_of_LO THEN
IMP_RES_THEN SUBST1_TAC TO_apto_TO_ID THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [TO_of_LinearOrder]);

val toto_unequal_imp = store_thm ("toto_unequal_imp", Term
`!cmp:'a toto phi. LinearOrder phi /\ (cmp = toto_of_LinearOrder phi) ==>
                   !x y. ((x = y) = F) ==>
                         (if phi x y
                          then apto cmp x y = LESS
                          else apto cmp x y =  GREATER)`,
REPEAT GEN_TAC THEN REWRITE_TAC [toto_of_LinearOrder] THEN
STRIP_TAC THEN AR THEN
IMP_RES_TAC TotOrd_TO_of_LO THEN
IMP_RES_THEN SUBST1_TAC TO_apto_TO_ID THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [TO_of_LinearOrder] THEN
Cases_on `phi x y` THEN AR);

(* TO_inv_Ord did not require r to be a linear order; hence no toto analog.*)

(* constructions of total orders to go with constructions on types;
   "lexicographic order" is the idea throughout. Since, as hinted by
   Exercise 3 after Sect. 6.6.3 in Gleason, Fundamentals of Abstract
   Analysis,  the domain ordering for functions must be a well-order, and
   WF and LEX are both defined in relationTheory, it seems most natural
   to work with StrongLinearOrder, and transfer the results to TotOrd. *)

val StrongOrder_ALT = maybe_thm ("StrongOrder_ALT",
 Term`!Z:'a reln. StrongOrder Z <=> irreflexive Z /\ transitive Z`,
GEN_TAC THEN REWRITE_TAC [StrongOrder] THEN EQ_TAC THEN
STRIP_TAC THEN AR THEN
REWRITE_TAC [antisymmetric_def] THEN
REPEAT STRIP_TAC THEN IMP_RES_TAC transitive_def THEN
IMP_RES_TAC irreflexive_def);

val _ = set_fixity "lexTO" (Infixr 850);
val _ = set_fixity "lextoto" (Infixr 850);

val LEX_ALT = maybe_thm ("LEX_ALT", Term`!R:'a reln U:'b->'b->bool c d.
(R LEX U) c d = R (FST c) (FST d) \/ (FST c = FST d) /\ U (SND c) (SND d)`,
REPEAT GEN_TAC THEN REWRITE_TAC [LEX_DEF] THEN
CONV_TAC (ONCE_DEPTH_CONV (PALPHA_CONV (Term`x:'a#'b`)) THENC
          LAND_CONV (RATOR_CONV BETA_CONV) THENC
          ONCE_DEPTH_CONV (PALPHA_CONV (Term`y:'a#'b`)) THENC
          LAND_CONV BETA_CONV)
THEN REFL_TAC);

val SLO_LEX =  maybe_thm ("SLO_LEX", Term`!R:'a reln V:'b->'b->bool.
StrongLinearOrder R /\ StrongLinearOrder V ==> StrongLinearOrder (R LEX V)`,
REWRITE_TAC [StrongLinearOrder] THEN REPEAT STRIP_TAC THEN
IMP_RES_TAC StrongOrder_ALT THENL
[REWRITE_TAC [StrongOrder_ALT, irreflexive_def, transitive_def, LEX_ALT] THEN
 REPEAT STRIP_TAC THEN IMP_RES_TAC irreflexive_def THENL
 [IMP_RES_TAC transitive_def THEN AR
 ,DISJ1_TAC THEN
  UNDISCH_THEN (Term`FST (y:'a#'b) = FST (z:'a#'b)`)
               (REWRITE_TAC o ulist o SYM) THEN AR
 ,AR
 ,IMP_RES_TAC transitive_def THEN AR
 ]
,IMP_RES_TAC trichotomous_ALT THEN
 REWRITE_TAC [trichotomous, LEX_ALT] THEN REPEAT GEN_TAC THEN
 Cases_on `R:'a reln (FST (a:'a#'b)) (FST (b:'a#'b))` THEN AR THEN
 Cases_on `R:'a reln (FST (b:'a#'b)) (FST (a:'a#'b))` THEN AR THEN
 RES_TAC THEN UNDISCH_TAC (Term`FST (b:'a#'b) = FST (a:'a#'b)`) THEN AR THEN
 Cases_on `V:'b->'b->bool (SND (a:'a#'b)) (SND (b:'a#'b))` THEN AR THEN
 Cases_on `V:'b->'b->bool (SND (b:'a#'b)) (SND (a:'a#'b))` THEN AR THEN
 RES_TAC THEN UNDISCH_TAC (Term`SND (b:'a#'b) = SND (a:'a#'b)`) THEN
              UNDISCH_TAC (Term`FST (b:'a#'b) = FST (a:'a#'b)`) THEN
 ASM_REWRITE_TAC [SPLIT_PAIRS]
]);

val lexTO = Define`(R:'a comp) lexTO (V:'b comp) = TO_of_LinearOrder (
  StrongLinearOrder_of_TO R LEX StrongLinearOrder_of_TO V)`;

val lextoto = Define
          `(c:'a toto) lextoto (v:'b toto) = TO (apto c lexTO apto v)`;

val lexTO_THM = maybe_thm ("lexTO_thm",
Term`!R:'a comp V:'b comp. TotOrd R /\ TotOrd V ==> !x y.
     ((R lexTO V) x y = case R (FST x) (FST y) of LESS => LESS |
                                            EQUAL => V (SND x) (SND y) |
                                            GREATER => GREATER)`,
REWRITE_TAC [TO_of_LinearOrder, lexTO, StrongLinearOrder_of_TO,
             LEX_ALT] THEN REPEAT STRIP_TAC THEN
REWRITE_TAC [SPLIT_PAIRS] THEN
Cases_on `FST (x:'a#'b) = FST (y:'a#'b)` THEN AR THENL
[IMP_RES_THEN (REWRITE_TAC o ulist) TO_refl THEN
 REWRITE_TAC [cpn_case_def] THEN
 Cases_on `SND (x:'a#'b) = SND (y:'a#'b)` THEN AR THENL
 [IMP_RES_THEN (REWRITE_TAC o ulist) TO_refl
 ,Cases_on `V:'b comp (SND (x:'a#'b)) (SND (y:'a#'b))` THEN
  ASM_REWRITE_TAC [cpn_case_def] THEN IMP_RES_TAC TO_equal_eq
 ]
,Cases_on `R (FST (x:'a#'b)) (FST (y:'a#'b))` THEN
 REWRITE_TAC [cpn_case_def] THEN IMP_RES_TAC TO_equal_eq
]);

val lexTO_ALT = maybe_thm ("lexTO_ALT", Term`!R:'a comp V:'b comp.
TotOrd R /\ TotOrd V ==> (!(r,u) (r',u'). (R lexTO V) (r,u) (r',u') =
   case R r r' of LESS => LESS | EQUAL => V u u'| GREATER => GREATER)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN
CONV_TAC (GEN_PALPHA_CONV (Term`x:'a#'b`)) THEN GEN_TAC THEN
CONV_TAC (GEN_PALPHA_CONV (Term`y:'a#'b`)) THEN GEN_TAC THEN
MATCH_MP_TAC lexTO_THM THEN AR);

val TO_lexTO = maybe_thm ("TO_lexTO", Term`!R:'a comp V:'b comp.
                          TotOrd R /\ TotOrd V ==> TotOrd (R lexTO V)`,
REPEAT STRIP_TAC THEN REWRITE_TAC [lexTO] THEN
MATCH_MP_TAC TotOrd_TO_of_Strong THEN
MATCH_MP_TAC SLO_LEX THEN CONJ_TAC THEN
IMP_RES_TAC Strong_Strong_of_TO);

val pre_aplextoto = maybe_thm ("pre_aplextoto",
Term`!c:'a toto v:'b toto x y.
     (apto (c lextoto v) x y = case apto c (FST x) (FST y) of LESS => LESS |
                                            EQUAL => apto v (SND x) (SND y) |
                                            GREATER => GREATER)`,
REPEAT GEN_TAC THEN REWRITE_TAC [lextoto] THEN
ASSUME_TAC (ISPEC (Term`c:'a toto`) TotOrd_apto) THEN
ASSUME_TAC (ISPEC (Term`v:'b toto`) TotOrd_apto) THEN
IMP_RES_TAC (GSYM lexTO_THM) THEN AR THEN REPEAT AP_THM_TAC THEN
MATCH_MP_TAC TO_apto_TO_IMP THEN
IMP_RES_TAC TO_lexTO);

val aplextoto = store_thm ("aplextoto", Term
`!c:'a toto v:'b toto x1 x2 y1 y2. (apto (c lextoto v) (x1,x2) (y1,y2) =
 case apto c x1 y1 of LESS => LESS
                  | EQUAL => apto v x2 y2
                | GREATER => GREATER)`,
REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [GSYM PAIR] THEN
REWRITE_TAC [pre_aplextoto]);

(* **** Some particular total order generators, additional to lextoto: **** *)

(* *********** num -- redone with numerals Oct. 2012 ************ *)

(* Theory: numto defined from numTheory.LESS *)

val StrongLinearOrder_LESS = maybe_thm ("StrongLinearOrder_LESS",
``StrongLinearOrder ($< :num reln)``,
RW_TAC (srw_ss ()) [StrongLinearOrder, StrongOrder_ALT,
trichotomous, Order, irreflexive_def, transitive_def] THENL
[IMP_RES_TAC LESS_TRANS
,STRIP_ASSUME_TAC (Q.SPECL [`a`, `b`] LESS_LESS_CASES) THEN AR]);
(* ****** 
val StrongWellOrder_LESS = maybe_thm ("StrongWellOrder_LESS",
 Term`StrongWellOrder ($< :num reln)`,
REWRITE_TAC [StrongWellOrder, prim_recTheory.WF_LESS, StrongLinearOrder,
 StrongOrder_ALT, trichotomous, Order, irreflexive_def, transitive_def]
THEN REPEAT CONJ_TAC THENL
[ACCEPT_TAC prim_recTheory.LESS_REFL
,ACCEPT_TAC LESS_TRANS
,REWRITE_TAC [DISJ_ASSOC] THEN ACCEPT_TAC (CONV_RULE (ONCE_DEPTH_CONV
               (REWR_CONV DISJ_SYM)) LESS_LESS_CASES)]);
**** *)
val numOrd = Define`numOrd = TO_of_LinearOrder ($< :num reln)`;

val TO_numOrd = store_thm ("TO_numOrd", Term`TotOrd numOrd`,
REWRITE_TAC [numOrd] THEN MATCH_MP_TAC TotOrd_TO_of_Strong THEN
ACCEPT_TAC StrongLinearOrder_LESS);

val numto = Define`numto = TO numOrd`;

val apnumto_thm = store_thm ("apnumto_thm", Term`apto numto = numOrd`,
REWRITE_TAC [numto, GSYM TO_apto_TO_ID, TO_numOrd]);

(* Practice: re_define numOrd, numto for computation on numerals. *)

val numeralOrd = store_thm ("numeralOrd", Term
`!x y.
 (numOrd ZERO ZERO = EQUAL) /\
 (numOrd ZERO (BIT1 y) = LESS) /\
 (numOrd ZERO (BIT2 y) = LESS) /\
 (numOrd (BIT1 x) ZERO = GREATER) /\
 (numOrd (BIT2 x) ZERO = GREATER) /\
 (numOrd (BIT1 x) (BIT1 y) = numOrd x y) /\
 (numOrd (BIT2 x) (BIT2 y) = numOrd x y) /\
 (numOrd (BIT1 x) (BIT2 y) =
  case numOrd x y of LESS => LESS | EQUAL => LESS | GREATER => GREATER) /\
 (numOrd (BIT2 x) (BIT1 y) =
  case numOrd x y of LESS => LESS | EQUAL => GREATER | GREATER => GREATER)`,
REPEAT GEN_TAC THEN
ASSUME_TAC (REWRITE_RULE [numOrd] (MATCH_MP TO_equal_eq TO_numOrd)) THEN
ASSUME_TAC (MATCH_MP TO_of_less_rel StrongLinearOrder_LESS) THEN
ASSUME_TAC (MATCH_MP TO_of_greater_ler StrongLinearOrder_LESS) THEN
REWRITE_TAC [numOrd] THEN Cases_on `TO_of_LinearOrder $< x y` THEN
RES_TAC THEN ASM_REWRITE_TAC [numeral_lt, cpn_case_def] THENL
[DISCH_TAC THEN IMP_RES_TAC LESS_ANTISYM
,MATCH_ACCEPT_TAC prim_recTheory.LESS_REFL
,DISCH_TAC THEN IMP_RES_TAC LESS_ANTISYM]);

(* ********************************************************************* *)
(*         qk_numto_CONV, a nonstandard ordering of num                  *)
(* ********************************************************************* *)

(* qk_numOrd is lexicographic ordering of numerals, regarded as binary
v   lists, least significant bit first. *)

(* Doubtless there is a better way, but all I can see to do is define
   a datatype like numerals as a crutch for getting qk_numOrd defined. *)

val _ = Hol_datatype `num_dt = zer | bit1 of num_dt | bit2 of num_dt`;

val num_to_dt_defn = Hol_defn "num_to_dt"
`num_to_dt n = if n = 0 then zer
               else if ODD n then bit1 (num_to_dt (DIV2 (n - 1)))
               else bit2 (num_to_dt (DIV2 (n - 2)))`;
                    
val half_lem = prove (Term`!m. m DIV 2 <= m`,
GEN_TAC THEN SIMP_TAC arith_ss [DIV_LESS_EQ]);

val (num_to_dt, num_to_dt_ind) = tprove (num_to_dt_defn,
WF_REL_TAC `measure I` THEN
CONJ_TAC THEN GEN_TAC THEN
SIMP_TAC arith_ss [DIV2_def] THEN STRIP_TAC THEN
MATCH_MP_TAC LESS_EQ_LESS_TRANS THENL
[EXISTS_TAC (Term`n - 1`), EXISTS_TAC (Term`n - 2`)] THEN
ASM_SIMP_TAC arith_ss [half_lem]);

val num_dtOrd = Define
`(num_dtOrd zer zer = EQUAL) /\
 (num_dtOrd zer (bit1 x) = LESS) /\
 (num_dtOrd zer (bit2 x) = LESS) /\
 (num_dtOrd (bit1 x) zer = GREATER) /\
 (num_dtOrd (bit2 x) zer = GREATER) /\
 (num_dtOrd (bit1 x) (bit2 y) = LESS) /\
 (num_dtOrd (bit2 x) (bit1 y) = GREATER) /\
 (num_dtOrd (bit1 x) (bit1 y) = num_dtOrd x y) /\
 (num_dtOrd (bit2 x) (bit2 y) = num_dtOrd x y)`;

val num_dt_distinct = theorem "num_dt_distinct";

val all_dt_distinct = CONJ num_dt_distinct (GSYM num_dt_distinct);

val num_dt_11 = theorem "num_dt_11";

val TO_num_dtOrd = prove (Term`TotOrd num_dtOrd`,
REWRITE_TAC [TotOrd] THEN REPEAT CONJ_TAC THEN
Induct THEN GEN_TAC THEN Cases_on `y` THEN
ASM_REWRITE_TAC [num_dtOrd, all_cpn_distinct, all_dt_distinct, num_dt_11] THEN
GEN_TAC THEN Cases_on `z` THEN
ASM_REWRITE_TAC [num_dtOrd, all_cpn_distinct, all_dt_distinct, num_dt_11]);

val qk_numOrd_def = xDefine "qk_numOrd_def"
`qk_numOrd m n = num_dtOrd (num_to_dt m) (num_to_dt n)`;

(* Most of the work to prove TO_qk_numOrd (below) comes in showing that
   num_to_dt is a bijection, which we do first, with help of some lemmas. *)

val zer_bit_neq = prove (Term`!P a b. zer <> (if P then bit1 a else bit2 b) /\
                                      (if P then bit1 a else bit2 b) <> zer`,
REPEAT GEN_TAC THEN CONJ_TAC THEN
Cases_on `P` THEN ASM_REWRITE_TAC [all_dt_distinct]);

val TWICE_DIV_2 = prove (Term`!n. 2 * n DIV 2 = n`,
GEN_TAC THEN
CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV MULT_COMM))) THEN
SUBGOAL_THEN (Term`0 < 2`) (REWRITE_TAC o ulist o MATCH_MP MULT_DIV) THEN
SIMP_TAC arith_ss []);

val DIV2_ODD_EQ = prove (Term
`!x y. x <> 0 /\ y <> 0 /\ ODD x /\ ODD y ==>
            (DIV2 (x - 1) = DIV2 (y - 1)) ==> (x = y)`,
REPEAT GEN_TAC THEN REWRITE_TAC [ODD_EXISTS] THEN STRIP_TAC THEN AR THEN
SIMP_TAC arith_ss [DIV2_def] THEN
REWRITE_TAC [TWICE_DIV_2] THEN DISCH_TAC THEN AR);

val EVEN_NZ = prove (Term`!z. z <> 0 /\ ~ODD z ==> z - 1 <> 0 /\ ODD (z - 1)`,
Cases THENL
[REWRITE_TAC []
,SIMP_TAC arith_ss [ODD] THEN Cases_on `n` THEN SIMP_TAC arith_ss [ODD]]);

val DIV2_EVEN_EQ = prove (Term
`x <> 0 /\ y <> 0 /\ ~ODD x /\ ~ODD y ==>
       (DIV2 (x - 2) = DIV2 (y - 2)) ==> (x = y)`,
STRIP_TAC THEN
SUBGOAL_THEN (Term`x - 1 <> 0 /\ y-1 <> 0 /\ ODD (x - 1) /\ ODD (y - 1)`)
             MP_TAC THENL
[IMP_RES_TAC EVEN_NZ THEN AR
,DISCH_THEN (fn cj => MP_TAC (MATCH_MP DIV2_ODD_EQ cj)) THEN
 SIMP_TAC arith_ss [] THEN
 DISCH_THEN (fn imp => DISCH_THEN (fn eq => MP_TAC (MATCH_MP imp eq))) THEN
 ASM_SIMP_TAC arith_ss []]);

val num_to_dt_bij = prove (Term`!x y. (num_to_dt x = num_to_dt y) <=> (x = y)`,
INDUCT_THEN num_to_dt_ind ASSUME_TAC THEN
INDUCT_THEN num_to_dt_ind ASSUME_TAC THEN
ONCE_REWRITE_TAC [num_to_dt] THEN EQ_TAC THENL
[Cases_on `x = 0` THEN Cases_on `y = 0` THEN
 ASM_REWRITE_TAC [zer_bit_neq] THEN
 Cases_on `ODD x` THEN Cases_on `ODD y` THEN RES_TAC THEN
 ASM_REWRITE_TAC [all_dt_distinct, num_dt_11] THENL
 [MATCH_MP_TAC DIV2_ODD_EQ THEN AR
 ,MATCH_MP_TAC DIV2_EVEN_EQ THEN AR]
,DISCH_TAC THEN AR]);

val TO_qk_numOrd = store_thm ("TO_qk_numOrd", Term`TotOrd qk_numOrd`,
REWRITE_TAC
 [TotOrd, qk_numOrd_def, REWRITE_RULE [TotOrd] TO_num_dtOrd] THEN
MATCH_ACCEPT_TAC num_to_dt_bij);

(* ******* At last we can prove (given a few more lemmas) what would ****** *)
(* ******* be a definition if only numeral were a datatype:          ****** *)

val ZERO_to_dt = prove (Term`num_to_dt ZERO = zer`,
ONCE_REWRITE_TAC [num_to_dt] THEN REWRITE_TAC [ALT_ZERO]);

val BIT_NZ = prove (Term`!n. BIT1 n <> 0 /\ BIT2 n <> 0`,
GEN_TAC THEN REWRITE_TAC [BIT1, BIT2] THEN
Cases_on `n` THEN SIMP_TAC arith_ss []);

val BIT1_to_dt = prove (Term`!n. num_to_dt (BIT1 n) = bit1 (num_to_dt n)`,
GEN_TAC THEN CONV_TAC (LAND_CONV (REWR_CONV num_to_dt)) THEN
REWRITE_TAC [numeral_evenodd, BIT_NZ, DIV2_def] THEN
REPEAT AP_TERM_TAC THEN
CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV BIT1)))) THEN
SIMP_TAC arith_ss [TWICE_DIV_2]);

val BIT2_to_dt = prove (Term`!n. num_to_dt (BIT2 n) = bit2 (num_to_dt n)`,
GEN_TAC THEN CONV_TAC (LAND_CONV (REWR_CONV num_to_dt)) THEN
REWRITE_TAC [numeral_evenodd, BIT_NZ, DIV2_def] THEN
REPEAT AP_TERM_TAC THEN
CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV BIT2)))) THEN
SIMP_TAC arith_ss [TWICE_DIV_2]);

val qk_numeralOrd = store_thm ("qk_numeralOrd", Term
`!x y.
 (qk_numOrd ZERO ZERO = EQUAL) /\
 (qk_numOrd ZERO (BIT1 y) = LESS) /\
 (qk_numOrd ZERO (BIT2 y) = LESS) /\
 (qk_numOrd (BIT1 x) ZERO = GREATER) /\
 (qk_numOrd (BIT2 x) ZERO = GREATER) /\
 (qk_numOrd (BIT1 x) (BIT1 y) = qk_numOrd x y) /\
 (qk_numOrd (BIT2 x) (BIT2 y) = qk_numOrd x y) /\
 (qk_numOrd (BIT1 x) (BIT2 y) = LESS) /\
 (qk_numOrd (BIT2 x) (BIT1 y) = GREATER)`,
REWRITE_TAC [qk_numOrd_def, ZERO_to_dt, BIT1_to_dt, BIT2_to_dt, num_dtOrd]);

(* ******** From here on we can imitate the treatment of numOrd ********** *)

val qk_numto = Define`qk_numto = TO qk_numOrd`;

val ap_qk_numto_thm = store_thm ("ap_qk_numto_thm", Term
`apto qk_numto = qk_numOrd`,
REWRITE_TAC [qk_numto, GSYM TO_apto_TO_ID, TO_qk_numOrd]);

(* ******************************************************************** *)
(* charOrd seems to be a serious problem. It takes some ingenuity to    *)
(* make one character comparison with only two num comparisons, and I   *)
(* see no way to bring that down to one.                                *)
(* ******************************************************************** *)

val charOrd = Define`charOrd (a:char) (b:char) = numOrd (ORD a) (ORD b)`;

val charto = Define`charto = TO (charOrd)`;

val TO_charOrd = maybe_thm ("TO_charOrd", Term`TotOrd charOrd`,
REWRITE_TAC [TotOrd, charOrd] THEN
STRIP_ASSUME_TAC (REWRITE_RULE [TotOrd] TO_numOrd) THEN
REPEAT STRIP_TAC THEN AR THENL
[MATCH_ACCEPT_TAC ORD_11, RES_TAC]);

val apcharto_thm = store_thm ("apcharto_thm", Term`apto charto = charOrd`,
REWRITE_TAC [charto, SYM (ISPEC (Term`charOrd`) TO_apto_TO_ID), TO_charOrd]);

val charOrd_lt_lem = store_thm ("charOrd_lt_lem", Term`!a b.
 (numOrd a b = LESS) ==> (b < 256 = T) ==> (charOrd (CHR a) (CHR b) = LESS)`,
REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
SUBGOAL_THEN (Term`a:num < b`) ASSUME_TAC THENL
[SUBGOAL_THEN (Term`(numOrd a b = LESS) <=> a < b`)
              (ASM_REWRITE_TAC o ulist o SYM) THEN
 REWRITE_TAC [numOrd] THEN MATCH_MP_TAC TO_of_less_rel THEN
 ACCEPT_TAC StrongLinearOrder_LESS
,IMP_RES_TAC LESS_TRANS THEN REWRITE_TAC [charOrd] THEN
 IMP_RES_THEN SUBST1_TAC ORD_CHR_RWT THEN AR]);

val charOrd_gt_lem = store_thm ("charOrd_gt_lem", Term
`!a b. (numOrd a b = GREATER) ==> (a < 256 = T) ==>
 (charOrd (CHR a) (CHR b) = GREATER)`,
REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
SUBGOAL_THEN (Term`b:num < a`) ASSUME_TAC THENL
[SUBGOAL_THEN (Term`(numOrd a b = GREATER) <=> b < a`)
              (ASM_REWRITE_TAC o ulist o SYM) THEN
 REWRITE_TAC [numOrd] THEN MATCH_MP_TAC TO_of_greater_ler THEN
 ACCEPT_TAC StrongLinearOrder_LESS
,IMP_RES_TAC LESS_TRANS THEN REWRITE_TAC [charOrd] THEN
 IMP_RES_THEN SUBST1_TAC ORD_CHR_RWT THEN AR]);

val charOrd_eq_lem = store_thm ("charOrd_eq_lem", Term
`!a b. (numOrd a b = EQUAL) ==> (charOrd (CHR a) (CHR b) = EQUAL)`,
REPEAT GEN_TAC THEN
REWRITE_TAC [charOrd, MATCH_MP TO_equal_eq TO_numOrd] THEN DISCH_TAC THEN AR);

val charOrd_thm = maybe_thm ("charOrd_thm", Term
`charOrd = TO_of_LinearOrder $<`,
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [charOrd, numOrd, TO_of_LinearOrder] THEN
REWRITE_TAC [char_lt_def, ORD_11]);

(* ********************************************************************** *)
(* A similar exercise to the above for lists should be useful itself, and *)
(*  an exemplar of how any datatype can be ordered if its components are. *)
(* ********************************************************************** *)

val listorder = Define`(listorder (V:'a reln) l [] = F) /\
                       (listorder V [] (s :: m) = T) /\
                       (listorder V (r :: l) (s :: m) =
                           V r s \/ (r = s) /\ listorder V l m)`;

val SLO_listorder = maybe_thm ("SLO_listorder", Term`!V:'a reln.
              StrongLinearOrder V ==> StrongLinearOrder (listorder V)`,
GEN_TAC THEN
REWRITE_TAC [StrongLinearOrder, StrongOrder_ALT] THEN
STRIP_TAC THEN
REWRITE_TAC [irreflexive_def, transitive_def, trichotomous_ALT] THEN
REPEAT CONJ_TAC THENL
[Induct THEN ASM_REWRITE_TAC [listorder, DE_MORGAN_THM] THEN
 IMP_RES_TAC irreflexive_def
,Induct THENL
 [REPEAT (Cases THEN REWRITE_TAC [listorder])
 ,REPEAT (GEN_TAC THEN Induct THEN ASM_REWRITE_TAC [listorder]) THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC transitive_def THEN RES_TAC THEN AR THEN
  UNDISCH_THEN (Term`(h':'a) = h''`) (ASM_REWRITE_TAC o ulist o SYM)
 ]
,Induct THENL
 [Cases THEN REWRITE_TAC [listorder]
 ,GEN_TAC THEN Induct THEN ASM_REWRITE_TAC [listorder] THEN
  GEN_TAC THEN Cases_on `(V:'a reln) h h'` THEN AR THEN
  Cases_on `(V:'a reln) h' h` THEN AR THEN
  IMP_RES_TAC trichotomous_ALT THEN
  UNDISCH_TAC (Term`h:'a = h'`) THEN AR THEN
  STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [CONS_11]
]]);

val ListOrd = Define`ListOrd (c:'a toto) =
         TO_of_LinearOrder (listorder (StrongLinearOrder_of_TO (apto c)))`;

val TO_ListOrd = maybe_thm ("TO_ListOrd", 
                         Term`!c:'a toto. TotOrd (ListOrd c)`,
GEN_TAC THEN REWRITE_TAC [ListOrd] THEN
ASSUME_TAC (ISPEC (Term`c:'a toto`) TotOrd_apto) THEN
IMP_RES_TAC Strong_Strong_of_TO THEN
IMP_RES_TAC SLO_listorder THEN
IMP_RES_TAC TotOrd_TO_of_Strong);

val ListOrd_THM = maybe_thm ("ListOrd_THM",
Term`(!c:'a toto. (ListOrd c ([]:'a list) [] = EQUAL) /\
     (!b:'a y. ListOrd c [] (b :: y) = LESS) /\
     (!a:'a x. ListOrd c (a :: x) [] = GREATER) /\
     (!a:'a x b y. ListOrd c (a :: x) (b :: y) =
         case apto c a b of LESS => LESS |
                           EQUAL => ListOrd c  x y |
                           GREATER => GREATER))`,
GEN_TAC THEN ASSUME_TAC (SPEC_ALL TotOrd_apto) THEN
REWRITE_TAC [ListOrd, TO_of_LinearOrder, list_distinct, 
             GSYM list_distinct, list_11] THEN
IMP_RES_TAC Strong_Strong_of_TO THEN
REWRITE_TAC [listorder, StrongLinearOrder_of_TO] THEN
REPEAT GEN_TAC THEN
Cases_on `apto c a b` THEN
ASM_REWRITE_TAC [cpn_case_def, all_cpn_distinct] THEN
IMP_RES_TAC toto_cpn_eqn THEN ASM_REWRITE_TAC [all_cpn_distinct]);

val listoto = Define`listoto (c:'a toto) = TO (ListOrd c)`;

val aplistoto = store_thm ("aplistoto", Term`!c:'a toto.
(apto (listoto c) [] [] = EQUAL) /\
(!b y. apto (listoto c) [] (b :: y) = LESS) /\
(!a x. apto (listoto c) (a :: x) [] = GREATER) /\
(!a x b y. apto (listoto c) (a :: x) (b :: y) =
        case apto c a b of LESS => LESS |
                          EQUAL => apto (listoto c) x y |
                        GREATER => GREATER)`,
GEN_TAC THEN ASSUME_TAC (SPEC_ALL TO_ListOrd) THEN
REWRITE_TAC [listoto] THEN
IMP_RES_THEN (REWRITE_TAC o ulist) TO_apto_TO_IMP THEN
MATCH_ACCEPT_TAC ListOrd_THM);

(* ***** string a synonym for char list -- makes stringto very easy. ***** *)

val stringto = Define`stringto = listoto charto`;

(* *********************************************************************** *)
(* ********* what was btOrd, etc. to be rethought - April 2013 *********** *)
(*              (consult this section of ORT/TotOrdScript.sml)             *)
(* *********************************************************************** *)

(* ********************************************************************** *)
(* Following may be useful for obtaining total orders on abstract types   *)
(* from total orders on their representations.                            *)
(* ********************************************************************** *)
val imageOrd = Define`imageOrd (f:'a->'c) (cp:'c comp) a b = cp (f a) (f b)`;

val TO_injection = maybe_thm ("TO_injection", Term
`!cp:'c comp. TotOrd cp ==> !f:'d->'c.
           ONE_ONE f ==> TotOrd (imageOrd f cp)`,
REWRITE_TAC [TotOrd, imageOrd, ONE_ONE_THM] THEN REPEAT STRIP_TAC THEN
AR THEN RES_TAC THEN EQ_TAC THEN DISCH_TAC THEN RES_TAC THEN AR);

(* **************************************************************** *)
(* The following treatment of total order on type one is completely *)
(* silly, but might be prudent to have. SUPPRESSED FOR NOW.         *) 
(* **************************************************************** *)
(* ************************
val oneOrd = Define`oneOrd (x:one) (y:one) = EQUAL`;

val TO_oneOrd = maybe_thm ("TO_oneOrd", Term`TotOrd oneOrd`,
REWRITE_TAC [TotOrd, oneOrd, all_cpn_distinct] THEN
ONCE_REWRITE_TAC [one] THEN REWRITE_TAC []);

val oneto = Define`oneto = TO oneOrd`;

val aponeto = store_thm ("aponeto", Term`!x y. apto oneto x y = EQUAL`,
ASSUME_TAC TO_oneOrd THEN REWRITE_TAC [oneto] THEN
IMP_RES_THEN SUBST1_TAC TO_apto_TO_IMP THEN REWRITE_TAC [oneOrd]);
************************** *)

(* **************************************************************** *)
(* Theorems to support intto_CONV, for comparing at type int.       *)
(* **************************************************************** *)

(* integer parsing remains deprecated; note use of suffix i below. *)

(* An integer ground term is, as well as I can see, either a application of
   ``$&`` to a num ground term (which is either ``0`` or an application
   of NUMERAL to a pile of ZERO, BIT0, and BIT1) or an application of
   numeric_negate:int -> int to such a &-application. ``-0`` is possible. *)

val intOrd = Define`intOrd = TO_of_LinearOrder ($< :int reln)`;

val StrongLinearOrder_int_lt = maybe_thm ("StrongLinearOrder_int_lt",
``StrongLinearOrder ($< :int reln)``,
RW_TAC (srw_ss ())[StrongLinearOrder,
 StrongOrder_ALT, trichotomous, Order, irreflexive_def, transitive_def] THENL
[IMP_RES_TAC integerTheory.INT_LT_TRANS
,STRIP_ASSUME_TAC (SPECL [``a:int``, ``b:int``] integerTheory.INT_LT_TOTAL)
 THEN AR]);

val TO_intOrd = maybe_thm ("TO_intOrd", ``TotOrd intOrd``,
REWRITE_TAC [intOrd] THEN MATCH_MP_TAC TotOrd_TO_of_Strong THEN
ACCEPT_TAC StrongLinearOrder_int_lt);

val intto = Define`intto = TO intOrd`;

val apintto_thm = store_thm ("apintto_thm", ``apto intto = intOrd``,
REWRITE_TAC [intto, GSYM TO_apto_TO_ID, TO_intOrd]);

val pos_pos_thm = store_thm ("pos_pos_thm",
``!m:num n:num. intOrd (&m) (&n) = numOrd m n``,
 RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, numOrd]);

val neg_neg_thm = store_thm ("neg_neg_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (numeric_negate (&n)) =
                numOrd n m``,
 RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, numOrd]);

val BIT1_nz = store_thm ("BIT1_nz",
``!n. BIT1 n <> 0``,
RW_TAC (srw_ss ()) [arithmeticTheory.NOT_ZERO_LT_ZERO, numeralTheory.numeral_lt,
                    GSYM arithmeticTheory.ALT_ZERO]);

val BIT2_nz = store_thm ("BIT2_nz",
``!n. BIT2 n <> 0``,
RW_TAC (srw_ss ()) [arithmeticTheory.NOT_ZERO_LT_ZERO, numeralTheory.numeral_lt,
                    GSYM arithmeticTheory.ALT_ZERO]);

val neg_lt_BIT1_thm = store_thm ("neg_lt_BIT1_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (& (BIT1 n)) = LESS``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT1_nz]);

val neg_lt_BIT2_thm = store_thm ("neg_lt_BIT2_thm",
``!m:num n:num. intOrd (numeric_negate (&m)) (& (BIT2 n)) = LESS``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT2_nz]);

val neg_BIT1_lt_thm = store_thm ("neg_BIT1_lt_thm",
``!m:num n:num. intOrd (numeric_negate (& (BIT1 m))) (& n) = LESS``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd,  BIT1_nz]);

val neg_BIT2_lt_thm = store_thm ("neg_BIT2_lt_thm",
``!m:num n:num. intOrd (numeric_negate (& (BIT2 m))) (& n) = LESS``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT2_nz]);

val neg_ZERO_eq_ZERO_thm = store_thm ("neg_ZERO_eq_ZERO_thm",
``intOrd (numeric_negate (& ZERO)) (& ZERO) = EQUAL``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, GSYM arithmeticTheory.ALT_ZERO]);

val BIT1_gt_neg_thm = store_thm ("BIT1_gt_neg_thm",
``!m:num n:num. intOrd (& (BIT1 m)) (numeric_negate (&n)) = GREATER``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT1_nz]);

val BIT2_gt_neg_thm = store_thm ("BIT2_gt_neg_thm",
``!m:num n:num. intOrd (& (BIT2 m)) (numeric_negate (&n)) = GREATER``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT2_nz]);

val gt_neg_BIT1_thm = store_thm ("gt_neg_BIT1_thm",
``!m:num n:num. intOrd (& m) (numeric_negate (& (BIT1 n))) = GREATER``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT1_nz]);

val gt_neg_BIT2_thm = store_thm ("gt_neg_BIT2_thm",
``!m:num n:num. intOrd (& m) (numeric_negate (& (BIT2 n))) = GREATER``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, BIT2_nz]);

val ZERO_eq_neg_ZERO_thm = store_thm ("ZERO_eq_neg_ZERO_thm",
``intOrd (& ZERO) (numeric_negate (& ZERO)) = EQUAL``,
RW_TAC (srw_ss ()) [TO_of_LinearOrder, intOrd, GSYM arithmeticTheory.ALT_ZERO]);

val _ = export_theory ();
val _ = print_theory "-";

end;
