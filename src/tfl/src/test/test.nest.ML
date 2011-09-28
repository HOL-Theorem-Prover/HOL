app load ["bossLib","Q"];
open bossLib; infix 8 by;

show_assums := true;

fun defn def_bind tm =
 Tfl.nested_function
    (TypeBase.theTypeBase()) def_bind
      (Tfl.wfrec_eqns (TypeBase.theTypeBase()) tm);


val N_defn =
 Hol_fun "N"
    `N(x) = if x>100 then x-10 else N (N (x+11))`;

val SOME N_aux_defn = Defn.aux_defn N_defn;


(*---------------------------------------------------------------------------
      Prove partial correctness for N, just to see how it works
      when no termination condition has been supplied.
 ---------------------------------------------------------------------------*)

val Neqns = Defn.eqns_of N_defn;
val SOME Nind = Defn.ind_of N_defn;


(*---------------------------------------------------------------------------
     Prove partial correctness.
 ---------------------------------------------------------------------------*)

val Npartly_correct = prove(Term
 `WF R /\
  (!x. ~(x > 100) ==> R (N_aux R (x + 11)) x) /\
  (!x. ~(x > 100) ==> R (x + 11) x)
     ==>
  !n. N(n) = if n>100 then n-10 else 91`,
STRIP_TAC THEN recInduct Nind
 THEN REPEAT STRIP_TAC
 THEN ONCE_REWRITE_TAC [Neqns]
 THEN RW_TAC base_ss []
 THENL [DECIDE_TAC   (* slow *),
        Q.PAT_ASSUM `p > q` MP_TAC
          THEN ASM_REWRITE_TAC[]
          THEN reduceLib.REDUCE_TAC]);

(*---------------------------------------------------------------------------
      Prove termination for N. This is done by proving the
      termination of N_aux. We choose the termination relation
      and make another definition, Nine1, just for simplicity.
 ---------------------------------------------------------------------------*)

val TR_def =
 Define
    `TR = measure \x. 101 - x`;

val Nine1_def =
 Define
    `Nine1 = N_aux TR`;

val WF_TR = Q.prove (`WF TR`,
RW_TAC base_ss [prim_recTheory.WF_measure,TR_def]);

val th = ISPEC (Term`TR`) relationTheory.WF_INDUCTION_THM;
val ind = CONV_RULE (Halts.TC_SIMP_CONV)
            (RW.RW_RULE[prim_recTheory.WF_measure,TR_def] th);

val lem0 = DECIDE`(~(x>100)) ==> (101-y < 101-x = x<y)`;
val lem  = Q.prove(`!x. ~(x>100) ==> TR (x + 11) x`,
RW_TAC arith_ss [prim_recTheory.measure_def,
                 relationTheory.inv_image_def,TR_def]);

val eqns0 = Q.INST [`R` |-> `TR`] (Defn.eqns_of N_aux_defn);
val eqns1 = REWRITE_RULE [GSYM Nine1_def,prim_recTheory.WF_measure,lem] eqns0;
val eqns = MP eqns1 WF_TR;

val eqn1 = Q.prove(`!x. x>100 ==> (Nine1 x = x-10)`,
RW_TAC base_ss []
   THEN MP_TAC eqns
    THEN ASM_REWRITE_TAC []);

val eqn2 = Q.prove
(`!x. ~(x>100) /\ x < Nine1 (x+11) ==> (Nine1 x = Nine1 (Nine1 (x+11)))`,
 RW_TAC base_ss [lem] THEN MP_TAC eqns
  THEN RW_TAC arith_ss
       [prim_recTheory.measure_def,relationTheory.inv_image_def,TR_def]);


val nested_tc = Q.prove
(`!x. ~(x > 100) ==> TR (Nine1 (x + 11)) x`,
RW_TAC base_ss
     [prim_recTheory.measure_def,relationTheory.inv_image_def,TR_def,lem0]
 THEN POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x`
 THEN recInduct ind THEN RW_TAC base_ss []
 THEN IMP_RES_THEN (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) lem0
 THEN Cases_on `x+11 > 100` THENL
 [RW_TAC arith_ss [eqn1],
  `x+11 < Nine1((x+11)+11)`  by PROVE_TAC [DECIDE `x<x+11`] THEN
  `x < Nine1((x+11)+11) -11` by PROVE_TAC[DECIDE`x + y < z = x < z-y`] THEN
  `Nine1 (x + 11) = Nine1 (Nine1 ((x + 11) + 11))` by PROVE_TAC[eqn2] THEN
  Cases_on `Nine1((x+11)+11) -11 > 100`
  THENL
  [`Nine1((x+11)+11) > 100` by PROVE_TAC[DECIDE`x-11 > 100 ==> x>100`] THEN
   `Nine1(Nine1((x+11)+11)) = Nine1((x+11)+11) -10` by PROVE_TAC[eqn1]
   THEN Q.PAT_ASSUM `Nine1 (x+11) = M` (SUBST_ALL_TAC o SYM)
   THEN PROVE_TAC [DECIDE `x>100 ==> x-11<x-10`,arithmeticTheory.LESS_TRANS],
   RES_TAC
     THEN IMP_RES_THEN SUBST_ALL_TAC (DECIDE`w+11<y ==> ((y-11)+11 = y)`)
     THEN PROVE_TAC [eqn2,arithmeticTheory.LESS_TRANS]]]);

val non_nested_tc = Q.prove
(`!x. ~(x > 100) ==> TR (x + 11) x`,
RW_TAC arith_ss
  [prim_recTheory.measure_def,relationTheory.inv_image_def,TR_def]);

val N_defn1 =
  Defn.inst_defn N_defn
      ([Term`R:num->num->bool` |-> Term`TR`], []);

val N_defn2 =
  Defn.elim_tcs N_defn1
     [WF_TR,non_nested_tc,
      REWRITE_RULE [Nine1_def] nested_tc];

val Neqns = Defn.eqns_of N_defn2;
val SOME Nind = Defn.ind_of N_defn2;


(*---------------------------------------------------------------------------
       Other examples.
 ---------------------------------------------------------------------------*)

val g_def = Hol_fun "g" `(g 0 = 0) /\ (g (SUC x) = g (g x))`;
val h_def = Hol_fun "h" `(h 0 = 0) /\ (h (SUC x) = h (h (h x)))`;
val j_def = Hol_fun "j" `j x = ((j (j (SUC x)) = x) => j (x+2) | 3)`;

val Conway_def =
 Hol_fun "Conway"
   `(C 0             = 1)
/\  (C (SUC 0)       = 1)
/\  (C (SUC (SUC 0)) = 1)
/\  (C   n           = C(C(n-1)) + C(n - C(n-1)))`;


(*---------------------------------------------------------------------------
     Test schematic nested defns.
 ---------------------------------------------------------------------------*)

val foo_def = defn "foo"
 (Term`foo(x) = (x>100 => decrten x | foo (foo (increleven x)))`);


(*---------------------------------------------------------------------------
     Proofs about the Conway function.
 ---------------------------------------------------------------------------*)

val conway_rules_ind =
 UNDISCH_ALL
  (INST [Term`R:num->num->bool` |-> Term`$<`]
    (PURE_REWRITE_RULE [arithmeticTheory.SUC_SUB1]
       (DISCH_ALL (#rules_ind Conway_def))));

open bossLib;
val TC1 = DECIDE`!v4. SUC (SUC v4) < SUC (SUC (SUC v4))`;
val conway0 = PROVE_HYP prim_recTheory.WF_LESS conway_rules_ind;
val conway1 = PROVE_HYP TC1 conway0;
val conway2 =
  UNDISCH_ALL
   (REWRITE_RULE [DECIDE `SUC x - y < SUC x = 0 < y`]
      (DISCH_ALL conway1));

val conway_aux = SPEC (Term`$<`) (#aux_rules Conway_def);
val D_def = Define `D = C1 $<`;
val conway_aux1 = REWRITE_RULE [SYM D_def] conway_aux;

(* This is useless! Need the TCs to be only attached to their clauses.
   Also, clauses with no recursion should have the WF(R) bit blown
   away as part of the definition process.
*)
val conway_aux2 =
  REWRITE_RULE [prim_recTheory.WF_LESS,arithmeticTheory.SUC_SUB1,
                TC1, DECIDE `SUC x - y < SUC x = 0 < y`,
                DECIDE `0 < 1`]
        conway_aux1;

val conway_aux_ind =
 REWRITE_RULE [SYM D_def, TC1,prim_recTheory.WF_LESS,
               DECIDE `SUC x - y < SUC x = 0 < y`]
   (INST [Term`R:num->num->bool` |-> Term`$<`]
    (PURE_REWRITE_RULE [arithmeticTheory.SUC_SUB1]
       (DISCH_ALL (#aux_ind Conway_def))));

load "tflLib";

g`!x. 0 < D x`;
e (tflLib.REC_INDUCT_TAC conway_aux_ind);
e (REPEAT CONJ_TAC);
(*1*)
e (RW_TAC
(*2*)
(*3*)
(*4*)
e (RW_TAC base_ss []);
e RES_TAC;


*---------------------------------------------------------------------------
             Unification
 ---------------------------------------------------------------------------*)

load"setTheory";

(*---------------------------------------------------------------------------
 * A simple unification algorithm. This is unfinished! The main interest
 * I had in attempting this file was to check 1) that the congruence rule
 * for the "subst" datatype is correctly proved and deployed; and 2) that
 * extraction works properly for a reasonably complicated function. Hopefully
 * one day, someone will finish the job.  The hard part is not defining the
 * functions (except for unification), but rather all the background theory
 * having to do with substitutions, mgus, and idempotent mgus. Another point
 * is that HOL should provide special syntax for case-statements, as the
 * current syntax, where the "cased" object comes last, is hopeless.
 *---------------------------------------------------------------------------*)

val _ = app delete_const ["g","N","N1"] handle _ => ();

Hol_datatype `term = Var of 'a
                   | Const of 'a
                   | App of term => term`;

Hol_datatype  `subst = Fail | Subst of ('a#'a term) list`;


(*---------------------------------------------------------------------------
 * Immediate subterm. No termination relation given.
 *---------------------------------------------------------------------------*)
val IST_def =
 Define
     `(IST x (Var y)   = F) /\
      (IST x (Const y) = F) /\
      (IST x (App M N) = (x=M) \/ (x=N))`;

val PST_def = Define `PST = TC IST`;


(*---------------------------------------------------------------------------
 *  Variables in a term.
 *---------------------------------------------------------------------------*)

val Vars_def =
 Define
     `(Vars (Var x)   = {x}) /\
      (Vars (Const y) = {})  /\
      (Vars (App M N) = (Vars M) UNION (Vars N))`;

val point_to_prod_def =
 Define
     `## (f:'a->'b) (g:'a->'c) x = (f x, g x)`;

val _ = set_fixity "##" (Infix 400);
val _ = set_MLname "##_def" "point_to_prod_def";

(*---------------------------------------------------------------------------
 * Composing substitutions; just declared, not defined.
 *---------------------------------------------------------------------------*)
val compose =
  new_constant{Name = "compose",
               Ty = Type`:('a#'a term) list
                          -> ('a#'a term) list
                            -> ('a#'a term) list`};

(*---------------------------------------------------------------------------
 * The field of a substitution; just declared, not defined.
 *---------------------------------------------------------------------------*)
val svars =
  new_constant{Name = "SVars",
               Ty = Type`:('a#'a term) list -> 'a set`};


(*---------------------------------------------------------------------------
 * Applying a substitution to a term; just declared, not defined.
 *---------------------------------------------------------------------------*)
val subst =
  new_constant{Name = "subst",
               Ty = Type`:('a#'a term) list -> 'a term -> 'a term`};



(*---------------------------------------------------------------------------
 * A reason why the following unification algorithm terminates.
 *---------------------------------------------------------------------------*)
(*
val TR_def =
 Define
    `TR = inv_image ($PSUBSET LEX (RPROD PST PST))
                  ((\(x:'a term,y). Vars(x) UNION Vars(y))##I)`;
*)

val unify_def = defn "unify"
(Term
   `(Unify(Const m, Const n) = if m=n then Subst[] else Fail)
 /\ (Unify(Const m, App M N) = Fail)
 /\ (Unify(Const m, Var v)   = Subst[(v:'a,Const m)])
 /\ (Unify(Var v, M)         = if PST(Var v) M then Fail else Subst[(v,M)])
 /\ (Unify(App M N, Const x) = Fail)
 /\ (Unify(App M N,Var v)    = if PST(Var v)(App M N)
                               then Fail else Subst[(v,App M N)])
 /\ (Unify(App M1 N1, App M2 N2) =
       subst_case Fail (\theta.
           subst_case Fail (\sigma. Subst (compose theta sigma))
               (Unify (subst theta N1, subst theta N2))) (Unify(M1,M2)))`);


