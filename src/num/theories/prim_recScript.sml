(* ===================================================================== *)
(* FILE          : mk_prim_rec.sml                                       *)
(* DESCRIPTION   : The primitive recursion theorem from Peano's axioms.  *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


(*---------------------------------------------------------------------------
 * In this file, we prove the primitive recursion theorem directly
 * from Peano's axioms (which are actually theorems in HOL).
 * These `axioms' define the type ":num" and two
 * constants "0:num" and "SUC:num->num", they are:
 *
 *    NOT_SUC   |- !n. ~(SUC n = 0)
 *
 *    INV_SUC   |- !m n. (SUC m = SUC n) ==> (m = n)
 *
 *    INDUCTION |- !P. (P 0 /\ (!n. P n ==> P(SUC n))) ==> !n. P n
 *
 * Using INDUCTION one can define an induction rule and tactic.
 * The rule is an ML function:
 *
 *  INDUCT: (thm # thm) -> thm
 *
 *    A1 |- t[0]      A2 |- !n. t[n] ==> t[SUC n]
 *  -----------------------------------------------
 *              A1 u A2 |- !n. t[n]
 *
 * The tactic is:
 *
 *             [A] !n.t[n]
 *   ================================
 *    [A] t[0]  ,  [A,t[n]] t[SUC x]
 *
 * From now on we only make (non-recursive) definitions and prove theorems.
 *
 * The following definition of < is from Hodges's article in "The Handbook of
 * Philosophical Logic" (page 111):
 *
 *    m < n = ?P. (!n. P(SUC n) ==> P n) /\ P m /\ ~(P n)
 *
 *
 * The following consequence of INV_SUC will be useful for rewriting:
 *
 *  |- !m n. (SUC m = SUC n)  =  (m = n)
 *
 * It is used in SUC_ID and PRIM_REC_EXISTS below. We establish it by
 * forward proof.
 *
 * After proving this we prove some standard properties of <.
 *---------------------------------------------------------------------------*)

structure prim_recScript =
struct

open HolKernel basicHol90Lib Parse
infix THEN THENL;

type thm = Thm.thm

val _ = new_theory "prim_rec";

(* Added TFM 88.04.02						*)

val NOT_SUC     = numTheory.NOT_SUC
and INV_SUC     = numTheory.INV_SUC
and INDUCTION   = numTheory.INDUCTION;

fun INDUCT_TAC g = INDUCT_THEN INDUCTION ASSUME_TAC g;

val LESS_DEF =
  new_infixr_definition
  ("LESS_DEF",
      Term `$< m n = ?P. (!n. P(SUC n) ==> P n) /\ P m /\ ~(P n)`,
   450);

val INV_SUC_EQ = save_thm("INV_SUC_EQ",
   GENL [--`m:num`--, --`n:num`--]
        (IMP_ANTISYM_RULE
             (SPEC_ALL INV_SUC)
             (DISCH (--`m:num = n`--)
                    (AP_TERM (--`SUC`--)
                             (ASSUME (--`m:num = n`--))))));

val LESS_REFL = store_thm( "LESS_REFL", --`!n. ~(n < n)`--,
   GEN_TAC THEN
   REWRITE_TAC[LESS_DEF, NOT_AND]);


val SUC_LESS =
 store_thm
   ("SUC_LESS",
    --`!m n. (SUC m < n) ==>  m < n`--,
   REWRITE_TAC[LESS_DEF]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (--`P:num->bool`--)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

val NOT_LESS_0 =
 store_thm
   ("NOT_LESS_0",
    --`!n. ~(n < 0)`--,
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_REFL]
    THEN IMP_RES_TAC(CONTRAPOS
            (SPECL[--`n:num`--, --`0`--] SUC_LESS))
    THEN ASM_REWRITE_TAC[]);

val LESS_0_0 =
 store_thm
  ("LESS_0_0",
   --`0 < SUC 0`--,
   REWRITE_TAC[LESS_DEF]
    THEN EXISTS_TAC (--`\x.x = 0`--)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[NOT_SUC]);


val LESS_MONO =
 store_thm
  ("LESS_MONO",
   --`!m n. (m < n) ==> (SUC m < SUC n)`--,
   REWRITE_TAC[LESS_DEF]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (--`\x.(x = SUC m) \/ (P x)`--)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
          (DISCH_ALL
           (CONTRAPOS(SPEC (--`(n:num)`--)
                           (ASSUME (--`!n'. P(SUC n')  ==>  P n'`--)))))
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN IMP_RES_TAC INV_SUC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS [ASSUME (--`n:num = m`--)]
                          (ASSUME (--`~(P (n:num))`--))))
    THEN RES_TAC);

val LESS_SUC_REFL =
 store_thm
  ("LESS_SUC_REFL",
   --`!n. n < SUC n`--,
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_0_0]
    THEN IMP_RES_TAC LESS_MONO
    THEN ASM_REWRITE_TAC[]);

val LESS_SUC =
 store_thm
 ("LESS_SUC",
  --`!m n. (m < n) ==> (m < SUC n)`--,
  REWRITE_TAC [LESS_DEF]
   THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC (--`P:num->bool`--)
   THEN IMP_RES_TAC
         (CONTRAPOS(SPEC (--`(n:num)`--)
                         (ASSUME (--`  !n'. P(SUC n')  ==>  P n'  `--))))
   THEN ASM_REWRITE_TAC[]);

val LESS_LEMMA1 =
 store_thm
  ("LESS_LEMMA1",
   --`!m n. (m < SUC n) ==> (m = n) \/ (m < n)`--,
   REWRITE_TAC[LESS_DEF]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC (--`(m:num) = n`--)
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC (--`\(x:num). ~(x = n) /\ (P x)`--)
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME (--`(n':num) = n`--)]
                         (ASSUME(--`P(SUC n'):bool`--))))
    THEN ASSUME_TAC(REFL(--`n:num`--))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);


val LESS_LEMMA2 =
 store_thm
  ("LESS_LEMMA2",
   --`!m n. ((m = n) \/ (m < n)) ==> (m < SUC n)`--,
   REPEAT STRIP_TAC
    THEN (IMP_RES_TAC LESS_SUC)
    THEN ASM_REWRITE_TAC[LESS_SUC_REFL]);

(* |- !m n. m < (SUC n)  =  (m  =  n)  \/  m < n *)
val LESS_THM = save_thm("LESS_THM",
    GENL [--`m:num`--, --`n:num`--]
         (IMP_ANTISYM_RULE(SPEC_ALL LESS_LEMMA1)
                          (SPEC_ALL LESS_LEMMA2)));

val LESS_SUC_IMP =
 store_thm
  ("LESS_SUC_IMP",
   --`!m n. (m < SUC n) ==> ~(m = n) ==> (m < n)`--,
   REWRITE_TAC[LESS_THM]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

(* Move to conversion nets forces different tactic in this proof. kls. *)
val LESS_0 = store_thm("LESS_0",
   --`!n. 0 < (SUC n)`--,
   INDUCT_TAC THEN
   ONCE_REWRITE_TAC[LESS_THM] THEN
   ASM_REWRITE_TAC[]);

val EQ_LESS =
 store_thm
  ("EQ_LESS",
   --`!n. (SUC m = n) ==> (m < n)`--,
   INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC, LESS_THM]
    THEN DISCH_TAC
    THEN IMP_RES_TAC INV_SUC
    THEN ASM_REWRITE_TAC[]);

val SUC_ID =
 store_thm
  ("SUC_ID",
   --`!n. ~(SUC n = n)`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_SUC, INV_SUC_EQ]);

val NOT_LESS_EQ =
 store_thm
  ("NOT_LESS_EQ",
   --`!m n. (m = n) ==> ~(m < n)`--,
   REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[LESS_REFL]);

val LESS_NOT_EQ =
 store_thm
  ("LESS_NOT_EQ",
   --`!m n. (m < n) ==> ~(m = n)`--,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME (--`(m:num) = n`--)]
                         (ASSUME (--`m < n`--))))
    THEN IMP_RES_TAC LESS_REFL
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------
 * Now we will prove that:
 *
 *   |- !x f. ?fun.
 *       (fun 0 = x) /\
 *       (!m. fun(SUC m) = f(fun m)m)
 *
 *  We start by defining a (higher order) function SIMP_REC and
 *  proving that:
 *
 *    |- !m x f.
 *        (SIMP_REC x f 0 = x) /\
 *        (SIMP_REC x f (SUC m) = f(SIMP_REC x f m))
 *
 *  We then define a function PRIM_REC in terms of SIMP_REC and prove that:
 *
 *    |- !m x f.
 *        (PRIM_REC x f 0  = x) /\
 *        (PRIM_REC x f (SUC m) = f (PRIM_REC x f m) m)
 *
 *  This is sufficient to justify any primitive recursive definition
 *  because a definition:
 *
 *      fun 0 x1 ... xn       = f1(x1, ... ,xn)
 *
 *      fun (SUC m) x1 ... xn = f2(fun m x1 ... xn, m, x1, ... ,xn)
 *
 *  is equivalent to:
 *
 *      fun 0       = \x1 ... xn. f1(x1, ... ,xn)
 *
 *      fun (SUC m) = \x1 ... xn. f2(fun m x1 ... xn, m, x1, ... ,xn)
 *                  = (\f m x1 ... xn. f2(f x1 ... xn, m, x1, ... ,xn))(fun m)m
 *
 *  which defines fun to be:
 *
 *      PRIM_REC
 *       (\x1 ... xn. f1(x1, ... ,xn))
 *       (\f m x1 ... xn. f2(f x1 ... xn, m, x1, ... ,xn))
 *---------------------------------------------------------------------------*)

val SIMP_REC_REL =
 new_definition
  ("SIMP_REC_REL",
   Term`!(fun:num->'a) (x:'a) (f:'a->'a) (n:num).
            SIMP_REC_REL fun x f n =
                (fun 0 = x) /\
                !m. (m < n) ==> (fun(SUC m) = f(fun m))`);

val SIMP_REC_FUN =
 new_definition
  ("SIMP_REC_FUN",
   --`SIMP_REC_FUN (x:'a) (f:'a->'a) (n:num) =
     @fun. SIMP_REC_REL fun x f n`--);

val SIMP_REC =
 new_definition
  ("SIMP_REC",
   --`SIMP_REC (x:'a) (f:'a->'a) (n:num) =
     SIMP_REC_FUN x f (SUC n) n`--);

(*---------------------------------------------------------------------------
   |- (?fun. SIMP_REC_REL fun x f n)  =
       (SIMP_REC_FUN x f n 0  =  x)  /\
       (!m.
         m < n  ==>
         (SIMP_REC_FUN x f n (SUC m)  =  f(SIMP_REC_FUN x f n m)))
 *---------------------------------------------------------------------------*)

val SIMP_REC_FUN_LEMMA =
 let val t1 = --`?(fun:num->'a). SIMP_REC_REL fun x f n`--
     val t2 = --`SIMP_REC_REL (@(fun:num->'a). SIMP_REC_REL fun x f n) x f n`--
     val th1 = DISCH t1 (SELECT_RULE(ASSUME t1))
     val th2 = DISCH t2 (EXISTS(t1,--`@(fun:num->'a).SIMP_REC_REL fun x f n`--)
                               (ASSUME t2))
     val th3 = PURE_REWRITE_RULE[SYM(SPEC_ALL SIMP_REC_FUN)]
                                (IMP_ANTISYM_RULE th1 th2)
 in
     save_thm("SIMP_REC_FUN_LEMMA",
     TRANS th3 (DEPTH_CONV(REWR_CONV SIMP_REC_REL)(rhs(concl th3))))
 end;

val SIMP_REC_EXISTS = store_thm("SIMP_REC_EXISTS",
   --`!x f n. ?fun:num->'a. SIMP_REC_REL fun x f n`--,
   GEN_TAC THEN
   GEN_TAC THEN
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THEN
   PURE_REWRITE_TAC[SIMP_REC_REL] THENL
   [EXISTS_TAC (--`\p:num. (x:'a)`--) THEN
    REWRITE_TAC[NOT_LESS_0]
    ,
    EXISTS_TAC (--`\p. (p=(SUC n))
                       => f(SIMP_REC_FUN (x:'a) f n n)
                        | SIMP_REC_FUN x f n p`--) THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[NOT_EQ_SYM(SPEC_ALL NOT_SUC)] THEN
    IMP_RES_TAC SIMP_REC_FUN_LEMMA THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (--`m:num = n`--) THEN
    IMP_RES_TAC LESS_NOT_EQ THEN
    IMP_RES_TAC LESS_SUC_IMP THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[LESS_THM,INV_SUC_EQ,SUC_ID]]);

(*---------------------------------------------------------------------------
   |- !x f n.
       (SIMP_REC_FUN x f n 0  =  x)  /\
       (!m.
         m < n  ==>
         (SIMP_REC_FUN x f n (SUC m)  =  f(SIMP_REC_FUN x f n m)))
 *---------------------------------------------------------------------------*)

val SIMP_REC_FUN_THM =
   GEN_ALL(EQ_MP(SPEC_ALL SIMP_REC_FUN_LEMMA)
                (SPEC_ALL SIMP_REC_EXISTS));

val SIMP_REC_FUN_THM1 = GEN_ALL(CONJUNCT1(SPEC_ALL SIMP_REC_FUN_THM));
val SIMP_REC_FUN_THM2 = GEN (--`n:num`--)
                            (CONJUNCT2(SPEC_ALL SIMP_REC_FUN_THM));

val SIMP_REC_UNIQUE =prove
   (--`!n m1 m2 (x:'a) f.
       (n < m1) ==>
       (n < m2) ==>
       (SIMP_REC_FUN x f m1 n = SIMP_REC_FUN x f m2 n)`--,
    INDUCT_TAC
     THEN ASM_REWRITE_TAC[SIMP_REC_FUN_THM1]
     THEN REPEAT GEN_TAC
     THEN REPEAT DISCH_TAC
     THEN IMP_RES_TAC SUC_LESS
     THEN IMP_RES_TAC SIMP_REC_FUN_THM2
     THEN ASM_REWRITE_TAC[]
     THEN RES_TAC
     THEN AP_TERM_TAC THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC);

val LESS_SUC_SUC =
 store_thm
  ("LESS_SUC_SUC",
   --`!m. (m < SUC m) /\ (m < SUC(SUC m))`--,
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[LESS_THM]);

val SIMP_REC_THM =
 store_thm
  ("SIMP_REC_THM",
   --`!(x:'a) f.
     (SIMP_REC x f 0 = x) /\
     (!m. SIMP_REC x f (SUC m) = f(SIMP_REC x f m))`--,
    ASM_REWRITE_TAC
     [SIMP_REC, SIMP_REC_FUN_THM1,
      MP(SPECL[--`SUC(SUC m)`--, --`(m:num)`--]SIMP_REC_FUN_THM2)
        (CONJUNCT2(SPEC_ALL LESS_SUC_SUC)),
      MP
       (MP(SPEC_ALL(SPECL[--`(m:num)`--, --`SUC(SUC m)`--, --`SUC m`--]
                         SIMP_REC_UNIQUE))
          (CONJUNCT2(SPEC_ALL LESS_SUC_SUC)))
       (CONJUNCT1(SPEC_ALL LESS_SUC_SUC))]);

(*---------------------------------------------------------------------------
 * We now use simple recursion to prove that:
 *
 *   |- !x f. ?fun.
 *       (fun ZERO = x) /\
 *       (!m. fun(SUC m) = f(fun m)m)
 *
 *  We proceed by defining a function PRIM_REC and proving that:
 *
 *   |- !m x f.
 *       (PRIM_REC x f 0  = x) /\
 *       (PRIM_REC x f (SUC m) = f(PRIM_REC x f m)m)
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * First we define a partial inverse to SUC called PRE such that:
 *
 *   (PRE 0 = 0) /\ (!m. PRE(SUC m) = m)
 *---------------------------------------------------------------------------*)
val PRE_DEF = new_definition("PRE_DEF",
    --`PRE m = ((m=0) => 0 | @n. m = SUC n)`--);


(* |- (@n. m = n) = m *)
val SELECT_LEMMA =
   let val th = SELECT_INTRO(EQ_MP (SYM(BETA_CONV (--`(\n:'a. m = n) m`--)))
                                   (REFL (--`m: 'a`--)))
   in
   SYM(EQ_MP(BETA_CONV(concl th))th)
   end;

val PRE =
 store_thm
  ("PRE",
   --`(PRE 0 = 0) /\ (!m. PRE(SUC m) = m)`--,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRE_DEF, INV_SUC_EQ, NOT_SUC, SELECT_LEMMA]);

val PRIM_REC_FUN =
 new_definition
  ("PRIM_REC_FUN",
   --`PRIM_REC_FUN (x:'a) (f:'a->num->'a) =
        SIMP_REC (\n:num. x) (\fun n. f(fun(PRE n))n)`--);

val PRIM_REC_EQN =
 store_thm
  ("PRIM_REC_EQN",
   --`!(x:'a) f.
     (!n. PRIM_REC_FUN x f 0 n = x) /\
     (!m n. PRIM_REC_FUN x f (SUC m) n = f (PRIM_REC_FUN x f m (PRE n)) n)`--,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC [PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[]);

val PRIM_REC =
 new_definition
  ("PRIM_REC",
   --`PRIM_REC (x:'a) f m = PRIM_REC_FUN x f m (PRE m)`--);

val PRIM_REC_THM =
 store_thm
  ("PRIM_REC_THM",
   --`!x f.
     (PRIM_REC (x:'a) f 0 = x) /\
     (!m. PRIM_REC x f (SUC m) = f (PRIM_REC x f m) m)`--,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRIM_REC, PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[PRE]);


(*---------------------------------------------------------------------------*
 * The axiom of dependent choice (DC).                                       *
 *---------------------------------------------------------------------------*)

local
  val DCkey = BETA_RULE (SPEC
                (Term`\y. P y /\ R (SIMP_REC a (\x. @y. P y /\ R x y) n) y`)
                     SELECT_AX)
  val totalDClem = prove
    (Term`!P R a. P a /\ (!x. P x ==> ?y. P y /\ R x y)
                   ==>
                   !n. P (SIMP_REC a (\x. @y. P y /\ R x y) n)`,
     REPEAT GEN_TAC THEN STRIP_TAC
       THEN INDUCT_THEN numTheory.INDUCTION ASSUME_TAC
       THEN ASM_REWRITE_TAC [SIMP_REC_THM]
       THEN BETA_TAC THEN RES_TAC THEN IMP_RES_TAC DCkey)
in
val DC = store_thm("DC",
Term
  `!P R a.
      P a /\ (!x. P x ==> ?y. P y /\ R x y)
          ==>
      ?f. (f 0 = a) /\ (!n. P (f n) /\ R (f n) (f (SUC n)))`,
REPEAT STRIP_TAC
  THEN EXISTS_TAC (Term`SIMP_REC a (\x. @y. P y /\ R x y)`)
  THEN REWRITE_TAC [SIMP_REC_THM] THEN BETA_TAC THEN GEN_TAC
  THEN SUBGOAL_THEN
       (Term`P (SIMP_REC a (\x. @y. P y /\ R x y) n)`) ASSUME_TAC THENL
  [MATCH_MP_TAC totalDClem THEN ASM_REWRITE_TAC[],
   ASM_REWRITE_TAC[] THEN RES_THEN MP_TAC THEN DISCH_THEN (K ALL_TAC)
  THEN DISCH_THEN (CHOOSE_THEN (ACCEPT_TAC o CONJUNCT2 o MATCH_MP DCkey))])
end;


(*----------------------------------------------------------------------*)
(* Unique existence theorem for prim rec definitions on num.		*)
(*									*)
(* ADDED TFM 88.04.02							*)
(*----------------------------------------------------------------------*)
val num_Axiom_old = store_thm(
  "num_Axiom_old",
   --`!e:'a. !f. ?! fn1. (fn1 0 = e) /\
                         (!n. fn1 (SUC n) = f (fn1 n) n)`--,
   REPEAT GEN_TAC THEN
   CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [EXISTS_TAC (--`PRIM_REC (e:'a) (f:'a->num->'a)`--) THEN
    REWRITE_TAC [PRIM_REC_THM],
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC FUN_EQ_CONV THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC []]);

val num_Axiom = store_thm(
  "num_Axiom",
  Term`!(e:'a) f. ?fn. (fn 0 = e) /\ !n. fn (SUC n) = f n (fn n)`,
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC
     (CONV_RULE EXISTS_UNIQUE_CONV
        (SPECL [Term`e:'a`, Term`\a:'a n:num. f n a:'a`] num_Axiom_old)) THEN
  EXISTS_TAC (Term`fn1 : num -> 'a`) THEN
  RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC []);

(*---------------------------------------------------------------------------*
 * Wellfoundedness taken as no infinite descending chains in 'a. This defn   *
 * is conceptually simpler (to some) than the original definition of         *
 * wellfoundedness, which is solely in terms of sets (and therefore          *
 * logically simpler).                                                       *
 *---------------------------------------------------------------------------*)

val wellfounded_def =
Q.new_definition
  ("wellfounded_def",
   `wellfounded (R:'a->'a->bool) = ~?f. !n. R (f (SUC n)) (f n)`);


(*---------------------------------------------------------------------------
 * First half of showing that the two definitions of wellfoundedness agree.
 *---------------------------------------------------------------------------*)

val WF_IMP_WELLFOUNDED = Q.prove(
`!R. WF R ==> wellfounded R`,
 GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN REWRITE_TAC[wellfounded_def,relationTheory.WF_DEF]
 THEN STRIP_TAC
 THEN Ho_rewrite.REWRITE_TAC
        [NOT_FORALL_THM,NOT_EXISTS_THM,boolTheory.NOT_IMP,DE_MORGAN_THM]
 THEN Q.EXISTS_TAC`\p:'a. ?n:num. p = f n`
 THEN BETA_TAC THEN CONJ_TAC THENL
  [MAP_EVERY Q.EXISTS_TAC [`(f:num->'a) n`,  `n`] THEN REFL_TAC,
   REWRITE_TAC[GSYM IMP_DISJ_THM]
    THEN GEN_TAC THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN Q.EXISTS_TAC`f(SUC n)` THEN ASM_REWRITE_TAC[]
    THEN Q.EXISTS_TAC`SUC n` THEN REFL_TAC]);

(*---------------------------------------------------------------------------
 * Second half.
 *---------------------------------------------------------------------------*)

val WELLFOUNDED_IMP_WF = Q.prove(
`!R. wellfounded R ==> WF R`,
 REWRITE_TAC[wellfounded_def,relationTheory.WF_DEF]
  THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
  THEN Ho_rewrite.REWRITE_TAC
        [NOT_FORALL_THM,NOT_EXISTS_THM,NOT_IMP,DE_MORGAN_THM]
  THEN REWRITE_TAC [GSYM IMP_DISJ_THM]
  THEN REPEAT STRIP_TAC
  THEN Q.EXISTS_TAC`SIMP_REC w (\x. @q. R q x /\ B q)` THEN GEN_TAC
  THEN Q.SUBGOAL_THEN `!n. B(SIMP_REC w (\x. @q. R q x /\ B q) n)`
                      (ASSUME_TAC o SPEC_ALL)
  THENL [INDUCT_TAC,ALL_TAC]
  THEN ASM_REWRITE_TAC[SIMP_REC_THM] THEN BETA_TAC
  THEN RES_TAC
  THEN IMP_RES_TAC(BETA_RULE
     (Q.SPEC `\q. R q (SIMP_REC w (\x. @q. R q x /\ B q) n) /\ B q`
              boolTheory.SELECT_AX)));


val WF_IFF_WELLFOUNDED = Q.store_thm("WF_IFF_WELLFOUNDED",
`!R. WF R = wellfounded R`,
GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [IMP_RES_TAC WF_IMP_WELLFOUNDED,
         IMP_RES_TAC WELLFOUNDED_IMP_WF]);


val WF_PRED =
Q.store_thm
("WF_PRED",
  `WF \x y. y = SUC x`,
 REWRITE_TAC[relationTheory.WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC CONTRAPOS_CONV
  THEN Ho_rewrite.REWRITE_TAC
        [NOT_FORALL_THM,NOT_EXISTS_THM,NOT_IMP,DE_MORGAN_THM]
  THEN REWRITE_TAC [GSYM IMP_DISJ_THM]
  THEN DISCH_TAC
  THEN INDUCT_TAC THEN CCONTR_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[])
  THEN RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[INV_SUC_EQ, GSYM NOT_SUC])
  THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC])
  THEN FILTER_ASM_REWRITE_TAC is_eq [] THEN ASM_REWRITE_TAC[]);


(*----------------------------------------------------------------------------
 * This theorem would be a lot nicer if < was defined as the transitive
 * closure of predecessor.
 *---------------------------------------------------------------------------*)

val WF_LESS = Q.store_thm("WF_LESS", `WF $<`,
REWRITE_TAC[relationTheory.WF_DEF]
 THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN DISCH_THEN (fn th1 =>
       SUBGOAL_THEN (--`^(concl th1) ==> !i j. j<i ==> ~B j`--)
                    (fn th => MP_TAC (MP th th1)))
 THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THENL
  [INDUCT_TAC THEN GEN_TAC THEN
    REWRITE_TAC[NOT_LESS_0,LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THENL[SUBST1_TAC, ASSUME_TAC])
    THEN STRIP_TAC THEN RES_TAC,
   GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC
    THEN Q.EXISTS_TAC`SUC w`
    THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);


(*---------------------------------------------------------------------------
 * Measure functions are definable as inverse image into (<). Every relation
 * arising from a measure function is wellfounded, which is really great!
 *---------------------------------------------------------------------------*)

val measure_def = Q.new_definition ("measure_def", `measure = inv_image $<`);

val WF_measure =
Q.store_thm("WF_measure", `!m. WF (measure m)`,
REWRITE_TAC[measure_def]
 THEN MATCH_MP_TAC relationTheory.WF_inv_image
 THEN ACCEPT_TAC WF_LESS);

val _ = export_theory() ;

end;
