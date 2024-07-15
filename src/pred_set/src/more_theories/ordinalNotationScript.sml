open HolKernel Parse boolLib bossLib IndDefLib
     numTheory prim_recTheory arithmeticTheory

val _ = numLib.temp_prefer_num();

(*---------------------------------------------------------------------------*)
(* Functionality discussed with Matt Kaufmann                                *)
(*---------------------------------------------------------------------------*)

fun DISPOSE_TAC q = Q.PAT_X_ASSUM q (K ALL_TAC);

fun DROP_ASSUMS_TAC [] (asl,c) = REPEAT (WEAKEN_TAC (K true)) (asl,c)
  | DROP_ASSUMS_TAC nlist (asl,c) =
      let val tmlist = map (fn n => el (n+1) (rev asl)) nlist
      in MAP_EVERY (fn tm => UNDISCH_THEN tm (K ALL_TAC)) tmlist
      end (asl,c);

fun DROP_ASSUM n = DROP_ASSUMS_TAC [n];

val meter = Count.mk_meter();

(*---------------------------------------------------------------------------*)
(* Start the theory                                                          *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "ordinalNotation";

(*---------------------------------------------------------------------------*)
(* Raw syntax of ordinals                                                    *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "=" (Infix(NONASSOC, 100))
val _ = Hol_datatype
  `osyntax = End of num
           | Plus of osyntax => num => osyntax`;

val osyntax_11       = TypeBase.one_one_of ``:osyntax``;
val osyntax_distinct = TypeBase.distinct_of ``:osyntax``;

(*---------------------------------------------------------------------------*)
(* And operations over osyntax.                                              *)
(*---------------------------------------------------------------------------*)

val expt_def =
 Define
    `(expt (End _) = End 0) /\
     (expt (Plus e k t) = e)`;

val coeff_def =
 Define
    `(coeff (End x) = x) /\
     (coeff (Plus e k t) = k)`;

val finp_def =
 Define
  `(finp (End _) = T) /\
   (finp (Plus _ _ _) = F)`;

val tail_def =
 Define
   `tail (Plus e k t) = t`;

val rank_def =
 Define
   `(rank (End _) = 0) /\
    (rank (Plus e k t) = 1 + rank e)`;

val ord_ss = arith_ss ++ rewrites
   [expt_def, coeff_def, finp_def, tail_def, rank_def, GSYM IMP_DISJ_THM];

(*---------------------------------------------------------------------------*)
(* Definition of less-than on osyntax                                        *)
(*---------------------------------------------------------------------------*)

val (oless_rules, oless_ind, oless_cases) =
 Hol_reln
 `(!k1 k2. k1 < k2 ==> oless (End k1) (End k2))  /\
  (!k1 e2 k2 t2. oless (End k1) (Plus e2 k2 t2)) /\
  (!e1 k1 t1 e2 k2 t2. oless e1 e2 ==> oless (Plus e1 k1 t1) (Plus e2 k2 t2)) /\
  (!e1 k1 t1 e2 k2 t2. (e1=e2) /\ k1<k2
                        ==> oless (Plus e1 k1 t1) (Plus e2 k2 t2)) /\
  (!e1 k1 t1 e2 k2 t2. (e1=e2) /\ (k1=k2) /\ oless t1 t2
                        ==> oless (Plus e1 k1 t1) (Plus e2 k2 t2))`;

val oless_strong_ind =
    save_thm ("oless_strong_ind",theorem "oless_strongind");

val oless_End_End = Q.store_thm
("oless_End_End",
 `!k1 k2. oless (End k1) (End k2) ==> k1 < k2`,
 RW_TAC ord_ss [Once oless_cases]);

(*---------------------------------------------------------------------------*)
(* Version of oless suitable for ML execution.                               *)
(*---------------------------------------------------------------------------*)

val oless_equations = Q.store_thm
("oless_equations",
 `(oless (End m) (End n) <=> m < n) /\
  (oless (End m) (Plus e k t) <=> T) /\
  (oless (Plus e k t) (End m) <=> F) /\
  (oless (Plus e1 k1 t1) (Plus e2 k2 t2) <=>
     if oless e1 e2 then T else
     if (e1 = e2) /\ k1 < k2 then T else
     if (e1 = e2) /\ (k1 = k2) /\ oless t1 t2 then T
     else F)`,
 SIMP_TAC arith_ss [EQ_IMP_THM] THEN REPEAT CONJ_TAC THENL
 [RW_TAC arith_ss [Once oless_cases],
  METIS_TAC [oless_rules],
  METIS_TAC [oless_rules],
  RW_TAC arith_ss [Once oless_cases] THEN METIS_TAC[],
  RW_TAC arith_ss [Once oless_cases] THEN METIS_TAC[],
  METIS_TAC [oless_rules]]);

(*---------------------------------------------------------------------------*)
(* Subset of osyntax things that are ordinals in Cantor Normal Form          *)
(*---------------------------------------------------------------------------*)

val (is_ord_rules, is_ord_ind, is_ord_cases) =
 Hol_reln
  `(!k. is_ord (End k)) /\
   (!e k t. is_ord e /\ ~(e = End 0) /\ 0 < k /\ is_ord t /\ oless (expt t) e
            ==> is_ord (Plus e k t))`;

val is_ord_strong_ind =
    save_thm("is_ord_strong_ind", theorem "is_ord_strongind")

val decompose_plus = Q.store_thm
("decompose_plus",
 `!e k t. is_ord (Plus e k t) ==>
          is_ord e /\ ~(e = End 0) /\ 0 < k /\ is_ord t /\ oless (expt t) e`,
 METIS_TAC [is_ord_cases,osyntax_distinct,osyntax_11]);

(*---------------------------------------------------------------------------*)
(* Functional version of is_ord                                              *)
(*---------------------------------------------------------------------------*)

val is_ord_equations = Q.store_thm
("is_ord_equations",
 `(is_ord (End k) <=> T) /\
  (is_ord (Plus e k t) <=>
        is_ord e /\ ~(e = End 0) /\ 0 < k /\ is_ord t /\ oless (expt t) e)`,
  METIS_TAC [is_ord_rules,decompose_plus]);

val is_ord_End = CONJUNCT1 is_ord_rules;

val ord_ss = ord_ss ++ rewrites [is_ord_End];

(*---------------------------------------------------------------------------*)
(* Closure properties of ordinal operations.                                 *)
(*---------------------------------------------------------------------------*)

val is_ord_expt_closed = Q.store_thm
("is_ord_expt_closed",
 `!x. is_ord x ==> is_ord (expt x)`,
 Induct THEN RW_TAC ord_ss [] THEN METIS_TAC [decompose_plus]);

val is_ord_tail_closed = Q.store_thm
("is_ord_tail_closed",
`!x. ~finp x /\ is_ord x ==> is_ord (tail x)`,
Induct THEN RW_TAC ord_ss [] THEN METIS_TAC [decompose_plus]);

val is_ord_downclosed = Q.store_thm
("is_ord_downclosed",
 `is_ord (Plus w k t) ==> is_ord w /\ is_ord t`,
 METIS_TAC [is_ord_cases,osyntax_11,osyntax_distinct]);

val is_ord_coeff_pos = Q.store_thm
("is_ord_coeff_pos",
 `!x. ~finp(x) /\ is_ord x ==> 0 < coeff x`,
Induct THEN RW_TAC ord_ss [] THEN METIS_TAC [decompose_plus]);

val rank_expt = Q.store_thm
("rank_expt",
 `!x n. is_ord(x) /\ (rank x = SUC n) ==> (rank (expt x) = n)`,
 Cases THEN RW_TAC ord_ss []);

(*---------------------------------------------------------------------------*)
(* oless is antireflexive                                                    *)
(*---------------------------------------------------------------------------*)

val oless_antirefl_lem = Q.prove
(`!x y. oless x y ==> (x=y) /\ is_ord x ==> F`,
 HO_MATCH_MP_TAC oless_ind
   THEN RW_TAC ord_ss [] THEN METIS_TAC[decompose_plus]);

val oless_antirefl = Q.store_thm
("oless_antirefl",
 `!x. is_ord x ==> ~oless x x`,
 METIS_TAC[oless_antirefl_lem]);

(*---------------------------------------------------------------------------*)
(* oless is antisymmetric                                                    *)
(*---------------------------------------------------------------------------*)

val oless_antisym_lem = Q.prove
(`!x y. oless x y ==> is_ord x /\ is_ord y ==> ~oless y x`,
 HO_MATCH_MP_TAC oless_strong_ind THEN RW_TAC std_ss []
   THEN ONCE_REWRITE_TAC [oless_cases]
   THEN RW_TAC ord_ss []
   THEN METIS_TAC [oless_antirefl,decompose_plus]);

val oless_antisym = Q.store_thm
("oless_antisym",
 `!x y. is_ord x /\ is_ord y /\ oless x y ==> ~oless y x`,
 METIS_TAC [oless_antisym_lem]);

(*---------------------------------------------------------------------------*)
(* trichotomy and transitivity of oless ... not proved                       *)
(*---------------------------------------------------------------------------*)
(*
val oless_trichotomy =
 ``!x y. is_ord x /\ is_ord y ==> oless x y \/ (x=y) \/ oless y x``;

val oless_transitivity =
 ``!x y. is_ord x /\ is_ord y /\ is_ord x /\ oless x y /\ oless y z ==> oless x z``
*)

(*---------------------------------------------------------------------------*)
(* rank less implies oless                                                   *)
(*---------------------------------------------------------------------------*)

val rank_less_imp_oless = Q.store_thm
("rank_less_imp_oless",
 `!x y. is_ord x /\ is_ord y /\ rank x < rank y ==> oless x y`,
 measureInduct_on `rank x`
   THEN Cases_on `x` THEN Cases_on `y`
   THEN FULL_SIMP_TAC ord_ss [] THENL
   [METIS_TAC [oless_rules],
    RW_TAC ord_ss [] THEN
    METIS_TAC [DECIDE``x < x + 1n``,decompose_plus,oless_rules]]);

(*---------------------------------------------------------------------------*)
(* oless implies rank leq.                                                   *)
(*---------------------------------------------------------------------------*)

val oless_imp_rank_leq = Q.store_thm
("oless_imp_rank_leq",
 `!x y. is_ord x /\ is_ord y /\ oless x y ==> rank x <= rank y`,
 RW_TAC ord_ss [] THEN SPOSE_NOT_THEN ASSUME_TAC THEN
 `rank y < rank x` by DECIDE_TAC THEN
 METIS_TAC [rank_less_imp_oless,oless_antisym]);

(*---------------------------------------------------------------------------*)
(* Ordinals of rank 0 are essentially natural numbers                        *)
(*---------------------------------------------------------------------------*)

val rank_0_End = Q.store_thm
("rank_0_End",
 `!x. (rank x = 0) = ?n. x = End n`,
 Cases THEN RW_TAC ord_ss [rank_def]);

val rank_finp = Q.store_thm
("rank_finp",
 `!x. (rank x = 0) = finp x`,
 Cases THEN RW_TAC ord_ss [rank_def,finp_def]);

val rank_positive_exists = Q.store_thm
("rank_positive_exists",
 `!x. 0 < rank x <=> ?e c t. x = Plus e c t`,
 Cases THEN RW_TAC ord_ss [rank_def]);

val rank_positive = Q.store_thm
("rank_positive",
 `!x. 0 < rank x <=> (x = Plus (expt x) (coeff x) (tail x))`,
 Cases THEN RW_TAC ord_ss [rank_def,expt_def, coeff_def, tail_def]);

val rank_positive_expt = Q.store_thm
("rank_positive_expt",
`!x n. (rank x = SUC n) ==> (rank(expt x) = n)`,
 Cases THEN RW_TAC ord_ss [rank_def,expt_def]);

(*---------------------------------------------------------------------------*)
(* Proper subterms of an ordinal are oless than the ordinal                  *)
(*---------------------------------------------------------------------------*)

val oless_expt = Q.store_thm
("oless_expt",
 `!e k t. is_ord (Plus e k t) ==> oless e (Plus e k t)`,
 REPEAT STRIP_TAC THEN
 MATCH_MP_TAC rank_less_imp_oless THEN
 RW_TAC ord_ss [] THEN
 METIS_TAC [is_ord_downclosed]);

val oless_tail_lem = Q.prove
(`!x. is_ord x ==> ~finp x ==> oless (tail x) x`,
 HO_MATCH_MP_TAC is_ord_ind THEN
 RW_TAC ord_ss [tail_def,finp_def] THEN
 Cases_on `x'` THEN FULL_SIMP_TAC ord_ss [finp_def,tail_def,expt_def] THEN
 METIS_TAC [oless_rules]);;

val oless_tail = Q.store_thm
("oless_tail",
 `!x. is_ord x /\ ~finp x ==> oless (tail x) x`,
 METIS_TAC [oless_tail_lem]);


(*---------------------------------------------------------------------------*)
(* A non-empty set of ordinals of rank at most SUC n has either got at least *)
(* one element of rank <= n or all are of rank = n+1.                        *)
(*---------------------------------------------------------------------------*)

val split_lem = Q.prove
(`!P n. (?x. P x) /\ (!x. P x ==> rank x <= SUC n) ==>
        (?x. P x /\ rank x <= n) \/ (!x. P x ==> (rank x = SUC n))`,
 RW_TAC ord_ss [] THEN SPOSE_NOT_THEN ASSUME_TAC THEN RW_TAC arith_ss [] THEN
 STRIP_ASSUME_TAC
   (Q.SPECL [`rank x'`, `n`]
         (DECIDE ``!x y. x <= y \/ (x = SUC y) \/ (x > SUC y)``)) THENL
 [METIS_TAC [], RES_TAC THEN DECIDE_TAC]);

(*---------------------------------------------------------------------------*)
(* Every n.e. set of ordinals of rank <= n has an oless-minimal element      *)
(* imples every n.e. set having at least one ordinal of rank <= n has an     *)
(* oless-minimal element.                                                    *)
(*---------------------------------------------------------------------------*)

val stronger = Q.prove
(`(!n. !P:osyntax->bool. !x.
     P x /\ (!x. P x ==> is_ord(x) /\ rank(x) <= n) ==>
     ?m. is_ord m /\ P m /\ rank m <= n /\
         !y. is_ord y /\ rank y <= n /\ oless y m ==> ~P y)
   ==>
   (!n. !P:osyntax->bool.
     (?x. is_ord x /\ P x /\ rank x <= n) ==>
      ?m. is_ord m /\ P m /\ rank m <= n /\
       !y. is_ord y /\ rank y <= n /\ oless y m ==> ~P y)`,
 RW_TAC std_ss [] THEN
 Q.PAT_X_ASSUM `$!M`
    (MP_TAC o Q.SPEC `\a. P a /\ is_ord a /\ rank a <= n` o Q.ID_SPEC) THEN
 DISCH_THEN (MP_TAC o Q.ID_SPEC) THEN RW_TAC std_ss [] THEN METIS_TAC []);


(*---------------------------------------------------------------------------*)
(* Main lemma: every non-empty set having at least one ordinal of rank <= n  *)
(* has an oless-minimal element. The proof is by induction on n.             *)
(*---------------------------------------------------------------------------*)

val _ = Parse.hide "S";   (* used as a variable in the following proof *)

val lemma = Q.store_thm
("lemma",
 `!n. !P:osyntax->bool.
     (?x. is_ord x /\ P x /\ rank x <= n) ==>
      ?m. is_ord m /\ P m /\ rank m <= n /\
          !y. is_ord y /\ rank y <= n /\ oless y m ==> ~P y`,

 MATCH_MP_TAC stronger THEN Induct THENL

(*---------------------------------------------------------------------------*)
(* Base case .... everything in P has rank 0, so are natural numbers.        *)
(*---------------------------------------------------------------------------*)

[
RW_TAC ord_ss [] THEN
`?n. is_ord (End n) /\ P (End n) /\ (rank (End n) = 0) /\
     !m. m<n ==> ~(is_ord (End m) /\ P (End m) /\ (rank (End m) = 0))`
   by let val End_pred = ``\x. is_ord (End x) /\ P (End x) /\ (rank (End x) = 0)``
          val End_WOP = BETA_RULE (ISPEC End_pred WOP)
      in METIS_TAC [End_WOP,rank_0_End]
      end THEN METIS_TAC[oless_End_End,rank_0_End],
ALL_TAC
]

THEN

(*---------------------------------------------------------------------------*)
(* Step case: everything in P has rank <= n+1, so some b has rank <= n or    *)
(* all els of P have rank = n+1. Hence case split.                           *)
(*---------------------------------------------------------------------------*)

RW_TAC ord_ss [] THEN
`(?b. P b /\ rank b <= n) \/ !b. P b ==> (rank b = SUC n)`
  by METIS_TAC [split_lem]

THENL

(*---------------------------------------------------------------------------*)
(* Some b has rank <= n. Use IH on b.                                        *)
(*---------------------------------------------------------------------------*)
[
FIRST_ASSUM  (MP_TAC o SPEC ``\x. is_ord(x) /\ P x /\ rank(x) <= n``)
THEN RW_TAC std_ss []
THEN `?m. is_ord m /\ P m /\ rank m <= n /\
          !y. is_ord y /\ rank y <= n /\ oless y m ==> ~P y` by METIS_TAC[]
THEN Q.EXISTS_TAC `m` THEN RW_TAC ord_ss []
THEN `rank y <= rank m` by METIS_TAC [oless_imp_rank_leq]
THEN METIS_TAC [LESS_EQ_TRANS,DECIDE ``x <= SUC x``],
ALL_TAC
]

THEN

(*---------------------------------------------------------------------------*)
(* Adjust goal to take account of fact that everything in P has rank n+1.    *)
(*---------------------------------------------------------------------------*)

`!x. P x ==> is_ord x /\ (rank x = SUC n)` by METIS_TAC [] THEN
  DROP_ASSUMS_TAC [2,3] THEN
`(?m. is_ord m /\ P m /\ (rank m = SUC n) /\
 !y. is_ord y /\ (rank y = SUC n) /\ oless y m ==> ~P y)
  ==>
   ?m.
      is_ord m /\ P m /\ rank m <= SUC n /\
      !y. is_ord y /\ rank y <= SUC n /\ oless y m ==> ~P y`
  by (RW_TAC ord_ss [] THEN Q.EXISTS_TAC `m` THEN RW_TAC ord_ss []
      THEN METIS_TAC[])
  THEN POP_ASSUM MATCH_MP_TAC

THEN

(*---------------------------------------------------------------------------*)
(* Start proof by contradiction. Thus we assume that every element a in P    *)
(* has a b also in P such that oless b a.                                    *)
(*---------------------------------------------------------------------------*)

 SPOSE_NOT_THEN
    (ASSUME_TAC o SIMP_RULE ord_ss [DECIDE ``A \/ B <=> ~A ==> B``,
                          DECIDE ``a ==> b ==> c <=> a /\ b ==> c``])
THEN

(*---------------------------------------------------------------------------*)
(* So there is a set S of such sets                                          *)
(*---------------------------------------------------------------------------*)

`?S. (?si. S(si)) /\
     (!si. S si <=> (?x. si x) /\
        (!x. si(x) ==> is_ord(x) /\ (rank x = SUC n) /\ ?y. si y /\ oless y x))`
  by (Q.EXISTS_TAC `\si.
         (?a. si a) /\
         (!b. si b ==> is_ord b /\ (rank b = SUC n) /\ ?d. si d /\ oless d b)`
      THEN METIS_TAC []) THEN
 DROP_ASSUMS_TAC [1,2,3]  (* used to show existence of S; can now toss *)

THEN

(*---------------------------------------------------------------------------*)
(* The set of all first exponents of ordinals anywhere in S is n.e. and      *)
(* everything in it has rank at most n.                                      *)
(*---------------------------------------------------------------------------*)

`?E. (?e. E e) /\ (!e. E e = ?si x. S si /\ si x /\ (e = expt x))`
      by (Q.EXISTS_TAC `\x. ?si y. S si /\ si y /\ (x = expt y)`
          THEN METIS_TAC[]) THEN
`!e. E e ==> is_ord(e) /\ rank e <= n` by
    (RW_TAC ord_ss [] THEN METIS_TAC [is_ord_expt_closed,rank_expt,LESS_OR_EQ])

THEN

(*---------------------------------------------------------------------------*)
(* So has a minimal element (alpha_1) by the IH                              *)
(*---------------------------------------------------------------------------*)

`?alpha_1. is_ord(alpha_1) /\ E alpha_1 /\ rank alpha_1 <= n /\
              !y. is_ord(y) /\ rank y <= n /\ oless y alpha_1 ==> ~E y`
   by (RES_TAC THEN METIS_TAC [])

THEN

(*---------------------------------------------------------------------------*)
(* Now we are going to work inside a particular set of ordinals that has an  *)
(* element that alpha_1 is the first exponent of. There may be more than one *)
(* such set, of course, but we already have a witness from showing the       *)
(* existence of alpha_1.                                                     *)
(*---------------------------------------------------------------------------*)

`?sj x. S sj /\ sj x /\ (alpha_1 = expt x)` by METIS_TAC[]

THEN

(*---------------------------------------------------------------------------*)
(* Now consider the subset of sj where all the ordinals have first exponent  *)
(* equal to alpha_1. Call it s_alpha_1.                                      *)
(*---------------------------------------------------------------------------*)

`?s_alpha_1.
       (?a. s_alpha_1 a) /\
       (!b. s_alpha_1(b) <=> sj(b) /\ (expt b = alpha_1))`
    by (Q.EXISTS_TAC `\x. sj(x) /\ (expt x = alpha_1)` THEN METIS_TAC [])

THEN

(*---------------------------------------------------------------------------*)
(* Now we want to consider the set of all first coeff. for any ordinal in    *)
(* s_alpha_1. This is a set of nums, so has a minimum element, k_1.          *)
(*---------------------------------------------------------------------------*)

let val wop_thm =
REWRITE_RULE []
 (Q.SPEC `a`
   (Q.SPEC `coeff a`
      (Ho_Rewrite.REWRITE_RULE
            [GSYM LEFT_FORALL_IMP_THM,
             GSYM LEFT_EXISTS_AND_THM,
             GSYM RIGHT_EXISTS_AND_THM]
      (BETA_RULE (SPEC ``\n. ?x. s_alpha_1(x) /\ (n = coeff x)`` WOP)))))
in
`?k_1 x1. (s_alpha_1 x1 /\ (k_1 = coeff x1)) /\
             !m. m < k_1 ==> ~?b. s_alpha_1 b /\ (m = coeff b)`
  by (MATCH_MP_TAC wop_thm THEN FIRST_ASSUM ACCEPT_TAC)
end

THEN

(*---------------------------------------------------------------------------*)
(* Consider the subset of ordinals in s_alpha_1 that have k_1 as first expt. *)
(* This is n.e.                                                              *)
(*---------------------------------------------------------------------------*)

`?s_alpha_1_k_1.
     (?a1. s_alpha_1_k_1(a1)) /\
     (!b. s_alpha_1_k_1(b) <=> s_alpha_1 b /\ (coeff(b) = k_1))`
  by (Q.EXISTS_TAC `\x. s_alpha_1(x) /\ (coeff(x) = k_1)` THEN METIS_TAC [])

THEN

(*---------------------------------------------------------------------------*)
(* Consider the set of all tails of elements of s_alpha_1_k_1. This is n.e.  *)
(*---------------------------------------------------------------------------*)

`?Tails. (?b. Tails b) /\
         (!c. Tails(c) <=> ?b. s_alpha_1_k_1(b) /\ (c = tail b))`
     by (Q.EXISTS_TAC `\x. ?b. s_alpha_1_k_1(b) /\ (x = tail b)`
         THEN METIS_TAC [])

THEN

`!q. Tails q ==> is_ord q` by
    (RW_TAC std_ss [] THEN
     METIS_TAC [rank_finp,NOT_SUC,is_ord_tail_closed])

THEN

(*---------------------------------------------------------------------------*)
(* Consider whether there is some x in Tails with rank <= n. If so, use IH;  *)
(* otherwise, all x in Tails have rank n+1 and we recap.                     *)
(*---------------------------------------------------------------------------*)

Cases_on `?d. Tails(d) /\ rank d <= n`

THENL

(*---------------------------------------------------------------------------*)
(* Start first case. There is a "d" in Tails with rank <=n.                  *)
(* Use IH to get min.el. t                                                   *)
(*---------------------------------------------------------------------------*)

[`?t. Tails t /\ rank t <= n /\
       !y. is_ord y /\ rank y <= n /\ oless y t ==> ~Tails y`
     by (POP_ASSUM STRIP_ASSUME_TAC THEN
         Q.ABBREV_TAC `Q = \x. Tails x /\ rank(x) <= n` THEN
         `?x. Q x /\ !x. Q x ==> is_ord(x) /\ rank(x) <= n` by METIS_TAC[] THEN
         Q.PAT_X_ASSUM `!P:osyntax->bool. !x. A P x ==> B P x`
               (MP_TAC o BETA_RULE o Q.SPECL [`Q`, `x'`]) THEN
         Q.UNABBREV_TAC `Q` THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN METIS_TAC[])

  THEN

(*---------------------------------------------------------------------------*)
(* Then  w^alpha_1 \cdot k_1 + t is in sj.                                   *)
(*---------------------------------------------------------------------------*)

`sj (Plus alpha_1 k_1 t)` by
    (`?v. s_alpha_1_k_1 v /\ (t = tail v)` by METIS_TAC[] THEN
     `s_alpha_1 v /\ (coeff v = coeff x1)` by METIS_TAC [] THEN
     `sj(v) /\ (expt v = expt x)` by METIS_TAC [] THEN
     `v = Plus (expt v) (coeff v) (tail v)`
       by METIS_TAC [rank_positive,LESS_0] THEN
    METIS_TAC [])

THEN

(*---------------------------------------------------------------------------*)
(* The ordinal (Plus alpha_1 k_1 t) is minimal in sj, so contradiction       *)
(*---------------------------------------------------------------------------*)

`?y. sj y /\ oless y (Plus alpha_1 k_1 t)` by METIS_TAC [] THEN
`is_ord y /\ (y = Plus (expt y) (coeff y) (tail y))`
      by METIS_TAC [rank_positive,LESS_0] THEN POP_ASSUM SUBST_ALL_TAC THEN
 Q.PAT_X_ASSUM `oless _ _` MP_TAC THEN
 RW_TAC ord_ss [Once oless_cases] THENL
 [METIS_TAC [expt_def],
  METIS_TAC [expt_def,coeff_def],
   `Tails (tail y)` by METIS_TAC [tail_def, expt_def,coeff_def] THEN
   `is_ord (tail y)` by METIS_TAC [is_ord_tail_closed,finp_def] THEN STRIP_TAC THEN
   `rank (tail y) <= rank t` by METIS_TAC [oless_imp_rank_leq] THEN
   METIS_TAC[LESS_EQ_TRANS]],
 ALL_TAC
]

(*---------------------------------------------------------------------------*)
(* End first case.                                                           *)
(*---------------------------------------------------------------------------*)

THEN

(*---------------------------------------------------------------------------*)
(* Other side of case: Everything in Tails has rank = n+1                    *)
(*---------------------------------------------------------------------------*)

`!d. Tails(d) ==> n < rank (d)` by METIS_TAC[DECIDE``~(x<=y) <=> y<x``] THEN
`!d. Tails(d) ==> rank d <= SUC n`
      by (RW_TAC ord_ss [] THEN `SUC n = rank b'` by METIS_TAC []
          THEN POP_ASSUM SUBST1_TAC
           THEN METIS_TAC [oless_imp_rank_leq,rank_finp, SUC_NOT,
                           is_ord_tail_closed,oless_tail]) THEN
`!d. Tails d ==> (rank d = SUC n)`
      by METIS_TAC [DECIDE ``x < y /\ y <= SUC x ==> (y=SUC x)``] THEN
 POP_ASSUM (fn th => NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN ASSUME_TAC th)

THEN

(*---------------------------------------------------------------------------*)
(*  Now split on if Tails has a minimal element                              *)
(*---------------------------------------------------------------------------*)

Cases_on `!c. Tails(c) ==> ?d. Tails d /\ oless d c`

THENL
[
(*---------------------------------------------------------------------------*)
(* First case: No min.el., so contradiction because Tails \in S, but can't   *)
(* be, because of what S is.                                                 *)
(*---------------------------------------------------------------------------*)

`S Tails` by (RW_TAC ord_ss [] THEN METIS_TAC[]) THEN
`!d. Tails d ==> oless (expt d) (expt x)`
       by METIS_TAC [decompose_plus,rank_positive,LESS_0] THEN
`!d. Tails d ==> oless (expt x) (expt d)`
       by METIS_TAC [decompose_plus, rank_positive_expt,DECIDE``(m=n)==>m<=n``]
THEN METIS_TAC [oless_antisym],
ALL_TAC
]

THEN

(*---------------------------------------------------------------------------*)
(* Otherwise, Tails has an oless min.el., so build min.el of sj, in a        *)
(* similar way to how it was already done above.                             *)
(*---------------------------------------------------------------------------*)

`?t. Tails t /\ !u. is_ord u /\ oless u t ==> ~Tails u` by METIS_TAC [] THEN
`sj (Plus alpha_1 k_1 t)` by
    (`?v. s_alpha_1_k_1 v /\ (t = tail v)` by METIS_TAC[] THEN
     `s_alpha_1 v /\ (coeff v = coeff x1)` by METIS_TAC [] THEN
     `sj(v) /\ (expt v = expt x)` by METIS_TAC [] THEN
     `v = Plus (expt v) (coeff v) (tail v)` by METIS_TAC [rank_positive,LESS_0]
     THEN METIS_TAC [])

THEN

(*---------------------------------------------------------------------------*)
(* But S implies there is an element of sj less than w^alpha_1 * k1 + t. And *)
(* we again get a contradiction.                                             *)
(*---------------------------------------------------------------------------*)

`?y. sj y /\ oless y (Plus alpha_1 k_1 t)` by METIS_TAC [] THEN
   POP_ASSUM MP_TAC THEN RW_TAC ord_ss [Once oless_cases] THENL
    [METIS_TAC [rank_def,SUC_NOT],
     METIS_TAC [is_ord_downclosed,rank_positive_expt,expt_def,DECIDE``(m=n) ==> m<=n``],
     METIS_TAC [coeff_def,expt_def],
     METIS_TAC [expt_def,coeff_def,tail_def]]

(*---------------------------------------------------------------------------*)
(* Done.                                                                     *)
(*---------------------------------------------------------------------------*)

);


(*---------------------------------------------------------------------------*)
(* Now to use the lemma. First instantiate it to rank(x).                    *)
(*---------------------------------------------------------------------------*)

val lemma' =
  SIMP_RULE std_ss [LESS_EQ_REFL]
     (Q.SPEC `x`
        (SIMP_RULE std_ss [GSYM LEFT_FORALL_IMP_THM]
           (SPEC_ALL (Q.SPEC `rank x` lemma))));

(*---------------------------------------------------------------------------*)
(* So can rephrase lemma by getting rid of the rank restriction.             *)
(*---------------------------------------------------------------------------*)

val main_lemma = Q.store_thm
("main_lemma",
 `!P. (?x. P x /\ is_ord x) ==>
      ?x. P x /\ is_ord x /\ !y. is_ord y /\ oless y x ==> ~P y`,
 REPEAT STRIP_TAC THEN
   `?m. is_ord m /\ P m /\ rank m <= rank x /\
        !y. is_ord y /\ rank y <= rank x /\ oless y m ==> ~P y` by METIS_TAC [lemma']
  THEN METIS_TAC [oless_imp_rank_leq,LESS_EQ_TRANS]);

(*---------------------------------------------------------------------------*)
(* less-than on ordinals.                                                    *)
(*---------------------------------------------------------------------------*)

val ord_less_def =
 Define
   `ord_less x y <=> is_ord x /\ is_ord y /\ oless x y`;


(*---------------------------------------------------------------------------*)
(* ord_less is well-founded.                                                 *)
(*---------------------------------------------------------------------------*)

val WF_ord_less = Q.store_thm
("WF_ord_less",
 `WF ord_less`,
 RW_TAC ord_ss [relationTheory.WF_DEF,ord_less_def] THEN
 METIS_TAC [main_lemma,ord_less_def]);

(*---------------------------------------------------------------------------*)
(* Hence induction and recursion on the ordinals up to e_0, ala ACL2.        *)
(*---------------------------------------------------------------------------*)

val WF_ord_measure =
 SPEC_ALL (MATCH_MP relationTheory.WF_inv_image WF_ord_less);

val e0_induction = save_thm
("e0_INDUCTION",
 GEN ``P:'a->bool``
  (GEN ``f:'a->osyntax``
    (SPEC_ALL
       (SIMP_RULE std_ss [relationTheory.inv_image_def]
          (MATCH_MP relationTheory.WF_INDUCTION_THM WF_ord_measure)))));

val e0_RECURSION = Q.store_thm
("e0_RECURSION",
 `!f. ?!g. !x. g x = M (RESTRICT g (\x y. ord_less (f x) (f y)) x) x`,
 MATCH_ACCEPT_TAC
   (SIMP_RULE std_ss [relationTheory.inv_image_def]
      (MATCH_MP relationTheory.WF_RECURSION_THM WF_ord_measure)));

(*---------------------------------------------------------------------------*)
(* Ordinal addition, subtraction, multiplication and exponentiation. Taken   *)
(* from Manolios and Vroon, JAR.                                             *)
(*---------------------------------------------------------------------------*)

val ord_add_def =
 Define
  `(ord_add (End m) (End n) = End (m+n)) /\
   (ord_add (End m) (Plus p k t) = Plus p k t) /\
   (ord_add (Plus e k t) (End m) = Plus e k (ord_add t (End m))) /\
   (ord_add (Plus e1 k1 t1) (Plus e2 k2 t2) =
     if oless e1 e2 then Plus e2 k2 t2 else
     if e1 = e2 then Plus e2 (k1+k2) t2 else
     Plus e1 k1 (ord_add t1 (Plus e2 k2 t2)))`;

val ord_sub_def =
 Define
  `(ord_sub (End m) (End n) = End (m-n)) /\
   (ord_sub (End m) (Plus p k t) = End 0) /\
   (ord_sub (Plus e k t) (End m) = Plus e k t) /\
   (ord_sub (Plus e1 k1 t1) (Plus e2 k2 t2) =
     if oless e1 e2 then End 0 else
     if e1 = e2
      then (if k1<k2 then End 0 else
            if k1>k2 then Plus e1 (k1-k2) t1
            else ord_sub t1 t2)
     else Plus e1 k1 t1)`;

(*---------------------------------------------------------------------------*)
(* Weird renaming in last two clauses by Define.                             *)
(*---------------------------------------------------------------------------*)

val ord_mult_def =
 Define
  `ord_mult x y =
    if (x = End 0) \/ (y = End 0) then End 0 else
    case (x,y)
    of (End m, End n) => End (m * n)
     | (End m, Plus e k t) => Plus (ord_add (End 0) e) k (ord_mult (End m) t)
     | (Plus e k t, End n) => Plus e (k*n) t
     | (Plus e1 k1 t1, Plus e2 k2 t2) => Plus (ord_add e1 e2) k2
                                              (ord_mult (Plus e1 k1 t1) t2)`;

val _ = Count.report (Count.read meter);

(* ----------------------------------------------------------------------
    More efficient multiplication (again from Manolios & Vroon)
   ---------------------------------------------------------------------- *)

val restn_def = Define`
  (restn a 0 = a) /\
  (restn a (SUC n) = restn (tail a) n)
`;

val cf1_def = Define`
  (cf1 (End _) b = 0) /\
  (cf1 (Plus e1 c1 k1) b = if ord_less (expt b) e1 then 1 + cf1 k1 b
                           else 0)
`
val _ = export_rewrites ["cf1_def"]

val cf2_def = Define`cf2 a b n = n + cf1 (restn a n) b`

val padd_def = Define`
  (padd a b 0 = ord_add a b) /\
  (padd a b (SUC n) = Plus (expt a) (coeff a) (padd (tail a) b n))
`

val pmult_def = tDefine "pmult" `
  pmult a b n =
    if (a = End 0) \/ (b = End 0) then End 0
    else
      case (a,b) of
          (End i, End j) => End (i * j)
        | (Plus e1 c1 k1, End j) => Plus e1 (c1 * j) k1
        | (_, Plus e2 c2 k2) =>
          let m = cf2 (expt a) e2 n
          in
            Plus (padd (expt a) e2 m) c2 (pmult a k2 m)
` (WF_REL_TAC `measure (osyntax_size o FST o SND)`)

val _ = export_theory();
