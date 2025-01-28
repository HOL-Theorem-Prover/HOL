(* ========================================================================= *)
(*  A basic theory of the cardinality partial order and equivalence          *)
(*  relations (by Michael Norrish, see also README)                          *)
(* ========================================================================= *)
(*  Basic notions of cardinal arithmetic (by John Harrison from HOL-Light)   *)
(* ------------------------------------------------------------------------- *)
(*  HOL-Light's Cardinal Theory (Library/card.ml)                            *)
(*                                                                           *)
(*        (c) Copyright 2015                                                 *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open boolSimps pred_setTheory set_relationTheory tautLib permutesTheory
     prim_recTheory arithmeticTheory numTheory numLib pairTheory mesonLib
     optionTheory sumTheory ind_typeTheory wellorderTheory hurdUtils;

val _ = new_theory "cardinal";

(* ----------------------------------------------------------------------
    K_TAC, METIS, DISC_RW_KILL, ASM_ARITH_TAC
   ---------------------------------------------------------------------- *)

fun K_TAC _ = ALL_TAC;

fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons                                                      *)
(* ------------------------------------------------------------------------- *)

(* first of these clashes with indicator_fn in extreal etc *)
Overload "𝟙"[local] = “{()}”                                           (* UOK *)
Overload "𝟚" = “{T;F}”                                                 (* UOK *)

val cardeq_def = Define`
  cardeq s1 s2 <=> ?f. BIJ f s1 s2
`
val _ = set_fixity "=~" (Infix(NONASSOC, 450));
val _ = Unicode.unicode_version {u = UTF8.chr 0x2248, tmnm = "=~"};
val _ = TeX_notation {hol = "=~",            TeX = ("\\ensuremath{\\approx}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x2248, TeX = ("\\ensuremath{\\approx}", 1)};

val _ = overload_on("=~", ``cardeq``)

Overload "≉" = “λa b. ¬(a ≈ b)”                                        (* UOK *)
val _ = set_fixity "≉" (Infix(NONASSOC, 450))                          (* UOK *)

val cardeq_REFL = store_thm(
  "cardeq_REFL",
  ``!s. s =~ s``,
  rw[cardeq_def] >> qexists_tac `\x. x` >> rw[BIJ_IFF_INV] >>
  qexists_tac `\x. x` >> simp[]);

val cardeq_SYMlemma = prove(
  ``!s t. s =~ t ==> t =~ s``,
  rw[cardeq_def] >> metis_tac [BIJ_LINV_BIJ]);


val cardeq_SYM = store_thm(
  "cardeq_SYM",
  ``!s:'a set t:'b set. s =~ t <=> t =~ s``,
  metis_tac [cardeq_SYMlemma]);

val cardeq_TRANS = store_thm(
  "cardeq_TRANS",
  ``!s t u. s =~ t /\ t =~ u ==> s =~ u``,
  metis_tac [BIJ_COMPOSE, cardeq_def]);

(* less-or-equal *)
val cardleq_def = Define`
  cardleq s1 s2 <=> ?f. INJ f s1 s2
`;

val _ = overload_on ("<<=", ``cardleq``)

val cardleq_REFL = store_thm(
  "cardleq_REFL",
  ``!s:'a set. s <<= s``,
  rw[cardleq_def] >> qexists_tac `\x. x` >> rw[INJ_ID]);
val _ = export_rewrites ["cardleq_REFL"]

val cardleq_TRANS = store_thm(
  "cardleq_TRANS",
  ``!s:'a set t:'b set u:'c set. s <<= t /\ t <<= u ==> s <<= u``,
  rw[cardleq_def] >> metis_tac [INJ_COMPOSE]);

(* Schroeder-Bernstein theorem *)
val cardleq_ANTISYM = store_thm (
   "cardleq_ANTISYM",
  ``!s t. s <<= t /\ t <<= s ==> s =~ t``,
    REWRITE_TAC [cardleq_def, cardeq_def]
 >> REWRITE_TAC [SCHROEDER_BERNSTEIN]); (* in pred_setTheory *)

val CARDEQ_FINITE = store_thm(
  "CARDEQ_FINITE",
  ``s1 =~ s2 ==> (FINITE s1 <=> FINITE s2)``,
  metis_tac [cardeq_def, BIJ_FINITE, BIJ_LINV_BIJ]);

val CARDEQ_CARD = store_thm(
  "CARDEQ_CARD",
  ``s1 =~ s2 /\ FINITE s1 ==> (CARD s1 = CARD s2)``,
  metis_tac [cardeq_def, FINITE_BIJ_CARD_EQ, CARDEQ_FINITE]);

val CARDEQ_0 = store_thm(
  "CARDEQ_0",
  ``(x =~ {} <=> (x = {})) /\ (({} =~ x) <=> (x = {}))``,
  rw[cardeq_def, BIJ_EMPTY]);

val cardeq_INSERT = store_thm(
  "cardeq_INSERT",
  ``(x INSERT s) =~ s <=> x IN s \/ INFINITE s``,
  simp[EQ_IMP_THM] >> conj_tac
    >- (Cases_on `FINITE s` >> simp[] >> strip_tac >>
        `CARD (x INSERT s) = CARD s` by metis_tac [CARDEQ_CARD, cardeq_SYM] >>
        pop_assum mp_tac >> srw_tac[ARITH_ss][]) >>
  Cases_on `x IN s` >- metis_tac [ABSORPTION, cardeq_REFL] >> rw[] >>
  match_mp_tac cardleq_ANTISYM >> Tactical.REVERSE conj_tac
    >- (rw[cardleq_def] >> qexists_tac `\x. x` >> rw[INJ_DEF]) >>
  rw[cardleq_def] >> fs[infinite_num_inj] >>
  qexists_tac `\e. if e = x then f 0
                   else case some n. e = f n of
                          NONE => e
                        | SOME n => f (n + 1)` >>
  fs[INJ_DEF] >>
  `!x y. (f x = f y) <=> (x = y)` by metis_tac[] >> rw[] >| [
    rw[option_case_compute],
    DEEP_INTRO_TAC some_intro >> rw[] >>
    metis_tac [DECIDE ``0 <> x + 1``],
    DEEP_INTRO_TAC some_intro >> rw[] >>
    metis_tac [DECIDE ``0 <> x + 1``],
    pop_assum mp_tac >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    DEEP_INTRO_TAC some_intro >> simp[]
  ]);

(* !s. INFINITE s ==> x INSERT s =~ s

   more useful then CARDEQ_INSERT as a (conditional) "rewrite", when
   working with the =~ congruence (rather than equality) *)
val CARDEQ_INSERT_RWT = save_thm(
  "CARDEQ_INSERT_RWT",
  ``INFINITE (s:'a set)`` |> ASSUME |> DISJ2 ``(x:'a) IN s``
                          |> EQ_MP (SYM cardeq_INSERT) |> DISCH_ALL
                          |> Q.GEN `s`)

val EMPTY_CARDLEQ = store_thm(
  "EMPTY_CARDLEQ",
  ``{} <<= t``,
  simp[cardleq_def, INJ_EMPTY]);  (* export_rewrites for pred_set *)
val _ = export_rewrites ["EMPTY_CARDLEQ"]

val FINITE_CLE_INFINITE = store_thm(
  "FINITE_CLE_INFINITE",
  ``FINITE s /\ INFINITE t ==> s <<= t``,
  qsuff_tac `INFINITE t ==> !s. FINITE s ==> s <<= t` >- metis_tac[] >>
  strip_tac >> Induct_on `FINITE` >> conj_tac >- simp[] >>
  simp[cardleq_def] >> gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                              (Q.X_CHOOSE_THEN `f` assume_tac)) >>
  qx_gen_tac `e` >> strip_tac >>
  `FINITE (IMAGE f s)` by simp[] >>
  `?y. y IN t /\ y NOTIN IMAGE f s` by metis_tac [IN_INFINITE_NOT_FINITE] >>
  qexists_tac `\x. if x = e then y else f x` >>
  fs[INJ_DEF] >> asm_simp_tac (srw_ss() ++ DNF_ss) [] >> rw[] >> metis_tac[])

val FORALL_PROD = pairTheory.FORALL_PROD
val CARDEQ_CROSS = store_thm(
  "CARDEQ_CROSS",
  ``s1 =~ s2 /\ t1 =~ t2 ==> (s1 CROSS t1 =~ s2 CROSS t2)``,
  simp[cardeq_def] >>
  disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `f` assume_tac)
                              (Q.X_CHOOSE_THEN `g` assume_tac)) >>
  qexists_tac `f ## g` >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD,
       pairTheory.EXISTS_PROD] >>
  fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >> metis_tac []);

val CARDEQ_CROSS_SYM = store_thm("CARDEQ_CROSS_SYM",
  ``s CROSS t =~ t CROSS s``,
  simp[cardeq_def] >>
  qexists_tac`\p. (SND p,FST p)` >>
  simp[BIJ_IFF_INV] >>
  qexists_tac`\p. (SND p,FST p)` >>
  simp[])

val CARDEQ_SUBSET_CARDLEQ = store_thm(
  "CARDEQ_SUBSET_CARDLEQ",
  ``s =~ t ==> s <<= t``,
  rw[cardeq_def, cardleq_def, BIJ_DEF] >> metis_tac[])

val CARDEQ_CARDLEQ = store_thm(
  "CARDEQ_CARDLEQ",
  ``s1 =~ s2 /\ t1 =~ t2 ==> (s1 <<= t1 <=> s2 <<= t2)``,
  metis_tac[cardeq_SYM, CARDEQ_SUBSET_CARDLEQ, cardleq_TRANS])

val CARDLEQ_FINITE = store_thm("CARDLEQ_FINITE",
  ``!s1 s2. FINITE s2 /\ s1 <<= s2 ==> FINITE s1``,
  metis_tac[cardleq_def,FINITE_INJ])

val _ = type_abbrev ("inf", ``:num + 'a``)

val INFINITE_UNIV_INF = store_thm(
  "INFINITE_UNIV_INF",
  ``INFINITE univ(:'a inf)``,
  simp[INFINITE_UNIV] >> qexists_tac `SUM_MAP SUC I` >>
  simp[sumTheory.FORALL_SUM] >> qexists_tac `INL 0` >> simp[]);
val _ = export_rewrites ["INFINITE_UNIV_INF"]

val IMAGE_cardleq = store_thm(
  "IMAGE_cardleq",
  ``!f s. IMAGE f s <<= s``,
  simp[cardleq_def] >> metis_tac [SURJ_IMAGE, SURJ_INJ_INV]);
val _ = export_rewrites ["IMAGE_cardleq"]

val CARDLEQ_CROSS_CONG = store_thm(
  "CARDLEQ_CROSS_CONG",
  ``!x1 x2 y1 y2. x1 <<= x2 /\ y1 <<= y2 ==> x1 CROSS y1 <<= x2 CROSS y2``,
  rpt gen_tac \\
  simp[cardleq_def] >>
  disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `f1` assume_tac)
                              (Q.X_CHOOSE_THEN `f2` assume_tac)) >>
  fs [INJ_DEF] >>
  qexists_tac `\(x,y). (f1 x, f2 y)` >>
  simp[FORALL_PROD]);

val SUBSET_CARDLEQ = store_thm(
  "SUBSET_CARDLEQ",
  ``!x y. x SUBSET y ==> x <<= y``,
  rpt gen_tac \\
  simp[SUBSET_DEF, cardleq_def] >> strip_tac >> qexists_tac `I` >>
  simp[INJ_DEF]);

val IMAGE_cardleq_rwt = store_thm(
  "IMAGE_cardleq_rwt",
  ``!s t. s <<= t ==> IMAGE f s <<= t``,
  metis_tac [cardleq_TRANS, IMAGE_cardleq]);

val countable_thm = store_thm(
  "countable_thm",
  ``!s. countable s <=> s <<= univ(:num)``,
  simp[countable_def, cardleq_def]);

val countable_cardeq = store_thm(
  "countable_cardeq",
  ``!s t. s =~ t ==> (countable s <=> countable t)``,
  simp[countable_def, cardeq_def, EQ_IMP_THM] >>
  metis_tac [INJ_COMPOSE, BIJ_DEF, BIJ_LINV_BIJ]);

val cardleq_dichotomy = store_thm(
  "cardleq_dichotomy",
  ``!s t. s <<= t \/ t <<= s``,
  rpt gen_tac \\
  `(?w1. elsOf w1 = s) /\ (?w2. elsOf w2 = t)`
    by metis_tac [allsets_wellorderable] >>
  `orderlt w1 w2 \/ orderiso w1 w2 \/ orderlt w2 w1`
    by metis_tac [orderlt_trichotomy]
  >| [
    `?f x. BIJ f s (elsOf (wobound x w2))`
      by metis_tac[orderlt_def, orderiso_thm] >>
    `elsOf (wobound x w2) SUBSET t`
      by (simp[elsOf_wobound, SUBSET_DEF] >> metis_tac [WIN_elsOf]) >>
    rw[] >> qsuff_tac `elsOf w1 <<= elsOf w2` >- simp[] >>
    simp[cardleq_def] >> qexists_tac `f` >>
    fs[BIJ_DEF, INJ_DEF, SUBSET_DEF],

    `?f. BIJ f s t` by metis_tac [orderiso_thm] >>
    fs[BIJ_DEF, cardleq_def] >> metis_tac[],

    `?f x. BIJ f t (elsOf (wobound x w1))`
      by metis_tac[orderlt_def, orderiso_thm] >>
    `elsOf (wobound x w1) SUBSET s`
      by (simp[elsOf_wobound, SUBSET_DEF] >> metis_tac [WIN_elsOf]) >>
    rw[] >> qsuff_tac `elsOf w2 <<= elsOf w1` >- simp[] >>
    simp[cardleq_def] >> qexists_tac `f` >>
    fs[BIJ_DEF, INJ_DEF, SUBSET_DEF]
  ]);

val _ = set_fixity "<</=" (Infix(NONASSOC, 450));

val _ = Unicode.unicode_version {u = UTF8.chr 0x227A, tmnm = "<</="};
val _ = TeX_notation {hol = "<</=",          TeX = ("\\ensuremath{\\prec}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227A, TeX = ("\\ensuremath{\\prec}", 1)};

val _ = overload_on ("cardlt", ``\s1 s2. ~(cardleq s2 s1)``); (* cardlt *)
val _ = overload_on ("<</=", ``cardlt``);

val cardleq_lteq = store_thm(
  "cardleq_lteq",
  ``!s1 s2. s1 <<= s2 <=> s1 <</= s2 \/ (s1 =~ s2)``,
  metis_tac [cardleq_ANTISYM, cardleq_dichotomy, CARDEQ_SUBSET_CARDLEQ]);

val cardlt_REFL = store_thm(
  "cardlt_REFL",
  ``!s. ~(s <</= s)``,
  simp[cardleq_REFL]);

val cardlt_lenoteq = store_thm(
  "cardlt_lenoteq",
  ``!s t. s <</= t <=> s <<= t /\ ~(s =~ t)``,
  metis_tac [cardleq_dichotomy, CARDEQ_SUBSET_CARDLEQ, cardeq_SYM,
             cardleq_ANTISYM, cardeq_REFL]);

val cardlt_TRANS = store_thm(
  "cardlt_TRANS",
  ``!s t u:'a set. s <</= t /\ t <</= u ==> s <</= u``,
  metis_tac [cardleq_TRANS, cardleq_ANTISYM, CARDEQ_SUBSET_CARDLEQ,
             cardeq_SYM, cardlt_lenoteq]);

val cardlt_leq_trans = store_thm("cardlt_leq_trans",
  ``!r s t. r <</= s /\ s <<= t ==> r <</= t``,
  rw[cardlt_lenoteq] >- metis_tac[cardleq_TRANS] >>
  metis_tac[CARDEQ_CARDLEQ,cardeq_REFL,cardleq_ANTISYM])

val cardleq_lt_trans = store_thm("cardleq_lt_trans",
  ``!r s t. r <<= s /\ s <</= t ==> r <</= t``,
  rw[cardlt_lenoteq] >- metis_tac[cardleq_TRANS] >>
  metis_tac[CARDEQ_CARDLEQ,cardeq_REFL,cardleq_ANTISYM])

val cardleq_empty = store_thm("cardleq_empty",
  ``!x. x <<= {} <=> (x = {})``,
  simp[cardleq_lteq,CARDEQ_0])

val better_BIJ = BIJ_DEF |> SIMP_RULE (srw_ss() ++ CONJ_ss) [INJ_DEF, SURJ_DEF]

fun unabbrev_in_goal s = let
  fun check th = let
    val c = concl th
    val _ = match_term ``Abbrev b`` c
    val (v,ty) = c |> rand |> lhand |> dest_var
  in
    if v = s then let
        val th' = PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
      in
        SUBST1_TAC th'
      end
    else NO_TAC
  end
in
  first_assum check
end

Theorem set_binomial2:
  (A UNION B) CROSS (A UNION B) =
  A CROSS A UNION A CROSS B UNION B CROSS A UNION B CROSS B
Proof
  simp[EXTENSION, FORALL_PROD] >>
  simp_tac (srw_ss() ++ DNF_ss) [DISJ_ASSOC]
QED

val lemma1 = prove(
  ``INFINITE M /\ M =~ M CROSS M ==>
    M =~ {T;F} CROSS M /\
    !A B. DISJOINT A B /\ A =~ M /\ B =~ M ==> A UNION B =~ M``,
  strip_tac >> CONJ_ASM1_TAC
  >- (match_mp_tac cardleq_ANTISYM >> conj_tac
      >- (simp[cardleq_def] >> qexists_tac `\x. (T,x)` >> simp[INJ_DEF]) >>
     `M CROSS M <<= M` by metis_tac [CARDEQ_CARDLEQ, cardleq_REFL, cardeq_REFL] >>
     qsuff_tac `{T;F} CROSS M <<= M CROSS M` >- metis_tac [cardleq_TRANS] >>
     match_mp_tac CARDLEQ_CROSS_CONG >> simp[FINITE_CLE_INFINITE]) >>
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  `(?f1. BIJ f1 A M) /\ (?f2. BIJ f2 B M)` by metis_tac[cardeq_def] >>
  qsuff_tac `A UNION B =~ {T;F} CROSS M`
  >- metis_tac [cardeq_TRANS, cardeq_SYM] >>
  simp[cardeq_def] >>
  qexists_tac `\x. if x IN A then (T,f1 x) else (F,f2 x)` >>
  simp[better_BIJ] >> rpt conj_tac
  >- (fs[better_BIJ] >> rw[])
  >- (map_every qx_gen_tac [`a`, `b`] >> strip_tac >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF, pairTheory.PAIR_EQ]) >>
  simp[FORALL_PROD] >> map_every qx_gen_tac [`test`, `m`] >> strip_tac >>
  Cases_on `test`
  >- (`?a. a IN A /\ (f1 a = m)` by metis_tac [BIJ_DEF, SURJ_DEF] >>
      qexists_tac `a` >> simp[]) >>
  `?b. b IN B /\ (f2 b = m)` by metis_tac [BIJ_DEF, SURJ_DEF] >>
  qexists_tac `b` >> simp[] >> metis_tac[]);

fun PRINT_TAC s gl = (print ("** " ^ s ^ "\n"); ALL_TAC gl)

val SET_SQUARED_CARDEQ_SET = store_thm(
  "SET_SQUARED_CARDEQ_SET",
  ``!s. INFINITE s ==> (s CROSS s =~ s)``,
  PRINT_TAC "beginning s CROSS s =~ s proof" >>
  rpt strip_tac >>
  qabbrev_tac `
    A = { (As,f) | INFINITE As /\ As SUBSET s /\ BIJ f As (As CROSS As) /\
                   !x. x NOTIN As ==> (f x = ARB) }` >>
  qabbrev_tac `
    rr = {((s1:'a set,f1),(s2,f2)) | (s1,f1) IN A /\ (s2,f2) IN A /\
                                     s1 SUBSET s2 /\
                                     !x. x IN s1 ==> (f1 x = f2 x)} ` >>
  `partial_order rr A`
     by (simp[partial_order_def] >> rpt conj_tac
         >- (simp[domain_def, Abbr`rr`, SUBSET_DEF] >> rw[] >> rw[])
         >- (simp[range_def, Abbr`rr`, SUBSET_DEF] >> rw[] >> rw[])
         >- (simp[transitive_def, Abbr`rr`] >> rw[] >>
             metis_tac [SUBSET_TRANS, SUBSET_DEF])
         >- simp[reflexive_def, Abbr`rr`, FORALL_PROD] >>
         simp[antisym_def, Abbr`rr`, FORALL_PROD] >>
         map_every qx_gen_tac [`s1`, `f1`, `s2`, `f2`] >>
         strip_tac >> `s1 = s2` by metis_tac [SUBSET_ANTISYM] >>
         fs[Abbr`A`] >> simp[FUN_EQ_THM] >> metis_tac[]) >>
  `A <> {}`
    by (`?Nf. INJ Nf univ(:num) s` by metis_tac [infinite_num_inj] >>
        qabbrev_tac `
           Nfn = \a. case some m. Nf m = a of
                           NONE => ARB
                         | SOME m => (Nf (nfst m), Nf (nsnd m))` >>
        `(IMAGE Nf univ(:num), Nfn) IN A`
           by (`!x y. (Nf x = Nf y) = (x = y)`
                 by metis_tac [INJ_DEF, IN_UNIV] >>
               simp[Abbr`A`] >> conj_tac
               >- (fs[SUBSET_DEF, INJ_DEF] >> metis_tac[]) >>
               simp[better_BIJ] >>
               asm_simp_tac (srw_ss() ++ DNF_ss) [FORALL_PROD] >>
               simp[Abbr`Nfn`] >> conj_tac
               >- (map_every qx_gen_tac [`m`, `p`] >> strip_tac >>
                   map_every (fn q => qspec_then q (SUBST1_TAC o SYM)
                                                 numpairTheory.npair)
                             [`m`, `p`] >> simp[]) >>
               simp[FORALL_PROD] >>
               map_every qx_gen_tac [`m`, `p`] >> qexists_tac `m *, p` >>
               simp[]) >>
        strip_tac >> fs[]) >>
  `!t. chain t rr ==> upper_bounds t rr <> {}`
     by (PRINT_TAC "beginning proof that chains have upper bound" >>
         gen_tac >>
         simp[chain_def] >> strip_tac >>
         `!s0 f. (s0,f) IN t ==> BIJ f s0 (s0 CROSS s0) /\ s0 SUBSET s /\ (s0,f) IN A /\
                              !x. x NOTIN s0 ==> (f x = ARB)`
            by (rpt gen_tac >> strip_tac >>
                pop_assum (fn th => first_x_assum (fn impth =>
                  mp_tac (MATCH_MP impth (CONJ th th)))) >>
                rw[Abbr`rr`, Abbr`A`]) >>
         simp[upper_bounds_def] >> simp[EXTENSION] >>
         `!s1 f1 s2 f2 x. (s1,f1) IN t /\ (s2,f2) IN t /\ x IN s1 /\ x IN s2 ==>
                          (f1 x = f2 x)`
            by (rpt strip_tac >>
                Q.UNDISCH_THEN `(s1,f1) IN t` (fn th1 =>
                   Q.UNDISCH_THEN `(s2,f2) IN t` (fn th2 =>
                    first_x_assum (fn impth =>
                                      mp_tac
                                          (MATCH_MP impth (CONJ th1 th2))))) >>
                simp[Abbr`rr`] >> rw[] >> rw[]) >>
         qabbrev_tac `BigSet = BIGUNION (IMAGE FST t)` >>
         qabbrev_tac `BigF = (\a. case some (s,f). (s,f) IN t /\ a IN s of
                                    NONE => ARB
                                  | SOME (_, f) => f a)` >>
         Cases_on `t = {}`
         >- (simp[range_def] >>
             `?x. x IN A` by (fs[EXTENSION] >> metis_tac[]) >>
             map_every qexists_tac [`x`, `x`] >>
             simp[Abbr`rr`] >> Cases_on `x` >> simp[]) >>
         `(BigSet,BigF) IN A` by
            (unabbrev_in_goal "A" >> simp[] >> rpt conj_tac
             >- (simp[Abbr`BigSet`] >> DISJ2_TAC >>
                 simp[pairTheory.EXISTS_PROD] >>
                 `?pr. pr IN t` by simp[MEMBER_NOT_EMPTY] >>
                 Cases_on `pr` >> res_tac >> fs[Abbr`A`] >> metis_tac[])
             >- (simp_tac (srw_ss() ++ DNF_ss)
                          [BIGUNION_SUBSET, FORALL_PROD, Abbr`BigSet`] >>
                 metis_tac[])
             >- ((* showing function is a bijection *)
                 asm_simp_tac (srw_ss() ++ DNF_ss)
                              [better_BIJ, FORALL_PROD, Abbr`BigF`,
                               Abbr`BigSet`, pairTheory.EXISTS_PROD] >>
                 rpt conj_tac
                 >- ((* function hits target set *)
                     map_every qx_gen_tac [`a`, `ss`, `sf`] >>
                     strip_tac >>
                     map_every qexists_tac [`ss`, `sf`, `ss`, `sf`] >>
                     simp[] >>
                     qmatch_abbrev_tac `FST XX IN ss /\ SND XX IN ss` >>
                     `XX = sf a`
                        by (simp[Abbr`XX`] >>
                            DEEP_INTRO_TAC some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     `BIJ sf ss (ss CROSS ss)` by metis_tac[] >> simp[] >>
                     pop_assum mp_tac >> simp_tac (srw_ss())[better_BIJ] >>
                     simp[])
                 >- ((* function is injective *)
                     map_every qx_gen_tac
                               [`a1`, `a2`, `s1`, `f1`, `s2`, `f2`] >>
                     strip_tac >>
                     qmatch_abbrev_tac `(XX1 = XX2) ==> (a1 = a2)` >>
                     `XX1 = f1 a1`
                        by (simp[Abbr`XX1`] >>
                            DEEP_INTRO_TAC some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     `XX2 = f2 a2`
                        by (simp[Abbr`XX2`] >>
                            DEEP_INTRO_TAC some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     map_every markerLib.RM_ABBREV_TAC ["XX1", "XX2"] >>
                     rw[] >>
                     Q.UNDISCH_THEN `(s1,f1) IN t` (fn th1 =>
                        (Q.UNDISCH_THEN `(s2,f2) IN t` (fn th2 =>
                           (first_x_assum (fn impth =>
                              mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                     simp[Abbr`rr`, Abbr`A`] >> rw[]
                     >- (`f1 a1 = f2 a1` by metis_tac[] >>
                         `a1 IN s2` by metis_tac [SUBSET_DEF] >>
                         metis_tac [BIJ_DEF, INJ_DEF]) >>
                     `f2 a2 = f1 a2` by metis_tac[] >>
                     `a2 IN s1` by metis_tac [SUBSET_DEF] >>
                     metis_tac [BIJ_DEF, INJ_DEF]) >>
                 (* function is surjective *)
                 map_every qx_gen_tac [`a`, `b`, `s1`, `f1`, `s2`, `f2`] >>
                 strip_tac >>
                 Q.UNDISCH_THEN `(s1,f1) IN t` (fn th1 =>
                    (Q.UNDISCH_THEN `(s2,f2) IN t` (fn th2 =>
                       (first_assum (fn impth =>
                          mp_tac (MATCH_MP impth (CONJ th1 th2)) >>
                          assume_tac th1 >> assume_tac th2))))) >>
                 unabbrev_in_goal "rr" >> simp_tac(srw_ss())[] >> rw[]
                 >- (`a IN s2` by metis_tac [SUBSET_DEF] >>
                     `(a,b) IN s2 CROSS s2` by simp[] >>
                     `?x. x IN s2 /\ (f2 x = (a,b))`
                       by metis_tac [SURJ_DEF, BIJ_DEF] >>
                     map_every qexists_tac [`x`, `s2`, `f2`] >>
                     simp[] >> DEEP_INTRO_TAC some_intro >>
                     simp[FORALL_PROD] >>
                     Tactical.REVERSE conj_tac >- metis_tac[] >>
                     map_every qx_gen_tac [`s3`, `f3`] >> strip_tac >>
                     Q.UNDISCH_THEN `(s2,f2) IN t` (fn th1 =>
                        (Q.UNDISCH_THEN `(s3,f3) IN t` (fn th2 =>
                           (first_x_assum (fn impth =>
                              mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                     unabbrev_in_goal "rr" >> simp[] >> rw[] >> metis_tac[]) >>
                 `b IN s1` by metis_tac [SUBSET_DEF] >>
                 `(a,b) IN s1 CROSS s1` by simp[] >>
                 `?x. x IN s1 /\ (f1 x = (a,b))`
                   by metis_tac[BIJ_DEF, SURJ_DEF] >>
                 map_every qexists_tac [`x`, `s1`, `f1`] >> simp[] >>
                 DEEP_INTRO_TAC some_intro >>
                 simp[FORALL_PROD] >>
                 Tactical.REVERSE conj_tac >- metis_tac[] >>
                 map_every qx_gen_tac [`s3`, `f3`] >> strip_tac >>
                 Q.UNDISCH_THEN `(s1,f1) IN t` (fn th1 =>
                    (Q.UNDISCH_THEN `(s3,f3) IN t` (fn th2 =>
                       (first_x_assum (fn impth =>
                          mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                 unabbrev_in_goal "rr" >> simp[] >> rw[] >> metis_tac[]) >>
             (* function is ARB outside of domain *)
             qx_gen_tac `x` >>
             asm_simp_tac (srw_ss() ++ DNF_ss)
                          [Abbr`BigF`, Abbr`BigSet`,
                           DECIDE ``~p\/q = (p ==> q)``, FORALL_PROD]>>
             strip_tac >> DEEP_INTRO_TAC some_intro >>
             simp[FORALL_PROD] >> metis_tac[]) >>
         qexists_tac `(BigSet, BigF)` >> conj_tac
         >- ((* (BigSet, BigF) IN range rr *)
             simp[range_def] >> qexists_tac `(BigSet,BigF)` >>
             simp[Abbr`rr`]) >>
         (* upper bound really is bigger than arbitrary element of chain *)
         simp[FORALL_PROD] >> map_every qx_gen_tac [`s1`, `f1`] >>
         Cases_on `(s1,f1) IN t` >> simp[] >>
         unabbrev_in_goal "rr" >> simp[] >> conj_tac
         >- (simp[Abbr`BigSet`] >> match_mp_tac SUBSET_BIGUNION_I >>
             simp[pairTheory.EXISTS_PROD] >> metis_tac[]) >>
         qx_gen_tac `x` >> strip_tac >> simp[Abbr`BigF`] >>
         DEEP_INTRO_TAC some_intro >>
         simp[FORALL_PROD] >> metis_tac[]) >>
  PRINT_TAC "proved that upper bound works" >>
  `?Mf. Mf IN maximal_elements A rr` by metis_tac [zorns_lemma] >>
  `?M mf. Mf = (M,mf)` by metis_tac [pairTheory.pair_CASES] >>
  pop_assum SUBST_ALL_TAC >>
  fs[maximal_elements_def] >>
  Q.UNDISCH_THEN `(M,mf) IN A` mp_tac >> unabbrev_in_goal "A" >> simp[] >>
  strip_tac >>
  `M =~ M CROSS M` by metis_tac[cardeq_def] >>
  Cases_on `M =~ s` >- metis_tac [CARDEQ_CROSS, cardeq_TRANS, cardeq_SYM] >>
  `M <<= s` by simp[SUBSET_CARDLEQ] >>
  `M =~ {T;F} CROSS M` by metis_tac [lemma1] >>
  `s = M UNION (s DIFF M)` by (fs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  `~(s DIFF M <<= M)`
    by (strip_tac >>
        qsuff_tac `s <<= M` >- metis_tac [cardleq_ANTISYM] >>
        qsuff_tac `s <<= {T;F} CROSS M` >- metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
        `?f0. INJ f0 (s DIFF M) M` by metis_tac[cardleq_def] >>
        simp[cardleq_def, INJ_DEF] >>
        qexists_tac `\a. if a IN M then (T,a) else (F,f0 a)` >>
        simp[] >> conj_tac
        >- (rw[] >> metis_tac [IN_DIFF, INJ_DEF]) >>
        rw[] >> prove_tac[IN_DIFF, INJ_DEF]) >>
  `~(s DIFF M =~ M)` by metis_tac [CARDEQ_SUBSET_CARDLEQ] >>
  `?f. INJ f M (s DIFF M)` by metis_tac [cardleq_def, cardlt_lenoteq] >>
  qabbrev_tac `E = IMAGE f M` >>
  `E SUBSET s DIFF M` by (fs[INJ_DEF, SUBSET_DEF, Abbr`E`] >> metis_tac[]) >>
  `INJ f M E` by (fs[Abbr`E`, INJ_DEF] >> metis_tac[]) >>
  `SURJ f M E` by simp[Abbr`E`] >>
  `M =~ E` by metis_tac[cardeq_def, BIJ_DEF] >>
  `E CROSS E =~ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `E CROSS M =~ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `M CROSS E =~ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `DISJOINT (E CROSS M) (E CROSS E)`
    by (simp[DISJOINT_DEF, EXTENSION, FORALL_PROD] >>
        metis_tac [SUBSET_DEF, IN_DIFF]) >>
  `(E CROSS M) UNION (E CROSS E) =~ M` by metis_tac [lemma1] >>
  `DISJOINT (M CROSS E) (E CROSS M UNION E CROSS E)`
    by (simp[DISJOINT_DEF, EXTENSION, FORALL_PROD] >>
        metis_tac [SUBSET_DEF, IN_DIFF]) >>
  `M CROSS E UNION (E CROSS M UNION E CROSS E) =~ M` by metis_tac[lemma1] >>
  `M CROSS E UNION E CROSS M UNION E CROSS E =~ E`
    by metis_tac[UNION_ASSOC, cardeq_TRANS] >>
  pop_assum mp_tac >> qmatch_abbrev_tac `ME =~ E ==> s CROSS s =~ s` >>
  strip_tac >>
  `?f0. BIJ f0 E ME` by metis_tac [cardeq_def, cardeq_SYM] >>
  qabbrev_tac `FF = \m. if m IN M then mf m else if m IN E then f0 m else ARB` >>
  `(M UNION E) CROSS (M UNION E) = M CROSS M UNION ME`
    by simp[Abbr`ME`, UNION_ASSOC, set_binomial2] >>
  qabbrev_tac `MM = M CROSS M` >>
  `DISJOINT M E`
    by (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[IN_DIFF, SUBSET_DEF]) >>
  `DISJOINT MM ME`
    by (pop_assum mp_tac >>
        simp[DISJOINT_DEF, EXTENSION, Abbr`ME`, Abbr`MM`, FORALL_PROD] >>
        metis_tac[]) >>
  PRINT_TAC "proving properties of new (can't exist) bijection" >>
  `BIJ FF (M UNION E) ((M UNION E) CROSS (M UNION E))`
    by (simp[better_BIJ, Abbr`FF`] >> rpt conj_tac
        >- (qx_gen_tac `m` >> Cases_on `m IN M` >> simp[] >>
            fs[better_BIJ] >> strip_tac >>
            map_every qunabbrev_tac [`ME`, `MM`] >>
            fs[] >> metis_tac[])
        >- (map_every qx_gen_tac [`m1`, `m2`] >>
            strip_tac >> fs[better_BIJ, DISJOINT_DEF, EXTENSION] >>
            metis_tac[])
        >- (simp[FORALL_PROD] >> map_every qx_gen_tac [`m1`, `m2`] >>
            strip_tac
            >- (fs[better_BIJ] >> qsuff_tac `(m1,m2) IN MM` >- metis_tac[] >>
                simp[Abbr`MM`]) >>
            (Q.UNDISCH_THEN `DISJOINT M E` mp_tac >>
             simp[DISJOINT_DEF, EXTENSION] >> strip_tac >>
             fs[better_BIJ] >>
             qsuff_tac `(m1,m2) IN ME` >- metis_tac[] >>
             simp[Abbr`ME`]))) >>
  `(M UNION E, FF) IN A`
    by (simp[Abbr`A`] >> conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
        simp[Abbr`FF`]) >>
  `(M,mf) <> (M UNION E, FF)`
    by (`M <> {}` by metis_tac[FINITE_EMPTY] >>
        simp[] >> simp[EXTENSION] >>
        fs[DISJOINT_DEF, EXTENSION] >> metis_tac[CARDEQ_0, MEMBER_NOT_EMPTY]) >>
  qsuff_tac `((M,mf), (M UNION E, FF)) IN rr` >- metis_tac[] >>
  simp[Abbr`rr`] >> conj_tac >- simp[Abbr`A`] >>
  simp[Abbr`FF`]);

val SET_SUM_CARDEQ_SET = store_thm(
  "SET_SUM_CARDEQ_SET",
  ``INFINITE s ==>
    s =~ {T;F} CROSS s /\
    !A B. DISJOINT A B /\ A =~ s /\ B =~ s ==> A UNION B =~ s``,
  metis_tac[lemma1, SET_SQUARED_CARDEQ_SET, cardeq_SYM]);

val CARD_BIGUNION = store_thm(
  "CARD_BIGUNION",
  ``INFINITE k /\ s1 <<= k /\ (!e. e IN s1 ==> e <<= k) ==> BIGUNION s1 <<= k``,
  `BIGUNION s1 = BIGUNION (s1 DELETE {})` by (simp[EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `INFINITE k` >> simp[cardleq_def] >>
  disch_then (CONJUNCTS_THEN2
                  (Q.X_CHOOSE_THEN `f` strip_assume_tac) strip_assume_tac) >>
  qabbrev_tac `s = s1 DELETE {}` >>
  `INJ f s k` by fs[INJ_DEF, Abbr`s`] >>
  `(s = {}) \/ ?ff. SURJ ff k s` by metis_tac [inj_surj] >- simp[INJ_EMPTY] >>
  `{} NOTIN s` by simp[Abbr`s`] >>
  qsuff_tac `?fg. SURJ fg k (BIGUNION s)` >- metis_tac[SURJ_INJ_INV] >>
  `k =~ k CROSS k` by metis_tac [SET_SQUARED_CARDEQ_SET, cardeq_SYM] >>
  `?kkf. BIJ kkf k (k CROSS k)` by metis_tac [cardeq_def] >>
  qsuff_tac `?fg. SURJ fg (k CROSS k) (BIGUNION s)`
  >- (strip_tac >> qexists_tac `fg o kkf` >> match_mp_tac SURJ_COMPOSE >>
      metis_tac[BIJ_DEF]) >>
  `!e. e IN s ==> ?g. SURJ g k e` by metis_tac[inj_surj, IN_DELETE] >>
  pop_assum (Q.X_CHOOSE_THEN `g` assume_tac o
             CONV_RULE (BINDER_CONV RIGHT_IMP_EXISTS_CONV THENC
                        SKOLEM_CONV)) >>
  qexists_tac `\(k1,k2). g (ff k1) k2` >>
  asm_simp_tac (srw_ss() ++ DNF_ss)
       [SURJ_DEF, FORALL_PROD, pairTheory.EXISTS_PROD] >>
  fs[SURJ_DEF] >> metis_tac[]);

val CARD_MUL_ABSORB_LE = store_thm("CARD_MUL_ABSORB_LE",
  ``!s t. INFINITE t /\ s <<= t ==> s CROSS t <<= t``,
  metis_tac[CARDLEQ_CROSS_CONG,SET_SQUARED_CARDEQ_SET,
            cardleq_lteq,cardleq_TRANS,cardleq_REFL])

val CARD_MUL_LT_LEMMA = store_thm("CARD_MUL_LT_LEMMA",
  ``!s t. s <<= t /\ t <</= u /\ INFINITE u ==> s CROSS t <</= u``,
  rw[] >>
  Cases_on`FINITE t` >- (
    metis_tac[CARDLEQ_FINITE,FINITE_CROSS] ) >>
  metis_tac[CARD_MUL_ABSORB_LE,cardleq_lt_trans])

val CARD_MUL_LT_INFINITE = store_thm("CARD_MUL_LT_INFINITE",
  ``!s t. s <</= t /\ t <</= u /\ INFINITE u ==> s CROSS t <</= u``,
  metis_tac[CARD_MUL_LT_LEMMA,cardleq_lteq])

(* set exponentiation *)
Definition set_exp_def:
  set_exp A B = { f | (!b. b IN B ==> ?a. a IN A /\ (f b = a)) /\
                      !b. b NOTIN B ==> (f b = ARB) }
End
Overload "**" = “set_exp”

Theorem exp_c :
    !(s :'a set) (t :'b set).
         s ** t =
         {f | (!x. x IN t ==> f x IN s) /\ (!x. ~(x IN t) ==> f x = ARB)}
Proof
    rw [set_exp_def, Once EXTENSION]
QED

Theorem UNIV_fun_exp:
  univ(:'a -> 'b) = univ(:'b) ** univ(:'a)
Proof
  simp[set_exp_def]
QED

(* |- univ(:'b) ** univ(:'a) = univ(:'a -> 'b) *)
Theorem CARD_EXP_UNIV = GSYM UNIV_fun_exp

Theorem BIJ_functions_agree:
  !f g s t. BIJ f s t /\ (!x. x IN s ==> (f x = g x)) ==> BIJ g s t
Proof
  simp[BIJ_DEF, SURJ_DEF, INJ_DEF] >> rw[] >>
  full_simp_tac (srw_ss() ++ boolSimps.CONJ_ss) []
QED

Theorem CARD_CARDEQ_I:
  FINITE s1 /\ FINITE s2 /\ (CARD s1 = CARD s2) ==> s1 =~ s2
Proof
  Cases_on `FINITE s1` >> simp[] >> qid_spec_tac `s2` >> pop_assum mp_tac >>
  qid_spec_tac `s1` >> ho_match_mp_tac FINITE_INDUCT >> simp[] >> conj_tac
  >- metis_tac [CARD_EQ_0, cardeq_REFL, CARDEQ_0] >>
  qx_gen_tac `s1` >> strip_tac >> qx_gen_tac `a` >> strip_tac >>
  qx_gen_tac `s2` >>
  ‘(s2 = {}) \/ ?b s. (s2 = b INSERT s) /\ b NOTIN s’
    by metis_tac [SET_CASES] >>
  csimp[] >> strip_tac >> `s1 =~ s` by metis_tac[] >>
  `?f. BIJ f s1 s` by metis_tac [cardeq_def] >>
  simp[cardeq_def] >> qexists_tac `\x. if x = a then b else f x` >>
  simp[BIJ_INSERT] >>
  `(b INSERT s) DELETE b = s` by (simp[EXTENSION] >> metis_tac[]) >>
  match_mp_tac BIJ_functions_agree >> qexists_tac `f` >> rw[]
QED

val CARDEQ_CARD_EQN = store_thm(
  "CARDEQ_CARD_EQN",
  ``FINITE s1 /\ FINITE s2 ==> (s1 =~ s2 <=> (CARD s1 = CARD s2))``,
  metis_tac [CARD_CARDEQ_I, CARDEQ_CARD]);

val CARDLEQ_CARD = store_thm("CARDLEQ_CARD",
  ``FINITE s1 /\ FINITE s2 ==> (s1 <<= s2 <=> CARD s1 <= CARD s2)``,
  rw[EQ_IMP_THM] >-
    metis_tac[cardleq_def,INJ_CARD] >>
  Cases_on`CARD s1 = CARD s2` >-
    metis_tac[cardleq_lteq,CARDEQ_CARD_EQN] >>
  simp[Once cardleq_lteq] >> disj1_tac >>
  simp[cardleq_def] >>
  gen_tac >> match_mp_tac PHP >>
  fsrw_tac[ARITH_ss][])

val CARD_LT_CARD = store_thm("CARD_LT_CARD",
  ``FINITE s1 /\ FINITE s2 ==> (s1 <</= s2 <=> CARD s1 < CARD s2)``,
  rw[] >> simp[cardlt_lenoteq,CARDLEQ_CARD,CARDEQ_CARD_EQN])

Theorem EMPTY_set_exp:
  A ** {} = { K ARB } /\ (B <> {} ==> {} ** B = {})
Proof
  simp[set_exp_def] >> conj_tac >- simp[EXTENSION, FUN_EQ_THM] >>
  strip_tac >> qsuff_tac `(!b. b NOTIN B) = F`
  >- (disch_then SUBST_ALL_TAC >> simp[]) >>
  fs[EXTENSION] >> metis_tac[]
QED

Theorem EMPTY_set_exp_CARD:
  A ** {} =~ count 1
Proof
  simp[EMPTY_set_exp, CARDEQ_CARD_EQN]
QED

Theorem SING_set_exp:
  {x} ** B = { (\b. if b IN B then x else ARB) } /\
  A ** {x} = { (\b. if b = x then a else ARB) | a IN A }
Proof
  rw[set_exp_def, EXTENSION] >> rw[FUN_EQ_THM, EQ_IMP_THM] >> rw[] >>
  metis_tac[]
QED

Theorem SING_set_exp_CARD:
  {x} ** B =~ count 1 /\ A ** {x} =~ A
Proof
  simp[SING_set_exp, CARDEQ_CARD_EQN] >> simp[Once cardeq_SYM] >>
  simp[cardeq_def] >> qexists `\a b. if b = x then a else ARB` >>
  qmatch_abbrev_tac `BIJ f A s` >>
  qsuff_tac `s = IMAGE f A`
  >- (rw[] >> match_mp_tac (GEN_ALL INJ_BIJ_SUBSET) >>
      map_every qexists_tac [`IMAGE f A`, `A`] >> rw[INJ_DEF, Abbr`f`]
      >- metis_tac[]
      >> (fs[FUN_EQ_THM] >> first_x_assum (qspec_then `x` mp_tac) >> simp[])) >>
  rw[Abbr`s`, Abbr`f`, EXTENSION]
QED

Theorem POW_TWO_set_exp:
  POW A =~ count 2 ** A
Proof
  simp[POW_DEF, set_exp_def, BIJ_IFF_INV, cardeq_def] >>
  qexists_tac `\s a. if a IN A then if a IN s then 1 else 0
                     else ARB` >> simp[] >> conj_tac
  >- (qx_gen_tac `s` >> strip_tac >> qx_gen_tac `b` >> strip_tac >>
      Cases_on `b IN s` >> simp[]) >>
  qexists `\f. { a | a IN A /\ f a = 1 }` >> simp[] >> rpt conj_tac
  >- simp[SUBSET_DEF]
  >- (qx_gen_tac `s` >> csimp[] >> simp[EXTENSION, SUBSET_DEF] >>
      rw[] >> rw[]) >>
  qx_gen_tac `f` >> simp[FUN_EQ_THM] >> strip_tac >> qx_gen_tac `a` >>
  Cases_on `a IN A` >> simp[] >>
  `?n. n < 2 /\ (f a = n)` by metis_tac[] >>
  rw[] >> decide_tac
QED

Theorem set_exp_count:
  A ** count n =~ { l | (LENGTH l = n) /\ !e. MEM e l ==> e IN A }
Proof
  simp[cardeq_def, BIJ_IFF_INV] >>
  qexists_tac `\f. GENLIST f n` >> simp[listTheory.MEM_GENLIST] >>
  conj_tac
  >- (qx_gen_tac `f` >> dsimp[set_exp_def] >> rpt strip_tac >> res_tac >>
      simp[]) >>
  qexists ‘λl m. if m < n then EL m l else ARB’ >> rpt conj_tac
  >- (simp[] >> qx_gen_tac `l` >> strip_tac >>
      simp[set_exp_def] >> metis_tac [listTheory.MEM_EL])
  >- (qx_gen_tac `f` >> rw[set_exp_def] >> simp[FUN_EQ_THM] >>
      qx_gen_tac `m` >> rw[] >> res_tac >> simp[]) >>
  simp[combinTheory.o_ABS_R] >> qx_gen_tac `l` >> strip_tac >>
  match_mp_tac listTheory.LIST_EQ >> simp[]
QED

Theorem set_exp_card_cong:
  (a1:'a1 set) =~ (a2:'a2 set) ==> (b1:'b1 set) =~ (b2:'b2 set) ==>
  (a1 ** b1 =~ a2 ** b2)
Proof
  rw[cardeq_def, BIJ_IFF_INV] >>
  rename [‘_ IN a1 ** b1 ==> _ IN a2 ** b2’,
          ‘_ IN a1 ==> rf1 _ IN a2’, ‘_ IN a2 ==> rf2 _ IN a1’,
          ‘_ IN b1 ==> df1 _ IN b2’, ‘_ IN b2 ==> df2 _ IN b1’] >>
  qexists ‘λf b. if b IN b2 then
                   if f (df2 b) IN a1 then rf1 $ f $ df2 b else ARB
                 else ARB’ >>
  simp[set_exp_def, FUN_EQ_THM] >>
  qexists ‘λg b. if b IN b1 then
                   if g (df1 b) IN a2 then rf2 $ g $ df1 b else ARB
                 else ARB’ >>
  simp[] >> metis_tac[]
QED

Theorem set_exp_cardle_cong:
  (b = {} ==> d = {}) ==>
  (a:'a set) <<= (b:'b set) /\ (c:'c set) <<= (d:'d set) ==>
  a ** c <<= b ** d
Proof
  simp[set_exp_def, cardleq_def] >> strip_tac >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `abf` assume_tac)
                              (qx_choose_then `cdf` assume_tac)) >>
  qexists ‘
    λcaf di. if di IN d then
               case some ci. ci IN c /\ (cdf ci = di) of
                     NONE => CHOICE b
                   | SOME ci => abf (caf ci)
             else ARB
  ’ >>
  Cases_on ‘b = {}’ >> gvs[]
  >- simp[INJ_DEF, FUN_EQ_THM] >>
  rw[INJ_DEF]
  >- (rename [‘_ IN c /\ cdf _ = di’] >>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      rpt strip_tac >- metis_tac[INJ_DEF] >>
      simp[CHOICE_DEF]) >>
  rename [‘caf1 = caf2’] >> simp[FUN_EQ_THM] >>
  qx_gen_tac ‘ci’ >> Cases_on‘ci IN c’ >> simp[] >>
  ‘cdf ci IN d’ by metis_tac[INJ_DEF] >>
  ‘(some ci'. ci' IN c /\ (cdf ci' = cdf ci)) = SOME ci’
    by (DEEP_INTRO_TAC some_intro >> simp[] >>
        metis_tac[INJ_DEF]) >>
  first_assum (fn th => Q_TAC (mp_tac o AP_THM th) ‘cdf ci’) >> BETA_TAC >>
  simp[] >> metis_tac[INJ_DEF]
QED

Theorem exp_INSERT_cardeq:
  e NOTIN s ==> (A ** (e INSERT s) =~ A CROSS A ** s)
Proof
  simp[set_exp_def, cardeq_def] >> strip_tac >> simp[BIJ_IFF_INV] >>
  qexists_tac ‘\f. (f e, (λa. if a = e then ARB else f a))’ >> conj_tac
  >- (qx_gen_tac `f` >> strip_tac >> simp[] >> metis_tac[]) >>
  qexists ‘λ(a1,f) a2. if a2 = e then a1 else f a2’ >>
  simp[pairTheory.FORALL_PROD] >> rpt conj_tac
  >- (rw[] >> rw[])
  >- (qx_gen_tac `f` >> strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `a` >>
      simp[AllCaseEqs()]) >>
  rw[FUN_EQ_THM] >> rw[]
QED

Theorem exp_count_cardeq:
  INFINITE A /\ 0 < n ==> A ** count n =~ A
Proof
  strip_tac >> Induct_on `n` >> simp[] >>
  `(n = 0) \/ ?m. n = SUC m` by (Cases_on `n` >> simp[])
  >- simp[count_EQN, SING_set_exp_CARD] >>
  simp_tac (srw_ss()) [COUNT_SUC] >>
  `A ** (n INSERT count n) =~ A CROSS A ** count n`
    by simp[exp_INSERT_cardeq] >>
  `A ** count n =~ A` by simp[] >>
  `A CROSS A ** count n =~ A CROSS A` by metis_tac[CARDEQ_CROSS, cardeq_REFL] >>
  `A CROSS A =~ A` by simp[SET_SQUARED_CARDEQ_SET] >>
  metis_tac [cardeq_TRANS]
QED

Theorem K_lemma[local]:
  (!x. f x = y) <=> f = K y
Proof
  simp[FUN_EQ_THM]
QED

Theorem finite_image_lemma[local]:
  !A. FINITE (IMAGE f A) /\ (!x y. x IN A /\ y IN A /\ f x = f y ==> x = y) ==>
      FINITE A
Proof
  Induct_on ‘FINITE’ >> simp[] >> rw[] >>
  rename [‘IMAGE f A = e0 INSERT A0’] >>
  ‘?e. e IN A /\ f e = e0’
    by (qpat_x_assum ‘IMAGE f A = _’ mp_tac >> simp[EXTENSION] >> metis_tac[])>>
  ‘IMAGE f (A DELETE e) = A0’
    by (qpat_x_assum ‘IMAGE f A = _’ mp_tac >> simp[EXTENSION] >> metis_tac[])>>
  ‘FINITE (A DELETE e)’ suffices_by simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem FINITE_setexp[simp]:
  FINITE ((A:'a set) ** (B:'b set)) <=>
  B = {} \/ A <<= {()} \/ FINITE A /\ FINITE B
Proof
  simp[set_exp_def, EQ_IMP_THM] >> rpt strip_tac >> gvs[K_lemma]
  >- (Cases_on ‘B = {}’ >> simp[] >>
      Cases_on ‘A = {}’ >> gvs[] >>
      Cases_on ‘?a. A = {a}’ >> gvs[]
      >- (simp[cardleq_def] >> disj1_tac >> qexists_tac ‘K ()’ >>
          simp[INJ_IFF]) >> disj2_tac >>
      ‘?a1 a2. a1 <> a2 /\ a1 IN A /\ a2 IN A’
        by (pop_assum mp_tac >> simp[EXTENSION] >> gs[GSYM MEMBER_NOT_EMPTY] >>
            metis_tac[]) >> conj_tac
      >- (CCONTR_TAC >>
          qpat_x_assum ‘FINITE _’ mp_tac >> simp[] >>
          ‘?b. b IN B’ by simp[MEMBER_NOT_EMPTY] >>
          qabbrev_tac ‘ff = λa b. if b IN B then a else ARB’ >>
          ‘(!a1 a2. ff a1 = ff a2 ==> a1 = a2)’
            by (simp[Abbr‘ff’, FUN_EQ_THM, AllCaseEqs()] >> metis_tac[]) >>
          drule_then (drule_then assume_tac) IMAGE_11_INFINITE >>
          qmatch_abbrev_tac ‘INFINITE s’ >>
          ‘IMAGE ff A SUBSET s’ suffices_by metis_tac[SUBSET_FINITE] >>
          simp[Abbr‘ff’, Abbr‘s’, SUBSET_DEF, PULL_EXISTS]) >>
      CCONTR_TAC >> qpat_x_assum ‘FINITE _’ mp_tac >> simp[] >>
      qabbrev_tac ‘ff = λb1 b2. if b1 NOTIN B then ARB
                                else if b2 NOTIN B then ARB
                                else if b1 = b2 then a2 else a1’ >>
      ‘(!b1 b2. b1 IN B /\ b2 IN B /\ ff b1 = ff b2 ==> b1 = b2)’
        by (simp[Abbr‘ff’, FUN_EQ_THM, SF CONJ_ss] >>
            rpt strip_tac >> CCONTR_TAC >>
            first_x_assum $ qspec_then‘b1’ mp_tac >> simp[]) >>
      drule_at (Pos last) finite_image_lemma >> simp[] >> strip_tac >>
      qmatch_abbrev_tac ‘INFINITE s’ >>
      ‘IMAGE ff B SUBSET s’ suffices_by metis_tac[SUBSET_FINITE] >>
      first_x_assum $ qspecl_then [‘ARB : 'b’, ‘ARB : 'b’] kall_tac >>
      simp[Abbr‘ff’, Abbr‘s’, SUBSET_DEF, PULL_EXISTS, AllCaseEqs()] >>
      metis_tac[])
  >- (Cases_on ‘A = {}’ >> gvs[]
      >- (csimp[K_lemma] >> Cases_on ‘!b. b NOTIN B’ >> simp[]) >>
      ‘?a. A = {a}’
        by (gs[cardleq_def, INJ_IFF, GSYM MEMBER_NOT_EMPTY] >>
            rename [‘a IN A’] >> qexists_tac ‘a’ >> simp[EXTENSION] >>
            metis_tac[]) >>
      gvs[] >> qmatch_abbrev_tac ‘FINITE s’ >>
      ‘s = {λb. if b IN B then a else ARB}’ suffices_by simp[] >>
      simp[Abbr‘s’, Once FUN_EQ_THM, AllCaseEqs(), EQ_IMP_THM] >>
      rpt strip_tac >> csimp[FUN_EQ_THM, AllCaseEqs()])
  >- (‘FINITE (A CROSS B)’ by simp[] >>
      ‘FINITE (POW (A CROSS B))’ by simp[] >>
      first_assum $ C (resolve_then (Pos hd) irule) CARDLEQ_FINITE >>
      simp[INJ_IFF, cardleq_def, IN_POW, SUBSET_DEF, FORALL_PROD] >>
      qexists_tac ‘λf. { (a,b) | b IN B /\ f b = a }’ >>
      simp[] >> rw[] >~
      [‘GSPEC _ = GSPEC _ <=> _ = _’]
      >- (simp[EXTENSION] >> simp[FUN_EQ_THM, FORALL_PROD] >>
          simp[Once EQ_IMP_THM] >> rw[] >> rename [‘f1 a = f2 a’] >>
          metis_tac[]) >>
      metis_tac[])
QED

Theorem CARD_LE_EXP:
  {T; F} <<= B ==> (A:'a set) <<= (B:'b set) ** A
Proof
  simp[cardleq_def, set_exp_def, INJ_IFF] >>
  disch_then $ qx_choose_then ‘bf’ strip_assume_tac >>
  qexists_tac ‘λa1 a2. if a1 = a2 then bf T
                       else if a2 IN A then bf F
                       else ARB’ >>
  simp[] >> rw[]
  >- rw[]
  >- metis_tac[] >>
  simp[EQ_IMP_THM] >>
  disch_then (assume_tac o SRULE[FUN_EQ_THM]) >>
  pop_assum $ qspec_then ‘x’ mp_tac >> simp[] >> rw[]
QED

val INFINITE_Unum = store_thm(
  "INFINITE_Unum",
  ``INFINITE A <=> univ(:num) <<= A``,
  simp[infinite_num_inj, cardleq_def]);

val cardleq_SURJ = store_thm(
  "cardleq_SURJ",
  ``A <<= B <=> (?f. SURJ f B A) \/ (A = {})``,
  simp[cardleq_def, EQ_IMP_THM] >>
  metis_tac [SURJ_INJ_INV, inj_surj, INJ_EMPTY]);

val INFINITE_cardleq_INSERT = store_thm(
  "INFINITE_cardleq_INSERT",
  ``INFINITE A ==> (x INSERT s <<= A <=> s <<= A)``,
  simp[cardleq_def, INJ_INSERT, EQ_IMP_THM] >> strip_tac >> conj_tac
  >- metis_tac[] >>
  disch_then (Q.X_CHOOSE_THEN `f` strip_assume_tac) >>
  Cases_on `x IN s` >- (qexists_tac `f` >> fs[INJ_DEF]) >>
  Q.UNDISCH_THEN `INFINITE A` mp_tac >>
  simp[INFINITE_Unum, cardleq_def] >>
  disch_then (Q.X_CHOOSE_THEN `g` assume_tac) >>
  qexists_tac `\y. if y = x then g 0
                   else case some n. f y = g n of
                          NONE => f y
                        | SOME m => g (m + 1)` >>
  rpt conj_tac
  >- (simp[INJ_DEF] >> conj_tac
      >- (qx_gen_tac `y` >> strip_tac >> rw[] >- fs[] >>
          Cases_on `some n. f y = g n` >> fs[INJ_DEF]) >>
      map_every qx_gen_tac [`i`, `j`] >> strip_tac >> Cases_on `i = x` >>
      Cases_on `j = x` >> simp[]
      >- (DEEP_INTRO_TAC some_intro >> simp[] >> fs[INJ_DEF])
      >- (DEEP_INTRO_TAC some_intro >> simp[] >> fs[INJ_DEF]) >>
      ntac 2 (DEEP_INTRO_TAC some_intro) >> simp[] >>
      fs[INJ_DEF] >> qx_gen_tac `m` >> strip_tac >>
      qx_gen_tac `n` >> rpt strip_tac >>
      metis_tac [DECIDE ``(n + 1 = m + 1) <=> (m = n)``])
  >- fs[INJ_DEF] >>
  qx_gen_tac `y` >> simp[] >> Cases_on `x = y` >> simp[] >>
  Cases_on `y IN s` >> simp[] >> DEEP_INTRO_TAC some_intro >>
  simp[] >> fs[INJ_DEF] >> metis_tac [DECIDE ``0 <> n + 1``])

val list_def = Define`
  list A = { l | !e. MEM e l ==> e IN A }
`;

Theorem list_EMPTY[simp]: list {} = { [] }
Proof
  simp[list_def, EXTENSION] >> Cases >> dsimp[]
QED

Theorem list_SING: list {e} =~ univ(:num)
Proof
  simp[cardeq_def] >> qexists_tac `LENGTH` >>
  simp[list_def, BIJ_IFF_INV] >>
  qexists_tac `GENLIST (K e)` >> dsimp[listTheory.MEM_GENLIST] >>
  Induct >> simp[listTheory.GENLIST_CONS]
QED

Theorem UNIV_list:
  univ(:'a list) = list (univ(:'a))
Proof simp[EXTENSION, list_def]
QED

Theorem list_BIGUNION_EXP:
  list A =~ BIGUNION (IMAGE (\n. {n} CROSS (A ** count n)) univ(:num))
Proof
  match_mp_tac cardleq_ANTISYM >> simp[cardleq_def] >> conj_tac
  >- (dsimp[INJ_DEF, list_def] >>
      qexists ‘\l. (LENGTH l, (λn. if n < LENGTH l then EL n l else ARB))’ >>
      simp[] >>
      conj_tac
      >- (qx_gen_tac `l` >> strip_tac >>
          simp[set_exp_def] >> metis_tac[listTheory.MEM_EL]) >>
      simp[FUN_EQ_THM, listTheory.LIST_EQ_REWRITE] >>
      metis_tac[DECIDE ``(x = y) <=> ~(x < y) /\ ~(y < x)``]) >>
  qexists ‘λ(n,f). GENLIST f n’ >>
  simp[INJ_DEF, set_exp_def, FORALL_PROD, PULL_EXISTS] >> conj_tac
  >- simp[list_def, listTheory.MEM_GENLIST, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  disch_then (fn th => assume_tac th >> mp_tac (Q.AP_TERM ‘LENGTH’ th)) >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  gs[listTheory.LIST_EQ_REWRITE] >> metis_tac[]
QED

Theorem CARDEQ_CROSS_1:
  {x} CROSS A =~ A /\ A CROSS {x} =~ A
Proof
  simp[cardeq_def] >> conj_tac >| [qexists ‘SND’, qexists ‘FST’] >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD]
QED

Theorem INFINITE_A_list_BIJ_A:
  INFINITE A ==> list A =~ A
Proof
  strip_tac >>
  assume_tac list_BIGUNION_EXP >>
  `BIGUNION (IMAGE (\n. {n} CROSS (A ** count n)) univ(:num)) =~ A`
    suffices_by metis_tac[cardeq_TRANS] >>
  match_mp_tac cardleq_ANTISYM >> reverse conj_tac
  >- (simp[cardleq_def] >>
      qexists_tac ‘\e. (1, λn. if n = 0 then e else ARB)’ >>
      simp[INJ_DEF, set_exp_def, PULL_EXISTS] >>
      simp[FUN_EQ_THM] >> metis_tac[]) >>
  match_mp_tac CARD_BIGUNION >> dsimp[] >> conj_tac
  >- simp[IMAGE_cardleq_rwt, GSYM INFINITE_Unum] >>
  qx_gen_tac `n` >> Cases_on `0 < n` >> fs[]
  >- metis_tac[CARDEQ_SUBSET_CARDLEQ, exp_count_cardeq, cardeq_SYM,
               CARDEQ_CROSS_1, cardeq_TRANS] >>
  simp[EMPTY_set_exp, INFINITE_cardleq_INSERT]
QED

val finite_subsets_bijection = store_thm(
  "finite_subsets_bijection",
  ``INFINITE A ==> A =~ { s | FINITE s /\ s SUBSET A }``,
  strip_tac >> match_mp_tac cardleq_ANTISYM >> conj_tac
  >- (simp[cardleq_def] >> qexists_tac `\a. {a}` >>
      simp[INJ_DEF]) >>
  `{s | FINITE s /\ s SUBSET A} <<= list A`
    suffices_by metis_tac[CARDEQ_CARDLEQ, INFINITE_A_list_BIJ_A, cardeq_REFL] >>
  simp[cardleq_SURJ] >> disj1_tac >> qexists_tac `LIST_TO_SET` >>
  simp[SURJ_DEF, list_def] >> conj_tac >- simp[SUBSET_DEF] >>
  qx_gen_tac `s` >> strip_tac >> qexists_tac `SET_TO_LIST s` >>
  simp[listTheory.SET_TO_LIST_INV] >> fs[SUBSET_DEF]);

fun qxchl qs thtac = case qs of [] => thtac
                              | q::rest => Q.X_CHOOSE_THEN q (qxchl rest thtac)


Theorem disjoint_countable_decomposition:
  !s. INFINITE s ==>
      ?A. (BIGUNION A = s) /\
          (!a. a IN A ==> INFINITE a /\ countable a) /\
          !a1 a2. a1 IN A /\ a2 IN A /\ a1 <> a2 ==> DISJOINT a1 a2
Proof
  rpt strip_tac >>
  qabbrev_tac `
    Ds = { D | BIGUNION D SUBSET s /\
               (!d. d IN D ==> INFINITE d /\ countable d) /\
               !d1 d2. d1 IN D /\ d2 IN D /\ d1 <> d2 ==> DISJOINT d1 d2}` >>
  `?f. INJ f univ(:num) s` by metis_tac [infinite_num_inj] >>
  qabbrev_tac `s_nums = IMAGE f univ(:num)` >>
  `{s_nums} IN Ds`
    by (markerLib.WITHOUT_ABBREVS (simp[]) >> simp[Abbr`s_nums`] >>
        conj_tac >- (fs[SUBSET_DEF, INJ_DEF] >> metis_tac[])>>
        fs[FINITE_IMAGE_INJ', INJ_IFF]) >>
  `Ds <> {}` by (simp[EXTENSION] >>metis_tac[]) >>
  qabbrev_tac `R = {(D1,D2) | D1 IN Ds /\ D2 IN Ds /\ D1 SUBSET D2}` >>
  `partial_order R Ds`
    by (simp[Abbr`R`, partial_order_def, domain_def, range_def, reflexive_def,
             transitive_def, antisym_def] THEN REPEAT CONJ_TAC
        THENL [
           simp[SUBSET_DEF] >> metis_tac[],
           simp[SUBSET_DEF] >> metis_tac[],
           metis_tac[SUBSET_TRANS],
           metis_tac[SUBSET_ANTISYM]
        ]) >>
  `!t. chain t R ==> upper_bounds t R <> {}`
    by (simp[Abbr`R`, upper_bounds_def, chain_def] >>
        simp[Once EXTENSION, range_def] >>
        qx_gen_tac `t` >> strip_tac >>
        qabbrev_tac `UBD =BIGUNION t` >>
        qexists_tac `UBD` >>
        `UBD IN Ds`
          by (markerLib.WITHOUT_ABBREVS (simp[]) >>
              conj_tac
              >- (simp[BIGUNION_SUBSET, Abbr`UBD`] >>
                  qx_gen_tac `s0` >>
                  disch_then (qxchl [`t0`] strip_assume_tac) >>
                  `t0 IN Ds` by metis_tac[] >> pop_assum mp_tac >>
                  markerLib.WITHOUT_ABBREVS (simp[]) >>
                  simp[BIGUNION_SUBSET]) >>
              conj_tac
              >- (qx_gen_tac `s0` >>
                  disch_then (qxchl [`t0`] strip_assume_tac) >>
                  `t0 IN Ds` by metis_tac[] >> pop_assum mp_tac >>
                  markerLib.WITHOUT_ABBREVS (simp[])) >>
              map_every qx_gen_tac [`d1`, `d2`] >>
              disch_then (CONJUNCTS_THEN2
                            (qxchl [`t1`] strip_assume_tac)
                            (CONJUNCTS_THEN2
                               (qxchl [`t2`] strip_assume_tac)
                               assume_tac)) >>
              `t1 IN Ds /\ t2 IN Ds` by metis_tac[] >>
              ntac 2 (pop_assum mp_tac) >>
              markerLib.WITHOUT_ABBREVS (simp[]) >>
              simp[BIGUNION_SUBSET] >>
              `t1 SUBSET t2 \/ t2 SUBSET t1` suffices_by
                 metis_tac[SUBSET_DEF] >>
              metis_tac[]) >>
        simp[] >> conj_tac >- (qexists_tac `UBD` >> simp[]) >>
        qx_gen_tac `t0` >> Cases_on `t0 IN t` >> simp[] >>
        `t0 IN Ds` by metis_tac[] >> simp[] >>
        pop_assum mp_tac >> markerLib.WITHOUT_ABBREVS (simp[]) >>
        simp[Abbr`UBD`, BIGUNION_SUBSET] >> strip_tac >>
        simp[SUBSET_DEF] >> metis_tac[]) >>
  `?M. M IN maximal_elements Ds R` by metis_tac [zorns_lemma] >>
  pop_assum mp_tac >> simp[maximal_elements_def] >> strip_tac >>
  Q.UNDISCH_THEN `M IN Ds` (fn th => mp_tac th >> assume_tac th) >>
  markerLib.WITHOUT_ABBREVS (simp_tac (srw_ss()) []) >> strip_tac >>
  Cases_on `BIGUNION M = s` >- metis_tac[] >>
  `M <> {}`
    by (strip_tac >>
        `(M,{s_nums}) IN R` by (simp[Abbr`R`] >> fs[]) >>
        `M = {s_nums}` by metis_tac[] >> fs[]) >>
  Cases_on `FINITE (s DIFF BIGUNION M)`
  >- (`?M0. M0 IN M` by metis_tac [IN_INSERT, SET_CASES] >>
      qexists_tac `(M0 UNION (s DIFF BIGUNION M)) INSERT (M DELETE M0)` >>
      dsimp[finite_countable] >> rpt strip_tac >| [
        simp[Once EXTENSION] >> qx_gen_tac `e` >> eq_tac
        >- (strip_tac >> fs[BIGUNION_SUBSET] >>
            metis_tac [SUBSET_DEF]) >>
        simp[] >> Cases_on `e IN M0` >> simp[] >>
        Cases_on `e IN BIGUNION M` >> pop_assum mp_tac >> simp[] >>
        metis_tac[],
        `a2 SUBSET BIGUNION M` by (simp[SUBSET_DEF] >> metis_tac[]) >>
        simp[DISJOINT_DEF, EXTENSION] >> qx_gen_tac `e` >>
        Cases_on `e IN s` >> simp[] >> Cases_on `e IN a2` >> simp[] >>
        `e IN BIGUNION M` by metis_tac[SUBSET_DEF] >>
        fs[] >> metis_tac[],
        `a1 SUBSET BIGUNION M` by (simp[SUBSET_DEF] >> metis_tac[]) >>
        simp[DISJOINT_DEF, EXTENSION] >> qx_gen_tac `e` >>
        Cases_on `e IN s` >> simp[] >> Cases_on `e IN a1` >> simp[] >>
        `e IN BIGUNION M` by metis_tac[SUBSET_DEF] >>
        fs[] >> metis_tac[]
      ]) >>
  qabbrev_tac `M0 = s DIFF BIGUNION M` >>
  `?g. INJ g univ(:num) M0` by metis_tac[infinite_num_inj] >>
  qabbrev_tac`g_nums = IMAGE g univ(:num)` >>
  `INFINITE g_nums /\ countable g_nums`
    by (simp[Abbr`g_nums`] >> fs[FINITE_IMAGE_INJ', INJ_IFF]) >>
  qabbrev_tac `M' = g_nums INSERT M` >>
  `g_nums SUBSET M0` by (simp[Abbr`g_nums`, SUBSET_DEF] >>
                    full_simp_tac(srw_ss() ++ DNF_ss)[INJ_DEF]) >>
  `M' IN Ds`
    by (markerLib.WITHOUT_ABBREVS(simp[]) >> dsimp[] >>
        `M0 SUBSET s` by simp[Abbr`M0`] >>
        `g_nums SUBSET s` by metis_tac[SUBSET_TRANS] >> simp[] >>
        qmatch_abbrev_tac `PP /\ QQ` >>
        `PP` suffices_by metis_tac[DISJOINT_SYM] >>
        map_every markerLib.UNABBREV_TAC ["PP", "QQ"] >>
        qx_gen_tac `d2` >> strip_tac >> simp[DISJOINT_DEF, EXTENSION] >>
        qx_gen_tac `e` >> SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
        `e IN M0 /\ e IN BIGUNION M` by metis_tac[IN_BIGUNION, SUBSET_DEF] >>
        metis_tac[IN_DIFF]) >>
  `(M,M') IN R` by simp[Abbr`R`, Abbr`M'`, SUBSET_DEF] >>
  `M = M'` by metis_tac[] >>
  `g_nums NOTIN M` suffices_by metis_tac[IN_INSERT] >> strip_tac >>
  `g_nums SUBSET BIGUNION M` by (simp[SUBSET_DEF] >> metis_tac[]) >>
  `g 0 IN g_nums` by simp[Abbr`g_nums`] >>
  metis_tac[IN_DIFF, SUBSET_DEF]
QED

(* this proof inspired by one generated by DeepSeek in early January, 2025;
   original query was
     "prove that every infinite set can be partitioned into sets that are
      countably infinite"

   natural language proof was pretty good, though it wanted to first well-
   order the infinite set (s), which is unnecessary given that you separately
   establish the bijection with s CROSS univ(:num).

   I then asked it to render the proof in HOL4, which it did something along
   the lines of below.  It invented plenty of theorem names. I've retained its
   comments.  It's less than half the size of the one above that explicitly
   uses Zorn's Lemma.
*)
Theorem disjoint_countable_decomposition2:
  !s. INFINITE s ==>
      ?A. (BIGUNION A = s) /\
          (!a. a IN A ==> INFINITE a /\ countable a) /\
          pairwise (RC DISJOINT) A
Proof
  rpt strip_tac >>

  (* Step 1: Establish cardinal equivalence |A| = |A × ℕ|                 UOK *)
  ‘s =~ s CROSS univ(:num)’ by (
    irule cardleq_ANTISYM >> conj_tac >~
    [‘s <<= s CROSS univ(:num)’]
    >- (simp[cardleq_def] >> qexists_tac ‘\a. (a,0)’ >>
        simp[INJ_DEF]) >>
    ‘s CROSS univ(:num) <<= univ(:num) CROSS s’
      by (simp[cardleq_def] >> qexists_tac ‘λ(a,b). (b,a)’ >>
          simp[INJ_DEF, FORALL_PROD]) >>
    drule_then irule cardleq_TRANS >>
    irule CARD_MUL_ABSORB_LE >>
    metis_tac[INFINITE_Unum]
  ) >>

  (* Step 2: Construct bijection *)
  qabbrev_tac ‘f = @f. BIJ f s (s CROSS univ(:num))’ >>
  ‘BIJ f s (s CROSS UNIV)’ by (
    simp[Abbr‘f’] >> SELECT_ELIM_TAC >>
    metis_tac[cardeq_def]
  ) >>

  (* Step 3: Define partition as fibers *)
  qabbrev_tac ‘P = IMAGE (\a. {b | b IN s /\ ?n. f b = (a,n)}) s’ >>

  (* Verification *)
  ‘BIGUNION P = s’ by (
    simp[Abbr`P`, Once EXTENSION, PULL_EXISTS, FORALL_PROD, EQ_IMP_THM] >>
    gvs[BIJ_DEF, FORALL_PROD, INJ_IFF, SURJ_DEF] >>
    metis_tac[pair_CASES, FST, PAIR]
  ) >>
  ‘pairwise (RC DISJOINT) P’ by (
    simp[Abbr‘P’, pairwise_def, PULL_EXISTS, relationTheory.RC_DEF] >>
    rw[] >> CCONTR_TAC >> gvs[DISJOINT_DEF, GSYM MEMBER_NOT_EMPTY]
  ) >>
  ‘!X. X IN P ==> INFINITE X /\ countable X’ by (
    simp[Abbr`P`] >> rw[] >~
    [‘INFINITE { b | b IN s /\ ?n. f b = (a,n) }(* g *)’]
    >- (
      drule_then (qx_choose_then ‘g’ strip_assume_tac) BIJ_INV >>
      gvs[FORALL_PROD] >>
      simp[infinite_num_inj] >> qexists_tac ‘λn. g (a,n)’ >>
      simp[INJ_DEF] >> gvs[BIJ_DEF, INJ_IFF]
    ) >>
    simp[countable_def] >> qexists_tac ‘SND o f’ >>
    gvs[INJ_IFF, BIJ_DEF, PULL_EXISTS, EQ_IMP_THM, SF CONJ_ss]
  ) >>
  metis_tac[]
QED

val count_cardle = Q.store_thm(
  "count_cardle[simp]",
  ‘count n <<= A <=> (FINITE A ==> n <= CARD A)’,
  simp[cardleq_def] >> Cases_on ‘FINITE A’ >> simp[]
  >- (eq_tac
      >- metis_tac[DECIDE “x:num <= y <=> ~(y < x)”, PHP, CARD_COUNT,
                   FINITE_COUNT] >>
      metis_tac[FINITE_COUNT, CARDLEQ_CARD, cardleq_def, CARD_COUNT]) >>
  pop_assum mp_tac >> qid_spec_tac ‘A’ >> Induct_on ‘n’ >>
  simp[] >> rpt strip_tac >> simp[COUNT_SUC, INJ_INSERT] >>
  first_x_assum (drule_then strip_assume_tac) >>
  ‘?a. a IN A /\ !m. m < n ==> f m <> a’
     by (‘?a. a IN (A DIFF IMAGE f (count n))’
           suffices_by (simp[] >> metis_tac[]) >>
         irule INFINITE_INHAB >>
         metis_tac [IMAGE_FINITE, FINITE_COUNT, FINITE_DIFF_down]) >>
  qexists_tac ‘\m. if m < n then f m else a’ >> simp[] >> conj_tac
  >- fs[INJ_DEF] >>
  rw[])

Theorem CANTOR[simp]:
  A <</= POW A
Proof
  strip_tac >> fs[cardleq_def, INJ_IFF, IN_POW] >>
  qabbrev_tac ‘CS = {f s | s | s SUBSET A /\ f s NOTIN s}’ >>
  ‘!s. s IN CS <=> ?t. t SUBSET A /\ f t NOTIN t /\ (f t = s)’
    by (simp[Abbr`CS`] >> metis_tac[]) >>
  ‘CS SUBSET A’ by (simp[Abbr`CS`] >> ONCE_REWRITE_TAC[SUBSET_DEF] >>
                    simp[PULL_EXISTS]) >>
  irule (DECIDE “(p ==> ~p) /\ (~p ==> p) ==> Q”) >>
  qexists_tac ‘f CS IN CS’ >> conj_tac >> strip_tac >>
  qpat_x_assum ‘!s. s IN CS <=> P’ (fn th => REWRITE_TAC [th]) >>
  csimp[] >> simp[] >> metis_tac[]
QED

val cardlt_cardle = Q.store_thm(
  "cardlt_cardle",
  ‘A <</= B ==> A <<= B’,
  metis_tac[cardlt_lenoteq]);

Theorem set_exp_product:
  (A ** B1) ** B2 =~ A ** (B1 CROSS B2)
Proof
  simp[cardeq_def] >>
  qexists ‘\cf bp. if bp IN B1 CROSS B2 then cf (SND bp) (FST bp) else ARB’ >>
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF, set_exp_def, FORALL_PROD] >>
  rpt strip_tac >> simp[]
  >- (simp[FUN_EQ_THM, FORALL_PROD] >> iff_tac >> simp[] >> metis_tac[]) >>
  rename [‘uf (_,_) IN A’] >>
  qexists ‘\b2. if b2 IN B2 then
                  \b1. if b1 IN B1 then uf(b1,b2) else ARB
                else ARB’ >> simp[] >>
  simp[FUN_EQ_THM, FORALL_PROD] >> metis_tac[]
QED

Theorem CARD1_SING:
  (A:'a set) =~ {()} <=> ?a. A = {a}
Proof
  simp[cardeq_def, EQ_IMP_THM, PULL_EXISTS, BIJ_IFF_INV] >>
  rpt strip_tac
  >- (rename [‘g () IN A’] >> qexists_tac ‘g()’ >> simp[EXTENSION] >>
      metis_tac[]) >>
  qexists_tac ‘K a’ >> simp[]
QED

Theorem cardleq_setexp:
  x <<= x ** e <=> x = {} \/ x =~ {()} \/ e <> {}
Proof
  Cases_on ‘x = {}’ >> simp[] >>
  Cases_on ‘e = {}’ >> simp[EMPTY_set_exp, CARD1_SING]
  >- (simp[INJ_IFF, EQ_IMP_THM, PULL_EXISTS] >> reverse (rpt strip_tac)
      >- (simp[INJ_IFF, cardleq_def] >> qexists_tac ‘λa. K ARB’ >> simp[]) >>
      gs[cardleq_def, INJ_IFF, GSYM MEMBER_NOT_EMPTY] >> simp[EXTENSION] >>
      metis_tac[]) >>
  simp[cardleq_def, INJ_IFF] >> gs[GSYM MEMBER_NOT_EMPTY] >>
  rename [‘X ** E’, ‘x IN X’, ‘e IN E’] >>
  qexists ‘λx0 e0. if e0 IN E then x0 else ARB’ >>
  simp[set_exp_def, FUN_EQ_THM] >> metis_tac[]
QED

val POW_EQ_X_EXP_X = Q.store_thm(
  "POW_EQ_X_EXP_X",
  ‘INFINITE A ==> POW A =~ A ** A’,
  strip_tac >> irule cardleq_ANTISYM >> conj_tac
  >- (‘POW A =~ count 2 ** A’ by simp[POW_TWO_set_exp] >>
      ‘count 2 ** A <<= A ** A’
        suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
      irule set_exp_cardle_cong >> simp[]) >>
  ‘POW A =~ count 2 ** A’ by simp[POW_TWO_set_exp] >>
  ‘A ** A <<= count 2 ** A’
    suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
  ‘A <</= POW A’ by simp[] >>
  ‘A <<= POW A’ by simp[cardlt_cardle] >>
  ‘A ** A <<= POW A ** A’
    by metis_tac[set_exp_cardle_cong, cardleq_REFL, POW_EMPTY] >>
  ‘POW A ** A <<= count 2 ** A’ suffices_by metis_tac [cardleq_TRANS] >>
  ‘(count 2 ** A) ** A <<= count 2 ** A’
    suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL, set_exp_card_cong] >>
  ‘count 2 ** (A CROSS A) <<= count 2 ** A’
    suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL, set_exp_product] >>
  irule set_exp_cardle_cong >> simp[] >> irule CARDEQ_SUBSET_CARDLEQ >>
  simp[SET_SQUARED_CARDEQ_SET]);

Theorem setexp_eq_EMPTY[simp]:
  A ** B = {} <=> A = {} /\ B <> {}
Proof
  simp[set_exp_def] >> simp[SimpLHS, EXTENSION] >>
  simp[] >> eq_tac >> rpt strip_tac
  >- (Cases_on ‘B = {}’ >> gvs[]
      >- (pop_assum $ qspec_then ‘K ARB’ mp_tac >> simp[]) >>
      CCONTR_TAC >> gs[GSYM MEMBER_NOT_EMPTY] >>
      rename [‘_ IN B /\ _ NOTIN A’, ‘b IN B’, ‘a IN A’] >>
      first_x_assum $ qspec_then ‘λb0. if b0 IN B then a else ARB’ mp_tac>>
      csimp[] >> metis_tac[])
  >- (gvs[] >> pop_assum $ qspec_then ‘K ARB’ mp_tac >> simp[]) >>
  simp[] >> metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem FINITE_EXPONENT_SETEXP_UNCOUNTABLE:
  FINITE B /\ B <> {} /\ ~countable A ==>
  ~countable (A ** B)
Proof
  Induct_on ‘FINITE’ >> simp[] >> rpt strip_tac >>
  rename [‘A ** (e INSERT B) ’] >>
  ‘A ** (e INSERT B) =~ A CROSS (A ** B)’
    by simp[exp_INSERT_cardeq] >>
  drule_all (iffLR countable_cardeq) >> simp[cross_countable_IFF] >>
  rpt strip_tac >> gvs[CARDEQ_0, setexp_eq_EMPTY]
QED

Theorem FINITE_EXPONENT_SETEXP_COUNTABLE:
  FINITE (B:'b set) ==>
  (countable ((A:'a set) ** B) <=> B = {} \/ countable A)
Proof
  simp[EQ_IMP_THM, IMP_CONJ_THM] >> conj_tac
  >- metis_tac[FINITE_EXPONENT_SETEXP_UNCOUNTABLE] >>
  ‘!(A:'a set) (B:'b set). FINITE B /\ countable A ==> countable (A ** B)’
    suffices_by (rw[] >> simp[EMPTY_set_exp]) >>
  Induct_on ‘FINITE’ >> simp[EMPTY_set_exp] >> rpt strip_tac >>
  ‘A ** (e INSERT B) =~ A CROSS (A ** B)’ by simp[exp_INSERT_cardeq] >>
  drule_then irule (iffRL countable_cardeq) >> simp[cross_countable_IFF]
QED

Theorem FINITE_012:
  FINITE A ==> A = {} \/ A =~ {()} \/ 2 <= CARD A
Proof
  Induct_on ‘FINITE’ >> simp[] >> rw[] >> gvs[CARD1_SING]
QED

(* cf. permutesTheory.permutes_alt_bijns *)
Definition bijns_def:
  bijns A = { f | BIJ f A A /\ !a. a NOTIN A ==> f a = a }
End

Theorem bijns_alt_permutes:
    !f s. f IN bijns s <=> f permutes s
Proof
  simp[permutes_alt, bijns_def]
QED

Theorem cardeq_bijns_cong:
  A =~ B ==> bijns A =~ bijns B
Proof
  strip_tac >> ONCE_REWRITE_TAC [cardeq_SYM] >>
  fs[cardeq_def, bijns_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [BIJ_IFF_INV]) >> fs[] >>
  qexists ‘\bf a. if a IN A then g (bf (f a)) else a’ >>
  ‘!a1 a2. a1 IN A /\ a2 IN A ==> (f a1 = f a2 <=> a1 = a2)’ by metis_tac[] >>
  ‘!b1 b2. b1 IN B /\ b2 IN B ==> (g b1 = g b2 <=> b1 = b2)’ by metis_tac[] >>
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> rpt strip_tac >> csimp[]
  >- metis_tac[]
  >- (simp[EQ_IMP_THM, FUN_EQ_THM] >> rw[] >>
      rename [‘bf1 b = bf2 b’] >> reverse (Cases_on ‘b IN B’) >> simp[] >>
      ‘b = f (g b)’ by metis_tac[] >> pop_assum SUBST1_TAC >>
      ‘g b IN A’ by metis_tac[] >> first_x_assum (qspec_then ‘g b’ mp_tac) >>
      simp[])
  >- metis_tac[]
  >- (simp[PULL_EXISTS] >> csimp[] >>
      rename [‘(ff:'a -> 'a) _ = ff _ <=> _’] >>
      qexists ‘\b. if b IN B then f (ff (g b)) else b’ >>
      simp[] >> rpt strip_tac >> csimp[] >> metis_tac[] >>
      simp[FUN_EQ_THM] >> metis_tac[])
QED

Theorem bijections_cardeq:
  INFINITE s ==> bijns s =~ POW s
Proof
  strip_tac >>
  irule cardleq_ANTISYM >> conj_tac
  >- (‘POW s =~ s ** s’ by simp[POW_EQ_X_EXP_X] >>
      ‘bijns s <<= s ** s’ suffices_by metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
      simp[cardleq_def] >>
      simp[bijns_def, BIJ_DEF, INJ_IFF, set_exp_def] >>
      qexists ‘λf x. if x IN s then f x else ARB’ >> simp[] >>
      rpt strip_tac >> simp[FUN_EQ_THM] >> metis_tac[]) >>
  ‘s =~ {T;F} CROSS s’ by simp[SET_SUM_CARDEQ_SET] >>
  ‘bijns s =~ bijns ({T;F} CROSS s)’ by metis_tac[cardeq_bijns_cong] >>
  ‘POW s <<= bijns ({T;F} CROSS s)’
    suffices_by metis_tac[CARDEQ_CARDLEQ,cardeq_REFL] >>
  simp[cardleq_def] >>
  qexists_tac ‘\ss (bool,a). if a IN s then if a IN ss then (bool,a)
                                            else (~bool,a)
                             else (bool,a)’ >>
  simp[INJ_IFF, IN_POW, bijns_def, FORALL_PROD] >> rpt strip_tac
  >- (simp[BIJ_DEF, INJ_IFF, SURJ_DEF, FORALL_PROD] >> rpt strip_tac
      >- rw[]
      >- (rw[] >> metis_tac[])
      >- rw[] >>
      simp[pairTheory.EXISTS_PROD] >> csimp[] >>
      dsimp[AllCaseEqs()] >> metis_tac[]) >>
  simp[SimpLHS,FUN_EQ_THM] >> iff_tac >> rw[] >>
  simp[EXTENSION] >> qx_gen_tac `a` >> reverse (Cases_on `a IN s`)
  >- metis_tac[SUBSET_DEF] >>
  rename [‘a IN ss1 <=> a IN ss2’] >>
  Cases_on `a IN ss1` >> simp[]
  >- (first_x_assum (qspecl_then [‘T’, ‘a’] mp_tac) >> simp[] >> rw[])
  >- (first_x_assum (qspecl_then [‘F’, ‘a’] mp_tac) >> simp[] >> rw[])
QED

(* ------------------------------------------------------------------------- *)
(* misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem FORALL_IN_GSPEC :
   (!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>
          (!x y. P x y ==> Q(f x y))) /\
   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>
          (!w x y. P w x y ==> Q(f w x y)))
Proof
   SRW_TAC [][] THEN SET_TAC []
QED

Theorem EXISTS_IN_GSPEC :
   (!P f. (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P f. (?z. z IN {f x y | P x y} /\ Q z) <=>
          (?x y. P x y /\ Q(f x y))) /\
   (!P f. (?z. z IN {f w x y | P w x y} /\ Q z) <=>
          (?w x y. P w x y /\ Q(f w x y)))
Proof
  SRW_TAC [][] THEN SET_TAC []
QED

val LEFT_IMP_EXISTS_THM = store_thm ("LEFT_IMP_EXISTS_THM",
 ``!P Q. (?x. P x) ==> Q <=> (!x. P x ==> Q)``,
 SIMP_TAC std_ss [PULL_EXISTS]);

val LEFT_IMP_FORALL_THM = store_thm ("LEFT_IMP_FORALL_THM",
 ``!P Q. (!x. P x) ==> Q <=> (?x. P x ==> Q)``,
  METIS_TAC [GSYM LEFT_FORALL_IMP_THM]);

val RIGHT_IMP_EXISTS_THM = store_thm ("RIGHT_IMP_EXISTS_THM",
 ``!P Q. P ==> (?x. Q x) <=> (?x. P ==> Q x)``,
 REWRITE_TAC [GSYM RIGHT_EXISTS_IMP_THM]);

val RIGHT_IMP_FORALL_THM = store_thm ("RIGHT_IMP_FORALL_THM",
 ``!P Q. P ==> (!x. Q x) <=> (!x. P ==> Q x)``,
 REWRITE_TAC [GSYM RIGHT_FORALL_IMP_THM]);

(* old name IMP_CONJ seems to be a conv function *)
Theorem CONJ_EQ_IMP :
    !p q r. p /\ q ==> r <=> p ==> q ==> r
Proof
    REWRITE_TAC [AND_IMP_INTRO]
QED

Theorem IMP_CONJ_ALT :
    !p q r. p /\ q ==> r <=> q ==> p ==> r
Proof
    METIS_TAC [AND_IMP_INTRO]
QED

val lemma = prove (
  ``(!x. x IN s ==> (g(f(x)) = x)) <=>
    (!y x. x IN s /\ (y = f x) ==> (g y = x))``,
 MESON_TAC []);

val INJECTIVE_ON_LEFT_INVERSE = store_thm
  ("INJECTIVE_ON_LEFT_INVERSE",
 ``!f s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))``,
  REWRITE_TAC[lemma] THEN SIMP_TAC std_ss [GSYM SKOLEM_THM] THEN METIS_TAC[]);

val SURJECTIVE_ON_RIGHT_INVERSE = store_thm
  ("SURJECTIVE_ON_RIGHT_INVERSE",
 ``!f t. (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
   (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))``,
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]);

val SURJECTIVE_RIGHT_INVERSE = store_thm
  ("SURJECTIVE_RIGHT_INVERSE",
 ``(!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)``,
  MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE, IN_UNIV]);

val FINITE_IMAGE_INJ_GENERAL = store_thm ("FINITE_IMAGE_INJ_GENERAL",
 ``!(f:'a->'b) A s.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
        FINITE A
        ==> (FINITE {x | x IN s /\ f(x) IN A})``,
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [INJECTIVE_ON_LEFT_INVERSE] THEN ASSUME_TAC SUBSET_FINITE
  THEN POP_ASSUM (MP_TAC o Q.SPEC `IMAGE (g:'b->'a) A`) THEN
  KNOW_TAC ``FINITE (IMAGE g A)`` THENL [METIS_TAC [IMAGE_FINITE], DISCH_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
  POP_ASSUM (MP_TAC o Q.SPEC `{x | x IN s /\ f x IN A}`) THEN DISCH_TAC
  THEN KNOW_TAC ``{x | x IN s /\ f x IN A} SUBSET IMAGE g A`` THENL
  [REWRITE_TAC [IMAGE_DEF, SUBSET_DEF] THEN GEN_TAC THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [] , METIS_TAC []]]);

val FINITE_IMAGE_INJ = store_thm ("FINITE_IMAGE_INJ",
 ``!(f:'a->'b) A. (!x y. (f(x) = f(y)) ==> (x = y)) /\
                FINITE A ==> FINITE {x | f(x) IN A}``,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [``f:'a->'b``, ``A:'b->bool``, ``UNIV:'a->bool``]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);

Theorem INFINITE_IMAGE_INJ:
 !f:'a->'b. (!x y. (f x = f y) ==> (x = y)) ==>
            !s. INFINITE s ==> INFINITE(IMAGE f s)
Proof
  metis_tac[FINITE_IMAGE_INJ_EQ]
QED

Theorem INFINITE_NONEMPTY:
  !s. INFINITE(s) ==> ~(s = EMPTY)
Proof MESON_TAC[FINITE_EMPTY]
QED

val SURJECTIVE_IMAGE_THM = store_thm ("SURJECTIVE_IMAGE_THM",
 ``!f:'a->'b. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})``,
  GEN_TAC THEN SIMP_TAC std_ss [EXTENSION, IN_IMAGE, GSPECIFICATION] THEN
  EQ_TAC THENL [ALL_TAC, DISCH_THEN(MP_TAC o SPEC ``\y:'b. T``)] THEN
  METIS_TAC[]);

val SURJECTIVE_ON_IMAGE = store_thm ("SURJECTIVE_ON_IMAGE",
 ``!f:'a->'b u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ (IMAGE f s = t)) <=>
        (!y. y IN v ==> ?x. x IN u /\ (f x = y))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC ``y:'b`` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``{y:'b}``) THEN ASM_SET_TAC[],
    DISCH_TAC THEN X_GEN_TAC ``t:'b->bool`` THEN DISCH_TAC THEN
    EXISTS_TAC ``{x | x IN u /\ (f:'a->'b) x IN t}`` THEN ASM_SET_TAC[]]);;

val SURJECTIVE_IMAGE = store_thm ("SURJECTIVE_IMAGE",
 ``!f:'a->'b. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)``,
  GEN_TAC THEN
  MP_TAC (ISPECL [``f:'a->'b``,``univ(:'a)``,``univ(:'b)``] SURJECTIVE_ON_IMAGE) THEN
  SIMP_TAC std_ss [IN_UNIV, SUBSET_UNIV]);

val CARD_LE_INJ = store_thm ("CARD_LE_INJ",
 ``!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:'a->'b. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)``,
  REWRITE_TAC[CONJ_EQ_IMP] THEN SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [METIS []
    ``!s. (!t. FINITE t ==> CARD s <= CARD t ==>
    ?f. IMAGE (f:'a->'b) s SUBSET t /\
      !x. x IN s ==> !y. y IN s ==> (f x = f y) ==> (x = y)) =
     (\s. (!t. FINITE t ==> CARD s <= CARD t ==>
    ?f. IMAGE (f:'a->'b) s SUBSET t /\
      !x. x IN s ==> !y. y IN s ==> (f x = f y) ==> (x = y))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [IMAGE_EMPTY, IMAGE_INSERT, EMPTY_SUBSET, NOT_IN_EMPTY] THEN
  SIMP_TAC std_ss [CARD_EMPTY, CARD_INSERT] THEN
  SIMP_TAC std_ss [RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [``s:'a->bool``, ``x:'a``] THEN
  SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC [METIS []
   ``!t. (SUC (CARD s) <= CARD t ==>
  ?f. f x INSERT IMAGE (f:'a->'b) s SUBSET t /\
    !x'. x' IN x INSERT s ==>
      !y. y IN x INSERT s ==> (f x' = f y) ==> (x' = y)) =
     (\t. SUC (CARD s) <= CARD t ==>
  ?f. f x INSERT IMAGE (f:'a->'b) s SUBSET t /\
    !x'. x' IN x INSERT s ==>
      !y. y IN x INSERT s ==> (f x' = f y) ==> (x' = y)) t``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [CARD_EMPTY, CARD_INSERT, LE, NOT_SUC] THEN
  SIMP_TAC std_ss [RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [``t:'b->bool``, ``y:'b``] THEN
  SIMP_TAC std_ss [CARD_EMPTY, CARD_INSERT] THEN
  STRIP_TAC THEN POP_ASSUM K_TAC THEN DISCH_TAC THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``t:'b->bool``) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``\z:'a. if z = x then (y:'b) else f(z)`` THEN
  SIMP_TAC std_ss [IN_INSERT, SUBSET_DEF, IN_IMAGE] THEN
  METIS_TAC[SUBSET_DEF, IN_IMAGE]);

val CARD_EQ_BIJECTION = store_thm ("CARD_EQ_BIJECTION",
 ``!s t. FINITE s /\ FINITE t /\ (CARD s = CARD t)
   ==> ?f:'a->'b. (!x. x IN s ==> f(x) IN t) /\
                  (!y. y IN t ==> ?x. x IN s /\ (f x = y)) /\
                  !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)``,
  MP_TAC CARD_LE_INJ THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  POP_ASSUM (MP_TAC o SPECL [``s:'a->bool``,``t:'b->bool``]) THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LESS_EQ_REFL] THEN DISCH_THEN (X_CHOOSE_TAC ``f:'a->'b``) THEN
  EXISTS_TAC ``f:'a->'b`` THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC std_ss [SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  MESON_TAC[SUBSET_DEF, IN_IMAGE]);

val CARD_EQ_BIJECTIONS = store_thm ("CARD_EQ_BIJECTIONS",
 ``!s t. FINITE s /\ FINITE t /\ (CARD s = CARD t)
   ==> ?f:'a->'b g. (!x. x IN s ==> f(x) IN t /\ (g(f x) = x)) /\
                    (!y. y IN t ==> g(y) IN s /\ (f(g y) = y))``,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  DISCH_THEN (X_CHOOSE_TAC ``f:'a->'b``) THEN
  EXISTS_TAC ``f:'a->'b`` THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [SURJECTIVE_ON_RIGHT_INVERSE] THEN
  SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
  METIS_TAC[]);

val SING_SUBSET = store_thm ("SING_SUBSET",
 ``!s x. {x} SUBSET s <=> x IN s``,
  SET_TAC[]);

val INJECTIVE_ON_IMAGE = store_thm ("INJECTIVE_ON_IMAGE",
 ``!f:'a->'b u. (!s t. s SUBSET u /\ t SUBSET u /\
                (IMAGE f s = IMAGE f t) ==> (s = t)) <=>
      (!x y. x IN u /\ y IN u /\ (f x = f y) ==> (x = y))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC, SET_TAC[]] THEN MAP_EVERY X_GEN_TAC [``x:'a``, ``y:'a``] THEN
   STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [``{x:'a}``, ``{y:'a}``]) THEN
   ASM_REWRITE_TAC[SING_SUBSET, IMAGE_EMPTY, IMAGE_INSERT] THEN SET_TAC[]);

val INJECTIVE_IMAGE = store_thm ("INJECTIVE_IMAGE",
 ``!f:'a->'b. (!s t. (IMAGE f s = IMAGE f t) ==> (s = t)) <=>
              (!x y. (f x = f y) ==> (x = y))``,
  GEN_TAC THEN MP_TAC(ISPECL [``f:'a->'b``, ``univ(:'a)``] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV, SUBSET_UNIV]);

Theorem FINITE_FINITE_BIGUNION[local]:
 !s. FINITE(s) ==> (FINITE(BIGUNION s) <=> (!t. t IN s ==> FINITE(t)))
Proof
  metis_tac[FINITE_BIGUNION_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

val lemma = SET_RULE ``!a s. a IN s ==> (s = a INSERT (s DELETE a))``;

val HAS_SIZE_CLAUSES = store_thm ("HAS_SIZE_CLAUSES",
 ``!s. (s HAS_SIZE 0 <=> (s = {})) /\
       (s HAS_SIZE (SUC n) <=>
        ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))``,
  REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC, GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[lemma, IN_DELETE],
    SIMP_TAC std_ss [LEFT_IMP_EXISTS_THM, HAS_SIZE, CARD_EMPTY, CARD_INSERT,
     FINITE_INSERT]]);

val CARD_SUBSET_EQ = store_thm ("CARD_SUBSET_EQ",
 ``!(a:'a->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [``a:'a->bool``] CARD_UNION) THEN
  SUBGOAL_THEN ``FINITE(a:'a->bool)`` ASSUME_TAC THENL
   [METIS_TAC[SUBSET_FINITE_I], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPEC ``b DIFF (a:'a->bool)``) THEN
  SUBGOAL_THEN ``FINITE(b:'a->bool DIFF a)`` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_FINITE_I THEN EXISTS_TAC ``b:'a->bool`` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN ``a:'a->bool INTER (b DIFF a) = EMPTY`` ASSUME_TAC THENL
   [SET_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN ``a UNION (b:'a->bool DIFF a) = b`` ASSUME_TAC THENL
   [UNDISCH_TAC ``a:'a->bool SUBSET b`` THEN SET_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_PROVE ``(a = a + b) <=> (b = 0:num)``] THEN DISCH_TAC THEN
  SUBGOAL_THEN ``b:'a->bool DIFF a = EMPTY`` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
    FULL_SIMP_TAC std_ss [HAS_SIZE, CARD_EMPTY],
    UNDISCH_TAC ``a:'a->bool SUBSET b`` THEN SET_TAC[]]);

Theorem CARD_BIGUNION_LE:
 !s t:'a->'b->bool m n.
   s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n) ==>
   CARD(BIGUNION {t(x) | x IN s}) <= m * n
Proof
  REWRITE_TAC[HAS_SIZE] >> Induct_on ‘FINITE’ >> simp[] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] >>
  rw[DISJ_IMP_THM, FORALL_AND_THM,
     SET_RULE “BIGUNION {t x | x = a \/ x IN s} =
               t(a) UNION BIGUNION {t x | x IN s}”] >>
  MATCH_MP_TAC LESS_EQ_TRANS >>
  EXISTS_TAC
   “CARD((t:'a->'b->bool) e) + CARD(BIGUNION {(t:'a->'b->bool) x | x IN s})” >>
  CONJ_TAC >| [
    MATCH_MP_TAC CARD_UNION_LE >> ASM_SIMP_TAC std_ss [IN_INSERT] >>
    REWRITE_TAC[SET_RULE ``{t x | x IN s} = IMAGE t s``] >>
    ASM_SIMP_TAC std_ss [FINITE_FINITE_BIGUNION, IMAGE_FINITE, FORALL_IN_IMAGE,
                 IN_INSERT],
    REWRITE_TAC [ADD1] >>
    irule(ARITH_PROVE “a <= n /\ b <= x * n ==> a + b <= n * (x + 1:num)”) >>
    ASM_SIMP_TAC arith_ss [IN_INSERT]
  ]
QED

(* ----------------------------------------------------------------------
    Cardinality of type bool
   ---------------------------------------------------------------------- *)

(* simplifier gets all of these because it turns univ(:bool) into {T;F} *)

Theorem HAS_SIZE_BOOL: univ(:bool) HAS_SIZE 2
Proof simp[HAS_SIZE]
QED

Theorem CARD_BOOL[simp]:
  CARD univ(:bool) = 2
Proof simp[]
QED

Theorem FINITE_BOOL[simp]: FINITE univ(:bool)
Proof simp[]
QED

(* NOTE: This theorem has been moved to pred_setTheory with a different name *)
Theorem INFINITE_DIFF_FINITE = INFINITE_DIFF_FINITE'

(* ------------------------------------------------------------------------- *)
(* misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

val GE = store_thm ("GE",
  ``!n m:num. m >= n <=> n <= m``,
  METIS_TAC [GREATER_EQ]);

val LE_SUC_LT = store_thm ("LE_SUC_LT",
 ``!m n. (SUC m <= n) <=> (m < n)``,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LE, LT, GSYM SUC_NOT, INV_SUC_EQ]);

val lemma = METIS [] ``(!x. x IN s ==> (g(f(x)) = x)) <=>
                     (!y x. x IN s /\ (y = f x) ==> (g y = x))``;

val th = REWRITE_RULE[IN_UNIV]
            (ISPECL [“f:'a->'b”, “UNIV:'a->bool”] INJECTIVE_ON_LEFT_INVERSE);

val INJECTIVE_LEFT_INVERSE = store_thm ("INJECTIVE_LEFT_INVERSE",
 ``(!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)``,
  REWRITE_TAC[th]);

val INTER_ACI = store_thm ("INTER_ACI",
 ``!p q. (p INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)``,
  SET_TAC[]);

val CONJ_ACI = store_thm ("CONJ_ACI",
 ``!p q. (p /\ q <=> q /\ p) /\
   ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
   (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
   (p /\ p <=> p) /\
   (p /\ (p /\ q) <=> p /\ q)``,
  METIS_TAC [CONJ_ASSOC, CONJ_SYM]);

val UNION_ACI = store_thm ("UNION_ACI",
 ``!p q. (p UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)``,
  SET_TAC[]);

val LT_NZ = store_thm ("LT_NZ",
 ``!n. 0 < n <=> ~(n = 0:num)``,
  INDUCT_TAC THEN ASM_SIMP_TAC std_ss [NOT_SUC, LT, EQ_SYM_EQ] THEN
  TAUT_TAC);

val LE_1 = store_thm ("LE_1",
 ``(!n:num. ~(n = 0) ==> 0 < n) /\
   (!n:num. ~(n = 0) ==> 1 <= n) /\
   (!n:num. 0 < n ==> ~(n = 0)) /\
   (!n:num. 0 < n ==> 1 <= n) /\
   (!n:num. 1 <= n ==> 0 < n) /\
   (!n:num. 1 <= n ==> ~(n = 0))``,
  METIS_TAC [LT_NZ, GSYM NOT_LESS, ONE, LT]);

val OR_EXISTS_THM = store_thm ("OR_EXISTS_THM",
 ``!P Q. (?x. P x) \/ (?x. Q x) <=> (?x:'a. P x \/ Q x)``,
  METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* Now bijectivity.                                                          *)
(* ------------------------------------------------------------------------- *)

val BIJECTIVE_INJECTIVE_SURJECTIVE = store_thm ("BIJECTIVE_INJECTIVE_SURJECTIVE",
 ``!f s t. (!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
   (!y. y IN t ==> ?x. x IN s /\ (f x = y))``,
  MESON_TAC[]);

val BIJECTIVE_INVERSES = store_thm ("BIJECTIVE_INVERSES",
 ``!f s t. (!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   ?g. (!y. y IN t ==> g(y) IN s) /\
       (!y. y IN t ==> (f(g(y)) = y)) /\
       (!x. x IN s ==> (g(f(x)) = x))``,
  NTAC 3 GEN_TAC THEN
  REWRITE_TAC[BIJECTIVE_INJECTIVE_SURJECTIVE,
              INJECTIVE_ON_LEFT_INVERSE,
              SURJECTIVE_ON_RIGHT_INVERSE] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN METIS_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (in HOL-light's notations)                           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "<=_c" (Infix(NONASSOC, 450)); (* for cardleq *)
val _ = overload_on("<=_c", ``cardleq``);
val _ = overload_on("<<=",  ``$<=_c``);           (* defined in pred_setTheory *)

val _ = set_fixity "<_c" (Infix(NONASSOC, 450));  (* for cardlt *)
val _ = overload_on("<_c", ``cardlt``);
val _ = overload_on("<</=", ``$<_c``);

val _ = set_fixity ">=_c" (Infix(NONASSOC, 450)); (* for cardgeq *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x227D, tmnm = ">=_c"};
val _ = TeX_notation {hol = ">=_c",          TeX = ("\\ensuremath{\\succcurlyeq}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227D, TeX = ("\\ensuremath{\\succcurlyeq}", 1)};

val _ = set_fixity ">_c" (Infix(NONASSOC, 450));  (* for cardgt *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x227B, tmnm = ">_c"};
val _ = TeX_notation {hol = ">_c",           TeX = ("\\ensuremath{\\succ}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227B, TeX = ("\\ensuremath{\\succ}", 1)};

val _ = set_fixity "=_c" (Infix(NONASSOC, 450));  (* for cardeq *)
val _ = overload_on("=_c", ``cardeq``);
val _ = overload_on("=~",  ``$=_c``);

val le_c = store_thm ("le_c",
  ``!s t. s <=_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                           (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))``,
    rpt GEN_TAC
 >> REWRITE_TAC [cardleq_def, INJ_DEF]
 >> PROVE_TAC []);

val lt_c = store_thm ("lt_c",
  ``!s t. s <_c t <=> s <=_c t /\ ~(t <=_c s)``,
    rpt GEN_TAC
 >> EQ_TAC >> STRIP_TAC
 >> PROVE_TAC [cardlt_lenoteq]);

val eq_c = store_thm ("eq_c",
  ``!s t. s =_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                          !y. y IN t ==> ?!x. x IN s /\ (f x = y)``,
    rpt GEN_TAC
 >> REWRITE_TAC [cardeq_def, BIJ_ALT, IN_FUNSET]
 >> `!f x y. (f x = y) = (y = f x)` by PROVE_TAC [EQ_SYM]
 >> ASM_REWRITE_TAC []);

val cardgeq_def = Define
   `cardgeq s t = cardleq t s`;

val _ = overload_on (">=_c", ``cardgeq``);
val ge_c = save_thm ("ge_c",   cardgeq_def);

val cardgt_def = Define
   `cardgt s t = cardlt t s`;

val _ = overload_on (">_c",  ``cardgt``);
val gt_c = save_thm ("gt_c",   cardgt_def);

val LE_C = store_thm ("LE_C",
 ``!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\ (g y = x)``,
  SIMP_TAC std_ss [le_c, INJECTIVE_ON_LEFT_INVERSE, SURJECTIVE_ON_RIGHT_INVERSE,
  GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
  MESON_TAC[]);

val GE_C = store_thm ("GE_C",
 ``!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\ (y = f x)``,
  REWRITE_TAC[ge_c, LE_C] THEN MESON_TAC[]);

val COUNTABLE = store_thm
  ("COUNTABLE", ``!t. COUNTABLE t <=> univ(:num) >=_c t``,
    REWRITE_TAC [countable_def, cardgeq_def, cardleq_def]);

(* ------------------------------------------------------------------------- *)
(* Relational variant of =_c is sometimes useful.                            *)
(* ------------------------------------------------------------------------- *)

Theorem EQ_C_BIJECTIONS :
    !(s :'a -> bool) (t :'b -> bool).
        s =_c t <=> ?f g. (!x. x IN s ==> f x IN t /\ g(f x) = x) /\
                          (!y. y IN t ==> g y IN s /\ f(g y) = y)
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [eq_c] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I empty_rewrites [FUN_EQ_THM] THEN
  Q.X_GEN_TAC ‘f’ THEN SIMP_TAC std_ss [] THEN
  EQ_TAC THENL [STRIP_TAC, MESON_TAC[]] THEN
  Q.EXISTS_TAC `(\y. @x. x IN s /\ f x = y)` THEN
(* HOL-Light's ASM_MESON_TAC seems more powerful than HOL4's:
   ASM_MESON_TAC[]
 *)
  rw [] >> SELECT_ELIM_TAC \\
  fs [EXISTS_UNIQUE_DEF]
QED

val EQ_C = store_thm ("EQ_C",
 ``!s t. s =_c t <=>
   ?R:'a#'b->bool. (!x y. R(x,y) ==> x IN s /\ y IN t) /\
                 (!x. x IN s ==> ?!y. y IN t /\ R(x,y)) /\
                 (!y. y IN t ==> ?!x. x IN s /\ R(x,y))``,
  rpt GEN_TAC THEN
  REWRITE_TAC[eq_c] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ``\(x:'a,y:'b). x IN s /\ y IN t /\ (y = f x)`` THEN
    SIMP_TAC std_ss [] THEN ASM_MESON_TAC[],
    METIS_TAC []]);

(* ------------------------------------------------------------------------- *)
(* The "easy" ordering properties.                                           *)
(* ------------------------------------------------------------------------- *)

val CARD_LE_REFL = store_thm ("CARD_LE_REFL",
 ``!s:'a->bool. s <=_c s``,
  simp[cardleq_REFL]);

Theorem CARD_LE_TRANS:
   !s:'a->bool t:'b->bool u:'c->bool.
       s <=_c t /\ t <=_c u ==> s <=_c u
Proof
  metis_tac[cardleq_TRANS]
QED

val CARD_LT_REFL = store_thm ("CARD_LT_REFL",
 ``!s:'a->bool. ~(s <_c s)``,
  MESON_TAC [CARD_LE_REFL]);

val CARD_LET_TRANS = store_thm ("CARD_LET_TRANS",
 ``!s:'a->bool t:'b->bool u:'c->bool.
       s <=_c t /\ t <_c u ==> s <_c u``,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [lt_c] THEN
  MATCH_MP_TAC(TAUT `(a /\ b ==> c) /\ (c' /\ a ==> b')
                     ==> a /\ b /\ ~b' ==> c /\ ~c'`) THEN
  REWRITE_TAC[CARD_LE_TRANS]);

val CARD_LTE_TRANS = store_thm ("CARD_LTE_TRANS",
 ``!s:'a->bool t:'b->bool u:'c->bool.
       s <_c t /\ t <=_c u ==> s <_c u``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [lt_c] THEN
  MATCH_MP_TAC(TAUT `(a /\ b ==> c) /\ (b /\ c' ==> a')
                     ==> (a /\ ~a') /\ b ==> c /\ ~c'`) THEN
  REWRITE_TAC[CARD_LE_TRANS]);

val CARD_LT_TRANS = store_thm ("CARD_LT_TRANS",
 ``!s:'a->bool t:'b->bool u:'c->bool.
       s <_c t /\ t <_c u ==> s <_c u``,
  MESON_TAC[lt_c, CARD_LTE_TRANS]);

val CARD_EQ_REFL = store_thm ("CARD_EQ_REFL",
 ``!s:'a->bool. s =_c s``,
  GEN_TAC THEN REWRITE_TAC[eq_c] THEN EXISTS_TAC ``\x:'a. x`` THEN
  SIMP_TAC std_ss [] THEN MESON_TAC[]);

val CARD_EQ_SYM = store_thm ("CARD_EQ_SYM",
 ``!s t. (s =_c t) <=> (t =_c s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c, BIJECTIVE_INVERSES] THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN
  METIS_TAC []);

val CARD_EQ_IMP_LE = store_thm ("CARD_EQ_IMP_LE",
 ``!s t. s =_c t ==> s <=_c t``,
  REWRITE_TAC[le_c, eq_c] THEN MESON_TAC[]);

val CARD_LT_IMP_LE = store_thm ("CARD_LT_IMP_LE",
 ``!s t. s <_c t ==> s <=_c t``,
  ONCE_REWRITE_TAC [lt_c]
  THEN SIMP_TAC std_ss []);

val CARD_LE_RELATIONAL = store_thm ("CARD_LE_RELATIONAL",
 ``!(R:'a->'b->bool) s.
        (!x y y'. x IN s /\ R x y /\ R x y' ==> (y = y'))
        ==> {y | ?x. x IN s /\ R x y} <=_c s``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC ``\y:'b. @x:'a. x IN s /\ R x y`` THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Two trivial lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

val CARD_LE_EMPTY = store_thm ("CARD_LE_EMPTY",
 ``!s. (s <=_c EMPTY) <=> (s = EMPTY)``,
  SIMP_TAC std_ss [le_c, EXTENSION, NOT_IN_EMPTY] THEN METIS_TAC[]);

val CARD_EQ_EMPTY = store_thm ("CARD_EQ_EMPTY",
 ``!s. (s =_c EMPTY) <=> (s = EMPTY)``,
  REWRITE_TAC[eq_c, EXTENSION, NOT_IN_EMPTY] THEN MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Antisymmetry (the Schroeder-Bernstein theorem).                           *)
(* ------------------------------------------------------------------------- *)

val CARD_LE_ANTISYM = store_thm
  ("CARD_LE_ANTISYM",
  ``!s:'a->bool t:'b->bool. s <=_c t /\ t <=_c s <=> (s =_c t)``,
    rpt GEN_TAC >> EQ_TAC
 >- PROVE_TAC [cardleq_ANTISYM]
 >> PROVE_TAC [CARD_EQ_IMP_LE, CARD_EQ_SYM]);

(* ------------------------------------------------------------------------- *)
(* Totality (cardinal comparability).                                        *)
(* ------------------------------------------------------------------------- *)

val CARD_LE_TOTAL = save_thm ("CARD_LE_TOTAL", cardleq_dichotomy);

(* ------------------------------------------------------------------------- *)
(* Other variants like "trichotomy of cardinals" now follow easily.          *)
(* ------------------------------------------------------------------------- *)

val CARD_LET_TOTAL = store_thm ("CARD_LET_TOTAL",
 ``!s:'a->bool t:'b->bool. s <=_c t \/ t <_c s``,
  ONCE_REWRITE_TAC [lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);

val CARD_LTE_TOTAL = store_thm ("CARD_LTE_TOTAL",
 ``!s:'a->bool t:'b->bool. s <_c t \/ t <=_c s``,
  ONCE_REWRITE_TAC [lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);

val CARD_LT_TOTAL = store_thm ("CARD_LT_TOTAL",
 ``!s:'a->bool t:'b->bool. (s =_c t) \/ s <_c t \/ t <_c s``,
  REWRITE_TAC[Once lt_c, GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_TOTAL]);

val CARD_NOT_LE = store_thm ("CARD_NOT_LE",
 ``!s:'a->bool t:'b->bool. ~(s <=_c t) <=> t <_c s``,
  ONCE_REWRITE_TAC [lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);

val CARD_NOT_LT = store_thm ("CARD_NOT_LT",
 ``!s:'a->bool t:'b->bool. ~(s <_c t) <=> t <=_c s``,
  ONCE_REWRITE_TAC [lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);

val CARD_LT_LE = store_thm ("CARD_LT_LE",
 ``!s t. s <_c t <=> s <=_c t /\ ~(s =_c t)``,
  REWRITE_TAC[Once lt_c, GSYM CARD_LE_ANTISYM] THEN TAUT_TAC);

Theorem CARD_LE_LT = cardleq_lteq

Theorem CARD_LE_CONG = CARDEQ_CARDLEQ

Theorem CARD_LT_CONG:
 !s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
   s =_c s' /\ t =_c t' ==> (s <_c t <=> s' <_c t')
Proof
  REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CARD_LE_CONG THEN
  ASM_REWRITE_TAC[]
QED

Theorem CARD_12[simp]:
  {()} <</= {T;F} /\ ~({()} =~ {T;F}) /\ ~({T;F} =~ {()}) /\ {()} <<= {T;F}
Proof
  conj_asm1_tac
  >- (simp[cardleq_def, INJ_IFF] >> qexistsl_tac [‘T’, ‘F’] >> simp[]) >>
  metis_tac[CARD_LT_CONG, CARD_LT_REFL, cardeq_REFL, cardleq_lteq]
QED

Theorem CARD_EQ_TRANS = cardeq_TRANS

Theorem CARD_EQ_CONG:
  !s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
    s =_c s' /\ t =_c t' ==> (s =_c t <=> s' =_c t')
Proof
  METIS_TAC[CARD_EQ_TRANS, CARD_EQ_SYM]
QED

(* ------------------------------------------------------------------------- *)
(* Finiteness and infiniteness in terms of cardinality of N.                 *)
(* ------------------------------------------------------------------------- *)

Theorem INFINITE_CARD_LE[local] = INFINITE_Unum

val FINITE_CARD_LT = store_thm ("FINITE_CARD_LT",
 ``!s:'a->bool. FINITE s <=> s <_c (UNIV:num->bool)``,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC [Once (GSYM CARD_NOT_LT), INFINITE_CARD_LE]);

val CARD_LE_SUBSET = store_thm ("CARD_LE_SUBSET",
 ``!s:'a->bool t. s SUBSET t ==> s <=_c t``,
  REWRITE_TAC[SUBSET_DEF, le_c] THEN MESON_TAC[combinTheory.I_THM]);

val CARD_LE_UNIV = store_thm ("CARD_LE_UNIV",
 ``!s:'a->bool. s <=_c univ(:'a)``,
  GEN_TAC THEN MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);

val CARD_LE_EQ_SUBSET = store_thm ("CARD_LE_EQ_SUBSET",
 ``!s:'a->bool t:'b->bool. s <=_c t <=> ?u. u SUBSET t /\ (s =_c u)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
    MATCH_MP_TAC CARD_LE_CONG THEN
    ASM_REWRITE_TAC[CARD_LE_CONG, CARD_EQ_REFL]] THEN
  REWRITE_TAC[le_c, eq_c] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN EXISTS_TAC ``IMAGE (f:'a->'b) s`` THEN
  EXISTS_TAC ``f:'a->'b`` THEN REWRITE_TAC[IN_IMAGE, SUBSET_DEF] THEN
  ASM_MESON_TAC[]);

val CARD_INFINITE_CONG = store_thm ("CARD_INFINITE_CONG",
 ``!s:'a->bool t:'b->bool. s =_c t ==> (INFINITE s <=> INFINITE t)``,
  REWRITE_TAC[INFINITE_CARD_LE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARD_LE_CONG THEN ASM_SIMP_TAC std_ss [CARD_EQ_REFL]);

val CARD_FINITE_CONG = store_thm ("CARD_FINITE_CONG",
 ``!s:'a->bool t:'b->bool. s =_c t ==> (FINITE s <=> FINITE t)``,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  SIMP_TAC std_ss [CARD_INFINITE_CONG]);

val CARD_LE_FINITE = store_thm ("CARD_LE_FINITE",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s <=_c t ==> FINITE s``,
  ASM_MESON_TAC[CARD_LE_EQ_SUBSET, SUBSET_FINITE_I, CARD_FINITE_CONG]);

val CARD_EQ_FINITE = store_thm ("CARD_EQ_FINITE",
 ``!s t:'a->bool. FINITE t /\ s =_c t ==> FINITE s``,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_FINITE]);

val CARD_LE_INFINITE = store_thm ("CARD_LE_INFINITE",
 ``!s:'a->bool t:'b->bool. INFINITE s /\ s <=_c t ==> INFINITE t``,
  MESON_TAC[CARD_LE_FINITE]);

val CARD_LT_FINITE_INFINITE = store_thm ("CARD_LT_FINITE_INFINITE",
 ``!s:'a->bool t:'b->bool. FINITE s /\ INFINITE t ==> s <_c t``,
  ONCE_REWRITE_TAC[GSYM CARD_NOT_LE] THEN MESON_TAC[CARD_LE_FINITE]);

val CARD_LE_CARD_IMP = store_thm ("CARD_LE_CARD_IMP",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s <=_c t ==> CARD s <= CARD t``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``FINITE(s:'a->bool)`` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_LE_FINITE], ALL_TAC] THEN
  UNDISCH_TAC ``s <=_c t`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [le_c]) THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC ``CARD(IMAGE (f:'a->'b) s)`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_PROVE ``(m = n:num) ==> n <= m``) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[],
    KNOW_TAC ``(IMAGE (f :'a -> 'b) (s :'a -> bool)) SUBSET (t :'b -> bool)`` THENL
    [ASM_MESON_TAC[SUBSET_DEF, IN_IMAGE], ALL_TAC] THEN
    MATCH_MP_TAC (CARD_SUBSET) THEN ASM_REWRITE_TAC[]]);

val CARD_EQ_CARD_IMP = store_thm ("CARD_EQ_CARD_IMP",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s =_c t ==> (CARD s = CARD t)``,
  METIS_TAC[CARD_FINITE_CONG, ARITH_PROVE ``m <= n /\ n <= m <=> (m = n:num)``,
            CARD_LE_ANTISYM, CARD_LE_CARD_IMP]);

Theorem CARD_LE_CARD:
  !s:'a->bool t:'b->bool.
    FINITE s /\ FINITE t ==> (s <=_c t <=> CARD s <= CARD t)
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT ‘(a ==> b) /\ (~a ==> ~b) ==> (a <=> b)’) THEN
  ASM_SIMP_TAC std_ss [CARD_LE_CARD_IMP] THEN
  REWRITE_TAC[NOT_LESS_EQUAL] THEN REWRITE_TAC[Once lt_c, LT_LE] THEN
  ASM_SIMP_TAC std_ss [CARD_LE_CARD_IMP] THEN
  MATCH_MP_TAC(TAUT ‘(c ==> a ==> b) ==> a /\ ~b ==> ~c’) THEN
  DISCH_TAC THEN simp[CARD_LE_EQ_SUBSET, SimpL “$==>”] THEN
  DISCH_THEN(qx_choose_then ‘u’ STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  ‘u = s’ suffices_by ASM_MESON_TAC[CARD_EQ_SYM] THEN
  METIS_TAC[CARD_SUBSET_EQ, CARD_EQ_CARD_IMP, CARD_EQ_SYM]
QED

val CARD_EQ_CARD = store_thm ("CARD_EQ_CARD",
 ``!s:'a->bool t:'b->bool.
        FINITE s /\ FINITE t ==> (s =_c t <=> (CARD s = CARD t))``,
  MESON_TAC[CARD_FINITE_CONG, ARITH_PROVE ``m <= n /\ n <= m <=> (m = n:num)``,
            CARD_LE_ANTISYM, CARD_LE_CARD]);

val CARD_HAS_SIZE_CONG = store_thm ("CARD_HAS_SIZE_CONG",
 ``!s:'a->bool t:'b->bool n. s HAS_SIZE n /\ s =_c t ==> t HAS_SIZE n``,
  REWRITE_TAC[HAS_SIZE] THEN
  MESON_TAC[CARD_EQ_CARD, CARD_FINITE_CONG]);

val CARD_LE_IMAGE = store_thm ("CARD_LE_IMAGE",
 ``!f s. IMAGE f s <=_c s``,
  SIMP_TAC std_ss [LE_C, FORALL_IN_IMAGE] THEN MESON_TAC[]);

val CARD_LE_IMAGE_GEN = store_thm ("CARD_LE_IMAGE_GEN",
 ``!f:'a->'b s t. t SUBSET IMAGE f s ==> t <=_c s``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_LE_TRANS THEN
  EXISTS_TAC ``IMAGE (f:'a->'b) s`` THEN
  ASM_SIMP_TAC std_ss [CARD_LE_IMAGE, CARD_LE_SUBSET]);

val CARD_EQ_IMAGE = store_thm ("CARD_EQ_IMAGE",
 ``!f:'a->'b s.
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (IMAGE f s =_c s)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[eq_c] THEN EXISTS_TAC ``f:'a->'b`` THEN ASM_SET_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Cardinal arithmetic operations.                                           *)
(* ------------------------------------------------------------------------- *)

val add_c = disjUNION_def

val _ = set_mapped_fixity {tok = "+_c", fixity = Infixl 500,
                           term_name = "disjUNION"}
val _ = set_mapped_fixity {fixity = Infixl 500,
                           term_name = "disjUNION",
                           tok = UTF8.chr 0x2294}

Overload "+"[local,inferior] = “disjUNION”;

val _ = temp_set_fixity "*_c" (Infixl 600);
Overload "*_c"[local,inferior] = “pred_set$CROSS”;

Theorem mul_c:
  !s t. s *_c t = {(x,y) | x IN s /\ y IN t}
Proof
  simp[EXTENSION, FORALL_PROD]
QED

(* ------------------------------------------------------------------------- *)
(* Congruence properties for the arithmetic operators.                       *)
(* ------------------------------------------------------------------------- *)

Theorem CARD_LE_ADD:
 !s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
   s <=_c s' /\ t <=_c t' ==> s + t <=_c s' + t'
Proof
  rpt gen_tac >> simp[le_c, add_c, FORALL_SUM] >>
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN “f:'a->'b” STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN “g:'c->'d” STRIP_ASSUME_TAC)) >>
  qexists ‘λs. case s of INL a => INL (f a) | INR b => INR (g b)’ >>
  simp[]
QED

Theorem CARD_LE_MUL = CARDLEQ_CROSS_CONG

Theorem CARD_ADD_CONG:
 !s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
   s =_c s' /\ t =_c t' ==> (s +_c t) =_c (s' +_c t')
Proof
  SIMP_TAC std_ss [CARD_LE_ADD, GSYM CARD_LE_ANTISYM]
QED

Theorem CARD_MUL_CONG = CARDEQ_CROSS

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem IN_CARD_ADD = IN_disjUNION

Theorem IN_CARD_MUL: !s t x y. (x,y) IN (s *_c t) <=> x IN s /\ y IN t
Proof simp[]
QED

Theorem CARD_LE_SQUARE:
  !s:'a->bool. s <=_c (s *_c s)
Proof
  simp[le_c] >> gen_tac >> qexists ‘λx. (x,x)’ >> simp[]
QED

Theorem CARD_SQUARE_NUM:
  univ(:num) *_c univ(:num) =_c univ(:num)
Proof
  simp[cardeq_def] >> metis_tac[NUM_2D_BIJ_INV, BIJ_INV]
QED

Theorem UNION_LE_ADD_C:
 !s t:'a->bool. s UNION t <=_c s + t
Proof
  rw[le_c] >> qexists ‘λx. if x IN s then INL x else INR x’ >> rw[]
QED

Theorem CARD_DISJOINT_UNION:
  !s t.
    FINITE s /\ FINITE t /\ s INTER t = {} ==>
    CARD (s UNION t) = CARD s + CARD t
Proof
  simp[CARD_UNION_EQN]
QED

Theorem CARD_ADD_C = CARD_disjUNION

(* ------------------------------------------------------------------------- *)
(* Various "arithmetical" lemmas.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem CARD_ADD_SYM:
  !s:'a->bool t:'b->bool. (s +_c t) =_c (t +_c s)
Proof
  rw[cardeq_def] >> qexists ‘λx. case x of INL a => INR a | INR b => INL b’ >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_SUM, AllCaseEqs()]
QED

Theorem CARD_ADD_ASSOC:
  !s:'a->bool t:'b->bool u:'c->bool. (s +_c (t +_c u)) =_c ((s +_c t) +_c u)
Proof
  rw[cardeq_def] >>
  qexists ‘λx. case x of INL a => INL (INL a) | INR (INL b) => INL (INR b)
                      | INR (INR c) => INR c’ >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_SUM, AllCaseEqs()]
QED

Theorem CARD_MUL_SYM = CARDEQ_CROSS_SYM

Theorem CARD_MUL_ASSOC:
  !s:'a->bool t:'b->bool u:'c->bool. (s *_c (t *_c u)) =_c ((s *_c t) *_c u)
Proof
  rw[cardeq_def] >>
  qexists ‘λt. case t of (a,(b,c)) => ((a,b),c)’>>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD]
QED

Theorem CARD_LDISTRIB:
  !s:'a->bool t:'b->bool u:'c->bool.
    (s *_c (t +_c u)) =_c ((s *_c t) +_c (s *_c u))
Proof
  rw[cardeq_def] >>
  qexists ‘λp. case p of (a,INL b) => INL (a,b) | (a, INR c) => INR (a, c)’ >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD, FORALL_SUM,
       AllCaseEqs()]
QED

Theorem CARD_RDISTRIB:
  !s:'a->bool t:'b->bool u:'c->bool.
    (s +_c t) *_c u =_c (s *_c u) +_c (t *_c u)
Proof
  rw[cardeq_def] >>
  qexists ‘λp. case p of (INL a, c) => INL (a,c) | (INR b, c) => INR (b,c)’ >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD, EXISTS_PROD, FORALL_SUM,
       AllCaseEqs()]
QED

val CARD_LE_ADDR = store_thm ("CARD_LE_ADDR",
 ``!s:'a->bool t:'b->bool. s <=_c (s +_c t)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC ``INL:'a->'a+'b`` THEN SIMP_TAC std_ss [IN_CARD_ADD, INR_11, INL_11]);;

val CARD_LE_ADDL = store_thm ("CARD_LE_ADDL",
 ``!s:'a->bool t:'b->bool. t <=_c (s +_c t)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC ``INR:'b->'a+'b`` THEN SIMP_TAC std_ss [IN_CARD_ADD, INR_11, INL_11]);

(* ------------------------------------------------------------------------- *)
(* A rather special lemma but temporarily useful.                            *)
(* ------------------------------------------------------------------------- *)

val CARD_ADD_LE_MUL_INFINITE = store_thm ("CARD_ADD_LE_MUL_INFINITE",
 ``!s:'a->bool. INFINITE s ==> (s +_c s) <=_c (s *_c s)``,
  GEN_TAC THEN REWRITE_TAC[INFINITE_CARD_LE, le_c, IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:num->'a`` STRIP_ASSUME_TAC) THEN
  KNOW_TAC ``?h. (!x. h(INL x) = (f(0:num),x):'a#'a) /\ (!x. h(INR x) = (f(1),x))`` THENL
  [RW_TAC std_ss [sum_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``h:'a+'a->'a#'a`` THEN STRIP_TAC THENL
  [ONCE_REWRITE_TAC [METIS [] ``( x IN s +_c s ==> h x IN s *_c s) =
                            (\x.  x IN s +_c s ==> h x IN s *_c s) x``] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [] ``(!y. x IN s +_c s /\ y IN s +_c s /\ (h x = h y) ==> (x = y)) =
                          (\x. !y. x IN s +_c s /\ y IN s +_c s /\ (h x = h y) ==> (x = y)) x``] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ] THEN STRIP_TAC THEN STRIP_TAC THENL
   [ONCE_REWRITE_TAC [METIS [] ``(x IN s /\ y IN s +_c s /\ ((f (0:num),x) =
                                (h :'a + 'a -> 'a # 'a) y) ==> (INL x = y)) =
                      (\y:'a+'a. x IN s /\ y IN s +_c s /\ ((f (0:num),x) =
                                (h :'a + 'a -> 'a # 'a) y) ==> (INL x = y)) y``],
    ONCE_REWRITE_TAC [METIS [] ``(x IN s /\ y IN s +_c s /\ ((f (1:num),x) =
                                (h :'a + 'a -> 'a # 'a) y) ==> (INR x = y)) =
                      (\y:'a+'a. x IN s /\ y IN s +_c s /\ ((f (1:num),x) =
                                (h :'a + 'a -> 'a # 'a) y) ==> (INR x = y)) y``]] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ] THEN
   ASM_MESON_TAC[REDUCE_CONV ``1 = 0:num``]);

(* ------------------------------------------------------------------------- *)
(* Relate cardinal addition to the simple union operation.                   *)
(* ------------------------------------------------------------------------- *)

Theorem CARDEQ_DISJOINT_UNION:
  !s:'a->bool t. (s INTER t = EMPTY) ==> (s UNION t =_c (s +_c t))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[eq_c, IN_UNION] THEN
  EXISTS_TAC ``\x:'a. if x IN s then INL x else INR x`` THEN
  SIMP_TAC std_ss [FORALL_SUM, IN_CARD_ADD] THEN
  REWRITE_TAC[COND_RAND, COND_RATOR] THEN
  REWRITE_TAC[TAUT `(if b then x else y) <=> b /\ x \/ ~b /\ y`] THEN
  SIMP_TAC std_ss [sum_distinct, INL_11, INR_11, IN_CARD_ADD] THEN
  ASM_MESON_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* The key to arithmetic on infinite cardinals: k^2 = k.                     *)
(* ------------------------------------------------------------------------- *)

val CARD_SQUARE_INFINITE = save_thm
  ("CARD_SQUARE_INFINITE", SET_SQUARED_CARDEQ_SET);

(* ------------------------------------------------------------------------- *)
(* Preservation of finiteness.                                               *)
(* ------------------------------------------------------------------------- *)

val CARD_ADD_FINITE = store_thm ("CARD_ADD_FINITE",
 ``!s t. FINITE s /\ FINITE t ==> FINITE(s +_c t)``,
  SIMP_TAC std_ss [add_c, FINITE_UNION, GSYM IMAGE_DEF, IMAGE_FINITE]);

val CARD_ADD_FINITE_EQ = store_thm ("CARD_ADD_FINITE_EQ",
 ``!s:'a->bool t:'b->bool. FINITE(s +_c t) <=> FINITE s /\ FINITE t``,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CARD_ADD_FINITE] THEN
  DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) THEN
  REWRITE_TAC[CARD_LE_ADDL, CARD_LE_ADDR]);

val CARD_MUL_FINITE = store_thm ("CARD_MUL_FINITE",
 ``!s t. FINITE s /\ FINITE t ==> FINITE(s *_c t)``,
  SIMP_TAC std_ss [mul_c, FINITE_PRODUCT]);

(* ------------------------------------------------------------------------- *)
(* Hence the "absorption laws" for arithmetic with an infinite cardinal.     *)
(* ------------------------------------------------------------------------- *)

val CARD_MUL2_ABSORB_LE = store_thm ("CARD_MUL2_ABSORB_LE",
 ``!s:'a->bool t:'b->bool u:'c->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> (s *_c t) <=_c u``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s *_c t) <=_c ((s:'a->bool) *_c (u:'c->bool)) /\
             ((s:'a->bool) *_c (u:'c->bool)) <=_c u`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_MUL_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_MUL THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_ADD_ABSORB_LE = store_thm ("CARD_ADD_ABSORB_LE",
 ``!s:'a->bool t:'b->bool. INFINITE(t) /\ s <=_c t ==> (s +_c t) <=_c t``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s +_c t) <=_c ((t:'b->bool) *_c t) /\
             ((t:'b->bool) *_c t) <=_c t`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_SQUARE_INFINITE, CARD_EQ_IMP_LE] THEN
  KNOW_TAC ``(s +_c t) <=_c ((t:'b->bool) +_c t) /\
             ((t:'b->bool) +_c t) <=_c (t *_c t)`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD_LE_MUL_INFINITE, CARD_LE_ADD, CARD_LE_REFL]);

val CARD_ADD2_ABSORB_LE = store_thm ("CARD_ADD2_ABSORB_LE",
 ``!s:'a->bool t:'b->bool u:'c->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> (s +_c t) <=_c u``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s +_c t) <=_c ((s:'a->bool) +_c (u:'c->bool)) /\
             ((s:'a->bool) +_c (u:'c->bool)) <=_c u`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_ADD THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_MUL_ABSORB = store_thm ("CARD_MUL_ABSORB",
 ``!s:'a->bool t:'b->bool.
     INFINITE(t) /\ ~(s = {}) /\ s <=_c t ==> (s *_c t) =_c t``,
  SIMP_TAC std_ss [GSYM CARD_LE_ANTISYM, CARD_MUL_ABSORB_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC ``a:'a`` o
   REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC ``\x:'b. (a:'a,x)`` THEN
  ASM_SIMP_TAC std_ss [IN_CARD_MUL, PAIR_EQ]);

val CARD_ADD_ABSORB = store_thm ("CARD_ADD_ABSORB",
 ``!s:'a->bool t:'b->bool. INFINITE(t) /\ s <=_c t ==> (s +_c t) =_c t``,
  SIMP_TAC std_ss [GSYM CARD_LE_ANTISYM, CARD_LE_ADDL, CARD_ADD_ABSORB_LE]);

val CARD_ADD2_ABSORB_LT = store_thm ("CARD_ADD2_ABSORB_LT",
 ``!s:'a->bool t:'b->bool u:'c->bool.
        INFINITE u /\ s <_c u /\ t <_c u ==> (s +_c t) <_c u``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_CASES_TAC ``FINITE((s:'a->bool) +_c (t:'b->bool))`` THEN
  ASM_SIMP_TAC std_ss [CARD_LT_FINITE_INFINITE] THEN
  DISJ_CASES_TAC(ISPECL [``s:'a->bool``, ``t:'b->bool``] CARD_LE_TOTAL) THENL
   [(* goal 1 (of 2) *)
    ASM_CASES_TAC ``FINITE(t:'b->bool)`` THENL
     [ASM_MESON_TAC[CARD_LE_FINITE, CARD_ADD_FINITE],
      KNOW_TAC ``(s +_c t) <=_c (t:'b->bool) /\
                 (t:'b->bool) <_c u`` THENL
      [ALL_TAC, METIS_TAC [CARD_LET_TRANS]]],
    (* goal 2 (of 2) *)
    ASM_CASES_TAC ``FINITE(s:'a->bool)`` THENL
     [ASM_MESON_TAC[CARD_LE_FINITE, CARD_ADD_FINITE],
      KNOW_TAC ``(s +_c t) <=_c (s:'a->bool) /\
                 (s:'a->bool) <_c u`` THENL
      [ALL_TAC, METIS_TAC [CARD_LET_TRANS]]]] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_ADD2_ABSORB_LE THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_LT_ADD = store_thm ("CARD_LT_ADD",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
        s <_c s' /\ t <_c t' ==> (s +_c t) <_c (s' +_c t')``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_CASES_TAC ``FINITE((s':'b->bool) +_c (t':'d->bool))`` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE
      [CARD_ADD_FINITE_EQ]) THEN
    SUBGOAL_THEN ``FINITE(s:'a->bool) /\ FINITE(t:'c->bool)``
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) o
        MATCH_MP CARD_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[],
      MAP_EVERY UNDISCH_TAC
       [``(s:'a->bool) <_c (s':'b->bool)``,
        ``(t:'c->bool) <_c (t':'d->bool)``] THEN
      ASM_SIMP_TAC std_ss [CARD_LT_CARD, CARD_ADD_FINITE, CARD_ADD_C] THEN
      ARITH_TAC],
    MATCH_MP_TAC CARD_ADD2_ABSORB_LT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [METIS_TAC [CARD_LTE_TRANS, CARD_LE_ADDR],
      METIS_TAC [CARD_LTE_TRANS, CARD_LE_ADDL]]]);

(* ------------------------------------------------------------------------- *)
(* Cantor's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem CANTOR_THM:
   !s:'a->bool. s <_c {t | t SUBSET s}
Proof
  simp[GSYM POW_DEF]
QED

Theorem CANTOR_THM_UNIV:
   (UNIV:'a->bool) <_c (UNIV:('a->bool)->bool)
Proof
  ‘univ(:'a -> bool) = POW univ(:'a)’ suffices_by simp[] >>
  simp[EXTENSION, POW_DEF]
QED

Theorem CARD_EXP_SING :
    !(s :'a -> bool) (b :'b). (s ** {b}) =_c s
Proof
    REWRITE_TAC [SING_set_exp_CARD]
QED

Theorem CARD_EXP_CONG :
    !(s:'a->bool) (s':'b->bool) (t:'c->bool) (t':'d->bool).
      s =_c s' /\ t =_c t' ==> s ** t =_c s' ** t'
Proof
    rw [set_exp_card_cong]
QED

Theorem CARD_LE_EXP_LEFT :
    !(s :'a -> bool) (s' :'b -> bool) (t :'c -> bool).
        s <=_c s' ==> s ** t <=_c s' ** t
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c, exp_c] THEN
  DISCH_THEN(X_CHOOSE_TAC “f :'a -> 'b”) THEN
  rw [GSPECIFICATION] THEN
  EXISTS_TAC “\(g:'c->'a) (z:'c). if z IN t then f(g z):'b else ARB” THEN
  rw [FUN_EQ_THM] THEN
  METIS_TAC []
QED

Theorem CARD_EXP_MUL :
    !(s:'a->bool) (t:'b->bool) (u:'c->bool).
        s ** (t *_c u) =_c (s ** t) ** u
Proof
    rw [Once cardeq_SYM, set_exp_product]
QED

Theorem CARD_EXP_POWERSET :
    !s :'a -> bool. univ(:bool) ** s =_c {t | t SUBSET s}
Proof
    GEN_TAC
 >> REWRITE_TAC [exp_c, EQ_C_BIJECTIONS, IN_UNIV]
 >> qexistsl_tac [‘\P. {x | x IN s /\ P x}’,
                  ‘\t x. if x IN s then x IN t else ARB’]
 >> SIMP_TAC std_ss [GSPECIFICATION]
 >> SET_TAC []
QED

Theorem CARD_EXP_CANTOR :
    !s :'a -> bool. s <_c univ(:bool) ** s
Proof
  GEN_TAC THEN
  TRANS_TAC CARD_LTE_TRANS “{t :'a->bool | t SUBSET s}” THEN
  REWRITE_TAC[CANTOR_THM] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CARD_EXP_POWERSET]
QED

Theorem CARD_EXP_ABSORB :
    !(s :'a -> bool) (t :'b -> bool).
        INFINITE t /\ univ(:bool) <=_c s /\ s <=_c univ(:bool) ** t
        ==> s ** t =_c univ(:bool) ** t
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  ASM_SIMP_TAC std_ss [CARD_LE_EXP_LEFT, CARD_LE_REFL] THEN
  TRANS_TAC CARD_LE_TRANS “(univ(:bool) ** t) ** (t:'b->bool)” THEN
  ASM_SIMP_TAC std_ss[CARD_LE_EXP_LEFT] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  TRANS_TAC CARD_EQ_TRANS “univ(:bool) ** ((t:'b->bool) *_c t)” THEN
  SIMP_TAC std_ss[ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EXP_MUL] THEN
  MATCH_MP_TAC CARD_EXP_CONG THEN
  ASM_SIMP_TAC std_ss[CARD_SQUARE_INFINITE, CARD_EQ_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* Lemmas about countability.                                                *)
(* ------------------------------------------------------------------------- *)

Theorem NUM_COUNTABLE = num_countable

val COUNTABLE_ALT_cardleq = store_thm
  ("COUNTABLE_ALT_cardleq",
 ``!s. COUNTABLE s <=> s <=_c univ(:num)``,
  REWRITE_TAC[COUNTABLE, ge_c]);

val COUNTABLE_CASES = store_thm ("COUNTABLE_CASES",
  ``!s. COUNTABLE s <=> FINITE s \/ s =_c univ(:num)``,
    GEN_TAC
 >> ONCE_REWRITE_TAC[COUNTABLE_ALT_cardleq, FINITE_CARD_LT]
 >> METIS_TAC [CARD_LE_LT]);

(* changed ‘t:'a->bool’ to ‘t:'b->bool’ *)
Theorem CARD_LE_COUNTABLE :
    !s:'a->bool t:'b->bool. COUNTABLE t /\ s <=_c t ==> COUNTABLE s
Proof
    REWRITE_TAC [COUNTABLE, ge_c]
 >> rpt STRIP_TAC
 >> KNOW_TAC ``?(t :'b -> bool).
      (s :'a -> bool) <=_c t /\ t <=_c univ((:num) :num itself)``
 >- (EXISTS_TAC ``t:'b->bool`` >> ASM_REWRITE_TAC[])
 >> METIS_TAC [CARD_LE_TRANS]
QED

Theorem countable_setexp:
  countable (A ** B) <=>
    B = {} \/ FINITE B /\ countable A \/ A =~ {()} \/ A = {}
Proof
  rw[EQ_IMP_THM] >~
  [‘countable (A ** {})’]
  >- (resolve_then (Pos hd) irule EMPTY_set_exp_CARD (iffRL countable_cardeq) >>
      simp[COUNTABLE_COUNT]) >~
  [‘countable ({} ** B)’]
  >- (Cases_on ‘B = {}’
      >- (simp[] >>
          resolve_then (Pos hd) irule EMPTY_set_exp_CARD
                       (iffRL countable_cardeq) >>
          simp[COUNTABLE_COUNT]) >>
      simp[EMPTY_set_exp]) >~
  [‘FINITE B /\ countable A’]
  >- (Cases_on ‘B = {}’ >> simp[] >> Cases_on ‘A = {}’ >> simp[] >>
      Cases_on ‘A =~ {()}’ >> simp[] >>
      Cases_on ‘FINITE B’ >> simp[]
      >- metis_tac[FINITE_EXPONENT_SETEXP_UNCOUNTABLE] >>
      ‘~countable (POW B)’ by metis_tac[infinite_pow_uncountable] >>
      ‘~countable (count 2 ** B)’
        by metis_tac[countable_cardeq, POW_TWO_set_exp] >>
      pop_assum mp_tac >> simp[] >>
      ‘count 2 ** B <<= A ** B’ suffices_by metis_tac[CARD_LE_COUNTABLE] >>
      irule set_exp_cardle_cong >> simp[] >> metis_tac[FINITE_012]) >~
  [‘A =~ {()}’]
  >- gvs[CARD1_SING, SING_set_exp] >>
  metis_tac[FINITE_EXPONENT_SETEXP_COUNTABLE]
QED

(* NOTE: Changed the type of ‘t’ to ‘:'b->bool’ (was: 'a->bool) *)
Theorem CARD_EQ_COUNTABLE :
    !s:'a->bool t:'b->bool. COUNTABLE t /\ s =_c t ==> COUNTABLE s
Proof
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]
QED

(* NOTE: Changed the type of ‘t’ to ‘:'b->bool’ (was: 'a->bool) *)
Theorem CARD_COUNTABLE_CONG :
    !s:'a->bool t:'b->bool. s =_c t ==> (COUNTABLE s <=> COUNTABLE t)
Proof
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]
QED

val COUNTABLE_RESTRICT = store_thm ("COUNTABLE_RESTRICT",
 ``!s P. COUNTABLE s ==> COUNTABLE {x | x IN s /\ P x}``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val FINITE_IMP_COUNTABLE = store_thm ("FINITE_IMP_COUNTABLE",
 ``!s. FINITE s ==> COUNTABLE s``,
  SIMP_TAC std_ss [FINITE_CARD_LT, Once lt_c, COUNTABLE, ge_c]);

val COUNTABLE_IMAGE = store_thm ("COUNTABLE_IMAGE",
 ``!f:'a->'b s. COUNTABLE s ==> COUNTABLE (IMAGE f s)``,
  SIMP_TAC std_ss [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
  KNOW_TAC ``IMAGE (f:'a->'b) s <=_c s /\ s <=_c univ(:num)`` THENL
  [ASM_SIMP_TAC std_ss [CARD_LE_IMAGE], METIS_TAC [CARD_LE_TRANS]]);

val COUNTABLE_IMAGE_INJ_GENERAL = store_thm ("COUNTABLE_IMAGE_INJ_GENERAL",
 ``!(f:'a->'b) A s.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
        COUNTABLE A
        ==> COUNTABLE {x | x IN s /\ f(x) IN A}``,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC ``!x y. x IN s /\ y IN s /\ ((f:'a->'b) x = f y) ==>
                (x = y)`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:'b->'a``) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC ``IMAGE (g:'b->'a) A`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE] THEN ASM_SET_TAC[]);

Theorem COUNTABLE_IMAGE_INJ_EQ:
  !(f:'a->'b) s.
    (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) ==>
    (COUNTABLE(IMAGE f s) <=> COUNTABLE s)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[AND_IMP_INTRO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COUNTABLE_IMAGE_INJ_GENERAL) THEN
  csimp[IMAGE_IN]
QED

val COUNTABLE_IMAGE_INJ = store_thm ("COUNTABLE_IMAGE_INJ",
 ``!(f:'a->'b) A.
        (!x y. (f(x) = f(y)) ==> (x = y)) /\
         COUNTABLE A
         ==> COUNTABLE {x | f(x) IN A}``,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [``f:'a->'b``, ``A:'b->bool``, ``UNIV:'a->bool``]
    COUNTABLE_IMAGE_INJ_GENERAL) THEN SIMP_TAC std_ss [IN_UNIV]);

val COUNTABLE_EMPTY = store_thm ("COUNTABLE_EMPTY",
 ``COUNTABLE {}``,
  REWRITE_TAC [COUNTABLE, ge_c, le_c, NOT_IN_EMPTY]);

val COUNTABLE_INTER = store_thm ("COUNTABLE_INTER",
 ``!s t. COUNTABLE s \/ COUNTABLE t ==> COUNTABLE (s INTER t)``,
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val COUNTABLE_UNION_IMP = store_thm ("COUNTABLE_UNION_IMP",
 ``!s t:'a->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s UNION t)``,
  REWRITE_TAC[COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
  KNOW_TAC ``s UNION t <=_c ((s:'a->bool) +_c (t:'a->bool)) /\
             ((s:'a->bool) +_c (t:'a->bool)) <=_c univ(:num)`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD2_ABSORB_LE, num_INFINITE, UNION_LE_ADD_C]);

val COUNTABLE_UNION = store_thm ("COUNTABLE_UNION",
 ``!s t:'a->bool. COUNTABLE(s UNION t) <=> COUNTABLE s /\ COUNTABLE t``,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[COUNTABLE_UNION_IMP] THEN
  DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val COUNTABLE_SING = store_thm ("COUNTABLE_SING",
 ``!x. COUNTABLE {x}``,
  REWRITE_TAC [COUNTABLE, ge_c, le_c, IN_SING, IN_UNIV] THEN
  METIS_TAC []);

val COUNTABLE_INSERT = store_thm ("COUNTABLE_INSERT",
 ``!x s. COUNTABLE(x INSERT s) <=> COUNTABLE s``,
  ONCE_REWRITE_TAC[SET_RULE ``x INSERT s = {x} UNION s``] THEN
  REWRITE_TAC[COUNTABLE_UNION, COUNTABLE_SING]);

val COUNTABLE_DELETE = store_thm ("COUNTABLE_DELETE",
 ``!x:'a s. COUNTABLE(s DELETE x) <=> COUNTABLE s``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``(x:'a) IN s`` THEN
  ASM_SIMP_TAC std_ss [SET_RULE ``~(x IN s) ==> (s DELETE x = s)``] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``COUNTABLE((x:'a) INSERT (s DELETE x))`` THEN CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT], AP_TERM_TAC THEN ASM_SET_TAC[]]);

val COUNTABLE_DIFF_FINITE = store_thm ("COUNTABLE_DIFF_FINITE",
 ``!s t. FINITE s ==> (COUNTABLE(t DIFF s) <=> COUNTABLE t)``,
  SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s. (!t. COUNTABLE (t DIFF s) <=> COUNTABLE t) =
                          (\s. !t. COUNTABLE (t DIFF s) <=> COUNTABLE t) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [DIFF_EMPTY, SET_RULE ``s DIFF (x INSERT t) = (s DIFF t) DELETE x``,
           COUNTABLE_DELETE]);

val COUNTABLE_CROSS = store_thm ("COUNTABLE_CROSS",
  ``!s t. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s CROSS t)``,
    rpt GEN_TAC
 >> REWRITE_TAC [COUNTABLE, ge_c]
 >> STRIP_TAC
 >> MATCH_MP_TAC (Q.SPEC `UNIV`
                   (INST_TYPE [``:'c`` |-> ``:num``]
                     (ISPECL [``s :'a set``, ``t :'b set``] CARD_MUL2_ABSORB_LE)))
 >> ASM_REWRITE_TAC [num_INFINITE]);

val COUNTABLE_AS_IMAGE_SUBSET = store_thm ("COUNTABLE_AS_IMAGE_SUBSET",
 ``!s. COUNTABLE s ==> ?f. s SUBSET (IMAGE f univ(:num))``,
  REWRITE_TAC[COUNTABLE, ge_c, LE_C, SUBSET_DEF, IN_IMAGE] THEN MESON_TAC[]);

val COUNTABLE_AS_IMAGE_SUBSET_EQ = store_thm ("COUNTABLE_AS_IMAGE_SUBSET_EQ",
 ``!s:'a->bool. COUNTABLE s <=> ?f. s SUBSET (IMAGE f univ(:num))``,
  REWRITE_TAC[COUNTABLE, ge_c, LE_C, SUBSET_DEF, IN_IMAGE] THEN MESON_TAC[]);

val COUNTABLE_AS_IMAGE = store_thm ("COUNTABLE_AS_IMAGE",
 ``!s:'a->bool. COUNTABLE s /\ ~(s = {}) ==> ?f. (s = IMAGE f univ(:num))``,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC ``a:'a`` o
    REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP COUNTABLE_AS_IMAGE_SUBSET) THEN
  DISCH_THEN(X_CHOOSE_TAC ``f:num->'a``) THEN
  EXISTS_TAC ``\n. if (f:num->'a) n IN s then f n else a`` THEN
  ASM_SET_TAC[]);

val FORALL_COUNTABLE_AS_IMAGE = store_thm ("FORALL_COUNTABLE_AS_IMAGE",
 ``(!d. COUNTABLE d ==> P d) <=> P {} /\ (!f. P(IMAGE f univ(:num)))``,
  MESON_TAC[COUNTABLE_AS_IMAGE, COUNTABLE_IMAGE, NUM_COUNTABLE,
            COUNTABLE_EMPTY]);

val COUNTABLE_AS_INJECTIVE_IMAGE = store_thm ("COUNTABLE_AS_INJECTIVE_IMAGE",
 ``!s. COUNTABLE s /\ INFINITE s
       ==> ?f. (s = IMAGE f univ(:num)) /\ (!m n. (f(m) = f(n)) ==> (m = n))``,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[INFINITE_CARD_LE, COUNTABLE, ge_c] THEN
  SIMP_TAC std_ss [CARD_LE_ANTISYM, eq_c] THEN SET_TAC[]);

Theorem COUNTABLE_BIGUNION = bigunion_countable

val IN_ELIM_PAIR_THM = store_thm ("IN_ELIM_PAIR_THM",
 ``!P a b. (a,b) IN {(x,y) | P x y} <=> P a b``,
  SRW_TAC [][]);

Theorem COUNTABLE_PRODUCT_DEPENDENT:
  !f:'a->'b->'c s t.
    COUNTABLE s /\ (!x. x IN s ==> COUNTABLE(t x)) ==>
    COUNTABLE {f x y | x IN s /\ y IN (t x)}
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “{(f:'a->'b->'c) x y | x IN s /\ y IN (t x)} =
                 IMAGE (λ(x,y). f x y) {(x,y) | x IN s /\ y IN (t x)}”
  SUBST1_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, IN_IMAGE, EXISTS_PROD, IN_ELIM_PAIR_THM] THEN
    SET_TAC[],
    MATCH_MP_TAC COUNTABLE_IMAGE THEN POP_ASSUM MP_TAC] THEN
  CONV_TAC $ LAND_CONV  $ REWRITE_CONV [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC “f:num->'a”) MP_TAC) THEN
  DISCH_THEN (MP_TAC o SIMP_RULE std_ss [RIGHT_IMP_EXISTS_THM]) THEN
  SIMP_TAC std_ss [SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC “g:'a->num->'b”) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC “IMAGE (λ(m,n). (f:num->'a) m,(g:'a->num->'b)(f m) n)
                    (univ(:num) CROSS univ(:num))” THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, COUNTABLE_CROSS, NUM_COUNTABLE] THEN
  SIMP_TAC std_ss [SUBSET_DEF, FORALL_IN_BIGUNION] THEN
  SIMP_TAC std_ss [IN_IMAGE, FORALL_PROD, IN_ELIM_PAIR_THM,
              EXISTS_PROD, IN_CROSS, IN_UNIV] THEN
  ASM_SET_TAC[]
QED

(* cf. listTheory.INFINITE_LIST_UNIV |- INFINITE univ(:'a list) *)
Theorem COUNTABLE_LIST_UNIV :
    countable univ(:'a) ==> countable univ(:'a list)
Proof
    rw [UNIV_list]
 >> MP_TAC (INST [“A :'a set” |-> “univ(:'a)”] list_BIGUNION_EXP)
 >> qmatch_abbrev_tac ‘list univ(:'a) =~ s ==> _’
 >> DISCH_TAC
 >> Suff ‘countable s’
 >- (MP_TAC (Q.SPEC ‘s’ (INST_TYPE [“:'b” |-> “:num # (num -> 'a)”]
                          (ISPEC “list univ(:'a)” CARD_EQ_COUNTABLE))) \\
     rw [])
 >> qunabbrev_tac ‘s’
 >> MATCH_MP_TAC COUNTABLE_BIGUNION >> rw []
 >> MATCH_MP_TAC COUNTABLE_CROSS >> rw []
 >> rw [countable_setexp]
QED

Theorem COUNTABLE_LIST_UNIV' :
    FINITE univ(:'a) ==> countable univ(:'a list)
Proof
    DISCH_TAC
 >> MATCH_MP_TAC COUNTABLE_LIST_UNIV
 >> MATCH_MP_TAC FINITE_IMP_COUNTABLE >> art []
QED

Definition BIGPRODi_def:
  BIGPRODi (A : 'i -> ('a -> bool) option) =
  {tup : 'i -> 'a option |
   (!i. A i = NONE ==> tup i = NONE) /\
   !i s. A i = SOME s ==> ?a. tup i = SOME a /\ a IN s
  }
End

(* A^0 = 1 *)
Theorem BIGPRODi_KNONE[simp]:
  BIGPRODi (K NONE) = {K NONE}
Proof
  simp[BIGPRODi_def, EXTENSION, FUN_EQ_THM]
QED

Definition fnOfSet_def:
  fnOfSet s k = if ?!v. (k,v) IN s then SOME (@v. (k,v) IN s) else NONE
End

Theorem fnOfSet_SING[simp]:
  fnOfSet {(k,v)} = (K NONE)(| k |-> SOME v |)
Proof
  simp[fnOfSet_def, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> gs[]
QED

Theorem BIGPRODi_SING_EQ:
  BIGPRODi (fnOfSet {(i,s)}) = { (K NONE)(| i |-> SOME a |) | a IN s }
Proof
  simp[BIGPRODi_def, combinTheory.APPLY_UPDATE_THM, Once EXTENSION] >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  qx_gen_tac ‘tup’ >> simp[EQ_IMP_THM] >> rw[] >~
  [‘tup i = SOME a’] >- (first_assum $ irule_at Any >> metis_tac[]) >~
  [‘tup j = NONE’] >- metis_tac[] >>
  metis_tac[]
QED

Theorem BIGPRODi_SING_CEQ:
  BIGPRODi (fnOfSet {(i,s)}) =~ s
Proof
  simp[BIGPRODi_SING_EQ, cardeq_def, BIJ_IFF_INV, PULL_EXISTS] >>
  qexistsl_tac [‘λx. THE (x i)’, ‘λa j. if j = i then SOME a else NONE’] >>
  simp[combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] >> metis_tac[]
QED

Theorem BIGPRODi_pair:
  i <> j ==>
  BIGPRODi (K NONE)(| i |-> SOME A1; j |-> SOME A2|) =~ A1 CROSS A2
Proof
  strip_tac >>
  simp[BIGPRODi_def, cardeq_def, BIJ_IFF_INV, FORALL_PROD, PULL_EXISTS] >>
  qexistsl_tac [‘λt. (THE (t i), THE (t j))’,
               ‘λp k. if k = i then SOME (FST p)
                      else if k = j then SOME (SND p) else NONE’] >>
  rw[] >~
  [‘THE (tup i) IN A’] >- (first_x_assum $ qspec_then ‘i’ mp_tac >>
                           gs[combinTheory.APPLY_UPDATE_THM, PULL_EXISTS]) >~
  [‘THE (tup i) IN A’] >- (first_x_assum $ qspec_then ‘i’ mp_tac >>
                           gs[combinTheory.APPLY_UPDATE_THM, PULL_EXISTS]) >>
  gs[combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[] >>
  gs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem BIGPRODi_EQ_EMPTY:
  BIGPRODi Af = {} <=> ?i. Af i = SOME {}
Proof
  simp[BIGPRODi_def] >> Cases_on ‘!i. Af i = NONE’ >> simp[]
  >- (simp[EXTENSION] >> qexists_tac ‘K NONE’ >> simp[]) >> gs[] >>
  simp[Once EXTENSION] >> eq_tac >>
  rpt strip_tac >> gvs[] >~
  [‘Af j = SOME {}’] >- (disj2_tac >> qexists_tac ‘j’ >> simp[]) >>
  CCONTR_TAC >>
  qpat_x_assum ‘!x. _’ mp_tac >> simp[] >>
  qexists_tac ‘λj. OPTION_MAP CHOICE (Af j)’ >>
  simp[SF DISJ_ss] >> gs[] >> metis_tac[CHOICE_DEF, SOME_11]
QED

Definition BIGPROD_def:
  BIGPROD (A : ('a -> bool) -> bool) =
  BIGPRODi (λa. if a IN A then SOME a else NONE)
End

Theorem BIGPROD_thm:
  BIGPROD A =
  { tup : ('a -> bool) -> 'a option |
    (!s. s IN A ==> ?a. tup s = SOME a /\ a IN s) /\
    (!s. s NOTIN A ==> tup s = NONE) }
Proof
  simp[BIGPROD_def, BIGPRODi_def, FORALL_AND_THM, CONJ_COMM]
QED

Theorem BIGPROD_pair:
  A1 <> A2 ==>
  BIGPROD { A1; A2 } =~ A1 CROSS A2
Proof
  strip_tac >> simp[BIGPROD_def] >>
  ‘(\a. if a = A1 \/ a = A2 then SOME a else NONE) =
   (K NONE)(| A1 |-> SOME A1; A2 |-> SOME A2|)’
    by simp[Once FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, AllCaseEqs(),
            SF DISJ_ss] >>
  simp[BIGPRODi_pair]
QED

Theorem BIGPROD_SING:
  BIGPROD {A} =~ A
Proof
  simp[cardeq_def, BIGPROD_thm, BIJ_IFF_INV] >>
  qexists_tac ‘λt. THE (t A)’ >> simp[PULL_EXISTS] >>
  qexists_tac ‘\a s. if s = A then SOME a else NONE’ >> rw[] >>
  simp[Once FUN_EQ_THM] >> rw[]
QED

Theorem BIGPROD_ONE:
  BIGPROD {} =~ {()}
Proof
  simp[BIGPROD_thm, cardeq_def]>> qexists_tac ‘K ()’ >>
  simp[BIJ_IFF_INV] >> qexists_tac ‘K (K NONE)’ >> simp[] >>
  rpt strip_tac >> simp[FUN_EQ_THM]
QED

Theorem BIGPROD_EQ_EMPTY[simp]:
  BIGPROD As = {} <=> {} IN As
Proof
  simp[BIGPROD_def, BIGPRODi_EQ_EMPTY]
QED

Theorem image_thms[simp,local]:
  IMAGE OUTL (IMAGE INL A) = A /\
  IMAGE OUTR (IMAGE INR B) = B /\
  ((!x. x IN AB ==> ISL x) ==> (IMAGE INL (IMAGE OUTL AB) = AB)) /\
  ((!x. x IN AB ==> ISR x) ==> (IMAGE INR (IMAGE OUTR AB) = AB))
Proof
  rw[EXTENSION, PULL_EXISTS] >> csimp[INR, INL]
QED

Theorem BIGPROD_CONS:
  A CROSS BIGPROD As =~ BIGPROD (IMAGE INL A INSERT IMAGE (IMAGE INR) As)
Proof
  Cases_on ‘A = {}’ >> simp[iffRL BIGPROD_EQ_EMPTY, CARDEQ_0] >>
  Cases_on ‘{} IN As’ >> simp[iffRL BIGPROD_EQ_EMPTY, CARDEQ_0] >>
  simp[BIGPROD_thm, BIJ_IFF_INV, cardeq_def, FORALL_PROD] >>
  qexists_tac ‘λ(p : 'a # (('b -> bool) -> 'b option)) (s: 'a + 'b -> bool).
                 if s = EMPTY then NONE : ('a + 'b) option
                 else if (!x. x IN s ==> ISL x) then
                   if IMAGE OUTL s = A then SOME (INL (FST p)) else NONE
                 else if (!x. x IN s ==> ISR x) /\ IMAGE OUTR s IN As then
                   SOME (INR (THE (SND p (IMAGE OUTR s))))
                 else NONE’ >>
  rw[] >> simp[AllCaseEqs(), PULL_EXISTS]
  >- (metis_tac[THE_DEF, MEMBER_NOT_EMPTY])
  >- (rename [‘s = {}’, ‘s <> IMAGE INL A’] >>
      pop_assum mp_tac >> rw[]
      >- (qpat_x_assum ‘s <> IMAGE INL _’ mp_tac >>
          csimp[EXTENSION, PULL_EXISTS, sumTheory.INL]) >>
      first_x_assum $ qspec_then ‘IMAGE OUTR s’ mp_tac >> simp[]) >>
  qexists_tac ‘λtup. (OUTL (THE (tup (IMAGE INL A))),
                      (λB. if B IN As then
                             SOME (OUTR (THE (tup (IMAGE INR B))))
                           else NONE))’ >> rw[] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
  >- (first_x_assum drule >> simp[PULL_EXISTS])
  >- (simp[Once FUN_EQ_THM] >> rw[]
      >- gs[]
      >- metis_tac[MEMBER_NOT_EMPTY]
      >- metis_tac[MEMBER_NOT_EMPTY]
      >- (last_x_assum drule >> simp[PULL_EXISTS]))
  >- (simp[Once FUN_EQ_THM] >> qx_gen_tac ‘AB’ >> rw[]
      >- gs[]
      >- (first_x_assum irule >> rpt strip_tac >> gvs[PULL_EXISTS] >>
          metis_tac[MEMBER_NOT_EMPTY])
      >- (first_x_assum drule >> simp[PULL_EXISTS])
      >- (gs[] >> first_x_assum irule >> rpt strip_tac >> gvs[]))
QED

Theorem tupNONE_IN_BIGPRODi:
  tup IN BIGPRODi Af ==> (tup i = NONE <=> Af i = NONE)
Proof
  simp[BIGPRODi_def, EQ_IMP_THM] >> rpt strip_tac >>
  first_x_assum $ qspec_then ‘i’ mp_tac >> simp[] >>
  Cases_on ‘Af i’ >> simp[]
QED

Theorem BIGPRODi_11[simp]:
  (!i. Af i <> SOME {}) /\ (!i. Bf i <> SOME ({}:'b set)) ==>
  (BIGPRODi Af = BIGPRODi Bf <=> Af = Bf)
Proof
  rpt strip_tac >> simp[EQ_IMP_THM] >>
  simp[Once EXTENSION] >> strip_tac >>
  simp[FUN_EQ_THM] >> qx_gen_tac ‘j’ >>
  Cases_on ‘Af j = NONE \/ Bf j = NONE’
  >- (‘?t. t IN BIGPRODi Af’
        suffices_by metis_tac[tupNONE_IN_BIGPRODi] >>
      simp[MEMBER_NOT_EMPTY] >> simp[BIGPRODi_EQ_EMPTY]) >> gs[] >>
  ‘(?s1. Af j = SOME s1) /\ (?s2. Bf j = SOME s2)’
    by (map_every Cases_on [‘Af j’, ‘Bf j’] >> gs[]) >> simp[] >>
  CCONTR_TAC >>
  wlog_tac ‘?e. e IN s1 /\ e NOTIN s2’ [‘s1’, ‘s2’, ‘Bf’, ‘Af’]
  >- (gs[] >>
      ‘!A B. (!e:'b. e NOTIN A \/ e IN B) <=> A SUBSET B’
        by metis_tac[SUBSET_DEF] >> gs[] >>
      first_x_assum $ qspecl_then [‘s2’, ‘s1’, ‘Af’, ‘Bf’] mp_tac >> simp[] >>
      metis_tac[SUBSET_ANTISYM]) >>
  ‘!tup. tup IN BIGPRODi Bf ==> tup j <> SOME e’
    by (simp[BIGPRODi_def] >> rpt strip_tac >>
        first_x_assum $ qspec_then ‘j’ mp_tac >> simp[]) >>
  ‘?tup. tup IN BIGPRODi Af /\ tup j = SOME e’ suffices_by metis_tac[] >>
  ‘?tup0. tup0 IN BIGPRODi Af’
    by simp[MEMBER_NOT_EMPTY, BIGPRODi_EQ_EMPTY] >>
  qexists_tac ‘tup0(| j |-> SOME e |)’ >>
  pop_assum mp_tac >> REWRITE_TAC [BIGPRODi_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >> rw[AllCaseEqs()] >>
  metis_tac[SOME_11]
QED

Theorem cardeq_addUnum:
  INFINITE (univ(:'a)) ==> univ(:num + 'a) =~ univ(:'a)
Proof
  strip_tac >> irule cardleq_ANTISYM >>
  ‘univ(:'a) <<= univ(:num + 'a)’
    by (simp[cardleq_def]>> qexists_tac ‘INR’ >>
        simp[INJ_DEF]) >> simp[] >>
  ‘univ(:num) <<= univ(:'a)’ by gs[INFINITE_Unum] >>
  simp[disjUNION_UNIV, CARD_ADD_ABSORB_LE]
QED

Theorem wellorder_destWO =
        wellorder_ABSREP |> cj 2
                         |> Q.SPEC ‘destWO r’
                         |> REWRITE_RULE [mkWO_destWO]

Theorem cardleq_copy_wellorders:
  univ(:'a) <<= univ(:'b) ==>
  !w1 : 'a wellorder. ?w2: 'b wellorder. orderiso w1 w2
Proof
  simp[orderiso_def, cardleq_def, INJ_IFF] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  qx_gen_tac ‘w1’ >> qabbrev_tac ‘W2 = {(f x, f y) | (x,y) IN destWO w1 }’ >>
  ‘wellorder (destWO w1)’ by simp[wellorder_destWO] >>
  ‘wellorder W2’
    by (‘W2 = IMAGE (f ## f) (destWO w1)’
          by simp[Abbr‘W2’, EXTENSION, EXISTS_PROD] >>
        simp[] >> irule INJ_preserves_wellorder >>
        simp[wellorder_destWO] >> qexists_tac ‘UNIV’ >>
        simp[INJ_IFF]) >>
  qexistsl_tac [‘mkWO W2’, ‘f’] >>
  ‘elsOf (mkWO W2) = { f x | x IN elsOf w1}’
    by (simp[elsOf_def, Abbr‘W2’, destWO_mkWO, domain_def, range_def] >>
        dsimp[EXTENSION] >> metis_tac[]) >>
  simp[PULL_EXISTS] >>
  simp[destWO_mkWO] >> simp[strict_def, Abbr‘W2’]
QED

(* ------------------------------------------------------------------------- *)
(* Misc lemmas from HOL-Light's card.ml                                      *)
(* ------------------------------------------------------------------------- *)

Theorem MUL_C_UNIV :
    univ(:'a) *_c univ(:'b) = univ(:'a # 'b)
Proof
  REWRITE_TAC[CROSS_UNIV]
QED

Theorem CARD_MUL_FINITE_EQ :
    !s t. FINITE (s *_c t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t
Proof
  REWRITE_TAC [FINITE_CROSS_EQ]
QED

Theorem INJECTIVE_ON_ALT :
    !P (f :'a -> 'b).
        (!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
        (!x y. P x /\ P y ==> (f x = f y <=> x = y))
Proof
  MESON_TAC[]
QED

Theorem INJECTIVE_ALT :
    !f :'a -> 'b. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)
Proof
  MESON_TAC[]
QED

val _ = export_theory()
