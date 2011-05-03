structure llistScript =
struct

open HolKernel boolLib Parse bossLib

open BasicProvers boolSimps markerLib;

val _ = new_theory "llist";


(* ----------------------------------------------------------------------
    The representing type is :num -> 'a option
   ---------------------------------------------------------------------- *)

val lrep_ok_def = Define`
  lrep_ok f =
     ?P. (!g. P g ==>
              (g = (\n. NONE)) \/
              ?h t. P t /\ (g = (\n. if n = 0 then SOME h else t(n - 1)))) /\
         P f
`;

val type_inhabited = prove(
  ``?f. lrep_ok f``,
  Q.EXISTS_TAC `\n. NONE` THEN SRW_TAC [][lrep_ok_def] THEN
  Q.EXISTS_TAC `(=) (\n.NONE)` THEN SRW_TAC [][]);

val llist_tydef =
  new_type_definition ("llist", type_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "llist_absrep",
  ABS = "llist_abs",
  REP = "llist_rep",
  tyax = llist_tydef};

val llist_absrep = CONJUNCT1 repabs_fns
val llist_repabs = CONJUNCT2 repabs_fns

val lrep_ok_llist_rep = prove(
  ``lrep_ok (llist_rep f)``,
  SRW_TAC [][llist_repabs, llist_absrep]);
val _ = BasicProvers.augment_srw_ss [rewrites [lrep_ok_llist_rep]]

val llist_abs_11 = prove(
  ``lrep_ok r1 /\ lrep_ok r2 ==> ((llist_abs r1 = llist_abs r2) = (r1 = r2))``,
  SRW_TAC [][llist_repabs, EQ_IMP_THM] THEN METIS_TAC []);

val llist_rep_11 = prove(
  ``(llist_rep t1 = llist_rep t2) = (t1 = t2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``llist_abs``) THEN SRW_TAC [][llist_absrep]);

val llist_repabs' = #1 (EQ_IMP_RULE (SPEC_ALL llist_repabs))

val LNIL = new_definition("LNIL", ``LNIL = llist_abs (\n. NONE)``);
val LCONS = new_definition(
  "LCONS",
  ``LCONS h t = llist_abs (\n. if n = 0 then SOME h
                               else llist_rep t (n - 1))``
);

val lrep_ok_rules = prove(
  ``lrep_ok (\n. NONE) /\
    (lrep_ok f ==> lrep_ok (\n. if n = 0 then SOME h else f (n - 1)))``,
  SRW_TAC [][lrep_ok_def] THENL [
    Q.EXISTS_TAC `(=) (\n. NONE)` THEN SRW_TAC [][],
    Q.EXISTS_TAC
      `\f'. P f' \/ (f' = (\n. (if n = 0 then SOME h else f (n - 1))))` THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val lrep_ok_coinduction = prove(
  ``(!f. P f ==>
         (f = (\n. NONE)) \/
         ?h t. P t /\ (f = (\n. if n = 0 then SOME h else t(n - 1)))) ==>
    !f. P f ==> lrep_ok f``,
  SRW_TAC [][lrep_ok_def] THEN Q.EXISTS_TAC `P` THEN SRW_TAC [][]);

val lrep_ok_cases = prove(
  ``lrep_ok f =
       (f = \n. NONE) \/
       (?h t. lrep_ok t /\ (f = \n. if n = 0 then SOME h else t (n - 1)))``,
  SIMP_TAC (srw_ss() ++ DNF_ss)[EQ_IMP_THM, lrep_ok_rules] THEN
  SRW_TAC [][lrep_ok_def] THEN RES_TAC THEN SRW_TAC [][] THEN
  DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h`,`t`] THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `P` THEN SRW_TAC [][]);

val llist_rep_LCONS = store_thm(
  "llist_rep_LCONS",
  ``llist_rep (LCONS h t) =
        \n. if n = 0 then SOME h else llist_rep t (n - 1)``,
  SRW_TAC [][LCONS, GSYM llist_repabs] THEN
  MATCH_MP_TAC (CONJUNCT2 lrep_ok_rules) THEN SRW_TAC [][]);

val LHD = new_definition("LHD", ``LHD ll = llist_rep ll 0``);
val LTL = new_definition(
  "LTL",
  ``LTL ll = case LHD ll of
                NONE -> NONE
             || SOME _ -> SOME (llist_abs (\n. llist_rep ll (n + 1)))``
);

val LHD_LCONS = store_thm(
  "LHD_LCONS",
  ``LHD (LCONS h t) = SOME h``,
  SRW_TAC [][LHD, llist_rep_LCONS]);
val LTL_LCONS = store_thm(
  "LTL_LCONS",
  ``LTL (LCONS h t) = SOME t``,
  SRW_TAC [ETA_ss][LTL, LHD_LCONS, llist_rep_LCONS, llist_absrep]);

(*---------------------------------------------------------------------------*)
(* Syntax for lazy lists, similar to lists                                   *)
(*---------------------------------------------------------------------------*)

val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "[|"], rightdelim = [TOK "|]"],
                      cons = "LCONS", nilstr = "LNIL",
                      block_info = (PP.INCONSISTENT, 0)};
val _ = TeX_notation {hol = "[|", TeX = ("\\HOLTokenLeftDenote{}", 1)}
val _ = TeX_notation {hol = "|]", TeX = ("\\HOLTokenRightDenote{}", 1)}

val _ = add_rule {term_name = "LCONS", fixity = Infixr 490,
                  pp_elements = [TOK ":::", BreakSpace(0,2)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 2))};


val LHDTL_CONS_THM = store_thm(
  "LHDTL_CONS_THM",
  ``!h t. (LHD (LCONS h t) = SOME h) /\ (LTL (LCONS h t) = SOME t)``,
  SRW_TAC [][LHD_LCONS, LTL_LCONS]);

val lrep_inversion = prove(
  ``lrep_ok f ==> (f = \n. NONE) \/
                  (?h t. lrep_ok t /\ (f = \n. if n = 0 then SOME h
                                               else t (n - 1)))``,
  SRW_TAC [][lrep_ok_def] THEN RES_TAC THENL [
    SRW_TAC [][],
    DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h`, `t`] THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `P` THEN SRW_TAC [][]
  ]);

val forall_llist = prove(
  ``(!l. P l) = (!r. lrep_ok r ==> P (llist_abs r))``,
  SRW_TAC [][EQ_IMP_THM] THEN
  ONCE_REWRITE_TAC [GSYM llist_absrep] THEN
  SRW_TAC [][]);

val llist_CASES = store_thm(
  "llist_CASES",
  ``!l. (l = LNIL) \/ (?h t. l = LCONS h t)``,
  SIMP_TAC (srw_ss() ++ ETA_ss) [LNIL,LCONS,forall_llist,llist_abs_11,
                                 lrep_ok_rules] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC lrep_inversion THENL [
    SRW_TAC [][],
    DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h`, `llist_abs t`] THEN
    SRW_TAC [][llist_repabs']
  ]);

val LHD_THM = store_thm(
  "LHD_THM",
  ``(LHD LNIL = NONE) /\ (!h t. LHD (LCONS h t) = SOME h)``,
  SRW_TAC [][LHDTL_CONS_THM] THEN
  SRW_TAC [][LHD, LNIL, llist_repabs', lrep_ok_rules]);
val _ = export_rewrites ["LHD_THM"]

val LTL_THM = store_thm(
  "LTL_THM",
  ``(LTL LNIL = NONE) /\ (!h t. LTL (LCONS h t) = SOME t)``,
  SRW_TAC [][LHDTL_CONS_THM] THEN
  SRW_TAC [][LTL, LNIL, llist_repabs', lrep_ok_rules, LHD]);
val _ = export_rewrites ["LTL_THM"]

val LCONS_NOT_NIL = store_thm(
  "LCONS_NOT_NIL",
  ``!h t. ~(LCONS h t = LNIL) /\ ~(LNIL = LCONS h t)``,
  SRW_TAC [][LCONS, LNIL, FUN_EQ_THM] THEN STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [llist_repabs', lrep_ok_rules] THEN
  POP_ASSUM (ASSUME_TAC o C AP_THM ``0``) THEN
  FULL_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LCONS_NOT_NIL"]

val LCONS_11 = store_thm(
  "LCONS_11",
  ``!h1 t1 h2 t2. (LCONS h1 t1 = LCONS h2 t2) = (h1 = h2) /\ (t1 = t2)``,
  SRW_TAC [][EQ_IMP_THM, LCONS] THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [llist_repabs', lrep_ok_rules] THENL [
    POP_ASSUM (MP_TAC o C AP_THM ``0``) THEN SRW_TAC [][],
    ALL_TAC
  ] THEN
  POP_ASSUM (MP_TAC o GEN ``n:num`` o SIMP_RULE (srw_ss()) [] o
             C AP_THM ``SUC n:num``) THEN
  SRW_TAC [ETA_ss][GSYM FUN_EQ_THM, llist_rep_11]);
val _ = export_rewrites ["LCONS_11"]

val LHD_EQ_NONE = store_thm(
  "LHD_EQ_NONE",
  ``!ll. ((LHD ll = NONE) = (ll = LNIL)) /\ ((NONE = LHD ll) = (ll = LNIL))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["LHD_EQ_NONE"]

val LTL_EQ_NONE = store_thm(
  "LTL_EQ_NONE",
  ``!ll. ((LTL ll = NONE) = (ll = LNIL)) /\ ((NONE = LTL ll) = (ll = LNIL))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][LTL_THM]);
val _ = export_rewrites ["LTL_EQ_NONE"]

val LHDTL_EQ_SOME = store_thm(
  "LHDTL_EQ_SOME",
  ``!h t ll. (ll = LCONS h t) = (LHD ll = SOME h) /\ (LTL ll = SOME t)``,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][LHD_THM, LTL_THM]);


(* ----------------------------------------------------------------------
    indexing into lazy lists

    LNTH : num -> 'a llist -> 'a option
   ---------------------------------------------------------------------- *)

val LNTH = new_recursive_definition{
  name = "LNTH",
  rec_axiom = prim_recTheory.num_Axiom,
  def = ``(LNTH 0 ll = LHD ll) /\
          (LNTH (SUC n) ll = OPTION_JOIN (OPTION_MAP (LNTH n) (LTL ll)))``};

val LNTH_THM = store_thm(
  "LNTH_THM",
  ``(!n. LNTH n LNIL = NONE) /\
    (!h t. LNTH 0 (LCONS h t) = SOME h) /\
    (!n h t. LNTH (SUC n) (LCONS h t) = LNTH n t)``,
  SRW_TAC [][LNTH] THEN Induct_on `n` THEN
  SRW_TAC [][LNTH]);
val _ = export_rewrites ["LNTH_THM"]

(*---------------------------------------------------------------------------*)
(* Co-recursion theorem for lazy lists                                       *)
(*---------------------------------------------------------------------------*)

val llist_ue_Axiom = store_thm(
  "llist_ue_Axiom",
  ``!f : 'a -> ('a # 'b) option.
      ?!g : 'a -> 'b llist.
        (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
        (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))``,
  GEN_TAC THEN
  STRIP_ASSUME_TAC
    (prove_rec_fn_exists prim_recTheory.num_Axiom
       ``(h f 0 = \x:'a. OPTION_MAP SND (f x)) /\
         (!n. h f (SUC n) =
                  \x. OPTION_JOIN (OPTION_MAP (h f n o FST) (f x)))``) THEN
  `!f x. lrep_ok (\n. h f n x)`
     by (REPEAT GEN_TAC THEN
         Q_TAC SUFF_TAC `!g. (?x. g = (\n. h f n x)) ==> lrep_ok g`
               THEN1 SRW_TAC [DNF_ss][] THEN
         HO_MATCH_MP_TAC lrep_ok_coinduction THEN
         SRW_TAC [][] THEN
         Cases_on `f x` THENL [
           DISJ1_TAC THEN SRW_TAC [][FUN_EQ_THM] THEN
           Cases_on `n` THEN SRW_TAC [][],
           DISJ2_TAC THEN
           MAP_EVERY Q.EXISTS_TAC [`SND x'`, `\n. h f n (FST x')`] THEN
           CONJ_TAC THENL [
             Q.EXISTS_TAC `FST x'` THEN SRW_TAC [][],
             SRW_TAC [][FUN_EQ_THM] THEN Cases_on `n` THEN
             SRW_TAC [][]
           ]
         ]) THEN
  SRW_TAC [][EXISTS_UNIQUE_THM] THENL [
    Q.EXISTS_TAC `\x. llist_abs (\n. h f n x)` THEN
    SRW_TAC [][LHD,LTL,llist_repabs'] THEN
    Cases_on `f x` THEN SRW_TAC [][] THEN AP_TERM_TAC THEN
    SRW_TAC [][FUN_EQ_THM] THEN
    Cases_on `n` THENL [
      ASM_SIMP_TAC bool_ss [DECIDE ``0 + 1 = SUC 0``] THEN
      SRW_TAC [][],
      SRW_TAC [][DECIDE ``SUC n + 1 = SUC (SUC n)``]
    ],

    Q_TAC SUFF_TAC `!a. g a = g' a` THEN1 SRW_TAC [][FUN_EQ_THM] THEN
    Q_TAC SUFF_TAC `!a. llist_rep (g a) = llist_rep (g' a)` THEN1
          SRW_TAC [][llist_rep_11] THEN
    Q_TAC SUFF_TAC `!n a. llist_rep (g a) n = llist_rep (g' a) n` THEN1
          SRW_TAC [][FUN_EQ_THM] THEN
    Q_TAC SUFF_TAC `!n a. (llist_rep (g a) n = h f n a) /\
                          (llist_rep (g' a) n = h f n a)` THEN1
          SRW_TAC [][] THEN
    Induct THENL [
      FULL_SIMP_TAC (srw_ss()) [LHD],
      GEN_TAC THEN
      `(f a = NONE) \/ (?a' b. f a = SOME (a', b))`
          by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES]
      THENL [
        `(LHD (g a) = NONE) /\ (LHD (g' a) = NONE)`
           by ASM_SIMP_TAC std_ss [] THEN
        `(g a = LNIL) /\ (g' a = LNIL)` by METIS_TAC [LHD_EQ_NONE] THEN
        SRW_TAC [][LNIL,llist_repabs',lrep_ok_rules],
        Q_TAC SUFF_TAC `(g a = LCONS b (g a')) /\ (g' a = LCONS b (g' a'))`
              THEN1 SRW_TAC [][llist_rep_LCONS] THEN
        SRW_TAC [][LHDTL_EQ_SOME]
      ]
    ]
  ]);

val llist_Axiom = store_thm(
  "llist_Axiom",
  ``!f : 'a -> ('a # 'b) option.
      ?g.
         (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
         (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))``,
  MATCH_ACCEPT_TAC
    (CONJUNCT1
      (SIMP_RULE bool_ss [EXISTS_UNIQUE_THM, FORALL_AND_THM] llist_ue_Axiom)));

(*---------------------------------------------------------------------------*)
(* Alternative version of llist_Axiom (more understandable)                  *)
(*---------------------------------------------------------------------------*)

val llist_Axiom_1 = Q.store_thm
("llist_Axiom_1",
 `!f :'a -> ('a#'b)option.
     ?g:'a -> 'b llist.
       !x. g x =
            case f x
             of NONE -> LNIL
             || SOME (a,b) -> LCONS b (g a)`,
 GEN_TAC THEN
 STRIP_ASSUME_TAC (SPEC_ALL llist_Axiom) THEN
 Q.EXISTS_TAC `g` THEN
 GEN_TAC THEN (REPEAT CASE_TAC) THENL [
   METIS_TAC [LHD_EQ_NONE,optionTheory.OPTION_MAP_DEF],
   SRW_TAC [][LHDTL_EQ_SOME]
 ]);

val llist_Axiom_1ue = store_thm(
  "llist_Axiom_1ue",
  ``!f. ?!g. !x. g x = case f x
                       of NONE -> LNIL
                       || SOME (a,b) -> b ::: g a``,
  GEN_TAC THEN
  STRIP_ASSUME_TAC
    (SIMP_RULE bool_ss [EXISTS_UNIQUE_THM] (SPEC_ALL llist_ue_Axiom)) THEN
  SIMP_TAC bool_ss [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
    Q.EXISTS_TAC `g` THEN GEN_TAC THEN REPEAT CASE_TAC THENL [
      METIS_TAC [LHD_EQ_NONE,optionTheory.OPTION_MAP_DEF],
      SRW_TAC [][LHDTL_EQ_SOME]
    ],
    MAP_EVERY Q.X_GEN_TAC [`f1`, `f2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    `(f x = NONE) \/  (?a b. f x = SOME(a,b))`
       by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES] THEN
    POP_ASSUM SUBST1_TAC THEN SIMP_TAC (srw_ss()) []
  ]);

(*---------------------------------------------------------------------------*)
(* From which we get LUNFOLD by Skolemization :                              *)
(*                                                                           *)
(* LUNFOLD                                                                   *)
(*    |- !f x. LUNFOLD f x =                                                 *)
(*              case f x                                                     *)
(*               of NONE -> [||]                                             *)
(*               || SOME (v1,v2) -> v2:::LUNFOLD f v1                        *)
(*---------------------------------------------------------------------------*)

val LUNFOLD = new_specification
("LUNFOLD", ["LUNFOLD"],
  Q.prove(
    `?LUNFOLD.
      !f x. LUNFOLD f x =
             case f x
              of NONE -> [||]
              || SOME (v1,v2) -> v2:::LUNFOLD f v1`,
   METIS_TAC [llist_Axiom_1]));

(* ----------------------------------------------------------------------
    Another consequence of the finality theorem is the principle of
    bisimulation
   ---------------------------------------------------------------------- *)

val LLIST_BISIMULATION0 = store_thm(
  "LLIST_BISIMULATION0",
  ``!ll1 ll2. (ll1 = ll2) =
              ?R. R ll1 ll2 /\
                  !ll3 ll4.  R ll3 ll4 ==>
                             (ll3 = LNIL) /\ (ll4 = LNIL) \/
                             ?h t1 t2.
                                 (ll3 = h:::t1) /\ (ll4 = h:::t2) /\
                                 R t1 t2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `$=` THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `ll3` STRUCT_CASES_TAC llist_CASES THEN SRW_TAC [][],
    SRW_TAC [][] THEN
    Q.ISPEC_THEN `\ (l1,l2). if R l1 l2 then
                               case LHD l1 of
                                  NONE -> NONE
                               || SOME h -> SOME ((THE (LTL l1), THE (LTL l2)),
                                                  h)
                             else NONE`
                 (ASSUME_TAC o
                  Q.SPECL [`\ (l1,l2). if R l1 l2 then l1 else LNIL`,
                           `\ (l1,l2). if R l1 l2 then l2 else LNIL`] o
                  CONJUNCT2 o
                  SIMP_RULE bool_ss [EXISTS_UNIQUE_THM])
                 llist_Axiom_1ue THEN
    Q_TAC SUFF_TAC `(\ (l1,l2). if R l1 l2 then l1 else LNIL) =
                    (\ (l1,l2). if R l1 l2 then l2 else LNIL)`
          THEN1 (SRW_TAC [][FUN_EQ_THM,pairTheory.FORALL_PROD] THEN
                 METIS_TAC []) THEN
    POP_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
    SRW_TAC [][] THEN
    Cases_on `LHD p_1` THEN SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss()) [],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []
    ]
  ]);

val LLIST_BISIMULATION = store_thm(
  "LLIST_BISIMULATION",
  ``!ll1 ll2.
       (ll1 = ll2) =
       ?R. R ll1 ll2 /\
           !ll3 ll4.
              R ll3 ll4 ==>
              (ll3 = [||]) /\ (ll4 = [||]) \/
              (LHD ll3 = LHD ll4) /\ R (THE (LTL ll3)) (THE (LTL ll4))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
    Q.EXISTS_TAC `R` THEN SRW_TAC [][] THEN
    `(ll3 = [||]) /\ (ll4 = [||]) \/
     (LHD ll3 = LHD ll4) /\ R (THE (LTL ll3)) (THE (LTL ll4))`
        by METIS_TAC [] THEN
    SRW_TAC [][] THEN
    Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.SPEC_THEN `ll4` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val LLIST_STRONG_BISIMULATION = store_thm(
  "LLIST_STRONG_BISIMULATION",
  ``!ll1 ll2.
       (ll1 = ll2) =
       ?R. R ll1 ll2 /\
           !ll3 ll4.
              R ll3 ll4 ==>
              (ll3 = ll4) \/
              ?h t1 t2. (ll3 = h ::: t1) /\ (ll4 = h ::: t2) /\
                        R t1 t2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
    Q.EXISTS_TAC `\l1 l2. R l1 l2 \/ (l1 = l2)` THEN
    SRW_TAC [][] THENL [
      `(ll3 = ll4) \/
       ?h t1 t2. (ll3 = h:::t1) /\ (ll4 = h:::t2) /\ R t1 t2`
          by METIS_TAC [] THEN
      Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
      Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
      SRW_TAC [][]
    ]
  ]);

(* can also prove that two lists are equal "extensionally", by showing
   that LNTH is everywhere the same over them *)
val LNTH_llist_rep = prove(
  ``!n r. lrep_ok r ==> (LNTH n (llist_abs r) = r n)``,
  Induct THEN SRW_TAC [][LNTH, LHD, llist_repabs',LTL] THEN
  Q.UNDISCH_THEN `lrep_ok r` MP_TAC THEN
  ONCE_REWRITE_TAC [lrep_ok_cases] THEN SRW_TAC [][] THEN
  SRW_TAC [ETA_ss][]);

val LNTH_EQ = store_thm(
  "LNTH_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LNTH n ll1 = LNTH n ll2)``,
  SIMP_TAC (srw_ss()) [forall_llist, LNTH_llist_rep, llist_abs_11,
                       FUN_EQ_THM]);


(* ----------------------------------------------------------------------
    LTAKE : num -> 'a llist -> 'a list option

    returns the prefix of the given length, if the input list is at least
    that long
   ---------------------------------------------------------------------- *)

val LTAKE = new_recursive_definition {
  def = ``(LTAKE 0 ll = SOME []) /\
          (LTAKE (SUC n) ll =
             option_case
                NONE
                (\hd. option_case NONE (\tl. SOME (hd::tl))
                         (LTAKE n (THE (LTL ll))))
                (LHD ll))``,
  name = "LTAKE",
  rec_axiom = prim_recTheory.num_Axiom};

val LTAKE_THM = store_thm(
  "LTAKE_THM",
  ``(!l. LTAKE 0 l = SOME []) /\
    (!n. LTAKE (SUC n) LNIL = NONE) /\
    (!n h t. LTAKE (SUC n) (LCONS h t) = OPTION_MAP (CONS h) (LTAKE n t))``,
  SRW_TAC [][LTAKE, LHD_THM, LTL_THM] THEN REPEAT GEN_TAC THEN
  Cases_on `LTAKE n t` THEN SRW_TAC [][]);
val _ = export_rewrites ["LTAKE_THM"]

(* can also prove llist equality by proving all prefixes are the same *)
val LTAKE_SNOC_LNTH = store_thm(
  "LTAKE_SNOC_LNTH",
  ``!n ll. LTAKE (SUC n) ll =
             case LTAKE n ll of
                NONE -> NONE
             || SOME l -> (case LNTH n ll of
                              NONE -> NONE
                           || SOME e -> SOME (l ++ [e]))``,
  Induct THENL [
    SRW_TAC [][LTAKE,LNTH],
    GEN_TAC THEN
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LTAKE])) THEN
    Q.SPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THENL [
      POP_ASSUM (K ALL_TAC) THEN SRW_TAC [][LHD_THM, LTAKE_THM],
      SIMP_TAC (srw_ss()) [LHD_THM,LTL_THM,LTAKE_THM,LNTH_THM] THEN
      SRW_TAC [][] THEN Cases_on `LTAKE n t` THENL [
        SRW_TAC [][],
        SRW_TAC [][] THEN Cases_on `LNTH n t` THEN SRW_TAC [][]
      ]
    ]
  ]);

val LTAKE_EQ_NONE_LNTH = store_thm(
  "LTAKE_LNTH",
  ``!n ll. (LTAKE n ll = NONE) ==> (LNTH n ll = NONE)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [LTAKE,LNTH] THEN
  Q.X_GEN_TAC `ll` THEN
  Q.SPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  ASM_SIMP_TAC (srw_ss()) [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE n t` THEN SRW_TAC [][]);

val LTAKE_NIL_EQ_SOME = store_thm(
  "LTAKE_NIL_EQ_SOME",
  ``!l m. (LTAKE m LNIL = SOME l) = (m = 0) /\ (l = [])``,
  REPEAT GEN_TAC THEN Cases_on `m` THEN SIMP_TAC (srw_ss()) [LTAKE, LHD_THM] THEN
  PROVE_TAC []);
val _ = export_rewrites ["LTAKE_NIL_EQ_SOME"]

val LTAKE_NIL_EQ_NONE = store_thm(
  "LTAKE_NIL_EQ_NONE",
  ``!m. (LTAKE m LNIL = NONE) = (0 < m)``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC (srw_ss()) [LTAKE, LHD_THM]);
val _ = export_rewrites ["LTAKE_NIL_EQ_NONE"]

val SNOC_11 = prove(
  ``!l1 l2 x y. (l1 ++ [x] = l2 ++ [y]) = (l1 = l2) /\ (x = y)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THEN
  Induct THEN REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  Cases_on `l2` THEN SRW_TAC [][] THEN METIS_TAC []);

val LTAKE_EQ = store_thm(
  "LTAKE_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LTAKE n ll1 = LTAKE n ll2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  SRW_TAC [][LNTH_EQ] THEN
  POP_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
  SIMP_TAC (srw_ss())[LTAKE_SNOC_LNTH] THEN
  Cases_on `LTAKE n ll1` THEN Cases_on `LTAKE n ll2` THEN
  ASM_SIMP_TAC (srw_ss()) [] THENL [
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll2` THEN SRW_TAC [][] THEN
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll1` THEN SRW_TAC [][] THEN
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll1` THEN Cases_on `LNTH n ll2` THEN
    SRW_TAC [][SNOC_11]
  ]);

(* more random facts about LTAKE *)
val LTAKE_CONS_EQ_NONE = store_thm(
  "LTAKE_CONS_EQ_NONE",
  ``!m h t. (LTAKE m (LCONS h t) = NONE) =
            (?n. (m = SUC n) /\ (LTAKE n t = NONE))``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC (srw_ss()) []);

val LTAKE_CONS_EQ_SOME = store_thm(
  "LTAKE_CONS_EQ_SOME",
  ``!m h t l.
       (LTAKE m (LCONS h t) = SOME l) =
       (m = 0) /\ (l = []) \/
       ?n l'. (m = SUC n) /\ (LTAKE n t = SOME l') /\  (l = h::l')``,
  GEN_TAC THEN Cases_on `m` THEN
  SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val LTAKE_EQ_SOME_CONS = store_thm(
  "LTAKE_EQ_SOME_CONS",
  ``!n l x. (LTAKE n l = SOME x) ==> !h. ?y. LTAKE n (LCONS h l) = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LTAKE, LHD_THM, LTL_THM] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE n t` THEN SIMP_TAC (srw_ss()) [] THEN RES_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `h`) THEN
  ASM_SIMP_TAC (srw_ss()) []);


(* ----------------------------------------------------------------------
    Finality allows us to  define MAP
   ---------------------------------------------------------------------- *)

val LMAP = new_specification
("LMAP", ["LMAP"],
  prove(
    ``?LMAP. (!f. LMAP f LNIL = LNIL) /\
             (!f h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\l. if l = LNIL then NONE
                     else SOME (THE (LTL l), f (THE (LHD l)))`
                llist_Axiom_1)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN
    REPEAT STRIP_TAC THEN
    POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
    SRW_TAC [][LHD_THM, LTL_THM]));
val _ = export_rewrites ["LMAP"]

(* and append *)

val LAPPEND = new_specification
 ("LAPPEND", ["LAPPEND"],
  prove(
    ``?LAPPEND. (!x. LAPPEND LNIL x = x) /\
               (!h t x. LAPPEND (LCONS h t) x = LCONS h (LAPPEND t x))``,
    STRIP_ASSUME_TAC
       (Q.ISPEC `\(l1,l2).
                     if l1 = LNIL then
                        if l2 = LNIL then NONE
                        else SOME ((l1, THE (LTL l2)), THE (LHD l2))
                     else SOME ((THE (LTL l1), l2), THE (LHD l1))`
                llist_Axiom) THEN
    Q.EXISTS_TAC `\l1 l2. g (l1, l2)` THEN SIMP_TAC (srw_ss()) [] THEN
    REPEAT STRIP_TAC THENL [
      ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
      Q.EXISTS_TAC `\ll1 ll2. ll1 = g (LNIL, ll2)` THEN
      SIMP_TAC (srw_ss()) [] THEN Q.X_GEN_TAC `x` THEN
      STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THENL [
        DISJ1_TAC THEN
        ASM_SIMP_TAC std_ss [GSYM LHD_EQ_NONE, LHD_THM],
        SRW_TAC [][]
      ],
      SRW_TAC [][LHDTL_EQ_SOME]
    ]));
val _ = export_rewrites ["LAPPEND"]

(* properties of map and append *)

val LMAP_APPEND = store_thm(
  "LMAP_APPEND",
  ``!f ll1 ll2. LMAP f (LAPPEND ll1 ll2) =
                LAPPEND (LMAP f ll1) (LMAP f ll2)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?x y. (ll1 = LMAP f (LAPPEND x y)) /\
                                (ll2 = LAPPEND (LMAP f x) (LMAP f y))` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    ALL_TAC
  ] THEN
  STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THEN SRW_TAC [][] THENL [
    STRUCT_CASES_TAC (Q.SPEC `y` llist_CASES) THEN
    SRW_TAC [][] THEN
    PROVE_TAC [LAPPEND, LMAP],
    PROVE_TAC []
  ]);

val LAPPEND_EQ_LNIL = store_thm(
  "LAPPEND_EQ_LNIL",
  ``(LAPPEND l1 l2 = [||]) = (l1 = [||]) /\ (l2 = [||])``,
  SRW_TAC [][EQ_IMP_THM] THEN
  Q.SPEC_THEN `l1` FULL_STRUCT_CASES_TAC llist_CASES THEN
  FULL_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LAPPEND_EQ_LNIL"]

val LAPPEND_ASSOC = store_thm(
  "LAPPEND_ASSOC",
  ``!ll1 ll2 ll3. LAPPEND (LAPPEND ll1 ll2) ll3 =
                  LAPPEND ll1 (LAPPEND ll2 ll3)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_STRONG_BISIMULATION] THEN
  Q.EXISTS_TAC `\l1 l2. ?u. (l1 = LAPPEND (LAPPEND u ll2) ll3) /\
                            (l2 = LAPPEND u (LAPPEND ll2 ll3))` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    STRUCT_CASES_TAC (Q.SPEC `u` llist_CASES) THEN SRW_TAC [][] THEN
    PROVE_TAC []
  ]);

val LMAP_MAP = store_thm(
  "LMAP_MAP",
  ``!(f:'a -> 'b) (g:'c -> 'a) (ll:'c llist).
        LMAP f (LMAP g ll) = LMAP (f o g) ll``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?ll0. (ll1 = LMAP f (LMAP g ll0)) /\
                                (ll2 = LMAP (f o g) ll0)` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
      (Q.ISPEC `ll0:'c llist` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LMAP, LTL_THM, LHD_THM] THEN
    PROVE_TAC []
  ]);

val LAPPEND_NIL_2ND = store_thm(
  "LAPPEND_NIL_2ND",
  ``!ll. LAPPEND ll LNIL = ll``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LAPPEND ll2 LNIL` THEN
  SIMP_TAC (srw_ss()) [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC (srw_ss()) []);

(* ----------------------------------------------------------------------
    finiteness and list length
   ---------------------------------------------------------------------- *)

val (LFINITE_rules,LFINITE_ind,LFINITE_cases) = Hol_reln`
  LFINITE [||] /\
  (!h t. LFINITE t ==> LFINITE (h:::t))
`;

val LFINITE_THM = store_thm(
  "LFINITE_THM",
  ``(LFINITE LNIL = T) /\
    (!h t. LFINITE (LCONS h t) = LFINITE t)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LFINITE_cases])) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["LFINITE_THM"]

val LFINITE = store_thm(
  "LFINITE",
  ``LFINITE ll = ?n. LTAKE n ll = NONE``,
  EQ_TAC THENL [
    Q.ID_SPEC_TAC `ll` THEN HO_MATCH_MP_TAC LFINITE_ind THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][],
    Q_TAC SUFF_TAC `!n ll. (LTAKE n ll = NONE) ==> LFINITE ll` THEN1
          METIS_TAC [] THEN
    Induct THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val (llength_rel_rules,llength_rel_ind,llength_rel_cases) = Hol_reln`
  llength_rel [||] 0  /\
  (!h n t. llength_rel t n ==> llength_rel (h:::t) (SUC n))
`;

val llength_lfinite = prove(
 ``!t n. llength_rel t n ==> LFINITE t``,
  HO_MATCH_MP_TAC llength_rel_ind THEN SRW_TAC [][]);
val lfinite_llength = prove(
  ``!t. LFINITE t ==> ?n. llength_rel t n``,
  HO_MATCH_MP_TAC LFINITE_ind THEN SRW_TAC [][] THEN
  METIS_TAC [llength_rel_rules]);

val llength_unique = prove(
  ``!t m n. llength_rel t n /\ llength_rel t m ==> (m = n)``,
  Q_TAC SUFF_TAC `!t n. llength_rel t n ==> !m. llength_rel t m ==> (m = n)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC llength_rel_ind THEN SRW_TAC [][] THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [llength_rel_cases]) THEN
  FULL_SIMP_TAC (srw_ss()) []);

val llength_rel_nil = prove(
  ``llength_rel [||] n = (n = 0)``,
  ONCE_REWRITE_TAC [llength_rel_cases] THEN SRW_TAC [][]);
val _ = augment_srw_ss [rewrites [llength_rel_nil]]

val LLENGTH = new_definition(
  "LLENGTH",
  ``LLENGTH ll = if LFINITE ll then SOME (@n. llength_rel ll n) else NONE``);

val LLENGTH_THM = store_thm(
  "LLENGTH_THM",
  ``(LLENGTH LNIL = SOME 0) /\
    (!h t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t))``,
  SRW_TAC [][LLENGTH] THEN
  `?n. llength_rel t n` by METIS_TAC [lfinite_llength] THEN
  `!m. llength_rel t m = (m = n)` by METIS_TAC [llength_unique] THEN
  SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [llength_rel_cases] THEN SRW_TAC [][]);
val _ = export_rewrites ["LLENGTH_THM"]

val LFINITE_HAS_LENGTH = store_thm(
  "LFINITE_HAS_LENGTH",
  ``!ll. LFINITE ll ==> ?n. LLENGTH ll = SOME n``,
  SRW_TAC [][LLENGTH]);

val NOT_LFINITE_NO_LENGTH = store_thm(
  "NOT_LFINITE_NO_LENGTH",
  ``!ll. ~LFINITE ll ==> (LLENGTH ll = NONE)``,
  SIMP_TAC (srw_ss()) [LLENGTH]);

val LFINITE_INDUCTION = save_thm(
  "LFINITE_INDUCTION",
  CONV_RULE (RENAME_VARS_CONV ["P"]) LFINITE_ind);

val LFINITE_STRONG_INDUCTION = save_thm(
  "LFINITE_STRONG_INDUCTION",
  SIMP_RULE (srw_ss()) [LFINITE_THM]
  (Q.SPEC `\ll. LFINITE ll /\ P ll` LFINITE_INDUCTION))

val LFINITE_MAP = store_thm(
  "LFINITE_MAP",
  ``!f (ll:'a llist). LFINITE (LMAP f ll) = LFINITE ll``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    Q_TAC SUFF_TAC `!ll1. LFINITE ll1 ==>
                          !ll. (ll1 = LMAP f ll) ==> LFINITE ll`
          THEN1 SRW_TAC [][] THEN
    HO_MATCH_MP_TAC LFINITE_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LMAP, LFINITE_THM],
    Q.ID_SPEC_TAC `ll` THEN HO_MATCH_MP_TAC LFINITE_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LFINITE_THM, LMAP]
  ]);

val LFINITE_APPEND = store_thm(
  "LFINITE_APPEND",
  ``!ll1 ll2. LFINITE (LAPPEND ll1 ll2) = LFINITE ll1 /\ LFINITE ll2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    Q_TAC SUFF_TAC `!ll0. LFINITE ll0 ==>
                          !ll1 ll2. (LAPPEND ll1 ll2 = ll0) ==>
                                    LFINITE ll1 /\ LFINITE ll2`
          THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND] THEN
    PROVE_TAC [],
    REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
    Q.ID_SPEC_TAC `ll1` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND]
  ]);

val NOT_LFINITE_APPEND = store_thm(
  "NOT_LFINITE_APPEND",
  ``!ll1 ll2. ~LFINITE ll1 ==> (LAPPEND ll1 ll2 = ll1)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ~LFINITE ll2 /\  ?ll3. ll1 = LAPPEND ll2 ll3` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll4` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND, LHD_THM, LTL_THM] THEN
    PROVE_TAC []
  ]);

val LLENGTH_MAP = store_thm(
  "LLENGTH_MAP",
  ``!ll f. LLENGTH (LMAP f ll) = LLENGTH ll``,
  REPEAT GEN_TAC THEN Cases_on `LFINITE ll` THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LLENGTH_THM, LMAP],
    PROVE_TAC [NOT_LFINITE_NO_LENGTH, LFINITE_MAP]
  ]);

val LLENGTH_APPEND = store_thm(
  "LLENGTH_APPEND",
  ``!ll1 ll2.
       LLENGTH (LAPPEND ll1 ll2) =
         if LFINITE ll1 /\ LFINITE ll2 then
           SOME (THE (LLENGTH ll1) + THE (LLENGTH ll2))
         else
           NONE``,
  REPEAT GEN_TAC THEN
  Cases_on `LFINITE (LAPPEND ll1 ll2)` THENL [
    POP_ASSUM (fn th => `LFINITE ll1 /\ LFINITE ll2` by
                        PROVE_TAC [th, LFINITE_APPEND]) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll2` THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN
    ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_CLAUSES],
    `LLENGTH (LAPPEND ll1 ll2) = NONE`
      by PROVE_TAC [NOT_LFINITE_NO_LENGTH] THEN
    FULL_SIMP_TAC (srw_ss()) [LFINITE_APPEND]
  ]);

(* ----------------------------------------------------------------------
    mapping in and out of ordinary (finite) lists
   ---------------------------------------------------------------------- *)

val toList = new_definition(
  "toList",
  ``toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE``);

val toList_THM = store_thm(
  "toList_THM",
  ``(toList LNIL = SOME []) /\
    (!h t. toList (LCONS h t) = OPTION_MAP (CONS h) (toList t))``,
  SIMP_TAC (srw_ss()) [toList, LFINITE_THM, LLENGTH_THM, LTAKE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  ASM_SIMP_TAC (srw_ss()) [LTAKE_THM, LHD_THM, LTL_THM]);

val fromList = new_recursive_definition{
  name = "fromList",
  def = ``(fromList [] = LNIL) /\ (fromList (h::t) = LCONS h (fromList t))``,
  rec_axiom = listTheory.list_Axiom};
val _ = export_rewrites ["fromList"]

val LFINITE_fromList = store_thm(
  "LFINITE_fromList",
  ``!l. LFINITE (fromList l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val LLENGTH_fromList = store_thm(
  "LLENGTH_fromList",
  ``!l. LLENGTH (fromList l) = SOME (LENGTH l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val LTAKE_fromList = store_thm(
  "LTAKE_fromList",
  ``!l. LTAKE (LENGTH l) (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val from_toList = store_thm(
  "from_toList",
  ``!l. toList (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [toList_THM]);

val LFINITE_toList = store_thm(
  "LFINITE_toList",
  ``!ll. LFINITE ll ==> ?l. toList ll = SOME l``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [toList_THM]);

val to_fromList = store_thm(
  "to_fromList",
  ``!ll. LFINITE ll ==> (fromList (THE (toList ll)) = ll)``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC (srw_ss()) [toList_THM] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LFINITE_toList THEN FULL_SIMP_TAC (srw_ss()) []);

(* ----------------------------------------------------------------------
    LDROP : num -> 'a llist -> 'a llist option

    drops a prefix of given length, if there are that many items to be
    dropped
   ---------------------------------------------------------------------- *)

val LDROP = new_recursive_definition {
  def = ``(LDROP 0 ll = SOME ll) /\
          (LDROP (SUC n) ll = OPTION_JOIN (OPTION_MAP (LDROP n) (LTL ll)))``,
  rec_axiom = prim_recTheory.num_Axiom,
  name = "LDROP"};

val LDROP_THM = store_thm(
  "LDROP_THM",
  ``(!ll. LDROP 0 ll = SOME ll) /\
    (!n. LDROP (SUC n) LNIL = NONE) /\
    (!n h t. LDROP (SUC n) (LCONS h t) = LDROP n t)``,
  SIMP_TAC (srw_ss()) [LDROP, LTL_THM]);
val _ = export_rewrites ["LDROP_THM"]

val LDROP1_THM = store_thm(
  "LDROP1_THM",
  ``LDROP 1 = LTL``,
  CONV_TAC (Q.X_FUN_EQ_CONV `ll`) THEN
  SIMP_TAC bool_ss [DECIDE ``1 = SUC 0``, LDROP] THEN
  GEN_TAC THEN Cases_on `LTL ll` THEN
  SIMP_TAC (srw_ss()) [LDROP]);


val NOT_LFINITE_TAKE = store_thm(
  "NOT_LFINITE_TAKE",
  ``!ll. ~LFINITE ll ==> !n. ?y. LTAKE n ll = SOME y``,
  SIMP_TAC (srw_ss()) [LFINITE] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.SPEC `n`) THEN
  Cases_on `LTAKE n ll` THEN FULL_SIMP_TAC (srw_ss()) []);

val LFINITE_TAKE = store_thm(
  "LFINITE_TAKE",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LTAKE n ll = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LTAKE_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (srw_ss()) []);

val NOT_LFINITE_DROP = store_thm(
  "NOT_LFINITE_DROP",
  ``!ll. ~LFINITE ll ==> !n. ?y. LDROP n ll = SOME y``,
  CONV_TAC (BINDER_CONV RIGHT_IMP_FORALL_CONV THENC
            SWAP_VARS_CONV) THEN
  Induct THEN SIMP_TAC (srw_ss()) [LDROP] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val LFINITE_DROP = store_thm(
  "LFINITE_DROP",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LDROP n ll = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LDROP_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LLENGTH_THM, LFINITE_THM, LDROP_THM] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC (srw_ss()) []);

val option_case_NONE = prove(
  ``!f x y. (option_case NONE f x = SOME y) =
            (?z. (x = SOME z) /\ (f z = SOME y))``,
  REPEAT GEN_TAC THEN Cases_on `x` THEN SIMP_TAC (srw_ss()) []);

val LTAKE_DROP = store_thm(
  "LTAKE_DROP",
  ``(!n ll:'a llist.
        ~LFINITE ll ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll)) /\
    (!n ll:'a llist.
        LFINITE ll /\ n <= THE (LLENGTH ll) ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll))``,
  CONJ_TAC THEN Induct THEN SRW_TAC [][] THENL [
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC NOT_LFINITE_TAKE THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `y` ASSUME_TAC o Q.SPEC `n`) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    Q_TAC SUFF_TAC `y = THE (LTAKE n t)` THEN1 METIS_TAC [] THEN
    ASM_SIMP_TAC (srw_ss()) [],
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC (srw_ss()) [LFINITE_TAKE] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `z = THE (LTAKE n t)` by ASM_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
  ]);

(* ----------------------------------------------------------------------
    exists : ('a -> bool) -> 'a llist -> bool

    defined inductively
   ---------------------------------------------------------------------- *)

val (exists_rules,exists_ind,exists_cases) = Hol_reln`
  (!h t. P h ==> exists P (h ::: t)) /\
  (!h t. exists P t ==> exists P (h ::: t))
`;

val exists_thm = store_thm(
  "exists_thm",
  ``(exists P [||] = F) /\
    (exists P (h:::t) = P h \/ exists P t)``,
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exists_cases])) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["exists_thm"]

val exists_LNTH = store_thm(
  "exists_LNTH",
  ``!l. exists P l = ?n e. (SOME e = LNTH n l) /\ P e``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC exists_ind THEN SRW_TAC [][] THENL [
      MAP_EVERY Q.EXISTS_TAC [`0`, `h`] THEN SRW_TAC [][],
      MAP_EVERY Q.EXISTS_TAC [`SUC n`, `e`] THEN SRW_TAC [][]
    ],
    Q_TAC SUFF_TAC `!n l e. (SOME e = LNTH n l) /\ P e ==> exists P l`
          THEN1 METIS_TAC [] THEN
    Induct THEN REPEAT GEN_TAC THEN
    Q.SPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val MONO_exists = store_thm(
  "MONO_exists",
  ``(!x. P x ==> Q x) ==> (exists P l ==> exists Q l)``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `l` THEN HO_MATCH_MP_TAC exists_ind THEN
  SRW_TAC [][]);
val _ = IndDefLib.export_mono "MONO_exists"

val exists_strong_ind = save_thm(
  "exists_strong_ind",
  exists_ind |> Q.SPECL [`P`, `\ll. Q ll /\ exists P ll`]
             |> SIMP_RULE (srw_ss()) []
             |> Q.GEN `Q` |> Q.GEN `P`);

val exists_LDROP = store_thm(
  "exists_LDROP",
  ``exists P ll <=> ?n a t. (LDROP n ll = SOME (a:::t)) /\ P a``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC
       `!ll. exists P ll ==> ?n a t. (LDROP n ll = SOME (a:::t)) /\ P a`
       THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC exists_strong_ind THEN SRW_TAC [][] THENL [
      Q.EXISTS_TAC `0` THEN SRW_TAC [][],
      Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][]
    ],
    Q_TAC SUFF_TAC
       `!n ll a t. (LDROP n ll = SOME (a:::t)) /\ P a ==> exists P ll`
       THEN1 METIS_TAC [] THEN
    Induct THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [LDROP]
  ]);


(* ----------------------------------------------------------------------
    companion LL_ALL/every (has a coinduction principle)
   ---------------------------------------------------------------------- *)

val every_def = Define`every P ll = ~exists ((~) o P) ll`
val _ = overload_on ("LL_ALL", ``every``)
val _ = overload_on ("every", ``every``)

val every_coind = store_thm(
  "every_coind",
  ``!P Q.
       (!h t. Q (h:::t) ==> P h /\ Q t) ==>
       !ll. Q ll ==> every P ll``,
  SIMP_TAC (srw_ss()) [every_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!ll. exists ($~ o P) ll ==> ~Q ll` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC exists_ind THEN
  SRW_TAC [][DECIDE ``(~p ==> ~q) = (q ==> p)``] THEN METIS_TAC []);

val every_thm = store_thm(
  "every_thm",
  ``(every P [||] = T) /\
    (every P (h:::t) = P h /\ every P t)``,
  SRW_TAC [][every_def]);
val _ = export_rewrites ["every_thm"]
val LL_ALL_THM = save_thm("LL_ALL_THM", every_thm)

val MONO_every = store_thm(
  "MONO_every",
  ``(!x. P x ==> Q x) ==> (every P l ==> every Q l)``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `l` THEN HO_MATCH_MP_TAC every_coind THEN
  SRW_TAC [][]);
val _ = export_mono "MONO_every"

val every_strong_coind = save_thm(
  "every_strong_coind",
  every_coind |> Q.SPECL [`P`, `\ll. Q ll \/ every P ll`]
              |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, IMP_CONJ_THM,
                                       FORALL_AND_THM]
              |> Q.GEN `Q` |> Q.GEN `P`);

(*
  could alternatively take contrapositives of the exists induction principle:

  exists_strong_ind |> Q.SPECL [`(~) o P`, `(~) o Q`]
                     |> CONV_RULE (BINOP_CONV (ONCE_REWRITE_CONV [MONO_NOT_EQ]))
                     |> SIMP_RULE (srw_ss()) [GSYM every_def]
*)

(* ----------------------------------------------------------------------
    can now define LFILTER and LFLATTEN
   ---------------------------------------------------------------------- *)

val least_lemma = prove(
  ``(?n. P n) ==> ((LEAST) P = if P 0 then 0 else SUC ((LEAST) (P o SUC)))``,
  SRW_TAC [][] THENL [
    Q_TAC SUFF_TAC `(\n. n = 0) ($LEAST P)` THEN1 SRW_TAC [][] THEN
    MATCH_MP_TAC whileTheory.LEAST_ELIM THEN SRW_TAC [][] THENL [
      PROVE_TAC [],
      SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
      `0 < n'` by DECIDE_TAC THEN METIS_TAC []
    ],
    Q_TAC SUFF_TAC `(\n. n = SUC ($LEAST (P o SUC))) ((LEAST) P)` THEN1
          SRW_TAC [][] THEN
    MATCH_MP_TAC whileTheory.LEAST_ELIM THEN CONJ_TAC THENL [
      PROVE_TAC [],
      Q.X_GEN_TAC `p` THEN SRW_TAC [][] THEN
      Q_TAC SUFF_TAC `(\k. p = SUC k) ($LEAST (P o SUC))` THEN1
            SRW_TAC [][] THEN
      MATCH_MP_TAC whileTheory.LEAST_ELIM THEN CONJ_TAC THENL [
        SRW_TAC [][] THEN Cases_on `n` THEN PROVE_TAC [],
        SRW_TAC [][] THEN
        `~(SUC n' < p)` by PROVE_TAC [] THEN
        `(p = SUC n') \/ (p < SUC n')` by DECIDE_TAC THEN
        `?p0. p = SUC p0` by METIS_TAC [arithmeticTheory.num_CASES] THEN
        FULL_SIMP_TAC (srw_ss()) []
      ]
    ]
  ]);

val LFILTER = new_specification
 ("LFILTER", ["LFILTER"],
  prove(
    ``?LFILTER.
        !P ll. LFILTER P ll = if ~ exists P ll then LNIL
                              else
                                if P (THE (LHD ll)) then
                                    LCONS (THE (LHD ll))
                                          (LFILTER P (THE (LTL ll)))
                                else
                                    LFILTER P (THE (LTL ll))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\ll. if exists P ll then
                        let n = LEAST n. ?e. (SOME e = LNTH n ll) /\ P e in
                          SOME (THE (LDROP (SUC n) ll),
                                THE (LNTH n ll))
                      else NONE` llist_Axiom_1)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN REPEAT GEN_TAC THEN
    POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `P`) THEN
    Cases_on `exists P ll` THENL [
      POP_ASSUM MP_TAC THEN
      POP_ASSUM
        (fn th => CONV_TAC
                    (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
                  ASSUME_TAC (GSYM th)) THEN
      SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `?h t. ll = h:::t` by METIS_TAC [llist_CASES, exists_thm] THENL [
        Q.PAT_ASSUM `exists P ll` (K ALL_TAC) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        Q_TAC SUFF_TAC `n = 0` THEN1 SRW_TAC [][] THEN
        CONV_TAC (UNBETA_CONV ``n:num``) THEN UNABBREV_ALL_TAC THEN
        MATCH_MP_TAC whileTheory.LEAST_ELIM THEN SRW_TAC [][] THENL [
          Q.EXISTS_TAC `0` THEN SRW_TAC [][],
          SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
          `0 < n` by DECIDE_TAC THEN
          METIS_TAC [optionTheory.SOME_11, LNTH_THM]
        ],
        FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        `n = SUC (LEAST m. ?e. (SOME e = LNTH m t) /\ P e)`
           by (Q.UNABBREV_TAC `n` THEN
               Q.HO_MATCH_ABBREV_TAC `(LEAST) Q1 = SUC ((LEAST) Q2)` THEN
               `Q2 = Q1 o SUC`
                  by (UNABBREV_ALL_TAC THEN SRW_TAC [][FUN_EQ_THM]) THEN
               POP_ASSUM SUBST1_TAC THEN
               Q.MATCH_ABBREV_TAC `LHS = RHS` THEN
               Q.UNABBREV_TAC `LHS` THEN
               `RHS = if Q1 0 then 0 else RHS` by SRW_TAC [][Abbr`Q1`] THEN
               POP_ASSUM SUBST1_TAC THEN
               Q.UNABBREV_TAC `RHS` THEN
               MATCH_MP_TAC least_lemma THEN
               UNABBREV_ALL_TAC  THEN
               SRW_TAC [][] THEN
               `?m e. (SOME e = LNTH m t) /\ P e`
                   by METIS_TAC [exists_LNTH] THEN
               MAP_EVERY Q.EXISTS_TAC [`SUC m`, `e`] THEN
               SRW_TAC [][]) THEN
        RM_ALL_ABBREVS_TAC THEN SRW_TAC [][] THEN
        FIRST_X_ASSUM
          ((fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) o
           assert (is_forall o concl)) THEN
        SRW_TAC [][] THEN SRW_TAC [][Abbr`n`]
      ],
      POP_ASSUM MP_TAC THEN
      POP_ASSUM
        (fn th => CONV_TAC
                    (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th])))) THEN
      SRW_TAC [][]
    ]));

val LFILTER_THM = store_thm(
  "LFILTER_THM",
  ``(!P. LFILTER P LNIL = LNIL) /\
    (!P h t. LFILTER P (LCONS h t) = if P h then LCONS h (LFILTER P t)
                                     else LFILTER P t)``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFILTER)) THEN
  SIMP_TAC (srw_ss()) [] THEN
  Cases_on `P h` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `exists P t` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  ONCE_REWRITE_TAC [LFILTER] THEN ASM_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LFILTER_THM"]

val LFILTER_NIL = store_thm(
  "LFILTER_NIL",
  ``!P ll. LL_ALL ($~ o P) ll ==> (LFILTER P ll = LNIL)``,
  ONCE_REWRITE_TAC [LFILTER, every_def] THEN
  `!P. $~ o $~ o P = P` by (GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
                            SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val LFILTER_EQ_NIL = store_thm(
  "LFILTER_EQ_NIL",
  ``!ll. (LFILTER P ll = LNIL) = every ((~) o P) ll``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, LFILTER_NIL] THEN
  HO_MATCH_MP_TAC every_coind THEN
  SRW_TAC [][]);

val LFILTER_APPEND = store_thm(
  "LFILTER_APPEND",
  ``!P ll1 ll2. LFINITE ll1 ==>
                (LFILTER P (LAPPEND ll1 ll2) =
                 LAPPEND (LFILTER P ll1) (LFILTER P ll2))``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC (srw_ss()) []);

val LFLATTEN = new_specification
 ("LFLATTEN", ["LFLATTEN"],
  prove(
    ``?LFLATTEN.
      !ll. LFLATTEN (ll:'a llist llist) =
             if LL_ALL ($= LNIL) ll then LNIL
             else
                if THE (LHD ll) = LNIL then
                   LFLATTEN (THE (LTL ll))
                else
                   LCONS (THE (LHD (THE (LHD ll))))
                         (LFLATTEN (LCONS (THE (LTL (THE (LHD ll))))
                                          (THE (LTL ll))))``,
    ASSUME_TAC (
      Q.ISPEC `\ll. if LL_ALL ($= LNIL) ll then NONE
                   else
                     let n = LEAST n. ?e. (SOME e = LNTH n ll) /\ ~(e = [||])
                     in
                        let nlist = THE (LNTH n ll)
                        in
                            SOME(LCONS (THE (LTL nlist))
                                       (THE (LDROP (SUC n) ll)),
                                 THE (LHD nlist))` llist_Axiom) THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `g` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `g` THEN GEN_TAC THEN
    Cases_on `LL_ALL ($= LNIL) ll` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      `LTL (g ll) = NONE` by ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC (srw_ss()) [],
      ALL_TAC
    ] THEN
    `?h t. ll = LCONS h t` by METIS_TAC [llist_CASES,every_thm] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC (srw_ss()) [] THEN
    Cases_on `h = LNIL` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      FULL_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      REPEAT (FIRST_X_ASSUM (fn th =>
                             MP_TAC (Q.SPEC `LCONS LNIL t` th) THEN
                             MP_TAC (Q.SPEC `t` th))) THEN
      ASM_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      `?n e. (SOME e = LNTH n t) /\ ~(e = [||])`
           by (FULL_SIMP_TAC (srw_ss()) [every_def, exists_LNTH] THEN
               METIS_TAC []) THEN
      `(LEAST n. ?e. (SOME e = LNTH n ([||]:::t)) /\ ~(e = [||])) =
       SUC (LEAST n. ?e. (SOME e = LNTH n t) /\ ~(e = [||]))`
         by (Q.MATCH_ABBREV_TAC `(LEAST) Q1 = SUC ((LEAST) Q2)` THEN
             `Q2 = Q1 o SUC` by SRW_TAC [][Abbr`Q1`, Abbr`Q2`, FUN_EQ_THM] THEN
             POP_ASSUM SUBST1_TAC THEN Q.UNABBREV_TAC `Q2` THEN
             Q.MATCH_ABBREV_TAC `(LEAST)Q1 = RHS` THEN
             `RHS = if Q1 0 then 0 else RHS` by SRW_TAC [][Abbr`Q1`] THEN
             POP_ASSUM SUBST1_TAC THEN Q.UNABBREV_TAC `RHS` THEN
             MATCH_MP_TAC least_lemma THEN
             Q.UNABBREV_TAC `Q1` THEN
             Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][] THEN METIS_TAC []) THEN
      POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][LET_THM] THEN
      `?h1 t1. g t = h1 ::: t1`
         by METIS_TAC [LHD_EQ_NONE, llist_CASES,
                       optionTheory.NOT_SOME_NONE] THEN
      POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][LHDTL_EQ_SOME],

      (* ~(h = LNIL) *)
      FULL_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      ASM_SIMP_TAC (srw_ss()) [LHDTL_EQ_SOME] THEN
      Q.SUBGOAL_THEN
        `(LEAST n. ?e. (SOME e = LNTH n (h:::t)) /\ ~(e = [||])) = 0`
      SUBST_ALL_TAC THENL [
        SRW_TAC [][whileTheory.LEAST_DEF] THEN
        ONCE_REWRITE_TAC [whileTheory.WHILE] THEN SRW_TAC [][],
        ALL_TAC
      ] THEN SRW_TAC [][LET_THM]
    ]));

val LFLATTEN_THM = store_thm(
  "LFLATTEN_THM",
  ``(LFLATTEN LNIL = LNIL) /\
    (!tl. LFLATTEN (LCONS LNIL t) = LFLATTEN t) /\
    (!h t tl. LFLATTEN (LCONS (LCONS h t) tl) =
              LCONS h (LFLATTEN (LCONS t tl)))``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFLATTEN)) THEN
  SIMP_TAC (srw_ss()) [LL_ALL_THM, LHD_THM, LTL_THM] THEN
  COND_CASES_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  ONCE_REWRITE_TAC [LFLATTEN] THEN ASM_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LFLATTEN_THM"]

val LFLATTEN_APPEND = store_thm(
  "LFLATTEN_APPEND",
  ``!h t. LFLATTEN (LCONS h t) = LAPPEND h (LFLATTEN t)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_STRONG_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?h t. (ll1 = LFLATTEN (LCONS h t)) /\
                                (ll2 = LAPPEND h (LFLATTEN t))` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    Cases_on `h = LNIL` THENL [
      SRW_TAC [][],

      (* ~(h = LNIL) *)
      POP_ASSUM (fn th =>
        `?h0 t0. h = LCONS h0 t0` by PROVE_TAC [llist_CASES, th]) THEN
      SRW_TAC [][] THEN PROVE_TAC []
    ]
  ]);
val _ = export_rewrites ["LFLATTEN_APPEND"]


val LFLATTEN_EQ_NIL = store_thm(
  "LFLATTEN_EQ_NIL",
  ``!ll. (LFLATTEN ll = LNIL) = LL_ALL ($= LNIL) ll``,
  GEN_TAC THEN EQ_TAC THENL [
    Q.ID_SPEC_TAC `ll` THEN
    HO_MATCH_MP_TAC every_coind THEN
    SRW_TAC [][],
    ONCE_REWRITE_TAC [LFLATTEN] THEN SIMP_TAC (srw_ss()) []
 ]);

val LFLATTEN_SINGLETON = store_thm(
  "LFLATTEN_SINGLETON",
  ``!h. LFLATTEN (LCONS h LNIL) = h``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LFLATTEN (LCONS ll2 LNIL)` THEN
  SIMP_TAC (srw_ss()) [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LFLATTEN_THM, LHD_THM, LTL_THM]);


(*---------------------------------------------------------------------------*)
(* ZIP two streams together, returning LNIL as soon as possible.             *)
(*                                                                           *)
(* LZIP_THM                                                                  *)
(*    |- (!l2. LZIP LNIL l2 = LNIL) /\                                       *)
(*       (!l1. LZIP l1 LNIL = LNIL) /\                                       *)
(*       (!h1 h2 t1 t2.                                                      *)
(*          LZIP (LCONS h1 t1) (LCONS h2 t2) = LCONS (h1,h2) (LZIP t1 t2))   *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

open pairTheory
val LZIP_THM = new_specification
 ("LZIP_THM", ["LZIP"],
  Q.prove
   (`?LZIP:'a llist # 'b llist -> ('a#'b) llist.
    (!l1. LZIP (l1,[||]) = [||]) /\
    (!l2. LZIP ([||],l2) = [||]) /\
    (!h1 h2 t1 t2. LZIP (h1:::t1, h2:::t2) = (h1,h2) ::: LZIP (t1,t2))`,
    let val ax =
       ISPEC
        ``\(l1,l2).
             if (l1:'a llist = LNIL) \/ (l2:'b llist = LNIL)
              then NONE
              else SOME ((THE(LTL l1),THE(LTL l2)),
                         (THE(LHD l1),THE(LHD l2)))``
         llist_Axiom_1
    in
     STRIP_ASSUME_TAC (SIMP_RULE (srw_ss()) [FORALL_PROD] ax)
       THEN Q.EXISTS_TAC `g`
       THEN REPEAT CONJ_TAC THENL
      [ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
         THEN RW_TAC (srw_ss()) [],
       ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
         THEN RW_TAC (srw_ss()) [],
       REPEAT GEN_TAC THEN
       POP_ASSUM (fn th => GEN_REWRITE_TAC LHS_CONV bool_rewrites [th])
         THEN RW_TAC (srw_ss()) [LTL_THM,LHD_THM]]
    end));
val _ = export_rewrites ["LZIP_THM"]


(*---------------------------------------------------------------------------*)
(* LUNZIP_THM                                                                *)
(*  |- (LUNZIP [||] = ([||],[||])) /\                                        *)
(*     !x y t. LUNZIP ((x,y):::t) =                                          *)
(*                let (ll1,ll2) = LUNZIP t in (x:::ll1,y:::ll2)              *)
(*---------------------------------------------------------------------------*)

val LUNZIP_THM = new_specification (
  "LUNZIP_THM",
  ["LUNZIP"],
  Q.prove(
      `?LUNZIP. (LUNZIP [||] = ([||]:'a llist, [||]:'b llist)) /\
    	(!x y t. LUNZIP ((x:'a, y:'b):::t) =
                  let (ll1, ll2) = LUNZIP t in (x:::ll1, y:::ll2))`,
      STRIP_ASSUME_TAC
       (Q.ISPEC `\ll. if (LHD ll = NONE) then NONE
        		else SOME (THE (LTL ll), SND (THE (LHD ll)))` llist_Axiom_1) THEN
      STRIP_ASSUME_TAC
       (Q.ISPEC `\ll. if (LHD ll = NONE) then NONE
                        else SOME (THE (LTL ll), FST (THE (LHD ll)))` llist_Axiom_1) THEN
      Q.EXISTS_TAC `\ll. (g' ll, g ll)` THEN SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THENL [
	POP_ASSUM (ASSUME_TAC o Q.SPEC `[||]`) THEN
	FULL_SIMP_TAC list_ss [LHD_THM],
	POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `[||]`) THEN
        FULL_SIMP_TAC list_ss [LHD_THM],
        NTAC 2 (POP_ASSUM (MP_TAC o Q.SPEC `(x,y):::t`)) THEN
	RW_TAC list_ss [LHD_THM, LTL_THM, LET_THM]])
  );
val _ = export_rewrites ["LUNZIP_THM"]

val LZIP_LUNZIP = Q.store_thm
("LZIP_LUNZIP",
 `!ll: ('a # 'b) llist. LZIP(LUNZIP ll) = ll`,
 REWRITE_TAC [Once LLIST_STRONG_BISIMULATION] THEN
 GEN_TAC THEN
 Q.EXISTS_TAC `\l1 l2. l1 = LZIP (LUNZIP l2)` THEN
 SRW_TAC [][] THEN
 Q.ISPEC_THEN `ll4` STRUCT_CASES_TAC llist_CASES THEN
 SRW_TAC [][] THEN
 Cases_on `h` THEN SRW_TAC [][] THEN SRW_TAC [][]);
val _ = export_rewrites ["LZIP_LUNZIP"]

val LUNFOLD_THM = Q.store_thm
("LUNFOLD_THM",
  `!f x v1 v2. 
     ((f x = NONE) ==> (LUNFOLD f x = [||])) /\
     ((f x = SOME (v1,v2)) ==> (LUNFOLD f x = v2:::LUNFOLD f v1))`,
 SRW_TAC [] [] THEN1
 SRW_TAC [] [Once LUNFOLD] THEN
 SRW_TAC [] [Once LUNFOLD]);

val LLIST_EQ = Q.store_thm 
("LLIST_EQ",
 `!f g. 
   (!x. ((f x = [||]) /\ (g x = [||])) \/
        (?h y. (f x = h:::f y) /\ (g x = h:::g y)))
   ==> 
   (!x. f x = g x)`,
 SRW_TAC [] [] THEN
 SRW_TAC [] [Once LLIST_BISIMULATION0] THEN
 Q.EXISTS_TAC `\ll1 ll2. ?x. (ll1 = f x) /\ (ll2 = g x)` THEN
 SRW_TAC [] [] THEN
 METIS_TAC []);

val LUNFOLD_EQ = Q.store_thm 
("LUNFOLD_EQ",
 `!R f s ll.
    R s ll /\
    (!s ll. 
       R s ll 
       ==> 
       ((f s = NONE) /\ (ll = [||])) \/ 
       ?s' x ll'. 
         (f s = SOME (s',x)) /\ (LHD ll = SOME x) /\ (LTL ll = SOME ll') /\ 
         R s' ll')
    ==>
    (LUNFOLD f s = ll)`,
 SRW_TAC [] [] THEN
 SRW_TAC [] [Once LLIST_BISIMULATION] THEN
 Q.EXISTS_TAC `\ll1 ll2. ?s. (ll1 = LUNFOLD f s) /\ R s ll2` THEN
 SRW_TAC [] [] THEN1
 METIS_TAC [] THEN
 RES_TAC THEN
 SRW_TAC [] [LUNFOLD_THM] THEN
 IMP_RES_TAC LUNFOLD_THM THEN
 SRW_TAC [] [] THEN
 METIS_TAC []);

val LMAP_LUNFOLD = Q.store_thm 
("LMAP_LUNFOLD",
 `!f g s. 
   LMAP f (LUNFOLD g s) = LUNFOLD (\s. OPTION_MAP (\(x, y). (x, f y)) (g s)) s`,
 SRW_TAC [] [] THEN
 MATCH_MP_TAC (GSYM LUNFOLD_EQ) THEN
 SRW_TAC [] [] THEN
 Q.EXISTS_TAC `\s ll. ll = LMAP f (LUNFOLD g s)` THEN
 SRW_TAC [] [] THEN
 Cases_on `g s` THEN
 SRW_TAC [] [LUNFOLD_THM] THEN
 Cases_on `x` THEN
 IMP_RES_TAC LUNFOLD_THM THEN
 SRW_TAC [] []);

val LNTH_LDROP = Q.store_thm 
("LNTH_LDROP",
 `!n l x. (LNTH n l = SOME x) ==> (LHD (THE (LDROP n l)) = SOME x)`,
 Induct THEN
 SRW_TAC [] [LNTH, LDROP] THEN
 Cases_on `LTL l` THEN
 SRW_TAC [] [] THEN 
 FULL_SIMP_TAC (srw_ss()) []);

val LAPPEND_fromList = Q.store_thm 
("LAPPEND_fromList",
 `!l1 l2. LAPPEND (fromList l1) (fromList l2) = fromList (l1 ++ l2)`,
 Induct THEN
 SRW_TAC [] []);

val LTAKE_LENGTH = Q.store_thm ("LTAKE_LENGTH",
`!n ll l. (LTAKE n ll = SOME l) ==> (n = LENGTH l)`,
Induct THEN
SRW_TAC [] [] THEN
SRW_TAC [] [] THEN
`(ll = [||]) \/ ?h t. ll = h:::t` by METIS_TAC [llist_CASES] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


(* ------------------------------------------------------------------------ *)
(* Turning a stream-like linear order into a lazy list                      *)
(* ------------------------------------------------------------------------ *)

local 
open pred_setTheory set_relationTheory

in

val linear_order_to_list_f_def = Define `
  linear_order_to_list_f lo =
    let min = minimal_elements (domain lo UNION range lo) lo in
      if min = {} then
        NONE
      else
        SOME (rrestrict lo ((domain lo UNION range lo) DIFF min), CHOICE min)`;

val linear_order_to_list_lem1 = Q.prove (
`!s. FINITE s ==> 
  !lo X x. 
    x IN X /\
    (s = { y | (y,x) IN lo }) /\
    linear_order lo X /\
    finite_prefixes lo X
    ==> 
    ?i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x`,
HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION THEN
SRW_TAC [] [] THEN
`SING (minimal_elements X lo)`
        by METIS_TAC [finite_prefix_linear_order_has_unique_minimal, 
                      SUBSET_REFL] THEN
FULL_SIMP_TAC (srw_ss()) [SING_DEF] THEN
`{y | (y,x) IN rrestrict lo (X DIFF minimal_elements X lo) } PSUBSET 
 { y | (y,x) IN lo }`
        by (SRW_TAC [] [PSUBSET_DEF, in_rrestrict, SUBSET_DEF, EXTENSION] THEN
            FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION, 
                                      linear_order_def, transitive_def, 
                                      antisym_def] THEN
            METIS_TAC []) THEN
`X DIFF minimal_elements X lo SUBSET X` by SRW_TAC [] [SUBSET_DEF] THEN
`linear_order (rrestrict lo (X DIFF minimal_elements X lo)) 
              (X DIFF minimal_elements X lo)` 
        by METIS_TAC [linear_order_subset] THEN
`finite_prefixes (rrestrict lo (X DIFF minimal_elements X lo)) 
                 (X DIFF minimal_elements X lo)`
        by METIS_TAC [finite_prefixes_subset] THEN
Cases_on `x NOTIN X DIFF minimal_elements X lo` THENL
[Q.EXISTS_TAC `0` THEN
     SRW_TAC [] [Once LUNFOLD, linear_order_to_list_f_def] THEN
     Q.UNABBREV_TAC `min` THEN
     `domain lo UNION range lo = X` 
             by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, in_domain, in_range, 
                                           linear_order_def, SUBSET_DEF] THEN
                 METIS_TAC []) THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC [IN_SING],
 `?i. LNTH i (LUNFOLD linear_order_to_list_f 
                      (rrestrict lo (X DIFF minimal_elements X lo))) = 
      SOME x` 
         by METIS_TAC [] THEN
     Q.EXISTS_TAC `SUC i` THEN
     SRW_TAC [] [Once LUNFOLD, Once linear_order_to_list_f_def] THEN
     Q.UNABBREV_TAC `min` THEN
     SRW_TAC [] [] THEN
     `domain lo UNION range lo = X` 
             by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, in_domain, in_range, 
                                           linear_order_def, SUBSET_DEF] THEN
                 METIS_TAC []) THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC []]);

val linear_order_to_list_lem2 = Q.prove (
`!i lo X x. 
  linear_order lo X /\
  (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x)
  ==> 
  x IN X`,
Induct THEN
SRW_TAC [] [] THEN
POP_ASSUM (MP_TAC o SIMP_RULE (srw_ss()) [Once LUNFOLD]) THEN
SRW_TAC [] [] THEN
Cases_on `linear_order_to_list_f lo` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN
FULL_SIMP_TAC (srw_ss()) [linear_order_to_list_f_def, LET_THM] THEN
IMP_RES_TAC CHOICE_DEF THEN
SRW_TAC [] [] THENL
[FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, linear_order_def, in_domain,
                           in_range, SUBSET_DEF] THEN
     METIS_TAC [],
 `(domain lo UNION range lo DIFF 
   minimal_elements (domain lo UNION range lo) lo) SUBSET X`
         by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, linear_order_def, in_domain,
                                       in_range] THEN
             METIS_TAC []) THEN
     IMP_RES_TAC linear_order_subset THEN
     RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, in_domain, in_range, 
                               linear_order_def] THEN
     METIS_TAC []]);

val linear_order_to_list_lem3 = Q.prove (
`!s. FINITE s ==> 
  !lo X x y. 
    (x,y) IN lo /\
    (s = { z | (z,x) IN lo }) /\
    linear_order lo X /\
    finite_prefixes lo X
    ==> 
    ?i j. i <= j /\ 
          (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x) /\
          (LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME y)`,
HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION THEN
SRW_TAC [] [] THEN
`x IN X /\ y IN X`
        by (FULL_SIMP_TAC (srw_ss()) [linear_order_def, in_domain, in_range, 
                                      SUBSET_DEF] THEN
            METIS_TAC []) THEN
`SING (minimal_elements X lo)` 
        by METIS_TAC [finite_prefix_linear_order_has_unique_minimal, 
                      SUBSET_REFL] THEN
FULL_SIMP_TAC (srw_ss()) [SING_DEF] THEN
`{y | (y,x) IN rrestrict lo (X DIFF minimal_elements X lo) } PSUBSET 
 { y | (y,x) IN lo }`
        by (SRW_TAC [] [PSUBSET_DEF, in_rrestrict, SUBSET_DEF, EXTENSION] THEN
            FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION, 
                                      linear_order_def, transitive_def,
                                      antisym_def] THEN
            METIS_TAC []) THEN
`X DIFF minimal_elements X lo SUBSET X` by SRW_TAC [] [SUBSET_DEF] THEN
`linear_order (rrestrict lo (X DIFF minimal_elements X lo)) 
              (X DIFF minimal_elements X lo)` 
        by METIS_TAC [linear_order_subset] THEN
`finite_prefixes (rrestrict lo (X DIFF minimal_elements X lo)) 
                 (X DIFF minimal_elements X lo)` 
        by METIS_TAC [finite_prefixes_subset] THEN
Cases_on `x NOTIN X DIFF minimal_elements X lo` THENL
[Q.EXISTS_TAC `0` THEN
     SRW_TAC [] [Once LUNFOLD, linear_order_to_list_f_def, RIGHT_EXISTS_AND_THM]
     THENL
     [Q.UNABBREV_TAC `min` THEN
          `domain lo UNION range lo = X`
                  by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, in_domain, in_range,
                                                linear_order_def,
                                                SUBSET_DEF] THEN
                      METIS_TAC []) THEN
          SRW_TAC [] [] THEN
          FULL_SIMP_TAC (srw_ss()) [] THEN
          METIS_TAC [IN_SING],
      METIS_TAC [linear_order_to_list_lem1, finite_prefixes_def]],
 `y NOTIN minimal_elements X lo` 
         by (FULL_SIMP_TAC (srw_ss()) [minimal_elements_def, EXTENSION] THEN
             METIS_TAC []) THEN
     `(x,y) IN rrestrict lo (X DIFF minimal_elements X lo)`
             by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, in_rrestrict] THEN
                 METIS_TAC []) THEN
     `?i j. i <= j /\ 
        (LNTH i (LUNFOLD linear_order_to_list_f 
                         (rrestrict lo (X DIFF minimal_elements X lo))) 
         = SOME x) /\
        (LNTH j (LUNFOLD linear_order_to_list_f 
                         (rrestrict lo (X DIFF minimal_elements X lo))) 
         = SOME y)` 
             by METIS_TAC [] THEN
     Q.EXISTS_TAC `SUC i` THEN
     Q.EXISTS_TAC `SUC j` THEN
     SRW_TAC [] [] THEN
     SRW_TAC [] [Once LUNFOLD, Once linear_order_to_list_f_def] THEN
     SRW_TAC [] [markerTheory.Abbrev_def] THEN
     `domain lo UNION range lo = X`
             by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, in_domain, in_range, 
                                           linear_order_def, SUBSET_DEF] THEN
                 METIS_TAC []) THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     SRW_TAC [] []]);

val linear_order_to_list_lem4 = Q.prove (
`!i j lo X x. 
  linear_order lo X /\
  (LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME x) /\
  (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x)
  ==> 
  (i = j)`,
Induct THEN
SRW_TAC [] [] THEN
Cases_on `j` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
REPEAT (Q.PAT_ASSUM `LNTH a b = c` 
                    (MP_TAC o SIMP_RULE (srw_ss()) [Once LUNFOLD])) THEN
SRW_TAC [] [] THEN
Cases_on `linear_order_to_list_f lo` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `x'` THEN
FULL_SIMP_TAC (srw_ss()) [linear_order_to_list_f_def, LET_THM] THEN
IMP_RES_TAC CHOICE_DEF THEN
SRW_TAC [] [] THEN
`domain lo UNION range lo DIFF minimal_elements (domain lo UNION range lo) lo
 SUBSET X`
        by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, linear_order_def, in_domain, 
                                      in_range] THEN
            METIS_TAC []) THEN
IMP_RES_TAC linear_order_subset THENL
[`x IN (domain lo UNION range lo DIFF 
        minimal_elements (domain lo UNION range lo) lo)` 
         by METIS_TAC [linear_order_to_list_lem2] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC [],
 CCONTR_TAC THEN
     `CHOICE (minimal_elements (domain lo UNION range lo) lo) IN 
        (domain lo UNION range lo DIFF 
         minimal_elements (domain lo UNION range lo) lo)` 
             by METIS_TAC [linear_order_to_list_lem2] THEN
     FULL_SIMP_TAC (srw_ss()) [],
 RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, in_domain, in_range, 
                               linear_order_def] THEN
     METIS_TAC []]);
 
val linear_order_to_llist = Q.store_thm ("linear_order_to_llist",
`!lo X. 
  linear_order lo X /\
  finite_prefixes lo X
  ==> 
  ?ll. 
    (X = { x | ?i. LNTH i ll = SOME x }) /\
    lo SUBSET { (x,y) | ?i j. i <= j /\ (LNTH i ll = SOME x) /\ 
                              (LNTH j ll = SOME y) } /\
    (!i j x. (LNTH i ll = SOME x) /\ (LNTH j ll = SOME x) ==> (i = j))`,
SRW_TAC [] [] THEN
Q.EXISTS_TAC `LUNFOLD linear_order_to_list_f lo` THEN
SRW_TAC [] [SUBSET_DEF, EXTENSION] THEN1
METIS_TAC [linear_order_to_list_lem1, finite_prefixes_def,
linear_order_to_list_lem2] THENL
[`?y z. x = (y,z)`
         by (Cases_on `x` THEN
             METIS_TAC []) THEN
     SRW_TAC [] [] THEN
     `y IN X`
             by (FULL_SIMP_TAC (srw_ss()) [in_domain, linear_order_def, 
                                           SUBSET_DEF] THEN
                 METIS_TAC []) THEN 
     METIS_TAC [linear_order_to_list_lem3, finite_prefixes_def],
 METIS_TAC [linear_order_to_list_lem4]]);

end

val _ = export_theory();

end;
