open HolKernel Parse boolLib

open bossLib llistTheory

local open pred_setLib fixedPointTheory in end

val _ = new_theory "path";

val path_TY_DEF = new_type_definition (
  "path",
  prove(``?x :('a # ('b # 'a) llist). (\x. T) x``,
        BETA_TAC THEN REWRITE_TAC [EXISTS_SIMP]));

val path_absrep_bijections =
    define_new_type_bijections { ABS = "toPath", REP = "fromPath",
                                 name = "path_absrep_bijections",
                                 tyax = path_TY_DEF};

val path_rep_bijections_thm = save_thm(
  "path_rep_bijections_thm",
  REWRITE_RULE [] (BETA_RULE path_absrep_bijections));

val toPath_11 = save_thm(
  "toPath_11",
  REWRITE_RULE [] (BETA_RULE (prove_abs_fn_one_one path_absrep_bijections)));
val fromPath_11 = save_thm(
  "fromPath_11",
  prove_rep_fn_one_one path_absrep_bijections);


val fromPath_onto = save_thm(
  "fromPath_onto",
  REWRITE_RULE [] (BETA_RULE (prove_rep_fn_onto path_absrep_bijections)));
val toPath_onto = save_thm(
  "toPath_onto",
  SIMP_RULE std_ss [] (prove_abs_fn_onto path_absrep_bijections));

val _ = augment_srw_ss [rewrites [path_rep_bijections_thm,
                                  toPath_11, fromPath_11]]

val path_eq_fromPath = prove(
  ``!p q. (p = q) = (fromPath p = fromPath q)``,
  SRW_TAC [][]);

val forall_path = prove(
  ``(!p. P p) = !r. P (toPath r)``,
  SRW_TAC [][EQ_IMP_THM] THEN PROVE_TAC [toPath_onto]);
val exists_path = prove(
  ``(?p. P p) = ?r. P (toPath r)``,
  SRW_TAC [][EQ_IMP_THM] THEN PROVE_TAC [toPath_onto]);

val first_def = Define`first (p:('a,'b) path) = FST (fromPath p)`;
val stopped_at_def = Define`stopped_at x:('a,'b) path = toPath (x, LNIL)`;
val pcons_def =
    Define`pcons x r p : ('a,'b) path =
                      toPath (x, LCONS (r, first p) (SND (fromPath p)))`;

val stopped_at_11 = store_thm(
  "stopped_at_11",
  ``!x y. (stopped_at x = stopped_at y : ('a,'b) path) = (x = y)``,
  SRW_TAC [][stopped_at_def]);
val pcons_11 = store_thm(
  "pcons_11",
  ``!x r p y s q.
       (pcons x r p = pcons y s q) = (x = y) /\ (r = s) /\ (p = q)``,
  SRW_TAC [][pcons_def, first_def] THEN
  REWRITE_TAC [path_eq_fromPath, pairTheory.PAIR_FST_SND_EQ, CONJ_ASSOC]);

val stopped_at_not_pcons = store_thm(
  "stopped_at_not_pcons",
  ``!x y r p. ~(stopped_at x = pcons y r p) /\ ~(pcons y r p = stopped_at x)``,
  SRW_TAC [][stopped_at_def, pcons_def]);

val _ = BasicProvers.export_rewrites ["stopped_at_11", "pcons_11",
                                      "stopped_at_not_pcons"]

val path_cases = store_thm(
  "path_cases",
  ``!p. (?x. p = stopped_at x) \/ (?x r q. p = pcons x r q)``,
  SIMP_TAC (srw_ss()) [stopped_at_def, pcons_def, forall_path,
                       exists_path, first_def, pairTheory.EXISTS_PROD,
                       pairTheory.FORALL_PROD] THEN
  PROVE_TAC [pairTheory.ABS_PAIR_THM, llistTheory.llist_CASES]);

val first_thm = store_thm(
  "first_thm",
  ``(!x. first (stopped_at x : ('a,'b) path) = x) /\
    (!x r p. first (pcons x r p : ('a,'b) path) = x)``,
  SRW_TAC [][first_def, stopped_at_def, pcons_def]);

val finite_def =
  Define`finite (sigma : ('a,'b) path) = LFINITE (SND (fromPath sigma))`;
val finite_thm = store_thm(
  "finite_thm",
  ``(!x. finite (stopped_at x : ('a,'b) path) = T) /\
    (!x r p. finite (pcons x r p : ('a,'b) path) = finite p)``,
  SRW_TAC [][finite_def, pcons_def, stopped_at_def, llistTheory.LFINITE_THM]);

val _ = BasicProvers.export_rewrites ["finite_thm"]

val last_thm =
    new_specification
      ("last_thm", ["last"],
       prove(
        ``?f. (!x. f (stopped_at x) = x) /\
              (!x r p. f (pcons x r p) = f p)``,
        Q.EXISTS_TAC `\p. if finite p then
                            if SND (fromPath p) = LNIL then first p
                            else SND (LAST (THE (toList (SND (fromPath p)))))
                          else ARB` THEN
        SRW_TAC [][finite_def, stopped_at_def, first_def, pcons_def,
                   toList_THM, LFINITE_THM] THEN
        IMP_RES_TAC LFINITE_toList THEN
        `?h t. SND (fromPath p) = LCONS h t` by PROVE_TAC [llist_CASES] THEN
        FULL_SIMP_TAC (srw_ss()) [toList_THM]));

val _ = BasicProvers.export_rewrites ["first_thm", "last_thm"]

val path_bisimulation = store_thm(
  "path_bisimulation",
  ``!p1 p2.
       (p1 = p2) =
       ?R. R p1 p2 /\
           !q1 q2.
              R q1 q2 ==>
              (?x. (q1 = stopped_at x) /\ (q2 = stopped_at x)) \/
              (?x r q1' q2'.
                   (q1 = pcons x r q1') /\ (q2 = pcons x r q2') /\
                   R q1' q2')``,
  SIMP_TAC (srw_ss()) [pcons_def, stopped_at_def, pairTheory.FORALL_PROD,
                       EQ_IMP_THM, FORALL_AND_THM, forall_path,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  CONJ_TAC THENL [
    REPEAT GEN_TAC THEN
    Q.REFINE_EXISTS_TAC `\p q. R' (SND (fromPath p)) (SND (fromPath q)) /\
                                  (first p = first q)` THEN
    SRW_TAC [][first_def] THEN
    Q.ISPECL_THEN [`p_2`,`p_2`] (STRIP_ASSUME_TAC o
                                 REWRITE_RULE []) LLIST_BISIMULATION THEN
    Q.EXISTS_TAC `R` THEN SRW_TAC [][] THEN
    Q.ISPEC_THEN `p_2''` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 llist_CASES THEN
    SRW_TAC [][] THEN
    Q.ISPEC_THEN `p_2'''` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                 llist_CASES THEN SRW_TAC [][]
    THENL [
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [LHD_THM],
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [LHD_THM],
      `(LHD (LCONS h t) = LHD (LCONS h' t')) /\
       R (THE (LTL (LCONS h t))) (THE (LTL (LCONS h' t')))` by
         PROVE_TAC [llistTheory.LCONS_NOT_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [LHD_THM, LTL_THM] THEN
      Cases_on `h` THEN SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`toPath (r, t)`, `toPath (r, t')`] THEN
      SRW_TAC [][]
    ],

    REPEAT STRIP_TAC THENL [
      RES_TAC THEN SRW_TAC [][],
      ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
      Q.EXISTS_TAC `\x y. ?x' y'. R (toPath (x', x)) (toPath (y', y))` THEN
      SRW_TAC [][] THENL [
        PROVE_TAC [],
        `(ll3 = LNIL) /\ (ll4 = LNIL) \/
         ?r q1' q2'. (ll3 = LCONS (r, first q1') (SND (fromPath q1'))) /\
                     (ll4 = LCONS (r, first q2') (SND (fromPath q2'))) /\
                     (x' = y') /\ R q1' q2'`
                                by (RES_TAC THEN SRW_TAC [][] THEN
                                    PROVE_TAC [])
        THENL [
          SRW_TAC [][],
          SRW_TAC [][LHD_THM, LTL_THM] THENL [
            `?q11 q12 q21 q22. (q1' = toPath (q11, q12)) /\
                               (q2' = toPath (q21, q22))` by
                PROVE_TAC [toPath_onto, pairTheory.ABS_PAIR_THM] THEN
            NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
            RES_TAC THEN SRW_TAC [][first_def],
            MAP_EVERY Q.EXISTS_TAC [`FST (fromPath q1')`,
                                    `FST (fromPath q2')`] THEN
            SRW_TAC [][]
          ]
        ]
      ]
    ]
  ]);

val finite_path_ind = store_thm(
  "finite_path_ind",
  ``!P.  (!x. P (stopped_at x)) /\
         (!x r p. finite p /\ P p ==> P (pcons x r p)) ==>
         (!q. finite q ==> P q)``,
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC (srw_ss()) [forall_path, pairTheory.FORALL_PROD, finite_def] THEN
  Q_TAC SUFF_TAC
        `(!pl. LFINITE pl ==> !x. P (toPath (x, pl)))` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  FULL_SIMP_TAC (srw_ss()) [finite_def, pcons_def, stopped_at_def,
                            pairTheory.FORALL_PROD, first_def, forall_path]);


val pmap_def =
    Define`pmap f g (p:('a,'b) path):('c,'d) path =
             toPath ((f ## LMAP (g ## f)) (fromPath p))`;

val pmap_thm = store_thm(
  "pmap_thm",
  ``(!x. pmap f g (stopped_at x) = stopped_at (f x)) /\
    (!x r p.
         pmap f g (pcons x r p) = pcons (f x) (g r) (pmap f g p))``,
  SRW_TAC [][pmap_def, stopped_at_def, pcons_def, first_def]);


val tail_def =
    new_specification
      ("tail_def", ["tail"],
       prove(``?f. !x r p. f (pcons x r p) = p``,
             Q.EXISTS_TAC `\p. if ?x r q. p = pcons x r q then
                                @q. ?x r. p = pcons x r q
                               else ARB` THEN
                      SRW_TAC [][]));

val _ = BasicProvers.export_rewrites ["tail_def"]

val first_label_def =
    new_specification
      ("first_label_def",["first_label"],
       prove(``?f. !x r p. f (pcons x r p) = r``,
                      Q.EXISTS_TAC `\p. if ?x r q. p = pcons x r q then
                                          @r. ?x q. p = pcons x r q
                                        else ARB` THEN SRW_TAC [][]));

val _ = BasicProvers.export_rewrites ["first_label_def"]


val length_def =
    Define`length p = if finite p then
                        SOME (LENGTH (THE (toList (SND (fromPath p)))) + 1)
                      else NONE`;

val length_thm = store_thm(
  "length_thm",
  ``(!x. length (stopped_at x) = SOME 1) /\
    (!x r p. length (pcons x r p) =
                if finite p then SOME (THE (length p) + 1)
                else NONE)``,
  SRW_TAC [][length_def, finite_def, stopped_at_def, pcons_def, toList_THM,
             LFINITE_THM] THEN
  IMP_RES_TAC LFINITE_toList THEN
  SRW_TAC [numSimps.ARITH_ss][]);

val alt_length_thm = store_thm(
  "alt_length_thm",
  ``(!x. length (stopped_at x) = SOME 1) /\
    (!x r p. length (pcons x r p) = OPTION_MAP SUC (length p))``,
  SRW_TAC [][length_def, finite_def, stopped_at_def, pcons_def, toList_THM,
             LFINITE_THM] THEN
  IMP_RES_TAC LFINITE_toList THEN
  SRW_TAC [numSimps.ARITH_ss][]);

val length_never_zero = store_thm(
  "length_never_zero",
  ``!p. ~(length p = SOME 0)``,
  GEN_TAC THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][alt_length_thm]);

val el_def = Define`(el 0 p = first p) /\ (el (SUC n) p = el n (tail p))`;

val path_Axiom = store_thm(
  "path_Axiom",
  ``!f: 'a -> 'b # ('c # 'a) option.
       ?g : 'a -> ('b, 'c) path.
         !x. g x = case f x of
                      (y, NONE) -> stopped_at y
                   || (y, SOME (l, v)) -> pcons y l (g v)``,
  GEN_TAC THEN
  STRIP_ASSUME_TAC
    (Q.ISPEC `\(x:'a,ks:'c option).
                  case ks of
                   NONE -> NONE
                || SOME k -> (case f x : 'b # ('c # 'a) option of
                                 (y, NONE) -> SOME((x, NONE), (k,y))
                              || (y, SOME (l, v)) -> SOME((v, SOME l), (k,y)))`
             llist_Axiom) THEN
  Q.EXISTS_TAC `\x. case f x of
                      (y, NONE) -> stopped_at y
                   || (y, SOME (l, v)) -> toPath (y, g (v, SOME l))` THEN
  SRW_TAC [][] THEN
  `?y lvs. f x = (y, lvs)` by PROVE_TAC [pairTheory.ABS_PAIR_THM] THEN
  SRW_TAC [][] THEN
  `(lvs = NONE) \/ (?l v. lvs = SOME(l, v))` by
      PROVE_TAC [pairTheory.ABS_PAIR_THM, optionTheory.option_CASES] THEN
  SRW_TAC [][] THEN
  SRW_TAC [][pcons_def] THEN
  ASM_SIMP_TAC (srw_ss()) [LHDTL_EQ_SOME] THEN
  `?u lvt. f v = (u, lvt)` by PROVE_TAC [pairTheory.ABS_PAIR_THM] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `(lvt = NONE) \/ (?m t. lvt = SOME (m, t))` by
      PROVE_TAC [pairTheory.ABS_PAIR_THM, optionTheory.option_CASES] THEN
  ASM_SIMP_TAC (srw_ss()) [] THENL [
    SRW_TAC [][stopped_at_def] THEN
    Q_TAC SUFF_TAC `LHD (g (v, NONE)) = NONE` THEN1
      PROVE_TAC [LHD_EQ_NONE] THEN
    ASM_SIMP_TAC (srw_ss()) [],
    ASM_SIMP_TAC (srw_ss()) [first_def]
  ]);


val pconcat_def =
    Define`pconcat p1 lab p2 =
             toPath (first p1, LAPPEND (SND (fromPath p1))
                                       (LCONS (lab,first p2)
                                              (SND (fromPath p2))))`;

val pconcat_thm = store_thm(
  "pconcat_thm",
  ``(!x lab p2. pconcat (stopped_at x) lab p2 = pcons x lab p2) /\
    (!x r p lab p2.
                pconcat (pcons x r p) lab p2 = pcons x r (pconcat p lab p2))``,
  SRW_TAC [][pconcat_def, pcons_def, first_def, stopped_at_def]);

val pconcat_eq_stopped = store_thm(
  "pconcat_eq_stopped",
  ``!p1 lab p2 x. ~(pconcat p1 lab p2 = stopped_at x)  /\
                  ~(stopped_at x = pconcat p1 lab p2)``,
  GEN_TAC THEN
  Q.ISPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][pconcat_thm]);

val pconcat_eq_pcons = store_thm(
  "pconcat_eq_pcons",
  ``!x r p p1 lab p2. ((pconcat p1 lab p2 = pcons x r p) =
                       (lab = r) /\ (p1 = stopped_at x) /\ (p = p2) \/
                       (?p1'. (p1 = pcons x r p1') /\
                              (p = pconcat p1' lab p2))) /\
                      ((pcons x r p = pconcat p1 lab p2) =
                       (lab = r) /\ (p1 = stopped_at x) /\ (p = p2) \/
                       (?p1'. (p1 = pcons x r p1') /\
                              (p = pconcat p1' lab p2)))``,
  REPEAT GEN_TAC THEN
  Q.ISPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][pconcat_thm] THEN PROVE_TAC []);

val finite_pconcat = store_thm(
  "finite_pconcat",
  ``!p1 lab p2. finite (pconcat p1 lab p2) = finite p1 /\ finite p2``,
  Q_TAC SUFF_TAC
        `(!p1 : ('a,'b) path.
              finite p1 ==>
              !lab p2. finite p2 ==> finite (pconcat p1 lab p2)) /\
         (!p : ('a, 'b) path.
              finite p ==> !p1 p2 lab. (p = pconcat p1 lab p2) ==>
                                       finite p1 /\ finite p2)` THEN1
        PROVE_TAC [] THEN
  CONJ_TAC THEN HO_MATCH_MP_TAC finite_path_ind THEN
  SRW_TAC [][pconcat_thm, pconcat_eq_stopped,
             pconcat_eq_pcons] THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val PL_def = Define`PL p = { i | finite p ==> i < THE (length p) }`

val infinite_PL = store_thm(
  "infinite_PL",
  ``!p. ~finite p ==> !i. i IN PL p``,
  SRW_TAC [][PL_def]);

val PL_pcons = store_thm(
  "PL_pcons",
  ``!x r q. PL (pcons x r q) = 0 INSERT IMAGE SUC (PL q)``,
  SRW_TAC [ARITH_ss]
          [PL_def, pred_setTheory.EXTENSION, length_thm,
           EQ_IMP_THM, arithmeticTheory.ADD1]
  THENL [
    Cases_on `x'` THEN
    SRW_TAC [ARITH_ss][arithmeticTheory.ADD1] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    DECIDE_TAC,
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val PL_stopped_at = store_thm(
  "PL_stopped_at",
  ``!x. PL (stopped_at x) = {0}``,
  SRW_TAC [ARITH_ss][pred_setTheory.EXTENSION, PL_def, length_thm]);

val PL_thm = save_thm("PL_thm", CONJ PL_stopped_at PL_pcons)

val PL_downward_closed = store_thm(
  "PL_downward_closed",
  ``!i p. i IN PL p ==> !j. j < i ==> j IN PL p``,
  SRW_TAC [][PL_def] THEN PROVE_TAC [arithmeticTheory.LESS_TRANS]);

val firstP_at_def =
    Define`firstP_at P p i = i IN PL p /\ P (el i p) /\
                             !j. j < i ==> ~P(el j p)`;

val firstP_at_stopped = prove(
  ``!P x n. firstP_at P (stopped_at x) n = (n = 0) /\ P x``,
  SIMP_TAC (srw_ss() ++ ARITH_ss) [firstP_at_def, PL_thm, EQ_IMP_THM,
                                   FORALL_AND_THM, el_def]);

val firstP_at_pcons = prove(
  ``!P n x r p.
       firstP_at P (pcons x r p) n =
          (n = 0) /\ P x \/ 0 < n /\ ~P x /\ firstP_at P p (n - 1)``,
 REPEAT GEN_TAC THEN Cases_on `n` THENL [
   SRW_TAC [ARITH_ss][firstP_at_def, PL_pcons, el_def],
   SRW_TAC [ARITH_ss][firstP_at_def, PL_pcons, el_def,
                      EQ_IMP_THM]
   THENL [
     FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
     SRW_TAC [ARITH_ss][el_def],
     FIRST_X_ASSUM (Q.SPEC_THEN `SUC j` MP_TAC) THEN
     SRW_TAC [ARITH_ss][el_def],
     Cases_on `j` THEN SRW_TAC [ARITH_ss][el_def]
   ]
 ]);

val firstP_at_thm = save_thm(
  "firstP_at_thm",
  CONJ firstP_at_stopped firstP_at_pcons);

val FORALL_path = store_thm(
  "FORALL_path",
  ``!P. (!p. P p) = (!x. P (stopped_at x)) /\ (!x r p. P (pcons x r p))``,
  GEN_TAC THEN EQ_TAC THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN SRW_TAC [][]);


val firstP_at_zero = store_thm(
  "firstP_at_zero",
  ``!P p. firstP_at P p 0 = P (first p)``,
  GEN_TAC THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN
  SIMP_TAC (srw_ss()) [firstP_at_thm]);

val exists_def = Define`exists P p = ?i. firstP_at P p i`
val every_def = Define`every P p = ~exists ($~ o P) p`

val exists_thm = store_thm(
  "exists_thm",
  ``!P. (!x. exists P (stopped_at x) = P x) /\
        (!x r p. exists P (pcons x r p) = P x \/ exists P p)``,
  SRW_TAC [][exists_def, firstP_at_thm, EQ_IMP_THM, EXISTS_OR_THM] THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    Cases_on `P x` THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `SUC i` THEN SRW_TAC [ARITH_ss][]
  ]);

val every_thm = store_thm(
  "every_thm",
  ``!P. (!x. every P (stopped_at x) = P x) /\
        (!x r p. every P (pcons x r p) = P x /\ every P p)``,
  SRW_TAC [][every_def, exists_thm]);

val _ = BasicProvers.export_rewrites ["exists_thm", "every_thm"]

val not_every = store_thm(
  "not_every",
  ``!P p. ~every P p = exists ($~ o P) p``,
  SRW_TAC [][every_def]);

val not_exists = store_thm(
  "not_exists",
  ``!P p. ~exists P p = every ($~ o P) p``,
  SRW_TAC [boolSimps.ETA_ss][every_def, combinTheory.o_DEF]);

val _ = BasicProvers.export_rewrites ["not_exists", "not_every"]

val exists_el = store_thm(
  "exists_el",
  ``!P p. exists P p = ?i. i IN PL p /\ P (el i p)``,
  SRW_TAC [][exists_def, firstP_at_def] THEN EQ_TAC THENL [
    PROVE_TAC [],
    DISCH_THEN (STRIP_ASSUME_TAC o CONV_RULE numLib.EXISTS_LEAST_CONV) THEN
    PROVE_TAC [PL_downward_closed]
  ]);

val every_el = store_thm(
  "every_el",
  ``!P p. every P p = !i. i IN PL p ==> P (el i p)``,
  REWRITE_TAC [every_def, exists_el] THEN SRW_TAC [][] THEN PROVE_TAC []);

val every_coinduction = store_thm(
  "every_coinduction",
  ``!P Q. (!x. P (stopped_at x) ==> Q x) /\
          (!x r p. P (pcons x r p) ==> Q x /\ P p) ==>
          (!p. P p ==> every Q p)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [every_def, exists_def] THEN
  SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC SWAP_VARS_CONV THEN Induct THEN
  CONV_TAC (HO_REWR_CONV FORALL_path) THENL [
    SRW_TAC [][firstP_at_thm, combinTheory.o_THM] THEN PROVE_TAC [],
    SRW_TAC [ARITH_ss][firstP_at_thm] THEN PROVE_TAC []
  ]);

val double_neg_lemma = prove(``$~ o $~ o P = P``,
                             SRW_TAC [][FUN_EQ_THM, combinTheory.o_THM])

val exists_induction = save_thm(
  "exists_induction",
  (SIMP_RULE (srw_ss()) [double_neg_lemma] o
   Q.SPECL [`(~) o P`, `(~) o Q`] o
   CONV_RULE (STRIP_QUANT_CONV
                (FORK_CONV (EVERY_CONJ_CONV
                              (STRIP_QUANT_CONV CONTRAPOS_CONV),
                            STRIP_QUANT_CONV CONTRAPOS_CONV)) THENC
              SIMP_CONV (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]))
  every_coinduction);

val mem_def = Define`mem s p = ?i. i IN PL p /\ (s = el i p)`;

val mem_thm = store_thm(
  "mem_thm",
  ``(!x s. mem s (stopped_at x) = (s = x)) /\
    (!x r p s. mem s (pcons x r p) = (s = x) \/ mem s p)``,
  SRW_TAC [][mem_def, PL_thm, el_def, RIGHT_AND_OVER_OR,
             EXISTS_OR_THM, GSYM LEFT_EXISTS_AND_THM]);

val drop_def = Define`(drop 0 p = p) /\
                      (drop (SUC n) p = drop n (tail p))`;

val _ = BasicProvers.export_rewrites ["mem_thm", "drop_def"]

val chop_narrows_def =
    Define`chop_narrows n p =
             if length p = SOME 1 then
               NONE
             else if n = 0 then
               SOME(stopped_at (first p), first_label p, tail p)
             else
               OPTION_MAP (\ (seg1, lab, seg2).
                             (pcons (first p) (first_label p) seg1,
                              lab,
                              seg2)) (chop_narrows (n - 1) (tail p))`;

val chop_narrows_thm = store_thm(
  "chop_narrows_thm",
  ``(!x n. chop_narrows n (stopped_at x) = NONE) /\
    (!x r p.
           chop_narrows 0 (pcons x r p) = SOME(stopped_at x, r, p)) /\
    (!x r p n.
           chop_narrows (SUC n) (pcons x r p) =
               case chop_narrows n p of
                  NONE -> NONE
               || SOME (seg1, lab, seg2) -> SOME(pcons x r seg1, lab, seg2))``,
  ONCE_REWRITE_TAC [chop_narrows_def] THEN
  SRW_TAC [][alt_length_thm,
             DECIDE ``(1 = SUC z) = (z = 0)``, length_never_zero]
  THENL [
    ONCE_REWRITE_TAC [chop_narrows_def] THEN SRW_TAC [][],
    ONCE_REWRITE_TAC [chop_narrows_def] THEN SRW_TAC [][],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [chop_narrows_def])) THEN
    SRW_TAC [ARITH_ss][] THEN
    Cases_on `chop_narrows (n - 1) (tail p)` THEN SRW_TAC [][] THEN
    Cases_on `x'` THEN Cases_on `r'` THEN
    SRW_TAC [][]
  ]);

val chop_narrows_eq_SOME = store_thm(
  "chop_narrows_eq_SOME",
  ``!p i. i + 1 IN PL p ==>
          (?seg1 lab seg2. chop_narrows i p = SOME(seg1, lab, seg2))``,
  CONV_TAC SWAP_VARS_CONV THEN SIMP_TAC (srw_ss()) [PL_def] THEN Induct THEN
  GEN_TAC THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [numSimps.REDUCE_ss, ARITH_ss][PL_def, length_thm, chop_narrows_thm,
                                         arithmeticTheory.ADD1] THEN
  `finite q ==> i + 1 < THE (length q)` by (SRW_TAC [][] THEN
                                            RES_TAC THEN
                                            DECIDE_TAC) THEN
  `?s1 l s2. chop_narrows i q = SOME(s1, l, s2)` by PROVE_TAC [] THEN
  SRW_TAC [][]);


val chop_narrows_pconcat = store_thm(
  "chop_narrows_pconcat",
  ``!i p. i + 1 IN PL p ==>
          let (s1, l, s2) = THE (chop_narrows i p)
          in
              finite s1 /\ (pconcat s1 l s2 = p)``,
  Induct THEN REPEAT STRIP_TAC THENL [
    `?s1 l s2. chop_narrows 0 p = SOME (s1, l, s2)`
       by PROVE_TAC [chop_narrows_eq_SOME] THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    Q.SPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [PL_def, length_thm,
                                          chop_narrows_thm] THEN
    SRW_TAC [][pconcat_thm],

    Q.SPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                path_cases
    THENL [
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [length_thm,
                                            chop_narrows_thm, PL_def],

      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [PL_pcons,
                                            GSYM arithmeticTheory.ADD1] THEN
      SRW_TAC [][chop_narrows_thm] THEN
      `?s1 l s2. chop_narrows i q = SOME (s1, l, s2)` by
          PROVE_TAC [REWRITE_RULE [GSYM arithmeticTheory.ADD1]
                                  chop_narrows_eq_SOME] THEN
      FIRST_ASSUM (ASSUME_TAC o Q.AP_TERM `THE`) THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `q` MP_TAC) THEN
      FULL_SIMP_TAC (srw_ss()) [pconcat_thm]
    ]
  ]);

val labels_def =
    new_specification
     ("labels_def", ["labels"],
      prove(``?f. (!x. f (stopped_at x) = LNIL) /\
                  (!x r p. f (pcons x r p) = LCONS r (f p))``,
            STRIP_ASSUME_TAC
              (Q.ISPEC `\p. if ?x. p = stopped_at x then NONE
                            else SOME (tail p, first_label p)`
                       llist_Axiom) THEN
            Q.EXISTS_TAC `g` THEN
            SRW_TAC [][LHDTL_EQ_SOME, GSYM LHD_EQ_NONE]));

val _ = BasicProvers.export_rewrites ["labels_def"]


val firstP_at_unique = store_thm(
  "firstP_at_unique",
  ``!P p n. firstP_at P p n ==> !m. firstP_at P p m = (m = n)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN GEN_TAC THEN
  CONV_TAC SWAP_VARS_CONV THEN Induct THENL [
    SIMP_TAC (srw_ss()) [firstP_at_zero] THEN
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][firstP_at_thm],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [ARITH_ss][firstP_at_thm] THEN
    `m - 1 = n` by PROVE_TAC [] THEN SRW_TAC [ARITH_ss][]
  ]);

val is_stopped_def = Define`is_stopped p = ?x. p = stopped_at x`;

val is_stopped_thm = store_thm(
  "is_stopped_thm",
  ``(!x. is_stopped (stopped_at x) = T) /\
    (!x r p. is_stopped (pcons x r p) = F)``,
  SRW_TAC [][is_stopped_def]);

val _ = BasicProvers.export_rewrites ["is_stopped_thm"]

val filter_def =
    new_specification
     ("filter_def", ["filter"],
      prove(``?f. !P.
                    (!x. P x ==> (f P (stopped_at x) = stopped_at x)) /\
                    (!x r p.
                        f P (pcons x r p) =
                          if P x then
                             if exists P p then pcons x r (f P p)
                             else stopped_at x
                          else f P p)``,
            STRIP_ASSUME_TAC
              ((CONV_RULE SKOLEM_CONV o
                GEN_ALL o
                Q.ISPEC `\p. let n = @n. firstP_at P p n in
                             let r = drop n p in
                               (first r,
                                if is_stopped r \/ ~exists P (tail r) then NONE
                                else SOME(first_label r, tail r))`)
                 path_Axiom) THEN
            Q.EXISTS_TAC `\P p. if exists P p then g P p else ARB` THEN
            SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
              ONCE_ASM_REWRITE_TAC [] THEN
              FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
              ASM_SIMP_TAC (srw_ss()) [firstP_at_thm, drop_def,
                                       is_stopped_def],
              Cases_on `P x` THENL [
                FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
                FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o
                               assert (is_forall o concl)) THEN
                SRW_TAC [][firstP_at_thm] THEN
                FULL_SIMP_TAC bool_ss [every_def, double_neg_lemma],
                FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
                COND_CASES_TAC THEN REWRITE_TAC [] THEN
                FIRST_X_ASSUM (fn th =>
                                  ONCE_REWRITE_TAC
                                    [assert (is_forall o concl) th]) THEN
                ASM_SIMP_TAC (srw_ss()) [firstP_at_thm] THEN
                Q.ABBREV_TAC `n = @n. firstP_at P p n` THEN
                `(@n. 0 < n /\ firstP_at P p (n - 1)) = SUC n` by
                     (FULL_SIMP_TAC (srw_ss()) [exists_def] THEN
                      `!m. firstP_at P p m = (m = i)`
                          by PROVE_TAC [firstP_at_unique] THEN
                      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [
                        DECIDE ``0 < n /\ (n - 1 = m) = (n = m + 1)``]) THEN
                ASM_SIMP_TAC (srw_ss())[drop_def]
              ]
            ]));


val filter_eq_stopped = prove(
  ``!P p. exists P p ==> !x. (filter P p = stopped_at x) ==> P x``,
  GEN_TAC THEN HO_MATCH_MP_TAC exists_induction THEN
  SRW_TAC [][filter_def]);

val filter_eq_pcons = prove(
  ``!P p. exists P p ==> !x r q. (filter P p = pcons x r q) ==>
                                 P x /\
                                 ?q0. (q = filter P q0) /\ exists P q0``,
  GEN_TAC THEN HO_MATCH_MP_TAC exists_induction THEN
  SRW_TAC [][filter_def] THEN PROVE_TAC []);

val filter_every = store_thm(
  "filter_every",
  ``!P p. exists P p ==> every P (filter P p)``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!p. (?q. (p = filter P q) /\ exists P q) ==>
                      every P p` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC every_coinduction THEN
  PROVE_TAC [filter_eq_stopped, filter_eq_pcons]);

val _ = print "Defining path OK-ness\n"

val okpath_f_def =
    Define`okpath_f R (X :('a,'b) path set) =
              { stopped_at x | x IN UNIV } UNION
              { pcons x r p | R x r (first p) /\ p IN X }`;

val okpath_monotone = store_thm(
  "okpath_monotone",
  ``!R. monotone (okpath_f R)``,
  SRW_TAC [][fixedPointTheory.monotone_def, okpath_f_def,
             pred_setTheory.SUBSET_DEF] THEN PROVE_TAC []);

val okpath_def = Define`okpath R = gfp (okpath_f R)`;

val okpath_co_ind = save_thm(
  "okpath_co_ind",
  (GEN_ALL o
   CONV_RULE (RENAME_VARS_CONV ["P"]) o
   SIMP_RULE (srw_ss()) [pred_setTheory.SPECIFICATION] o
   SIMP_RULE (srw_ss()) [pred_setTheory.SUBSET_DEF, GSYM okpath_def,
                         okpath_f_def])
    (MATCH_MP fixedPointTheory.gfp_coinduction
              (SPEC_ALL okpath_monotone)));

val okpath_cases = save_thm(
  "okpath_cases",
  (GEN_ALL o
   SIMP_RULE (srw_ss()) [pred_setTheory.SPECIFICATION] o
   SIMP_RULE (srw_ss()) [pred_setTheory.EXTENSION,
                         okpath_f_def, GSYM okpath_def] o
   CONJUNCT1)
    (MATCH_MP fixedPointTheory.gfp_greatest_fixedpoint
              (SPEC_ALL okpath_monotone)))

val okpath_thm = store_thm(
  "okpath_thm",
  ``!R. (!x. okpath R (stopped_at x)) /\
        (!x r p. okpath R (pcons x r p) = R x r (first p) /\ okpath R p)``,
  REPEAT STRIP_TAC THENL [
    ONCE_REWRITE_TAC [okpath_cases] THEN SRW_TAC [][],
    CONV_TAC (LAND_CONV (REWR_CONV okpath_cases)) THEN SRW_TAC [][]
  ]);

val _ = BasicProvers.export_rewrites ["okpath_thm"]

val finite_okpath_ind = store_thm(
  "finite_okpath_ind",
  ``!R.
        (!x. P (stopped_at x)) /\
        (!x r p. okpath R p /\ finite p /\ R x r (first p) /\ P p ==>
                 P (pcons x r p)) ==>
        !sigma. okpath R sigma /\ finite sigma ==> P sigma``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!sigma. finite sigma ==> okpath R sigma ==> P sigma` THEN1
        PROVE_TAC [] THEN
  HO_MATCH_MP_TAC finite_path_ind THEN
  ASM_SIMP_TAC (srw_ss()) []);

val plink_def = new_specification(
  "plink_def",
  ["plink"],
  prove(``?f. (!x p. f (stopped_at x) p = p) /\
              (!x r p1 p2. f (pcons x r p1) p2 = pcons x r (f p1 p2))``,
        STRIP_ASSUME_TAC
        (Q.ISPEC `\pair. let pullapart g p = (first p,
                                              if is_stopped p then NONE
                                              else SOME (first_label p,
                                                         g (tail p)))
                         in
                           case pair of
                              (NONE, p) -> pullapart (\t. (NONE, t)) p
                           || (SOME p1, p2) ->
                              if is_stopped p1 then
                                pullapart (\t. (NONE, t)) p2
                              else
                                pullapart (\t. (SOME t, p2)) p1`
                 path_Axiom) THEN
        Q.EXISTS_TAC `\p1 p2. g (SOME p1, p2)` THEN
        SIMP_TAC (srw_ss()) [] THEN
        FIRST_ASSUM (fn th => CONV_TAC
                              (BINOP_CONV
                               (STRIP_QUANT_CONV
                                (LAND_CONV (REWR_CONV th))))) THEN
        SIMP_TAC (srw_ss()) [] THEN
        Ho_Rewrite.ONCE_REWRITE_TAC [FORALL_path] THEN
        SIMP_TAC (srw_ss()) [] THEN
        ONCE_REWRITE_TAC [path_bisimulation] THEN GEN_TAC THEN
        Q.EXISTS_TAC `\p1 p2. (p1 = g (NONE, p2))` THEN
        SIMP_TAC (srw_ss()) [] THEN
        Ho_Rewrite.ONCE_REWRITE_TAC [FORALL_path] THEN
        SIMP_TAC (srw_ss()) [] THEN
        POP_ASSUM  (fn th => CONV_TAC
                              (BINOP_CONV
                               (STRIP_QUANT_CONV
                                (LAND_CONV (REWR_CONV th))))) THEN
        SRW_TAC [][]));

val _ = BasicProvers.export_rewrites ["plink_def"]

val plink_okpath = store_thm(
  "plink_okpath",
  ``!R p1. okpath R p1 /\ finite p1 ==>
           !p2. okpath R p2 /\ (last p1 = first p2) ==>
                okpath R (plink p1 p2)``,
  GEN_TAC THEN HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][] THEN
  Q.ISPEC_THEN `p` (REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) []);

val finite_plink = store_thm(
  "finite_plink",
  ``!p1 p2. finite (plink p1 p2) = finite p1 /\ finite p2``,
  Q_TAC SUFF_TAC
     `(!p1:('a,'b)path. finite p1 ==>
                        !p2. finite p2 ==> finite (plink p1 p2)) /\
      !p:('a,'b)path.   finite p ==>
                        !p1 p2. (p = plink p1 p2) ==> finite p1 /\ finite p2`
     THEN1 PROVE_TAC [] THEN CONJ_TAC THEN
  HO_MATCH_MP_TAC finite_path_ind THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p1` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val _ = BasicProvers.export_rewrites ["finite_plink"]

val _ = export_theory();

