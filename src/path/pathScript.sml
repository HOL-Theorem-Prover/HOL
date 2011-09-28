open HolKernel Parse boolLib

open bossLib llistTheory BasicProvers metisLib

local open pred_setLib fixedPointTheory rich_listTheory in end

val _ = augment_srw_ss [rewrites [LET_THM]]

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

val _ = export_rewrites
           ["stopped_at_11", "pcons_11", "stopped_at_not_pcons"]

val path_cases = store_thm(
  "path_cases",
  ``!p. (?x. p = stopped_at x) \/ (?x r q. p = pcons x r q)``,
  SIMP_TAC (srw_ss()) [stopped_at_def, pcons_def, forall_path,
                       exists_path, first_def, pairTheory.EXISTS_PROD,
                       pairTheory.FORALL_PROD] THEN
  PROVE_TAC [pairTheory.ABS_PAIR_THM, llistTheory.llist_CASES]);

val FORALL_path = store_thm(
  "FORALL_path",
  ``!P. (!p. P p) = (!x. P (stopped_at x)) /\ (!x r p. P (pcons x r p))``,
  GEN_TAC THEN EQ_TAC THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN SRW_TAC [][]);

val EXISTS_path = store_thm(
  "EXISTS_path",
  ``!P. (?p. P p) = (?x. P (stopped_at x)) \/ (?x r p. P (pcons x r p))``,
  SRW_TAC [][EQ_IMP_THM] THEN1
    (Q.SPEC_THEN `p` FULL_STRUCT_CASES_TAC path_cases THEN METIS_TAC []) THEN
  METIS_TAC []);

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

val _ = export_rewrites ["finite_thm"]

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

val _ = export_rewrites ["first_thm", "last_thm"]

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
val _ = export_rewrites ["pmap_thm"]

val first_pmap = store_thm(
  "first_pmap",
  ``!p. first (pmap f g p) = f (first p)``,
  CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][]);
val _ = export_rewrites ["first_pmap"]

val last_pmap = store_thm(
  "last_pmap",
  ``!p. finite p ==> (last (pmap f g p) = f (last p))``,
  HO_MATCH_MP_TAC finite_path_ind THEN SRW_TAC [][]);
val _ = export_rewrites ["last_pmap"]

val finite_pmap = store_thm(
  "finite_pmap",
  ``!(f:'a -> 'c) (g:'b -> 'd) p. finite (pmap f g p) = finite p``,
  Q_TAC SUFF_TAC
       `(!p. finite p ==> !(f:'a -> 'c) (g:'b -> 'd). finite (pmap f g p)) /\
        (!p. finite p ==> !(f:'a -> 'c) (g:'b -> 'd) p0. (
                                p = pmap f g p0) ==> finite p0)`
        THEN1 METIS_TAC [] THEN
  CONJ_TAC THEN HO_MATCH_MP_TAC finite_path_ind THEN
  SRW_TAC [][] THEN
  Q.ISPEC_THEN `p0` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
               path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);
val _ = export_rewrites ["finite_pmap"]



val tail_def =
    new_specification
      ("tail_def", ["tail"],
       prove(``?f. !x r p. f (pcons x r p) = p``,
             Q.EXISTS_TAC `\p. if ?x r q. p = pcons x r q then
                                @q. ?x r. p = pcons x r q
                               else ARB` THEN
                      SRW_TAC [][]));

val _ = export_rewrites ["tail_def"]

val first_label_def =
    new_specification
      ("first_label_def",["first_label"],
       prove(``?f. !x r p. f (pcons x r p) = r``,
                      Q.EXISTS_TAC `\p. if ?x r q. p = pcons x r q then
                                          @r. ?x q. p = pcons x r q
                                        else ARB` THEN SRW_TAC [][]));

val _ = export_rewrites ["first_label_def"]


(* ----------------------------------------------------------------------
    length : ('a,'b) path -> num option
      NONE indicates an infinite path
      SOME n indicates a path with n states, and n - 1 transitions
   ---------------------------------------------------------------------- *)

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

val finite_length_lemma = prove(
  ``!p. finite p = ?n. length p = SOME n``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC finite_path_ind THEN
    SRW_TAC [][length_thm],
    SIMP_TAC (srw_ss()) [GSYM LEFT_FORALL_IMP_THM] THEN
    Induct_on `n` THEN GEN_TAC THEN
    Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][length_thm]
  ]);


val finite_length = store_thm(
  "finite_length",
  ``!p. (finite p = (?n. length p = SOME n)) /\
        (~finite p = (length p = NONE))``,
  PROVE_TAC [finite_length_lemma, optionTheory.option_CASES,
             optionTheory.NOT_NONE_SOME]);


val length_pmap = store_thm(
  "length_pmap",
  ``!f g p. length (pmap f g p) = length p``,
  REPEAT GEN_TAC THEN Cases_on `finite p` THENL [
    Q_TAC SUFF_TAC `!p. finite p ==> (length (pmap f g p) = length p)` THEN1
          METIS_TAC [] THEN
    HO_MATCH_MP_TAC finite_path_ind THEN
    SRW_TAC [][length_thm],
    `~finite (pmap f g p)` by METIS_TAC [finite_pmap] THEN
    METIS_TAC [finite_length]
  ]);
val _ = export_rewrites ["length_pmap"]

(* ----------------------------------------------------------------------
    el : num -> ('a, 'b) path -> 'a

    return the nth state, counting from zero.  To be a valid index,
    n must be IN PL p.
   ---------------------------------------------------------------------- *)

val el_def = Define`
  (el 0 p = first p) /\ (el (SUC n) p = el n (tail p))
`;
val _ = export_rewrites ["el_def"]

(* ----------------------------------------------------------------------
    nth_label : num -> ('a,'b) path -> 'b

    returns the nth label, counting from zero up.  To be a valid index,
    n + 1 must be in PL p.
   ---------------------------------------------------------------------- *)

val nth_label_def = Define`
  (nth_label 0 p = first_label p) /\
  (nth_label (SUC n) p = nth_label n (tail p))
`;
val _ = export_rewrites ["nth_label_def"]

val path_Axiom = store_thm(
  "path_Axiom",
  ``!f: 'a -> 'b # ('c # 'a) option.
       ?g : 'a -> ('b, 'c) path.
         !x. g x = case f x of
                     (y, NONE) => stopped_at y
                   | (y, SOME (l, v)) => pcons y l (g v)``,
  GEN_TAC THEN
  STRIP_ASSUME_TAC
    (Q.ISPEC `\(x:'a,ks:'c option).
                  case ks of
                    NONE => NONE
                  | SOME k => (case f x : 'b # ('c # 'a) option of
                                 (y, NONE) => SOME((x, NONE), (k,y))
                               | (y, SOME (l, v)) => SOME((v, SOME l), (k,y)))`
             llist_Axiom) THEN
  Q.EXISTS_TAC `\x. case f x of
                      (y, NONE) => stopped_at y
                    | (y, SOME (l, v)) => toPath (y, g (v, SOME l))` THEN
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
    ASM_SIMP_TAC std_ss [],
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

(* ----------------------------------------------------------------------
    PL : ('a,'b) path -> num set

    PL(p) returns the set of valid indices into a path, where the index
    is going to extract a state.  When extracting labels (with nth_label),
    index + 1 must be in PL set for the path.  E.g., it's only valid to
    talk about the 0th label, if the list is two states long, and thus
    accepts indices {0, 1}.
   ---------------------------------------------------------------------- *)

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

val PL_thm = save_thm("PL_thm", CONJ PL_stopped_at PL_pcons);
val _ = export_rewrites ["PL_thm"]

val PL_0 = store_thm(
  "PL_0",
  ``!p. 0 IN PL p``,
  CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][])
val _ = export_rewrites ["PL_0"]


val PL_downward_closed = store_thm(
  "PL_downward_closed",
  ``!i p. i IN PL p ==> !j. j < i ==> j IN PL p``,
  SRW_TAC [][PL_def] THEN PROVE_TAC [arithmeticTheory.LESS_TRANS]);


val PL_pmap = store_thm(
  "PL_pmap",
  ``PL (pmap f g p) = PL p``,
  SRW_TAC [][PL_def, length_pmap, pred_setTheory.EXTENSION]);
val _ = export_rewrites ["PL_pmap"]

val el_pmap = store_thm(
  "el_pmap",
  ``!i p. i IN PL p ==> (el i (pmap f g p) = f (el i p))``,
  Induct THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][]);
val _ = export_rewrites ["el_pmap"]

val nth_label_pmap = store_thm(
  "nth_label_pmap",
  ``!i p. SUC i IN PL p ==> (nth_label i (pmap f g p) = g (nth_label i p))``,
  Induct THEN GEN_TAC THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][]);
val _ = export_rewrites ["nth_label_pmap"]

(* ---------------------------------------------------------------------- *)

val firstP_at_def =
    Define`firstP_at P p i = i IN PL p /\ P (el i p) /\
                             !j. j < i ==> ~P(el j p)`;

val firstP_at_stopped = prove(
  ``!P x n. firstP_at P (stopped_at x) n = (n = 0) /\ P x``,
  SIMP_TAC (srw_ss() ++ ARITH_ss) [firstP_at_def, EQ_IMP_THM,
                                   FORALL_AND_THM]);

val firstP_at_pcons = prove(
  ``!P n x r p.
       firstP_at P (pcons x r p) n =
          (n = 0) /\ P x \/ 0 < n /\ ~P x /\ firstP_at P p (n - 1)``,
 REPEAT GEN_TAC THEN Cases_on `n` THENL [
   SRW_TAC [ARITH_ss][firstP_at_def, PL_pcons],
   SRW_TAC [ARITH_ss][firstP_at_def, PL_pcons, EQ_IMP_THM]
   THENL [
     FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
     SRW_TAC [ARITH_ss][],
     FIRST_X_ASSUM (Q.SPEC_THEN `SUC j` MP_TAC) THEN
     SRW_TAC [ARITH_ss][],
     Cases_on `j` THEN SRW_TAC [ARITH_ss][]
   ]
 ]);

val firstP_at_thm = save_thm(
  "firstP_at_thm",
  CONJ firstP_at_stopped firstP_at_pcons);



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

val _ = export_rewrites ["exists_thm", "every_thm"]

val not_every = store_thm(
  "not_every",
  ``!P p. ~every P p = exists ($~ o P) p``,
  SRW_TAC [][every_def]);

val not_exists = store_thm(
  "not_exists",
  ``!P p. ~exists P p = every ($~ o P) p``,
  SRW_TAC [boolSimps.ETA_ss][every_def, combinTheory.o_DEF]);

val _ = export_rewrites ["not_exists", "not_every"]

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
  SRW_TAC [][mem_def, RIGHT_AND_OVER_OR,
             EXISTS_OR_THM, GSYM LEFT_EXISTS_AND_THM]);
val _ = export_rewrites ["mem_thm"]

(* ----------------------------------------------------------------------
    drop n p
       drops n elements from the front of p and returns what's left
   ---------------------------------------------------------------------- *)

val drop_def = Define`
  (drop 0 p = p) /\
  (drop (SUC n) p = drop n (tail p))
`;
val numeral_drop = save_thm(
  "numeral_drop",
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV (CONJUNCT2 drop_def));
val _ = export_rewrites ["drop_def", "numeral_drop"]


val finite_drop = store_thm(
  "finite_drop",
  ``!p n. n IN PL p ==> (finite (drop n p) = finite p)``,
  Induct_on `n` THENL [
    SRW_TAC [][],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][]
  ]);
val _ = export_rewrites ["finite_drop"]

val length_drop = store_thm(
  "length_drop",
  ``!p n. n IN PL p ==>
          (length (drop n p) = case (length p) of
                                 NONE => NONE
                               | SOME m => SOME (m - n))``,
  Induct_on `n` THENL [
    REPEAT STRIP_TAC THEN
    Cases_on `length p` THEN SRW_TAC [][drop_def],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][length_thm] THEN
    Cases_on `length p` THEN SRW_TAC [numSimps.ARITH_ss][] THEN
    PROVE_TAC [finite_length]
  ]);


val PL_drop = store_thm(
  "PL_drop",
  ``!p i. i IN PL p ==> (PL (drop i p) = IMAGE (\n. n - i) (PL p))``,
  Induct_on `i` THENL [
    SRW_TAC [][],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM] THENL [
      SRW_TAC [][LEFT_AND_OVER_OR, EXISTS_OR_THM,
                 GSYM RIGHT_EXISTS_AND_THM] THEN PROVE_TAC [],
      SRW_TAC [][] THEN PROVE_TAC [arithmeticTheory.LESS_EQ_REFL],
      SRW_TAC [][] THEN PROVE_TAC []
    ]
  ]);

val IN_PL_drop = store_thm(
  "IN_PL_drop",
  ``!i j p. i IN PL p ==> (j IN PL (drop i p) = i + j IN PL p)``,
  SRW_TAC [][PL_drop, EQ_IMP_THM] THENL [
    `(i + (n - i) = n) \/ (i + (n - i) = i)` by DECIDE_TAC THEN
    SRW_TAC [][],
    Q.EXISTS_TAC `i + j` THEN SRW_TAC [numSimps.ARITH_ss][]
  ]);
val _ = export_rewrites ["IN_PL_drop"]

val first_drop = store_thm(
  "first_drop",
  ``!i p. i IN PL p ==> (first (drop i p) = el i p)``,
  Induct THENL [
    SRW_TAC [][],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][]
  ]);
val _ = export_rewrites ["first_drop"]

val first_label_drop = store_thm(
  "first_label_drop",
  ``!i p. i IN PL p ==> (first_label (drop i p) = nth_label i p)``,
  Induct THENL [
    SRW_TAC [][nth_label_def],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][nth_label_def]
  ]);
val _ = export_rewrites ["first_label_drop"]

val tail_drop = store_thm(
  "tail_drop",
  ``!i p. (i + 1) IN PL p ==> (tail (drop i p) = drop (i + 1) p)``,
  Induct THEN
  CONV_TAC (HO_REWR_CONV FORALL_path) THEN
  SRW_TAC [][CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV drop_def] THEN
  FULL_SIMP_TAC (srw_ss()) [DECIDE ``SUC x + y = SUC (x + y)``]);
val _ = export_rewrites ["tail_drop"]

val el_drop = store_thm(
  "el_drop",
  ``!i j p. i + j IN PL p ==> (el i (drop j p) = el (i + j) p)``,
  Induct_on `j` THENL [
    SRW_TAC [][],
    GEN_TAC THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][arithmeticTheory.ADD_CLAUSES]
  ]);
val _ = export_rewrites ["el_drop"]

val nth_label_drop = store_thm(
  "nth_label_drop",
  ``!i j p.  SUC(i + j) IN PL p ==>
             (nth_label i (drop j p) = nth_label (i + j) p)``,
  Induct_on `j` THENL [
    SRW_TAC [][],
    GEN_TAC THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][arithmeticTheory.ADD_CLAUSES]
  ]);
val _ = export_rewrites ["nth_label_drop"]

(* ----------------------------------------------------------------------
    ``take n p`` takes n _labels_ from p
   ---------------------------------------------------------------------- *)

val take_def = Define`
  (take 0 p = stopped_at (first p)) /\
  (take (SUC n) p = pcons (first p) (first_label p) (take n (tail p)))
`;
val _ = export_rewrites ["take_def"]

val first_take = store_thm(
  "first_take",
  ``!p i. first (take i p) = first p``,
  REPEAT GEN_TAC THEN Cases_on `i` THEN SRW_TAC [][]);
val _ = export_rewrites ["first_take"]

val finite_take = store_thm(
  "finite_take",
  ``!p i. i IN PL p ==> finite (take i p)``,
  Induct_on `i` THENL [
    SRW_TAC [][finite_thm, take_def],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][take_def]
  ]);
val _ = export_rewrites ["finite_take"]

val length_take = store_thm(
  "length_take",
  ``!p i. i IN PL p ==> (length (take i p) = SOME (i + 1))``,
  Induct_on `i`  THENL [
    SRW_TAC [][length_thm, take_def],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][length_thm, arithmeticTheory.ADD1]
  ]);
val _ = export_rewrites ["length_take"]


val PL_take = store_thm(
  "PL_take",
  ``!p i. i IN PL p ==> (PL (take i p) = { n | n <= i })``,
  Induct_on `i` THENL [
    SRW_TAC [][],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][pred_setTheory.EXTENSION, EQ_IMP_THM] THEN
    SRW_TAC [][] THEN POP_ASSUM MP_TAC THEN Cases_on `x'` THEN SRW_TAC [][]
  ]);
val _ = export_rewrites ["PL_take"]

val last_take = store_thm(
  "last_take",
  ``!i p. i IN PL p ==> (last (take i p) = el i p)``,
  Induct_on `i` THENL [
    SRW_TAC [][],
    CONV_TAC (HO_REWR_CONV FORALL_path) THEN
    SRW_TAC [][]
  ]);
val _ = export_rewrites ["last_take"]

val nth_label_take = store_thm(
  "nth_label_take",
  ``!n p i. i < n /\ n IN PL p ==> (nth_label i (take n p) = nth_label i p)``,
  Induct THENL [
    SRW_TAC [][],
    GEN_TAC THEN
    Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN SRW_TAC [][] THEN
    Cases_on `i` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

(* ----------------------------------------------------------------------
    seg i j p
      is a path consisting of elements i to j from p
      has no useful meaning if i > j \/ j indexes beyond end of p
   ---------------------------------------------------------------------- *)

val seg_def = Define`
  seg i j p = take (j - i) (drop i p)
`;

val singleton_seg = store_thm(
  "singleton_seg",
  ``!i p. i IN PL p ==> (seg i i p = stopped_at (el i p))``,
  SRW_TAC [][seg_def]);
val _ = export_rewrites ["singleton_seg"]

val recursive_seg = store_thm(
  "recursive_seg",
  ``!i j p. i < j /\ j IN PL p ==>
            (seg i j p = pcons (el i p) (nth_label i p) (seg (i + 1) j p))``,
  SRW_TAC [][seg_def] THEN
  `~(j - i = 0)` by DECIDE_TAC THEN
  `?v. j - i = SUC v` by PROVE_TAC [arithmeticTheory.num_CASES] THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [PL_downward_closed, first_drop],
    PROVE_TAC [PL_downward_closed, first_label_drop],
    `j - (i + 1) = v` by DECIDE_TAC THEN
    SRW_TAC [][] THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    `i + 1 < j \/ (i + 1 = j)` by DECIDE_TAC THEN
    PROVE_TAC [tail_drop, PL_downward_closed]
  ]);


val PLdc_le = prove(
  ``i <= j ==> j IN PL p ==> i IN PL p``,
  PROVE_TAC [arithmeticTheory.LESS_OR_EQ, PL_downward_closed]);

val PL_seg = store_thm(
  "PL_seg",
  ``!i j p. i <= j /\ j IN PL p ==> (PL (seg i j p) = {n | n <= j - i})``,
  SRW_TAC [][seg_def] THEN `i IN PL p` by IMP_RES_TAC PLdc_le THEN
  SRW_TAC [numSimps.ARITH_ss][]);
val _ = export_rewrites ["PL_seg"]


val finite_seg = store_thm(
  "finite_seg",
  ``!p i j. i <= j /\ j IN PL p ==> finite (seg i j p)``,
  REPEAT STRIP_TAC THEN
  `i IN PL p` by IMP_RES_TAC PLdc_le THEN
  SRW_TAC [numSimps.ARITH_ss][seg_def]);
val _ = export_rewrites ["finite_seg"]

val first_seg = store_thm(
  "first_seg",
  ``!i j p. i <= j /\ j IN PL p ==> (first (seg i j p) = el i p)``,
  SRW_TAC [][seg_def] THEN IMP_RES_TAC PLdc_le THEN SRW_TAC [][]);
val _ = export_rewrites ["first_seg"]

val last_seg = store_thm(
  "last_seg",
  ``!i j p. i <= j /\ j IN PL p ==> (last (seg i j p) = el j p)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC PLdc_le THEN
  SRW_TAC [numSimps.ARITH_ss][seg_def]);
val _ = export_rewrites ["last_seg"]

(* ----------------------------------------------------------------------
    labels p  = lazy list of a path's labels
   ---------------------------------------------------------------------- *)

val labels_def =
    new_specification
     ("labels_def", ["labels"],
      prove(``?f. (!x. f (stopped_at x) = LNIL) /\
                  (!x r p. f (pcons x r p) = LCONS r (f p))``,
            STRIP_ASSUME_TAC
              (Q.ISPEC `\p. if ?x. p = stopped_at x then NONE
                            else SOME (tail p, first_label p)`
                       llist_Axiom_1) THEN
            Q.EXISTS_TAC `g` THEN
            REPEAT STRIP_TAC THEN
            POP_ASSUM
              (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
            SRW_TAC [][]));

val _ = export_rewrites ["labels_def"]


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

val _ = export_rewrites ["is_stopped_thm"]

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

val _ = print "Defining generation of paths from functions\n"

val pgenerate_t = ``\f. (FST (f 0), SOME (SND (f 0), f o SUC))``

val pgenerate_def = new_specification ("pgenerate_def",
  ["pgenerate"],
  prove(``?pg. !f g. pg f g = pcons (f 0) (g 0) (pg (f o SUC) (g o SUC))``,
        Q.X_CHOOSE_THEN `h` ASSUME_TAC
            (CONV_RULE SKOLEM_CONV (ISPEC pgenerate_t path_Axiom)) THEN
        Q.EXISTS_TAC `\f g. h (\x. (f x, g x))` THEN
        SIMP_TAC (srw_ss()) [] THEN REPEAT GEN_TAC THEN
        POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
        SIMP_TAC (srw_ss()) [combinTheory.o_DEF]));

val pgenerate_infinite = store_thm(
  "pgenerate_infinite",
  ``!f g. ~finite (pgenerate f g)``,
  Q_TAC SUFF_TAC `!p. finite p ==> !f g. ~(p = pgenerate f g)` THEN1
  PROVE_TAC [] THEN
  HO_MATCH_MP_TAC finite_path_ind THEN CONJ_TAC THENL [
    ONCE_REWRITE_TAC [pgenerate_def] THEN SRW_TAC [][],
    REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [pgenerate_def] THEN
    SRW_TAC [][]
  ]);

val pgenerate_not_stopped = store_thm(
  "pgenerate_not_stopped",
  ``!f g x. ~(stopped_at x = pgenerate f g)``,
  PROVE_TAC [pgenerate_infinite, finite_thm]);

val _ = export_rewrites ["pgenerate_not_stopped"]

val el_pgenerate = store_thm(
  "el_pgenerate",
  ``!n f g. el n (pgenerate f g) = f n``,
  Induct THEN ONCE_REWRITE_TAC [pgenerate_def] THEN SRW_TAC [][el_def]);

val nth_label_pgenerate = store_thm(
  "nth_label_pgenerate",
  ``!n f g. nth_label n (pgenerate f g) = g n``,
  Induct THEN ONCE_REWRITE_TAC [pgenerate_def] THEN SRW_TAC [][nth_label_def]);

val pgenerate_11 = store_thm(
  "pgenerate_11",
  ``!f1 g1 f2 g2. (pgenerate f1 g1 = pgenerate f2 g2) =
                  (f1 = f2) /\ (g1 = g2)``,
  SIMP_TAC (srw_ss()) [FORALL_AND_THM, EQ_IMP_THM] THEN
  SRW_TAC [][FUN_EQ_THM] THEN PROVE_TAC [el_pgenerate, nth_label_pgenerate]);


val pgenerate_onto = store_thm(
  "pgenerate_onto",
  ``!p. ~finite p ==> ?f g. p = pgenerate f g``,
  REPEAT STRIP_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`\n. el n p`, `\n. nth_label n p`] THEN
  ONCE_REWRITE_TAC [path_bisimulation] THEN
  Q.EXISTS_TAC
    `\x y. ~finite x /\ (y = pgenerate (\n. el n x) (\n. nth_label n x))` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  Q.SPEC_THEN `q1` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [pgenerate_def])) THEN
  SRW_TAC [][el_def, nth_label_def, combinTheory.o_DEF]);

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

infix |>
fun x |> f = f x

val okpath_co_ind = save_thm(
  "okpath_co_ind",
  okpath_monotone |> SPEC_ALL
                  |> MATCH_MP fixedPointTheory.gfp_coinduction
                  |> SIMP_RULE (srw_ss()) [pred_setTheory.SUBSET_DEF,
                                           GSYM okpath_def,
                                           okpath_f_def]
                  |> SIMP_RULE bool_ss [IN_DEF]
                  |> CONV_RULE (RENAME_VARS_CONV ["P"])
                  |> CONV_RULE
                      (STRIP_QUANT_CONV
                           (LAND_CONV (HO_REWR_CONV FORALL_path)))
                  |> SIMP_RULE (srw_ss()) []
                  |> CONV_RULE
                       (STRIP_QUANT_CONV
                          (LAND_CONV (RENAME_VARS_CONV ["x", "r", "p"]) THENC
                           RAND_CONV (RENAME_VARS_CONV ["p"]))))

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

val _ = export_rewrites ["okpath_thm"]

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

val okpath_pmap = store_thm(
  "okpath_pmap",
  ``!R f g p. okpath R p /\ (!x r y. R x r y ==> R (f x) (g r) (f y)) ==>
              okpath R (pmap f g p)``,
  REPEAT STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!p. (?p0. okpath R p0 /\ (p = pmap f g p0)) ==> okpath R p` THEN1
        METIS_TAC[] THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p0` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

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
                             (NONE, p) => pullapart (\t. (NONE, t)) p
                           | (SOME p1, p2) =>
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

val _ = export_rewrites ["plink_def"]


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
val _ = export_rewrites ["finite_plink"]


val first_plink = store_thm(
  "first_plink",
  ``!p1 p2. (last p1 = first p2) ==> (first (plink p1 p2) = first p1)``,
  CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][]);
val _ = export_rewrites ["first_plink"]


val last_plink = store_thm(
  "last_plink",
  ``!p1 p2. finite p1 /\ finite p2 /\ (last p1 = first p2) ==>
            (last (plink p1 p2) = last p2)``,
  Q_TAC SUFF_TAC `!p1. finite p1 ==>
                       !p2. finite p2 /\ (last p1 = first p2) ==>
                            (last (plink p1 p2) = last p2)`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC finite_path_ind THEN SRW_TAC [][]);
val _ = export_rewrites ["last_plink"]


val okpath_plink = store_thm(
  "okpath_plink",
  ``!R p1 p2. finite p1 /\ (last p1 = first p2) ==>
              (okpath R (plink p1 p2) = okpath R p1 /\ okpath R p2)``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC
        `!p1. finite p1 ==>
              !p2. (last p1 = first p2) ==>
                   (okpath R (plink p1 p2) = okpath R p1 /\ okpath R p2)`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC finite_path_ind THEN SRW_TAC [][] THEN PROVE_TAC []);
val _ = export_rewrites ["okpath_plink"]

val okpath_take = store_thm(
  "okpath_take",
  ``!R p i. i IN PL p /\ okpath R p ==> okpath R (take i p)``,
  Induct_on `i` THEN1 SRW_TAC [][] THEN
  GEN_TAC THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][]);
val _ = export_rewrites ["okpath_take"]

val okpath_drop = store_thm(
  "okpath_drop",
  ``!R p i. i IN PL p /\ okpath R p ==> okpath R (drop i p)``,
  Induct_on `i` THEN1 SRW_TAC [][] THEN
  GEN_TAC THEN CONV_TAC (HO_REWR_CONV FORALL_path) THEN SRW_TAC [][]);
val _ = export_rewrites ["okpath_drop"]

val okpath_seg = store_thm(
  "okpath_seg",
  ``!R p i j. i <= j /\ j IN PL p /\ okpath R p ==> okpath R (seg i j p)``,
  SRW_TAC [][seg_def] THEN IMP_RES_TAC PLdc_le THEN
  SRW_TAC [numSimps.ARITH_ss][]);
val _ = export_rewrites ["okpath_seg"]

(* "strongly normalising" for labelled transition relations *)
val SN_def = Define`
  SN R = WF (\x y. ?l. R y l x)
`;

val SN_finite_paths = store_thm(
  "SN_finite_paths",
  ``!R p. SN R /\ okpath R p ==> finite p``,
  SIMP_TAC (srw_ss()) [SN_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP relationTheory.WF_INDUCTION_THM) THEN
  SIMP_TAC (srw_ss()) [GSYM LEFT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!x p. (x = first p) /\ okpath R p ==> finite p`
                                                THEN1 SRW_TAC [][] THEN
  POP_ASSUM HO_MATCH_MP_TAC THEN SIMP_TAC (srw_ss()) [] THEN GEN_TAC THEN
  STRIP_TAC THEN GEN_TAC THEN
  Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val finite_paths_SN = store_thm(
  "finite_paths_SN",
  ``!R. (!p. okpath R p ==> finite p) ==> SN R``,
  SRW_TAC [][SN_def, prim_recTheory.WF_IFF_WELLFOUNDED,
             prim_recTheory.wellfounded_def] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  POP_ASSUM (Q.X_CHOOSE_THEN `g` ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
  Q_TAC SUFF_TAC `okpath R (pgenerate f g)` THEN1
        PROVE_TAC [pgenerate_infinite] THEN
  Q_TAC SUFF_TAC `!p. (?n. p = pgenerate (f o (+) n) (g o (+) n)) ==>
                      okpath R p` THEN1
        (SIMP_TAC (srw_ss()) [GSYM LEFT_FORALL_IMP_THM] THEN
         DISCH_THEN (Q.SPEC_THEN `0` MP_TAC) THEN
         SIMP_TAC (srw_ss() ++ boolSimps.ETA_ss)
                  [combinTheory.o_DEF]) THEN
  HO_MATCH_MP_TAC okpath_co_ind THEN REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [pgenerate_def])) THEN
  SRW_TAC [][] THENL [
    ONCE_REWRITE_TAC [pgenerate_def] THEN
    ASM_SIMP_TAC (srw_ss()) [GSYM arithmeticTheory.ADD1],
    Q.EXISTS_TAC `SUC n` THEN
    SIMP_TAC (srw_ss()) [combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES]
  ]);

val SN_finite_paths_EQ = store_thm(
  "SN_finite_paths_EQ",
  ``!R. SN R = !p. okpath R p ==> finite p``,
  PROVE_TAC [finite_paths_SN, SN_finite_paths]);

val labels_LMAP = Q.store_thm
("labels_LMAP",
 `!p. labels p = LMAP FST (SND (fromPath p))`,
 HO_MATCH_MP_TAC LLIST_EQ THEN
 SRW_TAC [] [] THEN
 ASSUME_TAC (Q.SPEC `p` path_cases) THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [stopped_at_def, pcons_def,
                           path_rep_bijections_thm] THEN
 METIS_TAC []);

local

val lemma = Q.prove (
 `!x.
    labels (plink (FST x) (SND x)) = LAPPEND (labels (FST x)) (labels (SND x))`,
 HO_MATCH_MP_TAC LLIST_EQ THEN
 SRW_TAC [] [] THEN
 Cases_on `x` THEN
 SRW_TAC [] [] THEN
 ASSUME_TAC (Q.SPEC `q` path_cases) THEN
 ASSUME_TAC (Q.SPEC `r` path_cases) THEN
 SRW_TAC [] [] THEN
 SRW_TAC [] [] THEN
 METIS_TAC [pairTheory.FST, pairTheory.SND, labels_def, plink_def, LAPPEND]);

in

val labels_plink = Q.store_thm
("labels_plink",
 `!p1 p2. labels (plink p1 p2) = LAPPEND (labels p1) (labels p2)`,
 METIS_TAC [pairTheory.FST, pairTheory.SND, lemma]);

end;

val finite_labels = Q.store_thm
("finite_labels",
 `!p. LFINITE (labels p) = finite p`,
 SRW_TAC [] [labels_LMAP, LFINITE_MAP, finite_def]);

val unfold_def =
  Define `unfold proj f s =
            toPath
              (proj s,
               LUNFOLD (\s. OPTION_MAP (\(next_s,lbl).
                                           (next_s,(lbl,proj next_s)))
                                       (f s))
                       s)`;

val unfold_thm = Q.store_thm
("unfold_thm",
 `!proj f s.
   unfold proj f s =
     case f s of
       NONE => stopped_at (proj s)
     | SOME (s',l) => pcons (proj s) l (unfold proj f s')`,
 SRW_TAC [] [unfold_def] THEN
 Cases_on `f s` THEN
 SRW_TAC [] [stopped_at_def, pcons_def, toPath_11, Once LUNFOLD] THEN
 Cases_on `x` THEN
 SRW_TAC [] [toPath_11, path_rep_bijections_thm, first_def]);

val unfold_thm2 = Q.store_thm
("unfold_thm2",
 `!proj f x v1 v2.
    ((f x = NONE) ==> (unfold proj f x = stopped_at (proj x))) /\
    ((f x = SOME (v1,v2)) ==>
     (unfold proj f x = pcons (proj x) v2 (unfold proj f v1)))`,
 SRW_TAC [] [] THEN1
 SRW_TAC [] [Once unfold_thm] THEN
 SRW_TAC [] [Once unfold_thm]);

val labels_unfold = Q.store_thm
("labels_unfold",
 `!proj f s. labels (unfold proj f s) = LUNFOLD f s`,
 SRW_TAC [] [labels_LMAP, unfold_def, path_rep_bijections_thm, LMAP_LUNFOLD,
             optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] THEN
 `!s. (OPTION_MAP (\x. (\(x,y). (x,FST y))
                         ((\(next_s,lbl). (next_s,lbl,proj next_s)) x))
                  (f s) =
       f s)`
         by (Cases_on `f s` THEN
             SRW_TAC [] [] THEN
             Cases_on `x` THEN
             SRW_TAC [] []) THEN
SRW_TAC [] [] THEN
METIS_TAC []);

val okpath_co_ind2 = Q.prove (
`!P R p.
  (!x r p. P (pcons x r p) ==> R x r (first p) /\ P p) /\ P p ==> okpath R p`,
METIS_TAC [okpath_co_ind]);

val okpath_unfold = Q.store_thm
("okpath_unfold",
 `!P m proj f s.
     P s /\
     (!s s' l. P s /\ (f s = SOME (s', l)) ==> P s') /\
     (!s s' l. P s /\ (f s = SOME (s',l)) ==> m (proj s) l (proj s'))
     ==>
     okpath m (unfold proj f s)`,
 SRW_TAC [] [] THEN
 HO_MATCH_MP_TAC okpath_co_ind2 THEN
 SRW_TAC [] [] THEN
 Q.EXISTS_TAC `\p. ?s. P s /\ (p = unfold proj f s)` THEN
 SRW_TAC [] [] THENL
 [FULL_SIMP_TAC (srw_ss()) [Once unfold_thm] THEN
      Cases_on `f s'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `x'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [Once unfold_thm] THEN
      Cases_on `f q` THEN
      SRW_TAC [] [] THEN
      Cases_on `x` THEN
      SRW_TAC [] [],
  POP_ASSUM (MP_TAC o SIMP_RULE (srw_ss()) [Once unfold_thm]) THEN
      SRW_TAC [] [] THEN
      Cases_on `f s'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `x'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      METIS_TAC [],
  METIS_TAC []]);

val trace_machine_def =
  Define `trace_machine P s l s' = (P (s++[l])) /\ (s' = s++[l])`;

local

val lemma1 = Q.prove (
`!l h t. LTAKE (SUC (LENGTH l)) (LAPPEND (fromList l) (h:::t)) = SOME (l++[h])`,
Induct THEN
SRW_TAC [] [LTAKE_CONS_EQ_SOME]);

val lemma2 = Q.prove (
`!l h t. LAPPEND (fromList l) (h:::t) =  LAPPEND (fromList (l++[h])) t`,
Induct THEN
SRW_TAC [] []);

in

val trace_machine_thm = Q.store_thm
("trace_machine_thm",
 `!P tr.
    (!n l. (LTAKE n tr = SOME l) ==> P l)
    ==>
    ?p. (tr = labels p) /\ okpath (trace_machine P) p /\ (first p = [])`,
 SRW_TAC [] [] THEN
 Q.EXISTS_TAC `unfold (\(s,tr). s)
                      (\(s,tr).
                         (if tr = [||] then
                            NONE
                          else
                            SOME ((s++[(THE (LHD tr))],(THE (LTL tr))),
                                  THE (LHD tr))))
                      ([],tr)` THEN
 SRW_TAC [] [labels_unfold] THENL
 [MATCH_MP_TAC (GSYM LUNFOLD_EQ) THEN
      Q.EXISTS_TAC `\(s,tr) tr'. (tr = tr')` THEN
      SRW_TAC [] [] THEN
      Cases_on `s` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `(ll = [||]) \/ ?h t. ll = h:::t` by METIS_TAC [llist_CASES] THEN
      SRW_TAC [] [],
  MATCH_MP_TAC okpath_unfold THEN
      Q.EXISTS_TAC `\(s,tr). (!n l. (LTAKE n (LAPPEND (fromList s) tr) = SOME l)
                                    ==>
                                    P l)` THEN
      SRW_TAC [] [] THEN1
      METIS_TAC [] THENL
      [Cases_on `s'` THEN
           SRW_TAC [] [] THEN
           Cases_on `s` THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           `?h t. r' = h:::t` by METIS_TAC [llist_CASES] THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           METIS_TAC [lemma2],
       SRW_TAC [] [trace_machine_def] THEN
           Cases_on `s` THEN
           Cases_on `s'` THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           `?h t. r = h:::t` by METIS_TAC [llist_CASES] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           METIS_TAC [lemma1]],
  SRW_TAC [] [Once unfold_thm]]);

end;

val trace_machine_thm2 = Q.store_thm
("trace_machine_thm2",
 `!n l P p init.
    okpath (trace_machine P) p /\
    P (first p)
    ==>
    ((LTAKE n (labels p) = SOME l) ==> P (first p ++ l))`,
 Induct_on `n` THEN
 SRW_TAC [] [] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [LTAKE] THEN
 Cases_on `LHD (labels p)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `LTAKE n (THE (LTL (labels p)))` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 `(?x. p = stopped_at x) \/ (?h l p'. p = pcons h l p')`
                  by METIS_TAC [path_cases] THEN
 FULL_SIMP_TAC (srw_ss()) [trace_machine_def] THEN
 SRW_TAC [] [] THEN
 METIS_TAC [listTheory.APPEND, listTheory.APPEND_ASSOC]);

local

val lemma = Q.prove (
`!n p. (LTAKE n (labels p) = NONE) = n NOTIN PL p`,
 Induct THEN
 SRW_TAC [] [] THEN
 `(?x. p = stopped_at x) \/ (?h l t. p = pcons h l t)`
            by METIS_TAC [path_cases] THEN
 SRW_TAC [] []);

in

val LTAKE_labels = Q.store_thm
("LTAKE_labels",
 `!n p l.
    (LTAKE n (labels p) = SOME l)
    =
    n IN PL p /\ (toList (labels (take n p)) = SOME l)`,
 Induct THEN
 SRW_TAC [] [toList_THM, LTAKE] THEN
 `(?x. p = stopped_at x) \/ (?h l t. p = pcons h l t)`
            by METIS_TAC [path_cases] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 Cases_on `LTAKE n (labels t)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THENL
 [METIS_TAC [lemma],
  METIS_TAC [optionTheory.SOME_11]]);

end;

val drop_eq_pcons = Q.store_thm
("drop_eq_pcons",
 `!n p h l t. n IN PL p /\ (drop n p = pcons h l t) ==> n + 1 IN PL p`,
 Induct THEN
 SRW_TAC [] [] THEN
 `(?x. p = stopped_at x) \/ (?h l t. p = pcons h l t)`
              by METIS_TAC [path_cases] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 RES_TAC THEN
 Q.EXISTS_TAC `n+1` THEN
 SRW_TAC [] [] THEN
 DECIDE_TAC);

val parallel_comp_def =
  Define `parallel_comp m1 m2 (s1,s2) l (s1',s2') =
            m1 s1 l s1' /\ m2 s2 l s2'`;

val okpath_parallel_comp = Q.store_thm
("okpath_parallel_comp",
  `!p m1 m2.
     okpath (parallel_comp m1 m2) p
     =
     okpath m1 (pmap FST (\x.x) p) /\ okpath m2 (pmap SND (\x.x) p)`,
 SRW_TAC [] [] THEN
 EQ_TAC THEN
 SRW_TAC [] [] THEN
 MATCH_MP_TAC okpath_co_ind2 THENL
 [Q.EXISTS_TAC `\p'. ?n. n IN PL p /\ okpath (parallel_comp m1 m2) (drop n p) /\
                         (p' = pmap FST (\x.x) (drop n p))` THEN
      SRW_TAC [] [] THENL
      [`(?x. (drop n p) = stopped_at x) \/ (?h l t. (drop n p) = pcons h l t)`
                         by METIS_TAC [path_cases] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [okpath_thm] THEN
           SRW_TAC [] [] THEN
           Cases_on `h` THEN
           Cases_on `first t` THEN
           FULL_SIMP_TAC (srw_ss()) [parallel_comp_def],
       `(?x. (drop n p) = stopped_at x) \/ (?h l t. (drop n p) = pcons h l t)`
                         by METIS_TAC [path_cases] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           SRW_TAC [] [] THEN
           IMP_RES_TAC drop_eq_pcons THEN
           Q.EXISTS_TAC `n+1` THEN
           SRW_TAC [] [] THEN
           METIS_TAC [tail_drop, tail_def],
       Q.EXISTS_TAC `0` THEN
           SRW_TAC [] []],
  Q.EXISTS_TAC `\p'. ?n. n IN PL p /\ okpath (parallel_comp m1 m2) (drop n p) /\
                         (p' = pmap SND (\x.x) (drop n p))` THEN
      SRW_TAC [] [] THENL
      [`(?x. (drop n p) = stopped_at x) \/ (?h l t. (drop n p) = pcons h l t)`
                          by METIS_TAC [path_cases] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [okpath_thm] THEN
           SRW_TAC [] [] THEN
           Cases_on `h` THEN
           Cases_on `first t` THEN
           FULL_SIMP_TAC (srw_ss()) [parallel_comp_def],
       `(?x. (drop n p) = stopped_at x) \/ (?h l t. (drop n p) = pcons h l t)`
                          by METIS_TAC [path_cases] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           SRW_TAC [] [] THEN
           IMP_RES_TAC drop_eq_pcons THEN
           Q.EXISTS_TAC `n+1` THEN
           SRW_TAC [] [] THEN
           METIS_TAC [tail_drop, tail_def],
       Q.EXISTS_TAC `0` THEN
           SRW_TAC [] []],
  Q.EXISTS_TAC `\p'. ?n. n IN PL p /\ okpath m1 (pmap FST (\x.x) p') /\
                    okpath m2 (pmap SND (\x.x) p') /\ (p' = drop n p)` THEN
      SRW_TAC [] [] THENL
      [Cases_on `x` THEN
           Cases_on `first p'` THEN
           FULL_SIMP_TAC (srw_ss()) [parallel_comp_def],
       `(?x. (drop n p) = stopped_at x) \/ (?h l t. (drop n p) = pcons h l t)`
                       by METIS_TAC [path_cases] THEN
           SRW_TAC [] [] THEN
           FULL_SIMP_TAC (srw_ss()) [] THEN
           SRW_TAC [] [] THEN
           IMP_RES_TAC drop_eq_pcons THEN
           Q.EXISTS_TAC `n+1` THEN
           SRW_TAC [] [] THEN
           METIS_TAC [tail_drop, tail_def],
       Q.EXISTS_TAC `0` THEN
           SRW_TAC [] []]]);

val build_pcomp_trace = Q.store_thm
("build_pcomp_trace",
 `!m1 p1 m2 p2.
   okpath m1 p1 /\ okpath m2 p2 /\ (labels p1 = labels p2)
   ==>
   ?p. okpath (parallel_comp m1 m2) p /\ (labels p = labels p1) /\
       (first p = (first p1, first p2))`,
 SRW_TAC [] [] THEN
 Q.EXISTS_TAC `unfold (\(p1,p2). (first p1, first p2))
                 (\(p1,p2).
                     if is_stopped p1 \/ is_stopped p2 then
                       NONE
                     else
                       SOME ((tail p1, tail p2), first_label p1))
                 (p1,p2)` THEN
 SRW_TAC [] [labels_unfold] THENL
 [HO_MATCH_MP_TAC okpath_unfold THEN
      Q.EXISTS_TAC `\(p1,p2). okpath m1 p1 /\ okpath m2 p2 /\
                              (labels p1 = labels p2)` THEN
      SRW_TAC [] [] THEN
      Cases_on `s` THEN
      Cases_on `s'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `?s l p s' l' p'. (r = pcons s l p) /\ (q = pcons s' l' p')`
                  by METIS_TAC [path_cases, is_stopped_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [parallel_comp_def],
  MATCH_MP_TAC LUNFOLD_EQ THEN
      Q.EXISTS_TAC `\(p1,p2) tr. (labels p1 = tr) /\
                                 (labels p1 = labels p2)` THEN
      SRW_TAC [] [] THEN
      Cases_on `s` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `(?x. q = stopped_at x) \/ ?h t p. q = pcons h t p`
                   by METIS_TAC [path_cases] THEN
      `(?x. r = stopped_at x) \/ ?h t p. r = pcons h t p`
                   by METIS_TAC [path_cases] THEN
      FULL_SIMP_TAC (srw_ss()) [],
  SRW_TAC [] [Once unfold_thm]]);

val nth_label_LNTH = Q.store_thm
("nth_label_LNTH",
 `!n p x.
    (LNTH n (labels p) = SOME x) = (n + 1 IN PL p /\ (nth_label n p = x))`,
 Induct THEN
 SRW_TAC [] [] THEN
 `(labels p = [||]) \/ ?h t. labels p = h:::t` by METIS_TAC [llist_CASES] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 `(?x. p = stopped_at x) \/ ?h l p'. p = pcons h l p'`
                by METIS_TAC [path_cases] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 EQ_TAC THEN
 SRW_TAC [] [] THENL
 [Q.EXISTS_TAC `n + 1` THEN
      SRW_TAC [] [] THEN
      DECIDE_TAC,
  `n + 1 = x'` by DECIDE_TAC THEN
      SRW_TAC [] []]);

val nth_label_LTAKE = Q.store_thm
("nth_label_LTAKE",
 `!n p l i v.
   (LTAKE n (labels p) = SOME l) /\
   i < LENGTH l
   ==>
   (nth_label i p = EL i l)`,
 Induct THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [LTAKE_SNOC_LNTH] THEN
 Cases_on `LTAKE n (labels p)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `LNTH n (labels p)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 `i < LENGTH x \/ (i = LENGTH x)` by DECIDE_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN1
 METIS_TAC [rich_listTheory.EL_APPEND1] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [nth_label_LNTH] THEN
 METIS_TAC [LTAKE_LENGTH, listTheory.SNOC_APPEND, listTheory.EL_LENGTH_SNOC]);

val finite_path_end_cases = Q.store_thm
("finite_path_end_cases",
 `!p.
    finite p ==>
    (?x. p = stopped_at x) \/
    (?p' l s. p = plink p' (pcons (last p') l (stopped_at s)))`,
 HO_MATCH_MP_TAC finite_path_ind THEN
 SRW_TAC [] [] THENL
 [Q.EXISTS_TAC `stopped_at x` THEN
      SRW_TAC [] [],
  Q.EXISTS_TAC `pcons x r p'` THEN
      SRW_TAC [] [] THEN
      METIS_TAC []]);

val simulation_trace_inclusion = Q.store_thm ("simulation_trace_inclusion",
`!R M1 M2 p t_init.
   (!s1 l s2 t1. R s1 t1 /\ M1 s1 l s2 ==> ?t2. R s2 t2 /\ M2 t1 l t2) /\
   okpath M1 p /\
   R (first p) t_init
   ==>
   ?q. okpath M2 q /\ (labels p = labels q) /\ (first q = t_init)`,
SRW_TAC [] [] THEN
`?next_t. !s1 l s2 t1. R s1 t1 /\ M1 s1 l s2 ==>
     R s2 (next_t s1 l s2 t1) /\ M2 t1 l (next_t s1 l s2 t1)` by
            METIS_TAC [SKOLEM_THM] THEN
Q.EXISTS_TAC `unfold (\(p,t). t)
                     (\(p,t). if is_stopped p then
                                NONE
                              else
                                SOME ((tail p,
                                       next_t (first p)
                                              (first_label p)
                                              (first (tail p)) t),
                                      first_label p))
                     (p,t_init)` THEN
SRW_TAC [] [] THENL
[HO_MATCH_MP_TAC okpath_unfold THEN
     Q.EXISTS_TAC `\(p',t_init'). okpath M1 p' /\ R (first p') t_init'` THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     Cases_on `s` THEN
     Cases_on `s'` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     `?s l p. q = pcons s l p` by METIS_TAC [path_cases, is_stopped_def] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     SRW_TAC [] [],
 SRW_TAC [] [labels_unfold] THEN
     MATCH_MP_TAC (GSYM LUNFOLD_EQ) THEN
     Q.EXISTS_TAC `\(p,i) tr'. (labels p = tr')` THEN
     SRW_TAC [] [] THEN
     Cases_on `s` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     SRW_TAC [] [] THEN
     `(?x. q = stopped_at x) \/ ?h l p. q = pcons h l p`
                       by METIS_TAC [path_cases] THEN
     SRW_TAC [] [],
 SRW_TAC [] [Once unfold_def, first_def, path_rep_bijections_thm]]);


val _ = export_theory();

