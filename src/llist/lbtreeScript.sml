open HolKernel Parse boolLib bossLib

open boolSimps BasicProvers llistTheory;

(* ----------------------------------------------------------------------
    a theory of "lazy" binary trees; that is potentially infinite binary
    tree, with constructors
       Lf : 'a lbtree
       Nd : 'a -> 'a lbtree -> 'a lbtree -> 'a lbtree
   ---------------------------------------------------------------------- *)

val _ = new_theory "lbtree"

(* set up the representative type and operations on it *)

val Lfrep_def = Define`Lfrep = \l. NONE`

val Ndrep_def = Define`
   Ndrep a t1 t2 = \l. case l of
                         [] -> SOME a
                      || T::xs -> t1 xs
                      || F::xs -> t2 xs
`;

val is_lbtree_def = Define`
  is_lbtree t = ?P. (!t. P t ==> (t = Lfrep) \/
                                 ?a t1 t2. P t1 /\ P t2 /\
                                           (t = Ndrep a t1 t2)) /\
                    P t
`;

val type_inhabited = prove(
  ``?t. is_lbtree t``,
  Q.EXISTS_TAC `Lfrep` THEN SRW_TAC [][is_lbtree_def] THEN
  Q.EXISTS_TAC `(=) Lfrep` THEN SRW_TAC [][]);

val lbtree_tydef = new_type_definition ("lbtree", type_inhabited)

val repabs_fns = define_new_type_bijections {
  name = "lbtree_absrep",
  ABS = "lbtree_abs",
  REP = "lbtree_rep",
  tyax = lbtree_tydef
};

val (lbtree_absrep, lbtree_repabs) = CONJ_PAIR repabs_fns
val _ = BasicProvers.augment_srw_ss [rewrites [lbtree_absrep]]

val is_lbtree_lbtree_rep = prove(
  ``is_lbtree (lbtree_rep t)``,
  SRW_TAC [][lbtree_repabs]);
val _ = BasicProvers.augment_srw_ss [rewrites [is_lbtree_lbtree_rep]]

val lbtree_rep_11 = prove(
  ``(lbtree_rep t1 = lbtree_rep t2) = (t1 = t2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``lbtree_abs``) THEN SRW_TAC [][]);
val _ = BasicProvers.augment_srw_ss [rewrites [lbtree_rep_11]]

val lbtree_abs_11 = prove(
  ``is_lbtree f1 /\ is_lbtree f2 ==>
    ((lbtree_abs f1 = lbtree_abs f2) = (f1 = f2))``,
  SRW_TAC [][lbtree_repabs, EQ_IMP_THM] THEN METIS_TAC []);

val lbtree_repabs' = #1 (EQ_IMP_RULE (SPEC_ALL lbtree_repabs))

val is_lbtree_rules = prove(
  ``is_lbtree Lfrep /\
    (is_lbtree t1 /\ is_lbtree t2 ==> is_lbtree (Ndrep a t1 t2))``,
  SRW_TAC [][is_lbtree_def] THENL [
    Q.EXISTS_TAC `(=) Lfrep` THEN SRW_TAC [][],
    Q.EXISTS_TAC `\t. P t \/ P' t \/ (t = Ndrep a t1 t2)` THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val is_lbtree_cases = prove(
  ``is_lbtree t =
       (t = Lfrep) \/
       ?a t1 t2. (t = Ndrep a t1 t2) /\ is_lbtree t1 /\ is_lbtree t2``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, is_lbtree_rules] THEN
  SRW_TAC [][is_lbtree_def] THEN RES_TAC THEN SRW_TAC [][] THEN
  DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`a`, `t1`, `t2`] THEN
  SRW_TAC [][] THEN Q.EXISTS_TAC `P` THEN SRW_TAC [][]);

val forall_lbtree = prove(
  ``(!t. P t) = (!f. is_lbtree f ==> P (lbtree_abs f))``,
  SRW_TAC [][EQ_IMP_THM] THEN ONCE_REWRITE_TAC [GSYM lbtree_absrep] THEN
  SRW_TAC [][]);

val Ndrep_11 = prove(
  ``(Ndrep a1 t1 u1 = Ndrep a2 t2 u2) = (a1 = a2) /\ (t1 = t2) /\ (u1 = u2)``,
  SRW_TAC [][Ndrep_def, EQ_IMP_THM, FUN_EQ_THM] THENL [
    POP_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN SRW_TAC [][],
    POP_ASSUM (Q.SPEC_THEN `T::x` MP_TAC) THEN SRW_TAC [][],
    POP_ASSUM (Q.SPEC_THEN `F::x` MP_TAC) THEN SRW_TAC [][]
  ]);

(* this is only used in the one proof below *)
val is_lbtree_coinduction = prove(
  ``(!f. P f ==> (f = Lfrep) \/
                 (?a t1 t2. P t1 /\ P t2 /\ (f = Ndrep a t1 t2))) ==>
   !f. P f ==> is_lbtree f``,
  SRW_TAC [][is_lbtree_def] THEN Q.EXISTS_TAC `P` THEN SRW_TAC [][]);

(* the path_follow function motivates the unique co-recursive function.
   for the moment we are still at the concrete/representative level *)

val path_follow_def = Define`
  (path_follow g x [] = OPTION_MAP FST (g x)) /\
  (path_follow g x (h::t) =
     case g x of
        NONE -> NONE
     || SOME (a,y,z) -> path_follow g (if h then y else z) t)
`;


val path_follow_is_lbtree = prove(
  ``!g x. is_lbtree (path_follow g x)``,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC `!f. (?x. f = path_follow g x) ==> is_lbtree f`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC is_lbtree_coinduction THEN SRW_TAC [][] THEN
  `(g x = NONE) \/ ?a b1 b2. g x = SOME (a, b1, b2)`
     by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES]
  THENL [
    DISJ1_TAC THEN SRW_TAC [][FUN_EQ_THM] THEN
    Cases_on `x'` THEN SRW_TAC [][path_follow_def, Lfrep_def],
    DISJ2_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`a`, `path_follow g b1`, `path_follow g b2`] THEN
    SRW_TAC [][] THENL [
      METIS_TAC [],
      METIS_TAC [],
      SRW_TAC [][FUN_EQ_THM] THEN Cases_on `x'` THEN
      SRW_TAC [][path_follow_def, Ndrep_def]
    ]
  ]);

(* now start to lift the representative operations to the abstract level *)

(* first define the constructors *)
val Lf_def = Define`Lf = lbtree_abs Lfrep`
val Nd_def = Define`
  Nd a t1 t2 = lbtree_abs (Ndrep a (lbtree_rep t1) (lbtree_rep t2))
`

val lbtree_cases = store_thm(
  "lbtree_cases",
  ``!t. (t = Lf) \/ (?a t1 t2. t = Nd a t1 t2)``,
  SIMP_TAC (srw_ss()) [Lf_def, Nd_def, forall_lbtree, lbtree_abs_11,
                       is_lbtree_rules] THEN
  ONCE_REWRITE_TAC [is_lbtree_cases] THEN SRW_TAC [][] THEN
  METIS_TAC [lbtree_repabs']);

val Lf_NOT_Nd = store_thm(
  "Lf_NOT_Nd",
  ``~(Lf = Nd a t1 t2)``,
  SRW_TAC [][Lf_def, Nd_def, lbtree_abs_11, is_lbtree_rules] THEN
  SRW_TAC [][Lfrep_def, Ndrep_def, FUN_EQ_THM] THEN
  Q.EXISTS_TAC `[]` THEN SRW_TAC [][]);
val _ = export_rewrites ["Lf_NOT_Nd"]

val Nd_11 = store_thm(
  "Nd_11",
  ``(Nd a1 t1 u1 = Nd a2 t2 u2) = (a1 = a2) /\ (t1 = t2) /\ (u1 = u2)``,
  SRW_TAC [][Nd_def, lbtree_abs_11, is_lbtree_rules, Ndrep_11]);
val _ = export_rewrites ["Nd_11"]

(* ----------------------------------------------------------------------
    co-recursion/finality axiom
   ---------------------------------------------------------------------- *)

val lbtree_ue_Axiom = store_thm(
  "lbtree_ue_Axiom",
  ``!f : 'a -> ('b # 'a # 'a) option.
       ?!g : 'a -> 'b lbtree.
          !x. g x = case f x of
                       NONE -> Lf
                    || SOME(b,y,z) -> Nd b (g y) (g z)``,
  GEN_TAC THEN
  SRW_TAC [][EXISTS_UNIQUE_THM] THENL [
    Q.EXISTS_TAC `\x. lbtree_abs (path_follow f x)` THEN
    SRW_TAC [][] THEN
    `(f x = NONE) \/ ?a b1 b2. f x = SOME(a,b1,b2)`
       by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES]
    THENL [
      SRW_TAC [][Lf_def, lbtree_abs_11, is_lbtree_rules,
                 path_follow_is_lbtree] THEN
      SRW_TAC [][FUN_EQ_THM, Lfrep_def] THEN
      Cases_on `x'` THEN SRW_TAC [][path_follow_def],
      SRW_TAC [][Nd_def, lbtree_abs_11, is_lbtree_rules,
                 path_follow_is_lbtree, lbtree_repabs'] THEN
      SRW_TAC [][FUN_EQ_THM, Ndrep_def] THEN
      Cases_on `x'` THEN SRW_TAC [][path_follow_def]
    ],

    Q_TAC SUFF_TAC `!x. g x = g' x` THEN1 SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN
    Q_TAC SUFF_TAC `!x. lbtree_rep (g x) = lbtree_rep (g' x)`
          THEN1 SIMP_TAC (srw_ss()) [] THEN
    Q_TAC SUFF_TAC `!l x. lbtree_rep (g x) l = lbtree_rep (g' x) l`
          THEN1 SIMP_TAC bool_ss [FUN_EQ_THM] THEN
    Q_TAC SUFF_TAC `!l x. (lbtree_rep (g x) l = path_follow f x l) /\
                          (lbtree_rep (g' x) l = path_follow f x l)`
          THEN1 SIMP_TAC bool_ss [] THEN
    Induct THENL [
      ONCE_ASM_REWRITE_TAC [] THEN
      SIMP_TAC (srw_ss()) [path_follow_def] THEN
      GEN_TAC THEN
      `(f x = NONE) \/ ?a b1 b2. f x = SOME (a, b1, b2)`
          by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES] THEN
      POP_ASSUM SUBST_ALL_TAC THENL [
        SIMP_TAC (srw_ss()) [Lf_def, lbtree_repabs', is_lbtree_rules] THEN
        SRW_TAC [][Lfrep_def],
        SIMP_TAC (srw_ss()) [Nd_def, lbtree_repabs', is_lbtree_rules] THEN
        SIMP_TAC (srw_ss())[Ndrep_def]
      ],
      ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC (srw_ss()) [path_follow_def] THEN
      REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN
      `(f x = NONE) \/ ?a b1 b2. f x = SOME (a, b1, b2)`
          by METIS_TAC [pairTheory.pair_CASES, optionTheory.option_CASES] THEN
      POP_ASSUM SUBST_ALL_TAC THENL [
        SIMP_TAC (srw_ss()) [Lf_def, lbtree_repabs', is_lbtree_rules] THEN
        SIMP_TAC (srw_ss()) [Lfrep_def],
        SIMP_TAC (srw_ss()) [Nd_def, lbtree_repabs', is_lbtree_rules] THEN
        SIMP_TAC (srw_ss()) [Ndrep_def] THEN
        REPEAT (POP_ASSUM (K ALL_TAC)) THEN SRW_TAC [][]
      ]
    ]
  ]);

(* ----------------------------------------------------------------------
    define a case constant - wouldn't it be nice if we could use nice case
      syntax with this?
   ---------------------------------------------------------------------- *)

val lbtree_case_def = Define`
  lbtree_case e f t = if t = Lf then e
                      else f (@a. ?t1 t2. t = Nd a t1 t2)
                             (@t1. ?a t2. t = Nd a t1 t2)
                             (@t2. ?a t1. t = Nd a t1 t2)
`;

val lbtree_case_thm = store_thm(
  "lbtree_case_thm",
  ``(lbtree_case e f Lf = e) /\
    (lbtree_case e f (Nd a t1 t2) = f a t1 t2)``,
  SRW_TAC [][lbtree_case_def]);
val _ = export_rewrites ["lbtree_case_thm"]

(* ----------------------------------------------------------------------
    Bisimulation

    Strong and weak versions.  Follows as a consequence of the finality
    theorem.
   ---------------------------------------------------------------------- *)

val lbtree_bisimulation = store_thm(
  "lbtree_bisimulation",
  ``!t u. (t = u) =
          ?R. R t u /\
              !t u. R t u ==>
                    (t = Lf) /\ (u = Lf) \/
                    ?a t1 u1 t2 u2.
                        R t1 u1 /\ R t2 u2 /\
                        (t = Nd a t1 t2) /\ (u = Nd a u1 u2)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][] THEN
    METIS_TAC [lbtree_cases],
    SRW_TAC [][] THEN
    Q.ISPEC_THEN
      `\ (t, u).
         if R t u then
           lbtree_case NONE
                       (\a t1 t2. SOME(a, (t1, (@u1. ?u2. u = Nd a u1 u2)),
                                          (t2, (@u2. ?u1. u = Nd a u1 u2))))
                       t
         else
           NONE`
       (ASSUME_TAC o
        Q.SPECL [`\ (t,u). if R t u then t else Lf`,
                 `\ (t,u). if R t u then u else Lf`] o
        CONJUNCT2 o
        SIMP_RULE bool_ss [EXISTS_UNIQUE_THM])
       lbtree_ue_Axiom THEN
    Q_TAC SUFF_TAC `(\ (t,u). if R t u then t else Lf) =
                    (\ (t,u). if R t u then u else Lf)`
          THEN1 (SRW_TAC [][FUN_EQ_THM, pairTheory.FORALL_PROD] THEN
                 METIS_TAC []) THEN
    POP_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
    SRW_TAC [][] THENL [
      `(p_1 = Lf) \/ (?a t1 t2. p_1 = Nd a t1 t2)`
         by METIS_TAC [lbtree_cases]
      THENL [
        SRW_TAC [][],
        `?u1 u2. (p_2 = Nd a u1 u2) /\ R t1 u1 /\ R t2 u2`
           by METIS_TAC [Lf_NOT_Nd, Nd_11] THEN
        SRW_TAC [][]
      ],
      `(p_2 = Lf) \/ (?a u1 u2. p_2 = Nd a u1 u2)`
         by METIS_TAC [lbtree_cases]
      THENL [
        `p_1 = Lf` by METIS_TAC [Lf_NOT_Nd] THEN SRW_TAC [][],
        `?t1 t2. (p_1 = Nd a t1 t2) /\ R t1 u1 /\ R t2 u2`
           by METIS_TAC [Lf_NOT_Nd, Nd_11] THEN
        SRW_TAC [][]
      ]
    ]
  ]);

val lbtree_strong_bisimulation = store_thm(
  "lbtree_strong_bisimulation",
  ``!t u.
      (t = u) =
      ?R. R t u /\
          !t u.
             R t u ==> (t = u) \/
                       ?a t1 u1 t2 u2.
                          R t1 u1 /\ R t2 u2 /\
                          (t = Nd a t1 t2) /\ (u = Nd a u1 u2)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [lbtree_bisimulation] THEN
    Q.EXISTS_TAC `\t u. R t u \/ (t = u)` THEN
    SRW_TAC [][] THENL [
      `(t' = u') \/
       ?a t1 u1 t2 u2. R t1 u1 /\ R t2 u2 /\ (t' = Nd a t1 t2) /\
                       (u' = Nd a u1 u2)`
          by METIS_TAC [] THEN
      SRW_TAC [][] THEN
      `(t' = Lf) \/ (?a t1 t2. t' = Nd a t1 t2)`
         by METIS_TAC [lbtree_cases] THEN
      SRW_TAC [][],
      `(t' = Lf) \/ (?a t1 t2. t' = Nd a t1 t2)`
         by METIS_TAC [lbtree_cases] THEN
      SRW_TAC [][]
    ]
  ]);

(* ----------------------------------------------------------------------
    mem : 'a -> 'a lbtree -> bool

    inductively defined
   ---------------------------------------------------------------------- *)

val (mem_rules, mem_ind, mem_cases) = Hol_reln`
  (!a t1 t2. mem a (Nd a t1 t2)) /\
  (!a b t1 t2. mem a t1 ==> mem a (Nd b t1 t2)) /\
  (!a b t1 t2. mem a t2 ==> mem a (Nd b t1 t2))
`;

val mem_thm = store_thm(
  "mem_thm",
  ``(mem a Lf = F) /\
    (mem a (Nd b t1 t2) = (a = b) \/ mem a t1 \/ mem a t2)``,
  CONJ_TAC THEN CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [mem_cases])) THEN
  SRW_TAC [][] THEN METIS_TAC []);
val _ = export_rewrites ["mem_thm"]


(* ----------------------------------------------------------------------
    map : ('a -> 'b) -> 'a lbtree -> 'b lbtree

    co-recursively defined
   ---------------------------------------------------------------------- *)

val map_def = new_specification("map_def", ["map"],
  prove(
    ``?map. !f : 'a -> 'b.
         (map f Lf = Lf) /\
         (!a t1 t2. map f (Nd a t1 t2) = Nd (f a) (map f t1) (map f t2))``,
    Q.ISPEC_THEN
      `lbtree_case NONE (\a:'a t1 t2. SOME (f a:'b, t1, t2))`
      (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV o GEN_ALL o
       CONJUNCT1 o SIMP_RULE bool_ss [EXISTS_UNIQUE_THM])
      lbtree_ue_Axiom THEN
    Q.EXISTS_TAC `g` THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
    SRW_TAC [][]));
val _ = export_rewrites ["map_def"]

val map_eq_Lf = store_thm(
  "map_eq_Lf",
  ``((map f t = Lf) = (t = Lf)) /\ ((Lf = map f t) = (t = Lf))``,
  `(t = Lf) \/ ?a t1 t2. t = Nd a t1 t2` by METIS_TAC [lbtree_cases] THEN
  SRW_TAC [][]);
val _ = export_rewrites ["map_eq_Lf"]

val map_eq_Nd = store_thm(
  "map_eq_Nd",
  ``(map f t = Nd a t1 t2) =
       ?a' t1' t2'. (t = Nd a' t1' t2') /\ (a = f a') /\
                    (t1 = map f t1') /\ (t2 = map f t2')``,
  `(t = Lf) \/ ?a' t1' t2'. t = Nd a' t1' t2'` by METIS_TAC [lbtree_cases] THEN
  SRW_TAC [][] THEN METIS_TAC []);


(* ----------------------------------------------------------------------
    finite : 'a lbtree -> bool

    inductively defined
   ---------------------------------------------------------------------- *)

val (finite_rules, finite_ind, finite_cases) = Hol_reln`
  finite Lf /\
  !a t1 t2. finite t1 /\ finite t2 ==> finite (Nd a t1 t2)
`;

val finite_thm = store_thm(
  "finite_thm",
  ``(finite Lf = T) /\
    (finite (Nd a t1 t2) = finite t1 /\ finite t2)``,
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [finite_cases])) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["finite_thm"]


val finite_map = store_thm(
  "finite_map",
  ``finite (map f t) = finite t``,
  Q_TAC SUFF_TAC `(!t. finite t ==> finite (map f t)) /\
                  !t. finite t ==> !t'. (t = map f t') ==> finite t'`
        THEN1 METIS_TAC [] THEN
  CONJ_TAC THENL [
    HO_MATCH_MP_TAC finite_ind THEN SRW_TAC [][],
    HO_MATCH_MP_TAC finite_ind THEN SRW_TAC [][map_eq_Nd] THEN
    SRW_TAC [][]
  ]);
val _ = export_rewrites ["finite_map"]

(* ----------------------------------------------------------------------
    bf_flatten : 'a lbtree list -> 'a llist

    breadth-first flatten, takes a list of trees because the recursion
    needs to maintain a queue of trees at the current fringe of
    exploration
   ---------------------------------------------------------------------- *)

(* helper function that we "delete" immediately after def'n below *)
val drop_while_def = Define`
  (drop_while P [] = []) /\
  (drop_while P (h::t) = if P h then drop_while P t else h::t)
`;

val bf_flatten_def = new_specification(
  "bf_flatten_def",
  ["bf_flatten"],
  prove(``?f. (f [] = LNIL) /\
              (!ts. f (Lf::ts) = f ts) /\
              (!a t1 t2 ts. f (Nd a t1 t2::ts) = a:::f (ts ++ [t1; t2]))``,
        Q.ISPEC_THEN
                `\l. case drop_while ((=) Lf) l of
                        [] -> NONE
                     || t::ts -> lbtree_case NONE
                                    (\a t1 t2. SOME (ts ++ [t1;t2], a))
                                    t`
                STRIP_ASSUME_TAC llist_Axiom_1 THEN
        Q.EXISTS_TAC `g` THEN
        REPEAT STRIP_TAC THENL [
          ONCE_ASM_REWRITE_TAC [] THEN
          POP_ASSUM (K ALL_TAC) THEN
          SRW_TAC [][drop_while_def],
          ONCE_ASM_REWRITE_TAC [] THEN
          SIMP_TAC (srw_ss()) [drop_while_def],
          POP_ASSUM (fn th => CONV_TAC (LAND_CONV
                                          (ONCE_REWRITE_CONV [th]))) THEN
          SRW_TAC [][drop_while_def]
        ]))

(* would like to actually delete_const this, but the theory file gets a
   reference to the definition because it's added to computeLib's compset.
   Instead we do the permanent version of hide, which ensures that people
   importing this theory won't have drop_while contaminating their
   constant name-space.  It will still be reachable as lbtree$drop_while of
   course.  *)
val _ = remove_ovl_mapping "drop_while" {Name = "drop_while", Thy = "lbtree"}

(* simple properties of bf_flatten *)
val bf_flatten_eq_lnil = store_thm(
  "bf_flatten_eq_lnil",
  ``!l. (bf_flatten l = [||]) = EVERY ((=)Lf) l``,
  Induct THEN SRW_TAC [][bf_flatten_def] THEN
  `(h = Lf) \/ (?a t1 t2. h = Nd a t1 t2)`
      by METIS_TAC [lbtree_cases] THEN
  SRW_TAC [][bf_flatten_def]);

val bf_flatten_append = store_thm(
  "bf_flatten_append",
  ``!l1. EVERY ((=) Lf) l1 ==> (bf_flatten (l1 ++ l2) = bf_flatten l2)``,
  Induct THEN SRW_TAC [][] THEN SRW_TAC [][bf_flatten_def]);

(* a somewhat more complicated property, requiring one simple lemma about
   lists and EXISTS first *)
val EXISTS_FIRST = store_thm(
  "EXISTS_FIRST",
  ``!l. EXISTS P l ==> ?l1 x l2. (l = l1 ++ (x::l2)) /\ EVERY ((~) o P) l1 /\
                                 P x``,
  Induct THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `l`] THEN SRW_TAC [][],
    Cases_on `P h` THENL [
      MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `l`] THEN SRW_TAC [][],
      RES_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`h::l1`, `x`, `l2`] THEN SRW_TAC [][]
    ]
  ]);

val exists_bf_flatten = store_thm(
  "exists_bf_flatten",
  ``exists ((=)x) (bf_flatten tlist) ==> EXISTS (mem x) tlist``,
  Q_TAC SUFF_TAC `!l. exists ((=)x) l ==>
                      !tlist. (l = bf_flatten tlist) ==>
                              EXISTS (mem x) tlist`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC exists_ind THEN SRW_TAC [][] THENL [
    `~EVERY ($= Lf) tlist`
       by METIS_TAC [LCONS_NOT_NIL, bf_flatten_eq_lnil] THEN
    `EXISTS ($~ o $= Lf) tlist`
       by FULL_SIMP_TAC (srw_ss()) [listTheory.NOT_EVERY] THEN
    `?l1 x l2. EVERY ($~ o $~ o $= Lf) l1 /\ ($~ o $= Lf) x /\
               (tlist = l1 ++ (x :: l2))`
       by METIS_TAC [EXISTS_FIRST] THEN
    `EVERY ((=) Lf) l1`
       by FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [combinTheory.o_DEF] THEN
    `~(Lf = x)` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `?a t1 t2. x = Nd a t1 t2` by METIS_TAC [lbtree_cases] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    (bf_flatten_append |> Q.SPEC `l1` |> Q.INST [`l2`|->`[Nd a t1 t2] ++ l2`] |> MP_TAC) THEN
    SRW_TAC [][bf_flatten_def] THEN FULL_SIMP_TAC (srw_ss()) [],
    `~EVERY ($= Lf) tlist`
       by METIS_TAC [LCONS_NOT_NIL, bf_flatten_eq_lnil] THEN
    `EXISTS ($~ o $= Lf) tlist`
       by FULL_SIMP_TAC (srw_ss()) [listTheory.NOT_EVERY] THEN
    `?l1 y l2. EVERY ($~ o $~ o $= Lf) l1 /\ ($~ o $= Lf) y /\
               (tlist = l1 ++ (y :: l2))`
       by METIS_TAC [EXISTS_FIRST] THEN
    `EVERY ((=) Lf) l1`
       by FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [combinTheory.o_DEF] THEN
    `~(Lf = y)` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `?a t1 t2. y = Nd a t1 t2` by METIS_TAC [lbtree_cases] THEN
    FULL_SIMP_TAC (srw_ss()) [bf_flatten_def, bf_flatten_append] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `l2 ++ [t1;t2]` MP_TAC) THEN
    SRW_TAC [][] THEN SRW_TAC [][] THEN
    (bf_flatten_append |> Q.SPEC `l1` |> Q.INST [`l2`|->`[Nd a t1 t2] ++ l2`] |> MP_TAC) THEN
    SRW_TAC [][bf_flatten_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []
  ]);

(* ----------------------------------------------------------------------
    Now it starts to get HIDEOUS.

    Everything in the rest of the file is an indictment of something,
    maybe
     * theorem-proving in general; or
     * HOL4; or
     * me

    Whatever it is, the following development of what is really a very
    simple proof is just ghastly.

    The proof is of the converse of the last lemma, that

      EXISTS (mem x) tlist ==> exists ((=) x) (bf_flatten tlist)

    This can't be proved by a structural induction on tlist because of
    the way tlist actually gets bigger as the flatten proceeds.  Nor
    can we induct on the "size" of tlist (taking into consideration
    the sizes of the tree-elements) because of the presence of
    infinite trees.  Instead, we induct on the lexicographic product
    of the minimum depth at which x occurs in a tree, and the minimum
    index within the list of a tree containing x to that depth.

    This is reduced because of the following:

      If the tree with x in it is not at the head of the list, then
      the depth number doesn't change, but the index goes down because
      all of the trees in the list move forward (as a Lf is either
      discarded from the head of the list, or as a Nd is pulled off,
      and two sub-trees are enqueued at the back of the list).

      If the tree with x in it is at the head of the list then it's
      either at the top of the tree in which case we're done, or it
      moves to the end of the list, but at a reduced depth.

    This reads fairly clearly I think, and feels as if it should be
    straightforward.  It's anything but.

   ---------------------------------------------------------------------- *)


(* depth x t n means that x occurs in tree t at depth n *)
val (depth_rules, depth_ind, depth_cases) = Hol_reln`
  (!x t1 t2. depth x (Nd x t1 t2) 0) /\
  (!m x a t1 t2. depth x t1 m ==> depth x (Nd a t1 t2) (SUC m)) /\
  (!m x a t1 t2. depth x t2 m ==> depth x (Nd a t1 t2) (SUC m))
`;

val mem_depth = store_thm(
  "mem_depth",
  ``!x t. mem x t ==> ?n. depth x t n``,
  HO_MATCH_MP_TAC mem_ind THEN SRW_TAC [][] THEN
  METIS_TAC [depth_rules]);

val depth_mem = store_thm(
  "depth_mem",
  ``!x t n. depth x t n ==> mem x t``,
  HO_MATCH_MP_TAC depth_ind THEN SRW_TAC [][]);

(* mindepth x t returns SOME n if x occurs in t at minimum depth n,
   else NONE *)
val mindepth_def = Define`
  mindepth x t = if mem x t then SOME (LEAST n. depth x t n) else NONE
`;

open numLib
(* following tactic is used twice in theorem below - yerk *)
val min_tac =
    LEAST_ELIM_TAC THEN CONJ_TAC THENL [
      SRW_TAC [][] THEN1 METIS_TAC [mem_depth],
      Q.X_GEN_TAC `t2d` THEN SRW_TAC [][]
    ] THEN
    LEAST_ELIM_TAC THEN CONJ_TAC THENL [
      SRW_TAC [][] THEN1 METIS_TAC [mem_depth],
      Q.X_GEN_TAC `t1d` THEN SRW_TAC [][]
    ] THEN
    LEAST_ELIM_TAC THEN CONJ_TAC THENL [
      SRW_TAC [][] THEN1 METIS_TAC [mem_thm, mem_depth],
      SRW_TAC [][]
    ] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [depth_cases] THEN
    SRW_TAC [][] THENL [
      `m = t1d`
         by (SPOSE_NOT_THEN ASSUME_TAC THEN
             `m < t1d \/ t1d < m` by DECIDE_TAC THENL [
                METIS_TAC [],
                METIS_TAC [DECIDE ``SUC x < SUC y = x < y``,
                           depth_rules]
             ]) THEN
      SRW_TAC [][arithmeticTheory.MIN_DEF] THEN
      SPOSE_NOT_THEN ASSUME_TAC THEN
      `t2d < m` by DECIDE_TAC THEN
      METIS_TAC [DECIDE ``SUC x < SUC y = x < y``, depth_rules],
      `m = t2d`
         by (SPOSE_NOT_THEN ASSUME_TAC THEN
             `m < t2d \/ t2d < m` by DECIDE_TAC THENL [
                METIS_TAC [],
                METIS_TAC [DECIDE ``SUC x < SUC y = x < y``,
                           depth_rules]
             ]) THEN
      SRW_TAC [][arithmeticTheory.MIN_DEF] THEN
      METIS_TAC [DECIDE ``SUC x < SUC y = x < y``, depth_rules]
    ]

(* a minimum function lifted to option type: NONEs are treated as if they
   are +ve infinity *)
val optmin_def = Define`
  (optmin NONE NONE = NONE) /\
  (optmin (SOME x) NONE = SOME x) /\
  (optmin NONE (SOME y) = SOME y) /\
  (optmin (SOME x) (SOME y) = SOME (MIN x y))
`;

(* recursive characterisation of mindepth *)
val mindepth_thm = store_thm(
  "mindepth_thm",
  ``(mindepth x Lf = NONE) /\
    (mindepth x (Nd a t1 t2) =
       if x = a then SOME 0
       else OPTION_MAP SUC (optmin (mindepth x t1) (mindepth x t2)))``,
  SRW_TAC [][mindepth_def] THEN FULL_SIMP_TAC (srw_ss()) [optmin_def] THENL [
    LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [depth_rules] THEN
    Cases_on `n` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][depth_rules],

    min_tac,
    min_tac,

    LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [mem_depth] THEN
    LEAST_ELIM_TAC THEN SRW_TAC [][]
       THEN1 METIS_TAC [mem_depth, depth_rules] THEN
    POP_ASSUM MP_TAC THEN
    `!n. ~depth x t2 n` by METIS_TAC [depth_mem] THEN
    ONCE_REWRITE_TAC [depth_cases] THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `~(m < n) /\ ~(n < m)` THEN1 DECIDE_TAC THEN
    REPEAT STRIP_TAC THEN METIS_TAC [DECIDE ``SUC x < SUC y = x < y``,
                                     depth_rules],

    LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [mem_depth] THEN
    LEAST_ELIM_TAC THEN SRW_TAC [][]
       THEN1 METIS_TAC [mem_depth, depth_rules] THEN
    POP_ASSUM MP_TAC THEN
    `!n. ~depth x t1 n` by METIS_TAC [depth_mem] THEN
    ONCE_REWRITE_TAC [depth_cases] THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `~(m < n) /\ ~(n < m)` THEN1 DECIDE_TAC THEN
    REPEAT STRIP_TAC THEN METIS_TAC [DECIDE ``SUC x < SUC y = x < y``,
                                     depth_rules]
  ]);

val mem_mindepth = store_thm(
  "mem_mindepth",
  ``!x t. mem x t ==> (?n. mindepth x t = SOME n)``,
  METIS_TAC [mindepth_def]);

val mindepth_depth = store_thm(
  "mindepth_depth",
  ``(mindepth x t = SOME n) ==> depth x t n``,
  SRW_TAC [][mindepth_def] THEN LEAST_ELIM_TAC THEN SRW_TAC [][] THEN
  METIS_TAC [mem_depth]);

(* is_mmindex f l n d says that n is the least index of the element with
   minimal weight (d), as defined by f : 'a -> num option

   Defining this relation as a recursive function to calculate n and d
   results in a complicated function with accumulators that is very fiddly
   to prove correct.  Its option return type also makes the ultimate proof
   ugly --- I decided it was a mistake bothering with it. *)
val is_mmindex_def = Define`
  is_mmindex f l n d =
    n < LENGTH l /\
    (f (EL n l) = SOME d) /\
    !i. i < LENGTH l ==>
          (f (EL i l) = NONE) \/
          ?d'. (f (EL i l) = SOME d') /\
               d <= d' /\ (i < n ==> d < d')
`;

(* the crucial fact about minimums -- two levels of LEAST-ness going on in
   here *)
val mmindex_EXISTS = store_thm(
  "mmindex_EXISTS",
  ``EXISTS (\e. ?n. f e = SOME n) l ==> ?i m. is_mmindex f l i m``,
  SRW_TAC [][is_mmindex_def] THEN
  Q.ABBREV_TAC `P = \n. ?i. i < LENGTH l /\ (f (EL i l) = SOME n)` THEN
  `?d. P d`
     by (FULL_SIMP_TAC (srw_ss()) [listTheory.EXISTS_MEM] THEN
         Q.EXISTS_TAC `n` THEN SRW_TAC [][Abbr`P`] THEN
         METIS_TAC [listTheory.MEM_EL]) THEN
  Q.ABBREV_TAC `min_d = LEAST x. P x` THEN
  Q.ABBREV_TAC `Inds = \i . i < LENGTH l /\ (f (EL i l) = SOME min_d)` THEN
  MAP_EVERY Q.EXISTS_TAC [`LEAST x. Inds(x)`, `min_d`] THEN
  LEAST_ELIM_TAC THEN CONJ_TAC THENL [
    SRW_TAC [][Abbr`Inds`, Abbr`min_d`] THEN
    LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
    Q.UNABBREV_TAC `P` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [],
    SIMP_TAC (srw_ss()) [] THEN Q.UNABBREV_TAC `Inds`  THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN Q.X_GEN_TAC `n` THEN
    STRIP_TAC THEN Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
    Cases_on `f (EL i l)` THEN SRW_TAC [][] THENL [
      `P x` by (SRW_TAC [][Abbr`P`] THEN METIS_TAC []) THEN
      Q.UNABBREV_TAC `min_d` THEN LEAST_ELIM_TAC THEN
      SRW_TAC [][] THEN1 METIS_TAC [] THEN
      METIS_TAC [DECIDE ``x <= y = ~(y < x)``],
      `P x` by (SRW_TAC [][Abbr`P`] THEN METIS_TAC []) THEN
      Q.UNABBREV_TAC `min_d` THEN LEAST_ELIM_TAC THEN
      CONJ_TAC THEN1 METIS_TAC [] THEN
      Q.X_GEN_TAC `m` THEN STRIP_TAC THEN
      `(LEAST x. P x) = m`
         by (LEAST_ELIM_TAC THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
             METIS_TAC [DECIDE ``(x = y) = ~(x < y) /\ ~(y < x)``]) THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      `m <= x` by METIS_TAC [DECIDE ``~(x < y) = y <= x``] THEN
      Q_TAC SUFF_TAC `~(m = x)` THEN1 DECIDE_TAC THEN
      METIS_TAC []
    ]
  ]);

val mmindex_unique = store_thm(
  "mmindex_unique",
  ``is_mmindex f l i m ==> !j n. is_mmindex f l j n = (j = i) /\ (n = m)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN
  SIMP_TAC (srw_ss()) [is_mmindex_def] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `~(j < i) /\ ~(i < j) /\ ~(n < m) /\ ~(m < n)`
        THEN1 DECIDE_TAC THEN
  REPEAT STRIP_TAC THEN
  METIS_TAC [DECIDE ``~(x < y /\ y <= x)``,
             optionTheory.SOME_11, optionTheory.NOT_SOME_NONE]);

val mmindex_bump = prove(
  ``(f x = NONE) ==> (is_mmindex f (x::t) (SUC j) n = is_mmindex f t j n)``,
  SRW_TAC [][EQ_IMP_THM, is_mmindex_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
    SRW_TAC [][],
    Cases_on `i` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

(* set up the induction principle the final proof will use *)
val WF_ltlt = prove(
  ``WF ((<) LEX (<))``,
  SRW_TAC [][prim_recTheory.WF_LESS, pairTheory.WF_LEX]);
val ltlt_induction = MATCH_MP relationTheory.WF_INDUCTION_THM WF_ltlt

(* this or something like it is in rich_listTheory - am tempted to put it
   in listTheory *)
val EL_APPEND = prove(
  ``!l1 l2 n. n < LENGTH l1 + LENGTH l2 ==>
              (EL n (l1 ++ l2) =
                  if n < LENGTH l1 then EL n l1
                  else EL (n - LENGTH l1) l2)``,
  Induct THEN SRW_TAC [][] THENL [
    Cases_on `n` THEN
    FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_CLAUSES],
    Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_CLAUSES]
  ]);

val optmin_EQ_NONE = prove(
  ``(optmin n m = NONE) = (n = NONE) /\ (m = NONE)``,
  Cases_on `n` THEN Cases_on `m` THEN SRW_TAC [][optmin_def]);

val mem_bf_flatten = store_thm(
  "mem_bf_flatten",
  ``exists ((=)x) (bf_flatten tlist) = EXISTS (mem x) tlist``,
  EQ_TAC THENL [
   METIS_TAC [exists_bf_flatten],
   Q_TAC SUFF_TAC
         `!p tlist x.
            (SND p = @i. ?d. is_mmindex (mindepth x) tlist i d) /\
            (FST p = THE (mindepth x (EL (SND p) tlist))) /\
            EXISTS (mem x) tlist ==>
            exists ((=) x) (bf_flatten tlist)` THEN1
         SRW_TAC [][pairTheory.FORALL_PROD] THEN
   HO_MATCH_MP_TAC ltlt_induction THEN
   SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
   MAP_EVERY Q.X_GEN_TAC [`td`, `ld`] THEN
   SRW_TAC [DNF_ss][pairTheory.LEX_DEF] THEN
   `EXISTS (\e. ?n. mindepth x e = SOME n) tlist`
      by (FULL_SIMP_TAC (srw_ss()) [listTheory.EXISTS_MEM] THEN
          METIS_TAC [mem_mindepth]) THEN
   `?i d. is_mmindex (mindepth x) tlist i d`
      by METIS_TAC [mmindex_EXISTS] THEN
   `!j n. is_mmindex (mindepth x) tlist j n = (j = i) /\ (n = d)`
      by METIS_TAC [mmindex_unique] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN
   `mindepth x (EL i tlist) = SOME d` by METIS_TAC [is_mmindex_def] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN
   `?h t. tlist = h::t`
      by METIS_TAC [listTheory.list_CASES, listTheory.EXISTS_DEF] THEN
   `(h = Lf) \/ ?a t1 t2. h = Nd a t1 t2` by METIS_TAC [lbtree_cases] THENL [
      SRW_TAC [][bf_flatten_def] THEN
      `?i0. i = SUC i0`
          by (Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) [mindepth_thm]) THEN
      `is_mmindex (mindepth x) (Lf::t) (SUC i0) d` by SRW_TAC [][] THEN
      `is_mmindex (mindepth x) t i0 d`
          by METIS_TAC [mmindex_bump, mindepth_thm] THEN
      `!j n. is_mmindex (mindepth x) t j n = (j = i0) /\ (n = d)`
          by METIS_TAC [mmindex_unique] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [``t : 'a lbtree list``, ``x:'a``]) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

      SRW_TAC [][bf_flatten_def] THEN
      Cases_on `x = a` THEN SRW_TAC [][] THEN
      Cases_on `i` THENL [
        REPEAT (Q.PAT_ASSUM `EXISTS P l` (K ALL_TAC)) THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        FULL_SIMP_TAC (srw_ss()) [mindepth_thm] THEN
        Cases_on `mindepth x t1` THENL [
          Cases_on `mindepth x t2` THEN
          FULL_SIMP_TAC (srw_ss()) [optmin_def] THEN
          `mem x t2` by METIS_TAC [depth_mem, mindepth_depth] THEN
          FIRST_X_ASSUM
            (MP_TAC o
             SPECL [``(t:'a lbtree list) ++ [t1; t2]``, ``x:'a``]) THEN
          SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          Q_TAC SUFF_TAC
                `is_mmindex (mindepth x) (t ++ [t1;t2]) (LENGTH t + 1) x'`
                THEN1 (DISCH_THEN (ASSUME_TAC o MATCH_MP mmindex_unique) THEN
                       SRW_TAC [ARITH_ss][EL_APPEND]) THEN
          `is_mmindex (mindepth x) (Nd a t1 t2::t) 0 (SUC x')`
              by SRW_TAC [][] THEN
          POP_ASSUM MP_TAC THEN
          FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
          SRW_TAC [][is_mmindex_def] THENL [
            SRW_TAC [ARITH_ss][EL_APPEND],
            Cases_on `i < LENGTH t` THENL [
              SRW_TAC [][EL_APPEND] THEN
              FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
              SRW_TAC [][] THEN SRW_TAC [ARITH_ss][],
              SRW_TAC [ARITH_ss][EL_APPEND] THEN
              `(i = LENGTH t) \/ (i = SUC (LENGTH t))` by DECIDE_TAC THENL [
                 SRW_TAC [][],
                 SRW_TAC [ARITH_ss][DECIDE ``SUC x - x = SUC 0``]
              ]
            ]
          ],
          Cases_on `mindepth x t2` THENL [
            FULL_SIMP_TAC (srw_ss()) [optmin_def] THEN
            `mem x t1` by METIS_TAC [depth_mem, mindepth_depth] THEN
            FIRST_X_ASSUM
              (MP_TAC o
               SPECL [``(t:'a lbtree list) ++ [t1; t2]``, ``x:'a``]) THEN
            SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            Q_TAC SUFF_TAC
                  `is_mmindex (mindepth x) (t ++ [t1;t2]) (LENGTH t) x'`
                  THEN1 (DISCH_THEN (ASSUME_TAC o MATCH_MP mmindex_unique) THEN
                         SRW_TAC [ARITH_ss][EL_APPEND]) THEN
            `is_mmindex (mindepth x) (Nd a t1 t2::t) 0 (SUC x')`
               by SRW_TAC [][] THEN
            POP_ASSUM MP_TAC THEN
            FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
            SRW_TAC [ARITH_ss][is_mmindex_def, EL_APPEND] THEN
            Cases_on `i < LENGTH t` THENL [
              SRW_TAC [][] THEN
              FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
              ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [],
              `(i = LENGTH t) \/ (i = LENGTH t + 1)` by DECIDE_TAC
              THENL [
                SRW_TAC [][],
                SRW_TAC [][DECIDE ``x + 1 - x = 1``]
              ]
            ],
            FULL_SIMP_TAC (srw_ss()) [optmin_def] THEN
            `mem x t1 /\ mem x t2`
               by METIS_TAC [depth_mem, mindepth_depth] THEN
            FIRST_X_ASSUM
              (MP_TAC o
               SPECL [``(t:'a lbtree list) ++ [t1;t2]``, ``x:'a``]) THEN
            SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            Cases_on `x' < x''` THENL [
              Q_TAC SUFF_TAC
                    `is_mmindex (mindepth x) (t ++ [t1;t2]) (LENGTH t) x'`
                    THEN1 (DISCH_THEN (ASSUME_TAC o
                                       MATCH_MP mmindex_unique) THEN
                           SRW_TAC [ARITH_ss][EL_APPEND,
                                              arithmeticTheory.MIN_DEF]) THEN
              `is_mmindex (mindepth x) (Nd a t1 t2::t) 0 (SUC x')`
                  by SRW_TAC [][arithmeticTheory.MIN_DEF] THEN
              POP_ASSUM MP_TAC THEN
              FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
              SRW_TAC [ARITH_ss][is_mmindex_def, EL_APPEND] THEN
              Cases_on `i < LENGTH t` THENL [
                SRW_TAC [][] THEN
                FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
                ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [],
                `(i = LENGTH t) \/ (i = LENGTH t + 1)` by DECIDE_TAC
                THENL [
                  SRW_TAC [][],
                  SRW_TAC [ARITH_ss][DECIDE ``x + 1 - x = 1``]
                ]
              ],
              Cases_on `x' = x''` THENL [
                Q_TAC SUFF_TAC
                      `is_mmindex (mindepth x) (t ++ [t1;t2]) (LENGTH t) x'`
                      THEN1 (DISCH_THEN (ASSUME_TAC o
                                         MATCH_MP mmindex_unique) THEN
                             SRW_TAC [ARITH_ss][EL_APPEND,
                                                arithmeticTheory.MIN_DEF])THEN
                `is_mmindex (mindepth x) (Nd a t1 t2::t) 0 (SUC x')`
                    by SRW_TAC [][arithmeticTheory.MIN_DEF] THEN
                POP_ASSUM MP_TAC THEN
                FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
                SRW_TAC [ARITH_ss][is_mmindex_def, EL_APPEND] THEN
                Cases_on `i < LENGTH t` THENL [
                  SRW_TAC [][] THEN
                  FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
                  ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [],
                  `(i = LENGTH t) \/ (i = LENGTH t + 1)` by DECIDE_TAC
                  THENL [
                    SRW_TAC [ARITH_ss][],
                    SRW_TAC [ARITH_ss][DECIDE ``x + 1 - x = 1``]
                  ]
                ],
                `x'' < x'` by DECIDE_TAC THEN
                Q_TAC SUFF_TAC
                   `is_mmindex (mindepth x) (t ++ [t1;t2]) (LENGTH t + 1) x''`
                    THEN1 (DISCH_THEN (ASSUME_TAC o
                                       MATCH_MP mmindex_unique) THEN
                           SRW_TAC [ARITH_ss][EL_APPEND,
                                              arithmeticTheory.MIN_DEF]) THEN
                `is_mmindex (mindepth x) (Nd a t1 t2::t) 0 (SUC x'')`
                    by SRW_TAC [][arithmeticTheory.MIN_DEF] THEN
                POP_ASSUM MP_TAC THEN
                FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
                SRW_TAC [ARITH_ss][is_mmindex_def, EL_APPEND] THEN
                Cases_on `i < LENGTH t` THENL [
                  SRW_TAC [][] THEN
                  FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
                  ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ ARITH_ss) [],
                  `(i = LENGTH t) \/ (i = LENGTH t + 1)` by DECIDE_TAC
                  THENL [
                    SRW_TAC [ARITH_ss][],
                    SRW_TAC [ARITH_ss][DECIDE ``x + 1 - x = 1``]
                  ]
                ]
              ]
            ]
          ]
        ],
        Q_TAC SUFF_TAC
              `is_mmindex (mindepth x) (t ++ [t1; t2]) n d`
              THEN1 (DISCH_THEN (ASSUME_TAC o MATCH_MP mmindex_unique) THEN
                     FIRST_X_ASSUM (MP_TAC o
                                    SPECL [``(t:'a lbtree list) ++ [t1;t2]``,
                                           ``x:'a``]) THEN
                     SRW_TAC [ARITH_ss][] THEN
                     FIRST_X_ASSUM MATCH_MP_TAC THEN
                     `n < LENGTH t`
                       by METIS_TAC [is_mmindex_def, listTheory.LENGTH,
                                     DECIDE ``SUC x < SUC y = x < y``] THEN
                     FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                                   [mindepth_thm, EL_APPEND]) THEN
        `is_mmindex (mindepth x) (Nd a t1 t2::t) (SUC n) d`
           by SRW_TAC [][] THEN
        POP_ASSUM MP_TAC THEN
        REPEAT (POP_ASSUM (K ALL_TAC)) THEN
        SRW_TAC [ARITH_ss][is_mmindex_def, EL_APPEND] THEN
        Cases_on `i < LENGTH t` THENL [
          FIRST_X_ASSUM (Q.SPEC_THEN `SUC i` MP_TAC) THEN
          SRW_TAC [ARITH_ss][],
          `(i = LENGTH t) \/ (i = LENGTH t + 1)` by DECIDE_TAC
          THENL [
            SRW_TAC [ARITH_ss][] THEN
            FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
            SRW_TAC [][mindepth_thm, optmin_EQ_NONE] THEN
            SRW_TAC [][] THEN
            Cases_on `mindepth x t1` THEN
            Cases_on `mindepth x t2` THEN
            FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [arithmeticTheory.MIN_DEF,
                                                  optmin_def],
            SRW_TAC [ARITH_ss][] THEN
            FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
            SRW_TAC [][mindepth_thm, optmin_EQ_NONE] THEN
            SRW_TAC [][] THEN
            Cases_on `mindepth x t1` THEN
            Cases_on `mindepth x t2` THEN
            FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [arithmeticTheory.MIN_DEF,
                                                  optmin_def]
          ]
        ]
      ]
    ]
  ])

(* "delete" all the totally boring auxiliaries *)
val _ = app (fn s => remove_ovl_mapping s {Name = s, Thy = "lbtree"})
            ["optmin", "depth", "mindepth", "is_mmindex"]

val _ = export_theory ()
