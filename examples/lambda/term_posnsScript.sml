open HolKernel Parse boolLib bossLib ncTheory ncLib chap2Theory

open BasicProvers pred_setTheory
open swapTheory

val _ = new_theory "term_posns";

val _ = Hol_datatype `redpos = Lt | Rt | In`;

val _ = type_abbrev ("posn", ``:redpos list``)

val DNF_ss = rewrites [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
                       RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                       IMP_CONJ_THM, DISJ_IMP_THM, FORALL_AND_THM,
                       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
                       EXISTS_OR_THM]

val APPEND_CASES = store_thm(
  "APPEND_CASES",
  ``!l1 l2 m1 m2.
        (APPEND l1 l2 = APPEND m1 m2) =
        (l1 = m1) /\ (l2 = m2) \/
        (?n. (m1 = APPEND l1 n) /\ (l2 = APPEND n m2) /\ ~(n = [])) \/
        (?n. (l1 = APPEND m1 n) /\ (m2 = APPEND n l2) /\ ~(n = []))``,
  Induct THENL [
    SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][] THEN
    PROVE_TAC [listTheory.APPEND],
    SRW_TAC [][] THEN Cases_on `m1` THENL [
      SRW_TAC [][] THEN PROVE_TAC [],
      SRW_TAC [][EQ_IMP_THM] THEN PROVE_TAC [listTheory.APPEND_ASSOC]
    ]
  ]);

val posn_lt_def = Define`
  (posn_lt _ [] = F) /\
  (posn_lt [] _ = T) /\
  (posn_lt (In::ps1) (In::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (In::_) _ = F) /\
  (posn_lt (Lt::ps1) (Lt::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (Lt::_) (In::_) = F) /\
  (posn_lt (Lt::_) (Rt::_) = T) /\
  (posn_lt (Rt::ps1) (Rt::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (Rt::_) _ = F)
`;
val _ = export_rewrites ["posn_lt_def"]


val _ = overload_on ("<", ``posn_lt``);

val posn_lt_inj = store_thm(
  "posn_lt_inj",
  ``!h p1 p2. (h::p1) < (h::p2) = p1 < p2``,
  Cases THEN SRW_TAC [][]);
val _ = BasicProvers.export_rewrites ["posn_lt_inj"]

val posn_lt_nil = store_thm(
  "posn_lt_nil",
  ``!p : posn. ~(p < [])``,
  Cases THEN SRW_TAC [][] THEN Cases_on `h` THEN SRW_TAC [][]);
val _ = BasicProvers.export_rewrites ["posn_lt_nil"]

val posn_lt_trans = store_thm(
  "posn_lt_trans",
  ``!p1 p2 p3 : posn. p1 < p2 /\ p2 < p3 ==> p1 < p3``,
  Induct THENL [
    NTAC 2 (Cases THEN SIMP_TAC (srw_ss()) [posn_lt_def]),
    Cases THEN Induct THEN
    SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    Cases THEN SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    Induct THEN TRY Cases THEN ASM_SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    PROVE_TAC []
  ]);

val posn_lt_irrefl = store_thm(
  "posn_lt_irrefl",
  ``!p : posn. ~(p < p)``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_irrefl"]

val posn_lt_antisym = store_thm(
  "posn_lt_antisym",
  ``!p1 p2. p1 < p2 ==> ~(p2 < p1)``,
  HO_MATCH_MP_TAC (theorem "posn_lt_ind") THEN
  SRW_TAC [][]);

val posn_lt_Lt = store_thm(
  "posn_lt_Lt",
  ``!h p1 p2. ((h::p1) < (Lt::p2) = (h = Lt) /\ p1 < p2) /\
              ((Lt::p1) < (h::p2) = (h = Rt) \/ (h = Lt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_Lt"]

val posn_lt_In = store_thm(
  "posn_lt_In",
  ``!h p1 p2. ((h::p1) < (In::p2) = (h = In) /\ p1 < p2) /\
              ((In::p1) < (h::p2) = (h = In) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_In"]

val posn_lt_Rt = store_thm(
  "posn_lt_Rt",
  ``!h p1 p2. ((h::p1) < (Rt::p2) = (h = Lt) \/ (h = Rt) /\ p1 < p2) /\
              ((Rt::p1) < (h::p2) = (h = Rt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_Rt"]


val (valid_posns_thm, _) = define_recursive_term_function`
  (valid_posns (VAR s) = {[]}) /\
  (valid_posns (CON k) = {[]}) /\
  (valid_posns (t @@ u) = [] INSERT IMAGE (CONS Lt) (valid_posns t) UNION
                                    IMAGE (CONS Rt) (valid_posns u)) /\
  (valid_posns (LAM v t) = [] INSERT IMAGE (CONS In) (valid_posns t))
`;
val _ = prove_vsubst_result valid_posns_thm NONE


val NIL_always_valid = store_thm(
  "NIL_always_valid",
  ``!t. [] IN valid_posns t``,
  GEN_TAC THEN Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][valid_posns_thm]);
val _ = export_rewrites ["NIL_always_valid"]

val valid_posns_FINITE = store_thm(
  "valid_posns_FINITE",
  ``!t : 'a nc. FINITE (valid_posns t)``,
  HO_MATCH_MP_TAC simple_induction THEN SIMP_TAC (srw_ss()) [valid_posns_thm]);
val _ = export_rewrites ["valid_posns_FINITE"]

val all_valid_posns_comparable = store_thm(
  "all_valid_posns_comparable",
  ``!t p1 p2. p1 IN valid_posns t /\ p2 IN valid_posns t ==>
              p1 < p2 \/ (p1 = p2) \/ p2 < p1``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][valid_posns_thm]);

val (var_posns_thm, _) = define_recursive_term_function`
   (var_posns (CON k : 'a nc) = {}) /\
   (var_posns (VAR s) = {[]}) /\
   (var_posns (t @@ u) = IMAGE (CONS Lt) (var_posns t) UNION
                         IMAGE (CONS Rt) (var_posns u)) /\
   (var_posns (LAM v t) = IMAGE (CONS In) (var_posns t))`;
val var_posns_vsubst_invariant = prove_vsubst_result var_posns_thm NONE

val var_posns_FINITE = store_thm(
  "var_posns_FINITE",
  ``!t : 'a nc. FINITE (var_posns t)``,
  HO_MATCH_MP_TAC simple_induction THEN SIMP_TAC (srw_ss()) [var_posns_thm]);
val _ = export_rewrites ["var_posns_FINITE"]

val var_posns_SUBSET_valid_posns = store_thm(
  "var_posns_SUBSET_valid_posns",
  ``!t p. p IN var_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm, var_posns_thm]);

val vp'_var = ``\s : string v. if v = s then {[]: redpos list} else {}``
val vp'_con = ``\k:'a v:string. {} : redpos list set``
val vp'_app = ``\rt ru (t:'a nc) (u:'a nc) v:string.
                    IMAGE (CONS Lt) (rt v) UNION IMAGE (CONS Rt) (ru v)``
val vp'_lam = ``\rt u:string t:'a nc v:string. IMAGE (CONS In) (rt v)``

open metisLib

val v_posns'_exists =
    (SIMP_RULE (srw_ss()) [str_swapping, swapfn_def, null_swapping] o
     Q.INST [`rswap` |-> `\x y z. z`,
             `rFV` |-> `K {}`,
             `pswap` |-> `swapstr`,
             `pFV` |-> `\s. {s}`,
             `X` |-> `{}`,
             `var` |-> `^vp'_var`,
             `con` |-> `^vp'_con`,
             `app` |-> `^vp'_app`,
             `lam` |-> `^vp'_lam`] o
     INST_TYPE [beta |-> ``:string``, gamma |-> ``:redpos list set``])
    swapTheory.swap_RECURSION_pgeneric

val swap_args = prove(``(?f:'a -> 'b -> 'c. P f) =
                        (?g:'b -> 'a -> 'c. P (\a b. g b a))``,
                      SRW_TAC [][EQ_IMP_THM] THENL [
                        Q.EXISTS_TAC `\a b. f b a` THEN
                        SRW_TAC [boolSimps.ETA_ss][],
                        PROVE_TAC []
                      ]);

val v_posns_exists =
    CONV_RULE (HO_REWR_CONV swap_args THENC SIMP_CONV bool_ss [])
              v_posns'_exists

val v_posns_def = new_specification("v_posns_def", ["v_posns"],
                                    v_posns_exists);

val v_posns_thm0 = save_thm("v_posns_thm0", CONJUNCT1 v_posns_def)
val v_posns_swap_invariant =
    save_thm("v_posns_swap_invariant", CONJUNCT2 v_posns_def)
val _ = export_rewrites ["v_posns_swap_invariant"]

val v_posns_FV = store_thm(
  "v_posns_FV",
  ``!t v. ~(v IN FV t) ==> (v_posns v t = {})``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][v_posns_thm0] THEN
  Q_TAC (NEW_TAC "z") `{v;v'} UNION FV t` THEN
  `LAM v t = LAM z (swap z v t)` by SRW_TAC [][swap_ALPHA] THEN
  SRW_TAC [][v_posns_thm0] THEN Cases_on `v = v'` THEN SRW_TAC [][]);

val v_posns_LAM = prove(
  ``v_posns v (LAM u t) = if v = u then {}
                          else IMAGE (CONS In) (v_posns v t)``,
  SRW_TAC [][v_posns_FV, v_posns_thm0]);
val v_posns_thm = save_thm(
  "v_posns_thm",
  LIST_CONJ (butlast (CONJUNCTS v_posns_thm0) @ [GEN_ALL v_posns_LAM]))

val v_posns_vsubst = store_thm(
  "v_posns_vsubst",
  ``!M x y z.
        v_posns x ([VAR y/z] M) =
           if x = y then v_posns x M UNION v_posns z M
           else if x = z then {}
           else v_posns x M``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss()) [v_posns_thm, SUB_THM, SUB_VAR] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN SRW_TAC [][v_posns_thm],
    REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SRW_TAC [][] THEN REWRITE_TAC [EXTENSION] THEN
    METIS_TAC [IN_UNION],

    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN SRW_TAC [][v_posns_thm, SUB_THM] THEN
    Q_TAC (NEW_TAC "u") `{x;y;z;v} UNION FV M` THEN
    `LAM v M = LAM u (swap u v M)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][SUB_THM, v_posns_thm, swap_subst_out, swapstr_def,
               swap_thm, v_posns_FV, IMAGE_EQ_EMPTY] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val v_posns_FV_EQ = store_thm(
  "v_posns_FV_EQ",
  ``!t v. (v_posns v t = {}) = ~(v IN FV t)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, v_posns_FV] THEN
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][v_posns_thm, IMAGE_EQ_EMPTY] THEN
  PROVE_TAC [IMAGE_EQ_EMPTY]);

val v_posns_LAM_COND = store_thm(
  "v_posns_LAM_COND",
  ``!v w t. v_posns v (LAM w t) = if v = w then {}
                                  else IMAGE (CONS In) (v_posns v t)``,
  SRW_TAC [][v_posns_thm]);

val v_posns_SUBSET_var_posns = store_thm(
  "v_posns_SUBSET_var_posns",
  ``!t v p. p IN v_posns v t ==> p IN var_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][v_posns_thm, var_posns_thm] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    Cases_on `v = v'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    PROVE_TAC []
  ]);

val IMAGE_DIFF = prove(
  ``(!x y. (f x = f y) = (x = y)) ==>
    (IMAGE f (P DIFF Q) = IMAGE f P DIFF IMAGE f Q)``,
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val IMAGE_CONS_APPEND = prove(
  ``IMAGE (CONS v) {APPEND x y | P x /\ Q y} =
    {APPEND x y | (?x'. (x = v::x') /\ P x') /\ Q y}``,
  SRW_TAC [][EXTENSION, EQ_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
             GSYM LEFT_EXISTS_AND_THM] THEN PROVE_TAC []);

val var_posns_subst = store_thm(
  "var_posns_subst",
  ``!x v t. var_posns ([t/v] x) =
               (var_posns x DIFF v_posns v x) UNION
               {APPEND p1 p2 | p1 IN v_posns v x /\ p2 IN var_posns t}``,
  HO_MATCH_MP_TAC simple_induction THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss ++ DNF_ss)
             [var_posns_thm, v_posns_thm, SUB_THM, SUB_VAR,
              EXTENSION, EQ_IMP_THM],
    SRW_TAC [][var_posns_thm, v_posns_thm, SUB_THM,
               EXTENSION],
    SRW_TAC [][var_posns_thm, v_posns_thm, SUB_THM] THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION, EQ_IMP_THM] THEN
    REPEAT CONJ_TAC THEN PROVE_TAC [],
    REPEAT STRIP_TAC THEN
    Q_TAC (NEW_TAC "z") `FV x UNION FV t UNION {v;v'}` THEN
    `LAM v x = LAM z (swap z v x)` by SRW_TAC [][swap_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss())
                 [SUB_THM, var_posns_thm, v_posns_thm,
                  v_posns_FV, swap_subst_out] THEN
    Cases_on `v = v'` THEN
    SRW_TAC [][swapstr_def, v_posns_FV, IMAGE_DIFF, IMAGE_CONS_APPEND]
  ]);

val (bv_posns_thm, _) = define_recursive_term_function
  `(bv_posns (LAM v t : 'a nc) = IMAGE (CONS In) (v_posns v t)) /\
   (bv_posns (CON k) = {}) /\
   (bv_posns (VAR s) = {}) /\
   (bv_posns (t @@ u) = {})`;


val bv_posns_vsubst =
    prove_vsubst_result bv_posns_thm
                        (SOME (NEW_ELIM_TAC THEN SRW_TAC [][v_posns_vsubst]))

val (lam_posns_thm, _) = define_recursive_term_function`
  (lam_posns (VAR s : 'a nc) = {}) /\
  (lam_posns (CON k) = {}) /\
  (lam_posns (t @@ u) = IMAGE (CONS Lt) (lam_posns t) UNION
                        IMAGE (CONS Rt) (lam_posns u)) /\
  (lam_posns (LAM v t) = [] INSERT IMAGE (CONS In) (lam_posns t))
`;
val lam_posns_vsubst = prove_vsubst_result lam_posns_thm NONE

val lam_posns_SUBSET_valid_posns = store_thm(
  "lam_posns_SUBSET_valid_posns",
  ``!t p. p IN lam_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm, lam_posns_thm]);

val lam_posns_var_posns = store_thm(
  "lam_posns_var_posns",
  ``!t p. ~(p IN lam_posns t /\ p IN var_posns t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][var_posns_thm, lam_posns_thm] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val (redex_posns_thm, _) = define_recursive_term_function`
  (redex_posns (VAR s : 'a nc) = {}) /\
  (redex_posns (CON k) = {}) /\
  (redex_posns (t @@ u) =
     IMAGE (CONS Lt) (redex_posns t) UNION
     IMAGE (CONS Rt) (redex_posns u) UNION
     (if is_abs t then {[]} else {})) /\
  (redex_posns (LAM v t) = IMAGE (CONS In) (redex_posns t))
`;

val redex_posns_vsubst_invariant = prove_vsubst_result redex_posns_thm NONE

val redex_posns_are_valid = store_thm(
  "redex_posns_are_valid",
  ``!t p. p IN redex_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm, redex_posns_thm]);

val bv_posns_at_exists0 =
    (SIMP_RULE (srw_ss()) [GSYM swap_thm] o
     SIMP_RULE (srw_ss()) [] o
     Q.INST [`var` |-> `\s l. {}`,
             `con` |-> `\k l. {}`,
             `app` |-> `\rt ru t u l.
                           case l of
                              Lt::rest -> IMAGE (CONS Lt) (rt rest)
                           || Rt::rest -> IMAGE (CONS Rt) (ru rest)
                           || _ -> {}`,
             `lam` |-> `\rt v t l.
                           case l of
                              [] -> bv_posns (LAM v t)
                           || In::rest -> IMAGE (CONS In) (rt rest)
                           || _ -> {}`] o
     INST_TYPE [beta |-> ``:redpos list -> redpos list set``])
    swap_RECURSION_simple

val bv_posns_at_exists = prove(
  ``?bv_posns_at.
       ((!s l. bv_posns_at l (VAR s) = {}) /\
        (!k l. bv_posns_at l (CON k) = {}) /\
        (!t u l. bv_posns_at l (t @@ u) =
                   case l of
                      (Lt::rest) -> IMAGE (CONS Lt) (bv_posns_at rest t)
                   || (Rt::rest) -> IMAGE (CONS Rt) (bv_posns_at rest u)
                   || _ -> {}) /\
        (!v t l. bv_posns_at l (LAM v t) =
                   case l of
                      [] -> bv_posns (LAM v t)
                   || In::rest -> IMAGE (CONS In) (bv_posns_at rest t)
                   || _ -> {})) /\
       !t l x y. bv_posns_at l (swap x y t) = bv_posns_at l t``,
  STRIP_ASSUME_TAC bv_posns_at_exists0 THEN
  Q.EXISTS_TAC `\l t. hom t l` THEN SRW_TAC [][]);

val bv_posns_at_def = new_specification("bv_posns_at_def", ["bv_posns_at"],
                                        bv_posns_at_exists)

val bv_posns_at_thm = save_thm("bv_posns_at_thm", CONJUNCT1 bv_posns_at_def)

val bv_posns_at_swap_invariant = save_thm(
  "bv_posns_at_swap_invariant",
  CONJUNCT2 bv_posns_at_def);
val _ = export_rewrites ["bv_posns_at_swap_invariant"]

val bv_posns_at_vsubst = store_thm(
  "bv_posns_at_vsubst",
  ``!t v u p. bv_posns_at p ([VAR v/u] t) = bv_posns_at p t``,
  vsubst_tac bv_posns_at_thm THEN
  NEW_ELIM_TAC THEN SRW_TAC [][bv_posns_thm, v_posns_vsubst]);
val _ = export_rewrites ["bv_posns_at_vsubst"]

val bv_posns_at_SUBSET_var_posns = store_thm(
  "bv_posns_at_SUBSET_var_posns",
  ``!t p1 p2. p1 IN lam_posns t /\ p2 IN bv_posns_at p1 t ==>
              p2 IN var_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss()) [lam_posns_thm, var_posns_thm, bv_posns_at_thm,
                       DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
                       FORALL_AND_THM, RIGHT_AND_OVER_OR,
                       GSYM LEFT_EXISTS_AND_THM,
                       GSYM RIGHT_EXISTS_AND_THM, bv_posns_thm] THEN
  PROVE_TAC [v_posns_SUBSET_var_posns]);

val lam_posns_subst = store_thm(
  "lam_posns_subst",
  ``!t u v. lam_posns ([u/v] t) = lam_posns t UNION
                                  {APPEND p1 p2 | p1 IN v_posns v t /\
                                                  p2 IN lam_posns u}``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss()) [SUB_THM, SUB_VAR, lam_posns_thm, v_posns_thm] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][EXTENSION, lam_posns_thm],
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION] THEN PROVE_TAC [],
    MAP_EVERY Q.X_GEN_TAC [`x`, `t`] THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`u`, `v`] THEN
    Q_TAC (NEW_TAC "z") `{v; x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z (swap z x t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [DNF_ss][SUB_THM, lam_posns_thm, v_posns_thm, EXTENSION,
                     swap_subst_out, v_posns_FV] THEN
    PROVE_TAC []
  ]);

val v_posns_subst = store_thm(
  "v_posns_subst",
  ``!t u v w. v_posns v ([u/w] t) =
              if v = w then { APPEND p1 p2 | p1 IN v_posns v t /\
                                             p2 IN v_posns v u}
              else v_posns v t UNION
                   { APPEND p1 p2 | p1 IN v_posns w t /\ p2 IN v_posns v u}``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss())[SUB_VAR, SUB_THM, v_posns_thm, EXTENSION] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    REPEAT VAR_EQ_TAC THEN ASM_SIMP_TAC (srw_ss()) [v_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [DNF_ss][] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    COND_CASES_TAC THEN REPEAT VAR_EQ_TAC THEN SRW_TAC [DNF_ss][] THEN
    PROVE_TAC [],
    MAP_EVERY Q.X_GEN_TAC [`x`, `t`] THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`u`,`v`,`w`,`y`] THEN
    Q_TAC (NEW_TAC "z") `{v;w;x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z (swap z x t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][SUB_THM, swap_subst_out, v_posns_thm, v_posns_FV] THEN
    SRW_TAC [DNF_ss][] THEN PROVE_TAC []
  ]);

val bv_posns_at_subst = store_thm(
  "bv_posns_at_subst",
  ``!t u v p. p IN lam_posns t ==>
              (bv_posns_at p ([v/u] t) = bv_posns_at p t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm] THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm,
             lam_posns_subst] THEN
  Q_TAC (NEW_TAC "z") `{u; x} UNION FV t UNION FV v` THEN
  `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THENL [
    SRW_TAC [][SUB_THM, bv_posns_at_thm, v_posns_subst, v_posns_FV,
               v_posns_thm, EXTENSION, bv_posns_thm],
    SRW_TAC [][SUB_THM, bv_posns_at_thm, lam_posns_subst]
  ]);

val bv_posns_at_subst2 = store_thm(
  "bv_posns_at_subst2",
  ``!t u v vp m.
       vp IN v_posns v t /\ m IN lam_posns u ==>
       (bv_posns_at (APPEND vp m) ([u/v] t) =
        IMAGE (APPEND vp) (bv_posns_at m u))``,
  HO_MATCH_MP_TAC simple_induction THEN
  ASM_SIMP_TAC (srw_ss()) [v_posns_thm, SUB_THM, SUB_VAR] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][EXTENSION],
    REPEAT STRIP_TAC THENL [
      `APPEND x m IN lam_posns ([u/v] t)`
          by (SRW_TAC [][lam_posns_subst] THEN PROVE_TAC []) THEN
      SRW_TAC [DNF_ss][bv_posns_at_thm, EXTENSION],
      `APPEND x m IN lam_posns ([u/v] t')`
          by (SRW_TAC [][lam_posns_subst] THEN PROVE_TAC []) THEN
      SRW_TAC [DNF_ss][bv_posns_at_thm, EXTENSION]
    ],
    MAP_EVERY Q.X_GEN_TAC [`x`, `t`] THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`u`,`v`,`vp`,`m`] THEN
    Cases_on `x = v` THEN SRW_TAC [][] THEN
    Q_TAC (NEW_TAC "z") `FV t UNION FV u UNION {x;v}` THEN
    `LAM x t = LAM z (swap z x t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][SUB_THM, bv_posns_at_thm, swap_subst_out] THEN
    SRW_TAC [DNF_ss][EXTENSION]
  ]);

val bv_posns_at_prefix_posn = store_thm(
  "bv_posns_at_prefix_posn",
  ``!p t bvp. p IN lam_posns t /\ bvp IN bv_posns_at p t ==>
              ?m. bvp = APPEND p (In::m)``,
  Induct THEN
  REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [bv_posns_at_def] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ boolSimps.CONJ_ss)
               [lam_posns_thm, bv_posns_thm, bv_posns_at_thm] THEN
  PROVE_TAC []);

val v_posns_injective = store_thm(
  "v_posns_injective",
  ``!t v1 p. p IN v_posns v1 t ==> (p IN v_posns v2 t = (v1 = v2))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][v_posns_thm],
    SRW_TAC [][v_posns_thm],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [v_posns_thm] THEN
    ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    Q_TAC (NEW_TAC "z") `{v1; v2; x} UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [v_posns_LAM_COND] THEN
    REPEAT COND_CASES_TAC THEN SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    PROVE_TAC []
  ]);

val v_posns_arent_bv_posns = store_thm(
  "v_posns_arent_bv_posns",
  ``!t lp p. lp IN lam_posns t /\ p IN bv_posns_at lp t ==>
             !v. ~(p IN v_posns v t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [] [lam_posns_thm, bv_posns_at_thm, v_posns_thm,
              bv_posns_thm] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][bv_posns_at_thm] THEN
  PROVE_TAC [v_posns_injective]);

val no_var_posns_in_var_posn_prefix = store_thm(
  "no_var_posns_in_var_posn_prefix",
  ``!t p1 l.
       p1 IN var_posns t /\ APPEND p1 l IN var_posns t ==> (l = [])``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  REWRITE_TAC[var_posns_thm, theorem "var_posns_vsubst_invariant"] THEN
  REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [],
    SIMP_TAC (srw_ss()) [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN ASM_REWRITE_TAC []
  ]);

val APPEND_var_posns = store_thm(
  "APPEND_var_posns",
  ``!vp1 vp2 t.
        vp1 IN var_posns t /\ vp2 IN var_posns t ==>
        !x y. (APPEND vp1 x = APPEND vp2 y) = (vp1 = vp2) /\ (x = y)``,
  SRW_TAC [][APPEND_CASES, EQ_IMP_THM] THEN
  PROVE_TAC [no_var_posns_in_var_posn_prefix]);

val valid_posns_subst = store_thm(
  "valid_posns_subst",
  ``!t u v. valid_posns ([u/v] t) =
              valid_posns t UNION
              {APPEND p1 p2 | p1 IN v_posns v t /\ p2 IN valid_posns u}``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][valid_posns_thm, v_posns_thm, SUB_THM] THENL [
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss() ++ DNF_ss)[EXTENSION, EQ_IMP_THM],
    SRW_TAC [][EXTENSION],
    SRW_TAC [][EXTENSION] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    SRW_TAC [DNF_ss][] THEN PROVE_TAC [],
    Q_TAC (NEW_TAC "z") `{v;x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][SUB_THM, valid_posns_thm, v_posns_thm, v_posns_vsubst] THEN
    SRW_TAC [DNF_ss][EXTENSION] THEN PROVE_TAC []
  ]);

val cant_be_deeper_than_var_posns = store_thm(
  "cant_be_deeper_than_var_posns",
  ``!t p1 p. p1 IN var_posns t /\ APPEND p1 p IN valid_posns t ==>
             (p = [])``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][var_posns_thm, valid_posns_thm],
    SRW_TAC [][var_posns_thm, valid_posns_thm],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [var_posns_thm, valid_posns_thm] THEN
    ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [var_posns_thm, valid_posns_thm] THEN
    PROVE_TAC [lemma14a]
  ]);



val NIL_IN_v_posns = store_thm(
  "NIL_IN_v_posns",
  ``!t v. [] IN v_posns v t = (t = VAR v)``,
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][v_posns_thm, v_posns_LAM_COND]);

val v_posns_FINITE = store_thm(
  "v_posns_FINITE",
  ``!v t. FINITE (v_posns v t)``,
  PROVE_TAC [v_posns_SUBSET_var_posns, var_posns_FINITE,
             pred_setTheory.SUBSET_FINITE, pred_setTheory.SUBSET_DEF]);

val _ = export_rewrites ["v_posns_FINITE"]




val _ = export_theory()

