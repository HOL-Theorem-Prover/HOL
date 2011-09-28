open HolKernel Parse boolLib bossLib termTheory binderLib chap2Theory

open BasicProvers pred_setTheory boolSimps

val _ = new_theory "term_posns";

fun Store_Thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]
fun Save_Thm(n,th) = save_thm(n,th) before export_rewrites [n]


(* ----------------------------------------------------------------------
    type of (term) positions
   ---------------------------------------------------------------------- *)

val _ = Hol_datatype `redpos = Lt | Rt | In`;

val _ = type_abbrev ("posn", ``:redpos list``)

val APPEND_CASES = store_thm(
  "APPEND_CASES",
  ``!l1 l2 m1 m2.
        (APPEND l1 l2 = APPEND m1 m2) <=>
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

(* ----------------------------------------------------------------------
    ordering positions
   ---------------------------------------------------------------------- *)

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

val posn_lt_inj = Store_Thm(
  "posn_lt_inj",
  ``!h p1 p2. (h::p1) < (h::p2) <=> p1 < p2``,
  Cases THEN SRW_TAC [][]);

val posn_lt_nil = Store_Thm(
  "posn_lt_nil",
  ``!p : posn. ~(p < [])``,
  Cases THEN SRW_TAC [][] THEN Cases_on `h` THEN SRW_TAC [][]);

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

val posn_lt_irrefl = Store_Thm(
  "posn_lt_irrefl",
  ``!p : posn. ~(p < p)``,
  Induct THEN SRW_TAC [][]);

val posn_lt_antisym = store_thm(
  "posn_lt_antisym",
  ``!p1 p2. p1 < p2 ==> ~(p2 < p1)``,
  HO_MATCH_MP_TAC (theorem "posn_lt_ind") THEN
  SRW_TAC [][]);

val posn_lt_Lt = Store_Thm(
  "posn_lt_Lt",
  ``!h p1 p2. ((h::p1) < (Lt::p2) <=> (h = Lt) /\ p1 < p2) /\
              ((Lt::p1) < (h::p2) <=> (h = Rt) \/ (h = Lt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);

val posn_lt_In = Store_Thm(
  "posn_lt_In",
  ``!h p1 p2. ((h::p1) < (In::p2) <=> (h = In) /\ p1 < p2) /\
              ((In::p1) < (h::p2) <=> (h = In) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);

val posn_lt_Rt = Store_Thm(
  "posn_lt_Rt",
  ``!h p1 p2. ((h::p1) < (Rt::p2) <=> (h = Lt) \/ (h = Rt) /\ p1 < p2) /\
              ((Rt::p1) < (h::p2) <=> (h = Rt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    all of a term's positions (valid_posns)
   ---------------------------------------------------------------------- *)

val (valid_posns_thm, _) = define_recursive_term_function`
  (valid_posns (VAR s) = {[]}) /\
  (valid_posns (t @@ u) = [] INSERT IMAGE (CONS Lt) (valid_posns t) UNION
                                    IMAGE (CONS Rt) (valid_posns u)) /\
  (valid_posns (LAM v t) = [] INSERT IMAGE (CONS In) (valid_posns t))
`;
val _ = export_rewrites ["valid_posns_thm"]

val valid_posns_vsubst = Store_Thm(
  "valid_posns_vsubst",
  ``!M. valid_posns ([VAR v/u] M) = valid_posns M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);


val NIL_always_valid = Store_Thm(
  "NIL_always_valid",
  ``!t. [] IN valid_posns t``,
  GEN_TAC THEN Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][]);

val valid_posns_FINITE = Store_Thm(
  "valid_posns_FINITE",
  ``!t : term. FINITE (valid_posns t)``,
  HO_MATCH_MP_TAC simple_induction THEN SIMP_TAC (srw_ss()) []);

val all_valid_posns_comparable = store_thm(
  "all_valid_posns_comparable",
  ``!t p1 p2. p1 IN valid_posns t /\ p2 IN valid_posns t ==>
              p1 < p2 \/ (p1 = p2) \/ p2 < p1``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    positions of all of a term's variables, free or bound.  (var_posns)
   ---------------------------------------------------------------------- *)

val (var_posns_thm, _) = define_recursive_term_function`
   (var_posns (VAR s) = {[]}) /\
   (var_posns (t @@ u) = IMAGE (CONS Lt) (var_posns t) UNION
                         IMAGE (CONS Rt) (var_posns u)) /\
   (var_posns (LAM v t) = IMAGE (CONS In) (var_posns t))`;
val _ = export_rewrites ["var_posns_thm"]

val var_posns_vsubst_invariant = Store_Thm(
  "var_posns_vsubst_invariant",
  ``!M. var_posns ([VAR v/u]M) = var_posns M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val var_posns_FINITE = Store_Thm(
  "var_posns_FINITE",
  ``!t:term. FINITE (var_posns t)``,
  HO_MATCH_MP_TAC simple_induction THEN SIMP_TAC (srw_ss()) []);

val var_posns_SUBSET_valid_posns = store_thm(
  "var_posns_SUBSET_valid_posns",
  ``!t p. p IN var_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][]);

(* ----------------------------------------------------------------------
    positions with a term of a particular free variable (v_posns)
   ---------------------------------------------------------------------- *)

val vp'_var = ``\(s : string) v. if v = s then {[]: redpos list} else {}``
val vp'_lam = ``\rt (w:string) t:term (v:string). IMAGE (CONS In) (rt v)``

val lemma = prove(
  ``fnpm dact discrete_pmact pi f x = f (pmact dact pi⁻¹ x)``,
  SRW_TAC [][nomsetTheory.fnpm_def]);

val flip_args = prove(
  ``(?f: 'a -> 'b -> 'c. P f) <=> (?f : 'b -> 'a -> 'c. P (λa b. f b a))``,
  SRW_TAC [][EQ_IMP_THM] THEN1 (Q.EXISTS_TAC `λb a. f a b` THEN SRW_TAC [ETA_ss][]) THEN
  METIS_TAC []);

val v_posns_exists =
    termTheory.parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:posn set``, ``:ρ`` |-> ``:string``]
        |> SPEC_ALL
        |> Q.INST [`apm` |-> `discrete_pmact`, `ppm` |-> `string_pmact`,
             `A` |-> `{}`,
             `vr` |-> `^vp'_var`,
             `ap` |-> `\rt ru t u v. IMAGE (CONS Lt) (rt v) ∪ IMAGE (CONS Rt) (ru v)`,
             `lm` |-> `^vp'_lam`]
        |> SIMP_RULE (srw_ss()) [GSYM basic_swapTheory.swapstr_eq_left,
                                 lemma]
        |> SIMP_RULE (srw_ss()) [Once flip_args]

val v_posns_def = new_specification("v_posns_def", ["v_posns"],
                                    v_posns_exists);

val lemma = v_posns_def |> CONJUNCT2 |> SPEC_ALL |> Q.INST [`p` |-> `swapstr x y p`]
                        |> SIMP_RULE (srw_ss()) []

val v_posns_tpm_invariant = Store_Thm(
  "v_posns_tpm_invariant",
  ``!M v. v_posns v (tpm pi M) = v_posns (lswapstr (REVERSE pi) v) M``,
  Induct_on `pi` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, nomsetTheory.pmact_decompose] THEN
  POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN
  SRW_TAC [][lemma, GSYM nomsetTheory.pmact_decompose]);

val v_posns_FV = store_thm(
  "v_posns_FV",
  ``!t. ~(v IN FV t) ==> (v_posns v t = {})``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][v_posns_def]);

val v_posns_LAM = prove(
  ``v_posns v (LAM u t) = if v = u then {}
                          else IMAGE (CONS In) (v_posns v t)``,
  SRW_TAC [][v_posns_FV, v_posns_def]);

val v_posns_thm = Save_Thm(
  "v_posns_thm",
  LIST_CONJ (butlast (CONJUNCTS (CONJUNCT1 v_posns_def)) @
             [GEN_ALL v_posns_LAM]))

val v_posns_vsubst = store_thm(
  "v_posns_vsubst",
  ``!M x y z.
        v_posns x ([VAR y/z] M) =
           if x = y then v_posns x M UNION v_posns z M
           else if x = z then {}
           else v_posns x M``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `M` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `{x;y;z}` THEN
  SIMP_TAC (srw_ss()) [v_posns_thm, SUB_THM, SUB_VAR] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN SRW_TAC [][v_posns_thm],
    REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    SRW_TAC [][] THEN REWRITE_TAC [EXTENSION] THEN
    METIS_TAC [IN_UNION],

    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN SRW_TAC [][]
  ]);

val v_posns_FV_EQ = store_thm(
  "v_posns_FV_EQ",
  ``!t v. (v_posns v t = {}) = ~(v IN FV t)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, v_posns_FV] THEN
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][v_posns_thm, IMAGE_EQ_EMPTY] THEN
  PROVE_TAC [IMAGE_EQ_EMPTY]);

val v_posns_LAM_COND = save_thm("v_posns_LAM_COND", v_posns_LAM);

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
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `x` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV t` THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss ++ DNF_ss)
             [var_posns_thm, v_posns_thm, SUB_THM, SUB_VAR,
              EXTENSION, EQ_IMP_THM],
    SRW_TAC [][var_posns_thm, v_posns_thm, SUB_THM] THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION, EQ_IMP_THM] THEN
    REPEAT CONJ_TAC THEN PROVE_TAC [],
    SRW_TAC [][SUB_THM, var_posns_thm, v_posns_thm] THEN
    SRW_TAC [][IMAGE_DIFF, IMAGE_CONS_APPEND],
    SRW_TAC [][]
  ]);

(* ----------------------------------------------------------------------
    positions of the bound variables underneath an abstraction
   ---------------------------------------------------------------------- *)

val (bv_posns_thm, _) = define_recursive_term_function
  `(bv_posns (LAM v t : term) = IMAGE (CONS In) (v_posns v t)) /\
   (bv_posns (VAR s) = {}) /\
   (bv_posns (t @@ u) = {})`;
val _ = export_rewrites ["bv_posns_thm"]

val bv_posns_vsubst = Store_Thm(
  "bv_posns_vsubst",
  ``!M. bv_posns ([VAR v/u] M) = bv_posns M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, v_posns_vsubst]);

(* ----------------------------------------------------------------------
    positions of all a term's abstractions
   ---------------------------------------------------------------------- *)

val (lam_posns_thm, _) = define_recursive_term_function`
  (lam_posns (VAR s : term) = {}) /\
  (lam_posns (t @@ u) = IMAGE (CONS Lt) (lam_posns t) UNION
                        IMAGE (CONS Rt) (lam_posns u)) /\
  (lam_posns (LAM v t) = [] INSERT IMAGE (CONS In) (lam_posns t))
`;
val _ = export_rewrites ["lam_posns_thm"]

val lam_posns_vsubst = Store_Thm(
  "lam_posns_vsubst",
  ``!M. lam_posns ([VAR v/u]M) = lam_posns M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val lam_posns_SUBSET_valid_posns = store_thm(
  "lam_posns_SUBSET_valid_posns",
  ``!t p. p IN lam_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][]);

val lam_posns_var_posns = store_thm(
  "lam_posns_var_posns",
  ``!t p. ~(p IN lam_posns t /\ p IN var_posns t)``,
  Q_TAC SUFF_TAC `!t p. p IN lam_posns t ==> ~(p IN var_posns t)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][var_posns_thm, lam_posns_thm] THEN
  METIS_TAC []);

(* ----------------------------------------------------------------------
    positions of all a term's redexes
   ---------------------------------------------------------------------- *)

val (redex_posns_thm, _) = define_recursive_term_function`
  (redex_posns (VAR s : term) = {}) /\
  (redex_posns (t @@ u) =
     IMAGE (CONS Lt) (redex_posns t) UNION
     IMAGE (CONS Rt) (redex_posns u) UNION
     (if is_abs t then {[]} else {})) /\
  (redex_posns (LAM v t) = IMAGE (CONS In) (redex_posns t))
`;

val redex_posns_vsubst_invariant = Store_Thm(
  "redex_posns_vsubst_invariant",
  ``!M. redex_posns ([VAR v/u]M) = redex_posns M``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, redex_posns_thm]);

val redex_posns_are_valid = store_thm(
  "redex_posns_are_valid",
  ``!t p. p IN redex_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm, redex_posns_thm]);

(* ----------------------------------------------------------------------
    bv_posns_at : posn -> term -> posn set
       assuming posn is the position of an abstraction within the term,
       return the set of positions of its bound variables.  Otherwise,
       return {}
   ---------------------------------------------------------------------- *)

val bv_posns_at_exists0 =
    tm_recursion_nosideset
        |> SPEC_ALL
        |> INST_TYPE [alpha |-> ``:redpos list -> redpos list set``]
        |> Q.INST [`apm` |-> `discrete_pmact`,
             `vr` |-> `\s l. {}`,
             `ap` |-> `\rt ru t u l.
                           case l of
                             Lt::rest => IMAGE (CONS Lt) (rt rest)
                           | Rt::rest => IMAGE (CONS Rt) (ru rest)
                           | _ => {}`,
             `lm` |-> `\rt v t l.
                           case l of
                             [] => bv_posns (LAM v t)
                           | In::rest => IMAGE (CONS In) (rt rest)
                           | _ => {}`]
        |> SIMP_RULE (srw_ss()) []
        |> CONV_RULE (QUANT_CONV (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])))

val bv_posns_at_exists = prove(
  ``?bv_posns_at.
       ((!s l. bv_posns_at l (VAR s) = {}) /\
        (!t u l. bv_posns_at l (t @@ u) =
                   case l of
                     (Lt::rest) => IMAGE (CONS Lt) (bv_posns_at rest t)
                   | (Rt::rest) => IMAGE (CONS Rt) (bv_posns_at rest u)
                   | _ => {}) /\
        (!v t l. bv_posns_at l (LAM v t) =
                   case l of
                     [] => bv_posns (LAM v t)
                   | In::rest => IMAGE (CONS In) (bv_posns_at rest t)
                   | _ => {})) /\
       !t l p. bv_posns_at l (tpm p t) = bv_posns_at l t``,
  Q.X_CHOOSE_THEN `f` STRIP_ASSUME_TAC bv_posns_at_exists0 THEN
  Q.EXISTS_TAC `\l t. f t l` THEN SRW_TAC [][]);

val bv_posns_at_def = new_specification("bv_posns_at_def", ["bv_posns_at"],
                                        bv_posns_at_exists)

val bv_posns_at_thm = save_thm("bv_posns_at_thm", CONJUNCT1 bv_posns_at_def)

val bv_posns_at_swap_invariant = Save_Thm(
  "bv_posns_at_swap_invariant",
  CONJUNCT2 bv_posns_at_def);

val bv_posns_at_vsubst = Store_Thm(
  "bv_posns_at_vsubst",
  ``!t p. bv_posns_at p ([VAR v/u] t) = bv_posns_at p t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, v_posns_vsubst, bv_posns_at_thm,
             bv_posns_thm])

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
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `t` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SIMP_TAC (srw_ss()) [SUB_THM, SUB_VAR, lam_posns_thm, v_posns_thm] THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION] THEN PROVE_TAC [],
    SRW_TAC [DNF_ss][lam_posns_thm, v_posns_thm, EXTENSION,
                     v_posns_FV] THEN
    PROVE_TAC []
  ]);

val v_posns_subst = store_thm(
  "v_posns_subst",
  ``!t u v w. v_posns v ([u/w] t) =
              if v = w then { APPEND p1 p2 | p1 IN v_posns v t /\
                                             p2 IN v_posns v u}
              else v_posns v t UNION
                   { APPEND p1 p2 | p1 IN v_posns w t /\ p2 IN v_posns v u}``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `t` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v;w} UNION FV u` THEN
  SIMP_TAC (srw_ss()) [SUB_VAR, SUB_THM, v_posns_thm, EXTENSION] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    REPEAT VAR_EQ_TAC THEN ASM_SIMP_TAC (srw_ss()) [v_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [DNF_ss][] THEN PROVE_TAC [],
    SRW_TAC [DNF_ss][] THEN PROVE_TAC []
  ]);

val bv_posns_at_subst = store_thm(
  "bv_posns_at_subst",
  ``!t u v p. p IN lam_posns t ==>
              (bv_posns_at p ([v/u] t) = bv_posns_at p t)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `u INSERT FV v` THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm] THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm,
             lam_posns_subst, bv_posns_thm, v_posns_subst, v_posns_FV] THEN
  SRW_TAC [][EXTENSION]);

val bv_posns_at_subst2 = store_thm(
  "bv_posns_at_subst2",
  ``!t u v vp m.
       vp IN v_posns v t /\ m IN lam_posns u ==>
       (bv_posns_at (APPEND vp m) ([u/v] t) =
        IMAGE (APPEND vp) (bv_posns_at m u))``,
  REPEAT GEN_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`m`, `vp`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV u` THEN
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
    SRW_TAC [][bv_posns_at_thm] THEN SRW_TAC [DNF_ss][EXTENSION]
  ]);

val bv_posns_at_prefix_posn = store_thm(
  "bv_posns_at_prefix_posn",
  ``∀p t bvp. p ∈ lam_posns t /\ bvp ∈ bv_posns_at p t ==>
              ∃m. bvp = p ++ [In] ++ m``,
  Induct THEN
  REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [bv_posns_at_def] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ boolSimps.CONJ_ss)
               [lam_posns_thm, bv_posns_thm, bv_posns_at_thm] THEN
  PROVE_TAC []);

val v_posns_injective = store_thm(
  "v_posns_injective",
  ``!t v1 p. p IN v_posns v1 t ==> (p IN v_posns v2 t <=> (v1 = v2))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`p`, `t`] THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v1;v2}` THEN
  SRW_TAC [][v_posns_thm] THEN PROVE_TAC []);

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
  HO_MATCH_MP_TAC simple_induction THEN
  REWRITE_TAC[var_posns_thm, theorem "var_posns_vsubst_invariant"] THEN
  REPEAT CONJ_TAC THENL [
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
        !x y. (APPEND vp1 x = APPEND vp2 y) <=> (vp1 = vp2) /\ (x = y)``,
  SRW_TAC [][APPEND_CASES, EQ_IMP_THM] THEN
  PROVE_TAC [no_var_posns_in_var_posn_prefix]);

val valid_posns_subst = store_thm(
  "valid_posns_subst",
  ``!t u v. valid_posns ([u/v] t) =
              valid_posns t UNION
              {APPEND p1 p2 | p1 IN v_posns v t /\ p2 IN valid_posns u}``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `t` THEN
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][valid_posns_thm, v_posns_thm, SUB_THM] THENL [
    SIMP_TAC (srw_ss() ++ DNF_ss)[EXTENSION, EQ_IMP_THM],
    SRW_TAC [][EXTENSION] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    SRW_TAC [DNF_ss][] THEN PROVE_TAC [],
    SRW_TAC [DNF_ss][EXTENSION] THEN PROVE_TAC []
  ]);

val cant_be_deeper_than_var_posns = store_thm(
  "cant_be_deeper_than_var_posns",
  ``!t p1 p. p1 IN var_posns t /\ APPEND p1 p IN valid_posns t ==>
             (p = [])``,
  HO_MATCH_MP_TAC simple_induction THEN REPEAT CONJ_TAC THENL [
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
  ``!t v. [] IN v_posns v t <=> (t = VAR v)``,
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][v_posns_thm, v_posns_LAM_COND]);

val v_posns_FINITE = Store_Thm(
  "v_posns_FINITE",
  ``!v t. FINITE (v_posns v t)``,
  PROVE_TAC [v_posns_SUBSET_var_posns, var_posns_FINITE,
             pred_setTheory.SUBSET_FINITE, pred_setTheory.SUBSET_DEF]);

val _ = export_theory()

