(* Thoughts about how to define alpha equivalence for types with sets
of names as binders.  This is important for type schemas, where the
model is apparently that you can have sets of binders so that things
like

  \forall \alpha \beta. \alpha -> \beta

is the same thing as

  \forall \beta \alpha. \alpha -> \beta

not to mention \forall \alpha \beta. \beta -> \alpha
and even       \forall \alpha \beta \gamma. \beta -> \alpha

Christian Urban and I talked to Peter Homeier about this in September
2007, while in Munich, and PH suggested that we drop the idea of being
able to do this by an Andy Pitts style definition, and that we instead
define a relation that embodied some sort of constraint satisfaction
routine.  This seems plausible, but in an alpha-equivalence test on a
binary operator (a function space in the type example, say), the
relation would have to "return" an updated context of equality
bindings after having checked the match in one argument, so that this
updated context could be passed onto the next argument.  There would
also have to be stacks of pairs of sets, recording at which level
names had occurred.  All told there'd be far too many parameters.

I did try this approach, but it became rather gruesome.  The eventual,
successful approach instead is very much in the style of Andy Pitts'
original after all.
*)

open HolKernel boolLib Parse bossLib

open binderLib boolSimps BasicProvers

open nomsetTheory
open pred_setTheory

val _ = new_theory "type_schemas"

val _ = Hol_datatype`
  type = tyvar of string
       | tyfun of type => type
       | tyforall of string set => type
`;

val fv_def = Define`
  (fv (tyvar s) = {s}) /\
  (fv (tyfun ty1 ty2) = fv ty1 UNION fv ty2) /\
  (fv (tyforall vs ty) = fv ty DIFF vs)
`;
val _ = export_rewrites ["fv_def"]

val FINITE_fv = store_thm(
  "FINITE_fv",
  ``!ty. FINITE (fv ty)``,
  Induct THEN SRW_TAC [][pred_setTheory.FINITE_DIFF]);
val _ = export_rewrites ["FINITE_fv"]

val raw_rtypm_def = Define`
  (raw_rtypm pi (tyvar s) = tyvar (stringpm pi s)) /\
  (raw_rtypm pi (tyfun ty1 ty2) = tyfun (raw_rtypm pi ty1) (raw_rtypm pi ty2)) /\
  (raw_rtypm pi (tyforall vs ty) = tyforall (ssetpm pi vs) (raw_rtypm pi ty))
`;
val _ = export_rewrites["raw_rtypm_def"];

val _ = overload_on("rty_pmact", ``mk_pmact raw_rtypm``);
val _ = overload_on("rtypm", ``pmact rty_pmact``);

val rtypm_raw = store_thm(
  "rtypm_raw",
  ``rtypm = raw_rtypm``,
  SRW_TAC [][GSYM pmact_bijections] THEN
  SRW_TAC [][is_pmact_def] THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][pmact_decompose],
    FULL_SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN
    Induct THEN SRW_TAC [][] THEN
    METIS_TAC [pmact_permeq]
  ]);

val rtypm_thm = save_thm(
"rtypm_thm",
raw_rtypm_def |> SUBS [GSYM rtypm_raw]);
val _ = export_rewrites["rtypm_thm"];

val fv_rtypm = prove(
  ``fv (rtypm pi ty) = ssetpm pi (fv ty)``,
  Induct_on `ty` THEN SRW_TAC [][pmact_INSERT, pmact_UNION, pmact_DIFF]);

val okpm_def = Define`
  okpm pi bvs avds t ⇔
     (!s. s IN bvs /\ s IN fv t ==> ~(stringpm pi s IN avds)) /\
     (!s. ~(s IN bvs) /\ s IN fv t ==> (stringpm pi s = s))
`;

fun Prove(t,tac) = let val th = prove(t,tac)
                   in
                     BasicProvers.augment_srw_ss [rewrites [th]] ;
                     th
                   end

val (aeq_rules, aeq_ind, aeq_cases) = Hol_reln`
  (!s. aeq (tyvar s) (tyvar s)) /\
  (!a b t u. aeq a t /\ aeq b u ==> aeq (tyfun a b) (tyfun t u)) /\
  (!us vs t u pi1 pi2. okpm pi1 vs (fv t UNION fv u) t /\
                       okpm pi2 us (fv t UNION fv u) u /\
                       aeq (rtypm pi1 t) (rtypm pi2 u)
                     ==>
                       aeq (tyforall vs t) (tyforall us u))
`;

val aeq_forall = last (CONJUNCTS aeq_rules)

val aeq_example1 = prove(
  ``aeq (tyforall {x} (tyvar x)) (tyforall {y} (tyvar y))``,
  MATCH_MP_TAC aeq_forall THEN
  Q_TAC (NEW_TAC "z") `{x;y}` THEN
  MAP_EVERY Q.EXISTS_TAC [`[(x,z)]`, `[(y,z)]`] THEN
  SRW_TAC [][aeq_rules, okpm_def]);

val aeq_example2 = prove(
  ``aeq (tyforall {x} (tyvar x)) (tyforall {y} (tyvar a)) = (a = y)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][okpm_def] THEN
  SRW_TAC [][Once aeq_cases] THEN Cases_on `a = y` THEN SRW_TAC [][] THENL [
    Q_TAC (NEW_TAC "z") `{x;a}` THEN
    MAP_EVERY Q.EXISTS_TAC [`[(x, z)]`, `[(a, z)]`] THEN
    SRW_TAC [][],
    Cases_on `lswapstr pi2 a = a` THEN SRW_TAC [][] THEN
    Cases_on `lswapstr pi1 x = a` THEN SRW_TAC [][stringpm_raw]
  ]);

val aeq_example3 = prove(
  ``aeq (tyforall {x} (tyfun (tyvar x) (tyforall {x} (tyvar x))))
        (tyforall {a} (tyfun (tyvar a) (tyforall {c;d} (tyvar d))))``,
  MATCH_MP_TAC aeq_forall THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `{x;a}` THEN
  MAP_EVERY Q.EXISTS_TAC [`[(x, z)]`, `[(a, z)]`] THEN
  SRW_TAC [][Once aeq_cases, okpm_def] THEN
  SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC aeq_forall THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "q") `{swapstr a z d; z}` THEN
  MAP_EVERY Q.EXISTS_TAC [`[(z, q)]`, `[(swapstr a z d, q)]`] THEN
  SRW_TAC [][aeq_rules, okpm_def]);

val aeq_example4 = prove(
  ``~(a = c) ==> ~aeq (tyforall {x} (tyfun (tyvar x) (tyvar x)))
                      (tyforall {a;c} (tyfun (tyvar a) (tyvar c)))``,
  SRW_TAC [][Once aeq_cases] THEN SRW_TAC [][Once aeq_cases] THEN
  SRW_TAC [][Once aeq_cases] THEN SRW_TAC [][Once aeq_cases] THEN
  SRW_TAC [][okpm_def] THEN
  SRW_TAC [DNF_ss][] THEN
  METIS_TAC [pmact_injective]);

fun find_small_cond t = let
  fun recurse t k =
    case dest_term t of
      COMB(t1,t2) => if is_cond t then
                       recurse t1 (fn () => recurse t2 (fn () => t))
                     else
                       recurse t1 (fn () => recurse t2 k)
    | LAMB(_, bod) => recurse bod k
    | _ => k()
in
  recurse t (fn () => raise raise mk_HOL_ERR "type_schemas" "find_small_cond"
                                             "No cond in term")
end

fun mCOND_CASES_TAC (asl, g) = let
  val c = find_small_cond g
in
  ASM_CASES_TAC (hd (#2 (strip_comb c))) THEN ASM_SIMP_TAC (srw_ss()) []
end (asl, g)

val rtypm_cpmpm = (SIMP_RULE (srw_ss()) []  o
                   Q.INST [`pm` |-> `rty_pmact`] o
                   INST_TYPE [alpha |-> ``:type``])
                  pm_pm_cpmpm

val lswapstr_lswapstr_cpmpm = stringpm_stringpm_cpmpm

val rtypm_okpm = prove(
  ``okpm (cpmpm pi pi0)
             (setpm string_pmact pi bvs)
             (setpm string_pmact pi avds)
             (rtypm pi t) =
    okpm pi0 bvs avds t``,
  SRW_TAC [][okpm_def, fv_rtypm, pmact_IN, EQ_IMP_THM] THENL [
    FULL_SIMP_TAC (srw_ss()) [Once lswapstr_lswapstr_cpmpm,
                              pmact_inverse] THEN
    FIRST_ASSUM (Q.SPEC_THEN `lswapstr pi s`
                             (MATCH_MP_TAC o SIMP_RULE (srw_ss()) [])) THEN
    SRW_TAC [][],

    FIRST_X_ASSUM (Q.SPEC_THEN `lswapstr pi s` MP_TAC) THEN
    SRW_TAC [][pmact_eqr] THEN
    FULL_SIMP_TAC (srw_ss()) [Once lswapstr_lswapstr_cpmpm],

    FULL_SIMP_TAC (srw_ss()) [Once lswapstr_lswapstr_cpmpm],

    `lswapstr pi0 (lswapstr (REVERSE pi) s) = lswapstr (REVERSE pi) s`
       by SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC (srw_ss()) [pmact_eqr] THEN
    SRW_TAC [][Once lswapstr_lswapstr_cpmpm]
  ]);

val aeq_rtypm = prove(
  ``!t u. aeq t u ==> !pi. aeq (rtypm pi t) (rtypm pi u)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC (last (CONJUNCTS aeq_rules))  THEN
  MAP_EVERY Q.EXISTS_TAC [`cpmpm pi pi1`, `cpmpm pi pi2`] THEN
  ASM_SIMP_TAC bool_ss [rtypm_okpm, fv_rtypm, GSYM pmact_UNION] THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM rtypm_cpmpm]);


val INTER_INSERT = prove(
  ``s INTER (e INSERT t) = if e IN s then e INSERT (s INTER t)
                           else s INTER t``,
  SRW_TAC [][EXTENSION] THEN METIS_TAC []);

val avoid_finite_set0 = prove(
  ``!s1. FINITE s1 ==>
         FINITE ub /\ s1 SUBSET ub ==>
         ?pi. (!x. x IN ub /\ ~(x IN s1) ==> ~(x IN patoms pi)) /\
              (!x. x IN s2 /\ x IN s1 ==> ~(lswapstr pi x IN s1)) /\
              (!x. ~(x IN s2) /\ x IN s1 ==> (lswapstr pi x = x)) ``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [DNF_ss][] THEN1
    (Q.EXISTS_TAC `[]` THEN SRW_TAC [][]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `e IN s2` THENL [
    Q_TAC (NEW_TAC "z") `e INSERT (patoms pi) UNION ub` THEN
    Q.EXISTS_TAC `(z,e)::pi` THEN SRW_TAC [][] THENL [
      METIS_TAC [],
      SRW_TAC [][basic_swapTheory.swapstr_eq_left, pmact_eql,
                 listsupp_REVERSE, lswapstr_unchanged],

      SRW_TAC [][lswapstr_unchanged] THEN METIS_TAC [SUBSET_DEF],

      SRW_TAC [][basic_swapTheory.swapstr_eq_left] THEN
      SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN SRW_TAC [][] THEN
      `lswapstr pi x = x` by (
        IMP_RES_TAC lswapstr_unchanged THEN
        FULL_SIMP_TAC (srw_ss()) [] ) THEN
      FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
      METIS_TAC [],

      `~(e IN patoms pi)` by SRW_TAC [][] THEN
      `swapstr e z (lswapstr pi x) = lswapstr [(e,z)] (lswapstr pi x)`
         by SRW_TAC [][] THEN
      ` _ = lswapstr (cpmpm [(e,z)] pi) (lswapstr [(e,z)] x)`
         by METIS_TAC [lswapstr_lswapstr_cpmpm] THEN
      ` _ = lswapstr (cpmpm [(e,z)] pi) x`
         by METIS_TAC [basic_swapTheory.swapstr_def, SUBSET_DEF,
                       stringpm_thm, pairTheory.FST,
                       pairTheory.SND] THEN
      ` _ = lswapstr pi x` by SRW_TAC [][supp_fresh] THEN
      METIS_TAC [],
      METIS_TAC [SUBSET_DEF, basic_swapTheory.swapstr_def]
    ],
    Q.EXISTS_TAC `pi` THEN SRW_TAC [][] THENL [
      SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN SRW_TAC [][] THEN
      `lswapstr pi x NOTIN patoms (REVERSE pi)` by (
        RES_TAC THEN SRW_TAC [][listsupp_REVERSE] ) THEN
      IMP_RES_TAC lswapstr_unchanged THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN POP_ASSUM (ASSUME_TAC o SYM) THEN
      FULL_SIMP_TAC (srw_ss()) [],
      SRW_TAC [][lswapstr_unchanged]
    ]
  ]);

val avoid_finite_set =
  (SIMP_RULE (srw_ss()) [] (Q.SPEC `ub` avoid_finite_set0))

val aeq_refl = prove(
  ``!t. aeq t t``,
  Induct THEN SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q_TAC SUFF_TAC `?pi. okpm pi f (fv t) t`
        THEN1 METIS_TAC [UNION_IDEMPOT, aeq_rtypm] THEN
  SRW_TAC [][okpm_def] THEN
  METIS_TAC [FINITE_fv, avoid_finite_set]);

val aeq_fv = prove(
  ``!t1 t2. aeq t1 t2 ==> (fv t1 = fv t2)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][EXTENSION, fv_rtypm] THEN
  Cases_on `x IN vs` THEN SRW_TAC [][] THENL [
    Cases_on `x IN us` THEN SRW_TAC [][] THEN
    STRIP_TAC THEN
    `stringpm pi2 x = x` by METIS_TAC [okpm_def] THEN
    `stringpm (REVERSE pi2) x = x`
       by METIS_TAC [pmact_eql] THEN
    `stringpm (REVERSE pi1) x IN fv t` by METIS_TAC [] THEN
    Cases_on `stringpm (REVERSE pi1) x IN vs` THENL [
      `~(stringpm pi1 (stringpm (REVERSE pi1) x) IN fv u)`
         by PROVE_TAC [okpm_def, IN_UNION] THEN
      FULL_SIMP_TAC (srw_ss()) [],
      `stringpm pi1 (stringpm (REVERSE pi1) x) = stringpm (REVERSE pi1) x`
         by PROVE_TAC [okpm_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []
    ],
    Cases_on `x IN us` THEN SRW_TAC [][] THENL [
      STRIP_TAC THEN
      `stringpm pi1 x = x` by PROVE_TAC [okpm_def] THEN
      `stringpm (REVERSE pi1) x = x`
         by METIS_TAC [pmact_eql] THEN
      `stringpm (REVERSE pi2) x IN fv u` by METIS_TAC [] THEN
      Cases_on `stringpm (REVERSE pi2) x IN us` THEN
      PROVE_TAC [okpm_def, IN_UNION, pmact_inverse],

      Cases_on `x IN fv t` THENL [
        `stringpm pi1 x = x` by PROVE_TAC [okpm_def] THEN
        `stringpm (REVERSE pi1) x = x`
           by METIS_TAC [pmact_eql] THEN
        `stringpm (REVERSE pi2) x IN fv u` by METIS_TAC [] THEN
        Cases_on `stringpm (REVERSE pi2) x IN us` THEN
        PROVE_TAC [okpm_def, IN_UNION, pmact_inverse],

        SRW_TAC [][] THEN STRIP_TAC THEN
        `stringpm pi2 x = x` by PROVE_TAC [okpm_def] THEN
        `stringpm (REVERSE pi2) x = x`
           by METIS_TAC [pmact_eql] THEN
        `stringpm (REVERSE pi1) x IN fv t` by METIS_TAC [] THEN
        Cases_on `stringpm (REVERSE pi1) x IN vs` THEN
        PROVE_TAC [okpm_def, IN_UNION, pmact_inverse]
      ]
    ]
  ]);

val aeq_tyvar = prove(
  ``aeq (tyvar s) t = (t = tyvar s)``,
  ONCE_REWRITE_TAC [aeq_cases] THEN SRW_TAC [][]);

val aeq_tyfun = prove(
  ``aeq (tyfun ty1 ty2) ty = ?ty1' ty2'. (ty = tyfun ty1' ty2') /\
                                         aeq ty1 ty1' /\ aeq ty2 ty2'``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SRW_TAC [][]);


val aeq_sym = prove(
  ``!t1 t2. aeq t1 t2 ==> aeq t2 t1``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  MATCH_MP_TAC aeq_forall THEN METIS_TAC [UNION_COMM]);

val strong_aeq_ind = theorem "aeq_strongind"

val aeq_rtypm_eqn = prove(
  ``aeq (rtypm pi ty1) (rtypm pi ty2) = aeq ty1 ty2``,
  METIS_TAC [pmact_inverse, aeq_rtypm])

val okpm_exists = store_thm(
  "okpm_exists",
  ``!s. FINITE s ==> ?pi. okpm pi bvs s ty``,
  SIMP_TAC (srw_ss()) [okpm_def] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THENL [
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
    Cases_on `e IN fv ty` THENL [
      Cases_on `e IN bvs` THENL [
        Q_TAC (NEW_TAC "z") `patoms pi UNION fv ty UNION {e} UNION s` THEN
        Q.EXISTS_TAC `(z,e) :: pi` THEN SRW_TAC [][] THENL [
          SRW_TAC [][basic_swapTheory.swapstr_eq_left, pmact_eql] THEN
          SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN SRW_TAC [][] THEN
          METIS_TAC [lswapstr_unchanged,listsupp_REVERSE],
          SRW_TAC [][basic_swapTheory.swapstr_def],
          `~(z = s')` by METIS_TAC [] THEN
          `~(e = s')` by METIS_TAC [] THEN SRW_TAC [][]
        ],
        Q.EXISTS_TAC `pi` THEN SRW_TAC [][] THEN
        `stringpm pi e = e` by METIS_TAC [] THEN
        `stringpm (REVERSE pi) e = e` by METIS_TAC [pmact_eql] THEN
        SRW_TAC [][pmact_eql] THEN METIS_TAC []
      ],
      Q_TAC (NEW_TAC "z") `patoms pi UNION fv ty UNION {e} UNION s` THEN
      Q.EXISTS_TAC `(z,e) :: pi` THEN SRW_TAC [][] THENL [
        SRW_TAC [][basic_swapTheory.swapstr_eq_left, pmact_eql] THEN
        METIS_TAC [lswapstr_unchanged,listsupp_REVERSE,stringpm_raw],
        SRW_TAC [][basic_swapTheory.swapstr_def],
        `~(z = s')` by METIS_TAC [] THEN
        `~(e = s')` by METIS_TAC [] THEN SRW_TAC [][]
      ]
    ]
  ]);

val aeq_trans = prove(
  ``!t1 t2. aeq t1 t2 ==> !t3. aeq t2 t3 ==> aeq t1 t3``,
  HO_MATCH_MP_TAC strong_aeq_ind THEN SRW_TAC [][aeq_tyvar, aeq_tyfun] THEN
  POP_ASSUM MP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC aeq_forall THEN
  `!pi t3. aeq (rtypm pi (rtypm pi2 u)) (rtypm pi t3) ==>
           aeq (rtypm pi (rtypm pi1 t)) (rtypm pi t3)`
     by SRW_TAC [][aeq_rtypm_eqn] THEN
  POP_ASSUM (Q.SPECL_THEN [`pi`, `rtypm (REVERSE pi) t3`]
                          (ASSUME_TAC o GEN_ALL o
                           SIMP_RULE (srw_ss()) [pmact_inverse])) THEN
  `?pi. okpm pi us (fv t UNION fv u UNION fv u') u`
     by SRW_TAC [][okpm_exists] THEN

  MAP_EVERY Q.EXISTS_TAC [`pi ++ REVERSE pi2 ++ pi1`,
                          `pi ++ REVERSE pi1' ++ pi2'`] THEN
  FULL_SIMP_TAC (srw_ss()) [pmact_decompose] THEN
  SRW_TAC [][okpm_def, pmact_decompose] THENL [
    `~(stringpm pi1 s IN fv t) /\ ~(stringpm pi1 s IN fv u)`
       by FULL_SIMP_TAC (srw_ss()) [okpm_def] THEN
    `stringpm pi1 s IN fv (rtypm pi1 t)` by SRW_TAC [][fv_rtypm] THEN
    `fv (rtypm pi1 t) = fv (rtypm pi2 u)` by METIS_TAC [aeq_fv] THEN
    `stringpm pi1 s IN fv (rtypm pi2 u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi2) (stringpm pi1 s) IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `stringpm (REVERSE pi2) (stringpm pi1 s) IN us`
       by (SPOSE_NOT_THEN ASSUME_TAC THEN
           `stringpm (REVERSE pi2) (stringpm pi1 s) =
            stringpm pi2 (stringpm (REVERSE pi2) (stringpm pi1 s))`
              by METIS_TAC [okpm_def] THEN
           ` _ = stringpm pi1 s` by SRW_TAC [][pmact_inverse] THEN
           METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    `~(stringpm pi1 s IN fv t) /\ ~(stringpm pi1 s IN fv u)`
       by FULL_SIMP_TAC (srw_ss()) [okpm_def] THEN
    `stringpm pi1 s IN fv (rtypm pi1 t)` by SRW_TAC [][fv_rtypm] THEN
    `fv (rtypm pi1 t) = fv (rtypm pi2 u)` by METIS_TAC [aeq_fv] THEN
    `stringpm pi1 s IN fv (rtypm pi2 u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi2) (stringpm pi1 s) IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `stringpm (REVERSE pi2) (stringpm pi1 s) IN us`
       by (SPOSE_NOT_THEN ASSUME_TAC THEN
           `stringpm (REVERSE pi2) (stringpm pi1 s) =
            stringpm pi2 (stringpm (REVERSE pi2) (stringpm pi1 s))`
              by METIS_TAC [okpm_def] THEN
           ` _ = stringpm pi1 s` by SRW_TAC [][pmact_inverse] THEN
           METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    `stringpm pi1 s = s` by METIS_TAC [okpm_def] THEN
    SRW_TAC [][] THEN
    `s IN fv (rtypm pi1 t)` by (SRW_TAC [][fv_rtypm] THEN
                                METIS_TAC [pmact_eql]) THEN
    `fv (rtypm pi1 t) = fv (rtypm pi2 u)` by METIS_TAC [aeq_fv] THEN
    `s IN fv (rtypm pi2 u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi2) s IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `~(stringpm (REVERSE pi2) s IN us)`
       by (STRIP_TAC THEN
           `~(stringpm pi2 (stringpm (REVERSE pi2) s) IN fv t)`
              by METIS_TAC [okpm_def, IN_UNION] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    `stringpm pi2 (stringpm (REVERSE pi2) s) = stringpm (REVERSE pi2) s`
       by METIS_TAC [okpm_def] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM (ASSUME_TAC o SYM) THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    `~(stringpm pi2' s IN fv u) /\ ~(stringpm pi2' s IN fv u')`
       by FULL_SIMP_TAC (srw_ss()) [okpm_def] THEN
    `stringpm pi2' s IN fv (rtypm pi2' u')` by SRW_TAC [][fv_rtypm] THEN
    `fv (rtypm pi1' u) = fv (rtypm pi2' u')` by METIS_TAC [aeq_fv] THEN
    `stringpm pi2' s IN fv (rtypm pi1' u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi1') (stringpm pi2' s) IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `stringpm (REVERSE pi1') (stringpm pi2' s) IN us`
       by (SPOSE_NOT_THEN ASSUME_TAC THEN
           `stringpm (REVERSE pi1') (stringpm pi2' s) =
            stringpm pi1' (stringpm (REVERSE pi1') (stringpm pi2' s))`
              by METIS_TAC [okpm_def] THEN
           ` _ = stringpm pi2' s` by SRW_TAC [][] THEN
           METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    `~(stringpm pi2' s IN fv u) /\ ~(stringpm pi2' s IN fv u')`
       by FULL_SIMP_TAC (srw_ss()) [okpm_def] THEN
    `stringpm pi2' s IN fv (rtypm pi2' u')` by SRW_TAC [][fv_rtypm] THEN
    `fv (rtypm pi1' u) = fv (rtypm pi2' u')` by METIS_TAC [aeq_fv] THEN
    `stringpm pi2' s IN fv (rtypm pi1' u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi1') (stringpm pi2' s) IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `stringpm (REVERSE pi1') (stringpm pi2' s) IN us`
       by (SPOSE_NOT_THEN ASSUME_TAC THEN
           `stringpm (REVERSE pi1') (stringpm pi2' s) =
            stringpm pi1' (stringpm (REVERSE pi1') (stringpm pi2' s))`
              by METIS_TAC [okpm_def] THEN
           ` _ = stringpm pi2' s` by SRW_TAC [][] THEN
           METIS_TAC []) THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    `stringpm pi2' s = s` by METIS_TAC [okpm_def] THEN
    SRW_TAC [][] THEN
    `s IN fv (rtypm pi2' u')` by (SRW_TAC [][fv_rtypm] THEN
                                  METIS_TAC [pmact_eql]) THEN
    `fv (rtypm pi1' u) = fv (rtypm pi2' u')` by METIS_TAC [aeq_fv] THEN
    `s IN fv (rtypm pi1' u)` by METIS_TAC [] THEN
    `stringpm (REVERSE pi1') s IN fv u`
       by FULL_SIMP_TAC (srw_ss()) [fv_rtypm] THEN
    `~(stringpm (REVERSE pi1') s IN us)`
       by (STRIP_TAC THEN
           `~(stringpm pi1' (stringpm (REVERSE pi1') s) IN fv u')`
              by METIS_TAC [okpm_def, IN_UNION] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    `stringpm pi1' (stringpm (REVERSE pi1') s) = stringpm (REVERSE pi1') s`
       by METIS_TAC [okpm_def] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM (ASSUME_TAC o SYM) THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    FULL_SIMP_TAC (srw_ss()) [okpm_def],

    Q_TAC SUFF_TAC `aeq (rtypm (pi ++ REVERSE pi2) (rtypm pi1 t))
                        (rtypm (pi ++ REVERSE pi1') (rtypm pi2' u'))`
          THEN1 SRW_TAC [][pmact_decompose] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SRW_TAC [][pmact_decompose, pmact_inverse] THEN
    SRW_TAC [][aeq_rtypm_eqn] THEN
    METIS_TAC [aeq_rtypm_eqn, pmact_inverse]
  ]);

val aeq_equiv = prove(
  ``!t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)``,
  SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC [aeq_trans, aeq_refl, aeq_sym]);

val forall_respects_aeq = prove(
  ``!vs t1 t2. aeq t1 t2 ==> aeq (tyforall vs t1) (tyforall vs t2)``,
  SRW_TAC [][] THEN MATCH_MP_TAC aeq_forall THEN
  `fv t1 = fv t2` by METIS_TAC [aeq_fv] THEN
  SRW_TAC [][okpm_def] THEN
  METIS_TAC [avoid_finite_set, FINITE_fv, aeq_rtypm]);

val tyfun_respects_aeq = List.nth(CONJUNCTS aeq_rules, 1)
fun mk_def (n,t) = {def_name = n ^ "_def", fname = n, func = t, fixity = NONE}

val okpm_respects = prove(
  ``!t1 t2. aeq t1 t2 ==> (okpm pi vs avoids t1 =
                           okpm pi vs avoids t2)``,
  SRW_TAC [][okpm_def] THEN METIS_TAC [aeq_fv]);

val liftrule = quotientLib.define_quotient_types_std_rule {
  types = [{name = "tyschema", equiv = aeq_equiv}],
  defs = [mk_def ("raw_tyspm", ``raw_rtypm``),
          mk_def ("tysFV", ``fv``),
          mk_def ("TYALL", ``tyforall``),
          mk_def ("TYFUN", ``tyfun``),
          mk_def ("TYV", ``tyvar``),
          mk_def ("OKpm", ``okpm``)],
  respects = [SIMP_RULE (bool_ss ++ DNF_ss) [rtypm_raw] aeq_rtypm,
              forall_respects_aeq, tyfun_respects_aeq,
              aeq_fv, okpm_respects]}

fun Save_thm(s,th) = save_thm(s,th) before export_rewrites [s]
fun Store_thm(s,t,tac) = store_thm(s,t,tac) before export_rewrites [s]
val tysFV_thm = Save_thm("tysFV_thm", liftrule fv_def)
val tysFV_FINITE = Save_thm("tysFV_FINITE", liftrule FINITE_fv)
val is_pmact_raw_tyspm = is_pmact_pmact |> Q.ISPEC `rty_pmact`
                         |> REWRITE_RULE [rtypm_raw,is_pmact_def] |> liftrule
val _ = overload_on("tys_pmact",``mk_pmact raw_tyspm``);
val _ = overload_on("tyspm",``pmact tys_pmact``);
val tyspm_raw = store_thm("tyspm_raw",``tyspm = raw_tyspm``,
  SRW_TAC [][GSYM pmact_bijections,is_pmact_def,is_pmact_raw_tyspm])
fun liftrule' th = th |> SUBS [rtypm_raw] |> liftrule |> SUBS [GSYM tyspm_raw]
val tyspm_thm = Save_thm("tyspm_thm", liftrule' rtypm_thm)
val tys_ind = save_thm("tys_ind", liftrule (TypeBase.induction_of ``:type``))
val OKpm_thm = save_thm("OKpm_thm", liftrule okpm_def)
val OKpm_eqvt = save_thm("OKpm_eqvt", liftrule' rtypm_okpm)
val tysFV_tyspm = save_thm("tysFV_tyspm", liftrule' fv_rtypm)
val tyseq_rule = liftrule' aeq_rules

val OKpm_exists = save_thm("OKpm_exists", liftrule okpm_exists)

val OKpm_increase = store_thm(
  "OKpm_increase",
  ``s1 SUBSET s2 /\ OKpm pi bvs s2 ty ==> OKpm pi bvs s1 ty``,
  SRW_TAC [][OKpm_thm] THEN METIS_TAC [SUBSET_DEF]);

val OKpm_avoids = prove(
  ``!Set. FINITE Set  ==>
          DISJOINT Set (tysFV ty) ==>
          ?pi. DISJOINT (patoms pi) Set /\ OKpm pi bvs (tysFV ty) ty``,
  SIMP_TAC (srw_ss()) [OKpm_thm] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THENL [
    SRW_TAC [][avoid_finite_set],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    Cases_on `e IN patoms pi` THENL [
      Q_TAC (NEW_TAC "z") `patoms pi UNION tysFV ty UNION {e} UNION Set` THEN
      Q.EXISTS_TAC `cpmpm [(z,e)] pi` THEN
      SRW_TAC [][patoms_cpmpm] THENL [
        SRW_TAC [][DISJOINT_DEF, EXTENSION] THEN
        Cases_on `x IN Set` THEN SRW_TAC [][] THEN
        `~(e = x) /\ ~(z = x)` by METIS_TAC [] THEN
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
        METIS_TAC [],
        `stringpm (cpmpm [(z,e)] pi) s = stringpm [(z,e)] (stringpm pi s)`
           by (ONCE_REWRITE_TAC [stringpm_stringpm_cpmpm] THEN
               `~(e = s) /\ ~(z = s)` by METIS_TAC [] THEN
               SRW_TAC [][]) THEN
        SRW_TAC [][] THEN SRW_TAC [][basic_swapTheory.swapstr_def],
        `~(e = s) /\ ~(z = s)` by METIS_TAC [] THEN
        `stringpm (cpmpm [(z,e)] pi) s = stringpm [(z,e)] (stringpm pi s)`
           by (ONCE_REWRITE_TAC [stringpm_stringpm_cpmpm] THEN
               `~(e = s) /\ ~(z = s)` by METIS_TAC [] THEN
               SRW_TAC [][]) THEN
        SRW_TAC [][]
      ],
      Q.EXISTS_TAC `pi` THEN SRW_TAC [][]
    ]
  ]);

val tys_fresh = store_thm(
  "tys_fresh",
  ``!ty a b. ~(a IN tysFV ty) /\ ~(b IN tysFV ty) ==> (tyspm [(a,b)] ty = ty)``,
  HO_MATCH_MP_TAC tys_ind THEN SRW_TAC [][] THENL [
    SRW_TAC [][] THEN MATCH_MP_TAC (last (CONJUNCTS tyseq_rule)) THEN
    SRW_TAC [][] THEN
    `setpm string_pmact [(a,b)] (tysFV ty) = tysFV ty`
       by SRW_TAC [][GSYM tysFV_tyspm] THEN
    `DISJOINT {a;b} (tysFV ty)` by SRW_TAC [][DISJOINT_DEF, EXTENSION] THEN
    `?pi. DISJOINT (patoms pi) {a;b} /\ OKpm pi f (tysFV ty) ty `
       by SRW_TAC [][OKpm_avoids] THEN
    `~(a IN patoms pi) /\ ~(b IN patoms pi)`
       by (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
           METIS_TAC []) THEN
    `cpmpm [(a,b)] pi = pi`
       by (MATCH_MP_TAC supp_fresh THEN SRW_TAC [][]) THEN
    METIS_TAC [OKpm_eqvt],

    MATCH_MP_TAC (last (CONJUNCTS tyseq_rule)) THEN
    `FINITE (tysFV (tyspm [(a,b)] ty) UNION tysFV ty)` by SRW_TAC [][] THEN
    `?pi. OKpm pi f (tysFV (tyspm [(a,b)] ty) UNION tysFV ty) ty`
        by METIS_TAC [OKpm_exists] THEN
    MAP_EVERY Q.EXISTS_TAC [`pi ++ [(a,b)]`, `pi`] THEN SRW_TAC [][] THENL [
      SRW_TAC [][OKpm_thm, tysFV_tyspm] THENL [
        SRW_TAC [][pmact_decompose] THEN
        `~(stringpm pi (swapstr a b s) IN tysFV (tyspm [(a,b)] ty))`
           by FULL_SIMP_TAC (srw_ss()) [OKpm_thm] THEN
        FULL_SIMP_TAC (srw_ss()) [tysFV_tyspm],

        SRW_TAC [][pmact_decompose] THEN
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm],

        SRW_TAC [][pmact_decompose] THEN
        `~(s = a)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        `~(s = b)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm]
      ],
      SRW_TAC [][pmact_decompose, pmact_sing_inv]
    ],

    MATCH_MP_TAC (last (CONJUNCTS tyseq_rule)) THEN
    `FINITE (tysFV (tyspm [(a,b)] ty) UNION tysFV ty)` by SRW_TAC [][] THEN
    `?pi. OKpm pi f (tysFV (tyspm [(a,b)] ty) UNION tysFV ty) ty`
        by METIS_TAC [OKpm_exists] THEN
    MAP_EVERY Q.EXISTS_TAC [`pi ++ [(a,b)]`, `pi`] THEN SRW_TAC [][] THENL [
      SRW_TAC [][OKpm_thm, tysFV_tyspm] THENL [
        SRW_TAC [][pmact_decompose] THEN
        `~(stringpm pi (swapstr a b s) IN tysFV (tyspm [(a,b)] ty))`
           by FULL_SIMP_TAC (srw_ss()) [OKpm_thm] THEN
        FULL_SIMP_TAC (srw_ss()) [tysFV_tyspm],

        SRW_TAC [][pmact_decompose] THEN
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm],

        SRW_TAC [][pmact_decompose] THEN
        `~(s = a)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        `~(s = b)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm]
      ],
      SRW_TAC [][pmact_decompose]
    ],

    MATCH_MP_TAC (last (CONJUNCTS tyseq_rule)) THEN
    `FINITE (tysFV (tyspm [(a,b)] ty) UNION tysFV ty)` by SRW_TAC [][] THEN
    `?pi. OKpm pi f (tysFV (tyspm [(a,b)] ty) UNION tysFV ty) ty`
        by METIS_TAC [OKpm_exists] THEN
    MAP_EVERY Q.EXISTS_TAC [`pi ++ [(a,b)]`, `pi`] THEN
    SRW_TAC [][] THENL [
      SRW_TAC [][OKpm_thm, tysFV_tyspm, pmact_decompose] THENL [
        `~(stringpm pi (swapstr a b s) IN tysFV (tyspm [(a,b)] ty))`
           by FULL_SIMP_TAC (srw_ss()) [OKpm_thm] THEN
        FULL_SIMP_TAC (srw_ss()) [tysFV_tyspm, pmact_decompose],
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm],
        `~(a = s)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        `~(b = s)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
        FULL_SIMP_TAC (srw_ss()) [OKpm_thm]
      ],
      SRW_TAC [][pmact_decompose]
    ]
  ]);

val _ = export_theory ();
