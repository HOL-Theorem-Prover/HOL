open HolKernel basicHol90Lib Parse

open SingleStep mesonLib

local open listTheory optionTheory pairTheory in end;

infix THEN THENL THENC ++
infix 8 by

open simpLib boolSimps

val UNCURRY_THM = prove(
  ``!p f. UNCURRY f p = f (FST p) (SND p)``,
  REPEAT GEN_TAC THEN Cases_on `p` THEN
  SIMP_TAC bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND]);

val hol_ss = bool_ss ++ optionSimps.OPTION_ss ++ listSimps.list_ss ++
                        arithSimps.ARITH_ss ++ arithSimps.REDUCE_ss ++
                        pairSimps.PAIR_ss ++ rewrites [UNCURRY_THM] ++
                        combinSimps.COMBIN_ss

val PAIR_EQ = pairTheory.PAIR_EQ
val ELIM1_TAC =
  let fun apply thm =
        let fun chkeq thm =
              let val con = concl thm
              in
                  is_var (lhs con) andalso not (free_in (lhs con) (rhs con))
              end
            fun check thm =
              let val con = concl thm in
                if (is_eq con) then
                  if (chkeq thm) then ([thm],[]) else
                  if (chkeq (SYM thm)) then ([SYM thm], []) else
                  if (is_pair (lhs con) andalso is_pair (rhs con)) then
                    let val conjs = CONJUNCTS (REWRITE_RULE [PAIR_EQ] thm)
                        val (ys,ns) = unzip (map check conjs)
                    in
                        (flatten ys, flatten ns)
                    end else ([], [thm])
                else
                   if (is_var con) then ([EQT_INTRO thm], []) else
                   if (is_neg con) andalso (is_var (dest_neg con)) then
                      ([EQF_INTRO thm], [])
                   else ([], [thm])
              end
            val (usables, to_assume) = check thm
            val con = concl thm
        in
            if (null usables) andalso (length to_assume = 1) then NO_TAC
            else
               UNDISCH_TAC con THEN DISCH_THEN (K ALL_TAC) THEN
               MAP_EVERY ASSUME_TAC to_assume THEN
               MAP_EVERY SUBST_ALL_TAC usables
         end
      fun elim_refl thm =
        let val con = concl thm
        in
            if (is_eq con andalso (rhs con) = (lhs con)) orelse
               (con = concl TRUTH) then
               UNDISCH_TAC con THEN DISCH_THEN (K ALL_TAC)
            else
               NO_TAC
        end
  in
      TRY (FIRST_ASSUM apply) THEN TRY (FIRST_ASSUM elim_refl)
  end
val ELIM_TAC = REPEAT (CHANGED_TAC ELIM1_TAC);


val _ = new_theory "llist";

(* representing type is :'a list -> 'a option *)

val lrep_take = Rsyntax.new_recursive_definition {
  rec_axiom = prim_recTheory.num_Axiom,
  def = ``(lrep_take f 0 = SOME []) /\
          (lrep_take f (SUC n) =
             option_case
                NONE
                (\pfx. option_case NONE (\a. SOME (APPEND pfx [a])) (f pfx))
                (lrep_take f n))``,
  name = "lrep_take"};

val lrep_ok = new_definition(
  "lrep_ok",
  ``lrep_ok f = !l x. (f l = SOME x) ==> (?n. lrep_take f n = SOME l)``);

val type_inhabited = prove(
  ``?f. lrep_ok f``,
  Q.EXISTS_TAC `\x. NONE` THEN
  SIMP_TAC bool_ss [lrep_ok, optionTheory.NOT_NONE_SOME]);

val llist_tydef = new_type_definition{
  name = "llist",
  pred = ``lrep_ok``,
  inhab_thm = type_inhabited};

val repabs_fns = define_new_type_bijections {
  name = "llist_absrep",
  ABS = "llist_abs",
  REP = "llist_rep",
  tyax = llist_tydef};

val llist_absrep = CONJUNCT1 repabs_fns
val llist_repabs = CONJUNCT2 repabs_fns

val lnil_rep = new_definition(
  "lnil_rep",
  ``lnil_rep = \l. NONE``);

val LNIL = new_definition(
  "LNIL",
  ``LNIL = llist_abs lnil_rep``);

val ldest_rep = new_definition(
  "ldest_rep",
  ``ldest_rep (f:'a list -> 'a option) =
      option_case NONE (\x. SOME (x, \l. f (x::l))) (f [])``);

val LDEST = new_definition(
  "LDEST",
  ``LDEST ll =
      option_case NONE (\p. SOME (FST p, llist_abs (SND p)))
                  (ldest_rep (llist_rep ll))``);

val LHD = new_definition(
  "LHD",
  ``LHD ll = option_APPLY FST (ldest_rep (llist_rep ll))``);

val LTL = new_definition(
  "LTL",
  ``LTL ll = option_APPLY (llist_abs o SND) (ldest_rep (llist_rep ll))``);

val lcons_rep = new_definition(
  "lcons_rep",
  ``lcons_rep h t = \l. if l = [] then SOME h
                        else if HD l = h then t (TL l) else NONE``);

val LCONS = new_definition(
  "LCONS",
  ``LCONS h t = llist_abs (lcons_rep h (llist_rep t))``);

val lbuildn_rep = Rsyntax.new_recursive_definition {
  name = "lbuildn_rep",
  rec_axiom = prim_recTheory.num_Axiom,
  def = ``(lbuildn_rep (f:'a -> ('a # 'b) option) x 0 = SOME ([], x)) /\
          (lbuildn_rep f x (SUC n) =
             option_case
                 NONE
                 (\(pfx,x').
                     option_case
                       NONE
                       (\(x'',last). SOME (APPEND pfx [last], x''))
                       (f x'))
                 (lbuildn_rep f x n))``};

val lbuild_rep = new_definition(
  "lbuild_rep",
  ``lbuild_rep (f:'a -> ('a # 'b) option) x =
       \pfx.
         option_case
           NONE
           (\ (pfx', nthseed).
               if pfx' = pfx then option_APPLY SND (f nthseed)
               else NONE)
           (lbuildn_rep f x (LENGTH pfx))``);

val lrep_take_SOME_NIL = prove(
  ``!n f. (lrep_take f n = SOME []) = (n = 0)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    Cases_on `n` THEN SIMP_TAC hol_ss [lrep_take] THEN
    SIMP_TAC (hol_ss ++ COND_elim_ss) [optionTheory.option_case_compute],
    SIMP_TAC bool_ss [lrep_take]
  ]);

val lrep_take_LENGTH = prove(
  ``!f n l. (lrep_take f n = SOME l) ==> (LENGTH l = n)``,
  GEN_TAC THEN numLib.INDUCT_TAC THENL [
    SIMP_TAC hol_ss [lrep_take],
    SIMP_TAC hol_ss [lrep_take] THEN
    Cases_on `lrep_take f n` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `f x` THEN ASM_SIMP_TAC hol_ss []
  ]);

val lbuildn_LENGTH = prove(
  ``!n f x pfx y.
       (lbuildn_rep f x n = SOME (pfx, y)) ==>
       (LENGTH pfx = n)``,
  Induct THEN SIMP_TAC hol_ss [lbuildn_rep] THEN
  REPEAT GEN_TAC THEN Cases_on `lbuildn_rep f x n` THEN SIMP_TAC hol_ss [] THEN
  Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
  Cases_on `f r` THEN SIMP_TAC hol_ss [] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN
  ASM_SIMP_TAC hol_ss [arithmeticTheory.ADD_CLAUSES] THEN
  ASM_MESON_TAC []);

val lbuildn_rep_predecessors = prove(
  ``!n f x pfx y.
      (lbuildn_rep f x (SUC n) = SOME(pfx, y)) ==>
      ?front last lastseed.
         (pfx = APPEND front [last]) /\
         (lbuildn_rep f x n = SOME(front, lastseed)) /\
         (f lastseed = SOME(y, last))``,
  Induct THENL [
    SIMP_TAC hol_ss [lbuildn_rep] THEN
    REPEAT GEN_TAC THEN Cases_on `f x` THEN SIMP_TAC hol_ss [] THEN
    STRIP_TAC THEN ELIM_TAC THEN SIMP_TAC hol_ss [],
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [lbuildn_rep] THEN
    Cases_on `lbuildn_rep f x (SUC n)` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN RES_TAC THEN
    Cases_on `f r` THEN SIMP_TAC hol_ss [] THEN STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`q`, `SND x'`, `r`] THEN
    ELIM_TAC THEN ASM_SIMP_TAC hol_ss []
  ]);

val lbuildn_rep_tl = prove(
  ``!n f x.
      lbuildn_rep f x (SUC n) =
      option_case
        NONE
        (\ (y, h). option_case
                      NONE
                      (\ (t,z). SOME (h::t, z))
                      (lbuildn_rep f y n))
        (f x)``,
  Induct THENL [
    SIMP_TAC hol_ss [lbuildn_rep],
    ONCE_REWRITE_TAC [lbuildn_rep] THEN
    POP_ASSUM (fn th => SIMP_TAC hol_ss [th]) THEN REPEAT GEN_TAC THEN
    Cases_on `f x` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `lbuildn_rep f q n` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `f r'` THEN SIMP_TAC hol_ss []
  ]);

val lbuild_rep_CONS = prove(
  ``!f x h t y.
       (lbuild_rep f x (h::t) = SOME y) ==>
       ?front last.
          (h::t = APPEND front [last]) /\
          (LENGTH front = LENGTH t) /\
          (lbuild_rep f x front = SOME last)``,
  SIMP_TAC hol_ss [lbuild_rep] THEN REPEAT GEN_TAC THEN
  Cases_on `lbuildn_rep f x (SUC (LENGTH t))` THEN SIMP_TAC hol_ss [] THEN
  Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
  Cases_on `f r` THEN SIMP_TAC hol_ss [] THEN
  STRIP_TAC THEN
  Q.SUBGOAL_THEN `q = h::t` (fn th => FULL_SIMP_TAC hol_ss [th]) THENL [
    SPOSE_NOT_THEN ASSUME_TAC THEN FULL_SIMP_TAC hol_ss [],
    ALL_TAC
  ] THEN IMP_RES_TAC lbuildn_rep_predecessors THEN
  MAP_EVERY Q.EXISTS_TAC [`front`, `last`] THEN
  ASM_SIMP_TAC hol_ss [] THEN
  IMP_RES_TAC lbuildn_LENGTH THEN
  ASM_SIMP_TAC hol_ss []);

val lbuild_rep_ok = prove(
  ``!f x. lrep_ok (lbuild_rep f x)``,
  SIMP_TAC bool_ss [lrep_ok] THEN
  REPEAT GEN_TAC THEN
  Q.ABBREV_TAC `n = LENGTH l` THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`f`, `x`, `x'`, `l`, `n`] THEN
  numLib.INDUCT_TAC THENL [
    SIMP_TAC hol_ss [listTheory.LENGTH_NIL] THEN MESON_TAC [lrep_take],
    SIMP_TAC hol_ss [listTheory.LENGTH_CONS] THEN
    CONV_TAC (REDEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC lbuild_rep_CONS THEN ELIM_TAC THEN
    `?m. lrep_take (lbuild_rep f x) m = SOME front`
       by ASM_MESON_TAC [] THEN
    Q.EXISTS_TAC `SUC m` THEN ASM_SIMP_TAC hol_ss [lrep_take]
  ]);

val repabs_build = prove(
  ``!f x. llist_rep (llist_abs (lbuild_rep f x)) = lbuild_rep f x``,
  SIMP_TAC hol_ss [GSYM llist_repabs, lbuild_rep_ok]);

val lrep_take_tl = prove(
  ``!n f.
      lrep_take f (SUC n) =
      option_case
        NONE
        (\(h,ltl).
           option_case NONE (\t. SOME (h::t)) (lrep_take ltl n))
        (ldest_rep f)``,
  Induct THENL [
    SIMP_TAC hol_ss [lrep_take, ldest_rep] THEN GEN_TAC THEN
    Cases_on `f []` THEN SIMP_TAC hol_ss [],
    GEN_TAC THEN ONCE_REWRITE_TAC [lrep_take] THEN
    POP_ASSUM (fn th => SIMP_TAC hol_ss [ldest_rep, th]) THEN
    Cases_on `f []` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `lrep_take (\l. f (x::l)) n` THEN SIMP_TAC hol_ss [] THEN
    Cases_on `f (x::x')` THEN SIMP_TAC hol_ss []
  ]);

val LCONS_ok = prove(
  ``!h t. lrep_ok t ==> lrep_ok (lcons_rep h t)``,
  SIMP_TAC hol_ss [lcons_rep, lrep_ok] THEN REPEAT STRIP_TAC THEN
  Cases_on `l` THENL [
    Q.EXISTS_TAC `0` THEN SIMP_TAC hol_ss [lrep_take],
    FULL_SIMP_TAC hol_ss [] THEN
    Cases_on `h = h'` THEN FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN
    RES_TAC THEN Q.EXISTS_TAC `SUC n` THEN
    ASM_SIMP_TAC hol_ss [lrep_take_tl, ldest_rep]
  ]);

val lcons_repabs = prove(
  ``!h t. llist_rep (llist_abs (lcons_rep h (llist_rep t))) =
          lcons_rep h (llist_rep t)``,
  SIMP_TAC hol_ss [GSYM llist_repabs] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC LCONS_ok THEN
  SIMP_TAC hol_ss [llist_repabs, llist_absrep]);

val LHDTL_CONS_THM = store_thm(
  "LHDTL_CONS_THM",
  ``!h t. (LHD (LCONS h t) = SOME h) /\ (LTL (LCONS h t) = SOME t)``,
  REPEAT STRIP_TAC THEN SIMP_TAC hol_ss [LHD, LCONS, lcons_repabs, LTL] THEN
  SIMP_TAC hol_ss [lcons_rep, ldest_rep, llist_absrep]);

val lrep_ltl = prove(
  ``!h t. lrep_ok t ==> lrep_ok (\sfx. t (h::sfx))``,
  SIMP_TAC hol_ss [lrep_ok] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN IMP_RES_TAC lrep_take_LENGTH THEN
  FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN
  FULL_SIMP_TAC hol_ss [lrep_take_tl] THEN
  Cases_on `ldest_rep t` THEN FULL_SIMP_TAC hol_ss [] THEN
  Cases_on `x'` THEN FULL_SIMP_TAC hol_ss [] THEN
  Cases_on `lrep_take r (LENGTH l)` THEN FULL_SIMP_TAC hol_ss [] THEN
  ELIM_TAC THEN FULL_SIMP_TAC hol_ss [ldest_rep] THEN
  Cases_on `t []` THEN FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN
  Q.EXISTS_TAC `LENGTH l` THEN ASM_SIMP_TAC hol_ss []);

val llist_CASES = store_thm(
  "llist_CASES",
  ``!l. (l = LNIL) \/ (?h t. l = LCONS h t)``,
  GEN_TAC THEN Cases_on `llist_rep l []` THENL [
    DISJ1_TAC THEN SIMP_TAC hol_ss [LNIL, lnil_rep] THEN
    Q.SUBGOAL_THEN `lrep_ok (llist_rep l)` ASSUME_TAC THENL [
      SIMP_TAC hol_ss [llist_absrep, llist_repabs],
      ALL_TAC
    ] THEN CONV_TAC (LHS_CONV (REWR_CONV (GSYM llist_absrep))) THEN
    AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
    SIMP_TAC hol_ss [] THEN Q.ABBREV_TAC `f = llist_rep l` THEN
    Cases_on `l'` THENL [
      ASM_SIMP_TAC hol_ss [],
      Cases_on `f (h::t)` THENL [
        REFL_TAC,
        `?n. lrep_take f n = SOME (h::t)` by ASM_MESON_TAC [lrep_ok] THEN
        Cases_on `n` THENL [
          FULL_SIMP_TAC hol_ss [lrep_take],
          FULL_SIMP_TAC hol_ss [lrep_take_tl, ldest_rep] THEN
          Q.PAT_ASSUM `f [] = NONE` (fn th => FULL_SIMP_TAC hol_ss [th])
        ]
      ]
    ],
    DISJ2_TAC THEN SIMP_TAC hol_ss [LCONS, lcons_rep] THEN
    MAP_EVERY Q.EXISTS_TAC [`THE (LHD l)`, `THE (LTL l)`] THEN
    SIMP_TAC hol_ss [LHD, LTL] THEN
    CONV_TAC (LHS_CONV (REWR_CONV (GSYM llist_absrep))) THEN
    AP_TERM_TAC THEN Q.ABBREV_TAC `f = llist_rep l` THEN
    CONV_TAC (Q.X_FUN_EQ_CONV `pfx`) THEN GEN_TAC THEN
    ASM_SIMP_TAC hol_ss [ldest_rep] THEN
    Cases_on `pfx` THENL [
      ASM_SIMP_TAC hol_ss [],
      SIMP_TAC hol_ss [] THEN
      Q.SUBGOAL_THEN `lrep_ok f` ASSUME_TAC THENL [
        ELIM_TAC THEN SIMP_TAC hol_ss [llist_repabs, llist_absrep],
        ALL_TAC
      ] THEN
      COND_CASES_TAC THENL [
        Q.SUBGOAL_THEN `llist_rep (llist_abs (\l. f (x::l))) =
                        \l. f (x::l)`
        (fn th => ASM_SIMP_TAC hol_ss [th]) THEN
        ASM_SIMP_TAC hol_ss [GSYM llist_repabs, lrep_ltl],
        Cases_on `f (h::t)` THENL [REFL_TAC, ALL_TAC] THEN
        `?n. lrep_take f n = SOME (h::t)` by ASM_MESON_TAC [lrep_ok] THEN
        `n = LENGTH (h::t)` by ASM_MESON_TAC [lrep_take_LENGTH] THEN
        POP_ASSUM (fn th => `n = SUC (LENGTH t)` by SIMP_TAC hol_ss [th]) THEN
        FULL_SIMP_TAC hol_ss [lrep_take_tl] THEN
        Cases_on `ldest_rep f` THEN FULL_SIMP_TAC hol_ss [ldest_rep] THEN
        Cases_on `x''` THEN FULL_SIMP_TAC hol_ss [] THEN
        Cases_on `f []` THEN FULL_SIMP_TAC hol_ss [] THEN
        Cases_on `lrep_take r (LENGTH t)` THEN FULL_SIMP_TAC hol_ss []
      ]
    ]
  ]);

val lnil_rep_ok = prove(
  ``lrep_ok lnil_rep``,
  SIMP_TAC hol_ss [lrep_ok, lnil_rep]);

val lnil_repabs = prove(
  ``llist_rep (llist_abs lnil_rep) = lnil_rep``,
  SIMP_TAC hol_ss [lnil_rep_ok, GSYM llist_repabs]);

val LHD_THM = store_thm(
  "LHD_THM",
  ``(LHD LNIL = NONE) /\ (!h t. LHD (LCONS h t) = SOME h)``,
  SIMP_TAC hol_ss [LHDTL_CONS_THM] THEN
  SIMP_TAC hol_ss [LHD, LNIL, lnil_repabs, ldest_rep] THEN
  SIMP_TAC hol_ss [lnil_rep]);
val LTL_THM = store_thm(
  "LTL_THM",
  ``(LTL LNIL = NONE) /\ (!h t. LTL (LCONS h t) = SOME t)``,
  SIMP_TAC hol_ss [LHDTL_CONS_THM] THEN
  SIMP_TAC hol_ss [LTL, LNIL, lnil_repabs, ldest_rep] THEN
  SIMP_TAC hol_ss [lnil_rep]);



val LCONS_NOT_NIL = store_thm(
  "LCONS_NOT_NIL",
  ``!h t. ~(LCONS h t = LNIL) /\ ~(LNIL = LCONS h t)``,
  SIMP_TAC hol_ss [LCONS, LNIL] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC hol_ss [lcons_repabs, lnil_repabs] THEN
  POP_ASSUM (ASSUME_TAC o C Q.AP_THM `[]`) THEN
  FULL_SIMP_TAC hol_ss [lcons_rep, lnil_rep]);

val LCONS_11 = store_thm(
  "LCONS_11",
  ``!h1 t1 h2 t2. (LCONS h1 t1 = LCONS h2 t2) = (h1 = h2) /\ (t1 = t2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
  FULL_SIMP_TAC hol_ss [LCONS] THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC hol_ss [lcons_repabs] THEN
  FULL_SIMP_TAC hol_ss [lcons_rep] THEN
  Q.SUBGOAL_THEN `h1 = h2` SUBST_ALL_TAC THENL [
    POP_ASSUM (ASSUME_TAC o C Q.AP_THM `[]`) THEN FULL_SIMP_TAC hol_ss [],
    ALL_TAC
  ] THEN REWRITE_TAC [] THEN
  POP_ASSUM (ASSUME_TAC o Q.GEN `x` o C Q.AP_THM `(h2::x)`) THEN
  FULL_SIMP_TAC hol_ss [] THEN
  POP_ASSUM (fn th => `llist_rep t1 = llist_rep t2` by
                      CONV_TAC FUN_EQ_CONV THEN SIMP_TAC hol_ss [th]) THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_abs`) THEN
  FULL_SIMP_TAC hol_ss [llist_absrep]);

val lbuild_rep_nil = prove(
  ``!f x. lbuild_rep f x [] = option_APPLY SND (f x)``,
  SIMP_TAC hol_ss [lbuild_rep, lbuildn_rep])

val lbuild_recurses = prove(
  ``!f x. option_APPLY SND (ldest_rep (lbuild_rep f x)) =
          option_case NONE (\ (y,h). SOME (lbuild_rep f y)) (f x)``,
  REPEAT GEN_TAC THEN Cases_on `f x` THENL [
    ASM_SIMP_TAC hol_ss [lbuild_rep, ldest_rep, lbuildn_rep],
    ASM_SIMP_TAC hol_ss [ldest_rep, lbuild_rep_nil] THEN
    Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
    CONV_TAC (Q.X_FUN_EQ_CONV `pfx`) THEN GEN_TAC THEN
    ASM_SIMP_TAC hol_ss [lbuild_rep, lbuildn_rep_tl] THEN
    Cases_on `lbuildn_rep f q (LENGTH pfx)` THEN SIMP_TAC hol_ss []
  ]);

val llist_Axiom = store_thm(
  "llist_Axiom",
  ``!f : 'a -> ('a # 'b) option.
      ?g.
         (!x. LHD (g x) = option_APPLY SND (f x)) /\
         (!x. LTL (g x) = option_APPLY (g o FST) (f x))``,
  GEN_TAC THEN
  CONV_TAC (BINDER_CONV AND_FORALL_CONV) THEN
  Q.EXISTS_TAC `llist_abs o lbuild_rep f` THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    SIMP_TAC hol_ss [LHD, repabs_build] THEN Cases_on `f x` THEN
    ASM_SIMP_TAC hol_ss [ldest_rep, lbuild_rep, lbuildn_rep],
    SIMP_TAC hol_ss [LTL, repabs_build] THEN Cases_on `f x` THENL [
      ASM_SIMP_TAC hol_ss [lbuild_rep, ldest_rep, lbuildn_rep],
      ALL_TAC
    ] THEN
    ASM_SIMP_TAC hol_ss [ldest_rep, lbuild_rep_nil] THEN AP_TERM_TAC THEN
    Cases_on `x'` THEN SIMP_TAC hol_ss [] THEN
    ACCEPT_TAC
      (SIMP_RULE hol_ss [ldest_rep, lbuild_rep_nil,
                         ASSUME ``(f:'a->('a#'b) option)x = SOME (q,r)``]
       (SPEC_ALL lbuild_recurses))
  ]);

val LHD_EQ_NONE = store_thm(
  "LHD_EQ_NONE",
  ``!ll. (LHD ll = NONE) = (ll = LNIL)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC hol_ss [LHD_THM, LCONS_NOT_NIL]);
val LTL_EQ_NONE = store_thm(
  "LTL_EQ_NONE",
  ``!ll. (LTL ll = NONE) = (ll = LNIL)``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC hol_ss [LTL_THM, LCONS_NOT_NIL]);

val LHDTL_EQ_SOME = store_thm(
  "LHDTL_EQ_SOME",
  ``!h t ll. (ll = LCONS h t) = (LHD ll = SOME h) /\ (LTL ll = SOME t)``,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC hol_ss [LCONS_11, LCONS_NOT_NIL, LHD_THM, LTL_THM]);


(* now we can define MAP  *)
val LMAP = new_specification {
  consts = [{const_name = "LMAP", fixity = Prefix}], name = "LMAP",
  sat_thm = prove(
    ``?LMAP. (!f. LMAP f LNIL = LNIL) /\
             (!f h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\l. if l = LNIL then NONE
                     else SOME (THE (LTL l), f (THE (LHD l)))`
                llist_Axiom)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN REPEAT STRIP_TAC THENL [
      POP_ASSUM (ACCEPT_TAC o SIMP_RULE hol_ss [LHD_EQ_NONE] o Q.SPEC `LNIL` o
                 CONJUNCT1 o Q.SPEC `f`),
      POP_ASSUM (CONJUNCTS_THEN (ASSUME_TAC o
                                 SIMP_RULE hol_ss [LHD_THM, LTL_THM,
                                                   LCONS_NOT_NIL] o
                                 Q.SPEC `LCONS h t`) o
                 Q.SPEC `f`) THEN
      ASM_SIMP_TAC hol_ss [LHDTL_EQ_SOME]
    ])};



(* FILTER, which we'd also like, really depends on having the notions
   of finite-ness defined. *)

val LTAKE = new_recursive_definition {
  def = ``(LTAKE ll 0 = SOME []) /\
          (LTAKE ll (SUC n) =
             option_case
                NONE
                (\hd. option_case NONE (\tl. SOME (hd::tl))
                         (LTAKE (THE (LTL ll)) n))
                (LHD ll))``,
  name = "LTAKE",
  rec_axiom = prim_recTheory.num_Axiom};

val LTAKE_ltake = prove(
  ``!n ll. LTAKE ll n = lrep_take (llist_rep ll) n``,
  Induct THENL [
     SIMP_TAC hol_ss [LTAKE, lrep_take],
     POP_ASSUM (fn th => SIMP_TAC hol_ss [LTAKE, lrep_take_tl, LHD, LTL,
                                          ldest_rep, th]) THEN
     Cases_on `llist_rep ll []` THEN SIMP_TAC hol_ss [] THEN
     Q.SUBGOAL_THEN `llist_rep (llist_abs (\l. llist_rep ll (x::l))) =
                     \l. llist_rep ll (x::l)`
     (fn th => SIMP_TAC hol_ss [th]) THEN
     SIMP_TAC hol_ss [GSYM llist_repabs] THEN MATCH_MP_TAC lrep_ltl THEN
     SIMP_TAC hol_ss [llist_repabs, llist_absrep]
  ]);

val llist_rep_11 = prove(
  ``!ll1 ll2. (llist_rep ll1 = llist_rep ll2) = (ll1 = ll2)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, SIMP_TAC hol_ss []] THEN
  STRIP_TAC THEN POP_ASSUM (ACCEPT_TAC o SIMP_RULE hol_ss [llist_absrep] o
                            Q.AP_TERM `llist_abs`));

val APPEND_11 = prove(
  ``!front1 last1 front2 last2.
       (APPEND front1 [last1] = APPEND front2 [last2]) =
       (front1 = front2) /\ (last1 = last2)``,
  Induct THEN SIMP_TAC hol_ss [] THENL [
    GEN_TAC THEN Induct THEN SIMP_TAC hol_ss [],
    GEN_TAC THEN GEN_TAC THEN Induct THEN ASM_SIMP_TAC hol_ss [] THEN
    MESON_TAC []
  ]);

val lrep_ok' = prove(
  ``lrep_ok f =
       !l x. (f l = SOME x) =
             (?n. lrep_take f (SUC n) = SOME (APPEND l [x]))``,
  SIMP_TAC hol_ss [lrep_ok] THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    EQ_TAC THENL [
      SIMP_TAC hol_ss [lrep_take] THEN STRIP_TAC THEN RES_TAC THEN
      Q.EXISTS_TAC `n` THEN ASM_SIMP_TAC hol_ss [],
      SIMP_TAC hol_ss [lrep_take] THEN STRIP_TAC THEN
      Cases_on `lrep_take f n` THEN FULL_SIMP_TAC hol_ss [] THEN
      Cases_on `f x'` THEN FULL_SIMP_TAC hol_ss [APPEND_11] THEN
      ELIM_TAC THEN ASM_SIMP_TAC hol_ss []
    ],
    `?m. lrep_take f (SUC m) = SOME (APPEND l [x])` by ASM_MESON_TAC [] THEN
    FULL_SIMP_TAC hol_ss [lrep_take] THEN
    Cases_on `lrep_take f m` THEN FULL_SIMP_TAC hol_ss [] THEN
    Cases_on `f x'` THEN FULL_SIMP_TAC hol_ss [APPEND_11] THEN ELIM_TAC THEN
    ASM_MESON_TAC []
  ]);

val LTAKE_EQ = store_thm(
  "LTAKE_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LTAKE ll1 n = LTAKE ll2 n)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC hol_ss [], ALL_TAC] THEN
  SIMP_TAC hol_ss [LTAKE_ltake] THEN REPEAT STRIP_TAC THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `~(llist_rep ll1 = llist_rep ll2)` by ASM_MESON_TAC [llist_rep_11] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE hol_ss [] o
             CONV_RULE (RAND_CONV (Q.X_FUN_EQ_CONV `pfx`))) THEN
  Q.ABBREV_TAC `f = llist_rep ll1` THEN
  Q.ABBREV_TAC `g = llist_rep ll2` THEN
  `lrep_ok f` by ASM_MESON_TAC [llist_absrep, llist_repabs] THEN
  `lrep_ok g` by ASM_MESON_TAC [llist_absrep, llist_repabs] THEN
  Cases_on `f pfx` THEN Cases_on `g pfx` THEN
  RULE_ASSUM_TAC (SIMP_RULE hol_ss []) THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  `?gm. lrep_take f (SUC gm) = SOME (APPEND pfx [x])` by
    ASM_MESON_TAC [lrep_ok'] THEN
  `f pfx = SOME x` by ASM_MESON_TAC [lrep_ok'] THEN
  `g pfx = SOME x` by ASM_MESON_TAC [lrep_ok'] THEN
  FULL_SIMP_TAC hol_ss []);

val LLIST_BISIMULATION = store_thm(
  "LLIST_BISIMULATION",
  ``!ll1 ll2. (ll1 = ll2) =
              ?R. R ll1 ll2 /\
                  !ll3 ll4.  R ll3 ll4 ==>
                             (ll3 = LNIL) /\ (ll4 = LNIL) \/
                             (LHD ll3 = LHD ll4) /\
                             R (THE (LTL ll3)) (THE (LTL ll4))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `$=` THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC hol_ss [],
    REPEAT STRIP_TAC THEN SIMP_TAC hol_ss [LTAKE_EQ] THEN GEN_TAC THEN
    Q.PAT_ASSUM `R ll1 ll2` MP_TAC THEN
    MAP_EVERY Q.ID_SPEC_TAC [`ll1`, `ll2`] THEN Induct_on `n` THEN
    SIMP_TAC hol_ss [LTAKE] THEN REPEAT STRIP_TAC THEN
    `(ll1 = LNIL) /\ (ll2 = LNIL) \/
     (LHD ll1 = LHD ll2) /\ R (THE (LTL ll1)) (THE (LTL ll2))` by
      ASM_MESON_TAC []
    THENL [
      ELIM_TAC THEN SIMP_TAC hol_ss [LHD_THM],
      Cases_on `LHD ll2` THEN ASM_SIMP_TAC hol_ss [] THEN
      `LTAKE (THE (LTL ll1)) n = LTAKE (THE (LTL ll2)) n` by
        ASM_MESON_TAC [] THEN
      ASM_SIMP_TAC hol_ss []
    ]
  ]);

val LAPPEND = new_specification{
  consts = [{const_name = "LAPPEND", fixity = Prefix}],
  name = "LAPPEND",
  sat_thm = prove(
    ``?LAPPEND. (!x. LAPPEND LNIL x = x) /\
               (!h t x. LAPPEND (LCONS h t) x = LCONS h (LAPPEND t x))``,
    STRIP_ASSUME_TAC
       (Q.ISPEC `\ (l1,l2).
                     if l1 = LNIL then
                        if l2 = LNIL then NONE
                        else SOME ((l1, THE (LTL l2)), THE (LHD l2))
                     else SOME ((THE (LTL l1), l2), THE (LHD l1))`
                llist_Axiom) THEN
    Q.EXISTS_TAC `\l1 l2. g (l1, l2)` THEN SIMP_TAC hol_ss [] THEN
    REPEAT STRIP_TAC THENL [
      ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
      Q.EXISTS_TAC `\ll1 ll2. ll1 = g (LNIL, ll2)` THEN
      SIMP_TAC hol_ss [] THEN Q.X_GEN_TAC `x` THEN
      ASM_SIMP_TAC hol_ss [] THEN
      STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THENL [
        DISJ1_TAC THEN
        ASM_SIMP_TAC hol_ss [GSYM LHD_EQ_NONE, LHD_THM],
        DISJ2_TAC THEN
        ASM_SIMP_TAC hol_ss [LHD_THM, LCONS_NOT_NIL]
      ],
      ASM_SIMP_TAC hol_ss [LHDTL_EQ_SOME, LCONS_NOT_NIL, LTL_THM, LHD_THM]
    ])};

val LMAP_APPEND = store_thm(
  "LMAP_APPEND",
  ``!f ll1 ll2. LMAP f (LAPPEND ll1 ll2) =
                LAPPEND (LMAP f ll1) (LMAP f ll2)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?x y. (ll1 = LMAP f (LAPPEND x y)) /\
                                (ll2 = LAPPEND (LMAP f x) (LMAP f y))` THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    MESON_TAC [],
    ALL_TAC
  ] THEN ELIM_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THENL [
    SIMP_TAC hol_ss [LMAP, LAPPEND] THEN
    STRUCT_CASES_TAC (Q.SPEC `y` llist_CASES) THEN
    SIMP_TAC hol_ss [LMAP, LCONS_NOT_NIL, LTL_THM] THEN
    MESON_TAC [LAPPEND, LMAP],
    SIMP_TAC hol_ss [LMAP, LAPPEND, LCONS_NOT_NIL, LHD_THM, LTL_THM] THEN
    MESON_TAC []
  ]);

val LMAP_MAP = store_thm(
  "LMAP_MAP",
  ``!(f:'a -> 'b) (g:'c -> 'a) (ll:'c llist).
        LMAP f (LMAP g ll) = LMAP (f o g) ll``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?ll0. (ll1 = LMAP f (LMAP g ll0)) /\
                                (ll2 = LMAP (f o g) ll0)` THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    MESON_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
      (Q.ISPEC `ll0:'c llist` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LMAP, LTL_THM, LHD_THM] THEN
    MESON_TAC []
  ]);

val LAPPEND_NIL_2ND = store_thm(
  "LAPPEND_NIL_2ND",
  ``!ll. LAPPEND ll LNIL = ll``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LAPPEND ll2 LNIL` THEN
  SIMP_TAC hol_ss [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC hol_ss [LAPPEND, LTL_THM, LHD_THM]);

val LFINITE = new_definition(
  "LFINITE",
  ``LFINITE ll = ?n. LTAKE ll n = NONE``);

val LFINITE_THM = store_thm(
  "LFINITE_THM",
  ``(LFINITE LNIL = T) /\
    (!h t. LFINITE (LCONS h t) = LFINITE t)``,
  SIMP_TAC hol_ss [LFINITE] THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `SUC 0` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM],
    EQ_TAC THENL [
      STRIP_TAC THEN Cases_on `n` THEN
      FULL_SIMP_TAC hol_ss [LTAKE, LTL_THM, LHD_THM] THEN
      Cases_on `LTAKE t n'` THEN FULL_SIMP_TAC hol_ss [] THEN ASM_MESON_TAC [],
      STRIP_TAC THEN Q.EXISTS_TAC `SUC n` THEN
      ASM_SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM]
    ]
  ]);

val LLENGTH = new_definition(
  "LLENGTH",
  ``LLENGTH ll = if LFINITE ll then
                   SOME ((@n. (LTAKE ll n = NONE) /\
                              !m. m < n ==> ?ll'. LTAKE ll m = SOME ll') - 1)
                 else NONE``);

val LTAKE_NIL_EQ_SOME = store_thm(
  "LTAKE_NIL_EQ_SOME",
  ``!l m. (LTAKE LNIL m = SOME l) = (m = 0) /\ (l = [])``,
  REPEAT GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM] THEN
  MESON_TAC []);

val LTAKE_NIL_EQ_NONE = store_thm(
  "LTAKE_NIL_EQ_NONE",
  ``!m. (LTAKE LNIL m = NONE) = (0 < m)``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM]);

val LTAKE_CONS_EQ_NONE = store_thm(
  "LTAKE_CONS_EQ_NONE",
  ``!m h t. (LTAKE (LCONS h t) m = NONE) =
            (?n. (m = SUC n) /\ (LTAKE t n = NONE))``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN
  SIMP_TAC (hol_ss ++ COND_elim_ss) [optionTheory.option_case_compute,
                                     optionTheory.option_CLAUSES]);

val LTAKE_CONS_EQ_SOME = store_thm(
  "LTAKE_CONS_EQ_SOME",
  ``!m h t l.
       (LTAKE (LCONS h t) m = SOME l) =
       (m = 0) /\ (l = []) \/
       ?n l'. (m = SUC n) /\ (LTAKE t n = SOME l') /\  (l = h::l')``,
  GEN_TAC THEN Cases_on `m` THEN
  SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THENL [
    MESON_TAC [],
    REPEAT GEN_TAC THEN Cases_on `LTAKE t n` THEN SIMP_TAC hol_ss [] THEN
    MESON_TAC []
  ]);

val SUC_EXISTS_lemma = prove(
  ``!P n. (?m. (n = SUC m) /\ P m n) = 0 < n /\ P (n - 1) n``,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    ELIM_TAC THEN ASM_SIMP_TAC hol_ss [],
    Q.EXISTS_TAC `n - 1` THEN ASM_SIMP_TAC hol_ss []
  ]);

val LTAKE_EQ_NONE = store_thm(
  "LTAKE_EQ_NONE",
  ``!ll n. (LTAKE ll n = NONE) ==> 0 < n``,
  REPEAT GEN_TAC THEN Cases_on `n` THEN SIMP_TAC hol_ss [LTAKE]);


val LTAKE_EQ_SOME_CONS = store_thm(
  "LTAKE_EQ_SOME_CONS",
  ``!n l x. (LTAKE l n = SOME x) ==> !h. ?y. LTAKE (LCONS h l) n = SOME y``,
  Induct THEN SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l` llist_CASES) THEN
  SIMP_TAC hol_ss [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE t n` THEN SIMP_TAC hol_ss [] THEN RES_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `h`) THEN
  ASM_SIMP_TAC hol_ss []);

val LAND_CONV = RATOR_CONV o RAND_CONV

open arithLib

val LLENGTH_THM = store_thm(
  "LLENGTH_THM",
  ``(LLENGTH LNIL = SOME 0) /\
    (!h t. LLENGTH (LCONS h t) = option_APPLY SUC (LLENGTH t))``,
  SIMP_TAC hol_ss [LLENGTH, LFINITE_THM] THEN REPEAT STRIP_TAC THENL [
    SIMP_TAC hol_ss [LTAKE_NIL_EQ_SOME, LTAKE_NIL_EQ_NONE] THEN
    Q.SUBGOAL_THEN `!n. (!m. m < n ==> (m = 0)) = (n <= 1)`
       (fn th => SIMP_TAC hol_ss [th])
    THENL [
      GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        SPOSE_NOT_THEN ASSUME_TAC THEN
        FIRST_X_ASSUM (MP_TAC o Q.SPEC `1`) THEN ASM_SIMP_TAC hol_ss [],
        ASM_SIMP_TAC hol_ss []
      ],
      SIMP_TAC hol_ss [ARITH_PROVE ``0 < n /\ n <= 1 = (n = 1)``]
    ],
    COND_CASES_TAC THEN SIMP_TAC hol_ss [] THEN
    Q.SUBGOAL_THEN `?!n. (LTAKE (LCONS h t) n = NONE) /\
                         !m. m < n ==> ?ll'. LTAKE (LCONS h t) m = SOME ll'`
    ASSUME_TAC THENL [
      SIMP_TAC hol_ss [Ho_theorems.EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
        POP_ASSUM (STRIP_ASSUME_TAC o
                   CONV_RULE numLib.EXISTS_LEAST_CONV o
                   SIMP_RULE hol_ss [LFINITE]) THEN Q.EXISTS_TAC `SUC n` THEN
        ASM_SIMP_TAC hol_ss [LTAKE, LTL_THM, LHD_THM] THEN
        GEN_TAC THEN Cases_on `m` THEN
        SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN REPEAT STRIP_TAC THEN
        Cases_on `LTAKE t n'` THEN SIMP_TAC hol_ss [] THEN ASM_MESON_TAC [],
        REPEAT STRIP_TAC THEN ASM_MESON_TAC [arithmeticTheory.LESS_LESS_CASES,
                                             optionTheory.NOT_NONE_SOME]
      ],
      ALL_TAC
    ] THEN
    POP_ASSUM (
      CONJUNCTS_THEN2
        (fn th => STRIP_ASSUME_TAC (SELECT_RULE th) THEN
                  Q.X_CHOOSE_THEN `LEN_ht` STRIP_ASSUME_TAC th)
        ASSUME_TAC o
      SIMP_RULE hol_ss [Ho_theorems.EXISTS_UNIQUE_THM]) THEN
    Q.SUBGOAL_THEN
       `(@n. (LTAKE (LCONS h t) n = NONE) /\
             !m. m < n ==> ?ll'. LTAKE (LCONS h t) m = SOME ll') = LEN_ht`
    SUBST_ALL_TAC THENL [
      POP_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC hol_ss [],
      POP_ASSUM (K ALL_TAC) THEN FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC
    ] THEN
    Q.SUBGOAL_THEN
       `?!n. (LTAKE t n = NONE) /\ !m. m < n ==> ?ll'. LTAKE t m = SOME ll'`
    ASSUME_TAC THENL [
      SIMP_TAC hol_ss [Ho_theorems.EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o
                       CONV_RULE numLib.EXISTS_LEAST_CONV o
                       SIMP_RULE hol_ss [LFINITE]) THEN Q.EXISTS_TAC `n` THEN
        ASM_MESON_TAC [optionTheory.NOT_SOME_NONE,
                       optionTheory.option_nchotomy],
        MESON_TAC [arithmeticTheory.LESS_LESS_CASES,
                   optionTheory.NOT_SOME_NONE]
      ],
      ALL_TAC
    ] THEN
    POP_ASSUM (
      CONJUNCTS_THEN2
        (fn th => STRIP_ASSUME_TAC (SELECT_RULE th) THEN
                  Q.X_CHOOSE_THEN `LEN_t` STRIP_ASSUME_TAC th)
        ASSUME_TAC o
      SIMP_RULE hol_ss [Ho_theorems.EXISTS_UNIQUE_THM]) THEN
    Q.SUBGOAL_THEN `(@n. (LTAKE t n = NONE) /\
                         !m. m < n ==> ?ll'. LTAKE t m = SOME ll') = LEN_t`
    SUBST_ALL_TAC THENL [
      POP_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC hol_ss [],
      FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN POP_ASSUM (K ALL_TAC)
    ] THEN
    `0 < LEN_t` by ASM_MESON_TAC [LTAKE_EQ_NONE] THEN
    `0 < LEN_ht` by ASM_MESON_TAC [LTAKE_EQ_NONE] THEN
    `SUC (LEN_t - 1) = LEN_t` by ASM_SIMP_TAC hol_ss [] THEN
    POP_ASSUM SUBST1_TAC THEN
    `(LEN_ht - 1 = LEN_t) = (LEN_ht = SUC LEN_t)`
      by ASM_SIMP_TAC hol_ss [] THEN
    POP_ASSUM SUBST1_TAC THEN
    SPOSE_NOT_THEN ASSUME_TAC THEN
    `LEN_ht < SUC LEN_t \/ SUC LEN_t < LEN_ht` by ASM_SIMP_TAC hol_ss []
    THENL [
      `LEN_ht < LEN_t \/ (LEN_ht = LEN_t)` by ASM_SIMP_TAC hol_ss [] THENL [
        `?ll1. LTAKE t LEN_ht = SOME ll1` by ASM_MESON_TAC [] THEN
        ASM_MESON_TAC [optionTheory.NOT_NONE_SOME, LTAKE_EQ_SOME_CONS],
        ELIM_TAC THEN
        `?lt_less_1. (LEN_t = SUC lt_less_1) /\
                     (LTAKE t lt_less_1 = NONE)` by
           ASM_MESON_TAC [LTAKE_CONS_EQ_NONE] THEN
        `?ll. LTAKE t lt_less_1 = SOME ll` by
           ASM_MESON_TAC [ARITH_PROVE ``!n. n < SUC n``] THEN
        FULL_SIMP_TAC hol_ss []
      ],
      `?ll. LTAKE (LCONS h t) (SUC LEN_t) = SOME ll` by ASM_MESON_TAC [] THEN
      POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE hol_ss [LTAKE_CONS_EQ_SOME]) THEN
      FULL_SIMP_TAC hol_ss []
    ]
  ]);

val LFINITE_HAS_LENGTH = store_thm(
  "LFINITE_HAS_LENGTH",
  ``!ll. LFINITE ll ==> ?n. LLENGTH ll = SOME n``,
  GEN_TAC THEN SIMP_TAC hol_ss [LLENGTH]);

val NOT_LFINITE_NO_LENGTH = store_thm(
  "NOT_LFINITE_NO_LENGTH",
  ``!ll. ~LFINITE ll ==> (LLENGTH ll = NONE)``,
  SIMP_TAC hol_ss [LLENGTH]);

val LFINITE_INDUCTION = store_thm(
  "LFINITE_INDUCTION",
  ``!P.  P LNIL /\ (!t. P t ==> !h. P (LCONS h t)) ==>
         !ll. LFINITE ll ==> P ll``,
  REPEAT STRIP_TAC THEN
  Induct_on `THE (LLENGTH ll)` THEN REPEAT STRIP_TAC THEN
  `?n. LLENGTH ll = SOME n` by ASM_MESON_TAC [LFINITE_HAS_LENGTH] THEN
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll` llist_CASES) THENL [
    ASM_SIMP_TAC hol_ss [],
    FULL_SIMP_TAC hol_ss [LLENGTH_THM, optionTheory.option_APPLY_EQ_SOME] THEN
    FULL_SIMP_TAC hol_ss [],
    FULL_SIMP_TAC hol_ss [LLENGTH_THM],
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC hol_ss [LLENGTH_THM, LFINITE_THM, AND_IMP_INTRO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC hol_ss [optionTheory.option_APPLY_EQ_SOME]
  ]);


val LFINITE_STRONG_INDUCTION = save_thm(
  "LFINITE_STRONG_INDUCTION",
  SIMP_RULE hol_ss [LFINITE_THM]
  (Q.SPEC `\ll. LFINITE ll /\ P ll` LFINITE_INDUCTION))

val LFINITE_MAP = store_thm(
  "LFINITE_MAP",
  ``!f (ll:'a llist). LFINITE (LMAP f ll) = LFINITE ll``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN Q.ABBREV_TAC `ll1 = LMAP f ll` THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll` THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
    Ho_resolve.MATCH_MP_TAC LFINITE_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LMAP, LCONS_NOT_NIL, LFINITE_THM, LCONS_11],
    Q.ID_SPEC_TAC `ll` THEN Ho_resolve.MATCH_MP_TAC LFINITE_INDUCTION THEN
    SIMP_TAC hol_ss [LFINITE_THM, LMAP]
  ]);

val LFINITE_APPEND = store_thm(
  "LFINITE_APPEND",
  ``!ll1 ll2. LFINITE (LAPPEND ll1 ll2) = LFINITE ll1 /\ LFINITE ll2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN Q.ABBREV_TAC `ll0 = LAPPEND ll1 ll2` THEN
    POP_ASSUM MP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`ll1`, `ll2`] THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll0` THEN
    Ho_resolve.MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LFINITE_THM, LAPPEND, LCONS_NOT_NIL, LCONS_11] THEN
    ASM_MESON_TAC [],
    REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
    Q.ID_SPEC_TAC `ll1` THEN
    Ho_resolve.MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC hol_ss [LFINITE_THM, LAPPEND]
  ]);

val LLENGTH_MAP = store_thm(
  "LLENGTH_MAP",
  ``!ll f. LLENGTH (LMAP f ll) = LLENGTH ll``,
  REPEAT GEN_TAC THEN Cases_on `LFINITE ll` THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll` THEN
    Ho_resolve.MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC hol_ss [LLENGTH_THM, LMAP],
    ASM_MESON_TAC [NOT_LFINITE_NO_LENGTH, LFINITE_MAP]
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
                        MESON_TAC [th, LFINITE_APPEND]) THEN
    ASM_SIMP_TAC hol_ss [] THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll2` THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
    Ho_resolve.MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC hol_ss [LLENGTH_THM, LAPPEND] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN ASM_SIMP_TAC hol_ss [],
    `LLENGTH (LAPPEND ll1 ll2) = NONE`
      by ASM_MESON_TAC [NOT_LFINITE_NO_LENGTH] THEN
    FULL_SIMP_TAC hol_ss [LFINITE_APPEND]
  ]);

val toList = new_definition(
  "toList",
  ``toList ll = if LFINITE ll then LTAKE ll (THE (LLENGTH ll)) else NONE``);


val LDROP = new_recursive_definition {
  def = ``(LDROP 0 ll = SOME ll) /\
          (LDROP (SUC n) ll = option_JOIN (option_APPLY (LDROP n) (LTL ll)))``,
  rec_axiom = prim_recTheory.num_Axiom,
  name = "LDROP"};

(*
val LFILTER = new_specification {
  consts = [{const_name = "LFILTER", fixity = Prefix}], name = "LFILTER",
  sat_thm = prove(
    ``?LFILTER.  (!P. LFILTER P LNIL = LNIL) /\
                 (!P h t.
                      LFILTER P (LCONS h t) = if P h then LCONS h (LFILTER P t)
                                              else LFILTER P t)``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\l. if l = LNIL then NONE
                     else SOME (THE (LTL l), f (THE (LHD l)))`
                llist_Axiom)) THEN

*)

val _ = export_theory();

