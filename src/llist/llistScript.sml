structure llistScript = 
struct

(* interactive use:
app load ["boolSimps","pairSimps","combinSimps",
          "optionSimps", "arithSimps", "listSimps",
          "mesonLib","SingleStep", "Q", "numLib"];

 open SingleStep mesonLib Rsyntax Prim_rec simpLib 
      boolSimps pairSimps combinSimps optionSimps arithSimps listSimps;
*)
open HolKernel boolLib Parse
      SingleStep mesonLib Rsyntax Prim_rec simpLib 
      boolSimps pairSimps combinSimps optionSimps arithSimps listSimps;

local open listTheory optionTheory pairTheory in end;

infix THEN THENL THENC ++
infix 8 by


val is_pair = pairSyntax.is_pair

val UNCURRY_THM = pairTheory.UNCURRY

val hol_ss = bool_ss ++ optionSimps.OPTION_ss ++ listSimps.list_ss ++
                        arithSimps.ARITH_ss ++ arithSimps.REDUCE_ss ++
                        pairSimps.PAIR_ss ++ rewrites [UNCURRY_THM] ++
                        combinSimps.COMBIN_ss

val PAIR_EQ = pairTheory.PAIR_EQ
val ELIM1_TAC =
  let fun apply thm =
        let fun chkeq thm =
              let val con = concl thm
              in is_var (lhs con) andalso not (free_in (lhs con) (rhs con))
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

val lrep_take = Prim_rec.new_recursive_definition {
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

val llist_tydef = 
  new_type_definition ("llist", type_inhabited);

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
  ``LHD ll = OPTION_MAP FST (ldest_rep (llist_rep ll))``);

val LTL = new_definition(
  "LTL",
  ``LTL ll = OPTION_MAP (llist_abs o SND) (ldest_rep (llist_rep ll))``);

val lcons_rep = new_definition(
  "lcons_rep",
  ``lcons_rep h t = \l. if l = [] then SOME h
                        else if HD l = h then t (TL l) else NONE``);

val LCONS = new_definition(
  "LCONS",
  ``LCONS h t = llist_abs (lcons_rep h (llist_rep t))``);

val lbuildn_rep = Prim_rec.new_recursive_definition {
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
               if pfx' = pfx then OPTION_MAP SND (f nthseed)
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

(* &&& FAILS  ... last tactic ... appears not to understand alpha-conv! ... *)
val lrep_ltl = prove(
(*  ``!h t. lrep_ok t ==> lrep_ok (\sfx. t (h::sfx))``, *)
  ``!h t. lrep_ok t ==> lrep_ok (\l. t (h::l))``,
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
  ``!f x. lbuild_rep f x [] = OPTION_MAP SND (f x)``,
  SIMP_TAC hol_ss [lbuild_rep, lbuildn_rep])

val lbuild_recurses = prove(
  ``!f x. OPTION_MAP SND (ldest_rep (lbuild_rep f x)) =
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
         (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
         (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))``,
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


val LTAKE = Prim_rec.new_recursive_definition {
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
  SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN REPEAT GEN_TAC THEN
  Cases_on `LTAKE n t` THEN SIMP_TAC hol_ss []);

val LTAKE_ltake = prove(
  ``!n ll. LTAKE n ll = lrep_take (llist_rep ll) n``,
  Induct THENL [
     SIMP_TAC hol_ss [LTAKE_THM, lrep_take],
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
  ``!ll1 ll2. (ll1 = ll2) = (!n. LTAKE n ll1 = LTAKE n ll2)``,
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
      `LTAKE n (THE (LTL ll1)) = LTAKE n (THE (LTL ll2))` by
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
       (Q.ISPEC `\(l1,l2).
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

val LAPPEND_ASSOC = store_thm(
  "LAPPEND_ASSOC",
  ``!ll1 ll2 ll3. LAPPEND (LAPPEND ll1 ll2) ll3 =
                  LAPPEND ll1 (LAPPEND ll2 ll3)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?l3 l4 l5. (ll1 = LAPPEND (LAPPEND l3 l4) l5) /\
                                     (ll2 = LAPPEND l3 (LAPPEND l4 l5))` THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    MESON_TAC [],
    ELIM_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l3` llist_CASES) THEN
    SIMP_TAC hol_ss [LHD_THM, LAPPEND, LCONS_NOT_NIL, LTL_THM] THENL [
      STRUCT_CASES_TAC (Q.SPEC `l4` llist_CASES) THEN
      SIMP_TAC hol_ss [LHD_THM, LTL_THM, LAPPEND, LCONS_NOT_NIL] THENL [
        STRUCT_CASES_TAC (Q.SPEC `l5` llist_CASES) THEN
        SIMP_TAC hol_ss [LHD_THM, LTL_THM, LAPPEND, LCONS_NOT_NIL] THEN
        MESON_TAC [LAPPEND],
        MESON_TAC [LAPPEND]
      ],
      MESON_TAC [LAPPEND]
    ]
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
  ``LFINITE ll = ?n. LTAKE n ll = NONE``);

val LFINITE_THM = store_thm(
  "LFINITE_THM",
  ``(LFINITE LNIL = T) /\
    (!h t. LFINITE (LCONS h t) = LFINITE t)``,
  SIMP_TAC hol_ss [LFINITE] THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `SUC 0` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM],
    EQ_TAC THENL [
      STRIP_TAC THEN Cases_on `n` THEN
      FULL_SIMP_TAC hol_ss [LTAKE_THM] THEN
      Cases_on `LTAKE n' t` THEN FULL_SIMP_TAC hol_ss [] THEN ASM_MESON_TAC [],
      STRIP_TAC THEN Q.EXISTS_TAC `SUC n` THEN
      ASM_SIMP_TAC hol_ss [LTAKE_THM]
    ]
  ]);

val LLENGTH = new_definition(
  "LLENGTH",
  ``LLENGTH ll = if LFINITE ll then
                   SOME ((@n. (LTAKE n ll = NONE) /\
                              !m. m < n ==> ?ll'. LTAKE m ll = SOME ll') - 1)
                 else NONE``);

val LTAKE_NIL_EQ_SOME = store_thm(
  "LTAKE_NIL_EQ_SOME",
  ``!l m. (LTAKE m LNIL = SOME l) = (m = 0) /\ (l = [])``,
  REPEAT GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM] THEN
  MESON_TAC []);

val LTAKE_NIL_EQ_NONE = store_thm(
  "LTAKE_NIL_EQ_NONE",
  ``!m. (LTAKE m LNIL = NONE) = (0 < m)``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM]);

val LTAKE_CONS_EQ_NONE = store_thm(
  "LTAKE_CONS_EQ_NONE",
  ``!m h t. (LTAKE m (LCONS h t) = NONE) =
            (?n. (m = SUC n) /\ (LTAKE n t = NONE))``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN
  SIMP_TAC (hol_ss ++ COND_elim_ss) [optionTheory.option_case_compute,
                                     optionTheory.option_CLAUSES]);

val LTAKE_CONS_EQ_SOME = store_thm(
  "LTAKE_CONS_EQ_SOME",
  ``!m h t l.
       (LTAKE m (LCONS h t) = SOME l) =
       (m = 0) /\ (l = []) \/
       ?n l'. (m = SUC n) /\ (LTAKE n t = SOME l') /\  (l = h::l')``,
  GEN_TAC THEN Cases_on `m` THEN
  SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THENL [
    MESON_TAC [],
    REPEAT GEN_TAC THEN Cases_on `LTAKE n t` THEN SIMP_TAC hol_ss [] THEN
    MESON_TAC []
  ]);

val LTAKE_EQ_NONE = store_thm(
  "LTAKE_EQ_NONE",
  ``!ll n. (LTAKE n ll = NONE) ==> 0 < n``,
  REPEAT GEN_TAC THEN Cases_on `n` THEN SIMP_TAC hol_ss [LTAKE]);


val LTAKE_EQ_SOME_CONS = store_thm(
  "LTAKE_EQ_SOME_CONS",
  ``!n l x. (LTAKE n l = SOME x) ==> !h. ?y. LTAKE n (LCONS h l) = SOME y``,
  Induct THEN SIMP_TAC hol_ss [LTAKE, LHD_THM, LTL_THM] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l` llist_CASES) THEN
  SIMP_TAC hol_ss [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE n t` THEN SIMP_TAC hol_ss [] THEN RES_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `h`) THEN
  ASM_SIMP_TAC hol_ss []);

val LAND_CONV = RATOR_CONV o RAND_CONV

open arithLib

val LLENGTH_THM = store_thm(
  "LLENGTH_THM",
  ``(LLENGTH LNIL = SOME 0) /\
    (!h t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t))``,
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
    Q.SUBGOAL_THEN `?!n. (LTAKE n (LCONS h t) = NONE) /\
                         !m. m < n ==> ?ll'. LTAKE m (LCONS h t) = SOME ll'`
    ASSUME_TAC THENL [
      SIMP_TAC hol_ss [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
        POP_ASSUM (STRIP_ASSUME_TAC o
                   CONV_RULE numLib.EXISTS_LEAST_CONV o
                   SIMP_RULE hol_ss [LFINITE]) THEN Q.EXISTS_TAC `SUC n` THEN
        ASM_SIMP_TAC hol_ss [LTAKE, LTL_THM, LHD_THM] THEN
        GEN_TAC THEN Cases_on `m` THEN
        SIMP_TAC hol_ss [LTAKE_THM] THEN REPEAT STRIP_TAC THEN
        Cases_on `LTAKE n' t` THEN SIMP_TAC hol_ss [] THEN ASM_MESON_TAC [],
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
      SIMP_RULE hol_ss [EXISTS_UNIQUE_THM]) THEN
    Q.SUBGOAL_THEN
       `(@n. (LTAKE n (LCONS h t) = NONE) /\
             !m. m < n ==> ?ll'. LTAKE m (LCONS h t) = SOME ll') = LEN_ht`
    SUBST_ALL_TAC THENL [
      POP_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC hol_ss [],
      POP_ASSUM (K ALL_TAC) THEN FULL_SIMP_TAC hol_ss [] THEN ELIM_TAC
    ] THEN
    Q.SUBGOAL_THEN
       `?!n. (LTAKE n t = NONE) /\ !m. m < n ==> ?ll'. LTAKE m t = SOME ll'`
    ASSUME_TAC THENL [
      SIMP_TAC hol_ss [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [
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
      SIMP_RULE hol_ss [EXISTS_UNIQUE_THM]) THEN
    Q.SUBGOAL_THEN `(@n. (LTAKE n t = NONE) /\
                         !m. m < n ==> ?ll'. LTAKE m t = SOME ll') = LEN_t`
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
        `?ll1. LTAKE LEN_ht t = SOME ll1` by ASM_MESON_TAC [] THEN
        ASM_MESON_TAC [optionTheory.NOT_NONE_SOME, LTAKE_EQ_SOME_CONS],
        ELIM_TAC THEN
        `?lt_less_1. (LEN_t = SUC lt_less_1) /\
                     (LTAKE lt_less_1 t = NONE)` by
           ASM_MESON_TAC [LTAKE_CONS_EQ_NONE] THEN
        `?ll. LTAKE lt_less_1 t = SOME ll` by
           ASM_MESON_TAC [ARITH_PROVE ``!n. n < SUC n``] THEN
        FULL_SIMP_TAC hol_ss []
      ],
      `?ll. LTAKE (SUC LEN_t) (LCONS h t) = SOME ll` by ASM_MESON_TAC [] THEN
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
    FULL_SIMP_TAC hol_ss [LLENGTH_THM, optionTheory.OPTION_MAP_EQ_SOME] THEN
    FULL_SIMP_TAC hol_ss [],
    FULL_SIMP_TAC hol_ss [LLENGTH_THM],
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC hol_ss [LLENGTH_THM, LFINITE_THM, AND_IMP_INTRO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC hol_ss [optionTheory.OPTION_MAP_EQ_SOME]
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
    HO_MATCH_MP_TAC LFINITE_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LMAP, LCONS_NOT_NIL, LFINITE_THM, LCONS_11],
    Q.ID_SPEC_TAC `ll` THEN HO_MATCH_MP_TAC LFINITE_INDUCTION THEN
    SIMP_TAC hol_ss [LFINITE_THM, LMAP]
  ]);

val LFINITE_APPEND = store_thm(
  "LFINITE_APPEND",
  ``!ll1 ll2. LFINITE (LAPPEND ll1 ll2) = LFINITE ll1 /\ LFINITE ll2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN Q.ABBREV_TAC `ll0 = LAPPEND ll1 ll2` THEN
    POP_ASSUM MP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`ll1`, `ll2`] THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll0` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LFINITE_THM, LAPPEND, LCONS_NOT_NIL, LCONS_11] THEN
    ASM_MESON_TAC [],
    REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
    Q.ID_SPEC_TAC `ll1` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC hol_ss [LFINITE_THM, LAPPEND]
  ]);

val NOT_LFINITE_APPEND = store_thm(
  "NOT_LFINITE_APPEND",
  ``!ll1 ll2. ~LFINITE ll1 ==> (LAPPEND ll1 ll2 = ll1)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ~LFINITE ll2 /\  ?ll3. ll1 = LAPPEND ll2 ll3` THEN
  ASM_SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    MESON_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll4` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LFINITE_THM, LAPPEND, LHD_THM, LTL_THM] THEN
    MESON_TAC []
  ]);


val LLENGTH_MAP = store_thm(
  "LLENGTH_MAP",
  ``!ll f. LLENGTH (LMAP f ll) = LLENGTH ll``,
  REPEAT GEN_TAC THEN Cases_on `LFINITE ll` THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
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
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC hol_ss [LLENGTH_THM, LAPPEND] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN ASM_SIMP_TAC hol_ss [],
    `LLENGTH (LAPPEND ll1 ll2) = NONE`
      by ASM_MESON_TAC [NOT_LFINITE_NO_LENGTH] THEN
    FULL_SIMP_TAC hol_ss [LFINITE_APPEND]
  ]);

val toList = new_definition(
  "toList",
  ``toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE``);

val toList_THM = store_thm(
  "toList_THM",
  ``(toList LNIL = SOME []) /\
    (!h t. toList (LCONS h t) = OPTION_MAP (CONS h) (toList t))``,
  SIMP_TAC hol_ss [toList, LFINITE_THM, LLENGTH_THM, LTAKE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC hol_ss [] THEN
  IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  ASM_SIMP_TAC hol_ss [LTAKE_THM, LHD_THM, LTL_THM]);

val fromList = new_recursive_definition{
  name = "fromList",
  def = ``(fromList [] = LNIL) /\ (fromList (h::t) = LCONS h (fromList t))``,
  rec_axiom = listTheory.list_Axiom};

val LFINITE_fromList = store_thm(
  "LFINITE_fromList",
  ``!l. LFINITE (fromList l)``,
  Induct THEN ASM_SIMP_TAC hol_ss [LFINITE_THM, fromList]);

val LLENGTH_fromList = store_thm(
  "LLENGTH_fromList",
  ``!l. LLENGTH (fromList l) = SOME (LENGTH l)``,
  Induct THEN ASM_SIMP_TAC hol_ss [LLENGTH_THM, fromList]);

val LTAKE_fromList = store_thm(
  "LTAKE_fromList",
  ``!l. LTAKE (LENGTH l) (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC hol_ss [LTAKE_THM, fromList]);

val from_toList = store_thm(
  "from_toList",
  ``!l. toList (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC hol_ss [fromList, toList_THM]);

val LFINITE_toList = store_thm(
  "LFINITE_toList",
  ``!ll. LFINITE ll ==> ?l. toList ll = SOME l``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC hol_ss [toList_THM]);

val to_fromList = store_thm(
  "to_fromList",
  ``!ll. LFINITE ll ==> (fromList (THE (toList ll)) = ll)``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC hol_ss [fromList, toList_THM] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LFINITE_toList THEN FULL_SIMP_TAC hol_ss [fromList]);


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
  SIMP_TAC hol_ss [LDROP, LTL_THM]);

val LDROP1_THM = store_thm(
  "LDROP1_THM",
  ``LDROP 1 = LTL``,
  CONV_TAC (Q.X_FUN_EQ_CONV `ll`) THEN
  SIMP_TAC hol_ss [ARITH_PROVE ``1 = SUC 0``, LDROP] THEN
  GEN_TAC THEN Cases_on `LTL ll` THEN
  SIMP_TAC hol_ss [LDROP]);


val NOT_LFINITE_TAKE = store_thm(
  "NOT_LFINITE_TAKE",
  ``!ll. ~LFINITE ll ==> !n. ?y. LTAKE n ll = SOME y``,
  SIMP_TAC hol_ss [LFINITE] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.SPEC `n`) THEN
  Cases_on `LTAKE n ll` THEN FULL_SIMP_TAC hol_ss []);

val LFINITE_TAKE = store_thm(
  "LFINITE_TAKE",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LTAKE n ll = SOME y``,
  Induct THEN SIMP_TAC hol_ss [LTAKE_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC hol_ss [LFINITE_THM, LTAKE_THM, LLENGTH_THM] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC hol_ss [] THEN
  `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC hol_ss [] THEN
  ASM_SIMP_TAC hol_ss []);

val NOT_LFINITE_DROP = store_thm(
  "NOT_LFINITE_DROP",
  ``!ll. ~LFINITE ll ==> !n. ?y. LDROP n ll = SOME y``,
  CONV_TAC (BINDER_CONV RIGHT_IMP_FORALL_CONV THENC
            SWAP_VARS_CONV) THEN
  Induct THEN SIMP_TAC hol_ss [LDROP] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  ASM_SIMP_TAC hol_ss [LFINITE_THM, LTL_THM]);

val LFINITE_DROP = store_thm(
  "LFINITE_DROP",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LDROP n ll = SOME y``,
  Induct THEN SIMP_TAC hol_ss [LDROP_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC hol_ss [LLENGTH_THM, LFINITE_THM, LDROP_THM] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC hol_ss []);

val option_case_NONE = prove(
  ``!f x y. (option_case NONE f x = SOME y) =
            (?z. (x = SOME z) /\ (f z = SOME y))``,
  REPEAT GEN_TAC THEN Cases_on `x` THEN SIMP_TAC hol_ss []);

val LTAKE_DROP = store_thm(
  "LTAKE_DROP",
  ``(!n ll:'a llist.
        ~LFINITE ll ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll)) /\
    (!n ll:'a llist.
        LFINITE ll /\ n <= THE (LLENGTH ll) ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll))``,
  CONJ_TAC THEN Induct THEN SIMP_TAC hol_ss [LTAKE_THM, LDROP_THM,
                                             fromList, LAPPEND]
  THENL [
    REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LFINITE_THM] THEN
    SIMP_TAC hol_ss [LTAKE_THM, LDROP_THM] THEN
    IMP_RES_TAC NOT_LFINITE_TAKE THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `y` ASSUME_TAC o Q.SPEC `n`) THEN
    ASM_SIMP_TAC hol_ss [fromList, LAPPEND, LCONS_11] THEN
    `y = THE (LTAKE n t)` by ASM_SIMP_TAC hol_ss [] THEN
    ELIM_TAC THEN ASM_SIMP_TAC hol_ss [],
    REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll` llist_CASES) THEN
    FULL_SIMP_TAC hol_ss [LLENGTH_THM, LTAKE_THM, LDROP_THM, LFINITE_THM] THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN
    FULL_SIMP_TAC hol_ss [] THEN
    `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC hol_ss [LFINITE_TAKE] THEN
    FULL_SIMP_TAC hol_ss [LAPPEND, fromList, LCONS_11] THEN
    `z = THE (LTAKE n t)` by ASM_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN
    `n' = THE (LLENGTH t)` by ASM_SIMP_TAC hol_ss [] THEN ELIM_TAC THEN
    ASM_SIMP_TAC hol_ss []
  ]);

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
  SIMP_TAC hol_ss [LNTH, LTL_THM, LHD_THM] THEN Induct THEN
  SIMP_TAC hol_ss [LNTH, LTL_THM, LHD_THM]);

val minP = ``(OPTION_MAP P  (LNTH n ll) = SOME T) /\
             !m. m < n ==> (OPTION_MAP P (LNTH m ll) = SOME F)``

val firstPelemAt = new_definition(
  "firstPelemAt",
  ``firstPelemAt P n ll =
       option_case F P (LNTH n ll) /\
       !m. m < n ==> (OPTION_MAP P (LNTH m ll) = SOME F)``);
val never = new_definition(
  "never",
  ``never P ll = !n. ~firstPelemAt P n ll``);

val never_THM = store_thm(
  "never_THM",
  ``(!P. never P LNIL = T) /\
    (!P h t. never P (LCONS h t) = ~P h /\ never P t)``,
  SIMP_TAC hol_ss [LNTH_THM, never, firstPelemAt] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o SIMP_RULE hol_ss [LNTH, LHD_THM] o
                 Q.SPEC `0`) THEN
    ASM_SIMP_TAC hol_ss [] THEN GEN_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE hol_ss [LNTH_THM] o
                   Q.SPEC `SUC n`) THEN ASM_SIMP_TAC hol_ss [] THEN
    Cases_on `m` THEN FULL_SIMP_TAC hol_ss [LNTH_THM, LHD_THM] THEN
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC THEN Cases_on `n` THENL [
      ASM_SIMP_TAC hol_ss [LNTH_THM],
      POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE hol_ss [LNTH_THM] o
                 Q.SPEC `n'`)
      THENL [
        ALL_TAC,
        DISJ2_TAC THEN Q.EXISTS_TAC `SUC m`
      ] THEN
      ASM_SIMP_TAC hol_ss [LNTH_THM]
    ]
  ]);

val firstPelemAt_SUC = store_thm(
  "firstPelemAt_SUC",
  ``!P n h t. firstPelemAt P (SUC n) (LCONS h t) ==> firstPelemAt P n t``,
  SIMP_TAC hol_ss [firstPelemAt, LNTH_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC hol_ss [] THEN
  FIRST_X_ASSUM (ASSUME_TAC o GEN_ALL o SIMP_RULE hol_ss [LNTH_THM] o
                 Q.SPEC `SUC q`) THEN RES_TAC);

val LFILTER = new_specification {
  consts = [{const_name = "LFILTER", fixity = Prefix}], name = "LFILTER",
  sat_thm = prove(
    ``?LFILTER.
        !P ll. LFILTER P ll = if never P ll then LNIL
                              else
                                if P (THE (LHD ll)) then
                                    LCONS (THE (LHD ll))
                                          (LFILTER P (THE (LTL ll)))
                                else
                                    LFILTER P (THE (LTL ll))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\ll. if (?n. firstPelemAt P n ll) then
                        let n = @n. firstPelemAt P n ll in
                          SOME (THE (LDROP (SUC n) ll),
                                THE (LNTH n ll))
                      else NONE` llist_Axiom)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `P`) THEN
    Cases_on `never P ll` THEN ASM_SIMP_TAC hol_ss [] THENL [
      POP_ASSUM (fn neverthm =>
        POP_ASSUM (K ALL_TAC) THEN
        POP_ASSUM (ASSUME_TAC o Q.SPEC `ll`) THEN
        ASSUME_TAC (SIMP_RULE hol_ss [never] neverthm)) THEN
      FULL_SIMP_TAC hol_ss [LHD_EQ_NONE],

      Q.SUBGOAL_THEN `?h t. ll = LCONS h t`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [
        SPOSE_NOT_THEN
         (fn th => `ll = LNIL` by ASM_MESON_TAC [llist_CASES, th]) THEN
        ELIM_TAC THEN FULL_SIMP_TAC hol_ss [never, firstPelemAt, LNTH_THM],
        ALL_TAC
      ] THEN SIMP_TAC hol_ss [LHD_THM, LTL_THM] THEN
      Cases_on `P h` THENL [
        REPEAT (FIRST_X_ASSUM (ASSUME_TAC o SIMP_RULE hol_ss [] o
                               Q.SPEC `LCONS h t`)) THEN
        Q.SUBGOAL_THEN `?n. firstPelemAt P n (LCONS h t)`
        (SUBST_ALL_TAC o EQT_INTRO) THENL [
          Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC hol_ss [firstPelemAt, LNTH_THM],
          ALL_TAC
        ] THEN RULE_ASSUM_TAC (SIMP_RULE hol_ss []) THEN
        Q.SUBGOAL_THEN `(@n. firstPelemAt P n (LCONS h t)) = 0`
        (SUBST_ALL_TAC o SIMP_RULE hol_ss []) THENL [
          SIMP_TAC hol_ss [firstPelemAt] THEN
          Q.SUBGOAL_THEN
            `!x.
               option_case F P (LNTH x (LCONS h t)) /\
               (!m. m < x ==> (OPTION_MAP P (LNTH m (LCONS h t)) = SOME F)) =
               (x = 0)`
          (fn th => SIMP_TAC hol_ss [th]) THEN
          GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC hol_ss [LNTH_THM] THEN
          STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN
          `?m. x = SUC m` by ASM_MESON_TAC [arithmeticTheory.num_CASES] THEN
          ELIM_TAC THEN
          FIRST_X_ASSUM (ASSUME_TAC o SIMP_RULE hol_ss [] o Q.SPEC `0`) THEN
          FULL_SIMP_TAC hol_ss [LNTH_THM],
          ALL_TAC
        ] THEN FULL_SIMP_TAC hol_ss [LDROP_THM, LNTH_THM] THEN
        ASM_SIMP_TAC hol_ss [LHDTL_EQ_SOME],

        (* ~ P h case *)
        FULL_SIMP_TAC hol_ss [never] THEN
        POP_ASSUM_LIST (MAP_EVERY
                        (fn th =>
                         if (is_forall (concl th)) then
                           MP_TAC (Q.SPEC `LCONS h t` th) THEN
                           ASSUME_TAC th
                         else
                           ASSUME_TAC th) o List.rev) THEN
        Q.SUBGOAL_THEN `?n. firstPelemAt P n (LCONS h t)`
        (SUBST_ALL_TAC o EQT_INTRO) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        SIMP_TAC hol_ss [] THEN
        Q.SUBGOAL_THEN `(@n. firstPelemAt P n (LCONS h t)) = n`
        (SUBST_ALL_TAC o SIMP_RULE hol_ss []) THENL [
          FULL_SIMP_TAC hol_ss [firstPelemAt] THEN
          Q.SUBGOAL_THEN
           `!x.
             option_case F P (LNTH x (LCONS h t)) /\
             (!m. m < x ==> (OPTION_MAP P (LNTH m (LCONS h t)) = SOME F)) =
             (x = n)`
          (fn th => SIMP_TAC hol_ss [th]) THEN
          GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
          REPEAT STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN
          FULL_SIMP_TAC hol_ss [optionTheory.OPTION_MAP_EQ_SOME] THEN
          `x < n \/ n < x`
            by ASM_MESON_TAC [arithmeticTheory.LESS_LESS_CASES] THEN
          RES_TAC THEN FULL_SIMP_TAC hol_ss [],
          ALL_TAC
        ] THEN SIMP_TAC hol_ss [LDROP_THM, LTAKE_THM] THEN
        `~(n = 0)` by (STRIP_TAC THEN ELIM_TAC THEN
                       FULL_SIMP_TAC hol_ss [LNTH_THM, firstPelemAt]) THEN
        POP_ASSUM (fn th =>
          `?m. n = SUC m` by
             ASM_MESON_TAC [arithmeticTheory.num_CASES, th]) THEN
        ELIM_TAC THEN REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC hol_ss [LNTH_THM] THEN
        REPEAT (FIRST_X_ASSUM (ASSUME_TAC o SPEC ``t:'a llist``)) THEN
        Q.SUBGOAL_THEN `?n. firstPelemAt P n t` (SUBST_ALL_TAC o EQT_INTRO)
        THENL [
          Q.EXISTS_TAC `m` THEN
          FULL_SIMP_TAC hol_ss [firstPelemAt, LNTH_THM] THEN
          FIRST_X_ASSUM (ACCEPT_TAC o GEN_ALL o SIMP_RULE hol_ss [LNTH_THM] o
                         Q.SPEC `SUC q`),
          ALL_TAC
        ] THEN
        FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP firstPelemAt_SUC) THEN
        RULE_ASSUM_TAC (SIMP_RULE hol_ss []) THEN
        Q.SUBGOAL_THEN `(@n. firstPelemAt P n t) = m` SUBST_ALL_TAC THENL [
          Q.SUBGOAL_THEN `!x. firstPelemAt P x t = (x = m)`
          (fn th => SIMP_TAC hol_ss [th]) THEN
          GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
          REPEAT STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN
          `x < m \/ m < x`
            by ASM_MESON_TAC [arithmeticTheory.LESS_LESS_CASES] THEN
          FULL_SIMP_TAC hol_ss [firstPelemAt,
                                optionTheory.OPTION_MAP_EQ_SOME] THEN
          RES_TAC THEN FULL_SIMP_TAC hol_ss [],
          ALL_TAC
        ] THEN
        ASM_MESON_TAC [LHDTL_EQ_SOME]
      ]
    ])};

val LFILTER_THM = store_thm(
  "LFILTER_THM",
  ``(!P. LFILTER P LNIL = LNIL) /\
    (!P h t. LFILTER P (LCONS h t) = if P h then LCONS h (LFILTER P t)
                                     else LFILTER P t)``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFILTER)) THEN
  SIMP_TAC hol_ss [never_THM, LHD_THM, LTL_THM] THEN
  Cases_on `P h` THEN ASM_SIMP_TAC hol_ss [] THEN
  Cases_on `never P t` THEN ASM_SIMP_TAC hol_ss [] THEN
  ONCE_REWRITE_TAC [LFILTER] THEN ASM_SIMP_TAC hol_ss []);

val LL_ALL = new_definition(
  "LL_ALL",
  ``LL_ALL P ll = never ($~ o P) ll``);

val LL_ALL_THM = store_thm(
  "LL_ALL_THM",
  ``(!P. LL_ALL P LNIL = T) /\
    (!P h t. LL_ALL P (LCONS h t) = P h /\ LL_ALL P t)``,
  SIMP_TAC hol_ss [LL_ALL, never_THM]);

val LFILTER_NIL = store_thm(
  "LFILTER_NIL",
  ``!P ll. LL_ALL ($~ o P) ll ==> (LFILTER P ll = LNIL)``,
  ONCE_REWRITE_TAC [LL_ALL, LFILTER] THEN
  `!P. $~ o $~ o P = P` by (GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
                            SIMP_TAC hol_ss []) THEN
  ASM_SIMP_TAC hol_ss []);

val LFILTER_APPEND = store_thm(
  "LFILTER_APPEND",
  ``!P ll1 ll2. LFINITE ll1 ==>
                (LFILTER P (LAPPEND ll1 ll2) =
                 LAPPEND (LFILTER P ll1) (LFILTER P ll2))``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC hol_ss [LAPPEND, LFILTER_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC hol_ss [LAPPEND]);

val firstPelemAt_CONS = store_thm(
  "firstPelemAt_CONS",
  ``!P n h t. firstPelemAt P n (LCONS h t) =
              (n = 0) /\ P h \/
              ?m. (n = SUC m) /\ firstPelemAt P m t /\ ~P h``,
  REPEAT GEN_TAC THEN Cases_on `n` THEN
  SIMP_TAC hol_ss [firstPelemAt, LNTH_THM] THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC hol_ss [],
      FIRST_X_ASSUM (ASSUME_TAC o SIMP_RULE hol_ss [LNTH_THM] o
                     Q.SPEC `SUC m'`) THEN RES_TAC,
      FIRST_X_ASSUM (ASSUME_TAC o SIMP_RULE hol_ss [LNTH_THM] o
                     Q.SPEC `0`) THEN RES_TAC
    ],
    REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC hol_ss [],
      Cases_on `m` THEN ASM_SIMP_TAC hol_ss [LNTH_THM]
    ]
  ]);

val LFLATTEN = new_specification {
  consts = [{const_name = "LFLATTEN", fixity = Prefix}],
  name = "LFLATTEN",
  sat_thm = prove(
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
                     let n = @n. firstPelemAt ($~ o $= LNIL) n ll
                     in
                        let nlist = THE (LNTH n ll)
                        in
                            SOME(LCONS (THE (LTL nlist))
                                       (THE (LDROP (SUC n) ll)),
                                 THE (LHD nlist))` llist_Axiom) THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `g` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `g` THEN GEN_TAC THEN
    Cases_on `LL_ALL ($= LNIL) ll` THEN ASM_SIMP_TAC hol_ss [] THENL [
      `LTL (g ll) = NONE` by ASM_SIMP_TAC hol_ss [] THEN
      ASM_MESON_TAC [LTL_EQ_NONE],
      ALL_TAC
    ] THEN
    `?h t. ll = LCONS h t` by
       (`~(ll = LNIL)` by (DISCH_THEN SUBST_ALL_TAC THEN
                           FULL_SIMP_TAC hol_ss [LL_ALL_THM]) THEN
        ASM_MESON_TAC [llist_CASES]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC hol_ss [LHD_THM, LTL_THM] THEN
    Cases_on `h = LNIL` THEN ASM_SIMP_TAC hol_ss [] THENL [
      FULL_SIMP_TAC hol_ss [LL_ALL_THM] THEN
      REPEAT (FIRST_X_ASSUM (fn th =>
                             MP_TAC (Q.SPEC `LCONS LNIL t` th) THEN
                             MP_TAC (Q.SPEC `t` th))) THEN
      ASM_SIMP_TAC hol_ss [LL_ALL_THM] THEN ELIM_TAC THEN
      POP_ASSUM (fn th =>
        `?n. firstPelemAt ($~ o $= LNIL) n t`
           by ASM_MESON_TAC [LL_ALL, never, th]) THEN
      Q.SUBGOAL_THEN
         `((@n. firstPelemAt ($~ o $= LNIL) n t) = n) /\
          ((@n. firstPelemAt ($~ o $= LNIL) n (LCONS LNIL t)) = SUC n)`
      (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [
         CONJ_TAC THENL [
           Q.SUBGOAL_THEN `!x. firstPelemAt ($~ o $= LNIL) x t = (x = n)`
           (fn th => SIMP_TAC hol_ss [th]),
           Q.SUBGOAL_THEN
             `!x. firstPelemAt ($~ o $= LNIL) x (LCONS LNIL t) = (x = SUC n)`
           (fn th => SIMP_TAC hol_ss [th])
         ] THEN
         GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC hol_ss [firstPelemAt_CONS] THEN
         STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN ELIM_TAC THEN
         FULL_SIMP_TAC hol_ss [firstPelemAt,
                               optionTheory.OPTION_MAP_EQ_SOME] THEN
         POP_ASSUM (STRIP_ASSUME_TAC o
                    MATCH_MP
                    (ARITH_PROVE ``!x y. ~(x = y) ==> x < y \/ y < x``)) THEN
         RES_TAC THEN FULL_SIMP_TAC hol_ss [],
         ALL_TAC
       ] THEN SIMP_TAC hol_ss [LDROP_THM, LNTH_THM] THEN
       MESON_TAC [LHDTL_EQ_SOME],

       (* ~(h = LNIL) *)
       FULL_SIMP_TAC hol_ss [LL_ALL_THM] THEN
       ASM_SIMP_TAC hol_ss [LHDTL_EQ_SOME] THEN
       Q.SUBGOAL_THEN
         `(@n. firstPelemAt ($~ o $= LNIL) n (LCONS h t)) = 0`
       SUBST_ALL_TAC THENL [
         Q.SUBGOAL_THEN `!x. firstPelemAt ($~ o $= LNIL) x (LCONS h t) =
                             (x = 0)`
         (fn th => SIMP_TAC hol_ss [th]) THEN
         GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC hol_ss [firstPelemAt_CONS],
         ALL_TAC
       ] THEN ASM_SIMP_TAC hol_ss [LL_ALL_THM, LNTH_THM, LDROP_THM]
     ])};


val LFLATTEN_THM = store_thm(
  "LFLATTEN_THM",
  ``(LFLATTEN LNIL = LNIL) /\
    (!tl. LFLATTEN (LCONS LNIL t) = LFLATTEN t) /\
    (!h t tl. LFLATTEN (LCONS (LCONS h t) tl) =
              LCONS h (LFLATTEN (LCONS t tl)))``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFLATTEN)) THEN
  SIMP_TAC hol_ss [LL_ALL_THM, LHD_THM, LTL_THM, LCONS_NOT_NIL] THEN
  COND_CASES_TAC THEN SIMP_TAC hol_ss [] THEN
  ONCE_REWRITE_TAC [LFLATTEN] THEN ASM_SIMP_TAC hol_ss []);

val LFLATTEN_EQ_NIL = store_thm(
  "LFLATTEN_EQ_NIL",
  ``!ll. (LFLATTEN ll = LNIL) = LL_ALL ($= LNIL) ll``,
  GEN_TAC THEN EQ_TAC THENL [
    SIMP_TAC hol_ss [LL_ALL, never] THEN
    CONV_TAC RIGHT_IMP_FORALL_CONV THEN GEN_TAC THEN
    MAP_EVERY Q.ID_SPEC_TAC [`ll`, `n`] THEN Induct THENL [
      SIMP_TAC hol_ss [firstPelemAt] THEN REPEAT STRIP_TAC THEN
      `~(ll = LNIL)` by (STRIP_TAC THEN ELIM_TAC THEN
                         FULL_SIMP_TAC hol_ss [LNTH_THM]) THEN
      POP_ASSUM (fn th =>
                 `?h t. ll = LCONS h t` by MESON_TAC [th, llist_CASES]) THEN
      ELIM_TAC THEN FULL_SIMP_TAC hol_ss [LNTH_THM] THEN
      POP_ASSUM (fn th =>
                 `?h0 t0. h = LCONS h0 t0` by MESON_TAC [th, llist_CASES]) THEN
      ELIM_TAC THEN FULL_SIMP_TAC hol_ss [LFLATTEN_THM, LCONS_NOT_NIL],

      REPEAT STRIP_TAC THEN
      `~(ll = LNIL)` by (STRIP_TAC THEN ELIM_TAC THEN
                         FULL_SIMP_TAC hol_ss [firstPelemAt, LNTH_THM]) THEN
      POP_ASSUM (fn th =>
        `?h t. ll = LCONS h t` by MESON_TAC [th, llist_CASES]) THEN
      ELIM_TAC THEN FULL_SIMP_TAC hol_ss [firstPelemAt_CONS] THEN
      POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
      FULL_SIMP_TAC hol_ss [LFLATTEN_THM] THEN ASM_MESON_TAC []
   ],
   ONCE_REWRITE_TAC [LFLATTEN] THEN SIMP_TAC hol_ss []
 ]);

val LFLATTEN_SINGLETON = store_thm(
  "LFLATTEN_SINGLETON",
  ``!h. LFLATTEN (LCONS h LNIL) = h``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LFLATTEN (LCONS ll2 LNIL)` THEN
  SIMP_TAC hol_ss [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC hol_ss [LFLATTEN_THM, LCONS_NOT_NIL, LHD_THM, LTL_THM]);

val LFLATTEN_APPEND = store_thm(
  "LFLATTEN_APPEND",
  ``!h t. LFLATTEN (LCONS h t) = LAPPEND h (LFLATTEN t)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?h t. (ll1 = LFLATTEN (LCONS h t)) /\
                                (ll2 = LAPPEND h (LFLATTEN t))` THEN
  SIMP_TAC hol_ss [] THEN REPEAT STRIP_TAC THENL [
    MESON_TAC [],
    Cases_on `h = LNIL` THENL [
      ELIM_TAC THEN SIMP_TAC hol_ss [LFLATTEN_THM, LAPPEND] THEN
      Cases_on `LL_ALL ($= LNIL) t` THENL [
        ASM_SIMP_TAC hol_ss [LFLATTEN_EQ_NIL],
        ALL_TAC
      ] THEN
      `~(LFLATTEN t = LNIL)` by ASM_SIMP_TAC hol_ss [LFLATTEN_EQ_NIL] THEN
      ASM_SIMP_TAC hol_ss [] THEN
      POP_ASSUM (fn th =>
        `?h0 t0. LFLATTEN t = LCONS h0 t0`
           by ASM_MESON_TAC [llist_CASES, th]) THEN
      ASM_SIMP_TAC hol_ss [LFLATTEN_THM, LTL_THM] THEN
      MAP_EVERY Q.EXISTS_TAC [`t0`, `LNIL`] THEN
      SIMP_TAC hol_ss [LFLATTEN_SINGLETON, LAPPEND_NIL_2ND, LFLATTEN_THM],

      (* ~(h = LNIL) *)
      POP_ASSUM (fn th =>
        `?h0 t0. h = LCONS h0 t0` by ASM_MESON_TAC [llist_CASES, th]) THEN
      ELIM_TAC THEN SIMP_TAC hol_ss [LAPPEND, LFLATTEN_THM, LCONS_NOT_NIL,
                                     LHD_THM, LTL_THM] THEN
      MESON_TAC []
    ]
  ]);

val _ = export_theory();

end;
