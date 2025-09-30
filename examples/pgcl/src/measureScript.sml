(* ========================================================================= *)
(* Create "measureTheory" setting up the theory of measure spaces            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
val () = app load
  ["bossLib", "realLib", "metisLib", "res_quanTools", "posrealLib"]
val () = quietdec := true;
*)
Theory measure
Ancestors
  combin pred_set posreal
Libs
  metisLib res_quanTools posrealLib


(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "measure"                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = Tactical.prove;

val norm_rule =
    SIMP_RULE (simpLib.++ (pureSimps.pure_ss, resq_SS))
      [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
       AND_IMP_INTRO, GSYM CONJ_ASSOC];

fun match_tac th =
    let
      val th = norm_rule th
      val (_,tm) = strip_forall (concl th)
    in
      (if is_imp tm then MATCH_MP_TAC else MATCH_ACCEPT_TAC) th
    end;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

Definition preimage_def:
   preimage (f : 'a -> 'b) s = { x | f x IN s}
End

Definition Function_def:
   Function s t = { f : 'a -> 'b | !x :: s. f x IN t }
End

Definition countable_def:
   countable s = ?f. !x : 'a. x IN s ==> ?n : num. f n = x
End

Definition finiteSum_def:
   (finiteSum (f : num -> posreal) 0 = 0) /\
   (finiteSum f (SUC n) = finiteSum f n + f n)
End

Definition sum_def:   sum f = sup (\x. ?n. finiteSum f n = x)
End

(* ------------------------------------------------------------------------- *)
(* Set systems.                                                              *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `set_system = <| carrier : 'a -> bool;
                   sets : ('a -> bool) -> bool |>`;

Definition SetSystem_def:
   SetSystem = { a : 'a set_system | !s :: (a.sets). s SUBSET a.carrier }
End

Definition BigInter_def:
   BigInter (s : 'a set_system -> bool) =
   <| carrier := BIGINTER { a.carrier | a IN s };
      sets := BIGINTER { a.sets | a IN s } |>
End

Definition IntersectionClosed_def:
   IntersectionClosed =
   { p : 'a set_system -> bool |
     !s. ~(s = {}) /\ (!a :: s. a IN SetSystem /\ p a) ==> p (BigInter s) }
End

Definition smallest_closed_def:
   smallest_closed p (a : 'a set_system) =
   <| carrier := a.carrier;
      sets :=
        BIGINTER
          { b |
            a.sets SUBSET b /\
            (!s :: b. s SUBSET a.carrier) /\
            p <| carrier := a.carrier; sets := b |> } |>
End

Definition algebra_def:
   algebra (a : 'a set_system) =
     a IN SetSystem /\
     {} IN a.sets /\
     (!s :: (a.sets). a.carrier DIFF s IN a.sets) /\
     (!s t :: (a.sets). s UNION t IN a.sets)
End

Definition sigma_algebra_def:
   sigma_algebra (a : 'a set_system) =
     algebra a /\
     !c. countable c /\ c SUBSET a.sets ==> BIGUNION c IN a.sets
End

Definition smallest_sigma_algebra_def:
   smallest_sigma_algebra (a : 'a set_system) =
   smallest_closed sigma_algebra a
End

Definition closed_cdi_def:
   closed_cdi (a : 'a set_system) =
   (!s :: (a.sets). a.carrier DIFF s IN a.sets) /\
   (!f :: Function UNIV (a.sets).
      (f 0 = {}) /\ (!n : num. f n SUBSET f (SUC n)) ==>
      BIGUNION (IMAGE f UNIV) IN a.sets) /\
   (!f :: Function UNIV (a.sets).
      (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
      BIGUNION (IMAGE f UNIV) IN a.sets)
End

Definition smallest_closed_cdi_def:
   smallest_closed_cdi (a : 'a set_system) = smallest_closed closed_cdi a
End

val smallest_closed_carrier = prove
  (``!p a. (smallest_closed p a).carrier = a.carrier``,
   RW_TAC std_ss [smallest_closed_def]);

val smallest_closed_subset = prove
  (``!p a. a.sets SUBSET (smallest_closed p a).sets``,
   RW_TAC std_ss
     [smallest_closed_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]);

(***
val smallest_closed_subset = prove
  (``!p a. smallest_closed p a IN SetSystem``,
   RW_TAC resq_ss
     [SetSystem_def, smallest_closed_def, SUBSET_DEF, IN_BIGINTER,
      GSPECIFICATION, K_THM]

);

val smallest_closed = prove
  (``!p :: IntersectionClosed. !a :: SetSystem.
       (?s. p <| carrier := a.carrier; sets := s |>) ==>
       ((smallest_closed p a).carrier = a.carrier) /\
       a.sets SUBSET (smallest_closed p a).sets /\
       p (smallest_closed p a)``,
   RW_TAC resq_ss
     [smallest_closed_def, IntersectionClosed_def, GSPECIFICATION, K_THM]
   ++

   RW_TAC std_ss [sigma_def, sigma_algebra_def, algebra_def, IN_BIGINTER,
                  GSPECIFICATION]
   ++ POP_ASSUM (fn th => MATCH_MP_TAC th ++ ASSUME_TAC th)
   ++ RW_TAC std_ss [SUBSET_DEF]
   ++ Q.PAT_ASSUM `c SUBSET x` MP_TAC
   ++ REWRITE_TAC [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]
   ++ BETA_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPEC `x`)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ Q.EXISTS_TAC `s`
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [SUBSET_DEF]);


val ALGEBRA_ALT_INTER = store_thm
  ("ALGEBRA_ALT_INTER",
   ``!a.
       algebra a =
       {} IN a /\ (!s. s IN a ==> COMPL s IN a) /\
       !s t. s IN a /\ t IN a ==> s INTER t IN a``,
   RW_TAC std_ss [algebra_def]
   ++ EQ_TAC <<
   [RW_TAC std_ss []
    ++ Know `s INTER t = COMPL (COMPL s UNION COMPL t)`
    >> RW_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_UNION]
    ++ RW_TAC std_ss [],
    RW_TAC std_ss []
    ++ Know `s UNION t = COMPL (COMPL s INTER COMPL t)`
    >> RW_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_UNION]
    ++ RW_TAC std_ss []]);

val ALGEBRA_EMPTY = store_thm
  ("ALGEBRA_EMPTY",
   ``!a. algebra a ==> {} IN a``,
   RW_TAC std_ss [algebra_def]);

val ALGEBRA_UNIV = store_thm
  ("ALGEBRA_UNIV",
   ``!a. algebra a ==> UNIV IN a``,
   RW_TAC std_ss [algebra_def]
   ++ PROVE_TAC [COMPL_EMPTY]);

val ALGEBRA_COMPL = store_thm
  ("ALGEBRA_COMPL",
   ``!a s. algebra a /\ s IN a ==> COMPL s IN a``,
   RW_TAC std_ss [algebra_def]);

val ALGEBRA_UNION = store_thm
  ("ALGEBRA_UNION",
   ``!a s t. algebra a /\ s IN a /\ t IN a ==> s UNION t IN a``,
   RW_TAC std_ss [algebra_def]);

val ALGEBRA_INTER = store_thm
  ("ALGEBRA_INTER",
   ``!a s t. algebra a /\ s IN a /\ t IN a ==> s INTER t IN a``,
   RW_TAC std_ss [ALGEBRA_ALT_INTER]);

val ALGEBRA_DIFF = store_thm
  ("ALGEBRA_DIFF",
   ``!a s t. algebra a /\ s IN a /\ t IN a ==> s DIFF t IN a``,
   PROVE_TAC [DIFF_ALT, ALGEBRA_INTER, ALGEBRA_COMPL]);

val ALGEBRA_FINITE_UNION = store_thm
  ("ALGEBRA_FINITE_UNION",
   ``!a c. algebra a /\ FINITE c /\ c SUBSET a ==> BIGUNION c IN a``,
   RW_TAC std_ss [algebra_def]
   ++ NTAC 2 (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [BIGUNION_EMPTY, BIGUNION_INSERT, INSERT_SUBSET]);

val LAMBDA_SYSTEM_EMPTY = store_thm
  ("LAMBDA_SYSTEM_EMPTY",
   ``!g0 lam. algebra g0 /\ zero_empty (g0, lam) ==> {} IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, zero_empty_def,
                  INTER_EMPTY, COMPL_EMPTY, INTER_UNIV, measure_def,
                   measurable_sets_def]
   ++ PROVE_TAC [algebra_def]);
***)

(* ------------------------------------------------------------------------- *)
(* Measure theory.                                                           *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `measure = <| carrier : 'a -> bool;
                sets : ('a -> bool) -> bool;
                mu : ('a -> bool) -> posreal |>`;

Definition zero_empty_def:
   zero_empty (m : 'a measure) = (m.mu {} = 0)
End

Definition additive_def:
   additive (m : 'a measure) =
   !s t :: (m.sets). DISJOINT s t ==> (m.mu (s UNION t) = m.mu s + m.mu t)
End

Definition countably_additive_def:
   countably_additive (m : 'a measure) =
   !f : num -> ('a -> bool).
     f IN Function UNIV m.sets /\
     (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
     BIGUNION (IMAGE f UNIV) IN m.sets ==>
     (sum (m.mu o f) = m.mu (BIGUNION (IMAGE f UNIV)))
End

Definition subadditive_def:
   subadditive (m : 'a measure) =
   !s t :: (m.sets). m.mu (s UNION t) <= m.mu s + m.mu t
End

Definition countably_subadditive_def:
   countably_subadditive (m : 'a measure) =
   !f : num -> ('a -> bool).
     f IN Function UNIV m.sets /\
     BIGUNION (IMAGE f UNIV) IN m.sets ==>
     m.mu (BIGUNION (IMAGE f UNIV)) <= sum (m.mu o f)
End

Definition increasing_def:
   increasing (m : 'a measure) =
   !s t :: (m.sets). s SUBSET t ==> m.mu s <= m.mu t
End

Definition MeasureSpace_def:
   MeasureSpace =
   { m : 'a measure |
     sigma_algebra <| carrier := m.carrier; sets := m.sets |> /\
     m.carrier IN m.sets /\
     zero_empty m /\
     countably_additive m }
End

Definition ProbabilitySpace_def:
   ProbabilitySpace =
   { m : 'a measure |
     m IN MeasureSpace /\
     (m.mu m.carrier = 1) }
End

Definition lambda_system_def:
   lambda_system (m : 'a measure) =
   { l |
     l IN m.sets /\
     !s :: (m.sets). m.mu (l INTER s) + m.mu (COMPL l INTER s) = m.mu s }
End

Definition outer_measure_space_def:
   outer_measure_space (m : 'a measure) =
   zero_empty m /\ increasing m /\ countably_subadditive m
End

Definition inf_measure_def:
   inf_measure (m : 'a measure) s =
   inf
   { r |
     ?f :: Function UNIV (m.sets).
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       s SUBSET BIGUNION (IMAGE f UNIV) /\
       (sum (m.mu o f) = r) }
End

(***
val LAMBDA_SYSTEM_COMPL = store_thm
  ("LAMBDA_SYSTEM_COMPL",
   ``!g0 lam l.
       algebra g0 /\ zero_empty (g0, lam) /\ l IN lambda_system g0 lam ==>
       COMPL l IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, zero_empty_def]
   >> PROVE_TAC [algebra_def]
   ++ RW_TAC std_ss [COMPL_COMPL]
   ++ PROVE_TAC [REAL_ADD_SYM]);

val LAMBDA_SYSTEM_INTER = store_thm
  ("LAMBDA_SYSTEM_INTER",
   ``!g0 lam l1 l2.
       algebra g0 /\ zero_empty (g0, lam) /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (l1 INTER l2) IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, zero_empty_def]
   >> PROVE_TAC [ALGEBRA_ALT_INTER]
   ++ Know
      `lam (COMPL (l1 INTER l2) INTER g) =
       lam (l2 INTER COMPL l1 INTER g) + lam (COMPL l2 INTER g)`
   >> (ONCE_REWRITE_TAC [EQ_SYM_EQ]
       ++ Know
          `l2 INTER COMPL l1 INTER g = l2 INTER (COMPL (l1 INTER l2) INTER g)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ Know `COMPL l2 INTER g = COMPL l2 INTER (COMPL (l1 INTER l2) INTER g)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ Q.PAT_ASSUM `!g. P g` MATCH_MP_TAC
       ++ PROVE_TAC [ALGEBRA_ALT_INTER])
   ++ Know `lam (l2 INTER g) + lam (COMPL l2 INTER g) = lam g`
   >> PROVE_TAC []
   ++ Know
      `lam (l1 INTER l2 INTER g) + lam (l2 INTER COMPL l1 INTER g) =
       lam (l2 INTER g)`
   >> (Know `l2 INTER COMPL l1 INTER g = COMPL l1 INTER (l2 INTER g)`
       >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL]
           ++ PROVE_TAC [])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ REWRITE_TAC [INTER_ASSOC]
       ++ Q.PAT_ASSUM `!g. P g` K_TAC
       ++ Q.PAT_ASSUM `!g. P g` MATCH_MP_TAC
       ++ PROVE_TAC [ALGEBRA_ALT_INTER])
   ++ Q.SPEC_TAC (`l1 INTER l2`, `l`)
   ++ GEN_TAC
   ++ Q.SPEC_TAC (`lam (l2 INTER COMPL l1 INTER g)`, `r1`)
   ++ Q.SPEC_TAC (`lam (l INTER g)`, `r2`)
   ++ Q.SPEC_TAC (`lam (COMPL l2 INTER g)`, `r3`)
   ++ Q.SPEC_TAC (`lam (l2 INTER g)`, `r4`)
   ++ Q.SPEC_TAC (`lam g`, `r5`)
   ++ Q.SPEC_TAC (`lam (COMPL l INTER g)`, `r6`)
   ++ KILL_TAC
   ++ REAL_ARITH_TAC);

val LAMBDA_SYSTEM_ALGEBRA = store_thm
  ("LAMBDA_SYSTEM_ALGEBRA",
   ``!g0 lam.
       algebra g0 /\ zero_empty (g0, lam) ==> algebra (lambda_system g0 lam)``,
   RW_TAC std_ss [ALGEBRA_ALT_INTER, LAMBDA_SYSTEM_EMPTY, zero_empty_def,
                  LAMBDA_SYSTEM_COMPL, LAMBDA_SYSTEM_INTER]);

val LAMBDA_SYSTEM_STRONG_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_STRONG_ADDITIVE",
   ``!g0 lam g l1 l2.
       algebra g0 /\ zero_empty (g0, lam) /\ g IN g0 /\ DISJOINT l1 l2 /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (lam ((l1 UNION l2) INTER g) = lam (l1 INTER g) + lam (l2 INTER g))``,
   RW_TAC std_ss [zero_empty_def]
   ++ Know `l1 INTER g = l1 INTER ((l1 UNION l2) INTER g)`
   >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `l2 INTER g = COMPL l1 INTER ((l1 UNION l2) INTER g)`
   >> (Q.PAT_ASSUM `DISJOINT x y` MP_TAC
       ++ RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_COMPL, DISJOINT_DEF,
                         NOT_IN_EMPTY]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ Know `(l1 UNION l2) INTER g IN g0`
   >> (Suff `l1 IN g0 /\ l2 IN g0`
       >> PROVE_TAC [algebra_def, ALGEBRA_ALT_INTER]
       ++ !! (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `l1 IN x` MP_TAC
   ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION]);

val LAMBDA_SYSTEM_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_ADDITIVE",
   ``!g0 lam l1 l2.
       algebra g0 /\ zero_empty (g0, lam) ==>
       additive (lambda_system g0 lam, lam)``,
   RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   ++ MP_TAC (Q.SPECL [`g0`, `lam`, `UNIV`, `s`, `t`]
              LAMBDA_SYSTEM_STRONG_ADDITIVE)
   ++ RW_TAC std_ss [INTER_UNIV, ALGEBRA_UNIV]);

val COUNTABLY_SUBADDITIVE_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE_SUBADDITIVE",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ countably_subadditive m ==>
       subadditive m``,
   RW_TAC std_ss [countably_subadditive_def, subadditive_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >> (Suff
       `IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV =
        {s; t; {}}`
       >> (RW_TAC std_ss [BIGUNION, EXTENSION, IN_INSERT, GSPECIFICATION]
           ++ RW_TAC std_ss [GSYM EXTENSION]
           ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_UNION]
           ++ PROVE_TAC [NOT_IN_EMPTY])
       ++ RW_TAC arith_ss [EXTENSION, IN_IMAGE, IN_INSERT, IN_UNIV]
       ++ RW_TAC std_ss [GSYM EXTENSION]
       ++ RW_TAC std_ss [NOT_IN_EMPTY]
       ++ KILL_TAC
       ++ EQ_TAC >> PROVE_TAC []
       ++ Know `~(0:num = 1) /\ ~(0:num = 2) /\ ~(1:num = 2)` >> DECIDE_TAC
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Know
      `(measure m o (\n. (if n = 0 then s else (if n = 1 then t else {})))) sums
       (measure m s + measure m t)`
   >> (Know
       `measure m s + measure m t =
        sum (0,2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >> (ASM_SIMP_TAC bool_ss [TWO, sum, ONE, o_DEF]
           ++ RW_TAC arith_ss []
           ++ RW_TAC real_ss [])
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC arith_ss [o_DEF]
       ++ PROVE_TAC [zero_empty_def])
   ++ REWRITE_TAC [SUMS_EQ]
   ++ DISCH_THEN (REWRITE_TAC o CONJUNCTS)
   ++ DISCH_THEN MATCH_MP_TAC
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `algebra a` MP_TAC
       ++ BasicProvers.NORM_TAC std_ss [IN_FUNSET, IN_UNIV, algebra_def])
   ++ PROVE_TAC [algebra_def]);

val SIGMA_ALGEBRA_ALT = store_thm
  ("SIGMA_ALGEBRA_ALT",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> a) ==> BIGUNION (IMAGE f UNIV) IN a)``,
   RW_TAC std_ss [sigma_algebra_def]
   ++ EQ_TAC
   >> (RW_TAC std_ss [countable_def, IN_FUNSET, IN_UNIV]
       ++ Q.PAT_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       ++ REVERSE (RW_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV])
       >> PROVE_TAC []
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [COUNTABLE_ALT]
   >> PROVE_TAC [ALGEBRA_FINITE_UNION]
   ++ Q.PAT_ASSUM `!f. P f` (MP_TAC o Q.SPEC `\n. enumerate c n`)
   ++ RW_TAC std_ss' [IN_UNIV, IN_FUNSET]
   ++ Know `BIGUNION c = BIGUNION (IMAGE (enumerate c) UNIV)`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
       ++ Suff `!s. s IN c = ?n. (enumerate c n = s)` >> PROVE_TAC []
       ++ Q.PAT_ASSUM `BIJ x y z` MP_TAC
       ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ Strip
   ++ Suff `enumerate c n IN c` >> PROVE_TAC [SUBSET_DEF]
   ++ Q.PAT_ASSUM `BIJ i j k` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]);

val SIGMA_ALGEBRA_ALT_MONO = store_thm
  ("SIGMA_ALGEBRA_ALT_MONO",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> a) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. BIGUNION (IMAGE f (count n))`)
   ++ RW_TAC std_ss [IN_UNIV, IN_FUNSET]
   ++ Know
      `BIGUNION (IMAGE f UNIV) =
       BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV)`
   >> (KILL_TAC
       ++ ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV]
       ++ EQ_TAC
       >> (RW_TAC std_ss []
           ++ Q.EXISTS_TAC `BIGUNION (IMAGE f (count (SUC x')))`
           ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
           ++ PROVE_TAC [prim_recTheory.LESS_SUC_REFL])
       ++ RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ REVERSE (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_COUNT, IN_IMAGE,
                              COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY])
   >> (Q.EXISTS_TAC `f x'`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `x'`
       ++ DECIDE_TAC)
   ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
   ++ POP_ASSUM MP_TAC
   ++ REVERSE (RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE])
   >> PROVE_TAC []
   ++ MATCH_MP_TAC IMAGE_FINITE
   ++ RW_TAC std_ss [FINITE_COUNT]);

val SIGMA_ALGEBRA_ALT_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_ALT_DISJOINT",
   ``!a.
       sigma_algebra a =
       algebra a /\
       (!f.
          f IN (UNIV -> a) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN a)``,
   Strip
   ++ EQ_TAC >> RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALT_MONO, IN_FUNSET, IN_UNIV]
   ++ Q.PAT_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `\n. f (SUC n) DIFF f n`)
   ++ RW_TAC std_ss []
   ++ Know
      `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE (\n. f (SUC n) DIFF f n) UNIV)`
   >> (POP_ASSUM K_TAC
       ++ ONCE_REWRITE_TAC [EXTENSION]
       ++ RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_DIFF]
       ++ REVERSE EQ_TAC
       >> (RW_TAC std_ss []
           ++ POP_ASSUM MP_TAC
           ++ RW_TAC std_ss [IN_DIFF]
           ++ PROVE_TAC [])
       ++ RW_TAC std_ss []
       ++ Induct_on `x'` >> RW_TAC std_ss [NOT_IN_EMPTY]
       ++ RW_TAC std_ss []
       ++ Cases_on `x IN f x'` >> PROVE_TAC []
       ++ Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       ++ RW_TAC std_ss [EXTENSION, IN_DIFF]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> RW_TAC std_ss [ALGEBRA_DIFF]
   ++ HO_MATCH_MP_TAC TRANSFORM_2D_NUM
   ++ CONJ_TAC >> PROVE_TAC [DISJOINT_SYM]
   ++ RW_TAC arith_ss []
   ++ Suff `f (SUC m) SUBSET f (m + n)`
   >> (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
                      IN_INTER, IN_DIFF, SUBSET_DEF]
       ++ PROVE_TAC [])
   ++ Cases_on `n` >> PROVE_TAC [ADD_CLAUSES]
   ++ POP_ASSUM K_TAC
   ++ Know `m + SUC n' = SUC m + n'` >> DECIDE_TAC
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Induct_on `n'` >> RW_TAC arith_ss [SUBSET_REFL]
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `f (SUC m + n')`
   ++ PROVE_TAC [ADD_CLAUSES]);

val SUBADDITIVE = store_thm
  ("SUBADDITIVE",
   ``!m s t u.
       subadditive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       (u = s UNION t) ==>
       measure m u <= measure m s + measure m t``,
   RW_TAC std_ss [subadditive_def]);

val ADDITIVE = store_thm
  ("ADDITIVE",
   ``!m s t u.
       additive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss [additive_def]);

val COUNTABLY_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE",
   ``!m f s.
       countably_subadditive m /\ f IN (UNIV -> measurable_sets m) /\
       summable (measure m o f) /\ (s = BIGUNION (IMAGE f UNIV)) /\
       (s IN measurable_sets m) ==>
       measure m s <= suminf (measure m o f)``,
   PROVE_TAC [countably_subadditive_def]);

val ADDITIVE_SUM = store_thm
  ("ADDITIVE_SUM",
   ``!m f n.
       algebra (measurable_sets m) /\ zero_empty m /\ additive m /\
       f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (measure m o f) =
        measure m (BIGUNION (IMAGE f (count n))))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Induct_on `n`
   >> (RW_TAC std_ss [sum, COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY]
       ++ PROVE_TAC [zero_empty_def])
   ++ RW_TAC std_ss [sum, COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, ADD_CLAUSES,
                     o_DEF]
   ++ MATCH_MP_TAC EQ_SYM
   ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [DISJOINT_COUNT]
   ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ PROVE_TAC [FINITE_COUNT, IMAGE_FINITE]);

val INCREASING_ADDITIVE_SUMMABLE = store_thm
  ("INCREASING_ADDITIVE_SUMMABLE",
   ``!m f.
       algebra (measurable_sets m) /\ zero_empty m /\ increasing m /\
       additive m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       summable (measure m o f)``,
   RW_TAC std_ss [increasing_def]
   ++ MATCH_MP_TAC POS_SUMMABLE
   ++ CONJ_TAC
   >> (RW_TAC std_ss [o_DEF]
       ++ PROVE_TAC [zero_empty_def, IN_FUNSET, IN_UNIV])
   ++ Q.EXISTS_TAC `measure m UNIV`
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`m`, `f`, `n`] ADDITIVE_SUM)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Q.PAT_ASSUM `!(s : 'a -> bool). P s` MATCH_MP_TAC
   ++ RW_TAC std_ss [ALGEBRA_UNIV, SUBSET_DEF, IN_UNIV]
   ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
   ++ Q.PAT_ASSUM `f IN x` MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE]
   ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT]);

val LAMBDA_SYSTEM_ZERO_EMPTY = store_thm
  ("LAMBDA_SYSTEM_ZERO_EMPTY",
   ``!g0 lam. zero_empty (g0, lam) ==> zero_empty (lambda_system g0 lam, lam)``,
   RW_TAC std_ss [zero_empty_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_INCREASING = store_thm
  ("LAMBDA_SYSTEM_INCREASING",
   ``!g0 lam. increasing (g0, lam) ==> increasing (lambda_system g0 lam, lam)``,
   RW_TAC std_ss [increasing_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_STRONG_SUM = store_thm
  ("LAMBDA_SYSTEM_STRONG_SUM",
   ``!g0 lam g f n.
       algebra g0 /\ zero_empty (g0, lam) /\ g IN g0 /\
       f IN (UNIV -> lambda_system g0 lam) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (lam o (\s. s INTER g) o f) =
        lam (BIGUNION (IMAGE f (count n)) INTER g))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Induct_on `n`
   >> (RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, sum, INTER_EMPTY]
       ++ PROVE_TAC [zero_empty_def, measure_def])
   ++ RW_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, sum, o_DEF]
   ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
   ++ MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC LAMBDA_SYSTEM_STRONG_ADDITIVE
   ++ Q.EXISTS_TAC `g0`
   ++ RW_TAC std_ss [DISJOINT_COUNT]
   ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, LAMBDA_SYSTEM_ALGEBRA]
   ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT]);

val SIGMA_ALGEBRA_ALGEBRA = store_thm
  ("SIGMA_ALGEBRA_ALGEBRA",
   ``!a. sigma_algebra a ==> algebra a``,
   PROVE_TAC [sigma_algebra_def]);

val OUTER_MEASURE_SPACE_ZERO_EMPTY = store_thm
  ("OUTER_MEASURE_SPACE_ZERO_EMPTY",
   ``!m. outer_measure_space m ==> zero_empty m``,
   PROVE_TAC [outer_measure_space_def]);

val LAMBDA_SYSTEM_CARATHEODORY = store_thm
  ("LAMBDA_SYSTEM_CARATHEODORY",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (gsig, lam) ==>
       (!f.
          f IN (UNIV -> lambda_system gsig lam) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN lambda_system gsig lam /\
          ((lam o f) sums lam (BIGUNION (IMAGE f UNIV))))``,
   NTAC 5 STRIP_TAC
   ++ Know `summable (lam o f)`
   >> (Suff `summable (measure (lambda_system gsig lam, lam) o f)`
       >> RW_TAC std_ss [measure_def]
       ++ MATCH_MP_TAC INCREASING_ADDITIVE_SUMMABLE
       ++ REWRITE_TAC [measurable_sets_def]
       ++ CONJ_TAC
       >> (MATCH_MP_TAC LAMBDA_SYSTEM_ALGEBRA
           ++ CONJ_TAC >> PROVE_TAC [sigma_algebra_def]
           ++ PROVE_TAC [outer_measure_space_def])
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_ZERO_EMPTY, outer_measure_space_def]
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_INCREASING, outer_measure_space_def]
       ++ CONJ_TAC
       >> PROVE_TAC [LAMBDA_SYSTEM_ADDITIVE, outer_measure_space_def,
                     sigma_algebra_def]
       ++ RW_TAC std_ss [])
   ++ STRIP_TAC
   ++ Know `BIGUNION (IMAGE f UNIV) IN gsig`
   >> (Q.PAT_ASSUM `sigma_algebra gsig` MP_TAC
       ++ Q.PAT_ASSUM `f IN s` MP_TAC
       ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALT, IN_FUNSET, IN_UNIV]
       ++ POP_ASSUM MATCH_MP_TAC
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` MP_TAC
       ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   ++ STRIP_TAC
   ++ Suff
      `!g l.
         g IN gsig /\ (BIGUNION (IMAGE f (UNIV : num -> bool)) = l) ==>
         (lam (l INTER g) + lam (COMPL l INTER g) = lam g) /\
         (lam (l INTER g) = suminf (lam o (\s. s INTER g) o f))`
   >> (RW_TAC std_ss [lambda_system_def, GSPECIFICATION, SUMS_EQ]
       ++ POP_ASSUM
          (MP_TAC o Q.SPEC `BIGUNION (IMAGE (f : num -> 'a -> bool) UNIV)`)
       ++ RW_TAC std_ss [INTER_IDEMPOT]
       ++ Suff `(\s. s INTER BIGUNION (IMAGE f UNIV)) o f = f`
       >> RW_TAC std_ss []
       ++ KILL_TAC
       ++ FUN_EQ_TAC
       ++ RW_TAC std_ss [o_DEF, EXTENSION, IN_INTER, IN_BIGUNION,
                         GSPECIFICATION, IN_IMAGE, IN_UNIV]
       ++ PROVE_TAC [])
   ++ !! GEN_TAC
   ++ STRIP_TAC
   ++ Know `summable (lam o (\s. s INTER g) o f)`
   >> (MATCH_MP_TAC SER_COMPAR
       ++ Q.EXISTS_TAC `lam o f`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC arith_ss [o_DEF]
       ++ Q.PAT_ASSUM `outer_measure_space (gsig, lam)` MP_TAC
       ++ RW_TAC std_ss [outer_measure_space_def, increasing_def, zero_empty_def,
                         measure_def, measurable_sets_def]
       ++ Know `f n IN gsig`
       >> (Q.PAT_ASSUM `f IN x` MP_TAC
           ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, lambda_system_def,
                             GSPECIFICATION])
       ++ STRIP_TAC
       ++ Know `f n INTER g IN gsig`
       >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
       ++ STRIP_TAC
       ++ Know `0 <= lam (f n INTER g)` >> PROVE_TAC []
       ++ RW_TAC std_ss [abs]
       ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
       ++ RW_TAC std_ss [SUBSET_DEF, IN_INTER])
   ++ STRIP_TAC
   ++ Suff
      `lam g <= lam (l INTER g) + lam (COMPL l INTER g) /\
       lam (l INTER g) <= suminf (lam o (\s. s INTER g) o f) /\
       suminf (lam o (\s. s INTER g) o f) + lam (COMPL l INTER g) <= lam g`
   >> REAL_ARITH_TAC
   ++ Strip <<
   [Know `lam = measure (gsig, lam)` >> RW_TAC std_ss [measure_def]
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC SUBADDITIVE
    ++ REWRITE_TAC [measurable_sets_def]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC COUNTABLY_SUBADDITIVE_SUBADDITIVE
        ++ REWRITE_TAC [measurable_sets_def]
        ++ PROVE_TAC [outer_measure_space_def, sigma_algebra_def])
    ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
    ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def, ALGEBRA_COMPL]
    ++ RW_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_COMPL,
                      IN_UNION]
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `f IN (x -> y)` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV]
    ++ Know `lam = measure (gsig, lam)` >> RW_TAC std_ss [measure_def]
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC COUNTABLY_SUBADDITIVE
    ++ REWRITE_TAC [measurable_sets_def, measure_def]
    ++ CONJ_TAC >> PROVE_TAC [outer_measure_space_def]
    ++ CONJ_TAC
    >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_DEF]
        ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
        ++ RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        ++ PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def])
    ++ CONJ_TAC >> PROVE_TAC []
    ++ CONJ_TAC
    >> (RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
                       o_DEF]
        ++ REVERSE EQ_TAC >> PROVE_TAC []
        ++ RW_TAC std_ss [GSYM EXTENSION]
        ++ Q.EXISTS_TAC `f x' INTER g`
        ++ RW_TAC std_ss [IN_INTER]
        ++ PROVE_TAC [])
    ++ PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def],
    Suff `suminf (lam o (\s. s INTER g) o f) <= lam g - lam (COMPL l INTER g)`
    >> REAL_ARITH_TAC
    ++ MATCH_MP_TAC SUMMABLE_LE
    ++ CONJ_TAC >> PROVE_TAC []
    ++ GEN_TAC
    ++ MP_TAC (Q.SPECL [`gsig`, `lam`, `g`, `f`, `n`] LAMBDA_SYSTEM_STRONG_SUM)
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA, OUTER_MEASURE_SPACE_ZERO_EMPTY]
    ++ POP_ASSUM K_TAC
    ++ Suff
       `(lam g = lam (BIGUNION (IMAGE f (count n)) INTER g) +
                 lam (COMPL (BIGUNION (IMAGE f (count n))) INTER g)) /\
        lam (COMPL (BIGUNION (IMAGE f UNIV)) INTER g) <=
        lam (COMPL (BIGUNION (IMAGE f (count n))) INTER g)`
    >> REAL_ARITH_TAC
    ++ CONJ_TAC
    >> (Suff `BIGUNION (IMAGE f (count n)) IN lambda_system gsig lam`
        >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
        ++ Q.PAT_ASSUM `f IN (x -> y)` MP_TAC
        ++ RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, IN_IMAGE]
        ++ PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                      OUTER_MEASURE_SPACE_ZERO_EMPTY, IMAGE_FINITE, FINITE_COUNT])
    ++ Q.PAT_ASSUM `outer_measure_space (gsig, lam)` MP_TAC
    ++ RW_TAC std_ss [outer_measure_space_def, increasing_def, measure_def,
                      measurable_sets_def]
    ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
    ++ CONJ_TAC
    >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_COMPL, ALGEBRA_INTER]
    ++ CONJ_TAC
    >> (Know `algebra gsig` >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA]
        ++ STRIP_TAC
        ++ MATCH_MP_TAC ALGEBRA_INTER
        ++ RW_TAC std_ss []
        ++ MATCH_MP_TAC ALGEBRA_COMPL
        ++ RW_TAC std_ss []
        ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
        ++ Q.PAT_ASSUM `f IN x` MP_TAC
        ++ RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, lambda_system_def,
                          GSPECIFICATION, IN_IMAGE]
        ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
    ++ RW_TAC std_ss [SUBSET_DEF, IN_INTER, IN_COMPL, IN_IMAGE, IN_BIGUNION,
                      IN_UNIV]
    ++ PROVE_TAC []]);

val CARATHEODORY_LEMMA = store_thm
  ("CARATHEODORY_LEMMA",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (gsig, lam) ==>
       measure_space (lambda_system gsig lam, lam)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`gsig`, `lam`] LAMBDA_SYSTEM_CARATHEODORY)
   ++ RW_TAC std_ss [measure_space_def, countably_additive_def,
                     measurable_sets_def, measure_def] <<
   [RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT]
    ++ PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                  outer_measure_space_def],
    PROVE_TAC [outer_measure_space_def, LAMBDA_SYSTEM_ZERO_EMPTY]]);

val INF_MEASURE_NONEMPTY = store_thm
  ("INF_MEASURE_NONEMPTY",
   ``!m g s.
       algebra (measurable_sets m) /\ zero_empty m /\ s IN measurable_sets m /\
       g SUBSET s ==>
       measure m s IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r}``,
   RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, zero_empty_def]
   ++ Q.EXISTS_TAC `\n. if n = 0 then s else {}`
   ++ BasicProvers.NORM_TAC std_ss
      [SUBSET_DEF, IN_BIGUNION, DISJOINT_EMPTY,
       IN_IMAGE, IN_UNIV, o_DEF, IN_FUNSET, ALGEBRA_EMPTY]
   >> PROVE_TAC []
   ++ Know `measure m s = sum (0,1) (\x. measure m (if x = 0 then s else {}))`
   >> (ASM_SIMP_TAC bool_ss [sum, ONE, REAL_ADD_LID] ++ RW_TAC arith_ss [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC SER_0
   ++ RW_TAC arith_ss []);

val INF_MEASURE_POS0 = store_thm
  ("INF_MEASURE_POS0",
   ``!m g x.
       algebra (measurable_sets m) /\ zero_empty m /\
       x IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} ==>
       0 <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV, zero_empty_def]
   ++ MATCH_MP_TAC SER_POS
   ++ RW_TAC std_ss [o_DEF]);

val INF_MEASURE_POS = store_thm
  ("INF_MEASURE_POS",
   ``!m g. algebra (measurable_sets m) /\ zero_empty m ==> 0 <= inf_measure m g``,
   RW_TAC std_ss [GSPECIFICATION, inf_measure_def]
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m UNIV`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [SUBSET_UNIV, ALGEBRA_UNIV]
       ++ PROVE_TAC [zero_empty_def])
   ++ ho_PROVE_TAC [INF_MEASURE_POS0]);

val INCREASING = store_thm
  ("INCREASING",
   ``!m s t.
       increasing m /\ s SUBSET t /\ s IN measurable_sets m /\
       t IN measurable_sets m ==>
       measure m s <= measure m t``,
   PROVE_TAC [increasing_def]);

val ADDITIVE_INCREASING = store_thm
  ("ADDITIVE_INCREASING",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ additive m ==>
       increasing m``,
   RW_TAC std_ss [increasing_def, zero_empty_def]
   ++ Suff
      `?u. u IN measurable_sets m /\ (measure m t = measure m s + measure m u)`
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `u`)
       ++ RW_TAC std_ss []
       ++ NTAC 2 (POP_ASSUM MP_TAC)
       ++ REAL_ARITH_TAC)
   ++ Q.EXISTS_TAC `t DIFF s`
   ++ STRONG_CONJ_TAC >> PROVE_TAC [ALGEBRA_DIFF]
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [DISJOINT_DEF, IN_DIFF, IN_UNION, EXTENSION, IN_INTER,
                     NOT_IN_EMPTY]
   ++ PROVE_TAC [SUBSET_DEF]);

val COUNTABLY_ADDITIVE_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE_ADDITIVE",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ countably_additive m ==>
       additive m``,
   RW_TAC std_ss [additive_def, zero_empty_def, countably_additive_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_UNION]
       ++ EQ_TAC >> PROVE_TAC [NOT_IN_EMPTY]
       ++ Know `~(1 = (0:num))` >> DECIDE_TAC
       ++ RW_TAC std_ss [] >> PROVE_TAC []
       ++ Q.EXISTS_TAC `t`
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `1`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, ALGEBRA_UNION]
   ++ Suff
      `measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       (measure m s + measure m t) /\
       measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       measure m (s UNION t)`
   >> PROVE_TAC [SUM_UNIQ]
   ++ CONJ_TAC
   >> (Know
       `measure m s + measure m t =
        sum (0, 2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >> (ASM_SIMP_TAC bool_ss [TWO, ONE, sum]
           ++ RW_TAC std_ss []
           ++ RW_TAC arith_ss [REAL_ADD_LID, o_THM])
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC arith_ss [o_THM])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_EMPTY]
   ++ RW_TAC std_ss [DISJOINT_EMPTY]
   ++ PROVE_TAC [DISJOINT_SYM]);

val COUNTABLY_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE",
   ``!m s f.
       countably_additive m /\ f IN (UNIV -> measurable_sets m)
       /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   ++ PROVE_TAC [countably_additive_def]);

val INF_MEASURE_AGREES = store_thm
  ("INF_MEASURE_AGREES",
   ``!m s.
       algebra (measurable_sets m) /\ zero_empty m /\ countably_additive m /\
       s IN measurable_sets m ==>
       (inf_measure m s = measure m s)``,
   RW_TAC std_ss [inf_measure_def]
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ CONJ_TAC
   >> (MATCH_MP_TAC INF_LE
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `0`
           ++ ho_PROVE_TAC [INF_MEASURE_POS0])
       ++ Q.EXISTS_TAC `measure m s`
       ++ REVERSE CONJ_TAC >> RW_TAC std_ss [REAL_LE_REFL]
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [SUBSET_REFL])
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m s`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [SUBSET_REFL])
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_FUNSET, IN_UNIV,
                     IN_BIGUNION, IN_IMAGE, SUMS_EQ]
   ++ MP_TAC (Q.SPECL [`m`] countably_additive_def)
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(\g. g INTER s) o f`)
   ++ Know `BIGUNION (IMAGE ((\g. g INTER s) o f) UNIV) = s`
   >> (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_INTER, o_THM]
       ++ EQ_TAC >> PROVE_TAC []
       ++ RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
       ++ RW_TAC std_ss [IN_UNIV]
       ++ Q.EXISTS_TAC `s INTER f x'`
       ++ RW_TAC std_ss [IN_INTER]
       ++ PROVE_TAC [EXTENSION])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [o_THM, IN_FUNSET, IN_UNIV, IN_INTER]
   ++ Suff `measure m o (\g. g INTER s) o f sums measure m s`
   >> (RW_TAC std_ss [SUMS_EQ]
       ++ POP_ASSUM (REWRITE_TAC o wrap o GSYM)
       ++ MATCH_MP_TAC SER_LE
       ++ RW_TAC std_ss [o_THM]
       ++ MATCH_MP_TAC INCREASING
       ++ RW_TAC std_ss [ALGEBRA_INTER, INTER_SUBSET]
       ++ MATCH_MP_TAC ADDITIVE_INCREASING
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
       ++ RW_TAC std_ss [])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> PROVE_TAC [ALGEBRA_INTER]
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m'`, `n`])
   ++ RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION]
   ++ PROVE_TAC []);

val MEASURE_DOWN = store_thm
  ("MEASURE_DOWN",
   ``!m0 m1.
       sigma_algebra (measurable_sets m0) /\
       measurable_sets m0 SUBSET measurable_sets m1 /\
       (measure m0 = measure m1) /\ measure_space m1 ==>
       measure_space m0``,
   RW_TAC std_ss [measure_space_def, zero_empty_def, SUBSET_DEF,
                  countably_additive_def, IN_FUNSET, IN_UNIV]);

val SIGMA_ALGEBRA_SIGMA_CLOSE = store_thm
  ("SIGMA_ALGEBRA_SIGMA_CLOSE",
   ``!b. sigma_algebra (sigma_close b)``,
   RW_TAC std_ss [sigma_def, sigma_algebra_def, algebra_def, IN_BIGINTER,
                  GSPECIFICATION]
   ++ POP_ASSUM (fn th => MATCH_MP_TAC th ++ ASSUME_TAC th)
   ++ RW_TAC std_ss [SUBSET_DEF]
   ++ Q.PAT_ASSUM `c SUBSET x` MP_TAC
   ++ REWRITE_TAC [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]
   ++ BETA_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPEC `x`)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ Q.EXISTS_TAC `s`
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [SUBSET_DEF]);

val UNIV_ALGEBRA = store_thm
  ("UNIV_ALGEBRA",
   ``algebra UNIV``,
   RW_TAC std_ss [algebra_def, IN_UNIV]);

val UNIV_SIGMA_ALGEBRA = store_thm
  ("UNIV_SIGMA_ALGEBRA",
   ``sigma_algebra UNIV``,
   RW_TAC std_ss [sigma_algebra_def, IN_UNIV, UNIV_ALGEBRA]);

val INF_MEASURE_EMPTY = store_thm
  ("INF_MEASURE_EMPTY",
   ``!m. algebra (measurable_sets m) /\ zero_empty m ==> (inf_measure m {} = 0)``,
   RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ REVERSE CONJ_TAC >> PROVE_TAC [INF_MEASURE_POS]
   ++ RW_TAC std_ss [inf_measure_def]
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC >> ho_PROVE_TAC [INF_MEASURE_POS0]
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   ++ Q.EXISTS_TAC `K {}`
   ++ RW_TAC bool_ss [IN_FUNSET, IN_UNIV, ALGEBRA_EMPTY, DISJOINT_EMPTY, K_THM,
                      SUBSET_DEF, NOT_IN_EMPTY, IN_BIGUNION, IN_IMAGE]
   ++ Know `0 = sum (0, 0) (measure m o K {})` >> RW_TAC std_ss [sum]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC SER_0
   ++ RW_TAC std_ss [K_THM, o_THM]
   ++ PROVE_TAC [zero_empty_def]);

val INF_MEASURE_ZERO_EMPTY = store_thm
  ("INF_MEASURE_ZERO_EMPTY",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m ==>
       zero_empty (UNIV, inf_measure m)``,
   RW_TAC std_ss [zero_empty_def, INF_MEASURE_EMPTY, INF_MEASURE_POS,
                  measure_def]);

val INF_MEASURE_INCREASING = store_thm
  ("INF_MEASURE_INCREASING",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m ==>
       increasing (UNIV, inf_measure m)``,
   RW_TAC std_ss [increasing_def, inf_measure_def, IN_UNIV, measure_def]
   ++ MATCH_MP_TAC LE_INF
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `measure m UNIV`
       ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
       ++ RW_TAC std_ss [ALGEBRA_UNIV, SUBSET_UNIV])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `0`
       ++ ho_PROVE_TAC [INF_MEASURE_POS0])
   ++ Q.EXISTS_TAC `x`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   ++ PROVE_TAC [SUBSET_TRANS]);

val INF_MEASURE_LE = store_thm
  ("INF_MEASURE_LE",
   ``!m s x.
       algebra (measurable_sets m) /\ zero_empty m /\ increasing m /\
       x IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          s SUBSET BIGUNION (IMAGE f UNIV) /\
          measure m o f sums r} ==>
       inf_measure m s <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV]
   ++ RW_TAC std_ss [inf_measure_def]
   ++ MATCH_MP_TAC INF_LE
   ++ CONJ_TAC
   >> (Q.EXISTS_TAC `0`
       ++ ho_PROVE_TAC [INF_MEASURE_POS0])
   ++ RW_TAC std_ss [GSPECIFICATION, SUMS_EQ]
   ++ CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV THENC SWAP_EXISTS_CONV)
   ++ Q.EXISTS_TAC `\n. f n DIFF (BIGUNION (IMAGE f (count n)))`
   ++ Q.EXISTS_TAC
      `suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n)))))`
   ++ REWRITE_TAC [GSYM CONJ_ASSOC, IN_FUNSET, IN_UNIV]
   ++ BETA_TAC
   ++ STRONG_CONJ_TAC
   >> (STRIP_TAC
       ++ MATCH_MP_TAC ALGEBRA_DIFF
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC ALGEBRA_FINITE_UNION
       ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE]
       ++ PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
   ++ STRIP_TAC
   ++ Know
      `summable (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) /\
       suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) <=
       suminf (measure m o f)`
   >> (MATCH_MP_TAC SER_POS_COMPARE
       ++ RW_TAC std_ss [o_THM] >> PROVE_TAC [zero_empty_def]
       ++ MATCH_MP_TAC INCREASING
       ++ PROVE_TAC [DIFF_SUBSET])
   ++ RW_TAC std_ss [] <<
   [RW_TAC arith_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION, IN_DIFF,
                     IN_BIGUNION, IN_IMAGE, IN_COUNT]
    ++ Know `m' < n \/ n < m'` >> DECIDE_TAC
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `s SUBSET g` MP_TAC
    ++ RW_TAC arith_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV]
    ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    ++ RW_TAC std_ss []
    ++ Know `?n. x IN f n` >> PROVE_TAC []
    ++ DISCH_THEN (MP_TAC o Ho_Rewrite.REWRITE_RULE [MINIMAL_EXISTS])
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC
       `f (minimal (\n. x IN f n)) DIFF
        BIGUNION (IMAGE f (count (minimal (\n. x IN f n))))`
    ++ REVERSE CONJ_TAC >> PROVE_TAC []
    ++ RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_COUNT]
    ++ PROVE_TAC []]);

val INF_MEASURE_CLOSE = store_thm
  ("INF_MEASURE_CLOSE",
   ``!m s e.
       algebra (measurable_sets m) /\ zero_empty m /\ 0 < e ==>
       ?f l.
         f IN (UNIV -> measurable_sets m) /\ s SUBSET BIGUNION (IMAGE f UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
         (measure m o f) sums l /\ l <= inf_measure m s + e``,
   RW_TAC std_ss [inf_measure_def]
   ++ Suff
      `?l.
         l IN
         {r |
          ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} /\
         l <
         inf
         {r |
          ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} + e`
   >> (RW_TAC std_ss [GSPECIFICATION]
       ++ Q.EXISTS_TAC `f`
       ++ Q.EXISTS_TAC `l`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [REAL_LT_IMP_LE])
   ++ MATCH_MP_TAC INF_CLOSE
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `measure m UNIV`
   ++ MATCH_MP_TAC INF_MEASURE_NONEMPTY
   ++ RW_TAC std_ss [ALGEBRA_UNIV, SUBSET_UNIV]);

val INF_MEASURE_COUNTABLY_SUBADDITIVE = store_thm
  ("INF_MEASURE_COUNTABLY_SUBADDITIVE",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ increasing m ==>
       countably_subadditive (UNIV, inf_measure m)``,
   RW_TAC std_ss [countably_subadditive_def, IN_FUNSET, IN_UNIV]
   ++ MATCH_MP_TAC REAL_LE_EPSILON
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Know
      `!n. ?g l.
         g IN (UNIV -> measurable_sets m) /\
         f n SUBSET BIGUNION (IMAGE g UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
         (measure m o g) sums l /\
         l <= inf_measure m (f n) + e * (1 / 2) pow (n + 1)`
   >> (STRIP_TAC
       ++ MATCH_MP_TAC INF_MEASURE_CLOSE
       ++ PROVE_TAC [REAL_LT_MUL, POW_HALF_POS])
   ++ CONV_TAC (REDEPTH_CONV (CHANGED_CONV SKOLEM_CONV))
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `suminf l`
   ++ Know `!n. 0 <= l n`
   >> (RW_TAC std_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUMS_EQ]
       ++ Q.PAT_ASSUM `a = b` (REWRITE_TAC o wrap o GSYM)
       ++ MATCH_MP_TAC SUMINF_POS
       ++ RW_TAC std_ss [o_THM]
       ++ PROVE_TAC [zero_empty_def])
   ++ STRIP_TAC
   ++ Know
      `summable l /\
       suminf l <= suminf (\n. inf_measure m (f n)) + e`
   >> (Know `(\n. e * (1 / 2) pow (n + 1)) sums (e * 1)`
       >> (HO_MATCH_MP_TAC SER_CMUL
           ++ RW_TAC std_ss [POW_HALF_SER])
       ++ PURE_REWRITE_TAC [REAL_MUL_RID, SUMS_EQ]
       ++ STRIP_TAC
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
       ++ Know
          `summable (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)) /\
           (suminf (\n. inf_measure m (f n)) +
            suminf (\n. e * (1 / 2) pow (n + 1)) =
            suminf (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)))`
       >> (HO_MATCH_MP_TAC SUMINF_ADD
           ++ Q.PAT_ASSUM `summable (a o b)` MP_TAC
           ++ RW_TAC std_ss [o_DEF, measure_def])
       ++ STRIP_TAC
       ++ POP_ASSUM (ONCE_REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SER_POS_COMPARE
       ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss [o_DEF, measure_def]
   ++ MATCH_MP_TAC INF_MEASURE_LE
   ++ RW_TAC std_ss [GSPECIFICATION]
   ++ MP_TAC NUM_2D_BIJ_INV
   ++ STRIP_TAC
   ++ Q.EXISTS_TAC `UNCURRY g o f'`
   ++ Q.PAT_ASSUM `!n. P n /\ Q n` MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, SUBSET_DEF, IN_BIGUNION,
                     IN_IMAGE] <<
   [Cases_on `f' x`
    ++ RW_TAC std_ss [UNCURRY_DEF],
    Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `x'`)
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!n. P n` K_TAC
    ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `g x' x''`
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `BIJ a b c` MP_TAC
    ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
    ++ POP_ASSUM (MP_TAC o Q.SPEC `(x', x'')`)
    ++ RW_TAC std_ss []
    ++ Q.EXISTS_TAC `y`
    ++ RW_TAC std_ss [UNCURRY_DEF],
    Know `measure m o UNCURRY g o f' = UNCURRY (\m'. measure m o g m') o f'`
    >> (FUN_EQ_TAC
        ++ RW_TAC std_ss [o_DEF]
        ++ Cases_on `f' x`
        ++ RW_TAC std_ss [UNCURRY_DEF])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC SUMINF_2D
    ++ RW_TAC std_ss [o_THM]
    ++ PROVE_TAC [zero_empty_def]]);

val INF_MEASURE_OUTER = store_thm
  ("INF_MEASURE_OUTER",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ increasing m ==>
       outer_measure_space (UNIV, inf_measure m)``,
   RW_TAC std_ss [outer_measure_space_def, INF_MEASURE_ZERO_EMPTY,
                  INF_MEASURE_INCREASING, INF_MEASURE_COUNTABLY_SUBADDITIVE]);

val SIGMA_SUBSET = store_thm
  ("SIGMA_SUBSET",
   ``!a b. sigma_algebra b /\ a SUBSET b ==> sigma a SUBSET b``,
   RW_TAC std_ss [sigma_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION]);

val ALGEBRA_SUBSET_LAMBDA_SYSTEM = store_thm
  ("ALGEBRA_SUBSET_LAMBDA_SYSTEM",
   ``!m.
       algebra (measurable_sets m) /\ zero_empty m /\ increasing m /\
       additive m ==>
       measurable_sets m SUBSET lambda_system UNIV (inf_measure m)``,
   REVERSE (RW_TAC std_ss [SUBSET_DEF, lambda_system_def, GSPECIFICATION,
                           IN_UNIV, GSYM REAL_LE_ANTISYM])
   >> (Know `inf_measure m = measure (UNIV, inf_measure m)`
       >> RW_TAC std_ss [measure_def]
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ MATCH_MP_TAC SUBADDITIVE
       ++ RW_TAC std_ss [IN_UNIV, EXTENSION, IN_INTER, IN_COMPL, IN_UNION,
                         measurable_sets_def]
       ++ PROVE_TAC [INF_MEASURE_COUNTABLY_SUBADDITIVE,
                     INF_MEASURE_ZERO_EMPTY, UNIV_ALGEBRA,
                     COUNTABLY_SUBADDITIVE_SUBADDITIVE,
                     measurable_sets_def])
   ++ MATCH_MP_TAC REAL_LE_EPSILON
   ++ RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`m`, `g`, `e`] INF_MEASURE_CLOSE)
   ++ RW_TAC std_ss [SUMS_EQ, IN_FUNSET, IN_UNIV]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC `suminf (measure m o f)`
   ++ RW_TAC std_ss []
   ++ POP_ASSUM K_TAC
   ++ Know
      `!x.
         x IN measurable_sets m ==>
         summable (measure m o (\s. x INTER s) o f) /\
         inf_measure m (x INTER g) <= suminf (measure m o (\s. x INTER s) o f)`
   >> (NTAC 2 STRIP_TAC
       ++ STRONG_CONJ_TAC
       >> (MATCH_MP_TAC SER_COMPAR
           ++ Q.EXISTS_TAC `measure m o f`
           ++ RW_TAC std_ss [GREATER_EQ]
           ++ Q.EXISTS_TAC `0`
           ++ REVERSE (RW_TAC arith_ss [o_THM, abs])
           >> PROVE_TAC [zero_empty_def, ALGEBRA_INTER]
           ++ MATCH_MP_TAC INCREASING
           ++ RW_TAC std_ss [INTER_SUBSET, ALGEBRA_INTER])
       ++ RW_TAC std_ss [inf_measure_def]
       ++ MATCH_MP_TAC INF_LE
       ++ CONJ_TAC
       >> (Q.EXISTS_TAC `0`
           ++ ho_PROVE_TAC [INF_MEASURE_POS0])
       ++ Q.EXISTS_TAC `suminf (measure m o (\s. x' INTER s) o f)`
       ++ RW_TAC std_ss [REAL_LE_REFL, GSPECIFICATION]
       ++ Q.EXISTS_TAC `(\s. x' INTER s) o f`
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, ALGEBRA_INTER, o_THM, SUMS_EQ]
       >> (Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPECL [`m'`, `n`])
           ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
           ++ PROVE_TAC [])
       ++ Q.PAT_ASSUM `g SUBSET ss` MP_TAC
       ++ RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_INTER, IN_IMAGE,
                         IN_UNIV, o_THM]
       ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [IN_INTER])
   ++ DISCH_THEN
      (fn th => MP_TAC (Q.SPEC `x` th) ++ MP_TAC (Q.SPEC `COMPL x` th))
   ++ RW_TAC std_ss [ALGEBRA_COMPL]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC
      `suminf (measure m o (\s. x INTER s) o f) +
       suminf (measure m o (\s. (COMPL x) INTER s) o f)`
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `(a:real) <= b` MP_TAC
       ++ Q.PAT_ASSUM `(a:real) <= b` MP_TAC
       ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss [SUMINF_ADD, o_THM]
   ++ Know `!a b : real. (a = b) ==> a <= b` >> REAL_ARITH_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ MATCH_MP_TAC RAND_THM
   ++ FUN_EQ_TAC
   ++ RW_TAC std_ss [o_THM]
   ++ MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [ALGEBRA_INTER, ALGEBRA_COMPL, DISJOINT_DEF, IN_INTER,
                     IN_COMPL, NOT_IN_EMPTY, EXTENSION, IN_UNION]
   ++ PROVE_TAC []);

val CARATHEODORY = store_thm
  ("CARATHEODORY",
   ``!m0.
       algebra (measurable_sets m0) /\ zero_empty m0 /\ countably_additive m0 ==>
       ?m.
         (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
         (measurable_sets m = sigma (measurable_sets m0)) /\ measure_space m``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(sigma (measurable_sets m0), inf_measure m0)`
   ++ CONJ_TAC >> PROVE_TAC [INF_MEASURE_AGREES, measure_def]
   ++ CONJ_TAC >> RW_TAC std_ss [measurable_sets_def]
   ++ MATCH_MP_TAC MEASURE_DOWN
   ++ Q.EXISTS_TAC
      `(lambda_system UNIV (inf_measure m0), inf_measure m0)`
   ++ REWRITE_TAC [measurable_sets_def, measure_def]
   ++ STRONG_CONJ_TAC >> PROVE_TAC [SIGMA_ALGEBRA_SIGMA]
   ++ STRIP_TAC
   ++ ONCE_REWRITE_TAC [CONJ_COMM]
   ++ STRONG_CONJ_TAC
   >> (MATCH_MP_TAC CARATHEODORY_LEMMA
       ++ CONJ_TAC >> PROVE_TAC [UNIV_SIGMA_ALGEBRA]
       ++ PROVE_TAC [INF_MEASURE_OUTER, COUNTABLY_ADDITIVE_ADDITIVE,
                     ADDITIVE_INCREASING])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC SIGMA_SUBSET
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def, measurable_sets_def]
   ++ PROVE_TAC [ALGEBRA_SUBSET_LAMBDA_SYSTEM, COUNTABLY_ADDITIVE_ADDITIVE,
                 ADDITIVE_INCREASING]);
***)

(* ------------------------------------------------------------------------- *)
(* Measurable functions.                                                     *)
(* ------------------------------------------------------------------------- *)

Definition Measurable_def:
   Measurable m1 m2 = { f | !s :: (m2.sets). preimage f s IN m1.sets }
End

Definition MeasurePreserving_def:
   MeasurePreserving m1 m2 =
   { f |
     f IN Measurable m1 m2 /\
     !s :: (m2.sets). m1.mu (preimage f s) = m2.mu s }
End

(***
val SIGMA_SUBSET = store_thm
  ("SIGMA_SUBSET",
   ``!a. a SUBSET sigma a``,
   RW_TAC std_ss [sigma_def, IN_BIGINTER, SUBSET_DEF, GSPECIFICATION]);

val IN_SIGMA = store_thm
  ("IN_SIGMA",
   ``!a x. x IN a ==> x IN sigma a``,
   MP_TAC SIGMA_SUBSET
   ++ RW_TAC std_ss [SUBSET_DEF]);

val SIGMA_ALGEBRA = store_thm
  ("SIGMA_ALGEBRA",
   ``!p.
       sigma_algebra p =
       {} IN p /\ (!s. s IN p ==> COMPL s IN p) /\
       (!c. countable c /\ c SUBSET p ==> BIGUNION c IN p)``,
   RW_TAC std_ss [sigma_algebra_def, algebra_def]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!c. P c` (MP_TAC o Q.SPEC `{s; t}`)
   ++ RW_TAC std_ss [COUNTABLE_ALT, FINITE_INSERT, FINITE_EMPTY, SUBSET_DEF,
                     BIGUNION_PAIR, IN_INSERT, NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val SIGMA_PROPERTY_WEAK = store_thm
  ("SIGMA_PROPERTY_WEAK",
   ``!p a.
       {} IN p /\ a SUBSET p /\ (!s. s IN p ==> COMPL s IN p) /\
       (!c. countable c /\ c SUBSET p ==> BIGUNION c IN p) ==>
       (sigma a) SUBSET p``,
   RW_TAC std_ss [sigma_def, IN_BIGINTER, GSPECIFICATION, SUBSET_DEF]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ CONJ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss [SIGMA_ALGEBRA]
   ++ PROVE_TAC [SUBSET_DEF]);

val IN_MEASURABLE = store_thm
  ("IN_MEASURABLE",
   ``!m1 m2 f. f IN measurable a b = !s. s IN b ==> PREIMAGE f s IN a``,
   RW_TAC std_ss [measurable_def, GSPECIFICATION]);

val MEASURABLE_SIGMA = store_thm
  ("MEASURABLE_SIGMA",
   ``!f a b.
       sigma_algebra a /\ (!s. s IN b ==> PREIMAGE f s IN a) ==>
       f IN measurable a (sigma b)``,
   RW_TAC std_ss []
   ++ REWRITE_TAC [IN_MEASURABLE]
   ++ Suff `sigma b SUBSET {s | PREIMAGE f s IN a}`
   >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   ++ MATCH_MP_TAC SIGMA_PROPERTY_WEAK
   ++ RW_TAC std_ss [GSPECIFICATION, PREIMAGE_EMPTY, SUBSET_DEF, PREIMAGE_COMPL,
                     PREIMAGE_BIGUNION] <<
   [PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY],
    PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_COMPL],
    Q.PAT_ASSUM `sigma_algebra a` MP_TAC
    ++ RW_TAC std_ss [sigma_algebra_def]
    ++ POP_ASSUM MATCH_MP_TAC
    ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE]
    ++ PROVE_TAC [COUNTABLE_IMAGE]]);

val MEASURABLE_SUBSET = store_thm
  ("MEASURABLE_SUBSET",
   ``!a b. sigma_algebra a ==> measurable a b SUBSET measurable a (sigma b)``,
   RW_TAC std_ss [SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURABLE_SIGMA
   ++ PROVE_TAC [IN_MEASURABLE]);

val MEASURABLE_LIFT = store_thm
  ("MEASURABLE_LIFT",
   ``!f a b.
       sigma_algebra a /\ f IN measurable a b ==> f IN measurable a (sigma b)``,
   PROVE_TAC [MEASURABLE_SUBSET, SUBSET_DEF]);

val SIGMA_ALGEBRA_COUNTABLE_UNION = store_thm
  ("SIGMA_ALGEBRA_COUNTABLE_UNION",
   ``!a c. sigma_algebra a /\ countable c /\ c SUBSET a ==> BIGUNION c IN a``,
   PROVE_TAC [sigma_algebra_def]);

val SIGMA_ALGEBRA_ENUM = store_thm
  ("SIGMA_ALGEBRA_ENUM",
   ``!a (f : num -> ('a -> bool)).
       sigma_algebra a /\ f IN (UNIV -> a) ==> BIGUNION (IMAGE f UNIV) IN a``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT]);

val MEASURE_COMPL = store_thm
  ("MEASURE_COMPL",
   ``!m s.
       measure_space m /\ s IN measurable_sets m ==>
       (measure m (COMPL s) = measure m UNIV - measure m s)``,
   RW_TAC std_ss []
   ++ Suff `measure m UNIV = measure m s + measure m (COMPL s)`
   >> REAL_ARITH_TAC
   ++ MATCH_MP_TAC ADDITIVE
   ++ Q.PAT_ASSUM `measure_space m` MP_TAC
   ++ RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                     EXTENSION, IN_COMPL, IN_UNIV, IN_UNION, IN_INTER,
                     NOT_IN_EMPTY]
   ++ PROVE_TAC [COUNTABLY_ADDITIVE_ADDITIVE, ALGEBRA_COMPL]);

val SIGMA_PROPERTY = store_thm
  ("SIGMA_PROPERTY",
   ``!p a.
       {} IN p /\ a SUBSET p /\ (!s. s IN (p INTER sigma a) ==> COMPL s IN p) /\
       (!c. countable c /\ c SUBSET (p INTER sigma a) ==> BIGUNION c IN p) ==>
       sigma a SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `sigma a SUBSET p INTER sigma a`
   >> PSET_TAC []
   ++ Suff `p INTER sigma a IN {b | a SUBSET b /\ sigma_algebra b}`
   >> (KILL_TAC
       ++ PSET_TAC [sigma_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ RW_TAC std_ss [SIGMA_ALGEBRA, IN_INTER]
   ++ PROVE_TAC [SIGMA_ALGEBRA, IN_INTER, SIGMA_ALGEBRA_SIGMA, SUBSET_DEF]);

val MEASURE_EMPTY = store_thm
  ("MEASURE_EMPTY",
   ``!m. measure_space m ==> (measure m {} = 0)``,
   RW_TAC std_ss [measure_space_def, zero_empty_def]);

val SIGMA_SUBSET_MEASURABLE_SETS = store_thm
  ("SIGMA_SUBSET_MEASURABLE_SETS",
   ``!a m.
       measure_space m /\ a SUBSET measurable_sets m ==>
       sigma a SUBSET measurable_sets m``,
   RW_TAC std_ss [measure_space_def]
   ++ MATCH_MP_TAC SIGMA_PROPERTY
   ++ RW_TAC std_ss [IN_INTER, SUBSET_INTER]
   ++ PROVE_TAC [SIGMA_ALGEBRA]);

val SIGMA_ALGEBRA_FN = store_thm
  ("SIGMA_ALGEBRA_FN",
   ``!a.
       sigma_algebra a =
       {} IN a /\ (!s. s IN a ==> COMPL s IN a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> a) ==> BIGUNION (IMAGE f UNIV) IN a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, IN_IMAGE]
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss [COUNTABLE_ENUM]
   >> RW_TAC std_ss [BIGUNION_EMPTY]
   ++ Q.PAT_ASSUM `!f. (!x. P x f) ==> Q f` MATCH_MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   ++ PROVE_TAC []);

val SIGMA_ALGEBRA_FN_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_FN_DISJOINT",
   ``!a.
       sigma_algebra a =
       {} IN a /\ (!s. s IN a ==> COMPL s IN a) /\
       (!s t. s IN a /\ t IN a ==> s UNION t IN a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> a) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT, algebra_def]
   ++ EQ_TAC
   ++ RW_TAC std_ss []);

val SIGMA_PROPERTY_ALT = store_thm
  ("SIGMA_PROPERTY_ALT",
   ``!p a.
       {} IN p /\ a SUBSET p /\ (!s. s IN (p INTER sigma a) ==> COMPL s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER sigma a) ==> BIGUNION (IMAGE f UNIV) IN p) ==>
       sigma a SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `sigma a SUBSET p INTER sigma a`
   >> PSET_TAC []
   ++ Suff `p INTER sigma a IN {b | a SUBSET b /\ sigma_algebra b}`
   >> (KILL_TAC
       ++ PSET_TAC [sigma_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_FN, IN_INTER, FUNSET_INTER]
   ++ PROVE_TAC [SIGMA_ALGEBRA_FN, IN_INTER, SIGMA_ALGEBRA_SIGMA, SUBSET_DEF]);

val SIGMA_PROPERTY_DISJOINT_WEAK = store_thm
  ("SIGMA_PROPERTY_DISJOINT_WEAK",
   ``!p a.
       {} IN p /\ a SUBSET p /\ (!s. s IN (p INTER sigma a) ==> COMPL s IN p) /\
       (!s t. s IN p /\ t IN p ==> s UNION t IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER sigma a) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       sigma a SUBSET p``,
   RW_TAC std_ss []
   ++ Suff `sigma a SUBSET p INTER sigma a`
   >> PSET_TAC []
   ++ Suff `p INTER sigma a IN {b | a SUBSET b /\ sigma_algebra b}`
   >> (KILL_TAC
       ++ PSET_TAC [sigma_def])
   ++ RW_TAC std_ss [GSPECIFICATION]
   >> PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [SIGMA_ALGEBRA_FN_DISJOINT, IN_INTER, FUNSET_INTER]
   ++ PROVE_TAC [SIGMA_ALGEBRA_FN_DISJOINT, IN_INTER, SIGMA_ALGEBRA_SIGMA,
                 SUBSET_DEF]);

val SMALLEST_CLOSED_CDI = store_thm
  ("SMALLEST_CLOSED_CDI",
   ``!a. a SUBSET smallest_closed_cdi a /\ closed_cdi (smallest_closed_cdi a)``,
   PSET_TAC [smallest_closed_cdi_def]
   ++ RW_TAC std_ss [closed_cdi_def, GSPECIFICATION, IN_BIGINTER, IN_FUNSET,
                     IN_UNIV]);

val CLOSED_CDI_DUNION = store_thm
  ("CLOSED_CDI_DUNION",
   ``!p s t.
       {} IN p /\ closed_cdi p /\ s IN p /\ t IN p /\ DISJOINT s t ==>
       s UNION t IN p``,
   RW_TAC std_ss [closed_cdi_def]
   ++ Q.PAT_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. if n = 0 then s else if n = 1 then t else {}`)
   ++ Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        (count 2))`
   >> (MATCH_MP_TAC BIGUNION_IMAGE_UNIV
       ++ RW_TAC arith_ss [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                      COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
   ++ ONCE_REWRITE_TAC [UNION_COMM]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
   ++ PROVE_TAC [DISJOINT_SYM]);

val CLOSED_CDI_COMPL = store_thm
  ("CLOSED_CDI_COMPL",
   ``!p s. closed_cdi p /\ s IN p ==> COMPL s IN p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_DISJOINT = store_thm
  ("CLOSED_CDI_DISJOINT",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> p) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       BIGUNION (IMAGE f UNIV) IN p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_INCREASING = store_thm
  ("CLOSED_CDI_INCREASING",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> p) /\ (f 0 = {}) /\
       (!n. f n SUBSET f (SUC n)) ==>
       BIGUNION (IMAGE f UNIV) IN p``,
   RW_TAC std_ss [closed_cdi_def]);

val SIGMA_PROPERTY_DISJOINT_LEMMA1 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA1",
   ``!a.
       algebra a ==>
       (!s t.
          s IN a /\ t IN smallest_closed_cdi a ==>
          s INTER t IN smallest_closed_cdi a)``,
   RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, smallest_closed_cdi_def]
   ++ Suff
      `t IN
       {b | b IN smallest_closed_cdi a /\ s INTER b IN smallest_closed_cdi a}`
   >> RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ STRONG_CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER,
                      smallest_closed_cdi_def]
       ++ PROVE_TAC [ALGEBRA_INTER])
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def] <<
   [PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI],
    Know `s INTER COMPL s'' = COMPL (COMPL s UNION (s INTER s''))`
    >> (PSET_TAC [EXTENSION]
        ++ PROVE_TAC [])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_COMPL
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ MATCH_MP_TAC CLOSED_CDI_DUNION
    ++ CONJ_TAC
    >> PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ CONJ_TAC >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC CLOSED_CDI_COMPL
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    ++ CONJ_TAC >> PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ PSET_TAC [EXTENSION]
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (num_case {} (\n. s INTER f n)) UNIV)`
    >> (KILL_TAC
        ++ PSET_TAC [EXTENSION]
        ++ (EQ_TAC ++ RW_TAC std_ss [NOT_IN_EMPTY]) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER] >> PROVE_TAC []
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ Cases_on `x'` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ Cases_on `x'` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> (REVERSE (Cases_on `x`) >> RW_TAC arith_ss []
        ++ RW_TAC arith_ss []
        ++ PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    ++ Cases_on `n` >> RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    ++ RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ PSET_TAC [EXTENSION]
        ++ (EQ_TAC ++ RW_TAC std_ss []) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER] >> PROVE_TAC []
         ++ Q.EXISTS_TAC `x'`
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ RW_TAC arith_ss [],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ RW_TAC arith_ss []
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ Q.PAT_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
    ++ PSET_TAC [DISJOINT_DEF, EXTENSION]
    ++ PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA2 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA2",
   ``!a.
       algebra a ==>
       (!s t.
          s IN smallest_closed_cdi a /\ t IN smallest_closed_cdi a ==>
          s INTER t IN smallest_closed_cdi a)``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [smallest_closed_cdi_def, IN_BIGINTER, GSPECIFICATION]
   ++ Suff
      `t IN
       {b | b IN smallest_closed_cdi a /\ s INTER b IN smallest_closed_cdi a}`
   >> RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ STRONG_CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] <<
       [PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF],
        PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA1, INTER_COMM]])
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def] <<
   [PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI],
    Know `s INTER COMPL s'' = COMPL (COMPL s UNION (s INTER s''))`
    >> (PSET_TAC [EXTENSION]
        ++ PROVE_TAC [])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_COMPL
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ MATCH_MP_TAC CLOSED_CDI_DUNION
    ++ CONJ_TAC
    >> PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ CONJ_TAC >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC CLOSED_CDI_COMPL
        ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    ++ CONJ_TAC >> PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    ++ PSET_TAC [EXTENSION]
    ++ PROVE_TAC [],
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (num_case {} (\n. s INTER f n)) UNIV)`
    >> (KILL_TAC
        ++ PSET_TAC [EXTENSION]
        ++ (EQ_TAC ++ RW_TAC std_ss [NOT_IN_EMPTY]) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER] >> PROVE_TAC []
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ Cases_on `x'` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ Cases_on `x'` >> RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         ++ RW_TAC arith_ss [num_case_def, IN_INTER]
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_INCREASING
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> (REVERSE (Cases_on `x`) >> RW_TAC arith_ss []
        ++ RW_TAC arith_ss []
        ++ PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    ++ Cases_on `n` >> RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    ++ RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.PAT_ASSUM `f IN x` MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >> (KILL_TAC
        ++ PSET_TAC [EXTENSION]
        ++ (EQ_TAC ++ RW_TAC std_ss []) <<
        [Q.EXISTS_TAC `s INTER f x'`
         ++ RW_TAC std_ss [IN_INTER] >> PROVE_TAC []
         ++ Q.EXISTS_TAC `x'`
         ++ RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ RW_TAC arith_ss [],
         POP_ASSUM (MP_TAC o Q.SPEC `x`)
         ++ RW_TAC arith_ss []
         ++ Q.EXISTS_TAC `f n`
         ++ RW_TAC std_ss []
         ++ PROVE_TAC []])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC CLOSED_CDI_DISJOINT
    ++ Q.PAT_ASSUM `f IN X` MP_TAC
    ++ RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    ++ Q.PAT_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
    ++ PSET_TAC [DISJOINT_DEF, EXTENSION]
    ++ PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA",
   ``!a p. algebra a /\ a SUBSET p /\ closed_cdi p ==> sigma a SUBSET p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `smallest_closed_cdi a`
   ++ REVERSE CONJ_TAC
   >> (RW_TAC std_ss [SUBSET_DEF, smallest_closed_cdi_def, IN_BIGINTER,
                      GSPECIFICATION]
       ++ PROVE_TAC [SUBSET_DEF])
   ++ NTAC 2 (POP_ASSUM K_TAC)
   ++ Suff `smallest_closed_cdi a IN {b | a SUBSET b /\ sigma_algebra b}`
   >> (KILL_TAC
       ++ PSET_TAC [sigma_def])
   ++ RW_TAC std_ss [GSPECIFICATION, SIGMA_ALGEBRA_ALT_DISJOINT,
                     ALGEBRA_ALT_INTER] <<
   [PROVE_TAC [SMALLEST_CLOSED_CDI],
    PROVE_TAC [ALGEBRA_EMPTY, SUBSET_DEF, SMALLEST_CLOSED_CDI],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_COMPL],
    PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA2],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_DISJOINT]]);

val SIGMA_PROPERTY_DISJOINT_WEAK = store_thm
  ("SIGMA_PROPERTY_DISJOINT_WEAK",
   ``!p a.
       algebra a /\ a SUBSET p /\
       (!s. s IN p ==> COMPL s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       sigma a SUBSET p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (Q.SPECL [`a`, `p`] SIGMA_PROPERTY_DISJOINT_LEMMA)
   ++ RW_TAC std_ss [closed_cdi_def]);

val SIGMA_PROPERTY_DISJOINT = store_thm
  ("SIGMA_PROPERTY_DISJOINT",
   ``!p a.
       algebra a /\ a SUBSET p /\
       (!s. s IN (p INTER sigma a) ==> COMPL s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER sigma a) /\ (f 0 = {}) /\
          (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER sigma a) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       sigma a SUBSET p``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INTER]
   ++ Suff `sigma a SUBSET p INTER sigma a`
   >> (KILL_TAC
       ++ PSET_TAC [])
   ++ MATCH_MP_TAC
      (Q.SPECL [`p INTER sigma a`, `a`] SIGMA_PROPERTY_DISJOINT_WEAK)
   ++ RW_TAC std_ss [SUBSET_INTER, IN_INTER, IN_FUNSET, IN_UNIV] <<
   [PROVE_TAC [SUBSET_DEF, IN_SIGMA],
    PROVE_TAC [SIGMA_ALGEBRA_SIGMA, SIGMA_ALGEBRA],
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV]
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INTER],
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    ++ RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV]
    ++ POP_ASSUM K_TAC
    ++ POP_ASSUM MP_TAC
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INTER]]);

val IN_MEASURE_PRESERVING = store_thm
  ("IN_MEASURE_PRESERVING",
   ``!m1 m2 f.
       f IN measure_preserving m1 m2 =
       f IN measurable (measurable_sets m1) (measurable_sets m2) /\
       !s.
         s IN measurable_sets m2 ==>
         (measure m1 (PREIMAGE f s) = measure m2 s)``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION]);

val MEASURE_COUNTABLY_ADDITIVE = store_thm
  ("MEASURE_COUNTABLY_ADDITIVE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE
   ++ RW_TAC std_ss []
   >> PROVE_TAC [measure_space_def]
   ++ MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ Q.PAT_ASSUM `f IN P` MP_TAC
   ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV,
                     IN_FUNSET]
   ++ PROVE_TAC []);

val MEASURE_SPACE_ADDITIVE = store_thm
  ("MEASURE_SPACE_ADDITIVE",
   ``!m. measure_space m ==> additive m``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
   ++ PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALGEBRA]);

val MEASURE_ADDITIVE = store_thm
  ("MEASURE_ADDITIVE",
   ``!m s t u.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ADDITIVE
   ++ RW_TAC std_ss [MEASURE_SPACE_ADDITIVE]);

val MEASURE_COUNTABLE_INCREASING = store_thm
  ("MEASURE_COUNTABLE_INCREASING",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   ++ Know
      `measure m o f = (\n. sum (0, n) (measure m o (\m. f (SUC m) DIFF f m)))`
   >> (FUN_EQ_TAC
       ++ Induct >> RW_TAC std_ss [o_THM, sum, MEASURE_EMPTY]
       ++ POP_ASSUM (MP_TAC o SYM)
       ++ RW_TAC arith_ss [o_THM, sum]
       ++ MATCH_MP_TAC MEASURE_ADDITIVE
       ++ PSET_TAC [EXTENSION]
       ++ PROVE_TAC [ALGEBRA_DIFF, measure_space_def, SIGMA_ALGEBRA_ALGEBRA])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [GSYM sums]
   ++ MATCH_MP_TAC COUNTABLY_ADDITIVE
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV]
       ++ PROVE_TAC [ALGEBRA_DIFF, measure_space_def, SIGMA_ALGEBRA_ALGEBRA])
   ++ CONJ_TAC
   >> (REPEAT STRIP_TAC
       ++ MATCH_MP_TAC DISJOINT_DIFFS
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss [])
   ++ CONJ_TAC
   >> (PSET_TAC [EXTENSION]
       ++ REVERSE (EQ_TAC ++ RW_TAC std_ss [])
       >> PROVE_TAC []
       ++ Know `x IN f x'` >> PROVE_TAC []
       ++ NTAC 2 (POP_ASSUM K_TAC)
       ++ Induct_on `x'` >> RW_TAC std_ss []
       ++ POP_ASSUM MP_TAC
       ++ Cases_on `x IN f x'` >> RW_TAC std_ss []
       ++ RW_TAC std_ss []
       ++ Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       ++ PSET_TAC [EXTENSION]
       ++ PROVE_TAC [])
   ++ MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
   ++ CONJ_TAC >> PROVE_TAC [measure_space_def]
   ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM]
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
   ++ PROVE_TAC []);

val MEASURE_SPACE_REDUCE = store_thm
  ("MEASURE_SPACE_REDUCE",
   ``!m. (measurable_sets m, measure m) = m``,
   Cases
   ++ RW_TAC std_ss [measurable_sets_def, measure_def]);

val MEASURE_PRESERVING_LIFT = store_thm
  ("MEASURE_PRESERVING_LIFT",
   ``!m1 m2 a f.
       measure_space m1 /\ measure_space m2 /\ algebra a /\
       (measurable_sets m2 = sigma a) /\
       f IN measure_preserving m1 (a, measure m2) ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss []
   ++ Suff `f IN measure_preserving m1 (measurable_sets m2, measure m2)`
   >> RW_TAC std_ss [MEASURE_SPACE_REDUCE]
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ REWRITE_TAC [IN_MEASURE_PRESERVING, measurable_sets_def, measure_def]
   ++ STRIP_TAC
   ++ STRONG_CONJ_TAC
   >> (MATCH_MP_TAC MEASURABLE_LIFT
       ++ PROVE_TAC [measure_space_def])
   ++ Q.PAT_ASSUM `f IN X` K_TAC
   ++ REWRITE_TAC [IN_MEASURABLE]
   ++ STRIP_TAC
   ++ Suff `sigma a SUBSET {s | measure m1 (PREIMAGE f s) = measure m2 s}`
   >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   ++ MATCH_MP_TAC SIGMA_PROPERTY_DISJOINT
   ++ RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_INTER, IN_FUNSET,
                     IN_UNIV, PREIMAGE_COMPL, PREIMAGE_BIGUNION, IMAGE_IMAGE,
                     MEASURE_COMPL] <<
   [Know `measure m1 (PREIMAGE f UNIV) = measure m2 UNIV`
    >> PROVE_TAC [ALGEBRA_UNIV]
    ++ RW_TAC std_ss [PREIMAGE_UNIV],
    Suff
    `(measure m2 o f') --> measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') -->
     measure m1 (BIGUNION (IMAGE (PREIMAGE f o f') UNIV))`
    >> PROVE_TAC [SEQ_UNIQ]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF])
    ++ Know `measure m2 o f' = measure m1 o (PREIMAGE f o f')`
    >> (FUN_EQ_TAC
        ++ RW_TAC std_ss [o_THM])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_EMPTY]
    ++ MATCH_MP_TAC PREIMAGE_SUBSET
    ++ RW_TAC std_ss [SUBSET_DEF],
    Suff
    `(measure m2 o f') sums measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') sums
     measure m1 (BIGUNION (IMAGE (PREIMAGE f o f') UNIV))`
    >> PROVE_TAC [SUM_UNIQ]
    ++ CONJ_TAC
    >> (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
        ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV])
    ++ Know `measure m2 o f' = measure m1 o (PREIMAGE f o f')`
    >> (FUN_EQ_TAC
        ++ RW_TAC std_ss [o_THM])
    ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    ++ MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
    ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_DISJOINT]]);

val MEASURE_PRESERVING_SUBSET = store_thm
  ("MEASURE_PRESERVING_SUBSET",
   ``!m1 m2 a.
       measure_space m1 /\ measure_space m2 /\ algebra a /\
       (measurable_sets m2 = sigma a) ==>
       measure_preserving m1 (a, measure m2) SUBSET
       measure_preserving m1 m2``,
   RW_TAC std_ss [SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURE_PRESERVING_LIFT
   ++ PROVE_TAC []);

val MEASURABLE_UP_LIFT = store_thm
  ("MEASURABLE_UP_LIFT",
   ``!a b c f. f IN measurable a c /\ a SUBSET b ==> f IN measurable b c``,
   RW_TAC std_ss [measurable_def, GSPECIFICATION, SUBSET_DEF]);

val MEASURABLE_UP_SUBSET = store_thm
  ("MEASURABLE_UP_SUBSET",
   ``!a b c. a SUBSET b ==> measurable a c SUBSET measurable b c``,
   RW_TAC std_ss [MEASURABLE_UP_LIFT, SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURABLE_UP_LIFT
   ++ PROVE_TAC [SUBSET_DEF]);

val MEASURABLE_UP_SIGMA = store_thm
  ("MEASURABLE_UP_SIGMA",
   ``!a b. measurable a b SUBSET measurable (sigma a) b``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC MEASURABLE_UP_SUBSET
   ++ RW_TAC std_ss [SUBSET_DEF, IN_SIGMA]);

val MEASURE_PRESERVING_UP_LIFT = store_thm
  ("MEASURE_PRESERVING_UP_LIFT",
   ``!m1 m2 f.
       f IN measure_preserving (a, measure m1) m2 /\
       a SUBSET measurable_sets m1 ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION, SUBSET_DEF,
                  measure_def, measurable_sets_def]
   ++ PROVE_TAC [MEASURABLE_UP_LIFT, SUBSET_DEF]);

val MEASURE_PRESERVING_UP_SUBSET = store_thm
  ("MEASURE_PRESERVING_UP_SUBSET",
   ``!m1 m2.
       a SUBSET measurable_sets m1 ==>
       measure_preserving (a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   ++ MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   ++ PROVE_TAC [SUBSET_DEF]);

val MEASURE_PRESERVING_UP_SIGMA = store_thm
  ("MEASURE_PRESERVING_UP_SIGMA",
   ``!m1 m2 a.
       (measurable_sets m1 = sigma a) ==>
       measure_preserving (a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC MEASURE_PRESERVING_UP_SUBSET
   ++ RW_TAC std_ss [SUBSET_DEF, IN_SIGMA]);

val MEASURABLE_COMP = store_thm
  ("MEASURABLE_COMP",
   ``!f g a b c.
       f IN measurable a b /\ g IN measurable b c ==>
       (g o f) IN measurable a c``,
   RW_TAC std_ss [IN_MEASURABLE, GSYM PREIMAGE_COMP]);

val MEASURABLE_I = store_thm
  ("MEASURABLE_I",
   ``!a. I IN measurable a a``,
   RW_TAC std_ss [IN_MEASURABLE, I_THM, PREIMAGE_I]);

val MEASURABLE_COMP_STRONG = store_thm
  ("MEASURABLE_COMP_STRONG",
   ``!f g a b c.
       f IN measurable a b /\
       (!x. x IN c ==> PREIMAGE g x INTER (range f) IN b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE, PREIMAGE_ALT, o_ASSOC]
   ++ ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
   ++ ONCE_REWRITE_TAC [GSYM PREIMAGE_INTER_RANGE]
   ++ RW_TAC std_ss [PREIMAGE_ALT]);

val MEASURABLE_COMP_STRONGER = store_thm
  ("MEASURABLE_COMP_STRONGER",
   ``!f g a b c t.
       f IN measurable a b /\
       range f SUBSET t /\
       (!s. s IN c ==> PREIMAGE g s INTER t IN b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE, PREIMAGE_ALT, o_ASSOC]
   ++ ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
   ++ MP_TAC
      (Q.SPECL [`f`, `(s : 'c -> bool) o g`, `t`] PREIMAGE_INTER_SUPER_RANGE)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM)
   ++ RW_TAC std_ss [PREIMAGE_ALT]);

val MEASURABLE_PROD_SIGMA = store_thm
  ("MEASURABLE_PROD_SIGMA",
   ``!a a1 a2 f.
       sigma_algebra a /\
       (FST o f) IN measurable a a1 /\
       (SND o f) IN measurable a a2 ==>
       f IN measurable a (sigma (prod_sets a1 a2))``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC MEASURABLE_LIFT
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [IN_MEASURABLE, IN_UNIV, IN_PROD_SETS]
   ++ RW_TAC std_ss [PREIMAGE_CROSS]
   ++ MATCH_MP_TAC ALGEBRA_INTER
   ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA]);

val MONOTONE_CONVERGENCE = store_thm
  ("MONOTONE_CONVERGENCE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
   RW_TAC std_ss [measure_space_def, IN_FUNSET, IN_UNIV]
   ++ (MP_TAC o
       INST_TYPE [beta |-> ``:num``] o
       Q.SPECL [`m`, `BIGUNION (IMAGE f UNIV)`, `num_case {} f`])
      MEASURE_COUNTABLE_INCREASING
   ++ Cond
   >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV, num_case_def, measure_space_def] <<
       [Cases_on `x` <<
        [RW_TAC std_ss [num_case_def]
         ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY],
         RW_TAC std_ss [num_case_def]],
        Cases_on `n`
        ++ RW_TAC std_ss [num_case_def, EMPTY_SUBSET],
        SET_EQ_TAC
        ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV]
        ++ EQ_TAC <<
        [RW_TAC std_ss []
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC std_ss [num_case_def],
         RW_TAC std_ss []
         ++ POP_ASSUM MP_TAC
         ++ Cases_on `x'` >> RW_TAC std_ss [NOT_IN_EMPTY, num_case_def]
         ++ RW_TAC std_ss [num_case_def]
         ++ PROVE_TAC []]])
   ++ RW_TAC std_ss []
   ++ Know `measure m o f = (\n. (measure m o (num_case {} f)) (SUC n))`
   >> (FUN_EQ_TAC
       ++ RW_TAC std_ss [num_case_def, o_THM])
   ++ Rewr
   ++ Ho_Rewrite.REWRITE_TAC [GSYM SEQ_SUC]
   ++ RW_TAC std_ss' []);
***)

(* ------------------------------------------------------------------------- *)
(* Lebesgue integration.                                                     *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("simple_function",
                      Type `:(posreal # ('a -> bool)) list`);

Definition range_simple_def:
   (range_simple ([] : 'a simple_function) = {}) /\
   (range_simple ((a,s) :: l) = s UNION range_simple l)
End

Definition evaluate_simple_def:
   (evaluate_simple ([] : 'a simple_function) x = 0) /\
   (evaluate_simple ((a,s) :: l) x =
    (if x IN s then a else 0) + evaluate_simple l x)
End

Definition integrate_simple_def:
   (integrate_simple (m : 'a measure) [] = 0) /\
   (integrate_simple m ((a,s) :: l) = a * m.mu s + integrate_simple m l)
End

Definition integrate_def:
   integrate m s f =
   sup { integrate_simple m g |
         range_simple g SUBSET s /\
         !x :: s. evaluate_simple g x <= f x }
End

