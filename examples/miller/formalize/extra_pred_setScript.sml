(* interactive mode
loadPath := ["../ho_prover","../subtypes","../rsa"] @ !loadPath;
app load ["bossLib","subtypeTheory","HurdUseful","extra_boolTheory",
          "boolContext","extra_listTheory","listContext",
          "state_transformerTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib arithmeticTheory combinTheory
     pred_setTheory hurdUtils boolContext listTheory
     res_quanTools res_quanTheory subtypeTheory subtypeTools
     extra_listTheory ho_proverTools listContext extra_numTheory
     pairTheory state_transformerTheory simpLib;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "extra_pred_set";
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val std_pc = precontext_mergel [bool_pc, list_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

val Strip = S_TAC;
val Simplify = R_TAC;
val bool_ss = boolSimps.bool_ss;
val Cond =
  MATCH_MP_TAC (PROVE [] ``!a b c. a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
  >> CONJ_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val IMAGE2_def = Define `IMAGE2 f s t = {f x y | x IN s /\ y IN t}`;

val UNIONL_def = Define `(UNIONL [] = {})
  /\ (UNIONL (s::ss) = (s:'a->bool) UNION UNIONL ss)`;

val DISJOINTL_def = Define `(DISJOINTL [] = T)
  /\ (DISJOINTL (s::ss) = DISJOINT (s:'a->bool) (UNIONL ss) /\ DISJOINTL ss)`;

val (list_elts_def, list_elts_ind) = ((Q.GEN `s` ## I) o Defn.tprove)
  let val d = Defn.Hol_defn "list_elts" `list_elts (s:'a->bool)
        = if FINITE s then
            (if s = {} then []
             else (CHOICE s)::(list_elts (s DELETE (CHOICE s))))
          else ARB`
      val m = `measure CARD`
  in (d,
      WF_REL_TAC m
      >> RW_TAC std_ss []
      >> MP_TAC (Q.SPEC `s` CARD_DELETE)
      >> ASM_REWRITE_TAC []
      >> DISCH_THEN (MP_TAC o Q.SPEC `CHOICE s`)
      >> RW_TAC arith_ss [CHOICE_DEF]
      >> MP_TAC (Q.SPEC `s` CARD_EQ_0)
      >> RW_TAC arith_ss [])
  end;

val _ = save_thm ("list_elts_def", list_elts_def);
val _ = save_thm ("list_elts_ind", list_elts_ind);

val set_def = Define `set p s = s SUBSET p`;

val nonempty_def = Define `nonempty s = ~(s = {})`;

val range_def = Define `range f = IMAGE f UNIV`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val IN_o = store_thm
  ("IN_o",
   ``!x f s. x IN (s o f) = f x IN s``,
   RW_TAC std_ss [SPECIFICATION, o_THM]);

val UNION_DEF_ALT = store_thm
  ("UNION_DEF_ALT",
   ``!s t. s UNION t = (\x:'a. s x \/ t x)``,
   REPEAT STRIP_TAC
   >> Suff `!v:'a. v IN (s UNION t) = v IN (\x. s x \/ t x)`
     >- (PURE_REWRITE_TAC [SPECIFICATION]
         >> PROVE_TAC [EQ_EXT])
   >> RW_TAC std_ss [UNION_DEF, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]);

val INTER_UNION_RDISTRIB = store_thm
  ("INTER_UNION_RDISTRIB",
   ``!(p:'a->bool) q r. (p UNION q) INTER r = p INTER r UNION q INTER r``,
   RW_TAC std_ss [EXTENSION, IN_UNION, IN_INTER]
   >> PROVE_TAC []);

val INTER_IS_EMPTY = store_thm
  ("INTER_IS_EMPTY",
   ``!(s:'a->bool) t. (s INTER t = {}) = (!x. ~s x \/ ~t x)``,
   RW_TAC std_ss [INTER_DEF, EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION, EMPTY_DEF]);

val GSPEC_DEF_ALT = store_thm
  ("GSPEC_DEF_ALT",
   ``!(f:'a -> 'b # bool). GSPEC f = (\v. ?x. (v, T) = f x)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]);

val UNION_DISJOINT_SPLIT = store_thm
  ("UNION_DISJOINT_SPLIT",
   ``!(s:'a->bool) t u. (s UNION t = s UNION u)
                        /\ (s INTER t = {}) /\ (s INTER u = {})
                        ==> (t = u)``,
   RW_TAC std_ss [UNION_DEF_ALT, EXTENSION, INTER_IS_EMPTY, SPECIFICATION]
   >> PROVE_TAC []);

val INSERT_THM1 = store_thm
  ("INSERT_THM1",
   ``!(x:'a) s. x IN (x INSERT s)``, RW_TAC std_ss [IN_INSERT]);

val INSERT_THM2 = store_thm
  ("INSERT_THM2",
   ``!(x:'a) y s. x IN s ==> x IN (y INSERT s)``, RW_TAC std_ss [IN_INSERT]);

val IMAGE_THM = store_thm
  ("IMAGE_THM",
   ``!(f:'a->'b) x s. x IN s ==> f x IN IMAGE f s``,
    RW_TAC std_ss [IN_IMAGE]
    >> PROVE_TAC []);

val ELT_IN_DELETE = store_thm
  ("ELT_IN_DELETE",
   ``!x s. ~(x IN (s DELETE x))``,
   RW_TAC std_ss [IN_DELETE]);

val FINITE_INTER = store_thm
  ("FINITE_INTER",
   ``!s. FINITE s ==> !t. FINITE (t INTER s)``,
   PROVE_TAC [INTER_FINITE, INTER_COMM]);

val IN_IMAGE2 = store_thm
  ("IN_IMAGE2",
   ``!x f s t. x IN IMAGE2 f s t = ?a b. a IN s /\ b IN t /\ (f a b = x)``,
   RW_TAC std_ss [IMAGE2_def, GSPECIFICATION]
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> POP_ASSUM MP_TAC
    >> Cases_on `x'`
    >> RW_TAC std_ss []
    >> PROVE_TAC [],
    RW_TAC std_ss []
    >> Q.EXISTS_TAC `(a, b)`
    >> RW_TAC std_ss []]);

val CONJ_IMAGE2 = store_thm
  ("CONJ_IMAGE2",
   ``!a b s t.
       (b ==> a IN s) /\ (a ==> b IN t) ==>
       ((a /\ b) IN ({F} UNION IMAGE2 $/\ s t))``,
   RW_TAC std_ss [IN_UNION, IN_IMAGE2, IN_INSERT, NOT_IN_EMPTY]
   >> Suff `a /\ b ==> ?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' = a /\ b)`
   >- (Q.SPEC_TAC (`?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' = a /\ b)`, `q`)
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> PROVE_TAC []);

val INJ_SUBSET = store_thm
  ("INJ_SUBSET",
   ``!f s s' t. INJ f s t /\ s' SUBSET s ==> INJ f s' t``,
   RW_TAC std_ss [INJ_DEF, SUBSET_DEF]);

val CARD_IMAGE = store_thm
  ("CARD_IMAGE",
   ``!f s t. FINITE s /\ INJ f s t ==> (CARD (IMAGE f s) = CARD s)``,
   Suff `!s. FINITE s ==> !f t. INJ f s t ==> (CARD (IMAGE f s) = CARD s)`
   >- PROVE_TAC []
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [IMAGE_EMPTY, CARD_DEF, IMAGE_INSERT]
   >> Know `~(f e IN IMAGE f s)`
   >- (rpt (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [IN_INSERT, IN_IMAGE, INJ_DEF]
       >> PROVE_TAC [])
   >> MP_TAC (Q.SPEC `s` IMAGE_FINITE)
   >> RW_TAC std_ss [CARD_INSERT]
   >> Suff `INJ f s t` >- PROVE_TAC []
   >> MATCH_MP_TAC INJ_SUBSET
   >> RW_TAC std_ss [SUBSET_DEF]
   >> PROVE_TAC [IN_INSERT]);

val CARD_SUBSET_PROPER = store_thm
  ("CARD_SUBSET_PROPER",
   ``!(s:'a->bool) t.
        FINITE t /\ s SUBSET t ==> ((CARD s = CARD t) = (s = t))``,
   RW_TAC std_ss []
   >> Cases_on `s = t` >- PROVE_TAC []
   >> Know `s PSUBSET t` >- PROVE_TAC [PSUBSET_DEF]
   >> STRIP_TAC
   >> MP_TAC (Q.SPEC `t` CARD_PSUBSET)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `s`)
   >> RW_TAC arith_ss []);

val LIST_ELTS = store_thm
  ("LIST_ELTS",
   ``!(s:'a->bool). FINITE s ==> (!v. MEM v (list_elts s) = v IN s)``,
   recInduct list_elts_ind
   >> RW_TAC std_ss []
   >> Cases_on `s = {}`
   >- (MP_TAC (Q.SPEC `s` list_elts_def)
       >> RW_TAC std_ss [FINITE_EMPTY, MEM, NOT_IN_EMPTY])
   >> Know `FINITE (s DELETE CHOICE s)` >- PROVE_TAC [FINITE_DELETE]
   >> S_TAC
   >> RES_TAC
   >> NTAC 2 (POP_ASSUM (K ALL_TAC))
   >> ONCE_REWRITE_TAC [list_elts_def]
   >> RW_TAC std_ss []
   >> Cases_on `v = CHOICE s`
   >- (RW_TAC std_ss [CHOICE_DEF]
       >> RW_TAC std_ss [SPECIFICATION, MEM])
   >> Q.PAT_X_ASSUM `!v. P v` (MP_TAC o Q.SPEC `v`)
   >> MP_TAC (Q.SPECL [`s`, `v`, `CHOICE s`] IN_DELETE)
   >> ASM_REWRITE_TAC []
   >> RW_TAC std_ss [MEM, SPECIFICATION]);

val FINITE_UNIONL = store_thm
  ("FINITE_UNIONL",
   ``!(ss:('a->bool) list). FINITE (UNIONL ss) = EVERY FINITE ss``,
   Induct >- RW_TAC list_ss [UNIONL_def, FINITE_EMPTY]
   >> RW_TAC list_ss [UNIONL_def, FINITE_UNION]);

val CARD_UNIONL = store_thm
  ("CARD_UNIONL",
   ``!(ss:('a->bool) list). EVERY FINITE ss /\ DISJOINTL ss
          ==> (CARD (UNIONL ss) = sum (MAP CARD ss))``,
   Induct >- RW_TAC list_ss [DISJOINTL_def, UNIONL_def, sum_def, CARD_DEF]
   >> RW_TAC list_ss [DISJOINTL_def, UNIONL_def, sum_def]
   >> Know `FINITE (UNIONL ss)` >- RW_TAC std_ss [FINITE_UNIONL]
   >> MP_TAC (Q.SPECL [`h`] CARD_UNION)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `UNIONL ss`)
   >> Q.PAT_X_ASSUM `DISJOINT a b` MP_TAC
   >> RW_TAC arith_ss [DISJOINT_DEF, CARD_DEF]);

val IN_UNIONL = store_thm
  ("IN_UNIONL",
   ``!l (v:'a). v IN UNIONL l = (?s. MEM s l /\ v IN s)``,
   Induct >- RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
   >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
   >> PROVE_TAC []);

val DISJOINT_UNION1 = DISJOINT_UNION;
val DISJOINT_UNION2 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNION1;

val DISJOINT_UNIONL2 = store_thm
  ("DISJOINT_UNIONL2",
   ``!l (x:'a->bool). DISJOINT x (UNIONL l) = (!y. MEM y l ==> DISJOINT x y)``,
   Induct >- RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_DEF, INTER_EMPTY]
   >> RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_UNION2]
   >> PROVE_TAC []);
val DISJOINT_UNIONL1 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNIONL2;

val DISJOINTL_KILL_DUPS = store_thm
  ("DISJOINTL_KILL_DUPS",
   ``!(l:('a->bool) list). DISJOINTL (kill_dups l)
         = (!x y. MEM x l /\ MEM y l ==> (x = y) \/ DISJOINT x y)``,
   Induct >- RW_TAC list_ss [DISJOINTL_def, MEM, kill_dups_def, FOLDR]
   >> REWRITE_TAC [kill_dups_def, FOLDR]
   >> (RW_TAC std_ss [GSYM kill_dups_def, MEM, DISJOINTL_def, MEM_KILL_DUPS,
                      DISJOINT_UNIONL2]
       >> EQ_TAC
       >> RW_TAC std_ss []
       >> PROVE_TAC [DISJOINT_SYM]));

val NUM_TO_FINITE = store_thm
  ("NUM_TO_FINITE",
   ``!s (f:num->'a).
       FINITE s /\ (!n. f n IN s) ==> ?i j. i < j /\ (f i = f j)``,
   Suff `!s. FINITE s ==> !(f:num->'a). (!n. f n IN s)
               ==> ?i j. i < j /\ (f i = f j)`
   >- PROVE_TAC []
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> REWRITE_TAC [NOT_IN_EMPTY]
   >> RW_TAC std_ss [IN_INSERT]
   >> Cases_on `?n. !m. m >= n ==> ~(f m = e)` >|
   [POP_ASSUM MP_TAC
    >> STRIP_TAC
    >> Q.PAT_X_ASSUM `!f. (!n. P f n) ==> Q f` (MP_TAC o Q.SPEC `(\x. f (x + n))`)
    >> Know `!n'. f (n + n') IN s`
    >- (STRIP_TAC
        >> Suff `n + n' >= n` >- PROVE_TAC []
        >> DECIDE_TAC)
    >> RW_TAC arith_ss []
    >> Suff `i + n < j + n` >- PROVE_TAC []
    >> DECIDE_TAC,
    POP_ASSUM MP_TAC
    >> RW_TAC std_ss []
    >> POP_ASSUM (fn th => MP_TAC th >> MP_TAC (Q.SPEC `0` th))
    >> RW_TAC std_ss []
    >> POP_ASSUM (MP_TAC o Q.SPEC `SUC m`)
    >> RW_TAC arith_ss []
    >> Suff `m < m'` >- PROVE_TAC []
    >> DECIDE_TAC]);

val SURJ_ALT = store_thm
  ("SURJ_ALT",
   ``!f s t. SURJ f s t = f IN (s -> t) /\ (!y :: t. ?x :: s. y = f x)``,
   S_TAC
   >> R_TAC [SURJ_DEF]
   >> RESQ_TAC
   >> R_TAC [IN_FUNSET, IN_DFUNSET]
   >> PROVE_TAC []);

val BIJ_ALT_RES = store_thm
  ("BIJ_ALT_RES",
   ``!f s t. BIJ f s t = f IN (s -> t) /\ (!y :: t. ?!x :: s. y = f x)``,
   S_TAC
   >> R_TAC [BIJ_DEF, INJ_DEF, SURJ_DEF, RES_EXISTS_UNIQUE_ALT]
   >> RESQ_TAC
   >> R_TAC [IN_FUNSET, IN_DFUNSET, GSYM CONJ_ASSOC]
   >> Know `!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)` >- PROVE_TAC []
   >> DISCH_THEN MATCH_MP_TAC
   >> REPEAT (STRIP_TAC ORELSE EQ_TAC) >|
   [PROVE_TAC [],
    Q.PAT_X_ASSUM `!x. P x`
    (fn th =>
     MP_TAC (Q.SPEC `(f:'a->'b) x` th)
     >> MP_TAC (Q.SPEC `(f:'a->'b) y` th))
    >> Cond >- PROVE_TAC []
    >> STRIP_TAC
    >> Cond >- PROVE_TAC []
    >> STRIP_TAC
    >> PROVE_TAC [],
    PROVE_TAC []]);

val DELETE_THEN_INSERT = store_thm
  ("DELETE_THEN_INSERT",
   ``!s. !x :: s. x INSERT (s DELETE x) = s``,
   RESQ_TAC
   >> R_TAC [INSERT_DELETE]);

val BIJ_INSERT_NOTIN = store_thm
  ("BIJ_INSERT_NOTIN",
   ``!f e s t.
       ~(e IN s) /\ BIJ f (e INSERT s) t ==>
       ?u. (f e INSERT u = t) /\ ~(f e IN u) /\ BIJ f s u``,
   R_TAC [BIJ_ALT_RES]
   >> S_TAC
   >> Q.EXISTS_TAC `t DELETE f e`
   >> AR_TAC [IN_FUNSET, DELETE_THEN_INSERT, ELT_IN_DELETE, IN_INSERT,
              DISJ_IMP_THM]
   >> RESQ_TAC
   >> AR_TAC [IN_DELETE, IN_INSERT]
   >> REPEAT STRIP_TAC
   >> METIS_TAC []);

val FINITE_MAXIMAL = store_thm
  ("FINITE_MAXIMAL",
   ``!f s. FINITE s /\ ~(s = {}) ==> ?x :: s. !y :: s. (f y:num) <= f x``,
   STRIP_TAC
   >> R_TAC [GSYM AND_IMP_INTRO]
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> R_TAC []
   >> S_TAC
   >> Cases_on `s = {}`
   >- (Q_RESQ_EXISTS_TAC `e`
       >> AR_TAC []
       >> S_TAC
       >> AR_TAC [IN_SING])
   >> RES_TAC
   >> S_TAC
   >> Know `(f:'a->num) e <= f x \/ f x <= f e` >- DECIDE_TAC
   >> S_TAC >|
   [Q_RESQ_EXISTS_TAC `x`
    >> R_TAC []
    >> S_TAC
    >> POP_ASSUM MP_TAC
    >> R_TAC [IN_INSERT]
    >> S_TAC >- R_TAC []
    >> Q.PAT_X_ASSUM `!y :: s. f y <= f x` (MP_TAC o Q_RESQ_SPEC `y`)
    >> R_TAC [],
    Q_RESQ_EXISTS_TAC `e`
    >> R_TAC []
    >> S_TAC
    >> POP_ASSUM MP_TAC
    >> R_TAC [IN_INSERT]
    >> S_TAC >- R_TAC []
    >> Q.PAT_X_ASSUM `!y :: s. f y <= f x` (MP_TAC o Q_RESQ_SPEC `y`)
    >> DECIDE_TAC]);

val EMPTY_UNION_ALT = store_thm
  ("EMPTY_UNION_ALT",
   ``!s t. ({} = s UNION t) = (s = {}) /\ (t = {})``,
   PROVE_TAC [EMPTY_UNION]);

val IN_SET = store_thm
  ("IN_SET",
   ``!s p. s IN set p = s SUBSET p``,
   RW_TAC std_ss [SPECIFICATION, set_def]);

val IN_NONEMPTY = store_thm
  ("IN_NONEMPTY",
   ``!s p. s IN nonempty = ~(s = {})``,
   RW_TAC std_ss [SPECIFICATION, nonempty_def]);

val IN_FINITE = store_thm
  ("IN_FINITE",
   ``!s. s IN FINITE = FINITE s``,
   RW_TAC std_ss [SPECIFICATION]);

val EMPTY_SUBTYPE = store_thm
  ("EMPTY_SUBTYPE",
   ``!x. {} IN (set x INTER FINITE)``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET]);

val INSERT_SUBTYPE = store_thm
  ("INSERT_SUBTYPE",
   ``!x. $INSERT IN ((x -> set x -> set x) INTER
                     (UNIV -> FINITE -> FINITE) INTER
                     (UNIV -> UNIV -> nonempty))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY]);

val INTER_SUBTYPE = store_thm
  ("INTER_SUBTYPE",
   ``!x. $INTER IN ((set x -> UNIV -> set x) INTER
                    (UNIV -> set x -> set x) INTER
                    (UNIV -> FINITE -> FINITE) INTER
                    (FINITE -> UNIV -> FINITE))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF]);

val UNION_SUBTYPE = store_thm
  ("UNION_SUBTYPE",
   ``!x. $UNION IN ((set x -> set x -> set x) INTER
                    (FINITE -> FINITE -> FINITE) INTER
                    (UNIV -> nonempty -> nonempty))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION,
                  IN_NONEMPTY, EMPTY_UNION]
   >> PROVE_TAC []);

val CHOICE_SUBTYPE = store_thm
  ("CHOICE_SUBTYPE",
   ``!x. CHOICE IN ((nonempty INTER set x) -> x)``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION, IN_NONEMPTY,
                  CHOICE_DEF]);

val REST_SUBTYPE = store_thm
  ("REST_SUBTYPE",
   ``!x. REST IN ((FINITE -> FINITE) INTER
                  (set x -> set x))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION, IN_NONEMPTY,
                  CHOICE_DEF, REST_DEF, FINITE_DELETE, IN_DELETE]);

val DELETE_SUBTYPE = store_thm
  ("DELETE_SUBTYPE",
   ``!x. $DELETE IN ((set x -> UNIV -> set x) INTER
                     (FINITE -> UNIV -> FINITE))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY, FINITE_DELETE, SUBSET_DEF,
                  IN_DELETE]);

val IMAGE_SUBTYPE = store_thm
  ("IMAGE_SUBTYPE",
   ``!x y. IMAGE IN (((x -> y) -> set x -> set y) INTER
                     (UNIV -> nonempty -> nonempty) INTER
                     (UNIV -> FINITE -> FINITE))``,
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY, FINITE_DELETE, SUBSET_DEF,
                  IN_DELETE, IN_IMAGE, IMAGE_EQ_EMPTY, IMAGE_FINITE]
   >> PROVE_TAC []);

val SET_UNIV = store_thm
  ("SET_UNIV",
   ``set UNIV = UNIV``,
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_SET, IN_UNIV, SUBSET_UNIV]);

val SET_SUBSET = store_thm
  ("SET_SUBSET",
   ``!x y. x SUBSET y ==> set x SUBSET set y``,
   RW_TAC std_ss [IN_SET, SUBSET_DEF]);

val FINITE_SUBTYPE_JUDGEMENT = store_thm
  ("FINITE_SUBTYPE_JUDGEMENT",
   ``!s. FINITE s ==> s IN FINITE``,
   RW_TAC std_ss [SPECIFICATION]);

val FINITE_SUBTYPE_REWRITE = store_thm
  ("FINITE_SUBTYPE_REWRITE",
   ``!s. s IN FINITE ==> FINITE s``,
   RW_TAC std_ss [SPECIFICATION]);

val NONEMPTY_SUBTYPE_JUDGEMENT = store_thm
  ("NONEMPTY_SUBTYPE_JUDGEMENT",
   ``!s x. (x IN s) \/ ~(s = {}) \/ ~({} = s) ==> s IN nonempty``,
   REWRITE_TAC [IN_NONEMPTY]
   >> SET_EQ_TAC
   >> RW_TAC std_ss [NOT_IN_EMPTY]
   >> PROVE_TAC []);

val NONEMPTY_SUBTYPE_REWRITE = store_thm
  ("NONEMPTY_SUBTYPE_REWRITE",
   ``!s. s IN nonempty ==> ~(s = {}) /\ ~({} = s)``,
   RW_TAC std_ss [SPECIFICATION, IN_NONEMPTY]
   >> PROVE_TAC []);

val CARD_SUBTYPE = store_thm
  ("CARD_SUBTYPE",
   ``CARD IN ((FINITE INTER nonempty) -> gtnum 0)``,
   R_TAC [IN_FUNSET, IN_NONEMPTY, IN_GTNUM, IN_INTER, IN_FINITE]
   >> S_TAC
   >> Suff `~(CARD x = 0)` >- DECIDE_TAC
   >> PROVE_TAC [CARD_EQ_0]);

val INTER_DEF_ALT = store_thm
  ("INTER_DEF_ALT",
   ``!s t. s INTER t = (\x. s x /\ t x)``,
   SET_EQ_TAC
   >> R_TAC [IN_INTER]
   >> R_TAC [SPECIFICATION]);

val FINITE_INTER_DISJ = store_thm
  ("FINITE_INTER_DISJ",
   ``!s t. FINITE s \/ FINITE t ==> FINITE (s INTER t)``,
   PROVE_TAC [FINITE_INTER, INTER_FINITE]);

val FINITE_SUBSET_CARD_EQ = store_thm
  ("FINITE_SUBSET_CARD_EQ",
   ``!s t. FINITE t /\ s SUBSET t /\ (CARD s = CARD t) ==> (s = t)``,
   S_TAC
   >> Suff `s SUBSET t /\ t SUBSET s`
   >- (KILL_TAC
       >> SET_EQ_TAC
       >> R_TAC [SUBSET_DEF]
       >> PROVE_TAC [])
   >> R_TAC []
   >> Know `FINITE s` >- PROVE_TAC [SUBSET_FINITE]
   >> S_TAC
   >> Know `FINITE t /\ s SUBSET t /\ (CARD s = CARD t)` >- PROVE_TAC []
   >> Q.SPEC_TAC (`t`, `t`)
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`s`, `s`)
   >> KILL_TAC
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> CONJ_TAC >- (R_TAC [CARD_EMPTY, SUBSET_EMPTY] >> PROVE_TAC [CARD_EQ_0])
   >> S_TAC
   >> Know `?t'. ~(e IN t') /\ (t = e INSERT t')`
   >- (Q.EXISTS_TAC `t DELETE e`
       >> R_TAC [IN_DELETE]
       >> MATCH_MP_TAC (GSYM INSERT_DELETE)
       >> AR_TAC [INSERT_SUBSET])
   >> S_TAC
   >> POP_ASSUM (fn th => AR_TAC [th, FINITE_INSERT, CARD_INSERT])
   >> R_TAC [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT]
   >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
   >> Q.PAT_X_ASSUM `x SUBSET y` MP_TAC
   >> R_TAC [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT]);

val SUBSET_INTER1 = store_thm
  ("SUBSET_INTER1",
   ``!s t. s SUBSET t ==> (s INTER t = s)``,
   SET_EQ_TAC
   >> Simplify [SUBSET_DEF, IN_INTER]);

val SUBSET_INTER2 = store_thm
  ("SUBSET_INTER2",
   ``!s t. s SUBSET t ==> (t INTER s = s)``,
   SET_EQ_TAC
   >> Simplify [SUBSET_DEF, IN_INTER]);

val FINITE_LESS = store_thm
  ("FINITE_LESS",
   ``!n. FINITE (\x : num. x < n)``,
   Induct
   >- (Suff `(\x : num. x < 0) = {}`
       >- Simplify [FINITE_EMPTY]
       >> SET_EQ_TAC
       >> Simplify []
       >> Simplify [SPECIFICATION]
       >> DECIDE_TAC)
   >> Suff `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >- Simplify [FINITE_INSERT]
   >> SET_EQ_TAC
   >> Simplify [IN_INSERT]
   >> Simplify [SPECIFICATION]
   >> DECIDE_TAC);

val FINITE_LESS1 = store_thm
  ("FINITE_LESS1",
   ``!n s. FINITE (\x : num. x < n /\ s x)``,
   Strip
   >> Simplify [GSYM INTER_DEF_ALT]
   >> MATCH_MP_TAC FINITE_INTER_DISJ
   >> Simplify [FINITE_LESS]);

val FINITE_LESS2 = store_thm
  ("FINITE_LESS2",
   ``!n s. FINITE (\x : num. s x /\ x < n)``,
   Strip
   >> Simplify [GSYM INTER_DEF_ALT]
   >> MATCH_MP_TAC FINITE_INTER_DISJ
   >> Simplify [FINITE_LESS]);

val CARD_LESS = store_thm
  ("CARD_LESS",
   ``!n. CARD (\x. x < n) = n``,
   Induct
   >- (Suff `(\x : num. x < 0) = {}`
       >- Simplify [CARD_EMPTY]
       >> SET_EQ_TAC
       >> Simplify []
       >> Simplify [SPECIFICATION]
       >> DECIDE_TAC)
   >> ASSUME_TAC (Q.SPEC `n` FINITE_LESS)
   >> Know `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >- (SET_EQ_TAC
       >> Simplify [IN_INSERT]
       >> Simplify [SPECIFICATION]
       >> DECIDE_TAC)
   >> Simplify [CARD_INSERT]
   >> DISCH_THEN K_TAC
   >> Suff `~(n IN (\x. x < n))` >- Simplify []
   >> Simplify [SPECIFICATION]
   >> DECIDE_TAC);

val INJ_IMAGE_BIJ = store_thm
  ("INJ_IMAGE_BIJ",
   ``!s f. (?t. INJ f s t) ==> BIJ f s (IMAGE f s)``,
   RW_TAC std_ss [INJ_DEF, BIJ_DEF, SURJ_DEF, IN_IMAGE]
   >> PROVE_TAC []);

val BIJ_SYM_IMP = store_thm
  ("BIJ_SYM_IMP",
   ``!s t. (?f. BIJ f s t) ==> (?g. BIJ g t s)``,
   RW_TAC std_ss [BIJ_DEF, SURJ_DEF, INJ_DEF]
   >> Suff `?(g : 'b -> 'a). !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >- (Strip
       >> Q.EXISTS_TAC `g`
       >> RW_TAC std_ss []
       >> PROVE_TAC [])
   >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [boolTheory.EXISTS_DEF])
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `\x. @y. y IN s /\ (f y = x)`
   >> RW_TAC std_ss []);

val BIJ_SYM = store_thm
  ("BIJ_SYM",
   ``!s t. (?f. BIJ f s t) = (?g. BIJ g t s)``,
   PROVE_TAC [BIJ_SYM_IMP]);

val BIJ_TRANS = store_thm
  ("BIJ_TRANS",
   ``!s t u.
       (?f. BIJ f s t) /\ (?g. BIJ g t u) ==> (?h : 'a -> 'b. BIJ h s u)``,
   RW_TAC std_ss []
   >> Q.EXISTS_TAC `g o f`
   >> PROVE_TAC [BIJ_COMPOSE]);

val SURJ_IMP_INJ = store_thm
  ("SURJ_IMP_INJ",
   ``!s t. (?f. SURJ f s t) ==> (?g. INJ g t s)``,
   RW_TAC std_ss [SURJ_DEF, INJ_DEF]
   >> Suff `?g. !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >- PROVE_TAC []
   >> Q.EXISTS_TAC `\y. @x. x IN s /\ (f x = y)`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val ENUMERATE = store_thm
  ("ENUMERATE",
   ``!s. (?f : num -> 'a. BIJ f UNIV s) = BIJ (enumerate s) UNIV s``,
   RW_TAC std_ss [boolTheory.EXISTS_DEF, enumerate_def]);

val FINITE_REST = store_thm
  ("FINITE_REST",
   ``!s. FINITE (REST s) = FINITE s``,
   RW_TAC std_ss [REST_DEF, FINITE_DELETE]);

val EXPLICIT_ENUMERATE_MONO = store_thm
  ("EXPLICIT_ENUMERATE_MONO",
   ``!n s. FUNPOW REST n s SUBSET s``,
   Induct >- RW_TAC std_ss [FUNPOW, SUBSET_DEF]
   >> RW_TAC std_ss [FUNPOW_SUC]
   >> PROVE_TAC [SUBSET_TRANS, REST_SUBSET]);

val EXPLICIT_ENUMERATE_NOT_EMPTY = store_thm
  ("EXPLICIT_ENUMERATE_NOT_EMPTY",
   ``!n s. INFINITE s ==> ~(FUNPOW REST n s = {})``,
   REWRITE_TAC []
   >> Induct >- (RW_TAC std_ss [FUNPOW] >> PROVE_TAC [FINITE_EMPTY])
   >> RW_TAC std_ss [FUNPOW]
   >> Q.PAT_X_ASSUM `!s. P s` (MP_TAC o Q.SPEC `REST s`)
   >> PROVE_TAC [FINITE_REST]);

val INFINITE_EXPLICIT_ENUMERATE = store_thm
  ("INFINITE_EXPLICIT_ENUMERATE",
   ``!s. INFINITE s ==> INJ (\n : num. CHOICE (FUNPOW REST n s)) UNIV s``,
   RW_TAC std_ss [INJ_DEF, IN_UNIV]
   >- (Suff `CHOICE (FUNPOW REST n s) IN FUNPOW REST n s`
       >- PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
       >> RW_TAC std_ss [GSYM CHOICE_DEF, EXPLICIT_ENUMERATE_NOT_EMPTY])
   >> rpt (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`s`, `s`)
   >> Q.SPEC_TAC (`n'`, `y`)
   >> Q.SPEC_TAC (`n`, `x`)
   >> (Induct >> Cases) >|
   [PROVE_TAC [],
    rpt STRIP_TAC
    >> Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC n) s)`
    >- (RW_TAC std_ss []
        >> MATCH_MP_TAC CHOICE_DEF
        >> PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    >> POP_ASSUM K_TAC
    >> RW_TAC std_ss [FUNPOW]
    >> Suff `~(CHOICE s IN REST s)`
    >- PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    >> PROVE_TAC [CHOICE_NOT_IN_REST],
    rpt STRIP_TAC
    >> POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
    >> Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC x) s)`
    >- (RW_TAC std_ss []
        >> MATCH_MP_TAC CHOICE_DEF
        >> PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    >> POP_ASSUM K_TAC
    >> RW_TAC std_ss [FUNPOW]
    >> Suff `~(CHOICE s IN REST s)`
    >- PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    >> PROVE_TAC [CHOICE_NOT_IN_REST],
    RW_TAC std_ss [FUNPOW]
    >> Q.PAT_X_ASSUM `!y. P y` (MP_TAC o Q.SPECL [`n`, `REST s`])
    >> PROVE_TAC [FINITE_REST]]);

val DIFF_ALT = store_thm
  ("DIFF_ALT",
   ``!s t. s DIFF t = s INTER (COMPL t)``,
   RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER, IN_COMPL]);

val DIFF_SUBSET = store_thm
  ("DIFF_SUBSET",
   ``!a b. a DIFF b SUBSET a``,
   RW_TAC std_ss [SUBSET_DEF, EXTENSION, IN_DIFF]);

val NUM_2D_BIJ = store_thm
  ("NUM_2D_BIJ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> REVERSE CONJ_TAC
   >- (Q.EXISTS_TAC `FST`
       >> RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       >> Q.EXISTS_TAC `(x, 0)`
       >> RW_TAC std_ss [FST])
   >> Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   >> RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> Cases_on `x`
   >> Cases_on `y`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_INV = store_thm
  ("NUM_2D_BIJ_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       ((UNIV : num -> bool) CROSS (UNIV : num -> bool))``,
   PROVE_TAC [NUM_2D_BIJ, BIJ_SYM]);

val BIJ_FINITE_SUBSET = store_thm
  ("BIJ_FINITE_SUBSET",
   ``!(f : num -> 'a) s t.
       BIJ f UNIV s /\ FINITE t /\ t SUBSET s ==>
       ?N. !n. N <= n ==> ~(f n IN t)``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`t`, `t`)
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [EMPTY_SUBSET, NOT_IN_EMPTY, INSERT_SUBSET, IN_INSERT]
   >> Know `?!k. f k = e`
   >- (Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
       >> RW_TAC std_ss [BIJ_ALT_RES, RES_EXISTS_UNIQUE_UNIV, RES_FORALL]
       >> PROVE_TAC [])
   >> CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   >> RW_TAC std_ss []
   >> RES_TAC
   >> Q.EXISTS_TAC `MAX N (SUC k)`
   >> RW_TAC std_ss [MAX_LE_X]
   >> STRIP_TAC
   >> Know `n = k` >- PROVE_TAC []
   >> DECIDE_TAC);

val NUM_2D_BIJ_SMALL_SQUARE = store_thm
  ("NUM_2D_BIJ_SMALL_SQUARE",
   ``!(f : num -> num # num) k.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?N. count k CROSS count k SUBSET IMAGE f (count N)``,
   Strip
   >> (MP_TAC o
       Q.SPECL [`f`, `UNIV CROSS UNIV`, `count k CROSS count k`] o
       INST_TYPE [``:'a`` |-> ``:num # num``]) BIJ_FINITE_SUBSET
   >> RW_TAC std_ss [CROSS_SUBSET, SUBSET_UNIV, FINITE_CROSS, FINITE_COUNT]
   >> Q.EXISTS_TAC `N`
   >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   >> Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
   >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `y`
   >> RW_TAC std_ss []
   >> Suff `~(N <= y)` >- DECIDE_TAC
   >> PROVE_TAC []);

val NUM_2D_BIJ_BIG_SQUARE = store_thm
  ("NUM_2D_BIJ_BIG_SQUARE",
   ``!(f : num -> num # num) N.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?k. IMAGE f (count N) SUBSET count k CROSS count k``,
   RW_TAC std_ss [IN_CROSS, IN_COUNT, SUBSET_DEF, IN_IMAGE, IN_COUNT]
   >> Induct_on `N` >- RW_TAC arith_ss []
   >> Strip
   >> Cases_on `f N`
   >> REWRITE_TAC [prim_recTheory.LESS_THM]
   >> Q.EXISTS_TAC `SUC (MAX k (MAX q r))`
   >> Know `!a b. a < SUC b = a <= b`
   >- (KILL_TAC
       >> DECIDE_TAC)
   >> RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ]);

val BIGUNION_EQ_EMPTY = store_thm
  ("BIGUNION_EQ_EMPTY",
   ``!a. (BIGUNION a = {}) = (!s. s IN a ==> (s = {}))``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, NOT_IN_EMPTY]
   >> PROVE_TAC []);

val IN_BIGUNION_IMAGE = store_thm
  ("IN_BIGUNION_IMAGE",
   ``!f s y. y IN BIGUNION (IMAGE f s) = ?x. x IN s /\ y IN f x``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE]
   >> PROVE_TAC []);

val FINITE_SUBSET_COUNT = store_thm
  ("FINITE_SUBSET_COUNT",
   ``!s. FINITE s = ?n. s SUBSET count n``,
   STRIP_TAC
   >> REVERSE EQ_TAC >- PROVE_TAC [FINITE_COUNT, SUBSET_FINITE]
   >> REWRITE_TAC [FINITE_DEF]
   >> DISCH_THEN (MP_TAC o Q.SPEC `\s. ?N. !n. n IN s ==> n <= N`)
   >> RW_TAC std_ss [SUBSET_DEF, IN_COUNT]
   >> Suff `?N. !n. n IN s ==> n <= N`
   >- (RW_TAC std_ss []
       >> Q.EXISTS_TAC `SUC N`
       >> Know `!x y. x < SUC y = x <= y` >- DECIDE_TAC
       >> RW_TAC std_ss [])
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
   >> Q.EXISTS_TAC `MAX N e`
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [X_LE_MAX, LESS_EQ_REFL]);

val INFINITE_DIFF_FINITE_EQ = store_thm
  ("INFINITE_DIFF_FINITE_EQ",
   ``!s t. FINITE t ==> (INFINITE (s DIFF t) = INFINITE s)``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- PROVE_TAC [SUBSET_FINITE, DIFF_SUBSET]
   >> Suff `s SUBSET (t UNION (s DIFF t))`
   >- PROVE_TAC [FINITE_UNION, SUBSET_FINITE]
   >> RW_TAC std_ss [SUBSET_DEF, IN_UNION, IN_DIFF]);

val INFINITE_DELETE = store_thm
  ("INFINITE_DELETE",
   ``!x s. INFINITE (s DELETE x) = INFINITE s``,
   RW_TAC std_ss [DELETE_DEF]
   >> PROVE_TAC [INFINITE_DIFF_FINITE_EQ, FINITE_SING, SING]);

val FINITE_TL = store_thm
  ("FINITE_TL",
   ``!s : bool list -> bool. FINITE (IMAGE TL s) = FINITE s``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- PROVE_TAC [IMAGE_FINITE]
   >> RW_TAC std_ss []
   >> Know `FINITE (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s))`
   >- PROVE_TAC [IMAGE_FINITE]
   >> STRIP_TAC
   >> Know `FINITE (BIGUNION (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s)))`
   >- (MATCH_MP_TAC FINITE_BIGUNION
       >> RW_TAC std_ss [IN_IMAGE]
       >> RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY])
   >> Suff `s SUBSET BIGUNION (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s))`
   >- PROVE_TAC [SUBSET_FINITE]
   >> KILL_TAC
   >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_IMAGE, IN_INSERT,
                     NOT_IN_EMPTY]
   >> Cases_on `x`
   >- (RW_TAC std_ss []
       >> PROVE_TAC [])
   >> Cases_on `h`
   >> RW_TAC std_ss []
   >> PROVE_TAC [TL]);

val IMAGE_o_INV = store_thm
  ("IMAGE_o_INV",
   ``!s f. (IMAGE f (s o f)) SUBSET s /\ s SUBSET ((IMAGE f s) o f)``,
   RW_TAC std_ss [IN_o, IN_IMAGE, SUBSET_DEF]
   >> PROVE_TAC []);

val BIGUNION_PAIR = store_thm
  ("BIGUNION_PAIR",
   ``!s t. BIGUNION {s; t} = s UNION t``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_UNION, IN_INSERT, NOT_IN_EMPTY]
   >> PROVE_TAC []);

val BIGUNION_IMAGE_UNIV = store_thm
  ("BIGUNION_IMAGE_UNIV",
   ``!f N.
       (!n. N <= n ==> (f n = {})) ==>
       (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N)))``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_COUNT,
                  NOT_IN_EMPTY]
   >> REVERSE EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> PROVE_TAC [NOT_LESS]);

val PREIMAGE_DISJOINT = store_thm
  ("PREIMAGE_DISJOINT",
   ``!f s t. DISJOINT s t ==> DISJOINT (PREIMAGE f s) (PREIMAGE f t)``,
   RW_TAC std_ss [DISJOINT_DEF, GSYM PREIMAGE_INTER, PREIMAGE_EMPTY]);

val PREIMAGE_SUBSET = store_thm
  ("PREIMAGE_SUBSET",
   ``!f s t. s SUBSET t ==> PREIMAGE f s SUBSET PREIMAGE f t``,
   RW_TAC std_ss [SUBSET_DEF, PREIMAGE_def, GSPECIFICATION]);

val SUBSET_ADD = store_thm
  ("SUBSET_ADD",
   ``!f n d.
       (!n. f n SUBSET f (SUC n)) ==>
       f n SUBSET f (n + d)``,
   RW_TAC std_ss []
   >> Induct_on `d` >- RW_TAC arith_ss [SUBSET_REFL]
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `f (n + d)`
   >> RW_TAC std_ss []);

val DISJOINT_DIFFS = store_thm
  ("DISJOINT_DIFFS",
   ``!f m n.
       (!n. f n SUBSET f (SUC n)) /\
       (!n. g n = f (SUC n) DIFF f n) /\ ~(m = n) ==>
       DISJOINT (g m) (g n)``,
   RW_TAC std_ss []
   >> Know `SUC m <= n \/ SUC n <= m` >- DECIDE_TAC
   >> REWRITE_TAC [LESS_EQ_EXISTS]
   >> STRIP_TAC >|
   [Know `f (SUC m) SUBSET f n` >- PROVE_TAC [SUBSET_ADD]
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    >> PROVE_TAC [],
    Know `f (SUC n) SUBSET f m` >- PROVE_TAC [SUBSET_ADD]
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    >> PROVE_TAC []]);

val PREIMAGE_COMP = store_thm
  ("PREIMAGE_COMP",
   ``!f g s. PREIMAGE f (PREIMAGE g s) = PREIMAGE (g o f) s``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, o_THM]);

val PREIMAGE_K = store_thm
  ("PREIMAGE_K",
   ``!x s. PREIMAGE (K x) s = if x IN s then UNIV else {}``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, K_THM, IN_UNIV, NOT_IN_EMPTY]);

val INSERT_CASES = store_thm
  ("INSERT_CASES",
   ``!P. P {} /\ (!x s. ~(x IN s) ==> P (x INSERT s)) ==> (!s. P s)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `s` SET_CASES)
   >> RW_TAC std_ss []
   >> PROVE_TAC []);

val BOOL_SET_CASES = store_thm
  ("BOOL_SET_CASES",
   ``!P. P {} /\ P {T} /\ P {F} /\ P UNIV ==> (!x. P x)``,
   NTAC 2 STRIP_TAC
   >> HO_MATCH_MP_TAC INSERT_CASES
   >> ASM_REWRITE_TAC []
   >> STRIP_TAC
   >> HO_MATCH_MP_TAC INSERT_CASES
   >> (Cases_on `x`
       >> ASM_REWRITE_TAC []
       >> Cases
       >> RW_TAC std_ss [IN_INSERT]) >|
   [Suff `T INSERT F INSERT x'' = UNIV`
    >- PROVE_TAC []
    >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT],
    Suff `F INSERT T INSERT x'' = UNIV`
    >- PROVE_TAC []
    >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT]]);

val COMPL_INTER = store_thm
  ("COMPL_INTER",
   ``!s t. COMPL (s INTER t) = COMPL s UNION COMPL t``,
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION]);

val COUNTABLE_BIGUNION = store_thm
  ("COUNTABLE_BIGUNION",
   ``!c.
       countable c /\ (!s. s IN c ==> countable s) ==> countable (BIGUNION c)``,
   PROVE_TAC [bigunion_countable]);

val COUNTABLE_BOOL_LIST = store_thm
  ("COUNTABLE_BOOL_LIST",
   ``!s : bool list -> bool. countable s``,
   STRIP_TAC
   >> MATCH_MP_TAC COUNTABLE_SUBSET
   >> Q.EXISTS_TAC `UNIV`
   >> RW_TAC std_ss [SUBSET_UNIV]
   >> Know
      `(UNIV : bool list -> bool) =
       BIGUNION (IMAGE (\x. PREIMAGE LENGTH {x}) UNIV)`
   >- RW_TAC std_ss [EXTENSION, IN_UNIV, IN_BIGUNION_IMAGE, IN_PREIMAGE,
                     IN_SING]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC COUNTABLE_BIGUNION
   >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM, IN_IMAGE, IN_UNIV]
   >> Induct_on `x`
   >- (RW_TAC std_ss [COUNTABLE_ALT, IN_PREIMAGE, IN_SING, LENGTH_NIL]
       >> Q.EXISTS_TAC `K []`
       >> RW_TAC std_ss [K_THM])
   >> Know
      `PREIMAGE LENGTH {SUC x} =
       IMAGE (CONS T) (PREIMAGE LENGTH {x}) UNION
       IMAGE (CONS F) (PREIMAGE LENGTH {x})`
   >- (RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_IMAGE, IN_SING, IN_UNION]
       >> Cases_on `x'` >- RW_TAC std_ss [LENGTH]
       >> RW_TAC std_ss [LENGTH]
       >> PROVE_TAC [])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC union_countable
   >> RW_TAC std_ss [image_countable]);

val INTER_BIGUNION = store_thm
  ("INTER_BIGUNION",
   ``!s a. s INTER BIGUNION a = BIGUNION (IMAGE ($INTER s) a)``,
   RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION_IMAGE]
   >> RW_TAC std_ss [IN_BIGUNION]
   >> PROVE_TAC []);

val FINITE_DISJOINT_ENUM = store_thm
  ("FINITE_DISJOINT_ENUM",
   ``!c.
       FINITE c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))``,
   RW_TAC std_ss []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`c`, `c`)
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
   >- (Q.EXISTS_TAC `K {}`
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, EXTENSION, IN_SING, K_THM,
                         DISJOINT_EMPTY, IN_BIGUNION, IN_IMAGE, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> Know `!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t`
   >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `f IN X` MP_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT]
   >> Q.EXISTS_TAC `\x. num_CASE x e f`
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT]
       >> Cases_on `x`
       >> RW_TAC std_ss [num_case_def]
       >> PROVE_TAC [])
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `X = Y` MP_TAC
       >> RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE]
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IN_INSERT, IN_IMAGE, IN_UNIV, IN_BIGUNION]
       >> EQ_TAC >|
       [RW_TAC std_ss [] >|
        [Q.EXISTS_TAC `0`
         >> RW_TAC std_ss [num_case_def],
         Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
         >> Know `?s. x IN s /\ s IN c` >- PROVE_TAC []
         >> RW_TAC std_ss []
         >> Q.EXISTS_TAC `SUC x'`
         >> RW_TAC std_ss [num_case_def]],
        RW_TAC std_ss []
        >> (Cases_on `x'`
            >> POP_ASSUM MP_TAC
            >> RW_TAC std_ss [num_case_def])
        >- PROVE_TAC []
        >> PROVE_TAC [NOT_IN_EMPTY]])
   >> (Cases >> Cases)
   >> RW_TAC arith_ss [num_case_def]
   >> PROVE_TAC [DISJOINT_EMPTY]);

val COUNTABLE_DISJOINT_ENUM = store_thm
  ("COUNTABLE_DISJOINT_ENUM",
   ``!c.
       countable c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))``,
   RW_TAC std_ss [COUNTABLE_ALT_BIJ]
   >- (MP_TAC (Q.SPEC `c` FINITE_DISJOINT_ENUM)
       >> RW_TAC std_ss [])
   >> Q.EXISTS_TAC `enumerate c`
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_FUNSET, IN_INSERT,
                     EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, INJ_DEF]
   >> PROVE_TAC []);

val COMPL_BIGINTER = store_thm
  ("COMPL_BIGINTER",
   ``!s. COMPL (BIGINTER s) = BIGUNION (IMAGE COMPL s)``,
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER, IN_BIGUNION_IMAGE]);

val IN_BIGINTER_IMAGE = store_thm
  ("IN_BIGINTER_IMAGE",
   ``!x f s. x IN BIGINTER (IMAGE f s) = (!y. y IN s ==> x IN f y)``,
   RW_TAC std_ss [IN_BIGINTER, IN_IMAGE]
   >> PROVE_TAC []);

val IMAGE_K = store_thm
  ("IMAGE_K",
   ``!x s. IMAGE (K x) s = if s = {} then {} else {x}``,
   RW_TAC std_ss [EXTENSION, IN_IMAGE, K_THM, NOT_IN_EMPTY, IN_SING]
   >> PROVE_TAC []);

val FINITE_BOOL = store_thm
  ("FINITE_BOOL",
   ``!s : bool -> bool. FINITE s``,
   Suff `FINITE (UNIV : bool -> bool)` >- PROVE_TAC [SUBSET_FINITE, SUBSET_UNIV]
   >> Suff `UNIV = {T; F}`
   >- RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]
   >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY]);

val COUNTABLE_BOOL = store_thm
  ("COUNTABLE_BOOL",
   ``!s : bool -> bool. countable s``,
   PROVE_TAC [finite_countable, FINITE_BOOL]);

val COUNTABLE_SING = store_thm
  ("COUNTABLE_SING",
   ``!x. countable {x}``,
   PROVE_TAC [finite_countable, FINITE_SING]);

val ALWAYS_IN_RANGE = store_thm
  ("ALWAYS_IN_RANGE",
   ``!f x. f x IN range f``,
   RW_TAC std_ss [range_def, IN_IMAGE, IN_UNIV]
   >> PROVE_TAC []);

val RANGE_NONEMPTY = store_thm
  ("RANGE_NONEMPTY",
   ``!f. ~(range f = {})``,
   RW_TAC std_ss [range_def, EXTENSION, NOT_IN_EMPTY, IN_IMAGE, IN_UNIV]);

val PREIMAGE_INTER_RANGE = store_thm
  ("PREIMAGE_INTER_RANGE",
   ``!f s. PREIMAGE f (s INTER range f) = PREIMAGE f s``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER, ALWAYS_IN_RANGE]);

val PREIMAGE_INTER_SUPER_RANGE = store_thm
  ("PREIMAGE_INTER_SUPER_RANGE",
   ``!f s t. range f SUBSET t ==> (PREIMAGE f (s INTER t) = PREIMAGE f s)``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER, SUBSET_DEF]
   >> PROVE_TAC [ALWAYS_IN_RANGE]);

val RANGE_BIND = store_thm
  ("RANGE_BIND",
   ``!f g.
       range (FST o BIND f g) SUBSET
       BIGUNION (IMAGE (range o (\x. FST o g x)) (range (FST o f)))``,
   RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, range_def, IN_IMAGE, IN_UNIV,
                  o_THM, BIND_DEF, UNCURRY]
   >> PROVE_TAC [FST, SND]);

val GEMPTY = store_thm
  ("GEMPTY",
   ``{s | F} = {}``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]);

val GUNIV = store_thm
  ("GUNIV",
   ``{s | T} = UNIV``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNIV]);

val GSPEC_DEST = store_thm
  ("GSPEC_DEST",
   ``!p. {s | p s} = p``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]);

val GUNION = store_thm
  ("GUNION",
   ``!p q. {s | p s \/ q s} = {s | p s} UNION {s | q s}``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION]);

val GDEST = store_thm
  ("GDEST",
   ``!p. {s | s IN p} = p``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]);

val GBIGUNION_IMAGE = store_thm
  ("GBIGUNION_IMAGE",
   ``!s p n. {s | ?n. p s n} = BIGUNION (IMAGE (\n. {s | p s n}) UNIV)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV]);

val GINTER = store_thm
  ("GINTER",
   ``!p q. {s | p s /\ q s} = {s | p s} INTER {s | q s}``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]);

val BIGUNION_IMAGE_INSIDE = store_thm
  ("BIGUNION_IMAGE_INSIDE",
   ``!f g s.
       BIGUNION (IMAGE f (BIGUNION (IMAGE g s))) =
       BIGUNION (IMAGE (BIGUNION o IMAGE f o g) s)``,
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_BIGUNION_IMAGE, o_THM]
   >> PROVE_TAC []);

val GCOMPL = store_thm
  ("GCOMPL",
   ``!p. {s | ~p s} = COMPL {s | p s}``,
   SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, IN_COMPL]);

val IN_I = store_thm
  ("IN_I",
   ``!x. x IN I = x``,
   RW_TAC std_ss [SPECIFICATION, I_THM]);

val COMPL_o = store_thm
  ("COMPL_o",
   ``!p q. COMPL p o q = COMPL (p o q)``,
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_COMPL, IN_o]);

val FST_o_UNIT = store_thm
  ("FST_o_UNIT",
   ``!p a. p o FST o UNIT a = if a IN p then UNIV else {}``,
   SET_EQ_TAC
   >> RW_TAC std_ss [o_THM, UNIT_DEF, IN_o, IN_UNIV, NOT_IN_EMPTY]);

val IS_SOME_MMAP = store_thm
  ("IS_SOME_MMAP",
   ``!f. {x | IS_SOME x} o FST o MMAP SOME f = UNIV``,
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_UNIV, IN_o, o_THM, MMAP_DEF, BIND_DEF, UNCURRY,
                     UNIT_DEF, GSPECIFICATION]);

val IS_SOME_INTER_MMAP = store_thm
  ("IS_SOME_INTER_MMAP",
   ``!p f.
       ((p o THE) INTER {x | IS_SOME x}) o FST o MMAP SOME f = p o FST o f``,
   SET_EQ_TAC
   >> RW_TAC std_ss [o_THM, MMAP_DEF, BIND_DEF, UNCURRY, UNIT_DEF, IN_INTER,
                     IN_o, GSPECIFICATION]);

val SET_PAIR_BOOL = store_thm
  ("SET_PAIR_BOOL",
   ``!s.
       s =
       (if (T, T) IN s then {(T, T)} else {}) UNION
       (if (T, F) IN s then {(T, F)} else {}) UNION
       (if (F, T) IN s then {(F, T)} else {}) UNION
       (if (F, F) IN s then {(F, F)} else {})``,
   STRIP_TAC
   >> SET_EQ_TAC
   >> Cases
   >> Cases_on `q`
   >> Cases_on `r`
   >> RW_TAC std_ss [IN_UNION, IN_SING, NOT_IN_EMPTY]);

val FINITE_PAIR_BOOL = store_thm
  ("FINITE_PAIR_BOOL",
   ``!s:bool#bool->bool. FINITE s``,
   RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [SET_PAIR_BOOL]
   >> RW_TAC std_ss [FINITE_UNION, FINITE_INSERT, FINITE_EMPTY]);

val _ = export_theory ();
