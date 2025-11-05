Theory extra_pred_set
Ancestors
  arithmetic combin pred_set list rich_list res_quan extra_list
  extra_num pair state_transformer subtype
Libs
  hurdUtils res_quanTools simpLib ho_proverTools subtypeTools
  boolContext listContext

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

val std_pc = precontext_mergel [bool_pc, list_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

Definition IMAGE2_def:   IMAGE2 f s t = {f x y | x IN s /\ y IN t}
End

Definition UNIONL_def:   (UNIONL [] = {})
  /\ (UNIONL (s::ss) = (s:'a->bool) UNION UNIONL ss)
End

Definition DISJOINTL_def:
   (DISJOINTL [] = T) /\
   (DISJOINTL (s::ss) = (DISJOINT (s:'a->bool) (UNIONL ss) /\ DISJOINTL ss))
End

Definition set_def:   set p s = (s SUBSET p)
End

Definition nonempty_def:   nonempty s = ~(s = {})
End

Definition range_def:   range f = IMAGE f UNIV
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem IN_o:
     !x f s. x IN (s o f) <=> f x IN s
Proof
   RW_TAC std_ss [SPECIFICATION, o_THM]
QED

Theorem UNION_DEF_ALT:
     !s t. s UNION t = (\x:'a. s x \/ t x)
Proof
   REPEAT STRIP_TAC
   >> Suff `!v:'a. v IN (s UNION t) <=> v IN (\x. s x \/ t x)`
     >- (PURE_REWRITE_TAC [SPECIFICATION]
         >> PROVE_TAC [EQ_EXT])
   >> RW_TAC std_ss [UNION_DEF, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]
QED

Theorem INTER_UNION_RDISTRIB:
     !(p:'a->bool) q r. (p UNION q) INTER r = p INTER r UNION q INTER r
Proof
   RW_TAC std_ss [EXTENSION, IN_UNION, IN_INTER]
   >> PROVE_TAC []
QED

Theorem INTER_IS_EMPTY:
     !(s:'a->bool) t. (s INTER t = {}) <=> (!x. ~s x \/ ~t x)
Proof
   RW_TAC std_ss [INTER_DEF, EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION, EMPTY_DEF]
QED

Theorem GSPEC_DEF_ALT:
     !(f:'a -> 'b # bool). GSPEC f = (\v. ?x. (v, T) = f x)
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]
QED

Theorem UNION_DISJOINT_SPLIT:
     !(s:'a->bool) t u. (s UNION t = s UNION u)
                        /\ (s INTER t = {}) /\ (s INTER u = {})
                        ==> (t = u)
Proof
   RW_TAC std_ss [UNION_DEF_ALT, EXTENSION, INTER_IS_EMPTY, SPECIFICATION]
   >> PROVE_TAC []
QED

Theorem INSERT_THM1:
     !(x:'a) s. x IN (x INSERT s)
Proof RW_TAC std_ss [IN_INSERT]
QED

Theorem INSERT_THM2:
     !(x:'a) y s. x IN s ==> x IN (y INSERT s)
Proof RW_TAC std_ss [IN_INSERT]
QED

Theorem IMAGE_THM:
     !(f:'a->'b) x s. x IN s ==> f x IN IMAGE f s
Proof
    RW_TAC std_ss [IN_IMAGE]
    >> PROVE_TAC []
QED

Theorem ELT_IN_DELETE:
     !x s. ~(x IN (s DELETE x))
Proof
   RW_TAC std_ss [IN_DELETE]
QED

Theorem FINITE_INTER:
     !s. FINITE s ==> !t. FINITE (t INTER s)
Proof
   PROVE_TAC [INTER_FINITE, INTER_COMM]
QED

Theorem IN_IMAGE2:
     !x f s t. x IN IMAGE2 f s t <=> ?a b. a IN s /\ b IN t /\ (f a b = x)
Proof
   RW_TAC std_ss [IMAGE2_def, GSPECIFICATION]
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> POP_ASSUM MP_TAC
    >> Cases_on `x'`
    >> RW_TAC std_ss []
    >> PROVE_TAC [],
    RW_TAC std_ss []
    >> Q.EXISTS_TAC `(a, b)`
    >> RW_TAC std_ss []]
QED

Theorem CONJ_IMAGE2:
     !a b s t.
       (b ==> a IN s) /\ (a ==> b IN t) ==>
       ((a /\ b) IN ({F} UNION IMAGE2 $/\ s t))
Proof
   RW_TAC std_ss [IN_UNION, IN_IMAGE2, IN_INSERT, NOT_IN_EMPTY]
   >> Suff `a /\ b ==> ?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' <=> a /\ b)`
   >- (Q.SPEC_TAC (`?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' <=> a /\ b)`, `q`)
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> PROVE_TAC []
QED

Theorem INJ_SUBSET:
     !f s s' t. INJ f s t /\ s' SUBSET s ==> INJ f s' t
Proof
   RW_TAC std_ss [INJ_DEF, SUBSET_DEF]
QED

Theorem CARD_IMAGE:
     !f s t. FINITE s /\ INJ f s t ==> (CARD (IMAGE f s) = CARD s)
Proof
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
   >> PROVE_TAC [IN_INSERT]
QED

val CARD_IMAGE2_lem = prove (
  ``!P. FINITE P ==>
        (\P. (!f. (!x y. x IN P /\ y IN P /\ (f x = f y) ==> (x = y)) ==>
                  (CARD (IMAGE f P) = CARD P))) P``,
    MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, CARD_EMPTY, CARD_INSERT,
                   IMAGE_FINITE, IN_IMAGE]
 >> `~?x. (f e = f x) /\ x IN s` by METIS_TAC [IN_INSERT]
 >> RW_TAC arith_ss []
 >> Q.PAT_X_ASSUM `!f. b ==> (c = d)` MATCH_MP_TAC
 >> METIS_TAC [IN_INSERT]);

Theorem CARD_IMAGE2:
    !P. FINITE P ==>
        (!f. (!x y. x IN P /\ y IN P /\ (f x = f y) ==> (x = y)) ==>
             (CARD (IMAGE f P) = CARD P))
Proof
   METIS_TAC [CARD_IMAGE2_lem]
QED

Theorem CARD_SUBSET_PROPER:
     !(s:'a->bool) t.
        FINITE t /\ s SUBSET t ==> ((CARD s = CARD t) <=> (s = t))
Proof
   RW_TAC std_ss []
   >> Cases_on `s = t` >- PROVE_TAC []
   >> Know `s PSUBSET t` >- PROVE_TAC [PSUBSET_DEF]
   >> STRIP_TAC
   >> MP_TAC (Q.SPEC `t` CARD_PSUBSET)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `s`)
   >> RW_TAC arith_ss []
QED

Theorem FINITE_UNIONL:
     !(ss:('a->bool) list). FINITE (UNIONL ss) = EVERY FINITE ss
Proof
   Induct >- RW_TAC list_ss [UNIONL_def, FINITE_EMPTY]
   >> RW_TAC list_ss [UNIONL_def, FINITE_UNION]
QED

Theorem CARD_UNIONL:
     !(ss:('a->bool) list). EVERY FINITE ss /\ DISJOINTL ss
          ==> (CARD (UNIONL ss) = SUM (MAP CARD ss))
Proof
   Induct >- RW_TAC list_ss [DISJOINTL_def, UNIONL_def, SUM, CARD_DEF]
   >> RW_TAC list_ss [DISJOINTL_def, UNIONL_def, SUM]
   >> Know `FINITE (UNIONL ss)` >- RW_TAC std_ss [FINITE_UNIONL]
   >> MP_TAC (Q.SPECL [`h`] CARD_UNION)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `UNIONL ss`)
   >> Q.PAT_X_ASSUM `DISJOINT a b` MP_TAC
   >> RW_TAC arith_ss [DISJOINT_DEF, CARD_DEF]
QED

Theorem IN_UNIONL:
     !l (v:'a). v IN UNIONL l <=> (?s. MEM s l /\ v IN s)
Proof
   Induct >- RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
   >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
   >> PROVE_TAC []
QED

val DISJOINT_UNION1 = DISJOINT_UNION;
val DISJOINT_UNION2 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNION1;

Theorem DISJOINT_UNIONL2:
     !l (x:'a->bool). DISJOINT x (UNIONL l) <=> (!y. MEM y l ==> DISJOINT x y)
Proof
   Induct >- RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_DEF, INTER_EMPTY]
   >> RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_UNION2]
   >> PROVE_TAC []
QED
val DISJOINT_UNIONL1 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNIONL2;

Theorem DISJOINTL_KILL_DUPS:
  !(l:('a->bool) list).
    DISJOINTL (nub l) = (!x y. MEM x l /\ MEM y l ==> (x = y) \/ DISJOINT x y)
Proof
  Induct >> rw[DISJOINTL_def, nub_def, DISJOINT_UNIONL2] >>
  metis_tac[DISJOINT_SYM]
QED

Theorem NUM_TO_FINITE:
     !s (f:num->'a).
       FINITE s /\ (!n. f n IN s) ==> ?i j. i < j /\ (f i = f j)
Proof
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
    >> DECIDE_TAC]
QED

Theorem SURJ_ALT:
     !f s t. SURJ f s t <=> f IN (s -> t) /\ (!y :: t. ?x :: s. y = f x)
Proof
   RW_TAC std_ss [SURJ_DEF]
   >> RESQ_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_DFUNSET]
   >> PROVE_TAC []
QED

Theorem BIJ_ALT_RES:
     !f s t. BIJ f s t <=> f IN (s -> t) /\ (!y :: t. ?!x :: s. y = f x)
Proof
   S_TAC
   >> R_TAC [BIJ_DEF, INJ_DEF, SURJ_DEF, RES_EXISTS_UNIQUE_ALT]
   >> RESQ_TAC
   >> R_TAC [IN_FUNSET, IN_DFUNSET, GSYM CONJ_ASSOC]
   >> Know `!a b c. (a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)` >- PROVE_TAC []
   >> DISCH_THEN MATCH_MP_TAC
   >> REPEAT (STRIP_TAC ORELSE EQ_TAC) >|
   [PROVE_TAC [],
    Q.PAT_X_ASSUM `!x. P x`
    (fn th =>
     MP_TAC (Q.SPEC `(f:'a->'b) x` th)
     >> MP_TAC (Q.SPEC `(f:'a->'b) y` th))
    >> impl_tac >- PROVE_TAC []
    >> STRIP_TAC
    >> impl_tac >- PROVE_TAC []
    >> STRIP_TAC
    >> PROVE_TAC [],
    PROVE_TAC []]
QED

Theorem DELETE_THEN_INSERT:
     !s. !x :: s. x INSERT (s DELETE x) = s
Proof
   RESQ_TAC
   >> RW_TAC std_ss [INSERT_DELETE]
QED

Theorem BIJ_INSERT:
     !f e s t.
       ~(e IN s) /\ BIJ f (e INSERT s) t ==>
       ?u. (f e INSERT u = t) /\ ~(f e IN u) /\ BIJ f s u
Proof
   RW_TAC std_ss [BIJ_ALT]
   >> Q.EXISTS_TAC `t DELETE f e`
   >> FULL_SIMP_TAC std_ss [IN_FUNSET, DELETE_THEN_INSERT, ELT_IN_DELETE, IN_INSERT,
              DISJ_IMP_THM]
   >> RESQ_TAC
   >> SIMP_TAC std_ss [IN_DELETE]
   >> REPEAT STRIP_TAC
   >> METIS_TAC [IN_INSERT]
QED

Theorem BIJ_INSERT_NOTIN:
     !f e s t.
       ~(e IN s) /\ BIJ f (e INSERT s) t ==>
       ?u. (f e INSERT u = t) /\ ~(f e IN u) /\ BIJ f s u
Proof
   R_TAC [BIJ_ALT_RES]
   >> S_TAC
   >> Q.EXISTS_TAC `t DELETE f e`
   >> AR_TAC [IN_FUNSET, DELETE_THEN_INSERT, ELT_IN_DELETE, IN_INSERT,
              DISJ_IMP_THM]
   >> RESQ_TAC
   >> AR_TAC [IN_DELETE, IN_INSERT]
   >> REPEAT STRIP_TAC
   >> METIS_TAC []
QED

Theorem FINITE_MAXIMAL:
     !f s. FINITE s /\ ~(s = {}) ==> ?x :: s. !y :: s. (f y:num) <= f x
Proof
   STRIP_TAC >> SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
   >> RESQ_TAC
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss []
   >> Cases_on `s = {}`
   >- FULL_SIMP_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
   >> RES_TAC
   >> S_TAC
   >> Know `(f:'a->num) e <= f x \/ f x <= f e` >- DECIDE_TAC
   >> S_TAC >|
   [Q.EXISTS_TAC `x`
    >> RW_TAC std_ss [IN_INSERT]
    >- ASM_REWRITE_TAC []
    >> Q.PAT_X_ASSUM `!y. y IN s ==> f y <= f x` MATCH_MP_TAC
    >> ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `e`
    >> RW_TAC arith_ss [IN_INSERT, LESS_EQ_REFL]
    >- DECIDE_TAC
    >> Q.PAT_X_ASSUM `!y. y IN s ==> f y <= f x` (MP_TAC o UNDISCH o Q.SPEC `y`)
    >> POP_ASSUM (K ALL_TAC)
    >> POP_ASSUM MP_TAC
    >> DECIDE_TAC]
QED

Theorem EMPTY_UNION_ALT:
     !s t. ({} = s UNION t) <=> (s = {}) /\ (t = {})
Proof
   PROVE_TAC [EMPTY_UNION]
QED

Theorem IN_SET:
     !s p. s IN set p <=> s SUBSET p
Proof
   RW_TAC std_ss [SPECIFICATION, set_def]
QED

Theorem IN_NONEMPTY:
     !s p. s IN nonempty <=> ~(s = {})
Proof
   RW_TAC std_ss [SPECIFICATION, nonempty_def]
QED

Theorem IN_FINITE:
     !s. s IN FINITE <=> FINITE s
Proof
   RW_TAC std_ss [SPECIFICATION]
QED

Theorem EMPTY_SUBTYPE:
     !x. {} IN (set x INTER FINITE)
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET]
QED

Theorem INSERT_SUBTYPE:
     !x. $INSERT IN ((x -> set x -> set x) INTER
                     (UNIV -> FINITE -> FINITE) INTER
                     (UNIV -> UNIV -> nonempty))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY]
QED

Theorem INTER_SUBTYPE:
     !x. $INTER IN ((set x -> UNIV -> set x) INTER
                    (UNIV -> set x -> set x) INTER
                    (UNIV -> FINITE -> FINITE) INTER
                    (FINITE -> UNIV -> FINITE))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF]
QED

Theorem UNION_SUBTYPE:
     !x. $UNION IN ((set x -> set x -> set x) INTER
                    (FINITE -> FINITE -> FINITE) INTER
                    (UNIV -> nonempty -> nonempty))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION,
                  IN_NONEMPTY, EMPTY_UNION]
   >> PROVE_TAC []
QED

Theorem CHOICE_SUBTYPE:
     !x. CHOICE IN ((nonempty INTER set x) -> x)
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION, IN_NONEMPTY,
                  CHOICE_DEF]
QED

Theorem REST_SUBTYPE:
     !x. REST IN ((FINITE -> FINITE) INTER
                  (set x -> set x))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INTER,
                  INTER_FINITE, SUBSET_DEF, FINITE_UNION, IN_UNION, IN_NONEMPTY,
                  CHOICE_DEF, REST_DEF, FINITE_DELETE, IN_DELETE]
QED

Theorem DELETE_SUBTYPE:
     !x. $DELETE IN ((set x -> UNIV -> set x) INTER
                     (FINITE -> UNIV -> FINITE))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY, FINITE_DELETE, SUBSET_DEF,
                  IN_DELETE]
QED

Theorem IMAGE_SUBTYPE:
     !x y. IMAGE IN (((x -> y) -> set x -> set y) INTER
                     (UNIV -> nonempty -> nonempty) INTER
                     (UNIV -> FINITE -> FINITE))
Proof
   RW_TAC std_ss [IN_SET, IN_INTER, IN_FINITE, FINITE_EMPTY, EMPTY_SUBSET,
                  IN_FUNSET, IN_UNIV, INSERT_SUBSET, FINITE_INSERT,
                  IN_NONEMPTY, NOT_INSERT_EMPTY, FINITE_DELETE, SUBSET_DEF,
                  IN_DELETE, IN_IMAGE, IMAGE_EQ_EMPTY, IMAGE_FINITE]
   >> PROVE_TAC []
QED

Theorem SET_UNIV:
     set UNIV = UNIV
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_SET, IN_UNIV, SUBSET_UNIV]
QED

Theorem SET_SUBSET:
     !x y. x SUBSET y ==> set x SUBSET set y
Proof
   RW_TAC std_ss [IN_SET, SUBSET_DEF]
QED

Theorem FINITE_SUBTYPE_JUDGEMENT:
     !s. FINITE s ==> s IN FINITE
Proof
   RW_TAC std_ss [SPECIFICATION]
QED

Theorem FINITE_SUBTYPE_REWRITE:
     !s. s IN FINITE ==> FINITE s
Proof
   RW_TAC std_ss [SPECIFICATION]
QED

Theorem NONEMPTY_SUBTYPE_JUDGEMENT:
     !s x. (x IN s) \/ ~(s = {}) \/ ~({} = s) ==> s IN nonempty
Proof
   REWRITE_TAC [IN_NONEMPTY]
   >> SET_EQ_TAC
   >> RW_TAC std_ss [NOT_IN_EMPTY]
   >> PROVE_TAC []
QED

Theorem NONEMPTY_SUBTYPE_REWRITE:
     !s. s IN nonempty ==> ~(s = {}) /\ ~({} = s)
Proof
   RW_TAC std_ss [SPECIFICATION, IN_NONEMPTY]
   >> PROVE_TAC []
QED

Theorem CARD_SUBTYPE:
     CARD IN ((FINITE INTER nonempty) -> gtnum 0)
Proof
   RW_TAC std_ss [IN_FUNSET, IN_NONEMPTY, IN_GTNUM, IN_INTER, IN_FINITE]
   >> S_TAC
   >> Suff `~(CARD x = 0)` >- DECIDE_TAC
   >> PROVE_TAC [CARD_EQ_0]
QED

Theorem INTER_DEF_ALT:
     !s t. s INTER t = (\x. s x /\ t x)
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_INTER, SPECIFICATION]
QED

Theorem FINITE_INTER_DISJ:
     !s t. FINITE s \/ FINITE t ==> FINITE (s INTER t)
Proof
   PROVE_TAC [FINITE_INTER, INTER_FINITE]
QED

Theorem FINITE_SUBSET_CARD_EQ:
     !s t. FINITE t /\ s SUBSET t /\ (CARD s = CARD t) ==> (s = t)
Proof
   S_TAC
   >> Suff `s SUBSET t /\ t SUBSET s`
   >- (KILL_TAC
       >> SET_EQ_TAC
       >> RW_TAC std_ss [SUBSET_DEF]
       >> PROVE_TAC [])
   >> Know `FINITE s` >- PROVE_TAC [SUBSET_FINITE]
   >> STRIP_TAC
   >> Know `FINITE t /\ s SUBSET t /\ (CARD s = CARD t)` >- PROVE_TAC []
   >> Q.SPEC_TAC (`t`, `t`)
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`s`, `s`)
   >> KILL_TAC
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> CONJ_TAC >- (RW_TAC std_ss [CARD_EMPTY, SUBSET_EMPTY] >> PROVE_TAC [CARD_EQ_0])
   >> RW_TAC std_ss []
   >> Know `?t'. ~(e IN t') /\ (t = e INSERT t')`
   >- (Q.EXISTS_TAC `t DELETE e`
       >> RW_TAC std_ss [IN_DELETE]
       >> MATCH_MP_TAC (GSYM INSERT_DELETE)
       >> FULL_SIMP_TAC std_ss [INSERT_SUBSET])
   >> S_TAC
   >> POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th, FINITE_INSERT, CARD_INSERT])
   >> RW_TAC std_ss [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT]
   >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
   >> Q.PAT_X_ASSUM `x SUBSET y` MP_TAC
   >> Q.PAT_X_ASSUM `CARD (e INSERT s) = CARD (e INSERT t')` MP_TAC
   >> ASM_SIMP_TAC std_ss [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT, CARD_INSERT]
QED

Theorem SUBSET_INTER1:
     !s t. s SUBSET t ==> (s INTER t = s)
Proof
   SET_EQ_TAC
   >> ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> PROVE_TAC []
QED

Theorem SUBSET_INTER2:
     !s t. s SUBSET t ==> (t INTER s = s)
Proof
   SET_EQ_TAC
   >> SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
   >> PROVE_TAC []
QED

Theorem FINITE_LESS:
     !n. FINITE (\x : num. x < n)
Proof
   Induct
   >- (Suff `(\x : num. x < 0) = {}`
       >- SIMP_TAC std_ss [FINITE_EMPTY]
       >> SET_EQ_TAC
       >> SIMP_TAC std_ss [SPECIFICATION, NOT_IN_EMPTY])
   >> Suff `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >- ASM_SIMP_TAC std_ss [FINITE_INSERT]
   >> SET_EQ_TAC
   >> SIMP_TAC std_ss [IN_INSERT]
   >> SIMP_TAC std_ss [SPECIFICATION]
   >> DECIDE_TAC
QED

Theorem FINITE_LESS1:
     !n s. FINITE (\x : num. x < n /\ s x)
Proof
   Strip
   >> SIMP_TAC std_ss [GSYM INTER_DEF_ALT]
   >> MATCH_MP_TAC FINITE_INTER_DISJ
   >> SIMP_TAC std_ss [FINITE_LESS]
QED

Theorem FINITE_LESS2:
     !n s. FINITE (\x : num. s x /\ x < n)
Proof
   Strip
   >> SIMP_TAC std_ss [GSYM INTER_DEF_ALT]
   >> MATCH_MP_TAC FINITE_INTER_DISJ
   >> SIMP_TAC std_ss [FINITE_LESS]
QED

Theorem CARD_LESS:
     !n. CARD (\x. x < n) = n
Proof
   Induct
   >- (Suff `(\x : num. x < 0) = {}`
       >- SIMP_TAC std_ss [CARD_EMPTY]
       >> SET_EQ_TAC
       >> SIMP_TAC std_ss [SPECIFICATION, NOT_IN_EMPTY])
   >> ASSUME_TAC (Q.SPEC `n` FINITE_LESS)
   >> Know `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >- (SET_EQ_TAC
       >> SIMP_TAC std_ss [IN_INSERT, SPECIFICATION]
       >> DECIDE_TAC)
   >> ASM_SIMP_TAC std_ss [CARD_INSERT]
   >> DISCH_THEN K_TAC
   >> Suff `~(n IN (\x. x < n))` >- SIMP_TAC std_ss []
   >> SIMP_TAC std_ss [SPECIFICATION]
QED

val FINITE_COUNTABLE = save_thm(
  "FINITE_COUNTABLE",
  pred_setTheory.finite_countable);

Theorem FINITE_REST:
     !s. FINITE (REST s) = FINITE s
Proof
   RW_TAC std_ss [REST_DEF, FINITE_DELETE]
QED

Theorem EXPLICIT_ENUMERATE_MONO:
     !n s. FUNPOW REST n s SUBSET s
Proof
   Induct >- RW_TAC std_ss [FUNPOW, SUBSET_DEF]
   >> RW_TAC std_ss [FUNPOW_SUC]
   >> PROVE_TAC [SUBSET_TRANS, REST_SUBSET]
QED

Theorem EXPLICIT_ENUMERATE_NOT_EMPTY:
     !n s. INFINITE s ==> ~(FUNPOW REST n s = {})
Proof
   REWRITE_TAC []
   >> Induct >- (RW_TAC std_ss [FUNPOW] >> PROVE_TAC [FINITE_EMPTY])
   >> RW_TAC std_ss [FUNPOW]
   >> Q.PAT_X_ASSUM `!s. P s` (MP_TAC o Q.SPEC `REST s`)
   >> PROVE_TAC [FINITE_REST]
QED

Theorem INFINITE_EXPLICIT_ENUMERATE:
     !s. INFINITE s ==> INJ (\n : num. CHOICE (FUNPOW REST n s)) UNIV s
Proof
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
    >> PROVE_TAC [FINITE_REST]]
QED

Theorem DIFF_ALT:
     !s t. s DIFF t = s INTER (COMPL t)
Proof
   RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER, IN_COMPL]
QED

Theorem DIFF_SUBSET:
     !a b. a DIFF b SUBSET a
Proof
   RW_TAC std_ss [SUBSET_DEF, EXTENSION, IN_DIFF]
QED

Theorem BIGUNION_EQ_EMPTY:
     !a. (BIGUNION a = {}) = (!s. s IN a ==> (s = {}))
Proof
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, NOT_IN_EMPTY]
   >> PROVE_TAC []
QED

Theorem FINITE_SUBSET_COUNT:
     !s. FINITE s = ?n. s SUBSET count n
Proof
   STRIP_TAC
   >> reverse EQ_TAC >- PROVE_TAC [FINITE_COUNT, SUBSET_FINITE]
   >> REWRITE_TAC [FINITE_DEF]
   >> DISCH_THEN (MP_TAC o Q.SPEC `\s. ?N. !n. n IN s ==> n <= N`)
   >> RW_TAC std_ss [SUBSET_DEF, IN_COUNT]
   >> Suff `?N. !n. n IN s ==> n <= N`
   >- (RW_TAC std_ss []
       >> Q.EXISTS_TAC `SUC N`
       >> Know `!x y. x < SUC y <=> x <= y` >- DECIDE_TAC
       >> RW_TAC std_ss [])
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
   >> Q.EXISTS_TAC `MAX N e`
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [X_LE_MAX, LESS_EQ_REFL]
QED

Theorem INFINITE_DIFF_FINITE_EQ:
     !s t. FINITE t ==> (INFINITE (s DIFF t) <=> INFINITE s)
Proof
   RW_TAC std_ss []
   >> reverse EQ_TAC >- PROVE_TAC [SUBSET_FINITE, DIFF_SUBSET]
   >> Suff `s SUBSET (t UNION (s DIFF t))`
   >- PROVE_TAC [FINITE_UNION, SUBSET_FINITE]
   >> RW_TAC std_ss [SUBSET_DEF, IN_UNION, IN_DIFF]
QED

Theorem INFINITE_DELETE:
     !x s. INFINITE (s DELETE x) <=> INFINITE s
Proof
   RW_TAC std_ss [DELETE_DEF]
   >> PROVE_TAC [INFINITE_DIFF_FINITE_EQ, FINITE_SING, SING]
QED

Theorem NOT_FINITE_NUM:
     ~FINITE (UNIV : num -> bool)
Proof
   RW_TAC std_ss [FINITE_SUBSET_COUNT, SUBSET_DEF, IN_UNIV, IN_COUNT]
   >> Q.EXISTS_TAC `n`
   >> RW_TAC arith_ss []
QED

Theorem INFINITE_NUM:
     INFINITE (UNIV : num -> bool)
Proof
   RW_TAC std_ss [NOT_FINITE_NUM]
QED

Theorem FINITE_TL:
     !s : bool list -> bool. FINITE (IMAGE TL s) <=> FINITE s
Proof
   RW_TAC std_ss []
   >> reverse EQ_TAC >- PROVE_TAC [IMAGE_FINITE]
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
   >> PROVE_TAC [TL]
QED

Theorem COUNTABLE_EMPTY:
     countable {}
Proof
   PROVE_TAC [FINITE_COUNTABLE, FINITE_EMPTY]
QED

Theorem IMAGE_I:
     IMAGE I = I
Proof
   FUN_EQ_TAC
   >> RW_TAC std_ss [EXTENSION, IN_IMAGE, I_THM]
QED

Theorem INSERT_CASES:
     !P. P {} /\ (!x s. ~(x IN s) ==> P (x INSERT s)) ==> (!s. P s)
Proof
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `s` SET_CASES)
   >> RW_TAC std_ss []
   >> PROVE_TAC []
QED

Theorem BOOL_SET_CASES:
     !P. P {} /\ P {T} /\ P {F} /\ P UNIV ==> (!x. P x)
Proof
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
    >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT]]
QED

Theorem COMPL_INTER:
     !s t. COMPL (s INTER t) = COMPL s UNION COMPL t
Proof
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION]
QED

Theorem COUNTABLE_BIGUNION:
     !c.
       countable c /\ (!s. s IN c ==> countable s) ==> countable (BIGUNION c)
Proof
   PROVE_TAC [bigunion_countable]
QED

Theorem COUNTABLE_BOOL_LIST:
     !s : bool list -> bool. countable s
Proof
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
   >> RW_TAC std_ss [image_countable]
QED

Theorem INTER_BIGUNION:
     !s a. s INTER BIGUNION a = BIGUNION (IMAGE ($INTER s) a)
Proof
   RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION_IMAGE]
   >> RW_TAC std_ss [IN_BIGUNION]
   >> PROVE_TAC []
QED

Theorem FINITE_DISJOINT_ENUM:
     !c.
       FINITE c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))
Proof
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
   >> PROVE_TAC [DISJOINT_EMPTY]
QED

Theorem COUNTABLE_DISJOINT_ENUM:
     !c.
       countable c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))
Proof
   RW_TAC std_ss [COUNTABLE_ALT_BIJ]
   >- (MP_TAC (Q.SPEC `c` FINITE_DISJOINT_ENUM)
       >> RW_TAC std_ss [])
   >> Q.EXISTS_TAC `enumerate c`
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_FUNSET, IN_INSERT,
                     EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, INJ_DEF]
   >> PROVE_TAC []
QED

Theorem COMPL_BIGINTER:
     !s. COMPL (BIGINTER s) = BIGUNION (IMAGE COMPL s)
Proof
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER, IN_BIGUNION_IMAGE]
QED

Theorem IMAGE_K:
     !x s. IMAGE (K x) s = if s = {} then {} else {x}
Proof
   RW_TAC std_ss [EXTENSION, IN_IMAGE, K_THM, NOT_IN_EMPTY, IN_SING]
   >> PROVE_TAC []
QED

Theorem FINITE_BOOL:
     !s : bool -> bool. FINITE s
Proof
   Suff `FINITE (UNIV : bool -> bool)` >- PROVE_TAC [SUBSET_FINITE, SUBSET_UNIV]
   >> Suff `UNIV = {T; F}`
   >- RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]
   >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY]
QED

Theorem COUNTABLE_BOOL:
     !s : bool -> bool. countable s
Proof
   PROVE_TAC [FINITE_COUNTABLE, FINITE_BOOL]
QED

Theorem COUNTABLE_SING:
     !x. countable {x}
Proof
   PROVE_TAC [FINITE_COUNTABLE, FINITE_SING]
QED

Theorem ALWAYS_IN_RANGE:
     !f x. f x IN range f
Proof
   RW_TAC std_ss [range_def, IN_IMAGE, IN_UNIV]
   >> PROVE_TAC []
QED

Theorem RANGE_NONEMPTY:
     !f. ~(range f = {})
Proof
   RW_TAC std_ss [range_def, EXTENSION, NOT_IN_EMPTY, IN_IMAGE, IN_UNIV]
QED

Theorem PREIMAGE_INTER_RANGE:
     !f s. PREIMAGE f (s INTER range f) = PREIMAGE f s
Proof
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER, ALWAYS_IN_RANGE]
QED

Theorem PREIMAGE_INTER_SUPER_RANGE:
     !f s t. range f SUBSET t ==> (PREIMAGE f (s INTER t) = PREIMAGE f s)
Proof
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER, SUBSET_DEF]
   >> PROVE_TAC [ALWAYS_IN_RANGE]
QED

Theorem RANGE_BIND:
     !f g.
       range (FST o BIND f g) SUBSET
       BIGUNION (IMAGE (range o (\x. FST o g x)) (range (FST o f)))
Proof
   RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, range_def, IN_IMAGE, IN_UNIV,
                  o_THM, BIND_DEF, UNCURRY]
   >> PROVE_TAC [FST, SND]
QED

Theorem GEMPTY:
     {s | F} = {}
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
QED

Theorem GUNIV:
     {s | T} = UNIV
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNIV]
QED

Theorem GSPEC_DEST:
     !p. {s | p s} = p
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   >> RW_TAC std_ss [SPECIFICATION]
QED

Theorem GUNION:
     !p q. {s | p s \/ q s} = {s | p s} UNION {s | q s}
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION]
QED

Theorem GDEST:
     !p. {s | s IN p} = p
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
QED

Theorem GBIGUNION_IMAGE:
     !s p n. {s | ?n. p s n} = BIGUNION (IMAGE (\n. {s | p s n}) UNIV)
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV]
QED

Theorem GINTER:
     !p q. {s | p s /\ q s} = {s | p s} INTER {s | q s}
Proof
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
QED

Theorem BIGUNION_IMAGE_INSIDE:
     !f g s.
       BIGUNION (IMAGE f (BIGUNION (IMAGE g s))) =
       BIGUNION (IMAGE (BIGUNION o IMAGE f o g) s)
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_BIGUNION_IMAGE, o_THM]
   >> PROVE_TAC []
QED

Theorem GCOMPL:
     !p. {s | ~p s} = COMPL {s | p s}
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, IN_COMPL]
QED

Theorem IN_I:
     !x. x IN I <=> x
Proof
   RW_TAC std_ss [SPECIFICATION, I_THM]
QED

Theorem COMPL_o:
     !p q. COMPL p o q = COMPL (p o q)
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_COMPL, IN_o]
QED

Theorem FST_o_UNIT:
     !p a. p o FST o UNIT a = if a IN p then UNIV else {}
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [o_THM, UNIT_DEF, IN_o, IN_UNIV, NOT_IN_EMPTY]
QED

Theorem IS_SOME_MMAP:
     !f. {x | IS_SOME x} o FST o MMAP SOME f = UNIV
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [IN_UNIV, IN_o, o_THM, MMAP_DEF, BIND_DEF, UNCURRY,
                     UNIT_DEF, GSPECIFICATION]
QED

Theorem IS_SOME_INTER_MMAP:
     !p f.
       ((p o THE) INTER {x | IS_SOME x}) o FST o MMAP SOME f = p o FST o f
Proof
   SET_EQ_TAC
   >> RW_TAC std_ss [o_THM, MMAP_DEF, BIND_DEF, UNCURRY, UNIT_DEF, IN_INTER,
                     IN_o, GSPECIFICATION]
QED

Theorem SET_PAIR_BOOL:
     !s.
       s =
       (if (T, T) IN s then {(T, T)} else {}) UNION
       (if (T, F) IN s then {(T, F)} else {}) UNION
       (if (F, T) IN s then {(F, T)} else {}) UNION
       (if (F, F) IN s then {(F, F)} else {})
Proof
   STRIP_TAC
   >> SET_EQ_TAC
   >> Cases
   >> Cases_on `q`
   >> Cases_on `r`
   >> RW_TAC std_ss [IN_UNION, IN_SING, NOT_IN_EMPTY]
QED

Theorem FINITE_PAIR_BOOL:
     !s:bool#bool->bool. FINITE s
Proof
   RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [SET_PAIR_BOOL]
   >> RW_TAC std_ss [FINITE_UNION, FINITE_INSERT, FINITE_EMPTY]
QED

val LIST_TO_SET_NIL = prove (
 ``(LIST_TO_SET [] = {})``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, LIST_TO_SET, MEM]);

Theorem LIST_TO_SET_SING:
     !x. LIST_TO_SET [x] = {x}
Proof
   RW_TAC list_ss [EXTENSION, GSPECIFICATION, IN_SING, LIST_TO_SET]
QED

Theorem LIST_TO_SET_THM:
     (LIST_TO_SET [] = {}) /\
     (!h l. LIST_TO_SET (h::l) = h INSERT (LIST_TO_SET l))
Proof
   CONJ_TAC >- SIMP_TAC std_ss [LIST_TO_SET_NIL]
   >> RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT, LIST_TO_SET, MEM]
QED

Theorem FINITE_LIST_TO_SET:
     !l. FINITE (LIST_TO_SET l)
Proof
   Induct
   >> RW_TAC std_ss [FINITE_EMPTY, FINITE_INSERT, LIST_TO_SET_THM]
QED

Theorem IMAGE_LIST_TO_SET:
     !f l. IMAGE f (LIST_TO_SET l) = LIST_TO_SET (MAP f l)
Proof
   RW_TAC std_ss [GSYM LIST_TO_SET_MAP]
QED

Theorem CROSS_LIST_TO_SET:
     !l l'. (LIST_TO_SET l) CROSS (LIST_TO_SET l') =
        LIST_TO_SET (LIST_COMBS l l')
Proof
   RW_TAC std_ss [EXTENSION, IN_CROSS, LIST_TO_SET, MEM_LIST_COMBS]
QED

