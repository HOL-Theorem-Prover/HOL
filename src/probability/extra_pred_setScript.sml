(* interactive mode
loadPath := ["../ho_prover","../subtypes","../rsa"] @ !loadPath;
app load ["bossLib","subtypeTheory","formalizeUseful","extra_boolTheory",
          "boolContext","extra_listTheory","listContext",
          "state_transformerTheory"];
open HolKernel Parse boolLib bossLib arithmeticTheory combinTheory
     pred_setTheory formalizeUseful boolContext listTheory
     res_quanTools res_quanTheory subtypeTheory subtypeTools
     extra_listTheory ho_proverTools listContext extra_numTheory
     pairTheory state_transformerTheory simpLib seqTheory;


loadPath := ["../subtypes"] @ !loadPath;
app load ["bossLib","subtypeTheory","formalizeUseful","extra_boolTheory",
          "extra_listTheory", "res_quanTools",
          "state_transformerTheory", "seqTheory"];


quietdec := true;
*)


open HolKernel Parse boolLib bossLib arithmeticTheory combinTheory
     pred_setTheory formalizeUseful listTheory rich_listTheory
     res_quanTools res_quanTheory subtypeTheory
     extra_listTheory extra_numTheory
     pairTheory realTheory realLib state_transformerTheory simpLib
     seqTheory;



(* interactive mode
quietdec := false;
*)

val _ = new_theory "extra_pred_set";

val EXISTS_DEF = boolTheory.EXISTS_DEF;

infixr 0 ++ << || THENC ORELSEC ORELSER ## |-> ORELSE;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val REVERSE = Tactical.REVERSE;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;


(* val std_pc = precontext_mergel [bool_pc, list_pc];
   val std_c = precontext_compile std_pc;

   val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

   val Strip = S_TAC;
   val Simplify = R_TAC; *)

val Suff = PARSE_TAC SUFF_TAC;
val Know = PARSE_TAC KNOW_TAC;
val bool_ss = boolSimps.bool_ss;
val Cond =
  MATCH_MP_TAC (PROVE [] ``!a b c. a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
  ++ CONJ_TAC;

val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val BIGINTER_def = Define `BIGINTER a = {x | !s. s IN a ==> x IN s}`;

val countable_def = Define
  `countable s = ?f. !x : 'a. x IN s ==> ?n : num. f n = x`;

val enumerate_def = Define `enumerate s = @f : num -> 'a. BIJ f UNIV s`;

val schroeder_close_def = Define
  `schroeder_close f s x = ?n. x IN FUNPOW (IMAGE f) n s`;

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
      ++ RW_TAC std_ss []
      ++ MP_TAC (Q.SPEC `s` CARD_DELETE)
      ++ ASM_REWRITE_TAC []
      ++ DISCH_THEN (MP_TAC o Q.SPEC `CHOICE s`)
      ++ RW_TAC arith_ss [CHOICE_DEF]
      ++ MP_TAC (Q.SPEC `s` CARD_EQ_0)
      ++ RW_TAC arith_ss [])
  end;
      
val _ = save_thm ("list_elts_def", list_elts_def);
val _ = save_thm ("list_elts_ind", list_elts_ind);

val set_def = Define `set p s = s SUBSET p`;

val nonempty_def = Define `nonempty s = ~(s = {})`;

val count_def = Define `count (n:num) m = m < n`;

val PREIMAGE_def = Define `PREIMAGE f s = {x | f x IN s}`;

val range_def = Define `range f = IMAGE f UNIV`;

val prod_sets_def = Define `prod_sets a b = {s CROSS t | s IN a /\ t IN b}`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val IN_o = store_thm
  ("IN_o",
   ``!x f s. x IN (s o f) = f x IN s``,
   RW_TAC std_ss [SPECIFICATION, o_THM]);

val COMPL_EMPTY = store_thm
  ("COMPL_EMPTY",
   ``COMPL {} = UNIV``,
   RW_TAC std_ss [EXTENSION, IN_COMPL, NOT_IN_EMPTY, IN_UNIV]);

val UNION_DEF_ALT = store_thm
  ("UNION_DEF_ALT",
   ``!s t. s UNION t = (\x:'a. s x \/ t x)``,
   REPEAT STRIP_TAC
   ++ Suff `!v:'a. v IN (s UNION t) = v IN (\x. s x \/ t x)`
     >> (PURE_REWRITE_TAC [SPECIFICATION]
         ++ PROVE_TAC [EQ_EXT])
   ++ RW_TAC std_ss [UNION_DEF, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION]);

val INTER_UNION_RDISTRIB = store_thm
  ("INTER_UNION_RDISTRIB",
   ``!(p:'a->bool) q r. (p UNION q) INTER r = p INTER r UNION q INTER r``,
   RW_TAC std_ss [EXTENSION, IN_UNION, IN_INTER]
   ++ PROVE_TAC []);

val INTER_IS_EMPTY = store_thm
  ("INTER_IS_EMPTY",
   ``!(s:'a->bool) t. (s INTER t = {}) = (!x. ~s x \/ ~t x)``,
   RW_TAC std_ss [INTER_DEF, EXTENSION, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION, EMPTY_DEF]);

val GSPEC_DEF_ALT = store_thm
  ("GSPEC_DEF_ALT",
   ``!(f:'a -> 'b # bool). GSPEC f = (\v. ?x. (v, T) = f x)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION]
   ++ RW_TAC std_ss [SPECIFICATION]);   

val UNION_DISJOINT_SPLIT = store_thm
  ("UNION_DISJOINT_SPLIT",
   ``!(s:'a->bool) t u. (s UNION t = s UNION u)
                        /\ (s INTER t = {}) /\ (s INTER u = {})
                        ==> (t = u)``,
   RW_TAC std_ss [UNION_DEF_ALT, EXTENSION, INTER_IS_EMPTY, SPECIFICATION]
   ++ PROVE_TAC []);

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
    ++ PROVE_TAC []);

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
   ++ EQ_TAC <<
   [RW_TAC std_ss []
    ++ POP_ASSUM MP_TAC
    ++ Cases_on `x'`
    ++ RW_TAC std_ss []
    ++ PROVE_TAC [],
    RW_TAC std_ss []
    ++ Q.EXISTS_TAC `(a, b)`
    ++ RW_TAC std_ss []]);

val CONJ_IMAGE2 = store_thm
  ("CONJ_IMAGE2",
   ``!a b s t.
       (b ==> a IN s) /\ (a ==> b IN t) ==>
       ((a /\ b) IN ({F} UNION IMAGE2 $/\ s t))``,
   RW_TAC std_ss [IN_UNION, IN_IMAGE2, IN_INSERT, NOT_IN_EMPTY]
   ++ Suff `a /\ b ==> ?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' = a /\ b)`
   >> (Q.SPEC_TAC (`?a' b'. a' IN s /\ b' IN t /\ (a' /\ b' = a /\ b)`, `q`)
       ++ PROVE_TAC [])
   ++ RW_TAC std_ss []
   ++ PROVE_TAC []);

val INJ_SUBSET = store_thm
  ("INJ_SUBSET",
   ``!f s s' t. INJ f s t /\ s' SUBSET s ==> INJ f s' t``,
   RW_TAC std_ss [INJ_DEF, SUBSET_DEF]);

val CARD_IMAGE = store_thm
  ("CARD_IMAGE",
   ``!f s t. FINITE s /\ INJ f s t ==> (CARD (IMAGE f s) = CARD s)``,
   Suff `!s. FINITE s ==> !f t. INJ f s t ==> (CARD (IMAGE f s) = CARD s)`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [IMAGE_EMPTY, CARD_DEF, IMAGE_INSERT]
   ++ Know `~(f e IN IMAGE f s)`
   >> (!! (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss [IN_INSERT, IN_IMAGE, INJ_DEF]
       ++ PROVE_TAC [])
   ++ MP_TAC (Q.SPEC `s` IMAGE_FINITE)
   ++ RW_TAC std_ss [CARD_INSERT]
   ++ Suff `INJ f s t` >> PROVE_TAC []
   ++ MATCH_MP_TAC INJ_SUBSET
   ++ RW_TAC std_ss [SUBSET_DEF]
   ++ PROVE_TAC [IN_INSERT]);

val CARD_IMAGE2_lem = prove  (``!P. FINITE P ==>		(\P. (!f. (!x y. x IN P /\ y IN P /\ (f x = f y) ==> (x = y)) ==>		 (CARD (IMAGE f P) = CARD P))) P``,   MATCH_MP_TAC FINITE_INDUCT   ++ RW_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, CARD_EMPTY, CARD_INSERT, IMAGE_FINITE, IN_IMAGE]   ++ `~?x. (f e = f x) /\ x IN s` by METIS_TAC [IN_INSERT] ++ RW_TAC arith_ss []   ++ Q.PAT_ASSUM `!f. b ==> (c = d)` MATCH_MP_TAC   ++ METIS_TAC [IN_INSERT]);val CARD_IMAGE2 = store_thm  ("CARD_IMAGE2",   ``!P. FINITE P ==>		(!f. (!x y. x IN P /\ y IN P /\ (f x = f y) ==> (x = y)) ==>		 (CARD (IMAGE f P) = CARD P))``,   METIS_TAC [CARD_IMAGE2_lem]);

val CARD_SUBSET_PROPER = store_thm
  ("CARD_SUBSET_PROPER",
   ``!(s:'a->bool) t.
        FINITE t /\ s SUBSET t ==> ((CARD s = CARD t) = (s = t))``,
   RW_TAC std_ss []
   ++ Cases_on `s = t` >> PROVE_TAC []
   ++ Know `s PSUBSET t` >> PROVE_TAC [PSUBSET_DEF]
   ++ STRIP_TAC
   ++ MP_TAC (Q.SPEC `t` CARD_PSUBSET)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPEC `s`)
   ++ RW_TAC arith_ss []);

val LIST_ELTS = store_thm
  ("LIST_ELTS",
   ``!(s:'a->bool). FINITE s ==> (!v. MEM v (list_elts s) = v IN s)``,
   recInduct list_elts_ind
   ++ RW_TAC std_ss []
   ++ Cases_on `s = {}`
   >> (MP_TAC (Q.SPEC `s` list_elts_def)
       ++ RW_TAC std_ss [FINITE_EMPTY, MEM, NOT_IN_EMPTY])
   ++ Know `FINITE (s DELETE CHOICE s)` >> PROVE_TAC [FINITE_DELETE]
   ++ STRIP_TAC ++ FULL_SIMP_TAC std_ss []
   ++ ONCE_REWRITE_TAC [list_elts_def]
   ++ RW_TAC std_ss []
   ++ Cases_on `v = CHOICE s`
   >> (RW_TAC std_ss [CHOICE_DEF]
       ++ RW_TAC std_ss [SPECIFICATION, MEM])
   ++ Q.PAT_ASSUM `!v. P v` (MP_TAC o Q.SPEC `v`)
   ++ MP_TAC (Q.SPECL [`s`, `v`, `CHOICE s`] IN_DELETE)
   ++ ASM_REWRITE_TAC []
   ++ RW_TAC std_ss [MEM, SPECIFICATION]);

val FINITE_UNIONL = store_thm
  ("FINITE_UNIONL",
   ``!(ss:('a->bool) list). FINITE (UNIONL ss) = EVERY FINITE ss``,
   Induct >> RW_TAC list_ss [UNIONL_def, FINITE_EMPTY]
   ++ RW_TAC list_ss [UNIONL_def, FINITE_UNION]);

val CARD_UNIONL = store_thm
  ("CARD_UNIONL",
   ``!(ss:('a->bool) list). EVERY FINITE ss /\ DISJOINTL ss
          ==> (CARD (UNIONL ss) = sum (MAP CARD ss))``,
   Induct >> RW_TAC list_ss [DISJOINTL_def, UNIONL_def, sum_def, CARD_DEF]
   ++ RW_TAC list_ss [DISJOINTL_def, UNIONL_def, sum_def]
   ++ Know `FINITE (UNIONL ss)` >> RW_TAC std_ss [FINITE_UNIONL]
   ++ MP_TAC (Q.SPECL [`h`] CARD_UNION)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPEC `UNIONL ss`)
   ++ Q.PAT_ASSUM `DISJOINT a b` MP_TAC
   ++ RW_TAC arith_ss [DISJOINT_DEF, CARD_DEF]);

val IN_UNIONL = store_thm
  ("IN_UNIONL",
   ``!l (v:'a). v IN UNIONL l = (?s. MEM s l /\ v IN s)``,
   Induct >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
   ++ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
   ++ PROVE_TAC []);

val DISJOINT_UNION1 = DISJOINT_UNION;
val DISJOINT_UNION2 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNION1;

val DISJOINT_UNIONL2 = store_thm
  ("DISJOINT_UNIONL2",
   ``!l (x:'a->bool). DISJOINT x (UNIONL l) = (!y. MEM y l ==> DISJOINT x y)``,
   Induct >> RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_DEF, INTER_EMPTY]
   ++ RW_TAC std_ss [UNIONL_def, MEM, DISJOINT_UNION2]
   ++ PROVE_TAC []);
val DISJOINT_UNIONL1 = ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_UNIONL2;

val DISJOINTL_KILL_DUPS = store_thm
  ("DISJOINTL_KILL_DUPS",
   ``!(l:('a->bool) list). DISJOINTL (kill_dups l)
         = (!x y. MEM x l /\ MEM y l ==> (x = y) \/ DISJOINT x y)``,
   Induct >> RW_TAC list_ss [DISJOINTL_def, MEM, kill_dups_def, FOLDR]
   ++ REWRITE_TAC [kill_dups_def, FOLDR]
   ++ (RW_TAC std_ss [GSYM kill_dups_def, MEM, DISJOINTL_def, MEM_KILL_DUPS,
                      DISJOINT_UNIONL2]
       ++ EQ_TAC
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [DISJOINT_SYM]));

val NUM_TO_FINITE = store_thm
  ("NUM_TO_FINITE",
   ``!s (f:num->'a).
       FINITE s /\ (!n. f n IN s) ==> ?i j. i < j /\ (f i = f j)``,
   Suff `!s. FINITE s ==> !(f:num->'a). (!n. f n IN s)
	       ==> ?i j. i < j /\ (f i = f j)`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ REWRITE_TAC [NOT_IN_EMPTY]
   ++ RW_TAC std_ss [IN_INSERT]
   ++ Cases_on `?n. !m. m >= n ==> ~(f m = e)` <<
   [POP_ASSUM MP_TAC
    ++ STRIP_TAC
    ++ Q.PAT_ASSUM `!f. (!n. P f n) ==> Q f` (MP_TAC o Q.SPEC `(\x. f (x + n))`)
    ++ Know `!n'. f (n + n') IN s`
    >> (STRIP_TAC
	++ Suff `n + n' >= n` >> PROVE_TAC []
	++ DECIDE_TAC)
    ++ RW_TAC arith_ss []
    ++ Suff `i + n < j + n` >> PROVE_TAC []
    ++ DECIDE_TAC,
    POP_ASSUM MP_TAC
    ++ RW_TAC std_ss []
    ++ POP_ASSUM (fn th => MP_TAC th ++ MP_TAC (Q.SPEC `0` th))
    ++ RW_TAC std_ss []
    ++ POP_ASSUM (MP_TAC o Q.SPEC `SUC m`)
    ++ RW_TAC arith_ss []
    ++ Suff `m < m'` >> PROVE_TAC []
    ++ DECIDE_TAC]);

val SURJ_ALT = store_thm
  ("SURJ_ALT",
   ``!f s t. SURJ f s t = f IN (s -> t) /\ (!y :: t. ?x :: s. y = f x)``,
   RW_TAC std_ss [SURJ_DEF]
   ++ RESQ_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_DFUNSET]
   ++ PROVE_TAC []);

val BIJ_ALT = store_thm
  ("BIJ_ALT",
   ``!f s t. BIJ f s t = f IN (s -> t) /\ (!y :: t. ?!x :: s. y = f x)``,
   RW_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, RES_EXISTS_UNIQUE_ALT]
   ++ RESQ_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_DFUNSET, GSYM CONJ_ASSOC]
   ++ Know `!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)` >> PROVE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ REPEAT (STRIP_TAC ORELSE EQ_TAC) <<
   [PROVE_TAC [],
    Q.PAT_ASSUM `!x. P x`
    (fn th =>
     MP_TAC (Q.SPEC `(f:'a->'b) x` th)
     ++ MP_TAC (Q.SPEC `(f:'a->'b) y` th))
    ++ Cond >> PROVE_TAC []
    ++ STRIP_TAC
    ++ Cond >> PROVE_TAC []
    ++ STRIP_TAC
    ++ PROVE_TAC [],
    PROVE_TAC [],
    PROVE_TAC []]);

val DELETE_THEN_INSERT = store_thm
  ("DELETE_THEN_INSERT",
   ``!s. !x :: s. x INSERT (s DELETE x) = s``,
   RESQ_TAC
   ++ RW_TAC std_ss [INSERT_DELETE]);

val BIJ_INSERT = store_thm
  ("BIJ_INSERT",
   ``!f e s t.
       ~(e IN s) /\ BIJ f (e INSERT s) t ==>
       ?u. (f e INSERT u = t) /\ ~(f e IN u) /\ BIJ f s u``,
   RW_TAC std_ss [BIJ_ALT]
   ++ Q.EXISTS_TAC `t DELETE f e`
   ++ FULL_SIMP_TAC std_ss [IN_FUNSET, DELETE_THEN_INSERT, ELT_IN_DELETE, IN_INSERT,
              DISJ_IMP_THM]
   ++ RESQ_TAC
   ++ SIMP_TAC std_ss [IN_DELETE]
   ++ REPEAT STRIP_TAC
   ++ METIS_TAC [IN_INSERT]);

val FINITE_BIJ = store_thm
  ("FINITE_BIJ",
   ``!f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)``,
   Suff `!s. FINITE s ==> !f t. BIJ f s t ==> FINITE t /\ (CARD s = CARD t)`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC >>
	(RW_TAC std_ss [BIJ_ALT, FINITE_EMPTY, CARD_EMPTY, IN_FUNSET, NOT_IN_EMPTY]
	 ++ RESQ_TAC
	 ++ FULL_SIMP_TAC std_ss [NOT_IN_EMPTY]
	 ++ `t = {}`
		by RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY]
	 ++ RW_TAC std_ss [FINITE_EMPTY, CARD_EMPTY])
   ++ NTAC 7 STRIP_TAC
   ++ MP_TAC (Q.SPECL [`f`, `e`, `s`, `t`] BIJ_INSERT)
   ++ ASM_REWRITE_TAC []
   ++ STRIP_TAC
   ++ Know `FINITE u` >> PROVE_TAC []
   ++ STRIP_TAC
   ++ CONJ_TAC >> PROVE_TAC [FINITE_INSERT]
   ++ Q.PAT_ASSUM `f e INSERT u = t` (fn th => RW_TAC std_ss [SYM th])
   ++ RW_TAC std_ss [CARD_INSERT]
   ++ PROVE_TAC []);

val FINITE_BIJ_CARD = store_thm
  ("FINITE_BIJ_CARD",
   ``!f s t. FINITE s /\ BIJ f s t ==> (CARD s = CARD t)``,
   PROVE_TAC [FINITE_BIJ]);

val FINITE_MAXIMAL = store_thm
  ("FINITE_MAXIMAL",
   ``!f s. FINITE s /\ ~(s = {}) ==> ?x :: s. !y :: s. (f y:num) <= f x``,
   STRIP_TAC ++ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
   ++ RESQ_TAC
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss []
   ++ Cases_on `s = {}`
   >> FULL_SIMP_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
   ++ RES_TAC
   ++ S_TAC
   ++ Know `(f:'a->num) e <= f x \/ f x <= f e` >> DECIDE_TAC
   ++ S_TAC <<
   [Q.EXISTS_TAC `x`
    ++ RW_TAC std_ss [IN_INSERT]
    >> ASM_REWRITE_TAC []
    ++ Q.PAT_ASSUM `!y. y IN s ==> f y <= f x` MATCH_MP_TAC
    ++ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `e`
    ++ RW_TAC arith_ss [IN_INSERT, LESS_EQ_REFL]
    >> DECIDE_TAC
    ++ Q.PAT_ASSUM `!y. y IN s ==> f y <= f x` (MP_TAC o UNDISCH o Q.SPEC `y`)
    ++ POP_ASSUM (K ALL_TAC)
    ++ POP_ASSUM MP_TAC
    ++ DECIDE_TAC]);

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
   ++ PROVE_TAC []);

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
   ++ PROVE_TAC []);

val SET_UNIV = store_thm
  ("SET_UNIV",
   ``set UNIV = UNIV``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [IN_SET, IN_UNIV, SUBSET_UNIV]);

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
   ++ SET_EQ_TAC
   ++ RW_TAC std_ss [NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val NONEMPTY_SUBTYPE_REWRITE = store_thm
  ("NONEMPTY_SUBTYPE_REWRITE",
   ``!s. s IN nonempty ==> ~(s = {}) /\ ~({} = s)``,
   RW_TAC std_ss [SPECIFICATION, IN_NONEMPTY]
   ++ PROVE_TAC []);

val CARD_SUBTYPE = store_thm
  ("CARD_SUBTYPE",
   ``CARD IN ((FINITE INTER nonempty) -> gtnum 0)``,
   RW_TAC std_ss [IN_FUNSET, IN_NONEMPTY, IN_GTNUM, IN_INTER, IN_FINITE]
   ++ S_TAC
   ++ Suff `~(CARD x = 0)` >> DECIDE_TAC
   ++ PROVE_TAC [CARD_EQ_0]);

val INTER_DEF_ALT = store_thm
  ("INTER_DEF_ALT",
   ``!s t. s INTER t = (\x. s x /\ t x)``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [IN_INTER, SPECIFICATION]);

val FINITE_INTER_DISJ = store_thm
  ("FINITE_INTER_DISJ",
   ``!s t. FINITE s \/ FINITE t ==> FINITE (s INTER t)``,
   PROVE_TAC [FINITE_INTER, INTER_FINITE]);

val FINITE_SUBSET_CARD_EQ = store_thm
  ("FINITE_SUBSET_CARD_EQ",
   ``!s t. FINITE t /\ s SUBSET t /\ (CARD s = CARD t) ==> (s = t)``,
   S_TAC
   ++ Suff `s SUBSET t /\ t SUBSET s`
   >> (KILL_TAC
       ++ SET_EQ_TAC
       ++ RW_TAC std_ss [SUBSET_DEF]
       ++ PROVE_TAC [])
   ++ Know `FINITE s` >> PROVE_TAC [SUBSET_FINITE]
   ++ STRIP_TAC
   ++ Know `FINITE t /\ s SUBSET t /\ (CARD s = CARD t)` >> PROVE_TAC []
   ++ Q.SPEC_TAC (`t`, `t`)
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ KILL_TAC
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC >> (RW_TAC std_ss [CARD_EMPTY, SUBSET_EMPTY] ++ PROVE_TAC [CARD_EQ_0])
   ++ RW_TAC std_ss []
   ++ Know `?t'. ~(e IN t') /\ (t = e INSERT t')`
   >> (Q.EXISTS_TAC `t DELETE e`
       ++ RW_TAC std_ss [IN_DELETE]
       ++ MATCH_MP_TAC (GSYM INSERT_DELETE)
       ++ FULL_SIMP_TAC std_ss [INSERT_SUBSET])
   ++ S_TAC
   ++ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th, FINITE_INSERT, CARD_INSERT])
   ++ RW_TAC std_ss [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ Q.PAT_ASSUM `x SUBSET y` MP_TAC
   ++ Q.PAT_ASSUM `CARD (e INSERT s) = CARD (e INSERT t')` MP_TAC
   ++ ASM_SIMP_TAC std_ss [INSERT_SUBSET, SUBSET_INSERT, IN_INSERT, CARD_INSERT]);

val SUBSET_INTER1 = store_thm
  ("SUBSET_INTER1",
   ``!s t. s SUBSET t ==> (s INTER t = s)``,
   SET_EQ_TAC
   ++ ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val SUBSET_INTER2 = store_thm
  ("SUBSET_INTER2",
   ``!s t. s SUBSET t ==> (t INTER s = s)``,
   SET_EQ_TAC
   ++ SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val FINITE_LESS = store_thm
  ("FINITE_LESS",
   ``!n. FINITE (\x : num. x < n)``,
   Induct
   >> (Suff `(\x : num. x < 0) = {}`
       >> SIMP_TAC std_ss [FINITE_EMPTY]
       ++ SET_EQ_TAC
       ++ SIMP_TAC std_ss [SPECIFICATION, NOT_IN_EMPTY])
   ++ Suff `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >> ASM_SIMP_TAC std_ss [FINITE_INSERT]
   ++ SET_EQ_TAC
   ++ SIMP_TAC std_ss [IN_INSERT]
   ++ SIMP_TAC std_ss [SPECIFICATION]
   ++ DECIDE_TAC);

val FINITE_LESS1 = store_thm
  ("FINITE_LESS1",
   ``!n s. FINITE (\x : num. x < n /\ s x)``,
   Strip
   ++ SIMP_TAC std_ss [GSYM INTER_DEF_ALT]
   ++ MATCH_MP_TAC FINITE_INTER_DISJ
   ++ SIMP_TAC std_ss [FINITE_LESS]);

val FINITE_LESS2 = store_thm
  ("FINITE_LESS2",
   ``!n s. FINITE (\x : num. s x /\ x < n)``,
   Strip
   ++ SIMP_TAC std_ss [GSYM INTER_DEF_ALT]
   ++ MATCH_MP_TAC FINITE_INTER_DISJ
   ++ SIMP_TAC std_ss [FINITE_LESS]);

val CARD_LESS = store_thm
  ("CARD_LESS",
   ``!n. CARD (\x. x < n) = n``,
   Induct
   >> (Suff `(\x : num. x < 0) = {}`
       >> SIMP_TAC std_ss [CARD_EMPTY]
       ++ SET_EQ_TAC
       ++ SIMP_TAC std_ss [SPECIFICATION, NOT_IN_EMPTY])
   ++ ASSUME_TAC (Q.SPEC `n` FINITE_LESS)
   ++ Know `(\x. x < SUC n) = n INSERT (\x. x < n)`
   >> (SET_EQ_TAC
       ++ SIMP_TAC std_ss [IN_INSERT, SPECIFICATION]
       ++ DECIDE_TAC)
   ++ ASM_SIMP_TAC std_ss [CARD_INSERT]
   ++ DISCH_THEN K_TAC
   ++ Suff `~(n IN (\x. x < n))` >> SIMP_TAC std_ss []
   ++ SIMP_TAC std_ss [SPECIFICATION]);

val FINITE_COUNTABLE = store_thm
  ("FINITE_COUNTABLE",
   ``!s. FINITE s ==> countable s``,
   REWRITE_TAC [countable_def]
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [NOT_IN_EMPTY]
   ++ Q.EXISTS_TAC `\n. if n = 0 then e else f (n - 1)`
   ++ RW_TAC std_ss [IN_INSERT] >> PROVE_TAC []
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `SUC n`
   ++ RW_TAC std_ss [SUC_SUB1]);

val BIJ_NUM_COUNTABLE = store_thm
  ("BIJ_NUM_COUNTABLE",
   ``!s. (?f : num -> 'a. BIJ f UNIV s) ==> countable s``,
   RW_TAC std_ss [countable_def, BIJ_DEF, SURJ_DEF, IN_UNIV]
   ++ PROVE_TAC []);

val SCHROEDER_CLOSE = store_thm
  ("SCHROEDER_CLOSE",
   ``!f s. x IN schroeder_close f s = ?n. x IN FUNPOW (IMAGE f) n s``,
   RW_TAC std_ss [SPECIFICATION, schroeder_close_def]);

val SCHROEDER_CLOSED = store_thm
  ("SCHROEDER_CLOSED",
   ``!f s. IMAGE f (schroeder_close f s) SUBSET schroeder_close f s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, IN_IMAGE, SUBSET_DEF]
   ++ Q.EXISTS_TAC `SUC n`
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ PROVE_TAC []);

val SCHROEDER_CLOSE_SUBSET = store_thm
  ("SCHROEDER_CLOSE_SUBSET",
   ``!f s. s SUBSET schroeder_close f s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, IN_IMAGE, SUBSET_DEF]
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC std_ss [FUNPOW]);

val SCHROEDER_CLOSE_SET = store_thm
  ("SCHROEDER_CLOSE_SET",
   ``!f s t. f IN (s -> s) /\ t SUBSET s ==> schroeder_close f t SUBSET s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, SUBSET_DEF, IN_FUNSET]
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`x`, `x`)
   ++ Induct_on `n` >> RW_TAC std_ss [FUNPOW]
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ PROVE_TAC []);

val SCHROEDER_BERNSTEIN_AUTO = store_thm
  ("SCHROEDER_BERNSTEIN_AUTO",
   ``!s t. t SUBSET s /\ (?f. INJ f s t) ==> ?g. BIJ g s t``,
   RW_TAC std_ss [INJ_DEF]
   ++ Q.EXISTS_TAC `\x. if x IN schroeder_close f (s DIFF t) then f x else x`
   ++ Know `s DIFF schroeder_close f (s DIFF t) SUBSET t`
   >> (RW_TAC std_ss [SUBSET_DEF, IN_DIFF]
       ++ Suff `~(x IN s DIFF t)` >> RW_TAC std_ss [IN_DIFF]
       ++ PROVE_TAC [SCHROEDER_CLOSE_SUBSET, SUBSET_DEF])
   ++ Know `schroeder_close f (s DIFF t) SUBSET s`
   >> (MATCH_MP_TAC SCHROEDER_CLOSE_SET
       ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_FUNSET]
       ++ PROVE_TAC [SUBSET_DEF])
   ++ Q.PAT_ASSUM `t SUBSET s` MP_TAC
   ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF]
   ++ RW_TAC std_ss [BIJ_DEF]
   >> (BasicProvers.NORM_TAC std_ss [INJ_DEF] <<
       [PROVE_TAC [SCHROEDER_CLOSED, SUBSET_DEF, IN_IMAGE],
        PROVE_TAC [SCHROEDER_CLOSED, SUBSET_DEF, IN_IMAGE],
        PROVE_TAC []])
   ++ RW_TAC std_ss [SURJ_DEF]
   ++ REVERSE (Cases_on `x IN schroeder_close f (s DIFF t)`) >> PROVE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [SCHROEDER_CLOSE]
   ++ Cases_on `n` >> (POP_ASSUM MP_TAC ++ RW_TAC std_ss [FUNPOW, IN_DIFF])
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ Q.EXISTS_TAC `x'`
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`n'`, `n`)
   ++ CONV_TAC FORALL_IMP_CONV
   ++ REWRITE_TAC [GSYM SCHROEDER_CLOSE]
   ++ RW_TAC std_ss []);

val INJ_IMAGE_BIJ = store_thm
  ("INJ_IMAGE_BIJ",
   ``!s f. (?t. INJ f s t) ==> BIJ f s (IMAGE f s)``,
   RW_TAC std_ss [INJ_DEF, BIJ_DEF, SURJ_DEF, IN_IMAGE]
   ++ PROVE_TAC []);

val BIJ_SYM_IMP = store_thm
  ("BIJ_SYM_IMP",
   ``!s t. (?f. BIJ f s t) ==> (?g. BIJ g t s)``,
   RW_TAC std_ss [BIJ_DEF, SURJ_DEF, INJ_DEF]
   ++ Suff `?(g : 'b -> 'a). !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >> (Strip
       ++ Q.EXISTS_TAC `g`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [boolTheory.EXISTS_DEF])
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `\x. @y. y IN s /\ (f y = x)`
   ++ RW_TAC std_ss []);

val BIJ_SYM = store_thm
  ("BIJ_SYM",
   ``!s t. (?f. BIJ f s t) = (?g. BIJ g t s)``,
   PROVE_TAC [BIJ_SYM_IMP]);

val BIJ_TRANS = store_thm
  ("BIJ_TRANS",
   ``!s t u.
       (?f. BIJ f s t) /\ (?g. BIJ g t u) ==> (?h : 'a -> 'b. BIJ h s u)``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `g o f`
   ++ PROVE_TAC [BIJ_COMPOSE]);

val SCHROEDER_BERNSTEIN = store_thm
  ("SCHROEDER_BERNSTEIN",
   ``!s t. (?f. INJ f s t) /\ (?g. INJ g t s) ==> (?h. BIJ h s t)``,
   Strip
   ++ MATCH_MP_TAC (INST_TYPE [``:'c`` |-> ``:'a``] BIJ_TRANS)
   ++ Q.EXISTS_TAC `IMAGE g t`
   ++ CONJ_TAC <<
   [MATCH_MP_TAC SCHROEDER_BERNSTEIN_AUTO
    ++ CONJ_TAC
    >> (POP_ASSUM MP_TAC
        ++ RW_TAC std_ss [INJ_DEF, SUBSET_DEF, IN_IMAGE]
        ++ PROVE_TAC [])
    ++ Q.EXISTS_TAC `g o f`
    ++ !! (POP_ASSUM MP_TAC)
    ++ RW_TAC std_ss [INJ_DEF, SUBSET_DEF, IN_IMAGE, o_DEF]
    ++ PROVE_TAC [],
    MATCH_MP_TAC BIJ_SYM_IMP
    ++ Q.EXISTS_TAC `g`
    ++ PROVE_TAC [INJ_IMAGE_BIJ]]);

val SURJ_IMP_INJ = store_thm
  ("SURJ_IMP_INJ",
   ``!s t. (?f. SURJ f s t) ==> (?g. INJ g t s)``,
   RW_TAC std_ss [SURJ_DEF, INJ_DEF]
   ++ Suff `?g. !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >> PROVE_TAC []
   ++ Q.EXISTS_TAC `\y. @x. x IN s /\ (f x = y)`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val BIJ_INJ_SURJ = store_thm
  ("BIJ_INJ_SURJ",
   ``!s t. (?f. INJ f s t) /\ (?g. SURJ g s t) ==> (?h. BIJ h s t)``,
   Strip
   ++ MATCH_MP_TAC SCHROEDER_BERNSTEIN
   ++ CONJ_TAC >> PROVE_TAC []
   ++ PROVE_TAC [SURJ_IMP_INJ]);

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
   Induct >> RW_TAC std_ss [FUNPOW, SUBSET_DEF]
   ++ RW_TAC std_ss [FUNPOW_SUC]
   ++ PROVE_TAC [SUBSET_TRANS, REST_SUBSET]);

val EXPLICIT_ENUMERATE_NOT_EMPTY = store_thm
  ("EXPLICIT_ENUMERATE_NOT_EMPTY",
   ``!n s. INFINITE s ==> ~(FUNPOW REST n s = {})``,
   REWRITE_TAC [INFINITE_DEF]
   ++ Induct >> (RW_TAC std_ss [FUNPOW] ++ PROVE_TAC [FINITE_EMPTY])
   ++ RW_TAC std_ss [FUNPOW]
   ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `REST s`)
   ++ PROVE_TAC [FINITE_REST]);

val INFINITE_EXPLICIT_ENUMERATE = store_thm
  ("INFINITE_EXPLICIT_ENUMERATE",
   ``!s. INFINITE s ==> INJ (\n : num. CHOICE (FUNPOW REST n s)) UNIV s``,
   RW_TAC std_ss [INJ_DEF, IN_UNIV]
   >> (Suff `CHOICE (FUNPOW REST n s) IN FUNPOW REST n s`
       >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
       ++ RW_TAC std_ss [GSYM CHOICE_DEF, EXPLICIT_ENUMERATE_NOT_EMPTY])
   ++ !! (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ Q.SPEC_TAC (`n'`, `y`)
   ++ Q.SPEC_TAC (`n`, `x`)
   ++ (Induct ++ Cases) <<
   [PROVE_TAC [],
    !! STRIP_TAC
    ++ Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC n) s)`
    >> (RW_TAC std_ss []
        ++ MATCH_MP_TAC CHOICE_DEF
        ++ PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    ++ POP_ASSUM K_TAC
    ++ RW_TAC std_ss [FUNPOW]
    ++ Suff `~(CHOICE s IN REST s)`
    >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    ++ PROVE_TAC [CHOICE_NOT_IN_REST],
    !! STRIP_TAC
    ++ POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
    ++ Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC x) s)`
    >> (RW_TAC std_ss []
        ++ MATCH_MP_TAC CHOICE_DEF
        ++ PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    ++ POP_ASSUM K_TAC
    ++ RW_TAC std_ss [FUNPOW]
    ++ Suff `~(CHOICE s IN REST s)`
    >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    ++ PROVE_TAC [CHOICE_NOT_IN_REST],
    RW_TAC std_ss [FUNPOW]
    ++ Q.PAT_ASSUM `!y. P y` (MP_TAC o Q.SPECL [`n`, `REST s`])
    ++ PROVE_TAC [INFINITE_DEF, FINITE_REST]]);

val COUNTABLE_ALT = store_thm
  ("COUNTABLE_ALT",
   ``!s. countable s = FINITE s \/ BIJ (enumerate s) UNIV s``,
   Strip
   ++ REVERSE EQ_TAC >> PROVE_TAC [FINITE_COUNTABLE, BIJ_NUM_COUNTABLE]
   ++ RW_TAC std_ss [countable_def]
   ++ Cases_on `FINITE s` >> PROVE_TAC []
   ++ RW_TAC std_ss [GSYM ENUMERATE]
   ++ MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Know `~(s = {})` >> PROVE_TAC [FINITE_EMPTY]
       ++ RW_TAC std_ss [GSYM MEMBER_NOT_EMPTY]
       ++ Q.EXISTS_TAC `\n. if f n IN s then f n else x`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV]
       ++ PROVE_TAC [])
   ++ MP_TAC (Q.SPEC `s` INFINITE_EXPLICIT_ENUMERATE)
   ++ RW_TAC std_ss [INFINITE_DEF]
   ++ PROVE_TAC []);

val DIFF_ALT = store_thm
  ("DIFF_ALT",
   ``!s t. s DIFF t = s INTER (COMPL t)``,
   RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER, IN_COMPL]);

val IN_BIGINTER = store_thm
  ("IN_BIGINTER",
   ``!x. x IN BIGINTER a = !s. s IN a ==> x IN s``,
   RW_TAC std_ss [BIGINTER_def, GSPECIFICATION]);

val DIFF_SUBSET = store_thm
  ("DIFF_SUBSET",
   ``!a b. a DIFF b SUBSET a``,
   RW_TAC std_ss [SUBSET_DEF, EXTENSION, IN_DIFF]);

val IN_COUNT = store_thm
  ("IN_COUNT",
   ``!m n. m IN count n = m < n``,
   RW_TAC std_ss [SPECIFICATION, count_def]);

val COUNT_ZERO = store_thm
  ("COUNT_ZERO",
   ``count 0 = {}``,
   RW_TAC std_ss [EXTENSION, IN_COUNT, NOT_IN_EMPTY]
   ++ DECIDE_TAC);

val COUNT_SUC = store_thm
  ("COUNT_SUC",
   ``!n. count (SUC n) = n INSERT count n``,
   RW_TAC std_ss [EXTENSION, IN_INSERT, IN_COUNT]
   ++ DECIDE_TAC);

val FINITE_COUNT = store_thm
  ("FINITE_COUNT",
   ``!n. FINITE (count n)``,
   Induct >> RW_TAC std_ss [COUNT_ZERO, FINITE_EMPTY]
   ++ RW_TAC std_ss [COUNT_SUC, FINITE_INSERT]);

val NUM_2D_BIJ = store_thm
  ("NUM_2D_BIJ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `FST`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       ++ Q.EXISTS_TAC `(x, 0)`
       ++ RW_TAC std_ss [FST])
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

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
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`t`, `t`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [EMPTY_SUBSET, NOT_IN_EMPTY, INSERT_SUBSET, IN_INSERT]
   ++ Know `?!k. f k = e`
   >> (Q.PAT_ASSUM `BIJ a b c` MP_TAC
       ++ RW_TAC std_ss [BIJ_ALT, RES_EXISTS_UNIQUE_UNIV, RES_FORALL]
       ++ PROVE_TAC [])
   ++ CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   ++ RW_TAC std_ss []
   ++ RES_TAC
   ++ Q.EXISTS_TAC `MAX N (SUC k)`
   ++ RW_TAC std_ss [MAX_LE_X]
   ++ STRIP_TAC
   ++ Know `n = k` >> PROVE_TAC []
   ++ DECIDE_TAC);

val NUM_2D_BIJ_SMALL_SQUARE = store_thm
  ("NUM_2D_BIJ_SMALL_SQUARE",
   ``!(f : num -> num # num) k.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?N. count k CROSS count k SUBSET IMAGE f (count N)``,
   Strip
   ++ (MP_TAC o
       Q.SPECL [`f`, `UNIV CROSS UNIV`, `count k CROSS count k`] o
       INST_TYPE [``:'a`` |-> ``:num # num``]) BIJ_FINITE_SUBSET
   ++ RW_TAC std_ss [CROSS_SUBSET, SUBSET_UNIV, FINITE_CROSS, FINITE_COUNT]
   ++ Q.EXISTS_TAC `N`
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ Q.PAT_ASSUM `BIJ a b c` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `y`
   ++ RW_TAC std_ss []
   ++ Suff `~(N <= y)` >> DECIDE_TAC
   ++ PROVE_TAC []);

val NUM_2D_BIJ_BIG_SQUARE = store_thm
  ("NUM_2D_BIJ_BIG_SQUARE",
   ``!(f : num -> num # num) N.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?k. IMAGE f (count N) SUBSET count k CROSS count k``,
   RW_TAC std_ss [IN_CROSS, IN_COUNT, SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ Induct_on `N` >> RW_TAC arith_ss []
   ++ Strip
   ++ Cases_on `f N`
   ++ REWRITE_TAC [prim_recTheory.LESS_THM]
   ++ Q.EXISTS_TAC `SUC (MAX k (MAX q r))`
   ++ Know `!a b. a < SUC b = a <= b`
   >> (KILL_TAC
       ++ DECIDE_TAC)
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ]);

val BIGUNION_EQ_EMPTY = store_thm
  ("BIGUNION_EQ_EMPTY",
   ``!a. (BIGUNION a = {}) = (!s. s IN a ==> (s = {}))``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val IN_BIGUNION_IMAGE = store_thm
  ("IN_BIGUNION_IMAGE",
   ``!f s y. y IN BIGUNION (IMAGE f s) = ?x. x IN s /\ y IN f x``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE]
   ++ PROVE_TAC []);

val FINITE_SUBSET_COUNT = store_thm
  ("FINITE_SUBSET_COUNT",
   ``!s. FINITE s = ?n. s SUBSET count n``,
   STRIP_TAC
   ++ REVERSE EQ_TAC >> PROVE_TAC [FINITE_COUNT, SUBSET_FINITE]
   ++ REWRITE_TAC [FINITE_DEF]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `\s. ?N. !n. n IN s ==> n <= N`)
   ++ RW_TAC std_ss [SUBSET_DEF, IN_COUNT]
   ++ Suff `?N. !n. n IN s ==> n <= N`
   >> (RW_TAC std_ss []
       ++ Q.EXISTS_TAC `SUC N`
       ++ Know `!x y. x < SUC y = x <= y` >> DECIDE_TAC
       ++ RW_TAC std_ss [])
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
   ++ Q.EXISTS_TAC `MAX N e`
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss [X_LE_MAX, LESS_EQ_REFL]);

val INFINITE_DIFF_FINITE_EQ = store_thm
  ("INFINITE_DIFF_FINITE_EQ",
   ``!s t. FINITE t ==> (INFINITE (s DIFF t) = INFINITE s)``,
   RW_TAC std_ss [INFINITE_DEF]
   ++ REVERSE EQ_TAC >> PROVE_TAC [SUBSET_FINITE, DIFF_SUBSET]
   ++ Suff `s SUBSET (t UNION (s DIFF t))`
   >> PROVE_TAC [FINITE_UNION, SUBSET_FINITE]
   ++ RW_TAC std_ss [SUBSET_DEF, IN_UNION, IN_DIFF]);

val INFINITE_DELETE = store_thm
  ("INFINITE_DELETE",
   ``!x s. INFINITE (s DELETE x) = INFINITE s``,
   RW_TAC std_ss [DELETE_DEF]
   ++ PROVE_TAC [INFINITE_DIFF_FINITE_EQ, FINITE_SING, SING]);

val NOT_FINITE_NUM = store_thm
  ("NOT_FINITE_NUM",
   ``~FINITE (UNIV : num -> bool)``,
   RW_TAC std_ss [FINITE_SUBSET_COUNT, SUBSET_DEF, IN_UNIV, IN_COUNT]
   ++ Q.EXISTS_TAC `n`
   ++ RW_TAC arith_ss []);

val INFINITE_NUM = store_thm
  ("INFINITE_NUM",
   ``INFINITE (UNIV : num -> bool)``,
   RW_TAC std_ss [INFINITE_DEF, NOT_FINITE_NUM]);

val FINITE_TL = store_thm
  ("FINITE_TL",
   ``!s : bool list -> bool. FINITE (IMAGE TL s) = FINITE s``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> PROVE_TAC [IMAGE_FINITE]
   ++ RW_TAC std_ss []
   ++ Know `FINITE (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s))`
   >> PROVE_TAC [IMAGE_FINITE]
   ++ STRIP_TAC
   ++ Know `FINITE (BIGUNION (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s)))`
   >> (MATCH_MP_TAC FINITE_BIGUNION
       ++ RW_TAC std_ss [IN_IMAGE]
       ++ RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY])
   ++ Suff `s SUBSET BIGUNION (IMAGE (\l. {T::l; F::l; []}) (IMAGE TL s))`
   >> PROVE_TAC [SUBSET_FINITE]
   ++ KILL_TAC
   ++ RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_IMAGE, IN_INSERT,
                     NOT_IN_EMPTY]
   ++ Cases_on `x`
   >> (RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ Cases_on `h`
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [TL]);

val FINITE_INJ = store_thm
  ("FINITE_INJ",
   ``!f s t. INJ f s t /\ FINITE t ==> FINITE s``,
   STRIP_TAC
   ++ Suff `!t. FINITE t ==> !s. INJ f s t ==> FINITE s`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [INJ_EMPTY, FINITE_EMPTY]
   ++ REVERSE (Cases_on `?x. x IN s /\ (f x = e)`)
   >> (Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
       ++ Q.PAT_ASSUM `INJ f p q` MP_TAC
       ++ RW_TAC std_ss [INJ_DEF, IN_INSERT]
       ++ PROVE_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ STRIP_TAC
   ++ Suff `FINITE (s DELETE x)` >> PROVE_TAC [FINITE_DELETE]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ Q.PAT_ASSUM `INJ f p q` MP_TAC
   ++ RW_TAC std_ss [INJ_DEF, IN_INSERT, IN_DELETE]
   ++ PROVE_TAC []);

val INFINITE_INJ = store_thm
  ("INFINITE_INJ",
   ``!f s t. INJ f s t /\ INFINITE s ==> INFINITE t``,
   PROVE_TAC [INFINITE_DEF, FINITE_INJ]);

val IN_PREIMAGE = store_thm
  ("IN_PREIMAGE",
   ``!f s x. x IN PREIMAGE f s = f x IN s``,
   RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]);

val PREIMAGE_EMPTY = store_thm
  ("PREIMAGE_EMPTY",
   ``!f. PREIMAGE f {} = {}``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, NOT_IN_EMPTY]);

val PREIMAGE_UNIV = store_thm
  ("PREIMAGE_UNIV",
   ``!f. PREIMAGE f UNIV = UNIV``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_UNIV]);

val PREIMAGE_COMPL = store_thm
  ("PREIMAGE_COMPL",
   ``!f s. PREIMAGE f (COMPL s) = COMPL (PREIMAGE f s)``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_COMPL]);

val PREIMAGE_UNION = store_thm
  ("PREIMAGE_UNION",
   ``!f s t. PREIMAGE f (s UNION t) = PREIMAGE f s UNION PREIMAGE f t``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_UNION]);

val PREIMAGE_INTER = store_thm
  ("PREIMAGE_INTER",
   ``!f s t. PREIMAGE f (s INTER t) = PREIMAGE f s INTER PREIMAGE f t``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER]);

val PREIMAGE_BIGUNION = store_thm
  ("PREIMAGE_BIGUNION",
   ``!f s. PREIMAGE f (BIGUNION s) = BIGUNION (IMAGE (PREIMAGE f) s)``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_BIGUNION_IMAGE]
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ PROVE_TAC []);

val IMAGE_o_INV = store_thm
  ("IMAGE_o_INV",
   ``!s f. (IMAGE f (s o f)) SUBSET s /\ s SUBSET ((IMAGE f s) o f)``,
   RW_TAC std_ss [IN_o, IN_IMAGE, SUBSET_DEF]
   ++ PROVE_TAC []);

val BIGUNION_PAIR = store_thm
  ("BIGUNION_PAIR",
   ``!s t. BIGUNION {s; t} = s UNION t``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_UNION, IN_INSERT, NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val COUNTABLE_IMAGE = store_thm
  ("COUNTABLE_IMAGE",
   ``!s f. countable s ==> countable (IMAGE f s)``,
   RW_TAC std_ss [countable_def, IN_IMAGE]
   ++ Q.EXISTS_TAC `f o f'`
   ++ RW_TAC std_ss [o_THM]
   ++ PROVE_TAC []);

val PREIMAGE_IMAGE = store_thm
  ("PREIMAGE_IMAGE",
   ``!f s. s SUBSET PREIMAGE f (IMAGE f s)``,
   RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_IMAGE]
   ++ PROVE_TAC []);

val IMAGE_PREIMAGE = store_thm
  ("IMAGE_PREIMAGE",
   ``!f s. IMAGE f (PREIMAGE f s) SUBSET s``,
   RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_IMAGE]
   ++ PROVE_TAC []);

val PREIMAGE_ALT = store_thm
  ("PREIMAGE_ALT",
   ``!f s. PREIMAGE f s = s o f``,
   RW_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION, IN_o]);

val DISJOINT_COUNT = store_thm
  ("DISJOINT_COUNT",
   ``!f.
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (!n. DISJOINT (f n) (BIGUNION (IMAGE f (count n))))``,
   RW_TAC arith_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                    IN_BIGUNION, IN_IMAGE, IN_COUNT]
   ++ REVERSE (Cases_on `x IN f n`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ REVERSE (Cases_on `x IN s`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ REVERSE (Cases_on `x' < n`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Know `~(x':num = n)` >> DECIDE_TAC
   ++ PROVE_TAC []);

val COUNTABLE_NUM = store_thm
  ("COUNTABLE_NUM",
   ``!s : num -> bool. countable s``,
   RW_TAC std_ss [countable_def]
   ++ Q.EXISTS_TAC `I`
   ++ RW_TAC std_ss [I_THM]);

val COUNTABLE_IMAGE_NUM = store_thm
  ("COUNTABLE_IMAGE_NUM",
   ``!f : num -> 'a. !s. countable (IMAGE f s)``,
   PROVE_TAC [COUNTABLE_NUM, COUNTABLE_IMAGE]);

val BIJ_IMAGE = store_thm
  ("BIJ_IMAGE",
   ``!f s t. BIJ f s t ==> (t = IMAGE f s)``,
   RW_TAC std_ss [BIJ_DEF, SURJ_DEF, EXTENSION, IN_IMAGE]
   ++ PROVE_TAC []);

val IMAGE_IMAGE = store_thm
  ("IMAGE_IMAGE",
   ``!f g s. IMAGE f (IMAGE g s) = IMAGE (f o g) s``,
   RW_TAC std_ss [EXTENSION, IN_IMAGE, o_THM]
   ++ PROVE_TAC []);

val FUNSET_INTER = store_thm
  ("FUNSET_INTER",
   ``!a b c. (a -> b INTER c) = (a -> b) INTER (a -> c)``,
   RW_TAC std_ss [EXTENSION, IN_FUNSET, IN_INTER]
   ++ PROVE_TAC []);

val COUNTABLE_EMPTY = store_thm
  ("COUNTABLE_EMPTY",
   ``countable {}``,
   PROVE_TAC [FINITE_COUNTABLE, FINITE_EMPTY]);

val COUNTABLE_ENUM = store_thm
  ("COUNTABLE_ENUM",
   ``!c. countable c = (c = {}) \/ (?f : num -> 'a. c = IMAGE f UNIV)``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC
   >> (NTAC 2 (RW_TAC std_ss [COUNTABLE_EMPTY])
       ++ RW_TAC std_ss [countable_def]
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
       ++ PROVE_TAC [])
   ++ REVERSE (RW_TAC std_ss [COUNTABLE_ALT])
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `enumerate c`
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [IN_UNIV, IN_IMAGE, BIJ_DEF, SURJ_DEF, EXTENSION]
       ++ PROVE_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss []
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `K e`
       ++ RW_TAC std_ss [EXTENSION, IN_SING, IN_IMAGE, IN_UNIV, K_THM])
   ++ DISJ2_TAC
   ++ Q.EXISTS_TAC `num_case e f`
   ++ RW_TAC std_ss [IN_INSERT, IN_IMAGE, EXTENSION, IN_UNIV]
   ++ EQ_TAC <<
   [RW_TAC std_ss [] <<
    [Q.EXISTS_TAC `0`
     ++ RW_TAC std_ss [num_case_def],
     Q.EXISTS_TAC `SUC x'`
     ++ RW_TAC std_ss [num_case_def]],
    RW_TAC std_ss []
    ++ Cases_on `x'` <<
    [RW_TAC std_ss [num_case_def],
     RW_TAC std_ss [num_case_def]
     ++ PROVE_TAC []]]);

val BIGUNION_IMAGE_UNIV = store_thm
  ("BIGUNION_IMAGE_UNIV",
   ``!f N.
       (!n. N <= n ==> (f n = {})) ==>
       (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N)))``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_COUNT,
                  NOT_IN_EMPTY]
   ++ REVERSE EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [NOT_LESS]);

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
   ++ Induct_on `d` >> RW_TAC arith_ss [SUBSET_REFL]
   ++ RW_TAC std_ss [ADD_CLAUSES]
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `f (n + d)`
   ++ RW_TAC std_ss []);

val DISJOINT_DIFFS = store_thm
  ("DISJOINT_DIFFS",
   ``!f m n.
       (!n. f n SUBSET f (SUC n)) /\
       (!n. g n = f (SUC n) DIFF f n) /\ ~(m = n) ==>
       DISJOINT (g m) (g n)``,
   RW_TAC std_ss []
   ++ Know `SUC m <= n \/ SUC n <= m` >> DECIDE_TAC
   ++ REWRITE_TAC [LESS_EQ_EXISTS]
   ++ STRIP_TAC <<
   [Know `f (SUC m) SUBSET f n` >> PROVE_TAC [SUBSET_ADD]
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    ++ PROVE_TAC [],
    Know `f (SUC n) SUBSET f m` >> PROVE_TAC [SUBSET_ADD]
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    ++ PROVE_TAC []]);

val PREIMAGE_COMP = store_thm
  ("PREIMAGE_COMP",
   ``!f g s. PREIMAGE f (PREIMAGE g s) = PREIMAGE (g o f) s``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, o_THM]);

val PREIMAGE_DIFF = store_thm
  ("PREIMAGE_DIFF",
   ``!f s t. PREIMAGE f (s DIFF t) = PREIMAGE f s DIFF PREIMAGE f t``,
   RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_DIFF]);

val PREIMAGE_I = store_thm
  ("PREIMAGE_I",
   ``PREIMAGE I = I``,
   FUN_EQ_TAC
   ++ SET_EQ_TAC
   ++ RW_TAC std_ss [IN_PREIMAGE, I_THM]);

val IMAGE_I = store_thm
  ("IMAGE_I",
   ``IMAGE I = I``,
   FUN_EQ_TAC
   ++ RW_TAC std_ss [EXTENSION, IN_IMAGE, I_THM]);

val PREIMAGE_K = store_thm
  ("PREIMAGE_K",
   ``!x s. PREIMAGE (K x) s = if x IN s then UNIV else {}``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, K_THM, IN_UNIV, NOT_IN_EMPTY]);

val INSERT_CASES = store_thm
  ("INSERT_CASES",
   ``!P. P {} /\ (!x s. ~(x IN s) ==> P (x INSERT s)) ==> (!s. P s)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `s` SET_CASES)
   ++ RW_TAC std_ss []
   ++ PROVE_TAC []);

val BOOL_SET_CASES = store_thm
  ("BOOL_SET_CASES",
   ``!P. P {} /\ P {T} /\ P {F} /\ P UNIV ==> (!x. P x)``,
   NTAC 2 STRIP_TAC
   ++ HO_MATCH_MP_TAC INSERT_CASES
   ++ ASM_REWRITE_TAC []
   ++ STRIP_TAC
   ++ HO_MATCH_MP_TAC INSERT_CASES
   ++ (Cases_on `x`
       ++ ASM_REWRITE_TAC []
       ++ Cases
       ++ RW_TAC std_ss [IN_INSERT]) <<
   [Suff `T INSERT F INSERT x'' = UNIV`
    >> PROVE_TAC []
    ++ RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT],
    Suff `F INSERT T INSERT x'' = UNIV`
    >> PROVE_TAC []
    ++ RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT]]);

val COMPL_INTER = store_thm
  ("COMPL_INTER",
   ``!s t. COMPL (s INTER t) = COMPL s UNION COMPL t``,
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION]);

val COUNTABLE_BIGUNION = store_thm
  ("COUNTABLE_BIGUNION",
   ``!c.
       countable c /\ (!s. s IN c ==> countable s) ==> countable (BIGUNION c)``,
   RW_TAC std_ss [countable_def]
   ++ POP_ASSUM
      (MP_TAC o CONV_RULE (DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV))
   ++ MP_TAC NUM_2D_BIJ_INV
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(\ (a : num, b : num). f'' (f a) b) o f'`
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ Q.PAT_ASSUM `!x. P x ==> ?y. Q x y` (MP_TAC o Q.SPEC `s`)
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `f (n : num)`)
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []      
   ++ Q.PAT_ASSUM `BIJ f' X Y` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(n, n')`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `y`
   ++ RW_TAC std_ss [o_THM]);

val COUNTABLE_UNION = store_thm
  ("COUNTABLE_UNION",
   ``!s t. countable s /\ countable t ==> countable (s UNION t)``,
   RW_TAC std_ss [GSYM BIGUNION_PAIR]
   ++ MATCH_MP_TAC COUNTABLE_BIGUNION
   ++ (RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
       ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC FINITE_COUNTABLE
   ++ RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]);

val COUNTABLE_SUBSET = store_thm
  ("COUNTABLE_SUBSET",
   ``!s t. s SUBSET t /\ countable t ==> countable s``,
   RW_TAC std_ss [countable_def, SUBSET_DEF]
   ++ Q.EXISTS_TAC `f`
   ++ PROVE_TAC []);

val COUNTABLE_BOOL_LIST = store_thm
  ("COUNTABLE_BOOL_LIST",
   ``!s : bool list -> bool. countable s``,
   STRIP_TAC
   ++ MATCH_MP_TAC COUNTABLE_SUBSET
   ++ Q.EXISTS_TAC `UNIV`
   ++ RW_TAC std_ss [SUBSET_UNIV]
   ++ Know
      `(UNIV : bool list -> bool) =
       BIGUNION (IMAGE (\x. PREIMAGE LENGTH {x}) UNIV)`
   >> RW_TAC std_ss [EXTENSION, IN_UNIV, IN_BIGUNION_IMAGE, IN_PREIMAGE,
                     IN_SING]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC COUNTABLE_BIGUNION
   ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, IN_IMAGE, IN_UNIV]
   ++ Induct_on `x`
   >> (RW_TAC std_ss [countable_def, IN_PREIMAGE, IN_SING, LENGTH_NIL]
       ++ Q.EXISTS_TAC `K []`
       ++ RW_TAC std_ss [K_THM])
   ++ Know
      `PREIMAGE LENGTH {SUC x} =
       IMAGE (CONS T) (PREIMAGE LENGTH {x}) UNION
       IMAGE (CONS F) (PREIMAGE LENGTH {x})`
   >> (RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_IMAGE, IN_SING, IN_UNION]
       ++ Cases_on `x'` >> RW_TAC std_ss [LENGTH]
       ++ RW_TAC std_ss [LENGTH]
       ++ PROVE_TAC [])
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC COUNTABLE_UNION
   ++ RW_TAC std_ss [COUNTABLE_IMAGE]);

val INTER_BIGUNION = store_thm
  ("INTER_BIGUNION",
   ``!s a. s INTER BIGUNION a = BIGUNION (IMAGE ($INTER s) a)``,
   RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION_IMAGE]
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ PROVE_TAC []);

val FINITE_DISJOINT_ENUM = store_thm
  ("FINITE_DISJOINT_ENUM",
   ``!c.
       FINITE c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))``,
   RW_TAC std_ss []
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
   >> (Q.EXISTS_TAC `K {}`
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, EXTENSION, IN_SING, K_THM,
                         DISJOINT_EMPTY, IN_BIGUNION, IN_IMAGE, NOT_IN_EMPTY]
       ++ PROVE_TAC [])
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ Know `!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t`
   >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `f IN X` MP_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT]
   ++ Q.EXISTS_TAC `num_case e f`
   ++ CONJ_TAC
   >> (RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INSERT]
       ++ Cases_on `x`
       ++ RW_TAC std_ss [num_case_def]
       ++ PROVE_TAC [])
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `X = Y` MP_TAC
       ++ RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE]
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [IN_INSERT, IN_IMAGE, IN_UNIV, IN_BIGUNION]
       ++ EQ_TAC <<
       [RW_TAC std_ss [] <<
        [Q.EXISTS_TAC `0`
         ++ RW_TAC std_ss [num_case_def],
         Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
         ++ Know `?s. x IN s /\ s IN c` >> PROVE_TAC []
         ++ RW_TAC std_ss []
         ++ Q.EXISTS_TAC `SUC x'`
         ++ RW_TAC std_ss [num_case_def]],
        RW_TAC std_ss []
        ++ (Cases_on `x'`
            ++ POP_ASSUM MP_TAC
            ++ RW_TAC std_ss [num_case_def])
        >> PROVE_TAC []
        ++ PROVE_TAC [NOT_IN_EMPTY]])
   ++ (Cases ++ Cases)
   ++ RW_TAC arith_ss [num_case_def]
   ++ PROVE_TAC [DISJOINT_EMPTY]);

val COUNTABLE_DISJOINT_ENUM = store_thm
  ("COUNTABLE_DISJOINT_ENUM",
   ``!c.
       countable c /\ (!s t. s IN c /\ t IN c /\ ~(s = t) ==> DISJOINT s t) ==>
       ?f : num -> 'a -> bool.
         f IN (UNIV -> ({} INSERT c)) /\
         (BIGUNION c = BIGUNION (IMAGE f UNIV)) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n))``,
   RW_TAC std_ss [COUNTABLE_ALT]
   >> (MP_TAC (Q.SPEC `c` FINITE_DISJOINT_ENUM)
       ++ RW_TAC std_ss [])
   ++ Q.EXISTS_TAC `enumerate c`
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_FUNSET, IN_INSERT,
                     EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, INJ_DEF]
   ++ PROVE_TAC []);

val COMPL_BIGINTER = store_thm
  ("COMPL_BIGINTER",
   ``!s. COMPL (BIGINTER s) = BIGUNION (IMAGE COMPL s)``,
   RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER, IN_BIGUNION_IMAGE]);

val IN_BIGINTER_IMAGE = store_thm
  ("IN_BIGINTER_IMAGE",
   ``!x f s. x IN BIGINTER (IMAGE f s) = (!y. y IN s ==> x IN f y)``,
   RW_TAC std_ss [IN_BIGINTER, IN_IMAGE]
   ++ PROVE_TAC []);

val IMAGE_K = store_thm
  ("IMAGE_K",
   ``!x s. IMAGE (K x) s = if s = {} then {} else {x}``,
   RW_TAC std_ss [EXTENSION, IN_IMAGE, K_THM, NOT_IN_EMPTY, IN_SING]
   ++ PROVE_TAC []);

val FINITE_BOOL = store_thm
  ("FINITE_BOOL",
   ``!s : bool -> bool. FINITE s``,
   Suff `FINITE (UNIV : bool -> bool)` >> PROVE_TAC [SUBSET_FINITE, SUBSET_UNIV]
   ++ Suff `UNIV = {T; F}`
   >> RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]
   ++ RW_TAC std_ss [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY]);

val COUNTABLE_BOOL = store_thm
  ("COUNTABLE_BOOL",
   ``!s : bool -> bool. countable s``,
   PROVE_TAC [FINITE_COUNTABLE, FINITE_BOOL]);

val COUNTABLE_SING = store_thm
  ("COUNTABLE_SING",
   ``!x. countable {x}``,
   PROVE_TAC [FINITE_COUNTABLE, FINITE_SING]);

val ALWAYS_IN_RANGE = store_thm
  ("ALWAYS_IN_RANGE",
   ``!f x. f x IN range f``,
   RW_TAC std_ss [range_def, IN_IMAGE, IN_UNIV]
   ++ PROVE_TAC []);

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
   ++ PROVE_TAC [ALWAYS_IN_RANGE]);

val RANGE_BIND = store_thm
  ("RANGE_BIND",
   ``!f g.
       range (FST o BIND f g) SUBSET
       BIGUNION (IMAGE (range o (\x. FST o g x)) (range (FST o f)))``,
   RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, range_def, IN_IMAGE, IN_UNIV,
                  o_THM, BIND_DEF, UNCURRY]
   ++ PROVE_TAC [FST, SND]);

val IN_PROD_SETS = store_thm
  ("IN_PROD_SETS",
   ``!s a b. s IN prod_sets a b = ?t u. (s = t CROSS u) /\ t IN a /\ u IN b``,
   RW_TAC std_ss [prod_sets_def, GSPECIFICATION, UNCURRY]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(t, u)`
   ++ RW_TAC std_ss []);

val PREIMAGE_CROSS = store_thm
  ("PREIMAGE_CROSS",
   ``!f a b.
       PREIMAGE f (a CROSS b) =
       PREIMAGE (FST o f) a INTER PREIMAGE (SND o f) b``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_CROSS, IN_INTER, o_THM]);

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
   ++ RW_TAC std_ss [SPECIFICATION]);

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
   ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, o_THM]
   ++ PROVE_TAC []);

val DISJOINT_ALT = store_thm
  ("DISJOINT_ALT",
   ``!s t. DISJOINT s t = !x. x IN s ==> ~(x IN t)``,
   RW_TAC std_ss [IN_DISJOINT]
   ++ PROVE_TAC []);

val COUNTABLE_INSERT = store_thm
  ("COUNTABLE_INSERT",
   ``!x xs. countable (x INSERT xs) = countable xs``,
   RW_TAC std_ss []
   ++ EQ_TAC >> PROVE_TAC [COUNTABLE_SUBSET, SUBSET_DEF, IN_INSERT]
   ++ RW_TAC std_ss [countable_def, IN_INSERT]
   ++ Q.EXISTS_TAC `num_case x f`
   ++ RW_TAC std_ss []
   >> (Q.EXISTS_TAC `0`
       ++ RW_TAC std_ss [num_case_def])
   ++ RES_TAC
   ++ Q.EXISTS_TAC `SUC n`
   ++ RW_TAC std_ss [num_case_def]);

val COUNTABLE_COUNT = store_thm
  ("COUNTABLE_COUNT",
   ``!n. countable (count n)``,
   PROVE_TAC [FINITE_COUNT, FINITE_COUNTABLE]);

val FINITE_BIJ_COUNT = store_thm
  ("FINITE_BIJ_COUNT",
   ``!s. FINITE s = ?c n. BIJ c (count n) s``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> PROVE_TAC [FINITE_COUNT, FINITE_BIJ]
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, NOT_IN_EMPTY]
   >> (Q.EXISTS_TAC `c`
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC std_ss [COUNT_ZERO, NOT_IN_EMPTY])
   ++ Q.EXISTS_TAC `\m. if m = n then e else c m`
   ++ Q.EXISTS_TAC `SUC n`
   ++ Know `!x. x IN count n ==> ~(x = n)`
   >> RW_TAC arith_ss [IN_COUNT]
   ++ RW_TAC std_ss [COUNT_SUC, IN_INSERT]
   ++ PROVE_TAC []);

val GCOMPL = store_thm
  ("GCOMPL",
   ``!p. {s | ~p s} = COMPL {s | p s}``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [GSPECIFICATION, IN_COMPL]);

val IN_I = store_thm
  ("IN_I",
   ``!x. x IN I = x``,
   RW_TAC std_ss [SPECIFICATION, I_THM]);

val COMPL_o = store_thm
  ("COMPL_o",
   ``!p q. COMPL p o q = COMPL (p o q)``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [IN_COMPL, IN_o]);

val BIJ_INV = store_thm
  ("BIJ_INV",
   ``!f s t.
       BIJ f s t ==>
       ?g.
         BIJ g t s /\
         (!x. x IN s ==> ((g o f) x = x)) /\
         (!x. x IN t ==> ((f o g) x = x))``,
   RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, o_THM]
   ++ POP_ASSUM
      (MP_TAC o
       CONV_RULE
       (DEPTH_CONV RIGHT_IMP_EXISTS_CONV
        THENC SKOLEM_CONV
        THENC REWRITE_CONV [EXISTS_DEF]
        THENC DEPTH_CONV BETA_CONV))
   ++ Q.SPEC_TAC (`@y. !x. x IN t ==> y x IN s /\ (f (y x) = x)`, `g`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `g`
   ++ RW_TAC std_ss []
   ++ PROVE_TAC []);

val FST_o_UNIT = store_thm
  ("FST_o_UNIT",
   ``!p a. p o FST o UNIT a = if a IN p then UNIV else {}``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [o_THM, UNIT_DEF, IN_o, IN_UNIV, NOT_IN_EMPTY]);

val IS_SOME_MMAP = store_thm
  ("IS_SOME_MMAP",
   ``!f. {x | IS_SOME x} o FST o MMAP SOME f = UNIV``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [IN_UNIV, IN_o, o_THM, MMAP_DEF, BIND_DEF, UNCURRY,
                     UNIT_DEF, GSPECIFICATION]);

val IS_SOME_INTER_MMAP = store_thm
  ("IS_SOME_INTER_MMAP",
   ``!p f.
       ((p o THE) INTER {x | IS_SOME x}) o FST o MMAP SOME f = p o FST o f``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [o_THM, MMAP_DEF, BIND_DEF, UNCURRY, UNIT_DEF, IN_INTER,
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
   ++ SET_EQ_TAC
   ++ Cases
   ++ Cases_on `q`
   ++ Cases_on `r`
   ++ RW_TAC std_ss [IN_UNION, IN_SING, NOT_IN_EMPTY]);

val FINITE_PAIR_BOOL = store_thm
  ("FINITE_PAIR_BOOL",
   ``!s:bool#bool->bool. FINITE s``,
   RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [SET_PAIR_BOOL]
   ++ RW_TAC std_ss [FINITE_UNION, FINITE_INSERT, FINITE_EMPTY]);


(* ************************************************************************* *)
(* Basic Definitions - pred_set - sum of a real-valued function on a set     *)
(* ************************************************************************* *)

(* ----------------------------------------------------------------------
    REAL_SUM_IMAGE

    This constant is the same as standard mathematics \Sigma operator:

     \Sigma_{x\in P}{f(x)} = SUM_IMAGE f P

    Where f's range is the real numbers and P is finite.
   ---------------------------------------------------------------------- *)

val REAL_SUM_IMAGE_DEF = new_definition(
  "REAL_SUM_IMAGE_DEF",
  ``REAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0:real)``);

val REAL_SUM_IMAGE_THM = store_thm(
  "REAL_SUM_IMAGE_THM",
  ``!f. (REAL_SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (REAL_SUM_IMAGE f (e INSERT s) =
                f e + REAL_SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC
  >> SIMP_TAC (srw_ss()) [ITSET_THM, REAL_SUM_IMAGE_DEF]
  ++ SIMP_TAC (srw_ss()) [REAL_SUM_IMAGE_DEF]
  ++ Q.ABBREV_TAC `g = \e acc. f e + acc`
  ++ Suff `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)`
  >> (Q.UNABBREV_TAC `g` ++ SRW_TAC [] [])
  ++ MATCH_MP_TAC COMMUTING_ITSET_RECURSES
  ++ Q.UNABBREV_TAC `g`
  ++ RW_TAC real_ss []
  ++ REAL_ARITH_TAC);

val REAL_SUM_IMAGE_SING = store_thm(
  "REAL_SUM_IMAGE_SING",
  ``!f e. REAL_SUM_IMAGE f {e} = f e``,
  SRW_TAC [][REAL_SUM_IMAGE_THM]);

val REAL_SUM_IMAGE_POS = store_thm
  ("REAL_SUM_IMAGE_POS",
   ``!f s. FINITE s /\
	   (!x. x IN s ==> 0 <= f x) ==>
		0 <= REAL_SUM_IMAGE f s``,
   REPEAT STRIP_TAC
   ++ POP_ASSUM MP_TAC ++ Q.SPEC_TAC (`f`, `f`)
   ++ POP_ASSUM MP_TAC ++ Q.SPEC_TAC (`s`, `s`)
   ++ Q.ABBREV_TAC `Q = (\s. !f. (!x. x IN s ==> 0 <= f x) ==> 0 <= REAL_SUM_IMAGE f s)`
   ++ Suff `!s. FINITE s ==> Q s` >> (Q.UNABBREV_TAC `Q` ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ Q.UNABBREV_TAC `Q`
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ MATCH_MP_TAC REAL_LE_ADD
   ++ CONJ_TAC >> FULL_SIMP_TAC real_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ Q.PAT_ASSUM `!f. (!x. x IN s ==> 0 <= f x) ==> 0 <= REAL_SUM_IMAGE f s` MATCH_MP_TAC
   ++ REPEAT STRIP_TAC ++ Q.PAT_ASSUM `!x. b` MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_INSERT]);

val REAL_SUM_IMAGE_SPOS = store_thm
  ("REAL_SUM_IMAGE_SPOS",
   ``!s. FINITE s /\ (~(s = {})) ==>
	   !f. (!x. x IN s ==> 0 < f x) ==>
		0 < REAL_SUM_IMAGE f s``,
   Suff `!s. FINITE s ==>
		(\s. (~(s = {})) ==>
	   !f. (!x. x IN s ==> 0 < f x) ==>
		0 < REAL_SUM_IMAGE f s) s`
   >> RW_TAC std_ss [] 
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
		      FORALL_AND_THM]
   ++ Cases_on `s = {}`
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ MATCH_MP_TAC REAL_LT_ADD
   ++ ASM_SIMP_TAC real_ss []);

val REAL_SUM_IMAGE_NONZERO_lem = prove
  (``!P. FINITE P ==>
	(\P. !f. (!x.x IN P ==> 0 <= f x) /\ (?x. x IN P /\ ~(f x = 0)) ==>
		((~(REAL_SUM_IMAGE f P = 0)) = (~(P = {})))) P``,
   (MATCH_MP_TAC FINITE_INDUCT
    ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_INSERT_EMPTY, IN_INSERT]
    ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
   >> (ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
       ++ `0 <= f e + REAL_SUM_IMAGE f s`
		by (MATCH_MP_TAC REAL_LE_ADD
		    ++ RW_TAC std_ss []
		    ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
		    ++ METIS_TAC [])
       ++ ASM_REWRITE_TAC []
       ++ RW_TAC std_ss [GSYM real_lt]
       ++ MATCH_MP_TAC REAL_LTE_TRANS
       ++ Q.EXISTS_TAC `f e + 0`
       ++ CONJ_TAC
       >> (RW_TAC real_ss [] ++ POP_ASSUM (K ALL_TAC)
	   ++ POP_ASSUM MP_TAC ++ POP_ASSUM (MP_TAC o Q.SPECL [`e`])
	   ++ SIMP_TAC std_ss []
	   ++ REAL_ARITH_TAC)
       ++ MATCH_MP_TAC REAL_LE_ADD2
       ++ RW_TAC real_ss []
       ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
       ++ METIS_TAC [])
   ++ Cases_on `f e = 0`
   >> (RW_TAC real_ss [] ++ METIS_TAC [NOT_IN_EMPTY])
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ `0 <= f e + REAL_SUM_IMAGE f s`
		by (MATCH_MP_TAC REAL_LE_ADD
		    ++ RW_TAC std_ss []
		    ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
		    ++ METIS_TAC [])
   ++ ASM_REWRITE_TAC []
   ++ RW_TAC std_ss [GSYM real_lt]
   ++ MATCH_MP_TAC REAL_LTE_TRANS
   ++ Q.EXISTS_TAC `f e + 0`
   ++ CONJ_TAC
   >> (RW_TAC real_ss [] ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM MP_TAC ++ POP_ASSUM (K ALL_TAC)
       ++ POP_ASSUM (K ALL_TAC) ++ POP_ASSUM (MP_TAC o Q.SPECL [`e`])
	   ++ SIMP_TAC std_ss []
	   ++ REAL_ARITH_TAC)
   ++ MATCH_MP_TAC REAL_LE_ADD2
   ++ RW_TAC real_ss []
   ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS
   ++ METIS_TAC []);

val REAL_SUM_IMAGE_NONZERO = store_thm
  ("REAL_SUM_IMAGE_NONZERO",
   ``!P. FINITE P ==>
	!f. (!x.x IN P ==> 0 <= f x) /\ (?x. x IN P /\ ~(f x = 0)) ==>
		((~(REAL_SUM_IMAGE f P = 0)) = (~(P = {})))``,
   METIS_TAC [REAL_SUM_IMAGE_NONZERO_lem]);

val REAL_SUM_IMAGE_IF_ELIM_lem = prove
  (``!s. FINITE s ==>
		(\s. !P f. (!x. x IN s ==> P x) ==>
			(REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
	 		 REAL_SUM_IMAGE f s)) s``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_IF_ELIM = store_thm
  ("REAL_SUM_IMAGE_IF_ELIM",
   ``!s P f. FINITE s /\ (!x. x IN s ==> P x) ==>
		(REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
	 	 REAL_SUM_IMAGE f s)``,
   METIS_TAC [REAL_SUM_IMAGE_IF_ELIM_lem]);

val REAL_SUM_IMAGE_FINITE_SAME_lem = prove
  (``!P. FINITE P ==>
	 (\P. !f p.             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, DELETE_NON_ELEMENT]
   ++ `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT] ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC real_ss [CARD_INSERT, ADD1]
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD]
   ++ RW_TAC real_ss [REAL_ADD_RDISTRIB]
   ++ Suff `REAL_SUM_IMAGE f s = & (CARD s) * f e`
   >> RW_TAC real_ss [REAL_ADD_COMM]
   ++ (MP_TAC o Q.SPECL [`s`]) SET_CASES ++ RW_TAC std_ss []
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   ++ `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
   ++ Q.PAT_ASSUM `!f p. b` MATCH_MP_TAC ++ METIS_TAC [IN_INSERT]);
   
val REAL_SUM_IMAGE_FINITE_SAME = store_thm
  ("REAL_SUM_IMAGE_FINITE_SAME",
   ``!P. FINITE P ==>
	 !f p.             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)``,
   MP_TAC REAL_SUM_IMAGE_FINITE_SAME_lem ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_FINITE_CONST = store_thm
  ("REAL_SUM_IMAGE_FINITE_CONST",
   ``!P. FINITE P ==>
	!f x. (!y. f y = x) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`P`]) REAL_SUM_IMAGE_FINITE_SAME
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   ++ RW_TAC std_ss []
   ++ (MP_TAC o Q.SPECL [`P`]) SET_CASES
   ++ RW_TAC std_ss [] >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM MATCH_MP_TAC
   ++ Q.EXISTS_TAC `x'` ++ RW_TAC std_ss [IN_INSERT]);

val REAL_SUM_IMAGE_IN_IF_lem = prove
  (``!P. FINITE P ==>
		(\P.!f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   ++ POP_ASSUM MP_TAC
   ++ ONCE_REWRITE_TAC [DELETE_NON_ELEMENT]
   ++ SIMP_TAC real_ss [IN_INSERT]
   ++ `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then f x else 0)) s =
       REAL_SUM_IMAGE (\x. (if x IN s then f x else 0)) s`
	by (POP_ASSUM (MP_TAC o Q.SPECL [`(\x. (if (x = e) \/ x IN s then f x else 0))`])
	    ++ RW_TAC std_ss [])
   ++ POP_ORW
   ++ POP_ASSUM (MP_TAC o Q.SPECL [`f`])
   ++ RW_TAC real_ss []);

val REAL_SUM_IMAGE_IN_IF = store_thm
  ("REAL_SUM_IMAGE_IN_IF",
   ``!P. FINITE P ==>
	!f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P``,
   METIS_TAC [REAL_SUM_IMAGE_IN_IF_lem]);

val REAL_SUM_IMAGE_CMUL_lem = prove
  (``!f c P. FINITE P ==>
	(\P. REAL_SUM_IMAGE (\x. c * f x) P = c * (REAL_SUM_IMAGE f P)) P``,
   STRIP_TAC ++ STRIP_TAC ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, REAL_ADD_LDISTRIB, DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_CMUL = store_thm
  ("REAL_SUM_IMAGE_CMUL",
   ``!P. FINITE P ==>
	!f c. (REAL_SUM_IMAGE (\x. c * f x) P = c * (REAL_SUM_IMAGE f P))``,
   METIS_TAC [REAL_SUM_IMAGE_CMUL_lem]);

val REAL_SUM_IMAGE_NEG = store_thm
  ("REAL_SUM_IMAGE_NEG",
   ``!P. FINITE P ==>
	!f. (REAL_SUM_IMAGE (\x. ~ f x) P = ~ (REAL_SUM_IMAGE f P))``,
   REPEAT STRIP_TAC
   ++ (ASSUME_TAC o Q.SPECL [`f`, `~1`] o UNDISCH o Q.SPEC `P`) REAL_SUM_IMAGE_CMUL
   ++ FULL_SIMP_TAC real_ss []);

val REAL_SUM_IMAGE_IMAGE_lem = prove
  (``!P. FINITE P ==>
	(\P.!f'. INJ f' P (IMAGE f' P) ==> (!f. REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, IMAGE_EMPTY, IMAGE_INSERT, INJ_DEF, IN_INSERT]
   ++ `FINITE (IMAGE f' s)` by (MATCH_MP_TAC IMAGE_FINITE ++ RW_TAC std_ss [])
   ++ `~ (f' e IN IMAGE f' s)`
	by (RW_TAC std_ss [IN_IMAGE] ++ REVERSE (Cases_on `x IN s`) >> ASM_REWRITE_TAC [] ++ METIS_TAC [])
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, REAL_SUM_IMAGE_THM, REAL_EQ_LADD]
   ++ Q.PAT_ASSUM `!f'. a /\ b ==> (!f. c = d)` MATCH_MP_TAC
   ++ RW_TAC std_ss [IN_IMAGE] ++ Q.EXISTS_TAC `x` ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_IMAGE = store_thm
  ("REAL_SUM_IMAGE_IMAGE",
   ``!P. FINITE P ==>
	!f'. INJ f' P (IMAGE f' P) ==> (!f. REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P)``,
   METIS_TAC [REAL_SUM_IMAGE_IMAGE_lem]);

val REAL_SUM_IMAGE_DISJOINT_UNION_lem = prove
  (``!P.
	FINITE P ==>
	(\P. !P'. FINITE P' ==>
		(\P'. DISJOINT P P' ==>
			(!f. REAL_SUM_IMAGE f (P UNION P') =
		     	     REAL_SUM_IMAGE f P +
		     	     REAL_SUM_IMAGE f P')) P') P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC
   >> (RW_TAC real_ss [DISJOINT_EMPTY, UNION_EMPTY, REAL_SUM_IMAGE_THM])
   ++ REPEAT STRIP_TAC
   ++ CONV_TAC (BETA_CONV) ++ MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC
   >> (RW_TAC real_ss [DISJOINT_EMPTY, UNION_EMPTY, REAL_SUM_IMAGE_THM])
   ++ FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
   ++ ONCE_REWRITE_TAC [DISJOINT_SYM]
   ++ RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
   ++ FULL_SIMP_TAC std_ss [DISJOINT_SYM]
   ++ ONCE_REWRITE_TAC [UNION_COMM] ++ RW_TAC std_ss [INSERT_UNION]
   ++ ONCE_REWRITE_TAC [UNION_COMM] ++ ONCE_REWRITE_TAC [INSERT_COMM]
   ++ `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
   ++ Q.ABBREV_TAC `Q = e INSERT s UNION s'`
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ Q.UNABBREV_TAC `Q`
   ++ `~ (e' IN (e INSERT s UNION s'))`
	by RW_TAC std_ss [IN_INSERT, IN_UNION]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ REAL_ARITH_TAC);

val REAL_SUM_IMAGE_DISJOINT_UNION = store_thm
  ("REAL_SUM_IMAGE_DISJOINT_UNION",
   ``!P P'. FINITE P /\ FINITE P' /\ DISJOINT P P' ==>
		(!f. REAL_SUM_IMAGE f (P UNION P') =
		     REAL_SUM_IMAGE f P +
		     REAL_SUM_IMAGE f P')``,
   METIS_TAC [REAL_SUM_IMAGE_DISJOINT_UNION_lem]);

val REAL_SUM_IMAGE_EQ_CARD_lem = prove
   (``!P. FINITE P ==>
	(\P. REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P))) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, IN_INSERT]
   ++ (MP_TAC o Q.SPECL [`s`]) CARD_INSERT
   ++ RW_TAC real_ss [ADD1] ++ ONCE_REWRITE_TAC [GSYM REAL_ADD]
   ++ Suff `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) (s DELETE e) = 
		REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
   >> RW_TAC real_ss []
   ++ Q.PAT_ASSUM `REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s = & (CARD s)` (K ALL_TAC)
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
       REAL_SUM_IMAGE (\x. if x IN s then (\x. (if (x = e) \/ x IN s then 1 else 0)) x else 0) s`
	by (METIS_TAC [REAL_SUM_IMAGE_IN_IF])
   ++ RW_TAC std_ss []);

val REAL_SUM_IMAGE_EQ_CARD = store_thm
  ("REAL_SUM_IMAGE_EQ_CARD",
   ``!P. FINITE P ==>
	(REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P)))``,
   METIS_TAC [REAL_SUM_IMAGE_EQ_CARD_lem]);

val REAL_SUM_IMAGE_INV_CARD_EQ_1 = store_thm
  ("REAL_SUM_IMAGE_INV_CARD_EQ_1",
   ``!P. (~(P = {})) /\ FINITE P ==>
		(REAL_SUM_IMAGE (\s. if s IN P then inv (& (CARD P)) else 0) P = 1)``,
    REPEAT STRIP_TAC
    ++ `(\s. if s IN P then inv (& (CARD P)) else 0) = (\s. inv (& (CARD P)) * (\s. if s IN P then 1 else 0) s)`
	by (RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC real_ss [])
    ++ POP_ORW
    ++ `REAL_SUM_IMAGE (\s. inv (& (CARD P)) * (\s. (if s IN P then 1 else 0)) s) P =
	(inv (& (CARD P))) * (REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P)`
		by (MATCH_MP_TAC REAL_SUM_IMAGE_CMUL ++ RW_TAC std_ss [])
    ++ POP_ORW
    ++ `REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P = (&(CARD P))`
		by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ_CARD ++ RW_TAC std_ss [])
    ++ POP_ORW
    ++ MATCH_MP_TAC REAL_MUL_LINV
    ++ RW_TAC real_ss []
    ++ METIS_TAC [CARD_EQ_0]);

val REAL_SUM_IMAGE_INTER_NONZERO_lem = prove
  (``!P. FINITE P ==>
	(\P. !f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
		 REAL_SUM_IMAGE f P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, INTER_EMPTY, INSERT_INTER]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ (RW_TAC std_ss [IN_DEF] ++ RW_TAC real_ss [])
   ++ `FINITE (s INTER (\p. ~(f p = 0)))` by (MATCH_MP_TAC INTER_FINITE ++ RW_TAC std_ss [])
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   ++ `~(e IN (s INTER (\p. ~(f p = 0))))`
	by RW_TAC std_ss [IN_INTER]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_NONZERO = store_thm
  ("REAL_SUM_IMAGE_INTER_NONZERO",
   ``!P. FINITE P ==>
	!f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
		 REAL_SUM_IMAGE f P``,
   METIS_TAC [REAL_SUM_IMAGE_INTER_NONZERO_lem]);

val REAL_SUM_IMAGE_INTER_ELIM_lem = prove
  (``!P. FINITE P ==>
	(\P. !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
			(REAL_SUM_IMAGE f (P INTER P') =
			 REAL_SUM_IMAGE f P)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM, INSERT_INTER]
   ++ Cases_on `e IN P'`
   >> (`~ (e IN (s INTER P'))` by RW_TAC std_ss [IN_INTER]
       ++ FULL_SIMP_TAC std_ss [INTER_FINITE, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT])
   ++ FULL_SIMP_TAC real_ss []
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_ELIM = store_thm
  ("REAL_SUM_IMAGE_INTER_ELIM",
   ``!P. FINITE P ==>
	 !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
			(REAL_SUM_IMAGE f (P INTER P') =
			 REAL_SUM_IMAGE f P)``,   
   METIS_TAC [REAL_SUM_IMAGE_INTER_ELIM_lem]);

val REAL_SUM_IMAGE_COUNT = store_thm
  ("REAL_SUM_IMAGE_COUNT",
   ``!f n. REAL_SUM_IMAGE f (pred_set$count n) =
	   sum (0,n) f``,
   STRIP_TAC ++ Induct
   >> RW_TAC std_ss [pred_setTheory.count_def, REAL_SUM_IMAGE_THM, GSPEC_F, sum]
   ++ `pred_set$count (SUC n) = n INSERT pred_set$count n`
	by (RW_TAC std_ss [EXTENSION, IN_INSERT, pred_setTheory.IN_COUNT] ++ DECIDE_TAC)
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, sum, pred_setTheory.FINITE_COUNT]
   ++ `pred_set$count n DELETE n = pred_set$count n`
	by RW_TAC arith_ss [DELETE_DEF, DIFF_DEF, IN_SING, pred_setTheory.IN_COUNT,
			    Once EXTENSION, pred_setTheory.IN_COUNT, GSPECIFICATION,
		      	    DECIDE ``!(x:num) (y:num). x < y ==> ~(x = y)``]
   ++ RW_TAC std_ss [REAL_ADD_SYM]);

val REAL_SUM_IMAGE_MONO = store_thm
  ("REAL_SUM_IMAGE_MONO",
   ``!P. FINITE P ==>
	   !f f'. (!x. x IN P ==> f x <= f' x) ==>
		REAL_SUM_IMAGE f P <= REAL_SUM_IMAGE f' P``,
   Suff `!P. FINITE P ==>
		(\P. !f f'. (!x. x IN P ==> f x <= f' x) ==>
		REAL_SUM_IMAGE f P <= REAL_SUM_IMAGE f' P) P`
   >> PROVE_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT, IN_INSERT,
		      DISJ_IMP_THM, FORALL_AND_THM, REAL_LE_ADD2]);

val REAL_SUM_IMAGE_POS_MEM_LE = store_thm
  ("REAL_SUM_IMAGE_POS_MEM_LE",
   ``!P. FINITE P ==>
	!f. (!x. x IN P ==> 0 <= f x) ==>
	    (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)``,
   Suff `!P. FINITE P ==>
	(\P. !f. (!x. x IN P ==> 0 <= f x) ==>
	    (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)) P`
   >> PROVE_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_IN_EMPTY, IN_INSERT,
		     DISJ_IMP_THM, FORALL_AND_THM,
		     DELETE_NON_ELEMENT]
   >> (Suff `f e + 0 <= f e + REAL_SUM_IMAGE f s` >> RW_TAC real_ss []
       ++ MATCH_MP_TAC REAL_LE_LADD_IMP
       ++ MATCH_MP_TAC REAL_SUM_IMAGE_POS ++ ASM_REWRITE_TAC [])
   ++ Suff `0 + f x <= f e + REAL_SUM_IMAGE f s` >> RW_TAC real_ss []
   ++ MATCH_MP_TAC REAL_LE_ADD2 ++ PROVE_TAC []);

val REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD = store_thm
  ("REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD",
   ``!P. FINITE P ==>
	!f. (REAL_SUM_IMAGE f P = 1) /\
	    (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
	    (!x. x IN P ==> (f x = inv (& (CARD P))))``,
   Suff `!P. FINITE P ==>
	(\P. !f. (REAL_SUM_IMAGE f P = 1) /\
	    (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
	    (!x. x IN P ==> (f x = inv (& (CARD P))))) P`
  >> RW_TAC std_ss []
  ++ MATCH_MP_TAC FINITE_INDUCT
  ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]
  >> (RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
      ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
      ++ Q.PAT_ASSUM `(f:'a->real) e + REAL_SUM_IMAGE f s = 1`
	(MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
      ++ `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
	       (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
	by METIS_TAC []
      ++ POP_ORW
      ++ ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
      ++ (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o 
	  UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
      ++ SIMP_TAC std_ss []
      ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
      ++ `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
      ++ POP_ORW
      ++ `1:real = &1` by RW_TAC real_ss []
      ++ POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
      ++ REPEAT (POP_ASSUM (K ALL_TAC))
      ++ METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT])
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   ++ RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
   ++ Q.PAT_ASSUM `f e + REAL_SUM_IMAGE f s = 1`
	(MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
   ++ `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
	       (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
	by METIS_TAC []
   ++ POP_ORW
   ++ ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
   ++ (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o 
	  UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
   ++ SIMP_TAC std_ss []
   ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
   ++ `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
   ++ POP_ORW
   ++ `1:real = &1` by RW_TAC real_ss []
   ++ POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
   ++ `f x = f e` by METIS_TAC [] ++ POP_ORW
   ++ REPEAT (POP_ASSUM (K ALL_TAC))
   ++ METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT]);


val REAL_SUM_IMAGE_ADD = store_thm
  ("REAL_SUM_IMAGE_ADD",
   ``!s. FINITE s ==> !f f'.
		(REAL_SUM_IMAGE (\x. f x + f' x) s =
		 REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f' s)``,
   Suff `!s. FINITE s ==>
	(\s. !f f'.
		(REAL_SUM_IMAGE (\x. f x + f' x) s =
		 REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f' s)) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
   ++ REAL_ARITH_TAC);


val REAL_SUM_IMAGE_REAL_SUM_IMAGE = store_thm
  ("REAL_SUM_IMAGE_REAL_SUM_IMAGE",
   ``!s s' f. FINITE s /\ FINITE s' ==>
	(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
	 REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))``,
   Suff `!s. FINITE s ==>
	     (\s. !s' f. FINITE s' ==>
	(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
	 REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [CROSS_EMPTY, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
   ++ `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
	by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
	    ++ (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
	    ++ RW_TAC std_ss [] ++ FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
	    ++ METIS_TAC [])
   ++ POP_ORW
   ++ `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
	by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION, 
				  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
	    ++ STRIP_TAC ++ (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
	    ++ RW_TAC std_ss [FST, SND]
	    ++ METIS_TAC [])
   ++ (MP_TAC o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
	Q.ISPECL [`IMAGE (\x. (e:'a,x)) (s':'b->bool)`, `(s:'a->bool) CROSS (s':'b->bool)`]) 
	REAL_SUM_IMAGE_DISJOINT_UNION
   ++ RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE]
   ++ POP_ASSUM (K ALL_TAC)
   ++ (MP_TAC o Q.SPEC `(\x. (e,x))` o UNDISCH o Q.SPEC `s'` o 
	INST_TYPE [``:'c``|->``:'a # 'b``] o INST_TYPE [``:'a``|->``:'b``] o 
	INST_TYPE [``:'b``|->``:'c``]) REAL_SUM_IMAGE_IMAGE
   ++ RW_TAC std_ss [INJ_DEF, IN_IMAGE, o_DEF] ++ METIS_TAC []);


val REAL_SUM_IMAGE_0 = store_thm
  ("REAL_SUM_IMAGE_0",
   ``!s. FINITE s ==> (REAL_SUM_IMAGE (\x. 0) s = 0)``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`(\x. 0)`,`0`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
   ++ RW_TAC real_ss []);


val SEQ_REAL_SUM_IMAGE = store_thm
  ("SEQ_REAL_SUM_IMAGE",
   ``!s. FINITE s ==>
	!f f'. (!x. x IN s ==> (\n. f n x) --> f' x) ==>
	 	(\n. REAL_SUM_IMAGE (f n) s) -->
		REAL_SUM_IMAGE f' s``,
   Suff `!s. FINITE s ==>
		(\s. !f f'. (!x. x IN s ==> (\n. f n x) --> f' x) ==>
	 	(\n. REAL_SUM_IMAGE (f n) s) -->
		REAL_SUM_IMAGE f' s) s`
   >> RW_TAC std_ss []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, SEQ_CONST, IN_INSERT, DELETE_NON_ELEMENT]
   ++ `(\n. f n e + REAL_SUM_IMAGE (f n) s) = (\n. (\n. f n e) n + (\n. REAL_SUM_IMAGE (f n) s) n)`
   	by RW_TAC std_ss []
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ METIS_TAC []);


val NESTED_REAL_SUM_IMAGE_REVERSE = store_thm
  ("NESTED_REAL_SUM_IMAGE_REVERSE",
   ``!f s s'. FINITE s /\ FINITE s' ==>
		(REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
		 REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (\y. f y x) s) s')``,
   RW_TAC std_ss [REAL_SUM_IMAGE_REAL_SUM_IMAGE]
   ++ `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
	by (RW_TAC std_ss [EXTENSION, IN_CROSS, IN_IMAGE]
	    ++ EQ_TAC >> (STRIP_TAC ++ Q.EXISTS_TAC `(SND x, FST x)` ++ RW_TAC std_ss [PAIR])
	    ++ RW_TAC std_ss [] ++ RW_TAC std_ss [FST, SND])
   ++ POP_ORW
   ++ `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
   ++ `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
	by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >> METIS_TAC []
	    ++ METIS_TAC [PAIR, PAIR_EQ])
   ++ `REAL_SUM_IMAGE (\x. f (SND x) (FST x)) (IMAGE (\x. (SND x,FST x)) (s CROSS s')) =
       REAL_SUM_IMAGE ((\x. f (SND x) (FST x)) o (\x. (SND x,FST x))) (s CROSS s')`
	by METIS_TAC [REAL_SUM_IMAGE_IMAGE]
   ++ POP_ORW
   ++ RW_TAC std_ss [o_DEF]);


val finite_enumeration_of_sets_has_max_non_empty = store_thm
  ("finite_enumeration_of_sets_has_max_non_empty",
   ``!f s. FINITE s /\ (!x. f x IN s) /\
	    (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
	    ?N. !n:num. n >= N ==> (f n = {})``,
	`!s. FINITE s ==>
	(\s.  !f. (!x. f x IN {} INSERT s) /\
		  (~({} IN s)) /\
		 (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
		 ?N. !n:num. n >= N ==> (f n = {})) s`
	by (MATCH_MP_TAC FINITE_INDUCT
	    ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
	    ++ Q.PAT_ASSUM `!f. (!x. (f x = {}) \/ f x IN s) /\ ~({} IN s) /\
				(!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
            			?N:num. !n. n >= N ==> (f n = {})`
		(MP_TAC o Q.SPEC `(\x. if f x = e then {} else f x)`)
	    ++ `(!x. ((\x. (if f x = e then {} else f x)) x = {}) \/
		     (\x. (if f x = e then {} else f x)) x IN s) /\ ~({} IN s)`
		by METIS_TAC []
	    ++ ASM_SIMP_TAC std_ss []
	    ++ `(!m n. ~(m = n) ==> DISJOINT (if f m = e then {} else f m)
			(if f n = e then {} else f n))`
		by (RW_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY]
			    ++ METIS_TAC [IN_DISJOINT])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss []
	    ++ Cases_on `?n. f n = e`
	    >> (FULL_SIMP_TAC std_ss []
		++ Cases_on `n < N`
		>> (Q.EXISTS_TAC `N`
		    ++ RW_TAC std_ss [GREATER_EQ]
		    ++ `~(n' = n)` 
			by METIS_TAC [LESS_LESS_EQ_TRANS, 
				      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
		    ++ Cases_on `f n' = f n`
		    >> (`DISJOINT (f n') (f n)` by METIS_TAC []
			++ FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
			++ METIS_TAC [])
		    ++ Q.PAT_ASSUM
				`!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
				(MP_TAC o Q.SPEC `n'`)
		    ++ ASM_SIMP_TAC std_ss [GREATER_EQ])
		++ Q.EXISTS_TAC `SUC n`
		++ RW_TAC std_ss [GREATER_EQ]
		++ FULL_SIMP_TAC std_ss [NOT_LESS]
		++ `~(n' = n)` 
			by METIS_TAC [LESS_LESS_EQ_TRANS,
				      DECIDE ``!n:num. n < SUC n``,
				      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
		++ Cases_on `f n' = f n`
		>> (`DISJOINT (f n') (f n)` by METIS_TAC []
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
		++ `N <= n'` by METIS_TAC [LESS_EQ_IMP_LESS_SUC,
				           LESS_LESS_EQ_TRANS,
				           LESS_IMP_LESS_OR_EQ]
		++ Q.PAT_ASSUM
				`!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
				(MP_TAC o Q.SPEC `n'`)
		++ ASM_SIMP_TAC std_ss [GREATER_EQ])
	++ METIS_TAC [])
   ++ REPEAT STRIP_TAC
   ++ Cases_on `{} IN s`
   >> (Q.PAT_ASSUM `!s. FINITE s ==> P` (MP_TAC o Q.SPEC `s DELETE {}`)
       ++ RW_TAC std_ss [FINITE_DELETE, IN_INSERT, IN_DELETE])
   ++ METIS_TAC [IN_INSERT]);

val _ = overload_on ("SIGMA", ``REAL_SUM_IMAGE ``);
val LIST_TO_SET_NIL = prove  (``(LIST_TO_SET [] = {})``,   RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_LIST_TO_SET, MEM]);val LIST_TO_SET_SING = store_thm  ("LIST_TO_SET_SING",   ``!x. LIST_TO_SET [x] = {x}``,   RW_TAC list_ss [EXTENSION, GSPECIFICATION, IN_SING, IN_LIST_TO_SET]);val LIST_TO_SET_THM = store_thm  ("LIST_TO_SET_THM",   ``(LIST_TO_SET [] = {}) /\     (!h l. LIST_TO_SET (h::l) = h INSERT (LIST_TO_SET l))``,   CONJ_TAC >> SIMP_TAC std_ss [LIST_TO_SET_NIL]   ++ RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT, IN_LIST_TO_SET, MEM]);val FINITE_LIST_TO_SET = store_thm  ("FINITE_LIST_TO_SET",   ``!l. FINITE (LIST_TO_SET l)``,   Induct   ++ RW_TAC std_ss [FINITE_EMPTY, FINITE_INSERT, LIST_TO_SET_THM]);   val ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM = store_thm  ("ALL_DISTINCT_imp_REAL_SUM_IMAGE_of_LIST_TO_SET_eq_REAL_SUM",   ``!l. ALL_DISTINCT l ==>		(REAL_SUM_IMAGE f (LIST_TO_SET l) = REAL_SUM (MAP f l))``,   Induct   ++ RW_TAC list_ss [REAL_SUM_def, LIST_TO_SET_THM, REAL_SUM_IMAGE_THM, ALL_DISTINCT, FINITE_INSERT, FINITE_LIST_TO_SET]   ++ METIS_TAC [DELETE_NON_ELEMENT, IN_LIST_TO_SET, REAL_EQ_LADD]);val LIST_TO_SET_APPEND = store_thm  ("LIST_TO_SET_APPEND",   ``!l l'. LIST_TO_SET (l++l') = (LIST_TO_SET l) UNION (LIST_TO_SET l')``,   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION, IN_LIST_TO_SET, MEM_APPEND]);val LIST_TO_SET_MAP = store_thm  ("LIST_TO_SET_MAP",   ``!f l. LIST_TO_SET (MAP f l) = IMAGE f (LIST_TO_SET l)``,   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_IMAGE, IN_LIST_TO_SET, MEM_MAP]);val IMAGE_LIST_TO_SET = store_thm  ("IMAGE_LIST_TO_SET",   ``!f l. IMAGE f (LIST_TO_SET l) = LIST_TO_SET (MAP f l)``,   RW_TAC std_ss [GSYM LIST_TO_SET_MAP]);val CROSS_LIST_TO_SET = store_thm  ("CROSS_LIST_TO_SET",   ``!l l'. (LIST_TO_SET l) CROSS (LIST_TO_SET l') =	    LIST_TO_SET (LIST_COMBS l l')``,   RW_TAC std_ss [EXTENSION, IN_CROSS, IN_LIST_TO_SET, MEM_LIST_COMBS]);val LIST_TO_SET_MAKE_ALL_DISTINCT = store_thm  ("LIST_TO_SET_MAKE_ALL_DISTINCT",   ``!l. LIST_TO_SET (MAKE_ALL_DISTINCT l) = LIST_TO_SET l``,   RW_TAC std_ss [EXTENSION, IN_LIST_TO_SET, MEM_MAKE_ALL_DISTINCT]);val CARD_LIST_TO_SET = store_thm  ("CARD_LIST_TO_SET",   ``!l. CARD (LIST_TO_SET l) =	 LENGTH (MAKE_ALL_DISTINCT l)``,   Induct >> RW_TAC std_ss [MAKE_ALL_DISTINCT_def, LENGTH, CARD_EMPTY, LIST_TO_SET_THM]   ++ RW_TAC std_ss [MAKE_ALL_DISTINCT_def, LENGTH, CARD_EMPTY, LIST_TO_SET_THM]   >> METIS_TAC [ABSORPTION, IN_LIST_TO_SET]   ++ ASM_SIMP_TAC bool_ss [CARD_DEF, FINITE_LIST_TO_SET, IN_LIST_TO_SET]);

val UNIV_NEQ_EMPTY = store_thm
  ("UNIV_NEQ_EMPTY",
   ``~(UNIV={})``,
   RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_UNIV]);

val DIFF_INTER = store_thm
	("DIFF_INTER", ``!s t g. (s DIFF t) INTER g = s INTER g DIFF t``,
		RW_TAC std_ss [DIFF_DEF,INTER_DEF,EXTENSION] 
		++ RW_TAC std_ss [GSPECIFICATION] 
		++ EQ_TAC >> RW_TAC std_ss [] ++ RW_TAC std_ss []
    ); 
    
val DIFF_INTER2 = store_thm
	("DIFF_INTER2", ``!s t. s DIFF (t INTER s) = s DIFF t``,
		RW_TAC std_ss [DIFF_DEF,INTER_DEF,EXTENSION] 
		++ RW_TAC std_ss [GSPECIFICATION,LEFT_AND_OVER_OR] 	
    ); 
    
val PREIMAGE_COMPL_INTER = store_thm
	("PREIMAGE_COMPL_INTER", ``!f t sp. PREIMAGE f (COMPL t) INTER sp = sp DIFF (PREIMAGE f t)``,
	RW_TAC std_ss [COMPL_DEF]
	++ MP_TAC (REWRITE_RULE [PREIMAGE_UNIV] (Q.SPECL [`f`,`UNIV`,`t`] PREIMAGE_DIFF))
	++ STRIP_TAC
	++ `(PREIMAGE f (UNIV DIFF t)) INTER sp = (UNIV DIFF PREIMAGE f t) INTER sp` by METIS_TAC []
	++ METIS_TAC [DIFF_INTER,INTER_UNIV]
			 
   );
   
val PREIMAGE_REAL_COMPL1 = store_thm 
   ("PREIMAGE_REAL_COMPL1", ``!c:real. COMPL {x | c < x} = {x | x <= c}``,
   RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION] THEN RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]
   );

val PREIMAGE_REAL_COMPL2 = store_thm 
   ("PREIMAGE_REAL_COMPL2", ``!c:real. COMPL {x | c <= x} = {x | x < c}``,
   RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION] THEN RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]
   );


val PREIMAGE_REAL_COMPL3 = store_thm 
   ("PREIMAGE_REAL_COMPL3", ``!c:real. COMPL {x | x <= c} = {x | c < x}``,
   RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION] THEN RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]
   );


val PREIMAGE_REAL_COMPL4 = store_thm 
   ("PREIMAGE_REAL_COMPL4", ``!c:real. COMPL {x | x < c} = {x | c <= x}``,
   RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION] THEN RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]
   );

val DIFF_DIFF_SUBSET = store_thm
   ("DIFF_DIFF_SUBSET", ``!s t. (t SUBSET s) ==> (s DIFF (s DIFF t) = t)``,
 	RW_TAC std_ss [DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,SUBSET_DEF]
 	++ EQ_TAC >> RW_TAC std_ss []
 	++ RW_TAC std_ss []
   );
 
 
val BIGINTER_SUBSET = store_thm
("BIGINTER_SUBSET", ``!sp s. (!t. t IN s ==> t SUBSET sp)  /\ (~(s = {})) ==> (BIGINTER s) SUBSET sp``,
  RW_TAC std_ss [SUBSET_DEF,IN_BIGINTER]
  ++ `?u. u IN s` by METIS_TAC [CHOICE_DEF]
  ++ METIS_TAC []
 );
  
val DIFF_BIGINTER1 = store_thm
   ("DIFF_BIGINTER1", ``!sp s. sp DIFF (BIGINTER s) = BIGUNION (IMAGE (\u. sp DIFF u) s)``,
  	RW_TAC std_ss [DIFF_DEF,BIGINTER,BIGUNION,EXTENSION,GSPECIFICATION,IN_IMAGE,IN_BIGINTER]
  	++ EQ_TAC >> ( RW_TAC std_ss [] ++ Q.EXISTS_TAC `(sp DIFF s')` ++ RW_TAC std_ss [DIFF_DEF,GSPECIFICATION] ++ Q.EXISTS_TAC `s'` ++ RW_TAC std_ss [] )
  	++ RW_TAC std_ss [] >> METIS_TAC []
 	++ Q.EXISTS_TAC `u` ++ METIS_TAC []
   );
 
 
val DIFF_BIGINTER = store_thm
   ("DIFF_BIGINTER", ``!sp s. (!t. t IN s ==> t SUBSET sp)  /\ (~(s = {})) ==> ( BIGINTER s = sp DIFF (BIGUNION (IMAGE (\u. sp DIFF u) s)) )``,
  	RW_TAC std_ss []
	++ `(BIGINTER s SUBSET sp)` by RW_TAC std_ss [BIGINTER_SUBSET]
	++ ASSUME_TAC (Q.SPECL [`sp`,`s`] DIFF_BIGINTER1)
	++ `sp DIFF (sp DIFF (BIGINTER s)) = (BIGINTER s)` by RW_TAC std_ss [DIFF_DIFF_SUBSET]
	++ METIS_TAC []
   );
 


val _ = export_theory ();
