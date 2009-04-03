open HolKernel boolLib bossLib Parse;
open EmitML rich_listTheory;
open list_emitTheory;

val _ = new_theory "rich_list_emit";

val num_CASES = arithmeticTheory.num_CASES;

val NOT_SUC = numTheory.NOT_SUC;
val PRE =  prim_recTheory.PRE;

val BUTFIRSTN_compute = Q.prove(
  `!n l. BUTFIRSTN n l =
           if n = 0 then l else
           if l = [] then
             FAIL BUTFIRSTN ^(mk_var("List too short",bool)) n []
           else
             BUTFIRSTN (PRE n) (TL l)`,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [BUTFIRSTN]
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, TL, NOT_SUC, PRE, BUTFIRSTN,
                      combinTheory.FAIL_THM]);

val ELL_compute = Q.prove(
  `!n l. ELL n l = if n = 0 then LAST l else ELL (PRE n) (FRONT l)`,
   STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
     THEN REWRITE_TAC [NOT_SUC, PRE, ELL]);

val GENLIST_compute = Q.prove(
  `!n l.
     GENLIST f n = if n = 0 then [] else SNOC (f (PRE n)) (GENLIST f (PRE n))`,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN REWRITE_TAC [NOT_SUC, PRE, GENLIST]);

val FIRSTN_compute = Q.prove(
  `!n l. FIRSTN n l =
           if n = 0 then [] else
           if l = [] then
             FAIL FIRSTN ^(mk_var("List too short",bool)) n []
           else
             (HD l)::FIRSTN (PRE n) (TL l)`,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [FIRSTN]
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, HD, TL, NOT_SUC, PRE, FIRSTN,
                      combinTheory.FAIL_THM]);

val REPLICATE_compute = Q.prove(
  `!n l. REPLICATE n l = if n = 0 then [] else l::(REPLICATE (PRE n) l)`,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC num_CASES
    THEN REWRITE_TAC [NOT_SUC, PRE, REPLICATE]);

val SEG_compute = Q.prove(
  `!m k l. SEG m k l =
             if m = 0 then [] else
             if l = [] then
               FAIL SEG ^(mk_var("List too short",bool)) m k []
             else
               if k = 0 then
                 (HD l)::SEG (PRE m) 0 (TL l)
               else
                 SEG m (PRE k) (TL l)`,
  STRIP_TAC THEN Q.SPEC_THEN `m` STRUCT_CASES_TAC num_CASES
    THEN1 REWRITE_TAC [SEG]
    THEN STRIP_TAC THEN Q.SPEC_THEN `k` STRUCT_CASES_TAC num_CASES
    THEN STRIP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES
    THEN REWRITE_TAC [NOT_CONS_NIL, HD, TL, NOT_SUC, PRE, SEG,
                      combinTheory.FAIL_THM]);

val defs =
  map DEFN [AND_EL_DEF,BUTFIRSTN_compute,
            ELL_compute,SNOC,GENLIST_compute,FIRSTN_compute,
            IS_PREFIX,IS_SUBLIST,OR_EL_DEF,SPLITP,PREFIX_DEF,
            REPLICATE_compute,SCANL,SCANR,SEG_compute,
            SUFFIX_DEF,UNZIP_FST_DEF,UNZIP_SND_DEF];

val _ = eSML "rich_list"
  (MLSIG "type num = numML.num"
   :: OPEN ["pair","num","list"]
   :: defs)

val _ = eCAML "rich_list"
  (MLSIG "type num = NumML.num"
   :: MLSTRUCT "type num = NumML.num"
   :: OPEN ["pair","num","list"]
   :: defs)

val _ = export_theory ();
