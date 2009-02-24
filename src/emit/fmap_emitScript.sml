open HolKernel boolLib bossLib Parse;
open EmitML pred_setTheory finite_mapTheory;
open option_emitTheory list_emitTheory set_emitTheory;

val _ = new_theory "fmap_emit";

val FAPPLY_FEMPTY = Q.prove
(`FAPPLY (FEMPTY:('a,'b)fmap) x :'b =
  FAIL FAPPLY ^(mk_var("empty map",bool)) FEMPTY x`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val DRESTRICT_PRED_THM =
  SIMP_RULE std_ss [boolTheory.IN_DEF]
   (CONJ DRESTRICT_FEMPTY DRESTRICT_FUPDATE);

val DRESTRICT_PRED_THM =
  SIMP_RULE std_ss [boolTheory.IN_DEF]
   (CONJ DRESTRICT_FEMPTY DRESTRICT_FUPDATE);

val th = GEN_ALL
             (CONV_RULE (DEPTH_CONV ETA_CONV)
               (ABS (Term `a:'a`)
                 (SIMP_RULE std_ss [IN_SING,IN_DEF]
                   (Q.SPEC `{x}` (Q.SPEC `a` IN_COMPL)))));

val RRESTRICT_PRED_THM = Q.prove
(`(!P. RRESTRICT (FEMPTY:'a|->'b) P = (FEMPTY:'a|->'b)) /\
  (!(f:'a|->'b) P x y.
       RRESTRICT (f |+ (x,y)) P =
        if P y then RRESTRICT f P |+ (x,y)
          else RRESTRICT (DRESTRICT f (\a. ~(a = x))) P)`,
 REWRITE_TAC [RRESTRICT_FEMPTY]
  THEN METIS_TAC [REWRITE_RULE [th] RRESTRICT_FUPDATE, IN_DEF]);

val FRANGE_EQNS = Q.prove
(`(FRANGE (FEMPTY:'a|->'b) = ({}:'b set)) /\
  (!(f:'a |-> 'b) (x:'a) (y:'b).
         FRANGE (f |+ (x,y)) = y INSERT FRANGE (DRESTRICT f (\a. ~(a = x))))`,
 METIS_TAC [REWRITE_RULE [th] FRANGE_FUPDATE, FRANGE_FEMPTY]);

val o_f_EQNS = Q.prove
(`(f          o_f (FEMPTY:'a|->'b) = (FEMPTY:'a|->'c)) /\
  ((f:'b->'c) o_f ((fm:'a|->'b) |+ (k,v)) = (f o_f fm \\ k) |+ (k,f v))`,
 METIS_TAC [o_f_FEMPTY, o_f_FUPDATE])

val T_INTRO = PURE_ONCE_REWRITE_RULE [PROVE[] (Term `x = (x = T)`)]

val defs =
  DEFN_NOSIG (CONJ FDOM_FEMPTY FDOM_FUPDATE)
  :: map DEFN [CONJ FAPPLY_FEMPTY FAPPLY_FUPDATE_THM,
       FCARD_DEF, FLOOKUP_DEF, REWRITE_RULE [FUN_EQ_THM] FUPDATE_LIST,
       CONJ FUNION_FEMPTY_1 (CONJ FUNION_FEMPTY_2 FUNION_FUPDATE_1),
       CONJ DOMSUB_FEMPTY DOMSUB_FUPDATE_THM,
       CONJ (T_INTRO (SPEC_ALL SUBMAP_FEMPTY)) SUBMAP_FUPDATE,
       DRESTRICT_PRED_THM, RRESTRICT_PRED_THM]
   @ DEFN_NOSIG FRANGE_EQNS
  :: map DEFN [o_f_EQNS, CONJ (T_INTRO (SPEC_ALL FEVERY_FEMPTY))
       (REWRITE_RULE [th] FEVERY_FUPDATE)]

val _ = eSML "fmap"
  (ABSDATATYPE (["'a","'b"], `fmap = FEMPTY | FUPDATE of fmap => 'a#'b`)
   :: OPEN ["num", "list", "set", "option"]
   :: MLSIG "type num = numML.num"
   :: MLSIG "type 'a set = 'a setML.set"
   :: MLSIG "val FEMPTY   : ('a,'b) fmap"
   :: MLSIG "val FUPDATE  : ('a,'b) fmap * ('a * 'b) -> ('a,'b)fmap"
   :: MLSIG "val FDOM     : ('a,'b) fmap -> 'a set"
   :: defs)

val _ = eCAML "fmap"
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set"]
   @ ABSDATATYPE (["'a","'b"], `fmap = FEMPTY | FUPDATE of fmap => 'a # 'b`)
   :: OPEN ["num", "list", "set", "option"]
   :: MLSIG "val _FDOM     : ('a,'b) fmap -> 'a set"
   :: MLSIG "val _FRANGE   : ('a,'b) fmap -> 'b set"
   :: defs)

val _ = export_theory ();
