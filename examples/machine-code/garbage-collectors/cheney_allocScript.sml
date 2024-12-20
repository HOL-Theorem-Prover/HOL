
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory finite_mapTheory;
open cheney_gcTheory;

val _ = new_theory "cheney_alloc";
val _ = ParseExtras.temp_loose_equality()
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* -- definitions -- *)

val cheney_alloc_gc_def = Define `
  cheney_alloc_gc (i,e,root,l,u,m) =
    if i < e then (i,e,root,l,u,m) else cheney_collector(i,e,root,l,u,m)`;

val cheney_alloc_aux_def = Define `
  cheney_alloc_aux (i,e,root,l,u,m) d =
    if i = e then (i,e,0::TL root,l,u,m) else
      let m = (i =+ DATA(HD root,HD (TL root),d)) m in
        (i+1,e,i::TL root,l,u,m)`;

val cheney_alloc_def = Define `
  cheney_alloc(i,e,root,l,u,m) d = cheney_alloc_aux (cheney_alloc_gc (i,e,root,l,u,m)) d`;

(* -- helper -- *)

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM pairTheory.PAIR)
  fun get_conv vs = let
    val (x,y) = pairSyntax.dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end
    handle HOL_ERR e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

(* -- theorems -- *)

val bijection_def = Define `bijection g = ONTO g /\ ONE_ONE g`;

val bijection_swap = prove(
  ``!i j. bijection (swap i j)``,
  SIMP_TAC std_ss [bijection_def,ONTO_DEF,ONE_ONE_THM,swap_def]
  \\ REPEAT STRIP_TAC THENL [
    Cases_on `y = i` THEN1 (Q.EXISTS_TAC `j` \\ Cases_on `j = i` \\ ASM_REWRITE_TAC [])
    \\ Cases_on `y = j` THEN1 (Q.EXISTS_TAC `i` \\ Cases_on `j = i` \\ ASM_REWRITE_TAC [])
    \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [],
    Cases_on `x1 = i` \\ Cases_on `x2 = i`
    \\ Cases_on `x1 = j` \\ Cases_on `x2 = j` \\ FULL_SIMP_TAC bool_ss []]);

val bijection_inv = prove(
  ``!f. bijection f ==> ?g. (f o g = I) /\ (g o f = I) /\ bijection g``,
  SIMP_TAC std_ss [bijection_def,ONE_ONE_DEF,ONTO_DEF,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `\x. @y. f y = x` \\ METIS_TAC []);

val bijection_bijection = prove(
  ``!f g. bijection f /\ bijection g ==> bijection (f o g)``,
  SIMP_TAC std_ss [bijection_def,ONTO_DEF,ONE_ONE_THM] \\ METIS_TAC []);

val basic_abs = basic_abs_def

val ok_abs_def = Define `
  ok_abs (r,h:(num|->(num#num#'a)),l:num) =
    ~(0 IN FDOM h) /\ FEVERY (\(x,y,z,d). {y;z} SUBSET0 FDOM h) h /\
    (!k. MEM k r /\ ~(k = 0) ==> k IN FDOM h)`;

val ch_set_def = Define `ch_set h (x,y,z,d) = (h ' x = (y,z,d)) /\ x IN FDOM h`;

val abstract_def = Define `
  abstract(b,m) = { (b(x), b(y), b(z), d) |(x,y,z,d)| m(x) = DATA(y,z,d) }`;

val ch_inv_def = Define `
  ch_inv (r,h,l) (i,e,c,l',u,m) =
    ok_state (i,e,c,l,u,m) /\ ok_abs (r,h,l) /\ (l = l') /\
    ?b. bijection b /\ (b 0 = 0) /\ (MAP b c = r) /\
        reachables r (ch_set(h)) SUBSET abstract(b,m) /\ abstract(b,m) SUBSET ch_set(h)`;

val apply_abstract = prove(
  ``!b m. bijection b ==> (apply b (abstract(b,m)) = basic_abs m)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ SIMP_TAC bool_ss [apply_def,abstract_def,GSPECIFICATION,basic_abs]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `(x,y,z,d)` \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [bijection_def,ONE_ONE_DEF] \\ METIS_TAC []);

val SUBSET_IMP_apply_SUBSET = prove(
  ``!b s t. s SUBSET t ==> apply b s SUBSET apply b t``,
  SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF,apply_def,
    METIS_PROVE [PAIR] ``(!x. f x ==> g x) = !x y z d. f (x,y,z,d) ==> g (x,y,z,d)``]);

val SUBSET_EQ_apply_SUBSET = prove(
  ``!b s t. bijection b ==> (s SUBSET t = apply b s SUBSET apply b t)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC [SUBSET_IMP_apply_SUBSET]
  \\ IMP_RES_TAC bijection_inv \\ METIS_TAC [apply_apply,apply_I,SUBSET_IMP_apply_SUBSET]);

val ch_inv_thm = prove(
  ``ch_inv (r,h,l) (i,e,c,l',u,m) =
      ok_state (i,e,c,l,u,m) /\ ok_abs (r,h,l) /\ (l = l') /\
      ?b. bijection b /\ (b 0 = 0) /\ (MAP b c = r) /\
          (basic_abs m SUBSET apply b (ch_set h)) /\
          (apply b (reachables r (ch_set h)) SUBSET basic_abs m)``,
  METIS_TAC [SUBSET_EQ_apply_SUBSET,apply_abstract,ch_inv_def]);

val INFINITE_num = prove(
  ``INFINITE (UNIV:num->bool)``,
  REWRITE_TAC [INFINITE_UNIV] \\ Q.EXISTS_TAC `SUC`
  \\ SIMP_TAC std_ss []  \\ Q.EXISTS_TAC `0` \\ DECIDE_TAC);

val fresh_def = Define `fresh (h:num|->(num#num#'a)) = @x:num. ~(x IN 0 INSERT FDOM h)`;

val fresh_NOT_IN_FDOM = (SIMP_RULE std_ss [IN_INSERT] o prove)(
  ``!h. ~(fresh h IN 0 INSERT FDOM h)``,
  REWRITE_TAC [fresh_def] \\ METIS_TAC [NOT_IN_FINITE,INFINITE_num,FINITE_INSERT,FDOM_FINITE]);

val _ = save_thm("fresh_NOT_IN_FDOM",fresh_NOT_IN_FDOM);

val fresh_THM = prove(
  ``FEVERY (\(x,y,z,d). {y; z} SUBSET0 FDOM h) h ==>
    !y z d. ~((fresh h,y,z,d) IN ch_set h) /\ ~((z,fresh h,y,d) IN ch_set h) /\
            ~((y,z,fresh h,d) IN ch_set h) /\ ~(fresh h = 0)``,
  SIMP_TAC std_ss [fresh_NOT_IN_FDOM,IN_DEF,ch_set_def,FEVERY_DEF]
  \\ REWRITE_TAC [METIS_PROVE [] ``x \/ ~y = y ==> x:bool``]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ Q.PAT_X_ASSUM `h ' qq = gh` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DEF]
  \\ METIS_TAC [SIMP_RULE std_ss [IN_DEF] fresh_NOT_IN_FDOM]);

val INSERT_THM = prove(
  ``!x s. x INSERT s = \y. (x = y) \/ s y``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF] \\ METIS_TAC []);

val apply_INSERT = prove(
  ``!k f. (f o k = I) ==> (k o f = I) ==> !x y z d s.
      (apply f ((x:num,y,z,d:'a) INSERT s) = ((k x):num,k y,k z,d) INSERT apply f s)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ SIMP_TAC std_ss [apply_def,IN_DEF,INSERT_THM,FUN_EQ_THM] \\ METIS_TAC []);

val PATH_SUBSET = prove(
  ``!xs x s t. PATH (x,xs) s /\ s SUBSET t ==> PATH (x,xs) t``,
  Induct \\ FULL_SIMP_TAC std_ss[PATH_def,SUBSET_DEF] \\ METIS_TAC []);

val fix_MEM = prove(``set l x = MEM x l``, SIMP_TAC bool_ss [IN_DEF])

val reachables_reachables = prove(
  ``!c s. reachables c (reachables c s) = reachables c s``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [reachables_def,IN_DEF]
  \\ REWRITE_TAC [fix_MEM]
  \\ EQ_TAC \\ SIMP_TAC std_ss [] \\ REWRITE_TAC [reachable_def]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
  \\ REPEAT (POP_ASSUM (fn th => ASSUME_TAC th \\ UNDISCH_TAC (concl th)))
  \\ Q.SPEC_TAC(`d`,`d`) \\ Q.SPEC_TAC(`z`,`z`) \\ Q.SPEC_TAC(`y`,`y`)
  \\ Q.SPEC_TAC(`x`,`x`) \\ Q.SPEC_TAC(`c`,`c`) \\ Q.SPEC_TAC(`r`,`r`)
  \\ Induct_on `p` \\ REWRITE_TAC [APPEND,PATH_def]
  THEN1 (SIMP_TAC std_ss [PATH_def,IN_DEF,reachables_def,reachable_def] \\ METIS_TAC [])
  \\ NTAC 8 STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF,reachable_def]
  \\ FULL_SIMP_TAC bool_ss [fix_MEM] \\ REPEAT STRIP_TAC
  THENL [ALL_TAC,METIS_TAC [],ALL_TAC,METIS_TAC []]
  \\ MATCH_MP_TAC PATH_SUBSET \\ Q.EXISTS_TAC `reachables [h] s`
  \\ (STRIP_TAC THEN1 METIS_TAC [MEM])
  \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF]
  \\ Cases \\ Cases_on `r'` \\ Cases_on `r''`
  \\ SIMP_TAC std_ss [reachables_def,IN_DEF,reachable_def,MEM]
  \\ REWRITE_TAC [fix_MEM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss [] \\ DISJ2_TAC THENL [
    Q.EXISTS_TAC `[]` \\ ASM_REWRITE_TAC [APPEND,PATH_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `h::p'` \\ ASM_REWRITE_TAC [APPEND,PATH_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `[]` \\ ASM_REWRITE_TAC [APPEND,PATH_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `h::p'` \\ ASM_REWRITE_TAC [APPEND,PATH_def,IN_DEF] \\ METIS_TAC []]);

val bijection_apply = prove(
  ``!b. bijection b ==> bijection (apply b)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC bijection_inv
  \\ SIMP_TAC std_ss [bijection_def,ONE_ONE_DEF,ONTO_DEF] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `apply g y` \\ ASM_REWRITE_TAC [apply_apply,apply_I])
  \\ SIMP_TAC std_ss [EXTENSION,IN_DEF]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
  \\ Q.SPEC_TAC (`q`,`x`) \\ Q.SPEC_TAC (`q'`,`y`) \\ Q.SPEC_TAC (`q''`,`z`) \\ Q.SPEC_TAC (`r`,`d`)
  \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ `apply b x1 (g x,g y,g z,d) = apply b x2 (g x,g y,g z,d)` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss [apply_def]
  \\ sg `!x. b (g x) = x` \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,IN_DEF]);

val CARD_EQ_CARD_apply = prove(
  ``!s:('a#'a#'a#'b)set b:'a->'a. FINITE s /\ bijection b ==> (CARD s = CARD (apply b s))``,
  REPEAT STRIP_TAC \\ (MATCH_MP_TAC o RW [AND_IMP_INTRO] o
    Q.GEN `f` o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) FINITE_BIJ_CARD_EQ
  \\ ASM_REWRITE_TAC []
  \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ Q.EXISTS_TAC `\x. (k (FST x),k (FST (SND x)),k (FST (SND (SND x))),SND (SND (SND x)))`
  \\ SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF] \\ REPEAT STRIP_TAC THENL [
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
    \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,IN_DEF,apply_def],
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
    \\ Cases_on `x'` \\ Cases_on `r'` \\ Cases_on `r''`
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [bijection_def,ONE_ONE_DEF],
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
    \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,IN_DEF,apply_def],
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
    \\ Q.EXISTS_TAC `(b q,b q',b q'',r)`
    \\ FULL_SIMP_TAC std_ss [IN_DEF,apply_def,FUN_EQ_THM],
    MATCH_MP_TAC
      (Q.ISPEC `\x. (b (FST x):'a,b (FST (SND x)):'a,b (FST (SND (SND x))):'a,SND (SND (SND x)):'b)` FINITE_INJ)
    \\ Q.EXISTS_TAC `s` \\ ASM_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF]
    \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
    \\ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,apply_def]
    \\ Cases_on `x'` \\ Cases_on `r'` \\ Cases_on `r''`
    \\ FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,apply_def]
    \\ METIS_TAC [bijection_def,ONE_ONE_DEF]]);

val apply_switch = prove(
  ``!f f' x x'. (f o f' = I) /\ (x' = apply f x) ==> (x = apply f' x')``,
  SIMP_TAC bool_ss [apply_apply,apply_I]);

val ok_state_part_def = Define `
  ok_state_part (i,j,m) =
    !k. if ~RANGE(i,j) k then m k = EMP else ?y z d. m k = DATA (y,z,d)`;

val WFS_part_IMP_CUT = prove(
  ``ok_state_part(i,j,m) ==> (m = CUT (i,j)m)``,
  SIMP_TAC std_ss [ok_state_part_def,LET_DEF,IN_DEF,CUT_def,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val WFS_IMP_CUT = prove(
  ``ok_state(i,e,r,l,u,m) ==> (m = CUT (if u then 1 + l else 1,i)m)``,
  SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF,CUT_def,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val FINITE_basic_abs_CUT = prove(
  ``!j i m. FINITE (basic_abs (CUT(i,j)m))``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (INST_TYPE [``:'a``|->``:(num#num#num#'a)``,``:'b``|->``:num``] FINITE_INJ)
  \\ Q.EXISTS_TAC `FST` \\ Q.EXISTS_TAC `RANGE(i,j)`
  \\ SIMP_TAC std_ss [INJ_DEF,FINITE_RANGE] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  THEN1 (FULL_SIMP_TAC std_ss [IN_DEF,basic_abs,CUT_def] \\ METIS_TAC [heap_type_distinct])
  \\ Cases_on `y` \\ Cases_on `r'` \\ Cases_on `r''`
  \\ FULL_SIMP_TAC std_ss [IN_DEF,basic_abs,CUT_def,heap_type_11] \\ METIS_TAC []);

val ok_state_CARD_EQ_lemma = prove(
  ``!j i m. ok_state_part (i,i+j,m) ==> (CARD (basic_abs m) = j)``,
  Induct THENL [
    SIMP_TAC std_ss [ok_state_part_def,LET_DEF,RANGE_lemmas,EMPTY_DEF]
    \\ REPEAT STRIP_TAC \\ sg `basic_abs m = {}` \\ ASM_REWRITE_TAC [CARD_EMPTY]
    \\ SIMP_TAC std_ss[FUN_EQ_THM,EMPTY_DEF]
    \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
    \\ ASM_SIMP_TAC std_ss[basic_abs,heap_type_distinct],
    REPEAT STRIP_TAC \\ sg `ok_state_part (i,i+j,(i+j =+ EMP) m)` THENL [
      FULL_SIMP_TAC std_ss [ok_state_part_def,LET_DEF] \\ REPEAT STRIP_TAC
      \\ Cases_on `RANGE(i,i+j)k` \\ ASM_SIMP_TAC std_ss [UPDATE_def] THENL [
        `~(i + j = k) /\ RANGE(i,i+SUC j)k` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
        \\ METIS_TAC [],
        Cases_on `i + j = k` \\ ASM_SIMP_TAC bool_ss []
        \\ `~RANGE(i,i+SUC j)k` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
        \\ METIS_TAC []],
      RES_TAC
      \\ `RANGE(i,i+SUC j)(i+j)` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
      \\ `?x y d. m (i + j) = DATA(x,y,d)` by METIS_TAC [ok_state_part_def]
      \\ Q.ABBREV_TAC `xxx = basic_abs ((i+j =+ EMP) m)`
      \\ sg `(basic_abs m = (i+j,x,y,d) INSERT xxx) /\ ~((i+j,x,y,d) IN xxx)`
      \\ REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
      \\ Q.UNABBREV_TAC `xxx` THENL [
        SIMP_TAC std_ss [INSERT_THM,IN_DEF,basic_abs,UPDATE_def,heap_type_distinct]
        \\ REPEAT STRIP_TAC
        \\ Cases_on `x' = i + j` \\ ASM_SIMP_TAC std_ss [heap_type_11,heap_type_distinct],
        `FINITE (basic_abs m)` by METIS_TAC [WFS_part_IMP_CUT,FINITE_basic_abs_CUT]
        \\ METIS_TAC [CARD_INSERT,FINITE_INSERT]]]]);

val ok_state_CARD_EQ = prove(
  ``!j i m. ok_state_part (i,j,m) ==> (CARD (basic_abs m) = j - i)``,
  NTAC 3 STRIP_TAC \\ Cases_on `i <= j` THENL [
    FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS]
    \\ `i + p - i = p` by DECIDE_TAC \\ METIS_TAC [ok_state_CARD_EQ_lemma],
    ` (j - i = 0) /\ !k.~RANGE(i,j)k` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [ok_state_part_def] \\ STRIP_TAC
    \\ sg `basic_abs m = {}` \\ ASM_SIMP_TAC bool_ss [CARD_EMPTY]
    \\ REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ ASM_REWRITE_TAC [basic_abs,EMPTY_DEF,heap_type_distinct]]);

val WFS_IMP_WFS_part = prove(
  ``ok_state (i,e,c,l,u,m) ==> ok_state_part (if u then 1 + l else 1,i,m)``,
  SIMP_TAC std_ss [LET_DEF,ok_state_def,ok_state_part_def,IN_DEF] \\ METIS_TAC []);

val MAP_INV = prove(
  ``!f g xs ys. (MAP f xs = ys) /\ (g o f = I) /\ (f o g = I) ==> (MAP g ys = xs)``,
  Induct_on `xs` \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [MAP,NOT_CONS_NIL,FUN_EQ_THM,CONS_11]
  \\ METIS_TAC []);

val reachables_SUBSET = prove(
  ``!x s. t SUBSET s ==> reachables x t SUBSET s``,
  SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF] \\ METIS_TAC []);

val apply_SUBSET = prove(
  ``!f s t. t SUBSET s ==> apply f t SUBSET apply f s``,
  SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [apply_def,IN_DEF] \\ METIS_TAC []);

val EXPAND_SUBSET = prove(
  ``!t s. t SUBSET s = !x y z d. t (x,y,z,d) ==> s (x,y,z,d)``,
  SIMP_TAC std_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [PAIR,PAIR_EQ]);

val FINITE_set = prove(
  ``!h:num|->num#num#'a. FINITE (ch_set h)``,
  CONV_TAC (QUANT_CONV (UNBETA_CONV ``h:num|->num#num#'a``))
  \\ MATCH_MP_TAC fmap_INDUCT \\ SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC THENL [
    sg `ch_set (FEMPTY:num|->num#num#'a) = {}`
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY]
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY,ch_set_def,EMPTY_DEF,FDOM_FEMPTY,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``],
    sg `ch_set ((f |+ (x,y)):num|->num#num#'a) = (x,y) INSERT ch_set f`
    \\ ASM_SIMP_TAC std_ss [FINITE_INSERT]
    \\ FULL_SIMP_TAC bool_ss [ch_set_def,INSERT_THM,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ Cases_on `y` \\ Cases_on `r` \\ METIS_TAC [PAIR_EQ]]);

val cheney_alloc_gc_spec = store_thm("cheney_alloc_gc_spec",
  ``(cheney_alloc_gc (i,e,c,l,u,m) = (i',e',c',l',u',m')) ==>
    ch_inv (r,h,l) (i,e,c,l,u,m) /\ CARD (reachables r (ch_set h)) < l ==>
    i' < e' /\ ch_inv (r,h,l) (i',e',c',l',u',m')``,
  Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss [PAIR_EQ,cheney_alloc_gc_def] THEN1 METIS_TAC []
  \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [ch_inv_thm]
  \\ IMP_RES_TAC cheney_collector_spec \\ ASM_SIMP_TAC bool_ss []
  \\ `bijection f` by (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def])
  \\ `apply b (reachables r (ch_set h)) = apply f (basic_abs m')` by
   (REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ Q.PAT_X_ASSUM `apply f (reachables c (basic_abs m)) = basic_abs m'`
      (fn th => ASM_REWRITE_TAC [GSYM th,apply_apply,apply_I])
    \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
    \\ IMP_RES_TAC (Q.ISPECL [`r:num list`,`f:num->num`,`g:num->num`,`s:(num#num#num#'a)set`] apply_reachables)
    \\ IMP_RES_TAC MAP_INV \\ FULL_SIMP_TAC bool_ss []
    \\ REPEAT (Q.PAT_X_ASSUM `!hj.jk` (K ALL_TAC))
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
      REWRITE_TAC [reachables_def]
      \\ STRIP_TAC THEN1 (FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
      \\ FULL_SIMP_TAC bool_ss [reachables_def,IN_DEF,reachable_def] THEN1 METIS_TAC []
      \\ FULL_SIMP_TAC bool_ss [fix_MEM]
      \\ Q.EXISTS_TAC `r'` \\ ASM_REWRITE_TAC [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ Q.UNDISCH_TAC `PATH (r',p ++ [x]) (apply b (ch_set h))`
      \\ `reachables [r'] (apply b (ch_set h)) SUBSET basic_abs m` by
       (MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `reachables c (apply b (ch_set h))`
        \\ ASM_SIMP_TAC bool_ss []
        \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF]
        \\ Cases \\ Cases_on `r''` \\ Cases_on `r'''`
        \\ ASM_SIMP_TAC std_ss [reachables_def,MEM] \\ METIS_TAC [])
      \\ Q.UNDISCH_TAC `reachables [r'] (apply b (ch_set h)) SUBSET basic_abs m`
      \\ Q.SPEC_TAC (`r'`,`rr`) \\ Induct_on `p` THEN1
       (SIMP_TAC bool_ss [APPEND,PATH_def,EXPAND_SUBSET,reachables_def,MEM,IN_DEF]
        \\ METIS_TAC [reachable_def])
      \\ SIMP_TAC std_ss [APPEND,PATH_def] \\ REPEAT STRIP_TAC THENL [
        `reachables [h'] (apply b (ch_set h)) SUBSET reachables [rr] (apply b (ch_set h))` by
         (ASM_SIMP_TAC bool_ss [EXPAND_SUBSET,reachables_def,MEM,reachable_def,IN_DEF]
          \\ REPEAT STRIP_TAC \\ DISJ2_TAC THENL [
            Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [PATH_def,APPEND] \\ METIS_TAC [],
            Q.EXISTS_TAC `h'::p'` \\ ASM_SIMP_TAC bool_ss [PATH_def,APPEND] \\ METIS_TAC []])
        \\ METIS_TAC [SUBSET_TRANS],
        `reachables [rr] (apply b (ch_set h)) (rr,h',z',d')` by
          (FULL_SIMP_TAC std_ss [reachables_def,MEM,IN_DEF,reachable_def] \\ METIS_TAC [])
        \\ FULL_SIMP_TAC bool_ss [IN_DEF,SUBSET_DEF] \\ METIS_TAC [],
        `reachables [h'] (apply b (ch_set h)) SUBSET reachables [rr] (apply b (ch_set h))` by
         (ASM_SIMP_TAC bool_ss [EXPAND_SUBSET,reachables_def,MEM,reachable_def,IN_DEF]
          \\ REPEAT STRIP_TAC \\ DISJ2_TAC THENL [
            Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [PATH_def,APPEND] \\ METIS_TAC [],
            Q.EXISTS_TAC `h'::p'` \\ ASM_SIMP_TAC bool_ss [PATH_def,APPEND] \\ METIS_TAC []])
        \\ METIS_TAC [SUBSET_TRANS],
        `reachables [rr] (apply b (ch_set h)) (rr,z',h',d')` by
          (FULL_SIMP_TAC std_ss [reachables_def,MEM,IN_DEF,reachable_def] \\ METIS_TAC [])
        \\ FULL_SIMP_TAC bool_ss [IN_DEF,SUBSET_DEF] \\ METIS_TAC []],
      FULL_SIMP_TAC std_ss [reachables_def,SUBSET_DEF,IN_DEF]
      \\ FULL_SIMP_TAC bool_ss [fix_MEM]
      \\ Q.EXISTS_TAC `r'` \\ ASM_REWRITE_TAC []
      \\ FULL_SIMP_TAC std_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ Q.UNDISCH_TAC `PATH (r',p ++ [x]) (basic_abs m)`
      \\ Q.UNDISCH_TAC `!x. basic_abs m x ==> apply b (ch_set h) x`
      \\ Q.SPEC_TAC (`r'`,`rr`) \\ Induct_on `p`
      \\ SIMP_TAC bool_ss [PATH_def,APPEND,IN_DEF] \\ METIS_TAC []])
  \\ ALL_TAC THENL [
    `FINITE (reachables r (ch_set h))` by
     ((MATCH_MP_TAC o RW [AND_IMP_INTRO] o Q.GEN `s` o DISCH_ALL o
       SPEC_ALL o UNDISCH o SPEC_ALL) SUBSET_FINITE
      \\ Q.EXISTS_TAC `ch_set h` \\ FULL_SIMP_TAC bool_ss [ok_abs_def,FINITE_set]
      \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF]
      \\ Cases \\ Cases_on `r'` \\ Cases_on `r''`
      \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF])
    \\ `FINITE (basic_abs m')` by METIS_TAC [FINITE_basic_abs_CUT,WFS_IMP_CUT]
    \\ `CARD (basic_abs m') < l` by METIS_TAC [CARD_EQ_CARD_apply]
    \\ IMP_RES_TAC WFS_IMP_WFS_part \\ IMP_RES_TAC ok_state_CARD_EQ
    \\ `e' = (if u' then 1 + l else 1) + l` by METIS_TAC [ok_state_def]
    \\ Cases_on `u'` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC,
    `?k. (f o k = I) /\ (k o f = I) /\ bijection k` by METIS_TAC [bijection_inv]
    \\ `(k o f) 0 = 0` by (ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [])
    \\ Q.EXISTS_TAC `b o f` \\ ASM_SIMP_TAC std_ss [bijection_bijection,GSYM apply_apply]
    \\ REWRITE_TAC [GSYM rich_listTheory.MAP_MAP_o]
    \\ IMP_RES_TAC MAP_INV
    \\ IMP_RES_TAC (Q.ISPECL [`r:num list`,`f:num->num`,`g:num->num`,`s:(num#num#num#'a)set`] apply_reachables)
    \\ ASM_SIMP_TAC std_ss [reachables_reachables,apply_apply,apply_I,SUBSET_REFL]
    \\ `basic_abs m' = apply f (apply b (reachables r (ch_set h)))` by METIS_TAC [apply_switch]
    \\ Q.PAT_X_ASSUM `apply b (reachables r (ch_set h)) = apply f (basic_abs m')` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `apply f (reachables c (basic_abs m)) = basic_abs m'` (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss [GSYM apply_apply]
    \\ METIS_TAC [apply_SUBSET,reachables_SUBSET,SUBSET_REFL]]);

val PATH_INSERT = prove(
  ``(!y z d. ~((x:num,y:num,z:num,d:'a) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(x = y) ==>
    (PATH (y,p) ((x,y',z,d) INSERT s) = PATH (y,p) s)``,
  REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC PATH_SUBSET \\ Q.EXISTS_TAC `s` \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT])
  \\ Q.UNDISCH_TAC `PATH (y,p) ((x,y',z,d) INSERT s)`
  \\ Q.UNDISCH_TAC `~(x = y)` \\ Q.SPEC_TAC (`(y',z,d)`,`t`)
  \\ Cases \\ Cases_on `r` \\ Q.SPEC_TAC (`y`,`y`)
  \\ Induct_on `p` \\ SIMP_TAC std_ss [PATH_def,IN_INSERT,PAIR_EQ]
  \\ REPEAT STRIP_TAC \\ `~(x = h)` by METIS_TAC [] \\ RES_TAC \\ METIS_TAC []);

val reachable_INSERT = prove(
  ``(!y z d. ~((x,y,z,d) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(a = x) /\ ~(x = y) /\ ~(x = z) ==>
    (reachable x ((x:num,y:num,z:num,d:'a) INSERT s) a = reachable y s a \/ reachable z s a)``,
  ASM_SIMP_TAC bool_ss [reachable_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [PATH_def,APPEND,IN_INSERT] \\ METIS_TAC [],
    Q.EXISTS_TAC `y::p` \\ SIMP_TAC std_ss [PATH_def,APPEND,IN_INSERT]
    \\ REVERSE STRIP_TAC \\ METIS_TAC [PATH_INSERT],
    Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [PATH_def,APPEND,IN_INSERT] \\ METIS_TAC [],
    Q.EXISTS_TAC `z::p` \\ SIMP_TAC std_ss [PATH_def,APPEND,IN_INSERT]
    \\ REVERSE STRIP_TAC \\ METIS_TAC [PATH_INSERT],
    Cases_on `p` \\ FULL_SIMP_TAC std_ss [APPEND,PATH_def,IN_INSERT] THEN1 METIS_TAC []
    \\ METIS_TAC [PATH_INSERT]]);

val reachables_INSERT = prove(
  ``!ts x y z d s.
      (!y z d. ~((x,y,z,d) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(x = y) /\ ~(x = z) ==>
      (reachables (x::ts) ((x:num,y:num,z:num,d:'a) INSERT s) = (x,y,z,d) INSERT reachables (y::z::ts) s)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !a b c e. f (a,b,c,e) = g (a,b,c,e)``]
  \\ SIMP_TAC std_ss [reachables_def,IN_DEF,INSERT_THM]
  \\ REWRITE_TAC [fix_MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] THENL [
    REVERSE (Cases_on `r = x`) \\ FULL_SIMP_TAC bool_ss [GSYM INSERT_THM] THENL [
      FULL_SIMP_TAC bool_ss [MEM] \\ DISJ2_TAC \\ Q.EXISTS_TAC `r`
      \\ FULL_SIMP_TAC bool_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ METIS_TAC [SIMP_RULE std_ss [IN_DEF] PATH_INSERT],
      `reachable y s a \/ reachable z s a` by METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT]
      \\ METIS_TAC [MEM]],
    Q.EXISTS_TAC `a` \\ SIMP_TAC bool_ss [reachable_def,MEM],
    FULL_SIMP_TAC bool_ss [MEM,GSYM INSERT_THM]
    THEN1 METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT,MEM]
    THEN1 METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT,MEM]
    \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC bool_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
    \\ MATCH_MP_TAC PATH_SUBSET \\ Q.EXISTS_TAC `s`
    \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT]]);

val reachables_DUP = prove(
  ``!x y ys s. reachables (x::y::y::ys) s = reachables (x::y::ys) s``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !a b c e. f (a,b,c,e) = g (a,b,c,e)``]
  \\ SIMP_TAC std_ss [reachables_def,IN_DEF,INSERT_THM,MEM] \\ METIS_TAC []);

val apply_swap_ID = prove(
  ``(!y z d. ~(s(i,y,z,d)) /\ ~(s(z,i,y,d)) /\ ~(s(y,z,i,d)) /\
             ~(s(j,y,z,d)) /\ ~(s(z,j,y,d)) /\ ~(s(y,z,j,d))) ==>
    (apply (swap i j) s = s)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ SIMP_TAC std_ss [apply_def,IN_DEF,swap_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `x = i` \\ Cases_on `y = i` \\ Cases_on `z = i` \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `x = j` \\ Cases_on `y = j` \\ Cases_on `z = j` \\ ASM_SIMP_TAC bool_ss []);

val ok_state_IMP_bounds = prove(
  ``ok_state (i,e,c,l,u,m) /\ (m k = DATA(x,y,d)) ==> (x < i \/ (x = 0)) /\ (y < i \/ (y = 0))``,
  FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
  \\ FULL_SIMP_TAC std_ss [IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on ` RANGE (if u then 1 + l else 1,i) k` \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [heap_type_11,heap_type_distinct,PAIR_EQ,RANGE_def] \\ METIS_TAC []);

val MAP_ID =prove(
  ``!xs. (!k. MEM k xs ==> (f k = k)) ==> (MAP f xs = xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [MAP,MEM,CONS_11] \\ METIS_TAC []);

val RANGE_BORDER = prove(``~RANGE(i,j)j``,REWRITE_TAC [RANGE_def] \\ DECIDE_TAC);

val cheney_alloc_lemma = prove(
  ``!i e t l u m x y z d k.
    ok_state (i,e,t,l,u,m) /\ basic_abs m (x,y,z,d) /\ (!a b c. ~basic_abs m (k,a,b,c)) /\ ~(k = 0) ==>
    ~(i = x) /\ ~(i = y) /\ ~(i = z) /\ ~(k = x) /\ ~(k = y) /\ ~(k = z)``,
  SIMP_TAC bool_ss [ok_state_def,LET_DEF,basic_abs,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ SIMP_TAC bool_ss [IN_DEF] \\ NTAC 12 STRIP_TAC
  \\ `~(i = 0)` by (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
  \\ `RANGE (if u then 1+l else 1,i) x` by METIS_TAC [heap_type_distinct]
  \\ RES_TAC \\ FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ]
  \\ METIS_TAC [RANGE_BORDER,heap_type_distinct]);

val set_FUPDATE = prove(
  ``!h x y d. ch_set (h |+ (fresh h,x,y,d)) = (fresh h,x,y,d) INSERT ch_set h``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !a b c e. f (a,b,c,e) = g (a,b,c,e)``]
  \\ SIMP_TAC std_ss [ch_set_def,INSERT_THM,FDOM_FUPDATE,IN_DEF,FAPPLY_FUPDATE_THM]
  \\ METIS_TAC [PAIR_EQ,SIMP_RULE std_ss [IN_DEF,INSERT_THM] fresh_NOT_IN_FDOM]);

val ok_state_LESS = prove(
  ``!t v i e r l u m d.
      ok_state (i,e,t::v::r,l,u,m) /\ i < e ==>
      ok_state (i + 1,e,i::v::r,l,u,(i =+ DATA (t,v,d)) m)``,
  SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [fix_MEM]
  THEN1 (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC)
  THEN1 (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC) THENL [
    Cases_on `k = i` THEN1 (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
    \\ `RANGE ((if u then 1 + l else 1),i) k ==> RANGE ((if u then 1 + l else 1),i + 1) k` by
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC bool_ss [MEM] \\ METIS_TAC [],
    `~RANGE ((if u then 1 + l else 1),i) k` by
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
    \\ Cases_on `i = k` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
    \\ Q.ABBREV_TAC `nn = if u then 1 + l else 1`
    \\ `RANGE (nn,k + 1) k` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC) \\ METIS_TAC [],
    Cases_on `i = k` \\ FULL_SIMP_TAC bool_ss
      [UPDATE_def,heap_type_11,PAIR_EQ,SUBSET0_DEF,SUBSET_DEF,INSERT_THM,IN_DEF,EMPTY_DEF,MEM]
    \\ `!k. RANGE ((if u then 1 + l else 1),i) k ==> RANGE ((if u then 1 + l else 1),i + 1) k` by
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC) THEN1 METIS_TAC []
    \\ `RANGE ((if u then 1 + l else 1),i) k` by
         (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
    \\ RES_TAC \\ METIS_TAC []]);

val cheney_alloc_ok = store_thm("cheney_alloc_ok",
  ``!i e t v r l u m d.
        ok_state (i,e,t::v::r,l,u,m) ==> ok_state (cheney_alloc (i,e,t::v::r,l,u,m) (d:'a))``,
  REWRITE_TAC [cheney_alloc_def,cheney_alloc_gc_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss [cheney_alloc_aux_def] THEN1
    (ASM_SIMP_TAC std_ss [LET_DEF,DECIDE ``n<m ==> ~(n=m:num)``,HD,TL]  \\ METIS_TAC [ok_state_LESS])
  \\ `?i2 e2 root2 l2 u2 m2. cheney_collector (i,e,t::v::r,l,u,m) = (i2,e2,root2,l2,u2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC bool_ss [cheney_alloc_aux_def]
  \\ IMP_RES_TAC cheney_collector_spec
  \\ Cases_on `i2 = e2` \\ ASM_SIMP_TAC std_ss [LET_DEF] THEN1
   (Q.PAT_X_ASSUM `ok_state (i2,e2,root2,l2,u2,m2)` MP_TAC
    \\ Cases_on `root2`
    \\ FULL_SIMP_TAC std_ss [MAP,NOT_CONS_NIL,TL]
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [ok_state_def,LET_DEF]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [MEM]
    \\ METIS_TAC [])
  \\ `FST (SND (SND (cheney_collector (i,e,t::v::r,l,u,m)))) = root2` by METIS_TAC [PAIR_EQ,PAIR]
  \\ Q.PAT_X_ASSUM `FST (SND xx) = yy` (ASSUME_TAC o RW [FST,SND] o
       CONV_RULE (DEPTH_CONV FORCE_PBETA_CONV) o
       SIMP_RULE std_ss [LET_DEF,move_roots_def,cheney_collector_def])
  \\ Cases_on `root2` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11]
  \\ FULL_SIMP_TAC std_ss [HD,TL] \\ MATCH_MP_TAC ok_state_LESS \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `u2` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC);

val cheney_alloc_spec = store_thm("cheney_alloc_spec",
  ``(cheney_alloc s (d:'a) = s') ==>
    ch_inv (t1::t2::ts,h,l) s /\ CARD (reachables (t1::t2::ts) (ch_set h)) < l ==>
    ch_inv (fresh h::t2::ts, h |+ (fresh h,t1,t2,d),l) s'``,
  `?i e root a l u m. s = (i,e,root,l,u,m)` by METIS_TAC [PAIR]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss []
  \\ STRIP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ ASM_SIMP_TAC bool_ss [cheney_alloc_def]
  \\ Cases_on `~(l' = l)` THEN1 METIS_TAC [ch_inv_def]
  \\ FULL_SIMP_TAC bool_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ `?i' e' c' l' u' m'. (cheney_alloc_gc (i,e,root,l,u,m) = (i',e',c',l',u',m'))` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,cheney_alloc_aux_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC cheney_alloc_gc_spec
  \\ FULL_SIMP_TAC std_ss [ch_inv_thm,ok_abs_def,FINITE_INSERT,DECIDE ``i<e==>~(i=e:num)``]
  \\ STRIP_TAC THEN1
   (Cases_on `c'` \\ FULL_SIMP_TAC bool_ss [MAP,NOT_CONS_NIL,TL,MEM]
    \\ Cases_on `t` \\ FULL_SIMP_TAC bool_ss [MAP,NOT_CONS_NIL,TL,MEM,CONS_11,HD,TL]
    \\ METIS_TAC [ok_state_LESS])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC bool_ss [IN_INSERT,FDOM_FUPDATE,fresh_NOT_IN_FDOM,MEM,FEVERY_FUPDATE,PAIR_EQ]
    \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
    \\ SIMP_TAC std_ss [fresh_NOT_IN_FDOM,NOT_FDOM_DRESTRICT] \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_DEF,INSERT_THM,EMPTY_DEF] \\ METIS_TAC [])
    \\ MATCH_MP_TAC (METIS_PROVE [FEVERY_DEF] ``!P Q h. (!x. P x ==> Q x) /\ FEVERY P h ==> FEVERY Q h``)
    \\ Q.EXISTS_TAC `(\(x,y,z,d). {y; z} SUBSET0 FDOM h)` \\ ASM_SIMP_TAC bool_ss []
    \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
    \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_DEF,INSERT_THM,EMPTY_DEF] \\ METIS_TAC [])
  \\ `?k. (b' o k = I) /\ (k o b' = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ Q.EXISTS_TAC `b' o swap i' (k (fresh h))`
  \\ ASM_SIMP_TAC std_ss [GSYM apply_apply,bijection_bijection,bijection_swap]
  \\ `!x. b' (k x) = x` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ ASM_SIMP_TAC bool_ss [METIS_PROVE [swap_def] ``!i k. swap i k i = k``]
  \\ Cases_on `c'` \\ FULL_SIMP_TAC bool_ss [MAP,NOT_CONS_NIL,TL,MEM,HD,CONS_11]
  \\ IMP_RES_TAC fresh_THM
  \\ Cases_on `k (fresh h) = 0` THEN1 METIS_TAC []
  \\ `~(i' = 0)` by (Cases_on `u'` \\
       FULL_SIMP_TAC bool_ss [RANGE_def,ok_state_def,IN_DEF,LET_DEF] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1  ASM_SIMP_TAC std_ss [swap_def]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC,GSYM rich_listTheory.MAP_MAP_o]
  \\ STRIP_TAC THEN1 ASM_SIMP_TAC std_ss [swap_def]
  \\ `(MAP b' (MAP (swap i' (k (fresh h))) t) = t2::ts)` by
   (Q.PAT_X_ASSUM `MAP b' t = t2::ts` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC bool_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
    \\ MATCH_MP_TAC MAP_ID
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF,RANGE_def,MEM]
    \\ Cases_on `k' = 0` \\ ASM_SIMP_TAC std_ss [swap_def]
    \\ `~(k' = i')` by METIS_TAC [DECIDE ``m<n:num ==> ~(m=n)``]
    \\ Cases_on `k' = k (fresh h)` \\ ASM_SIMP_TAC bool_ss []
    \\ `?x y d. (m' k' = DATA (x,y,d))` by METIS_TAC []
    \\ `basic_abs m' (k (fresh h),x,y,d)` by (SIMP_TAC bool_ss [basic_abs] \\ METIS_TAC [])
    \\ `apply b' (ch_set h) (k (fresh h),x,y,d)` by (FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [apply_def,IN_DEF,FUN_EQ_THM,ch_set_def]
    \\ METIS_TAC [SIMP_RULE std_ss [IN_DEF] fresh_NOT_IN_FDOM])
  \\ ASM_SIMP_TAC bool_ss []
  \\ `m' i' = EMP` by
    (FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF,RANGE_def,IN_DEF]
    \\ METIS_TAC [DECIDE ``~(n<n:num)``])
  \\`(basic_abs ((i' =+ DATA (h',HD t,d)) m') = (i',h',HD t,d) INSERT basic_abs m') /\
     !x y z. ~((i',x,y,z) IN basic_abs m')` by
   (REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ ASM_SIMP_TAC std_ss [INSERT_THM,basic_abs,IN_DEF,UPDATE_def,heap_type_distinct]
    \\ REPEAT STRIP_TAC \\ Cases_on `x = i'`
    \\ FULL_SIMP_TAC std_ss [heap_type_distinct,heap_type_11])
  \\ REWRITE_TAC [set_FUPDATE]
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.ABBREV_TAC `mm = basic_abs m'`
  \\ Q.ABBREV_TAC `f = fresh h`
  \\ `reachables (f::t2::ts) ((f,t1,t2,d) INSERT ch_set h) =
      (f,t1,t2,d) INSERT reachables (t1::t2::ts) (ch_set h)` by
   (MATCH_MP_TAC (RW [reachables_DUP] (Q.SPECL [`z::ys`,`x`,`y`,`z`] reachables_INSERT))
    \\ METIS_TAC [fresh_NOT_IN_FDOM])
  \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `t` \\ FULL_SIMP_TAC bool_ss [MAP,NOT_CONS_NIL,TL,MEM,HD,CONS_11]
  \\ `reachables (i'::h''::t') ((i',h',h'',d) INSERT mm) =
      (i',h',h'',d) INSERT reachables (h'::h''::t') mm` by
   (MATCH_MP_TAC (RW [reachables_DUP] (Q.SPECL [`z::ys`,`x`,`y`,`z`] reachables_INSERT))
    \\ Q.UNABBREV_TAC `mm`
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,basic_abs,ok_state_def,LET_DEF]
    \\ `~((if u' then 1 + l' else 1) <= 0)` by (Cases_on `u'` \\ REWRITE_TAC [] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC THENL [
      Cases_on `RANGE (if u' then 1+l' else 1,i') z` \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [RANGE_def,IN_DEF] \\ METIS_TAC [DECIDE ``~(i<i:num)``],
      Cases_on `RANGE (if u' then 1+l' else 1,i') y` \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [RANGE_def,IN_DEF] \\ METIS_TAC [DECIDE ``~(i<i:num)``],
      `~(b' h' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
      \\ FULL_SIMP_TAC bool_ss [fix_MEM, MEM]
      \\ METIS_TAC [RANGE_BORDER],
      `~(b' h'' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
      \\ FULL_SIMP_TAC bool_ss [MEM, fix_MEM] \\ METIS_TAC [RANGE_BORDER]])
  \\ ASM_SIMP_TAC bool_ss []
  \\ `(k 0 = 0)` by (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC [])
  \\ Q.UNABBREV_TAC `f`
  \\ `swap i' (k (fresh h)) o swap i' (k (fresh h)) = I` by METIS_TAC [swap_swap]
  \\ (ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`k`,`b'`]) apply_INSERT
  \\ (ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`swap i' (k (fresh h))`,`swap i' (k (fresh h))`]) apply_INSERT
  \\ ASM_SIMP_TAC std_ss []
  \\ `swap i' (k (fresh h)) (k (fresh h)) = i'` by SIMP_TAC bool_ss [swap_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ `(k t1 = h') /\ (k t2 = h'')` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ `~(i' = h') /\ ~(i' = h'')` by
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [IN_DEF,basic_abs,ok_state_def,LET_DEF,MEM]
    \\ METIS_TAC [RANGE_BORDER])
  \\ `~(k (fresh h) = h')` by
    (STRIP_TAC \\ `fresh h = t1` by METIS_TAC [bijection_def,ONE_ONE_DEF] \\ METIS_TAC [fresh_NOT_IN_FDOM])
  \\ `~(k (fresh h) = h'')` by
    (STRIP_TAC \\ `fresh h = t2` by METIS_TAC [bijection_def,ONE_ONE_DEF] \\ METIS_TAC [fresh_NOT_IN_FDOM])
  \\ `swap i' (k (fresh h)) h' = h'` by FULL_SIMP_TAC bool_ss [swap_def]
  \\ `swap i' (k (fresh h)) h'' = h''` by FULL_SIMP_TAC bool_ss [swap_def]
  \\ ASM_SIMP_TAC bool_ss []
  \\ SIMP_TAC std_ss [EXPAND_SUBSET,INSERT_THM] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Q.UNABBREV_TAC `mm` \\ DISJ2_TAC THEN1
   (ONCE_REWRITE_TAC [apply_def]
    \\ FULL_SIMP_TAC bool_ss [basic_abs,ok_state_def,LET_DEF]
    \\ `~(i' = x)` by (REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [IN_DEF,basic_abs,LET_DEF,MEM]
      \\ METIS_TAC [RANGE_BORDER])
    \\ `x IN RANGE (if u' then 1+l' else 1,i')` by METIS_TAC [heap_type_distinct]
    \\ `?x' y d. (m' x = DATA (x',y,d)) /\ {x'; y} SUBSET0 RANGE (if u' then 1+l' else 1,i')` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC std_ss [IN_DEF] \\ `~(y = i') /\ ~(z = i')` by METIS_TAC [RANGE_BORDER]
    \\ `~(x = k (fresh h)) /\ ~(y = k (fresh h)) /\ ~(z = k (fresh h))` suffices_by
    (STRIP_TAC THEN ASM_SIMP_TAC std_ss [swap_def] \\ METIS_TAC [basic_abs])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss []
    \\ `RANGE (if u' then 1+l' else 1,i') (k (fresh h))` by METIS_TAC []
    \\ `?j1 j2 j3. basic_abs m' (k (fresh h),j1,j2,j3)` by METIS_TAC [basic_abs]
    \\ `apply b' (ch_set h) (k (fresh h),j1,j2,j3)` by METIS_TAC []
    \\ FULL_SIMP_TAC bool_ss [apply_def,IN_DEF] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `xxx SUBSET basic_abs m'`
       (fn th => MATCH_MP_TAC (RW [EXPAND_SUBSET] th) \\ ASSUME_TAC th)
  \\ Q.ABBREV_TAC `xxx = apply b' (reachables (t1::t2::ts) (ch_set h))`
  \\ Q.PAT_X_ASSUM `apply (swap i' (k (fresh h))) xxx (x,y,z,d')`
       (ASSUME_TAC o SIMP_RULE std_ss [apply_def,IN_DEF])
  \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ `basic_abs m' (swap i' (k (fresh h)) x,swap i' (k (fresh h)) y,
              swap i' (k (fresh h)) z,d')` by METIS_TAC []
  \\ Q.ABBREV_TAC `ff = (fresh h)`
  \\ `(!a5 b5 c5. ~basic_abs m' (k ff,a5,b5,c5))` by
   (REPEAT STRIP_TAC \\ `apply b' (ch_set h) (k ff,a5,b5,c5)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,apply_def] \\ METIS_TAC [apply_def])
  \\ Q.ABBREV_TAC `sx = swap i' (k ff) x`
  \\ Q.ABBREV_TAC `sy = swap i' (k ff) y`
  \\ Q.ABBREV_TAC `sz = swap i' (k ff) z`
  \\ `~(i' = sx) /\ ~(i' = sy) /\ ~(i' = sz) /\ ~(k ff = sx) /\ ~(k ff = sy) /\ ~(k ff = sz)` by
    (MATCH_MP_TAC cheney_alloc_lemma \\ Q.EXISTS_TAC `e'`
     \\ Q.EXISTS_TAC `h'::h''::t'` \\ Q.EXISTS_TAC `l'` \\ Q.EXISTS_TAC `u'`
     \\ Q.EXISTS_TAC `m'` \\ Q.EXISTS_TAC `d'` \\ ASM_SIMP_TAC bool_ss [])
  \\ Q.UNABBREV_TAC `sx` \\ Q.UNABBREV_TAC `sy` \\ Q.UNABBREV_TAC `sz`
  \\ FULL_SIMP_TAC bool_ss [swap_def]
  \\ Cases_on `x = i'` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `y = i'` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `z = i'` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `x = k ff` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `y = k ff` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `z = k ff` \\ FULL_SIMP_TAC bool_ss []
  \\ METIS_TAC []);

val cheney_init = store_thm("cheney_init",
  ``!xs l. ch_inv (MAP (\x.0) xs,FEMPTY,l) (1,1+l,MAP (\x.0) (xs:num list),l,F,\x.EMP)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_state_def,ok_abs_def,FEVERY_FEMPTY,FDOM_FEMPTY,
    LESS_EQ_REFL,LET_DEF,FINITE_EMPTY,MEM_MAP,heap_type_distinct,NOT_IN_EMPTY,
    RANGE_lemmas,DECIDE ``1<=1+l:num``]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (Q.EXISTS_TAC `I` \\ SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o,apply_I,
     bijection_def,ONTO_DEF,EXPAND_SUBSET,reachables_def,EMPTY_DEF,IN_DEF,
     basic_abs,heap_type_distinct,ONE_ONE_DEF,ch_set_def,FDOM_FEMPTY])
  \\ METIS_TAC []);

(* add to library? *)

val MEM_TAKE = prove(
  ``!xs n x. MEM x (TAKE n xs) ==> MEM x xs``,
  Induct THEN REWRITE_TAC [TAKE_def] THEN METIS_TAC [MEM]);

val MEM_DROP = prove(
  ``!xs n x. MEM x (DROP n xs) ==> MEM x xs``,
  Induct THEN REWRITE_TAC [DROP_def] THEN METIS_TAC [MEM]);

val MAP_DROP = prove(
  ``!xs f n. MAP f (DROP n xs) = DROP n (MAP f xs)``,
  Induct THEN REWRITE_TAC [DROP_def,MAP,CONS_11] THEN METIS_TAC [MAP]);

val MAP_TAKE = prove(
  ``!xs f n. MAP f (TAKE n xs) = TAKE n (MAP f xs)``,
  Induct THEN REWRITE_TAC [TAKE_def,MAP,CONS_11] THEN METIS_TAC [MAP]);

(* /add *)

val LIST_DELETE_def = Define `
  LIST_DELETE n xs = TAKE n xs ++ DROP (SUC n) xs`;

val LIST_INSERT_def = Define `
  LIST_INSERT y n xs = TAKE n xs ++ [y] ++ DROP n xs`;

val LIST_UPDATE_def = Define `
  LIST_UPDATE n y xs = LIST_DELETE n (LIST_INSERT y (SUC n) xs)`;

val MEM_LIST_DELETE = prove(
  ``!xs n x. MEM x (LIST_DELETE n xs) ==> MEM x xs``,
  METIS_TAC [LIST_DELETE_def,MEM_APPEND,MEM_DROP,MEM_TAKE]);

val MEM_LIST_INSERT = prove(
  ``!xs n x. MEM x (LIST_INSERT y n xs) ==> MEM x (y::xs)``,
  METIS_TAC [LIST_INSERT_def,MEM_APPEND,MEM,MEM_DROP,MEM_TAKE]);

val MAP_LIST_DELETE = prove(
  ``!xs n f. MAP f (LIST_DELETE n xs) = LIST_DELETE n (MAP f xs)``,
  REWRITE_TAC [LIST_DELETE_def,MAP_DROP,MAP_TAKE,MAP_APPEND]);

val MAP_LIST_INSERT = prove(
  ``!xs n f. MAP f (LIST_INSERT y n xs) = LIST_INSERT (f y) n (MAP f xs)``,
  REWRITE_TAC [LIST_INSERT_def,MAP_DROP,MAP_TAKE,MAP_APPEND,MAP]);

val cheney_DELETE = prove(
  ``!n xs ys. ch_inv (xs,h,l) (i,e,ys,l,u,m) ==>
              ch_inv (LIST_DELETE n xs,h,l) (i,e,LIST_DELETE n ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] \\ IMP_RES_TAC MEM_LIST_DELETE
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC bool_ss [MAP_LIST_DELETE]
  \\ MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `apply b (reachables xs (ch_set h))`
  \\ ASM_SIMP_TAC bool_ss [] \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ FULL_SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MAP]
  \\ FULL_SIMP_TAC bool_ss [fix_MEM]
  \\ METIS_TAC [MEM_LIST_DELETE]);

val cheney_INSERT = prove(
  ``!n x xs y ys. ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==>
                  ch_inv (LIST_INSERT x n xs,h,l) (i,e,LIST_INSERT y n ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] \\ IMP_RES_TAC MEM_LIST_INSERT
  THEN1 METIS_TAC [MEM] THEN1 METIS_TAC [MEM]
  \\ Q.EXISTS_TAC `b` \\ FULL_SIMP_TAC bool_ss [MAP_LIST_INSERT,MAP,CONS_11]
  \\ MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `apply b (reachables (x::xs) (ch_set h))`
  \\ ASM_SIMP_TAC bool_ss [] \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ FULL_SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MAP]
  \\ FULL_SIMP_TAC bool_ss [fix_MEM]
  \\ METIS_TAC [MEM_LIST_INSERT,MEM]);

val cheney_UPDATE = prove(
  ``!n x xs y ys. ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==>
                  ch_inv (LIST_UPDATE n x xs,h,l) (i,e,LIST_UPDATE n y ys,l,u,m)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [LIST_UPDATE_def]
  \\ MATCH_MP_TAC cheney_DELETE \\ MATCH_MP_TAC cheney_INSERT \\ ASM_REWRITE_TAC []);

val cheney_0 = store_thm("cheney_0",
  ``!xs ys n h l i e u m.
      ch_inv (xs,h,l) (i,e,ys,l,u,m) ==>
      ch_inv (LIST_UPDATE n 0 xs,h,l) (i,e,LIST_UPDATE n 0 ys,l,u,m)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC cheney_UPDATE
  \\ FULL_SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC bool_ss [MAP]
  \\ MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `apply b (reachables xs (ch_set h))`
  \\ ASM_SIMP_TAC bool_ss [] \\ MATCH_MP_TAC apply_SUBSET
  \\ SIMP_TAC std_ss [reachables_def,EXPAND_SUBSET,MEM] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC []
  \\ Q.UNDISCH_TAC `x IN reachable r (ch_set h)` \\ ASM_SIMP_TAC std_ss [reachable_def,IN_DEF]
  \\ REPEAT STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [IN_DEF,ch_set_def]
  \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,ch_set_def] \\ METIS_TAC []);

val MAP_MEM_ZIP = prove(
  ``!xs ys b x y. (MAP b ys = xs) /\ MEM (x,y) (ZIP (xs,ys)) ==> MEM x xs /\ MEM y ys /\ (b y = x)``,
  Induct THENL [ALL_TAC,STRIP_TAC]
  \\ Cases \\ REWRITE_TAC [MAP,MEM,ZIP,NOT_CONS_NIL,NOT_NIL_CONS,CONS_11]
  \\ METIS_TAC [PAIR_EQ]);

val reachable_expand = prove(
  ``!x y s t. reachable y s t /\ (?z d. s (x,y,z,d) \/  s (x,z,y,d)) ==> reachable x s t``,
  SIMP_TAC bool_ss [reachable_def] \\ REPEAT STRIP_TAC \\ DISJ2_TAC
  THENL [Q.EXISTS_TAC `[]`,Q.EXISTS_TAC `[]`,Q.EXISTS_TAC `y::p`,Q.EXISTS_TAC `y::p`]
  \\ ASM_SIMP_TAC std_ss [PATH_def,APPEND,IN_DEF] \\ METIS_TAC []);

val cheney_move = store_thm("cheney_move",
  ``!xs ys x y h l i e u m.
      ch_inv (xs,h,l) (i,e,ys,l,u,m) /\ MEM (x,y) (ZIP (xs,ys)) ==>
      ch_inv (LIST_UPDATE n x xs,h,l) (i,e,LIST_UPDATE n y ys,l,u,m)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC cheney_UPDATE
  \\ FULL_SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]
  \\ IMP_RES_TAC MAP_MEM_ZIP \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC std_ss []
  \\ sg `reachables (x::xs) (ch_set h) = reachables xs (ch_set h)`
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [PAIR] ``(!x y z q. f (x,y,z,q) = g (x,y,z,q)) ==> (f = g)``)
  \\ SIMP_TAC bool_ss [reachables_def,MEM] \\ METIS_TAC []);

val CONS_LIST_UPDATE = prove(
  ``!n x y xs. x::LIST_UPDATE n y xs = LIST_UPDATE (SUC n) y (x::xs)``,
  REWRITE_TAC [LIST_UPDATE_def,LIST_DELETE_def,LIST_INSERT_def,rich_listTheory.BUTFIRSTN,
    rich_listTheory.FIRSTN,APPEND]);

val cheney_move2 = store_thm("cheney_move2",
  ``!xs ys x1 y1 n1 x2 y2 n2 h l i e u m.
      ch_inv (xs,h,l) (i,e,ys,l,u,m) /\ MEM (x1,y1) (ZIP (xs,ys)) /\ MEM (x2,y2) (ZIP (xs,ys)) ==>
      ch_inv (LIST_UPDATE n1 x1 (LIST_UPDATE n2 x2 xs),h,l)
             (i,e,LIST_UPDATE n1 y1 (LIST_UPDATE n2 y2 ys),l,u,m)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC cheney_UPDATE
  \\ REWRITE_TAC [CONS_LIST_UPDATE] \\ MATCH_MP_TAC cheney_UPDATE
  \\ FULL_SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]
  \\ IMP_RES_TAC MAP_MEM_ZIP \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC []
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC std_ss []
  \\ sg `reachables (x2::x1::xs) (ch_set h) = reachables xs (ch_set h)`
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [PAIR] ``(!x y z q. f (x,y,z,q) = g (x,y,z,q)) ==> (f = g)``)
  \\ SIMP_TAC bool_ss [reachables_def,MEM] \\ METIS_TAC []);

val cheney_car_cdr = store_thm("cheney_car_cdr",
  ``!xs ys x y h l i e u m.
      ch_inv (xs,h,l) (i,e,ys,l,u,m) /\ MEM (x,y) (ZIP (xs,ys)) /\ ~(y = 0) ==>
      ch_inv (LIST_UPDATE n (FST (h ' x)) xs,h,l) (i,e,LIST_UPDATE n (FST (getDATA (m y))) ys,l,u,m) /\
      ch_inv (LIST_UPDATE n (FST (SND (h ' x))) xs,h,l) (i,e,LIST_UPDATE n (FST (SND (getDATA (m y)))) ys,l,u,m)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC cheney_UPDATE
  \\ FULL_SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]
  \\ IMP_RES_TAC MAP_MEM_ZIP
  \\ `y IN RANGE ((if u then 1 + l else 1),i)` by METIS_TAC []
  \\ `?x3 y3 d. (m y = DATA (x3,y3,d)) /\ {x3; y3} SUBSET0 RANGE ((if u then 1 + l else 1),i)`
       by METIS_TAC []
  \\ Q.PAT_X_ASSUM `!k. ppp ==> ?x. bbb` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [getDATA_def,FST,SND,FEVERY_DEF]
  \\ (STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC []))
  \\ `~(x = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ `(\(x,y,z,d). {y; z} SUBSET0 FDOM h) (x,h ' x)` by METIS_TAC []
  \\ `?a1 b1 c1. h ' x = (a1,b1,c1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ (STRIP_TAC THEN1 METIS_TAC [])
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ `basic_abs m (y,x3,y3,d)` by FULL_SIMP_TAC bool_ss [basic_abs]
  \\ `apply b (ch_set h) (y,x3,y3,d)` by METIS_TAC []
  \\ Q.PAT_X_ASSUM `b y = x` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [apply_def,ch_set_def,IN_DEF]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM ` !x. apply b (reachables xs (ch_set h)) x ==> basic_abs m x` MATCH_MP_TAC
  \\ Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'`
  \\ (REVERSE (FULL_SIMP_TAC std_ss [apply_def,IN_DEF,reachables_def,MEM]) THEN1 METIS_TAC [])
  \\ Q.EXISTS_TAC `x` \\ ASM_SIMP_TAC bool_ss []
  \\ MATCH_MP_TAC reachable_expand
  \\ Q.EXISTS_TAC `r'` \\ ASM_SIMP_TAC bool_ss [ch_set_def,IN_DEF,PAIR_EQ] \\ METIS_TAC []);

val cheney_data = store_thm("cheney_data",
  ``ch_inv (xs,h,l) (i,e,ys,l,u,m) /\ MEM (x,y) (ZIP (xs,ys)) /\ ~(y = 0) ==>
    (SND (SND (h ' x)) = SND (SND (getDATA (m y))))``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]
  \\ IMP_RES_TAC MAP_MEM_ZIP
  \\ `y IN RANGE ((if u then 1 + l else 1),i)` by METIS_TAC []
  \\ `?x3 y3 d. (m y = DATA (x3,y3,d)) /\ {x3; y3} SUBSET0 RANGE ((if u then 1 + l else 1),i)`
       by METIS_TAC []
  \\ Q.PAT_X_ASSUM `!k. ppp ==> ?x. bbb` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [getDATA_def,FST,SND,FEVERY_DEF]
  \\ `~(x = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ `(\(x,y,z,d). {y; z} SUBSET0 FDOM h) (x,h ' x)` by METIS_TAC []
  \\ `?a1 b1 c1. h ' x = (a1,b1,c1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ `basic_abs m (y,x3,y3,d)` by FULL_SIMP_TAC bool_ss [basic_abs]
  \\ `apply b (ch_set h) (y,x3,y3,d)` by METIS_TAC []
  \\ Q.PAT_X_ASSUM `b y = x` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [apply_def,ch_set_def,IN_DEF]);

val ch_set_FUPDATE = prove(
  ``ch_set (h |+ (fresh h,v1,v2,x)) = (fresh h,v1,v2,x) INSERT ch_set h``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``(f = g) = !a x y d. f (a,x,y,d) = g (a,x,y,d)``]
  \\ SIMP_TAC std_ss [ch_set_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ SIMP_TAC bool_ss [SIMP_RULE std_ss [IN_DEF] IN_INSERT,PAIR_EQ,ch_set_def]
  \\ METIS_TAC [PAIR_EQ,fresh_NOT_IN_FDOM]);

val FINITE_ch_set = store_thm("FINITE_ch_set",
  ``!h:num|->num#num#'a. FINITE (ch_set h)``,
  CONV_TAC (QUANT_CONV (UNBETA_CONV ``h:num|->num#num#'a``))
  \\ MATCH_MP_TAC fmap_INDUCT \\ SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC THENL [
    sg `ch_set (FEMPTY:num|->num#num#'a) = {}`
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY]
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY,ch_set_def,EMPTY_DEF,FDOM_FEMPTY,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``],
    sg `ch_set ((f |+ (x,y)):num|->num#num#'a) = (x,y) INSERT ch_set f`
    \\ ASM_SIMP_TAC std_ss [FINITE_INSERT]
    \\ FULL_SIMP_TAC bool_ss [ch_set_def,INSERT_THM,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ Cases_on `y` \\ Cases_on `r` \\ METIS_TAC [PAIR_EQ]]);

val FINITE_reachables = store_thm("FINITE_reachables",
  ``!r h:num|->num#num#'a. FINITE (reachables r (ch_set h))``,
  REPEAT STRIP_TAC
  \\ (MATCH_MP_TAC o RW [AND_IMP_INTRO] o Q.GEN `s` o DISCH_ALL o
      SPEC_ALL o UNDISCH o SPEC_ALL) SUBSET_FINITE
  \\ Q.EXISTS_TAC `ch_set h` \\ FULL_SIMP_TAC bool_ss [ok_abs_def,FINITE_ch_set]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,FINITE_ch_set]
  \\ Cases \\ Cases_on `r'` \\ Cases_on `r''`
  \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF]);

val reachables_EQ_EMPTY = store_thm("reachables_EQ_EMPTY",
  ``!x h. ~(x IN FDOM h) ==> (reachables [x] (ch_set h) = {})``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``(f = g) = (!a x y d. f (a,x,y,d) = g (a,x,y,d))``]
  \\ SIMP_TAC bool_ss [reachables_def,MEM,IN_DEF,EMPTY_DEF,ch_set_def,reachable_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `a = x` \\ ASM_SIMP_TAC bool_ss []
  \\ DISJ2_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `p` \\ REPEAT (FULL_SIMP_TAC std_ss [ch_set_def,APPEND,PATH_def,IN_DEF]));

val reachables_NEXT = store_thm("reachables_NEXT",
  ``!i x1 x2 d h.
      i IN FDOM h /\ (h ' i = (x1,x2,d)) ==>
      (reachables [i] (ch_set h) =
       {(i,x1,x2,d)} UNION reachables [x1] (ch_set h) UNION reachables [x2] (ch_set h))``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``(f = g) = (!a x y d. f (a,x,y,d) = g (a,x,y,d))``]
  \\ SIMP_TAC bool_ss [SIMP_RULE std_ss [IN_DEF] (CONJ IN_UNION IN_INSERT),EMPTY_DEF]
  \\ SIMP_TAC bool_ss [reachables_def,IN_DEF,MEM,reachable_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 FULL_SIMP_TAC bool_ss [ch_set_def]
  THEN1 (Cases_on `p` \\ NTAC 2 (FULL_SIMP_TAC bool_ss [APPEND,PATH_def,ch_set_def,IN_DEF,PAIR_EQ])
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ,ch_set_def,IN_DEF]
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `[]` \\
    FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,ch_set_def,PAIR_EQ] \\ METIS_TAC [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `x1::p` \\
    FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,ch_set_def,PAIR_EQ] \\ METIS_TAC [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `[]` \\
    FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,ch_set_def,PAIR_EQ] \\ METIS_TAC [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `x2::p` \\
    FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,ch_set_def,PAIR_EQ] \\ METIS_TAC []));




val reachables_THM = store_thm("reachables_THM",
  ``!x y xs h. (reachables [] h = {}) /\
               (reachables (x::xs) h = reachables [x] h UNION reachables xs h)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [EXTENSION,IN_UNION]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
  \\ SIMP_TAC bool_ss [reachables_def,MEM,IN_DEF,EMPTY_DEF] \\ METIS_TAC []);

val reachables_fresh_LEMMA = prove(
  ``reachables [fresh h] (ch_set (h |+ (fresh h,v1,v2,x))) =
    {(fresh h,v1,v2,x)} UNION reachables [v1] (ch_set (h |+ (fresh h,v1,v2,x))) UNION
                              reachables [v2] (ch_set (h |+ (fresh h,v1,v2,x)))``,
  MATCH_MP_TAC reachables_NEXT \\ SIMP_TAC bool_ss [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM]);

val PATH_APPEND = prove(
  ``!xs x y ys. PATH (x,xs ++ y::ys) s = PATH(x,xs++[y]) s /\ PATH(y,ys) s``,
  Induct \\ SIMP_TAC std_ss [PATH_def,APPEND] \\ METIS_TAC []);

val LEMMA = prove(
  ``!p r. MEM r (v1::v2::vs) /\ PATH (r,p++[a]) ((fresh h,v1,v2,d) INSERT (ch_set h)) ==>
          ?p r'. MEM r' (v1::v2::vs) /\
                 (PATH (r',p++[a]) ((fresh h,v1,v2,d) INSERT (ch_set h)) \/ (a = v1) \/ (a = v2)) /\
                 ~MEM (fresh h) p``,
  completeInduct_on `LENGTH (p:num list)` \\ STRIP_TAC
  \\ REVERSE (Cases_on `?xs ys. p = xs ++ [fresh h] ++ ys`) \\ FULL_SIMP_TAC std_ss [] THENL [
    REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `p`
    \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss []
    \\ Q.PAT_X_ASSUM `!xs ys. bbb` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `p` \\ SIMP_TAC bool_ss [MEM] \\ METIS_TAC [APPEND,CONS_11],
    REWRITE_TAC [GSYM APPEND_ASSOC,APPEND]
    \\ ONCE_REWRITE_TAC [PATH_APPEND]
    \\ Cases_on `ys`
    \\ SIMP_TAC bool_ss [APPEND,PATH_def,IN_INSERT]
    \\ SIMP_TAC bool_ss [IN_DEF]
    \\ SIMP_TAC bool_ss [fix_MEM,ch_set_def,fresh_NOT_IN_FDOM,PAIR_EQ,LENGTH_APPEND,LENGTH]
    THEN1 (REPEAT STRIP_TAC \\ METIS_TAC [MEM])
    \\ STRIP_TAC
    \\ `LENGTH t < v` by DECIDE_TAC
    \\ REPEAT STRIP_TAC
    \\ `(LENGTH t = LENGTH t) /\ (MEM h' (v1::v2::vs))` by METIS_TAC [MEM]
    \\ METIS_TAC []]);

val LEMMA2 = prove(
  ``!p k r. ~MEM k (r::p) ==> (PATH (r,p ++ [a]) ((k,x,y,z) INSERT s) = PATH (r,p ++ [a]) s)``,
  Induct \\ FULL_SIMP_TAC bool_ss [PATH_def,APPEND,MEM,IN_INSERT,PAIR_EQ]);

val LEMMA3 = prove(
  ``!p k r x y z. ~MEM k (r::p) /\ PATH (r,p ++ [a]) ((k,x,y,z) INSERT s) ==> PATH (r,p ++ [a]) s``,
  METIS_TAC [LEMMA2]);

val reachable_SUBSET = prove(
  ``!xs x s t. reachable x s y /\ s SUBSET t ==> reachable x t y``,
  METIS_TAC [reachable_def,PATH_SUBSET]);

val reachables_fresh = store_thm("reachables_fresh",
  ``reachables (fresh h::vs) (ch_set (h |+ (fresh h,v1,v2,x))) =
    (fresh h,v1,v2,x) INSERT reachables (v1::v2::vs) (ch_set h)``,
  NTAC 2 (ONCE_REWRITE_TAC [reachables_THM])
  \\ REWRITE_TAC [CONJUNCT1 (SPEC_ALL reachables_THM),UNION_EMPTY]
  \\ REWRITE_TAC [reachables_fresh_LEMMA,INSERT_UNION_EQ,UNION_EMPTY,GSYM UNION_ASSOC]
  \\ REWRITE_TAC [GSYM reachables_THM,ch_set_FUPDATE]
  \\ REWRITE_TAC [METIS_PROVE [PAIR] ``(f = g) = !a x y d. f (a,x,y,d) = g (a,x,y,d)``]
  \\ SIMP_TAC bool_ss [SIMP_RULE std_ss [IN_DEF] IN_INSERT,PAIR_EQ,ch_set_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC THENL [
    FULL_SIMP_TAC bool_ss [reachables_def,IN_INSERT,PAIR_EQ]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [IN_DEF]
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss []
    \\ METIS_TAC [reachable_SUBSET,IN_INSERT,SUBSET_DEF],
    FULL_SIMP_TAC bool_ss [reachables_def,IN_INSERT,PAIR_EQ]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,reachable_def]
    \\ FULL_SIMP_TAC bool_ss [fix_MEM]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] THEN1 METIS_TAC []
    \\ CONV_TAC RIGHT_OR_EXISTS_CONV
    \\ Cases_on `(a = v1)` THEN1 METIS_TAC [MEM]
    \\ Cases_on `(a = v2)` THEN1 METIS_TAC [MEM]
    \\ ASM_SIMP_TAC bool_ss []
    \\ Cases_on `a = fresh h`
    \\ FULL_SIMP_TAC bool_ss [ch_set_def,fresh_NOT_IN_FDOM]
    \\ IMP_RES_TAC LEMMA
    \\ REVERSE (Cases_on `r' = fresh h`) THENL [
      `~MEM (fresh h) (r'::p')` by METIS_TAC [MEM]
      \\ IMP_RES_TAC LEMMA3
      \\ Q.EXISTS_TAC `r'`
      \\ ASM_SIMP_TAC bool_ss []
      \\ DISJ2_TAC
      \\ Q.EXISTS_TAC `p'`
      \\ ASM_SIMP_TAC bool_ss [],
      Cases_on `p'`
      \\ FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_INSERT,PAIR_EQ]
      \\ FULL_SIMP_TAC bool_ss [IN_DEF]
      \\ FULL_SIMP_TAC bool_ss [ch_set_def,fresh_NOT_IN_FDOM,fix_MEM]
      \\ METIS_TAC [MEM,LEMMA3]]]);

val _ = export_theory();
