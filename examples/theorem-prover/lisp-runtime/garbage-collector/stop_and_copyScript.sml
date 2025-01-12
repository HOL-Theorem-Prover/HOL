open HolKernel boolLib bossLib Parse; val _ = new_theory "stop_and_copy";
val _ = ParseExtras.temp_loose_equality()

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)
fun ALPHA_TAC s = let
  fun my_alpha_conv tm =
    ALPHA_CONV (mk_var(s,type_of (fst(dest_abs tm)))) tm
  in CONV_TAC (RAND_CONV my_alpha_conv) end;



val _ = Hol_datatype `heap_address = H_ADDR of num | H_DATA of 'a`;
val heap_address_11 = fetch "-" "heap_address_11";
val heap_address_distinct = fetch "-" "heap_address_distinct";

val _ = type_abbrev("abs_heap",``:(num |-> ('b heap_address) list # 'a) #
          (num set) # (num set) # (num set) # (num -> num)``);

val ADDR_MAP_def = Define `
  (ADDR_MAP f [] = []) /\
  (ADDR_MAP f (H_ADDR x::xs) = H_ADDR (f x) :: ADDR_MAP f xs) /\
  (ADDR_MAP f (H_DATA y::xs) = H_DATA y :: ADDR_MAP f xs)`;

val IN_THM = SIMP_RULE std_ss [EXTENSION,GSPECIFICATION]
val ADDR_SET_def = (IN_THM o Define) `ADDR_SET s = { x | MEM (H_ADDR x) s }`;

val (gc_reachable_rules,gc_reachable_ind,gc_reachable_cases) = Hol_reln `
  (!h roots x.
    x IN ADDR_SET roots ==> gc_reachable (h,roots) x) /\
  (!h roots x a xs d.
    a IN FDOM h /\ (h ' a = (xs,d)) /\ x IN ADDR_SET xs /\ gc_reachable (h,roots) a ==>
    gc_reachable (h,roots) x)`;

val PAIR_TRANSLATE_def = Define `PAIR_TRANSLATE f (xs,a) = (ADDR_MAP f xs,a)`;
val SET_TRANSLATE_def = (IN_THM o Define) `SET_TRANSLATE f s = { x | (f x) IN s }`;
val HAS_CHANGED_def = (IN_THM o Define) `HAS_CHANGED f = { x | ~(f x = x) }`;
val POINTERS_def = (IN_THM o Define) `POINTERS h y =
  { a | ?b zs d. b IN y /\ b IN FDOM h /\ (h ' b = (zs,d)) /\ a IN ADDR_SET zs }`;

val gc_filter_def = Define `
  gc_filter (h,roots) = (DRESTRICT h (gc_reachable (h,roots)),roots)`;

val gc_copy_def = Define `
  gc_copy (h1,roots1) (h2,roots2) =
    ?f. (f o f = I) /\ (FDOM h1 = SET_TRANSLATE f (FDOM h2)) /\
        (roots2 = ADDR_MAP f roots1) /\
        !x. x IN FDOM h1 ==> (h1 ' x = PAIR_TRANSLATE f (h2 ' (f x)))`;

val gc_exec_def = Define `gc_exec x y = gc_copy (gc_filter x) y`;

val (abs_step_rules,abs_step_ind,abs_step_cases) = Hol_reln `
  (!h x y z f a.
    a IN z /\ ~(f a = a) ==>
    abs_step (h,x,y,z,f) (h,x,y,z DELETE a,f)) /\
  (!h x y z f a xs d.
    a IN y /\ (h ' a = (xs,d)) /\ (!b. b IN ADDR_SET xs ==> ~(f b = b)) ==>
    abs_step (h,x,y,z,f) (h |+ (a,ADDR_MAP f xs,d),a INSERT x,y DELETE a,z,f)) /\
  (!h x y z f a b xs d.
    a IN z /\ (f a = a) /\ (f b = b) /\ ~(b IN FDOM h) /\ a IN FDOM h /\ (h ' a = (xs,d)) ==>
    abs_step (h,x,y,z,f) (h |+ (b,xs,d) \\ a,x,b INSERT y,z UNION (ADDR_SET xs),(a =+ b) ((b =+ a) f)))`;

val abs_steps_def = Define `abs_steps = RTC abs_step`;

val abs_steps_TRANS = store_thm("abs_steps_TRANS",
  ``!x y z. abs_steps x y /\ abs_steps y z ==> abs_steps x z``,
  METIS_TAC [abs_steps_def,RTC_RTC]);

val (abs_gc_rules,abs_gc_ind,abs_gc_cases) = Hol_reln `
  (!h roots h2 f x.
    abs_steps (h,{},{},ADDR_SET roots,I) (h2,x,{},{},f) ==>
    abs_gc (h,roots) (DRESTRICT h2 x,ADDR_MAP f roots))`;

val abs_gc_inv_def = Define `
  abs_gc_inv (h1,roots1) (h,x,y,z,f) =
    let old = FDOM h UNION HAS_CHANGED f DIFF (x UNION y) in
      DISJOINT x y /\
      POINTERS h x SUBSET (x UNION y) /\
      POINTERS h (UNIV DIFF x) SUBSET old /\
      POINTERS h y UNION ADDR_SET roots1 SUBSET SET_TRANSLATE f (x UNION y) UNION z /\
      SET_TRANSLATE f (x UNION y) UNION z SUBSET gc_reachable (h1,roots1) /\
      (!a. a IN z ==> if f a = a then a IN old else f a IN x UNION y) /\
      (!a. ~(f a = a) ==> ~(a IN x UNION y = f a IN x UNION y)) /\
      (!a. a IN y \/ a IN x = ~(f a = a) /\ a IN FDOM h) /\ (f o f = I) /\
      (SET_TRANSLATE f (FDOM h) = FDOM h1) /\
      (!d. d IN FDOM h1 ==>
          (h1 ' d = if (f d) IN x then PAIR_TRANSLATE f (h ' (f d)) else h ' (f d)))`;

val SET_TAC =
  FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
    DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV]
  \\ METIS_TAC [PAIR_EQ];

val SET2_TAC =
  FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
    DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV,
    POINTERS_def,HAS_CHANGED_def,SET_TRANSLATE_def,FDOM_FUPDATE,
    FDOM_DOMSUB,FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM] \\ SET_TAC;

val POINTERS_IGNORE = prove(
  ``~(a IN x) ==> (POINTERS (h |+ (a,xs,d)) x = POINTERS h x) /\
                  (POINTERS (h \\ a) x = POINTERS h x)``,
  SET2_TAC);

val set_SUBSET_POINTERS = prove(
  ``(h ' a = (xs,d)) /\ a IN FDOM h /\ a IN x ==> ADDR_SET xs SUBSET POINTERS h x``,
  SET2_TAC);

val POINTER_FUPDATE_EQ = store_thm("POINTER_FUPDATE_EQ",
  ``~(b IN FDOM h) /\ b IN x ==>
    (POINTERS (h |+ (b,xs,d)) x = POINTERS h x UNION ADDR_SET xs)``,
  SET2_TAC);

val POINTERS_FUPDATE = prove(
  ``POINTERS (h |+ (b,xs,d)) (b INSERT y) SUBSET POINTERS h y UNION ADDR_SET xs``,
  SET2_TAC);

val POINTERS_SUBSET = prove(
  ``!h x y. x SUBSET y ==> POINTERS h x SUBSET POINTERS h y``,
  SET2_TAC);

val POINTERS_DOMSUB = prove(
  ``!h y. POINTERS (h \\ a) y SUBSET POINTERS h y``,
  SET2_TAC);

val SET_TRANSLATE_SUBSET = prove(
  ``!f x y. (f o f = I) ==>
            (SET_TRANSLATE f x SUBSET y = x SUBSET SET_TRANSLATE f y)``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ SET2_TAC);

val SET_TRANSLATE_MAP = prove(
  ``!xs f. (f o f = I) ==> (ADDR_SET (ADDR_MAP f xs) = SET_TRANSLATE f (ADDR_SET xs))``,
  SIMP_TAC std_ss [EXTENSION,ADDR_SET_def,SET_TRANSLATE_def]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ Induct
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,MEM] \\ Cases
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,MEM,heap_address_11,heap_address_distinct]
  \\ SET2_TAC);

val SET_TRANSLATE_THM = prove(
  ``(f o f = I) ==>
     (SET_TRANSLATE f (x UNION y) = (SET_TRANSLATE f x) UNION (SET_TRANSLATE f y)) /\
     (SET_TRANSLATE f (x INTER y) = (SET_TRANSLATE f x) INTER (SET_TRANSLATE f y)) /\
     (SET_TRANSLATE f (a INSERT x) = (f a) INSERT (SET_TRANSLATE f x)) /\
     (SET_TRANSLATE f (SET_TRANSLATE f x) = x)``,
  SIMP_TAC std_ss [EXTENSION] \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ SET2_TAC);

val SET_TRANSLATE_IGNORE = prove(
  ``(f o f = I) /\ (f a = a) /\ (f b = b) /\ ~(a IN x) /\ ~(b IN x) ==>
      (SET_TRANSLATE ((a =+ b) ((b =+ a) f)) x = SET_TRANSLATE f x)``,
  SIMP_TAC std_ss [EXTENSION] \\ SIMP_TAC std_ss [FUN_EQ_THM,APPLY_UPDATE_THM,
    SET_TRANSLATE_def] \\ SET2_TAC);

val ADDR_MAP_ADDR_MAP = store_thm("ADDR_MAP_ADDR_MAP",
  ``!xs f. (f o f = I) ==> (ADDR_MAP f (ADDR_MAP f xs) = xs)``,
  Induct \\ SIMP_TAC std_ss [ADDR_MAP_def] \\ Cases
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,FUN_EQ_THM]);

val ADDR_MAP_EQ_ADDR_MAP = prove(
  ``!xs f g. (ADDR_MAP f xs = ADDR_MAP g xs) = !x. x IN ADDR_SET xs ==> (f x = g x)``,
  Induct \\ SIMP_TAC std_ss [ADDR_MAP_def,ADDR_SET_def,MEM]
  \\ Cases \\ FULL_SIMP_TAC std_ss [ADDR_MAP_def,ADDR_SET_def,MEM,CONS_11,
       heap_address_11,heap_address_distinct] \\ SET_TAC);

val abs_step_thm = prove(
  ``!s1 s2. abs_step s1 s2 /\ abs_gc_inv (h0,r0) s1 ==> abs_gc_inv (h0,r0) s2``,
  REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `abs_step s1 s1i` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [abs_step_cases]
  THEN1 (FULL_SIMP_TAC std_ss [abs_gc_inv_def,IN_UNION,IN_DELETE,LET_DEF]
         \\ `f a IN x UNION y` by SET_TAC
         \\ SUBGOAL `a IN SET_TRANSLATE f (x UNION y)` THEN1 SET_TAC \\ SET2_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [abs_gc_inv_def,IN_UNION,IN_DELETE,FDOM_FUPDATE,LET_DEF]
    \\ `a INSERT FDOM h = FDOM h` by SET_TAC \\ ASM_SIMP_TAC std_ss [IN_INSERT]
    \\ `~(a IN x) /\ ~(a IN (FDOM h UNION HAS_CHANGED f DIFF (a INSERT x)))` by SET_TAC
    \\ ASM_SIMP_TAC std_ss [POINTERS_IGNORE] \\ STRIP_TAC THEN1 SET_TAC
    \\ `(a INSERT x) UNION (y DELETE a) UNION z = x UNION y UNION z` by SET_TAC
    \\ `(a INSERT x) UNION (y DELETE a) = x UNION y` by SET_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (Cases_on `f d' = a` \\ ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,IN_INSERT]
      \\ `~(a IN x)` by SET_TAC
      \\ ASM_SIMP_TAC std_ss [PAIR_TRANSLATE_def,ADDR_MAP_ADDR_MAP])
    THEN1 SET_TAC THEN1 SET_TAC THEN1 SET_TAC THEN1 SET2_TAC THEN1 SET2_TAC
    \\ MATCH_MP_TAC (MATCH_MP (RW [GSYM AND_IMP_INTRO] SUBSET_TRANS) (SPEC_ALL POINTERS_FUPDATE))
    \\ ASM_SIMP_TAC std_ss [UNION_SUBSET] \\ `a IN FDOM h` by SET_TAC
    \\ IMP_RES_TAC set_SUBSET_POINTERS \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_SUBSET] \\ SET2_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [abs_gc_inv_def,IN_UNION,IN_DELETE,FDOM_FUPDATE,IN_INSERT,LET_DEF]
    \\ `~(a IN x) /\ ~(b IN x) /\ ~(a = b) /\ a IN (UNIV DIFF x) /\ a IN (UNIV DIFF (x UNION y))` by SET_TAC
    \\ `ADDR_SET xs SUBSET POINTERS h (UNIV DIFF (x UNION y))` by METIS_TAC [set_SUBSET_POINTERS]
    \\ `((a =+ b) ((b =+ a) f) o (a =+ b) ((b =+ a) f) = I)` by
         (FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,FUN_EQ_THM] \\ SET_TAC)
    \\ STRIP_TAC THEN1 SET_TAC
    \\ ASM_SIMP_TAC std_ss [POINTERS_IGNORE] \\ STRIP_TAC THEN1 SET_TAC
    \\ `(HAS_CHANGED ((a =+ b) ((b =+ a) f)) = a INSERT b INSERT HAS_CHANGED f) /\
       ~(b IN HAS_CHANGED f)` by
        (FULL_SIMP_TAC std_ss [EXTENSION,HAS_CHANGED_def,APPLY_UPDATE_THM] \\ SET2_TAC)
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [] \\ SET2_TAC)
    \\ `~(a IN y) /\ ~(b IN y)` by SET_TAC
    \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_THM,APPLY_UPDATE_THM,SET_TRANSLATE_IGNORE]
    \\ STRIP_TAC THEN1 SET2_TAC
    \\ STRIP_TAC THEN1
     (`a IN gc_reachable (h0,r0)` by SET_TAC
      \\ SUBGOAL `ADDR_SET xs SUBSET gc_reachable (h0,r0)` THEN1 SET_TAC
      \\ FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC
      \\ SIMP_TAC std_ss [IN_DEF] \\ ONCE_REWRITE_TAC [gc_reachable_cases]
      \\ DISJ2_TAC \\ Q.PAT_X_ASSUM `a IN gc_reachable hhh`
           (ASSUME_TAC o SIMP_RULE std_ss [IN_DEF]) \\ ASM_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`a`,`xs`,`d`] \\ ASM_SIMP_TAC std_ss [] \\ SET2_TAC)
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [FDOM_FUPDATE,FDOM_DOMSUB]
      \\ ALPHA_TAC "n" \\ REPEAT STRIP_TAC THEN1
       (Cases_on `a = n` \\ FULL_SIMP_TAC std_ss []
        \\ SUBGOAL `~(n = b)` THEN1 (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ SET_TAC)
        \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `~(b IN HAS_CHANGED f)` by (SIMP_TAC std_ss [HAS_CHANGED_def] \\ SET_TAC)
        \\ SET_TAC)
      \\ Cases_on `a = n` \\ FULL_SIMP_TAC std_ss []
      \\ `POINTERS h (UNIV DIFF (x UNION y)) SUBSET POINTERS h (UNIV DIFF x)` by
           (MATCH_MP_TAC POINTERS_SUBSET \\ SET_TAC)
      \\ `n IN FDOM h UNION HAS_CHANGED f DIFF (x UNION y)` by SET_TAC
      \\ FULL_SIMP_TAC std_ss [IN_INSERT,IN_UNION,IN_DELETE,IN_DIFF] \\ SET_TAC)
    \\ FULL_SIMP_TAC std_ss [FDOM_DOMSUB,FDOM_FUPDATE,IN_INSERT]
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ SET_TAC)
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ SET_TAC)
    \\ Q.PAT_X_ASSUM `gg = FDOM h0` (ASSUME_TAC o GSYM) \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [EXTENSION,SET_TRANSLATE_def,APPLY_UPDATE_THM]
      \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ SET_TAC)
    \\ ALPHA_TAC "i" \\ STRIP_TAC
    \\ Cases_on `(i = a) \/ (i = b)` \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,
        FUN_EQ_THM,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]
    THEN1 (FULL_SIMP_TAC std_ss [SET_TRANSLATE_def])
    \\ `~(f i = a) /\ ~(f i = b)` by METIS_TAC []
    \\ Cases_on `f i IN x` \\ FULL_SIMP_TAC std_ss []
    \\ `?xs d. h ' (f i) = (xs,d)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [PAIR_TRANSLATE_def,IN_DEF,SET_TRANSLATE_def]
    \\ ASM_SIMP_TAC std_ss [ADDR_MAP_EQ_ADDR_MAP,APPLY_UPDATE_THM]
    \\ REPEAT STRIP_TAC
    \\ `ADDR_SET xs' SUBSET x UNION y` by METIS_TAC [set_SUBSET_POINTERS,SUBSET_TRANS]
    \\ SET_TAC));

val abs_steps_thm = prove(
  ``!s1 s2. abs_steps s1 s2 /\ abs_gc_inv (h0,r0) s1 ==> abs_gc_inv (h0,r0) s2``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO,abs_steps_def]
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ SIMP_TAC std_ss [] \\ METIS_TAC [abs_step_thm]);

val ok_heap_def = Define `
  ok_heap (h,roots) = (POINTERS h UNIV UNION ADDR_SET roots SUBSET FDOM h)`;

val ok_heap_IMP = store_thm("ok_heap_IMP",
  ``ok_heap (h1,roots1) ==> abs_gc_inv (h1,roots1) (h1,{},{},ADDR_SET roots1,I)``,
  FULL_SIMP_TAC std_ss [abs_gc_inv_def,LET_DEF,ok_heap_def]
  \\ SUBGOAL `ADDR_SET roots1 SUBSET gc_reachable (h1,roots1)` THEN1 SET2_TAC
  \\ SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [IN_DEF]
  \\ ONCE_REWRITE_TAC [gc_reachable_cases] \\ ASM_SIMP_TAC std_ss []);

val abs_gc_thm = store_thm("abs_gc_thm",
  ``!h1 roots1 h2 roots2.
       ok_heap (h1,roots1) /\ abs_gc (h1,roots1) (h2,roots2) ==>
       gc_exec (h1,roots1) (h2,roots2)``,
  SIMP_TAC std_ss [abs_gc_cases,gc_exec_def,gc_filter_def,gc_copy_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `f` \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ok_heap_IMP \\ IMP_RES_TAC abs_steps_thm \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [abs_gc_inv_def,LET_DEF,NOT_IN_EMPTY,UNION_EMPTY]
  \\ STRIP_TAC \\ SIMP_TAC std_ss [FDOM_DRESTRICT,DRESTRICT_DEF]
  \\ SUBGOAL `gc_reachable (h1,roots1) = SET_TRANSLATE f x` THEN1 SET2_TAC
  \\ ASM_SIMP_TAC std_ss [SET_EQ_SUBSET] \\ SIMP_TAC std_ss [SUBSET_DEF]
  \\ `?tt. (h1,roots1) = tt` by METIS_TAC [PAIR] \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SIMP_TAC std_ss [AND_IMP_INTRO] \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o SIMP_RULE std_ss [IN_DEF])
  \\ Q.SPEC_TAC (`x'`,`q`) \\ Q.SPEC_TAC (`tt`,`t`)
  \\ HO_MATCH_MP_TAC gc_reachable_ind \\ REPEAT STRIP_TAC THEN1 SET_TAC
  \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_def]
  \\ `h2' ' (f q') = (ADDR_MAP f xs,d)` by
    (Q.PAT_X_ASSUM `!d. d IN FDOM h ==> bb` (MP_TAC o GSYM o Q.SPEC `q'`)
     \\ `?xs2 d2. h2' ' (f q') = (xs2,d2)` by METIS_TAC [PAIR]
     \\ ASM_SIMP_TAC std_ss [PAIR_TRANSLATE_def]
     \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
     \\ ASM_SIMP_TAC std_ss [ADDR_MAP_ADDR_MAP])
  \\ `ADDR_SET (ADDR_MAP f xs) SUBSET POINTERS h2' x` by METIS_TAC [set_SUBSET_POINTERS]
  \\ `f q IN ADDR_SET (ADDR_MAP f xs)` by
      (FULL_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_def]
       \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]) \\ SET_TAC);

val gc_copy_thm = prove(
  ``ok_heap (h1,roots1) /\ gc_copy (h1,roots1) (h2,roots2) ==> ok_heap (h2,roots2)``,
  SIMP_TAC std_ss [gc_exec_def,gc_copy_def,gc_filter_def,ok_heap_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_UNION,POINTERS_def]
  \\ `!k. f (f k) = k` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_def]
    \\ SET_TAC)
  \\ FULL_SIMP_TAC std_ss [IN_UNIV,SET_TRANSLATE_def,EXTENSION]
  \\ Q.PAT_X_ASSUM `!d. ff IN FDOM h1 <=> bb IN FDOM h2` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `h1 ' (f b) = PAIR_TRANSLATE f (zs,d)` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [PAIR_TRANSLATE_def]
  \\ SUBGOAL `f x IN ADDR_SET (ADDR_MAP f zs)` THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_def]);

val gc_filter_thm = prove(
  ``ok_heap (h1,roots1) ==> ok_heap (gc_filter(h1,roots1))``,
  SIMP_TAC std_ss [gc_exec_def,gc_copy_def,gc_filter_def,ok_heap_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_UNION,POINTERS_def]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (RES_TAC \\ FULL_SIMP_TAC std_ss [FDOM_DRESTRICT,IN_INTER]
    \\ FULL_SIMP_TAC std_ss [IN_DEF] \\ ONCE_REWRITE_TAC [gc_reachable_cases]
    \\ ASM_SIMP_TAC std_ss [IN_DEF])
  \\ FULL_SIMP_TAC std_ss [FDOM_DRESTRICT,IN_INTER]
  \\ Q.PAT_X_ASSUM `DRESTRICT h1 (gc_reachable (h1,roots1)) ' b = (zs,d)` MP_TAC
  \\ ASM_SIMP_TAC std_ss [DRESTRICT_DEF,IN_INTER] \\ REPEAT STRIP_TAC THEN1 SET_TAC
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ ONCE_REWRITE_TAC [gc_reachable_cases] \\ DISJ2_TAC
  \\ SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC std_ss [IN_DEF]);

val gc_exec_thm = store_thm("gc_exec_thm",
  ``ok_heap (h1,roots1) /\ gc_exec (h1,roots1) (h2,roots2) ==> ok_heap (h2,roots2)``,
  METIS_TAC [gc_exec_def,gc_filter_thm,gc_copy_thm,PAIR]);

(* next level *)

val _ = Hol_datatype `heap_element =
    H_EMP | H_REF of num | H_BLOCK of ('a heap_address) list # (num # 'b)`;
val heap_element_distinct = fetch "-" "heap_element_distinct";
val heap_element_11 = fetch "-" "heap_element_11";

val isDATA_def = Define `isDATA x = ?i. x = H_DATA i`;
val isADDR_def = Define `isADDR x = ?i. x = H_ADDR i`;
val isREF_def = Define `isREF x = ?i. x = H_REF i`;
val isBLOCK_def = Define `isBLOCK x = ?i. x = H_BLOCK i`;
val getADDR_def = Define `getADDR (H_ADDR x) = x`;
val getREF_def = Define `getREF (H_REF x) = x`;
val getBLOCK_def = Define `getBLOCK (H_BLOCK y) = y`;
val getLENGTH_def = Define `
  (getLENGTH (H_BLOCK (m,l,n)) = l + 1) /\
  (getLENGTH (H_REF i) = 0) /\
  (getLENGTH (H_EMP) = 0)`;

val RANGE_def = Define `RANGE(i:num,j) k = i <= k /\ k < j`;
val CUT_def = Define `CUT (i,j) m = \k. if RANGE (i,j) k then m k else H_EMP`;

val D0 = Define `D0 m k = ?x y z. m (k:num) = H_BLOCK (x,y,z)`;
val D1 = Define `D1 m i = ?k x y z. (m (k:num) = H_BLOCK(x,y,z)) /\ i IN ADDR_SET x`;
val R0 = Define `R0 m k = ?a. m (k:num) = H_REF a`;
val R1 = Define `R1 m a = ?k. m (k:num) = H_REF a`;
val DR0 = Define `DR0 m k = D0 m k \/ R0 m k`
val DR1 = Define `DR1 m k = D1 m k \/ R1 m k`

val EMP_RANGE_def = Define `
  EMP_RANGE (b,e) m = !k. k IN RANGE(b,e) ==> (m k = H_EMP)`;

val rel_move_def = Define `
  (rel_move (H_DATA x,j,m,b,e,b2,e2) = (T,H_DATA x,j,m)) /\
  (rel_move (H_ADDR a,j,m,b,e,b2,e2) =
     case m a of
        H_EMP => (F,ARB)
      | H_REF i => (RANGE (b2,e2) a,H_ADDR i,j,m)
      | H_BLOCK (xs,n,d) => let cond = RANGE (b2,e2) a in
                            let m = (a =+ H_REF j) m in
                            let cond = RANGE (b,e) j /\ (m j = H_EMP) /\ cond in
                            let m = (j =+ H_BLOCK (xs,n,d)) m in
                              (cond,H_ADDR j,j + n + 1,m))`;

val rel_move_list_def = Define `
  (rel_move_list ([],j,m,b,e,b2,e2) = (T,[],j,m)) /\
  (rel_move_list (x::xs,j,m,b,e,b2,e2) =
     let (c1,x,j,m) = rel_move (x,j,m,b,e,b2,e2) in
     let (c2,xs,j,m) = rel_move_list (xs,j,m,b,e,b2,e2) in
       (c1 /\ c2,x::xs,j,m))`;

val rel_gc_step_def = Define `
  rel_gc_step (i,j,m,b,e,b2,e2) =
    let cond = isBLOCK (m i) in
    let (xs,n,d) = getBLOCK (m i) in
    let (c2,ys,j,m) = rel_move_list (xs,j,m,b,e,b2,e2) in
    let cond = cond /\ (m i = H_BLOCK (xs,n,d)) /\ RANGE(b,e)i /\ c2 /\
               EMP_RANGE (i+1,i+n+1) m in
    let m = (i =+ H_BLOCK (ys,n,d)) m in
    let i = i + n + 1 in
    let cond = cond /\ i <= j in
      (cond,i,j,m)`;

val rel_gc_loop_def = tDefine "rel_gc_loop" `
  rel_gc_loop (i,j,m,b,e,b2,e2) =
    if i = j then (T,i,m) else
    if ~(i < j /\ j <= e) then (F,ARB) else
      let (c1,i,j,m) = rel_gc_step (i,j,m,b,e,b2,e2) in
      let (c2,i,m) = rel_gc_loop (i,j,m,b,e,b2,e2) in
        (c1/\c2,i,m)`
 (WF_REL_TAC `measure (\(i,j,m,b,e,b2,e2). e - i)`
  \\ SIMP_TAC std_ss [rel_gc_step_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val rel_gc_def = Define `
  rel_gc (b:num,e:num,b2:num,e2:num,roots,m) =
    let (b2,e2,b,e) = (b,e,b2,e2) in
    let (cond,roots,j,m) = rel_move_list (roots,b,m,b,e,b2,e2) in
    let (c,i,m) = rel_gc_loop (b,j,m,b,e,b2,e2) in
    let cond = cond /\ b <= i /\ i <= e in
    let m = CUT (b,i) m in
      (c /\ cond,b,i,e,b2,e2,roots,m)`;



(* invariant *)

Inductive full_heap:
  (!b m. full_heap b b m) /\
  (!b e m n xs d.
     (m b = H_BLOCK (xs,n,d)) /\ EMP_RANGE (b+1,b+n+1) m /\
     full_heap (b+n+1) e m ==> full_heap b e m)
End

val full_heap_ind = save_thm("full_heap_ind[allow_rebind]",full_heap_strongind);

Inductive part_heap:
  (!b m. part_heap b b m 0) /\
  (!b e m k.
     ~(isBLOCK (m b)) /\ part_heap (b+1) e m k ==> part_heap b e m k) /\
  (!b e m n xs d k.
     (m b = H_BLOCK (xs,n,d)) /\ EMP_RANGE (b+1,b+n+1) m /\
     part_heap (b+n+1) e m k ==> part_heap b e m (k+n+1))
End

val part_heap_ind = save_thm("part_heap_ind[allow_rebind]",part_heap_strongind);

val ref_heap_mem_def = Define `
  ref_heap_mem (h,f) m =
    !a. m a = if a IN FDOM h then H_BLOCK (h ' a) else
              if f a = a then H_EMP else H_REF (f a)`;

val gc_inv_def = Define `
  gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z) =
    (b <= i /\ i <= j /\ j <= e) /\
    (* semispaces are disjoint, simplified *)
    (~(e2 <= b) ==> e <= b2) /\
    (* EMP outside of b2-e2 and b-j *)
    (!k. ~(RANGE(b2,e2)k) /\ ~(RANGE(b,j)k) ==> (m k = H_EMP)) /\
    (* heap full of BLOCK elements between b-i, i-j *)
    full_heap b i m /\ full_heap i j m /\
    (* data elements from b2-e2 fit into j-e *)
    (?len. part_heap b2 e2 m len /\ len <= e-j) /\
    (* refinement *)
    ref_heap_mem (h,f) m /\
    (* simulation *)
    ok_heap (h1,roots1) /\
    abs_steps (h1,{},{},ADDR_SET roots1,I) (h,D0(CUT(b,i)m),D0(CUT(i,j)m),z,f)`;

(* some lemmas *)

val RANGE_TAC = FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF,gc_inv_def] \\ DECIDE_TAC

val gc_inv_IMP = store_thm("gc_inv_IMP",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z) ==>
    abs_gc_inv (h1,roots1) (h,D0(CUT(b,i)m),D0(CUT(i,j)m),z,f)``,
  SIMP_TAC std_ss [gc_inv_def] \\ METIS_TAC [ok_heap_IMP,abs_steps_thm]);

val gc_inv_THM = store_thm("gc_inv_THM",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z) =
    gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z) /\
    abs_gc_inv (h1,roots1) (h,D0(CUT(b,i)m),D0(CUT(i,j)m),z,f)``,
  METIS_TAC [gc_inv_IMP]);

val full_heap_REFL = store_thm("full_heap_REFL",
  ``!b m. full_heap b b m``,
  METIS_TAC [full_heap_cases]);

val full_heap_TRANS = store_thm("full_heap_TRANS",
  ``!j b i m. full_heap b i m /\ full_heap i j m ==> full_heap b j m``,
  STRIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ HO_MATCH_MP_TAC full_heap_ind
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ METIS_TAC [full_heap_cases]);

val full_heap_step = prove(
  ``!n xs d b e m. full_heap b e m ==>
            (m e = H_BLOCK (xs,n,d)) /\ EMP_RANGE (e+1,e+n+1) m ==>
            full_heap b (e+n+1) m``,
  NTAC 3 STRIP_TAC
  \\ HO_MATCH_MP_TAC full_heap_ind \\ STRIP_TAC THEN1 METIS_TAC [full_heap_cases]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [full_heap_cases]);

val CUT_EQ = store_thm("CUT_EQ",
  ``((CUT (b,e) m a = H_BLOCK x) = (a IN RANGE (b,e) /\ (m a = H_BLOCK x))) /\
    ((CUT (b,e) m a = H_REF i) = (a IN RANGE (b,e) /\ (m a = H_REF i)))``,
  SIMP_TAC std_ss [CUT_def,IN_DEF] \\ SRW_TAC [] []);

val CUT_update = prove(
  ``~RANGE (i,j) k ==> (CUT (i,j) ((k =+ x) m) = CUT (i,j) m)``,
  SIMP_TAC std_ss [CUT_def,UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val part_heap_LESS_EQ = store_thm("part_heap_LESS_EQ",
  ``!b e m k. part_heap b e m k ==> b <= e``,
  HO_MATCH_MP_TAC part_heap_ind \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val EMP_RANGE_RANGE = store_thm("EMP_RANGE_RANGE",
  ``!b e i m.
      ~(RANGE(b,e)i) ==> (EMP_RANGE (b,e) ((i=+x)m) = EMP_RANGE (b,e) m)``,
  FULL_SIMP_TAC std_ss [EMP_RANGE_def,APPLY_UPDATE_THM,IN_DEF] \\ METIS_TAC []);

val part_heap_TRANS = store_thm("part_heap_TRANS",
  ``!j k2 b i m k1. part_heap b i m k1 /\ part_heap i j m k2 ==> part_heap b j m (k1+k2)``,
  NTAC 2 STRIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ HO_MATCH_MP_TAC part_heap_ind \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  THEN1 (REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [part_heap_cases])
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ONCE_REWRITE_TAC [part_heap_cases]
  \\ ASM_SIMP_TAC std_ss [heap_element_11] \\ DISJ2_TAC
  \\ Q.EXISTS_TAC `k1+k2` \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val part_heap_IGNORE = store_thm("part_heap_IGNORE",
  ``!b e m k. part_heap b e m k /\ ~(RANGE(b,e)i) ==>
              part_heap b e ((i =+ x) m) k``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ HO_MATCH_MP_TAC part_heap_ind
  \\ STRIP_TAC THEN1 METIS_TAC [part_heap_cases]
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC part_heap_LESS_EQ
    \\ `~(RANGE(b+1,e)i) /\ ~(i = b)` by RANGE_TAC \\ RES_TAC
    \\ METIS_TAC [APPLY_UPDATE_THM,part_heap_cases])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC part_heap_LESS_EQ
  \\ `~RANGE (b + n + 1,e) i /\ ~(b = i) /\ ~(RANGE(b+1,b+n+1)i)` by RANGE_TAC
  \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ2_TAC
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_element_11,EMP_RANGE_RANGE]);

val part_heap_EMP_RANGE = store_thm("part_heap_EMP_RANGE",
  ``!i m. b <= i /\ EMP_RANGE (b,i) m ==> part_heap b i m 0``,
  STRIP_TAC \\ completeInduct_on `i-b` \\ REPEAT STRIP_TAC \\ Cases_on `i = b`
  \\ FULL_SIMP_TAC std_ss [] THEN1 METIS_TAC [part_heap_cases]
  \\ `b+1 <= i /\ i - (b + 1) < i - b /\ (i - (b + 1) = i - (b + 1))` by DECIDE_TAC
  \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ1_TAC
  \\ SUBGOAL `(m b = H_EMP) /\ EMP_RANGE (b+1,i) m`
  THEN1 (RES_TAC \\ FULL_SIMP_TAC std_ss [isBLOCK_def,heap_element_distinct])
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
  \\ `RANGE(b,i)b` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ `RANGE(b,i)k` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []);

val part_heap_REF = store_thm("part_heap_REF",
  ``!b e m k. part_heap b e m k /\ (m i = H_BLOCK (x,y,d)) /\ RANGE(b,e)i ==>
              y+1 <= k /\ part_heap b e ((i =+ H_REF t) m) (k - (y + 1))``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ HO_MATCH_MP_TAC part_heap_ind
  \\ STRIP_TAC THEN1 (REPEAT STRIP_TAC \\ `F` by RANGE_TAC)
  \\ STRIP_TAC THEN1
   (NTAC 7 STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `i = b`
    THEN1 FULL_SIMP_TAC std_ss [isBLOCK_def,heap_element_11]
    \\ `RANGE (b + 1,e) i` by RANGE_TAC
    \\ METIS_TAC [APPLY_UPDATE_THM,part_heap_cases])
  \\ NTAC 10 STRIP_TAC \\ RES_TAC
  \\ Cases_on `RANGE (b + n + 1,e) i` THEN1
   (`~(i = b)` by RANGE_TAC \\ RES_TAC \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ2_TAC
    \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_element_11]
    \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,APPLY_UPDATE_THM]
    \\ Q.EXISTS_TAC `k-(y+1)` \\ STRIP_TAC THEN1 RANGE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ ALPHA_TAC "j" \\ REPEAT STRIP_TAC
    \\ Cases_on `i = j` \\ FULL_SIMP_TAC std_ss [heap_element_distinct] \\ RANGE_TAC)
  \\ Cases_on `RANGE (b + 1,b + n + 1) i` THEN1
   (FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [heap_element_distinct])
  \\ `i = b` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [heap_element_11]
  \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ1_TAC
  \\ SIMP_TAC std_ss [isBLOCK_def,APPLY_UPDATE_THM,heap_element_distinct]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``k+n+1-(n+1)=k``]
  \\ MATCH_MP_TAC part_heap_IGNORE \\ REVERSE STRIP_TAC THEN1 RANGE_TAC
  \\ ONCE_REWRITE_TAC [GSYM (RW1[ADD_COMM]ADD_0)]
  \\ MATCH_MP_TAC part_heap_TRANS \\ Q.EXISTS_TAC `b+n+1` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [part_heap_EMP_RANGE]);

val part_heap_LENGTH_LESS_EQ = store_thm("part_heap_LENGTH_LESS_EQ",
  ``!b e m k. part_heap b e m k ==> k <= e - b``,
  HO_MATCH_MP_TAC part_heap_ind \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC part_heap_LESS_EQ \\ DECIDE_TAC);

val CUT_UPDATE = store_thm("CUT_UPDATE",
  ``!b e a m x.
      (~(RANGE(b,e)a) ==> (CUT(b,e)((a=+x)m) = CUT(b,e)m)) /\
      (RANGE(b,e)a ==> (CUT(b,e)((a=+x)m) = (a=+x)(CUT(b,e)m)))``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,CUT_def,APPLY_UPDATE_THM] \\ METIS_TAC []);

val ref_heap_mem_IMP = prove(
  ``(ref_heap_mem (h,f) m /\ (m n = H_BLOCK x) ==> n IN FDOM h /\ (h ' n = x)) /\
    (ref_heap_mem (h,f) m /\ (m n = H_REF i) ==> ~(n IN FDOM h) /\ ~(f n = n) /\ (f n = i)) /\
    (ref_heap_mem (h,f) m /\ (m n = H_EMP) ==> ~(n IN FDOM h) /\ (f n = n))``,
  SIMP_TAC std_ss [ref_heap_mem_def,GSYM AND_IMP_INTRO]
  \\ METIS_TAC [heap_element_11,heap_element_distinct]);

val full_heap_LESS_EQ = store_thm("full_heap_LESS_EQ",
  ``!b e m. full_heap b e m ==> b <= e``,
  HO_MATCH_MP_TAC full_heap_ind \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val full_heap_IGNORE = prove(
  ``!m2 b e m. full_heap b e m /\ (!a. RANGE(b,e)a ==> (m2 a = m a)) ==>
               full_heap b e m2``,
  STRIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ HO_MATCH_MP_TAC full_heap_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [full_heap_cases] \\ SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `RANGE (b,e) b` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ DISJ2_TAC \\ ASM_SIMP_TAC std_ss [heap_element_11]
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ `RANGE (b,e) k` by RANGE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Q.PAT_X_ASSUM `bbb ==> full_heap (b + n + 1) e m2` MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ `RANGE (b,e) a` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []);

val full_heap_RANGE = store_thm("full_heap_RANGE",
  ``!i x b e m. full_heap b e m /\ ~(RANGE(b,e)i) ==> full_heap b e ((i =+ x) m)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC full_heap_IGNORE \\ Q.EXISTS_TAC `m`
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `a = i` \\ FULL_SIMP_TAC std_ss [RANGE_def]);

val full_heap_R0 = prove(
  ``!b e m. full_heap b e m ==> !k. RANGE(b,e)k ==> ~(R0 m k)``,
  HO_MATCH_MP_TAC full_heap_ind \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ Cases_on `b = k` \\ FULL_SIMP_TAC std_ss [R0,heap_element_distinct]
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,heap_element_distinct]
  \\ Cases_on `RANGE (b + n + 1,e) k` THEN1 METIS_TAC []
  \\ `RANGE (b + 1,b + n + 1) k` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [R0,heap_element_distinct]);

(* proof *)

val move_lemma = store_thm("move_lemma",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z UNION {n}) /\
    n IN (DR0(CUT(b2,e2)m)) ==>
    (m n = H_REF (f n)) /\ ~(f n = n) \/
    getLENGTH (m n) <= e - j /\ (m n = H_BLOCK (h ' n)) /\ n IN FDOM h /\ ~(n = j) /\
    n IN RANGE(b2,e2) /\ (f n = n) /\ EMP_RANGE (j,j+getLENGTH(H_BLOCK (h ' n))) m``,
  PURE_ONCE_REWRITE_TAC [gc_inv_THM] \\ ONCE_REWRITE_TAC [IN_DEF] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [gc_inv_def] \\ FULL_SIMP_TAC std_ss [DR0,R0,D0,CUT_EQ]
  \\ IMP_RES_TAC ref_heap_mem_IMP \\ ASM_SIMP_TAC std_ss [heap_element_11,heap_element_distinct]
  \\ SIMP_TAC std_ss [getLENGTH_def] \\ `n < e2` by RANGE_TAC
  \\ `(CUT(b2,e2)m) n = H_BLOCK (x,y,z')` by FULL_SIMP_TAC std_ss [CUT_EQ]
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ IMP_RES_TAC part_heap_REF \\ STRIP_TAC THEN1 RANGE_TAC
  \\ FULL_SIMP_TAC std_ss [abs_gc_inv_def,LET_DEF]
  \\ STRIP_TAC THEN1 RANGE_TAC
  \\ STRIP_TAC THEN1
      (`n IN FDOM h` by FULL_SIMP_TAC std_ss [IN_DEF] \\ CCONTR_TAC
       \\ `n IN D0 (CUT (i,j) m) \/ n IN D0 (CUT (b,i) m)` by METIS_TAC []
       \\ FULL_SIMP_TAC std_ss [D0,CUT_EQ,IN_DEF] \\ RANGE_TAC)
   \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
   \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!k. bbb ==> (m k = H_EMP)` MATCH_MP_TAC
   \\ RANGE_TAC);

val ADDR_SET_THM = store_thm("ADDR_SET_THM",
  ``(ADDR_SET [] = {}) /\
    (ADDR_SET (H_DATA x :: xs) = ADDR_SET xs) /\
    (ADDR_SET (H_ADDR y :: xs) = y INSERT ADDR_SET xs)``,
  SRW_TAC [] [ADDR_SET_def,EXTENSION,MEM,NOT_IN_EMPTY,IN_INSERT]);

val CUT_EMPTY = store_thm("CUT_EMPTY",
  ``(D0(CUT(j,j)m) = {}) /\ (D1(CUT(j,j)m) = {}) /\
    (R0(CUT(j,j)m) = {}) /\ (R1(CUT(j,j)m) = {})``,
  SIMP_TAC std_ss [EXTENSION,NOT_IN_EMPTY]
  \\ `!j n. ~RANGE(j,j)n` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [IN_DEF,D0,R0,D1,R1,CUT_EQ]);

val remove_from_z = prove(
  ``~(f n = n) ==> abs_steps (h,x,y,z UNION {n},f) (h,x,y,z,f)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [abs_steps_def] \\ Cases_on `n IN z`
  THEN1 (`z UNION {n} = z` by SET_TAC \\ FULL_SIMP_TAC std_ss [RTC_REFL])
  \\ `(z,f) = ((z UNION {n}) DELETE n,f)` by SET_TAC
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) \\ MATCH_MP_TAC RTC_SINGLE
  \\ SIMP_TAC std_ss [abs_step_cases] \\ SET_TAC);

val full_heap_BLOCK = prove(
  ``!b e m. full_heap b e m /\ (m i = H_BLOCK (x2,y,z2)) ==>
            full_heap b e ((i =+ H_BLOCK (x,y,z)) m)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ HO_MATCH_MP_TAC full_heap_ind
  \\ SIMP_TAC std_ss [full_heap_REFL] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ ONCE_REWRITE_TAC [full_heap_cases]
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,APPLY_UPDATE_THM]
  \\ METIS_TAC [heap_element_11,heap_element_distinct,PAIR_EQ]);

val move_thm = store_thm("move_thm",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z UNION ADDR_SET [x]) /\
    ADDR_SET [x] SUBSET (DR0(CUT(b2,e2)m)) /\
    (rel_move (x,j,m,b,e,b2,e2) = (c,x2,j2,m2)) ==>
      ?h2 f2. gc_inv (h1,roots1,h2,f2) (b,i,j2,e,b2,e2,m2,z UNION (D1(CUT(j,j2)m2))) /\ j <= j2 /\
              DR0 (CUT (b2,e2) m) SUBSET DR0 (CUT (b2,e2) m2) /\
              (CUT(b,j)m = CUT(b,j)m2) /\
              (!a. ~(f a = a) ==> (f2 a = f a)) /\
              (!a. a IN ADDR_SET [x2] ==> ~(f2 a = a)) /\
              ([x2] = ADDR_MAP f2 [x]) /\ full_heap j j2 m2 /\ c``,
  CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [gc_inv_THM]))
  \\ REVERSE (Cases_on `x`) THEN1
   (SIMP_TAC std_ss [rel_move_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ sg `ADDR_SET [H_DATA a] = {}` \\ ASM_SIMP_TAC std_ss [full_heap_REFL]
    \\ ASM_SIMP_TAC std_ss [ADDR_SET_def,SUBSET_DEF,MEM,NOT_IN_EMPTY,ADDR_MAP_def,
          heap_address_distinct,EXTENSION,UNION_EMPTY,CUT_EMPTY] \\ SET_TAC)
  \\ SIMP_TAC std_ss [ADDR_SET_THM,INSERT_SUBSET,EMPTY_SUBSET]
  \\ STRIP_TAC
  \\ IMP_RES_TAC move_lemma \\ FULL_SIMP_TAC std_ss [heap_element_distinct]
  THEN1
   (Q.LIST_EXISTS_TAC [`h`,`f`] \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `rel_move xx = fg` MP_TAC \\ ASM_SIMP_TAC (srw_ss()) [rel_move_def]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [ADDR_SET_THM,
         IN_INSERT,NOT_IN_EMPTY,CUT_EMPTY,UNION_EMPTY,full_heap_REFL]
    \\ FULL_SIMP_TAC std_ss [gc_inv_def,ADDR_MAP_def] \\ IMP_RES_TAC remove_from_z
    \\ `f o f = I` by METIS_TAC [abs_gc_inv_def] \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,DR0,D0,R0,CUT_EQ]
    \\ METIS_TAC [abs_steps_thm,remove_from_z,abs_steps_TRANS])
  \\ `?x y d. h ' n = (x,y,d)` by METIS_TAC [PAIR]
  \\ Q.PAT_X_ASSUM `rel_move xx = fg` MP_TAC \\ ASM_SIMP_TAC (srw_ss()) [rel_move_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [LET_DEF,DECIDE ``j <= j + y + 1``]
  \\ STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`h |+ (j,h ' n) \\ n`,`(n =+ j) ((j =+ n) f)`] \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,ADDR_SET_THM,IN_INSERT,NOT_IN_EMPTY]
  \\ `full_heap j (j + y + 1) ((j =+ H_BLOCK (x,y,d)) ((n =+ H_REF j) m))` by
    (Q.PAT_X_ASSUM `~(n = j)` (fn th => REWRITE_TAC [MATCH_MP UPDATE_COMMUTES (GSYM th)])
     \\ `~(RANGE(j,j+y+1)n)` by
      (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IN_DEF,R0,D0,DR0,EMP_RANGE_def,
         getLENGTH_def,ADD_ASSOC,heap_element_distinct])
     \\ MATCH_MP_TAC full_heap_RANGE \\ ASM_SIMP_TAC std_ss []
     \\ ONCE_REWRITE_TAC [full_heap_cases] \\ DISJ2_TAC
     \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_element_11,full_heap_REFL,
          EMP_RANGE_def,getLENGTH_def,IN_DEF,ADD_ASSOC] \\ REPEAT STRIP_TAC
     \\ `~(j = k) /\ RANGE (j,j + y + 1) k` by RANGE_TAC \\ SET_TAC)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 ==> b2) /\ b1 ==> b1 /\ b2``)
  \\ STRIP_TAC THEN1
   (STRIP_TAC
    \\ `~(RANGE(b,j)j) /\ ~(RANGE(b,j)n) /\ ~(RANGE(b2,e2)j)` by RANGE_TAC
    \\ ASM_SIMP_TAC std_ss [CUT_UPDATE,ADDR_MAP_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,DR0,IN_DEF,D0,R0,CUT_EQ,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [getLENGTH_def,EMP_RANGE_def,ADD_ASSOC,IN_DEF]
    \\ `RANGE (j,j + y + 1) j` by RANGE_TAC
    \\ `RANGE (b,e) j` by RANGE_TAC
    \\ FULL_SIMP_TAC std_ss [gc_inv_def,FUN_EQ_THM,abs_gc_inv_def,LET_DEF]
    \\ `f j = j` by METIS_TAC [ref_heap_mem_def,heap_element_distinct]
    \\ REPEAT STRIP_TAC \\ METIS_TAC [heap_element_11,heap_element_distinct,PAIR_EQ])
  \\ FULL_SIMP_TAC std_ss [gc_inv_def]
  \\ FULL_SIMP_TAC std_ss [getLENGTH_def]
  \\ `~(RANGE(b,i)j) /\ ~(RANGE(b,i)n) /\ ~(RANGE(i,j)j) /\
      ~(RANGE(i,j)n) /\ ~(RANGE(b2,e2)j)` by RANGE_TAC
  \\ REPEAT STRIP_TAC THEN1 RANGE_TAC THEN1 RANGE_TAC
  THEN1 (`~(j = k) /\ ~(n = k) /\ ~RANGE (b,j) k` by RANGE_TAC \\ METIS_TAC [APPLY_UPDATE_THM])
  THEN1 METIS_TAC [full_heap_RANGE]
  THEN1
   (MATCH_MP_TAC full_heap_TRANS \\ Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss [full_heap_RANGE])
  THEN1
   (Q.EXISTS_TAC `len - (y+1)` \\ FULL_SIMP_TAC std_ss [IN_DEF]
    \\ IMP_RES_TAC (Q.INST [`t`|->`j`] part_heap_REF)
    \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
    \\ MATCH_MP_TAC part_heap_IGNORE \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (SIMP_TAC std_ss [ref_heap_mem_def,APPLY_UPDATE_THM,FDOM_FUPDATE,FDOM_DOMSUB,
      IN_INSERT,IN_DELETE,FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]
    \\ ALPHA_TAC "k" \\ REPEAT STRIP_TAC
    \\ Cases_on `j = k` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `k = n` \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def])
  \\ FULL_SIMP_TAC std_ss [CUT_UPDATE]
  \\ Q.PAT_X_ASSUM `~(n = j)` (fn th => REWRITE_TAC [MATCH_MP UPDATE_COMMUTES (GSYM th)] THEN ASSUME_TAC th)
  \\ `~(RANGE(j,j + y + 1)n) /\ ~(RANGE(i,j + y + 1)n)` by RANGE_TAC
  \\ FULL_SIMP_TAC std_ss [CUT_UPDATE]
  \\ REPEAT (Q.PAT_X_ASSUM `~(RANGE(xx,yy)df)` (K ALL_TAC))
  \\ `!k. RANGE (i,j + y + 1) k /\ ~RANGE (i,j) k  ==> RANGE (j,j + y + 1) k` by RANGE_TAC
  \\ `D0 (CUT (i,j + y + 1) ((j =+ H_BLOCK (x,y,d)) m)) =
       j INSERT D0 (CUT (i,j) m)` by
     (FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT]
      \\ FULL_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,APPLY_UPDATE_THM,EMP_RANGE_def,IN_DEF]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
       (Cases_on `j = x'` \\ FULL_SIMP_TAC std_ss [heap_element_11]
        \\ CCONTR_TAC \\ `RANGE(j,j+y+1)x'` by RANGE_TAC
        \\ METIS_TAC [heap_element_distinct,ADD_ASSOC])
      \\ Cases_on `j = x'` \\ FULL_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC)
  \\ `D1 (CUT (j,j + y + 1) ((j =+ H_BLOCK (x,y,d)) m)) = ADDR_SET x` by
     (FULL_SIMP_TAC std_ss [FUN_EQ_THM,D1,CUT_EQ,IN_DEF,APPLY_UPDATE_THM,EMP_RANGE_def]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      THEN1 (Cases_on `j = k` \\ METIS_TAC
        [heap_element_11,heap_element_distinct,PAIR_EQ,ADD_ASSOC])
      \\ Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC abs_steps_TRANS
  \\ Q.EXISTS_TAC `(h,D0 (CUT (b,i) m),D0 (CUT (i,j) m),z UNION {n},f)`
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC abs_steps_TRANS
  \\ Q.EXISTS_TAC `(h |+ (j,x,y,d) \\ n,D0 (CUT (b,i) m),j INSERT D0 (CUT (i,j) m),
       (z UNION ADDR_SET x) UNION {n},(n =+ j) ((j =+ n) f))`
  \\ REVERSE STRIP_TAC
  THEN1 (MATCH_MP_TAC remove_from_z \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM])
  \\ `!xx. z UNION xx UNION {n} = z UNION {n} UNION xx` by SET_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [abs_steps_def] \\ MATCH_MP_TAC RTC_SINGLE
  \\ SIMP_TAC std_ss [abs_step_cases] \\ DISJ2_TAC \\ DISJ2_TAC
  \\ Q.LIST_EXISTS_TAC [`n`,`j`,`x`,`(y,d)`] \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 SET_TAC
  \\ `~RANGE (b2,e2) j /\ ~RANGE (b,j) j` by RANGE_TAC
  \\ `m j = H_EMP` by SET_TAC
  \\ Q.PAT_X_ASSUM `ref_heap_mem (h,f) m` (fn th => FULL_SIMP_TAC std_ss [RW[ref_heap_mem_def]th])
  \\ METIS_TAC [heap_element_distinct,IN_UNION,IN_INSERT]);

val ADDR_SET_CONS = store_thm("ADDR_SET_CONS",
  ``!h xs. ADDR_SET (h::xs) = ADDR_SET xs UNION ADDR_SET [h]``,
  Cases \\ FULL_SIMP_TAC std_ss [ADDR_SET_THM,EXTENSION,IN_UNION] \\ SET_TAC);

val D1_UNION = store_thm("D1_UNION",
  ``b <= i /\ i <= j ==> (D1(CUT(b,j)m) = D1(CUT(b,i)m) UNION D1(CUT(i,j)m)) /\
                         (D0(CUT(b,j)m) = D0(CUT(b,i)m) UNION D0(CUT(i,j)m))``,
  SIMP_TAC std_ss [EXTENSION,IN_UNION] \\ SIMP_TAC std_ss [IN_DEF,D1,CUT_EQ,D0]
  \\ REPEAT STRIP_TAC \\ `!k. RANGE(b,j)k = RANGE(b,i)k \/ RANGE(i,j)k` by RANGE_TAC
  \\ SET_TAC);

val D1_CUT_EQ_ADDR_SET_THM = prove(
  ``(m j = H_BLOCK (x,y,d)) /\ EMP_RANGE (j+1,j+y+1) m ==>
    (D1 (CUT (j,j + y + 1) m) = ADDR_SET x)``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,D1,CUT_EQ,IN_DEF,APPLY_UPDATE_THM,EMP_RANGE_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `j = k` \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
         THEN1 METIS_TAC [heap_element_11,heap_element_distinct,PAIR_EQ,ADD_ASSOC]
         \\ `RANGE (j + 1,j + y + 1) k` by RANGE_TAC
         \\ METIS_TAC [heap_element_distinct])
  \\ Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC);

val EQ_RANGE_def = Define `
  EQ_RANGE (b,e) m m2 = !k. k IN RANGE (b,e) ==> (m k = m2 k)`;

val EQ_RANGE_IMP_EQ_RANGE = store_thm("EQ_RANGE_IMP_EQ_RANGE",
  ``!b e i j m m2. EQ_RANGE (b,e) m m2 /\ b <= i /\ j <= e ==> EQ_RANGE (i,j) m m2``,
  SIMP_TAC std_ss [EQ_RANGE_def,IN_DEF,RANGE_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!k.bbb` MATCH_MP_TAC \\ DECIDE_TAC);

val EQ_RANGE_full_heap = store_thm("EQ_RANGE_full_heap",
  ``!m2 b e m. full_heap b e m /\ EQ_RANGE (b,e) m m2 ==> full_heap b e m2``,
  STRIP_TAC \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ HO_MATCH_MP_TAC full_heap_ind
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [full_heap_cases]
  \\ ONCE_REWRITE_TAC [full_heap_cases] \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `~(e = b)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `b IN RANGE (b,e)` by (SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC)
  \\ `m2 b = m b` by METIS_TAC [EQ_RANGE_def]
  \\ ASM_SIMP_TAC std_ss [heap_element_11]
  \\ `b <= b + n + 1 /\ e <= e` by DECIDE_TAC \\ REVERSE STRIP_TAC
  THEN1 (IMP_RES_TAC EQ_RANGE_IMP_EQ_RANGE \\ RES_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ `k IN RANGE (b,e)` suffices_by METIS_TAC [EQ_RANGE_def]
  \\ FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC);

val EQ_RANGE_CUT = store_thm("EQ_RANGE_CUT",
  ``EQ_RANGE (b,i) m (CUT (b,i) m)``,
  SIMP_TAC std_ss [EQ_RANGE_def,CUT_def,IN_DEF]);

val EQ_RANGE_THM = store_thm("EQ_RANGE_THM",
  ``(CUT (b,e) m1 = CUT (b,e) m2) ==> EQ_RANGE (b,e) m1 m2``,
  FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM,EQ_RANGE_def,IN_DEF] \\ SET_TAC);

val move_list_thm = store_thm("move_list_thm",
  ``!xs z h f m j xs2 j2 (m2:num -> ('a,'b) heap_element).
      gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,z UNION ADDR_SET xs) /\
      ADDR_SET xs SUBSET (DR0(CUT(b2,e2)m)) /\
      (rel_move_list (xs,j,m,b,e,b2,e2) = (c,xs2,j2,m2)) ==>
        ?h3 f3. gc_inv (h1,roots1,h3,f3) (b,i,j2,e,b2,e2,m2,z UNION (D1(CUT(j,j2)m2))) /\ j <= j2 /\
                DR0 (CUT (b2,e2) m) SUBSET DR0 (CUT (b2,e2) m2) /\
                (CUT(b,j)m = CUT(b,j)m2) /\
                (!a. ~(f a = a) ==> (f3 a = f a)) /\
                (!a. a IN ADDR_SET xs2 ==> ~(f3 a = a)) /\
                (xs2 = ADDR_MAP f3 xs) /\ full_heap j j2 m2 /\ c``,
  Induct \\ SIMP_TAC std_ss [ADDR_SET_THM,UNION_EMPTY,rel_move_list_def,ADDR_MAP_def,
    NOT_IN_EMPTY,CUT_EMPTY,LET_DEF,full_heap_REFL] THEN1 SET_TAC
  \\ ONCE_REWRITE_TAC [ADDR_SET_CONS]
  \\ NTAC 6 STRIP_TAC \\ FULL_SIMP_TAC std_ss [UNION_SUBSET]
  \\ `?x3 j3 m3 c3. rel_move (h,j,m,b,e,b2,e2) = (c3,x3,j3,m3)` by METIS_TAC [PAIR]
  \\ `?xs4 j4 m4 c4. rel_move_list (xs,j3,m3,b,e,b2,e2) = (c4,xs4,j4,m4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [UNION_ASSOC] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC move_thm \\ Q.PAT_X_ASSUM `!z roots1 i. bb` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `!z h f.bbb` (MP_TAC o Q.SPECL [
       `z UNION D1(CUT(j,j3)(m3:num -> ('a,'b) heap_element))`,
       `h2`,`f2`,`m3`,`j3`,`xs4`,`j4`,`m4`])
  \\ `ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m3)` by SET_TAC
  \\ FULL_SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IN_UNION]
  \\ Q.LIST_EXISTS_TAC [`h3`,`f3`] \\ `j <= j4` by DECIDE_TAC
  \\ ONCE_REWRITE_TAC [ADDR_SET_CONS] \\ ASM_SIMP_TAC std_ss []
  \\ `(CUT (b,j) m3 = CUT (b,j) m4) /\ (CUT (j,j3) m3 = CUT (j,j3) m4)` by
      (`!k. k < j ==> k < j3` by DECIDE_TAC
       \\ `!k. j <= k ==> b <= k` by RANGE_TAC
       \\ FULL_SIMP_TAC std_ss [CUT_def,RANGE_def,FUN_EQ_THM] \\ SET_TAC)
  \\ IMP_RES_TAC EQ_RANGE_THM \\ IMP_RES_TAC EQ_RANGE_full_heap
  \\ IMP_RES_TAC full_heap_TRANS \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE STRIP_TAC THEN1
   (ASM_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1 SET_TAC \\ STRIP_TAC THEN1 SET_TAC
    \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [ADDR_MAP_def,CONS_11,
      ADDR_SET_def,MEM,heap_address_11] \\ IMP_RES_TAC gc_inv_IMP
    \\ `f2 (f2 n) = n` by FULL_SIMP_TAC std_ss [gc_inv_def,FUN_EQ_THM,abs_gc_inv_def,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [])
  \\ `D1 (CUT (j,j4) m4) = D1 (CUT (j,j3) m4) UNION D1 (CUT (j3,j4) m4)`
       by METIS_TAC [D1_UNION] \\ FULL_SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM]);

val D0_UPDATE = store_thm("D0_UPDATE",
  ``!i x m. i IN D0 m ==> (D0 ((i =+ H_BLOCK x) m) = D0 m)``,
  SIMP_TAC std_ss [FORALL_PROD,FUN_EQ_THM,IN_DEF,D0,CUT_EQ,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val gc_step_lemma = store_thm("gc_step_lemma",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,D1(CUT(i,j)m)) ==> ~(i = j) ==>
    ?xs n d. (m i = H_BLOCK (xs,n,d)) /\
             EMP_RANGE (i + 1,i + n + 1) m /\
             full_heap (i + n + 1) j m /\
             ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m) /\
             (D1 (CUT (i,j) m) = D1 (CUT (i+n+1,j) m) UNION ADDR_SET xs)``,
  SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC gc_inv_IMP
  \\ `full_heap i j m` by METIS_TAC [gc_inv_def] \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [full_heap_cases] \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [heap_element_11] \\ STRIP_TAC THEN1 METIS_TAC [full_heap_cases]
  \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `i < i + n + 1 /\ i <= i + n + 1` by DECIDE_TAC
  \\ `D1 (CUT (i,j) m) = D1 (CUT (i+n+1,j) m) UNION ADDR_SET xs`
       by METIS_TAC [D1_UNION,D1_CUT_EQ_ADDR_SET_THM,UNION_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ `i IN FDOM h /\ (h ' i = (xs,n,d))` by METIS_TAC [gc_inv_def,
       ref_heap_mem_def, heap_element_distinct,heap_element_11,PAIR_EQ]
    \\ `i IN (UNIV DIFF D0 (CUT (b,i) m))` by
      (FULL_SIMP_TAC std_ss [IN_DIFF,IN_UNIV]
       \\ FULL_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,heap_element_11] \\ RANGE_TAC)
    \\ `ADDR_SET xs SUBSET POINTERS h (UNIV DIFF D0 (CUT (b,i) m))`
         by METIS_TAC [set_SUBSET_POINTERS]
    \\ `D0 (CUT (b,i) m) UNION D0 (CUT (i,j) m) = D0 (CUT(b,j)m)`
         by METIS_TAC [D1_UNION,gc_inv_def,abs_gc_inv_def]
    \\ `ADDR_SET xs SUBSET (FDOM h UNION HAS_CHANGED f DIFF (D0 (CUT (b,j) m)))` by
         (FULL_SIMP_TAC std_ss [gc_inv_def,abs_gc_inv_def,LET_DEF] \\ SET_TAC)
    \\ SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC
    \\ `x IN (FDOM h UNION HAS_CHANGED f DIFF D0 (CUT (b,j) m))` by SET_TAC
    \\ Cases_on `x IN FDOM h` THEN1
     (`~(x IN D0 (CUT (b,j) m))` by SET_TAC
      \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ]
      \\ `?x1 y1 d1. h ' x = (x1,y1,d1)` by METIS_TAC [PAIR]
      \\ `m x = H_BLOCK (x1,y1,d1)` by METIS_TAC [ref_heap_mem_def,gc_inv_def]
      \\ FULL_SIMP_TAC std_ss [heap_element_11,DR0,D0,R0,CUT_EQ,
           heap_element_distinct,IN_DEF] \\ CCONTR_TAC
      \\ FULL_SIMP_TAC std_ss [gc_inv_def,abs_gc_inv_def,LET_DEF]
      \\ METIS_TAC [heap_element_distinct])
    \\ FULL_SIMP_TAC std_ss [IN_DIFF,IN_UNION]
    \\ Q.PAT_X_ASSUM `~(x IN D0 (CUT (b,j) m))` MP_TAC
    \\ SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ]
    \\ FULL_SIMP_TAC std_ss [HAS_CHANGED_def]
    \\ FULL_SIMP_TAC std_ss [gc_inv_def,abs_gc_inv_def,LET_DEF]
    \\ `m x = H_REF (f x)` by METIS_TAC [ref_heap_mem_def]
    \\ FULL_SIMP_TAC std_ss [heap_element_distinct,DR0,D0,R0,CUT_EQ,heap_element_11]
    \\ SIMP_TAC std_ss [IN_DEF]
    \\ `full_heap b j m` by METIS_TAC [full_heap_TRANS]
    \\ `R0 m x` by FULL_SIMP_TAC std_ss [R0,heap_element_11]
    \\ CCONTR_TAC \\ METIS_TAC [full_heap_R0,heap_element_distinct]);

val gc_step_thm = store_thm("gc_step_thm",
  ``gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,D1(CUT(i,j)m)) /\ ~(i = j) ==>
    (rel_gc_step (i,j,m,b,e,b2,e2) = (c,i2,j2,m2)) ==>
    ?h3 f3. gc_inv (h1,roots1,h3,f3) (b,i2,j2,e,b2,e2,m2,D1(CUT(i2,j2)m2)) /\
            i < i2 /\ j <= j2 /\ c /\ !a. ~(f a = a) ==> (f3 a = f a)``,
  STRIP_TAC \\ IMP_RES_TAC gc_inv_IMP \\ STRIP_ASSUME_TAC (UNDISCH_ALL gc_step_lemma)
  \\ ASM_SIMP_TAC std_ss [rel_gc_step_def,LET_DEF,getBLOCK_def]
  \\ `?xs3 j3 m3 c3. rel_move_list (xs,j,m,b,e,b2,e2) = (c3,xs3,j3,m3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ helperLib.EXPAND_TAC
  \\ `~RANGE(i + n + 1,j3)i` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [CUT_UPDATE]
  \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `i < i + n + 1 /\ i <= i + n + 1` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `gc_inv (h1,roots1,h,f) xxx` (fn th => ASSUME_TAC th THEN
       MP_TAC (Q.INST [`xs2`|->`xs3`,`j2`|->`j3`,`m2`|->`m3`,`c`|->`c3`]
               (helperLib.MATCH_INST (SPEC_ALL move_list_thm) (concl th))))
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ `CUT (i + n + 1,j) m = CUT (i + n + 1,j) m3` by
    (FULL_SIMP_TAC std_ss [gc_inv_def,abs_gc_inv_def,LET_DEF]
     \\ `!k. i + n + 1 <= k ==> b <= k` by DECIDE_TAC
     \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,CUT_def,RANGE_def] \\ SET_TAC)
  \\ `i + n + 1 <= j` by RANGE_TAC
  \\ `D1 (CUT (i + n + 1,j) m3) UNION D1 (CUT (j,j3) m3) = D1 (CUT (i + n + 1,j3) m3)`
         by METIS_TAC [D1_UNION,gc_inv_def,abs_gc_inv_def]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`h3 |+ (i,ADDR_MAP f3 xs,n,d)`,`f3`]
  \\ `~RANGE(b2,e2)i /\ RANGE(b,j3)i /\ RANGE(b,i+n+1)i` by RANGE_TAC
  \\ FULL_SIMP_TAC std_ss [gc_inv_def,CUT_UPDATE]
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ `i IN D0 (CUT (b,i + n + 1) m3) /\
      (m3 i = H_BLOCK (xs,n,d))` by
     (`!k. k < i + n + 1 ==> k < j` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `CUT (b,i+n+1) m3 = CUT (b,i+n+1) m` by
          (FULL_SIMP_TAC std_ss [CUT_def,RANGE_def] \\ SET_TAC)
      \\ `(CUT(b,i+n+1)m3) i = H_BLOCK (xs,n,d)` by
             (FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [CUT_EQ,IN_DEF])
      \\ FULL_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,heap_element_11])
  \\ REVERSE STRIP_TAC
  THEN1 (ASM_SIMP_TAC std_ss [isBLOCK_def] \\ `RANGE (b,e) i` by RANGE_TAC
         \\ ASM_SIMP_TAC (srw_ss()) []
         \\ `~(i = j3)` by RANGE_TAC
         \\ Q.PAT_X_ASSUM `full_heap i j3 m3` MP_TAC
         \\ ASM_SIMP_TAC (srw_ss()) [Once full_heap_cases]
         \\ REPEAT STRIP_TAC \\ IMP_RES_TAC full_heap_LESS_EQ)
  \\ STRIP_TAC THEN1 RANGE_TAC \\ STRIP_TAC THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [D0_UPDATE]
  \\ STRIP_TAC THEN1
   (MATCH_MP_TAC (RW[AND_IMP_INTRO]full_heap_step)
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_element_11,EMP_RANGE_def,IN_DEF]
    \\ STRIP_TAC THEN1 METIS_TAC [full_heap_BLOCK]
    \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ `RANGE (b,j) k /\ ~(RANGE (i + 1,i + n + 1) i)` by RANGE_TAC \\ SET_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,heap_element_11]
    \\ `~(i = j3)` by RANGE_TAC
    \\ METIS_TAC [full_heap_BLOCK,full_heap_cases,heap_element_11,PAIR_EQ])
  \\ STRIP_TAC THEN1
   (Q.EXISTS_TAC `len'` \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC part_heap_IGNORE \\ ASM_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ref_heap_mem_def,APPLY_UPDATE_THM,FDOM_FUPDATE,IN_INSERT]
    \\ REPEAT STRIP_TAC \\ Cases_on `i = a`
    \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM])
  \\ MATCH_MP_TAC abs_steps_TRANS
  \\ Q.EXISTS_TAC `(h3,D0 (CUT (b,i) m3),D0 (CUT (i,j3) m3),
          D1 (CUT (i + n + 1,j3) m3),f3)` \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [abs_steps_def]
  \\ MATCH_MP_TAC RTC_SINGLE
  \\ SIMP_TAC std_ss [abs_step_cases] \\ DISJ2_TAC \\ DISJ1_TAC
  \\ Q.LIST_EXISTS_TAC [`i`,`xs`,`(n,d)`] \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ok_heap_IMP \\ IMP_RES_TAC abs_steps_thm \\ POP_ASSUM (K ALL_TAC)
  \\ `f3 o f3 = I` by FULL_SIMP_TAC std_ss [gc_inv_def,abs_gc_inv_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_def]
  \\ Q.PAT_X_ASSUM `!a. bbb` (MP_TAC o Q.GEN `a` o Q.SPEC `(f3:num->num) a`)
  \\ `!k. f3 (f3 k) = (k:num)` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SET_EQ_SUBSET,GSYM SUBSET_INSERT_DELETE,INSERT_SUBSET]
  \\ SIMP_TAC std_ss [SUBSET_DEF,IN_INSERT,IN_DELETE]
  \\ `RANGE (i,j3) i` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,heap_element_11]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC [heap_element_distinct,ref_heap_mem_def,heap_element_11,PAIR_EQ]
  THEN1
   (FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,heap_element_11]
    \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `RANGE(i+1,i+n+1)x /\ RANGE(b,j)x` by RANGE_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM] \\ METIS_TAC [heap_element_distinct])
  THEN1 (FULL_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [heap_element_11] \\ RANGE_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [heap_element_11]
    \\ REVERSE (Cases_on `RANGE(i+1,i+n+1)x`) THEN1 RANGE_TAC
    \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,heap_element_11]
    \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM]
    \\ `m x = H_EMP` by SET_TAC
    \\ `RANGE(b,j)x` by RANGE_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM] \\ METIS_TAC [heap_element_distinct]));

val gc_loop_thm = store_thm("gc_loop_thm",
  ``!j h f m i2 m2 c2.
      gc_inv (h1,roots1,h,f) (b,i,j,e,b2,e2,m,D1(CUT(i,j)m)) ==>
      (rel_gc_loop (i,j,m,b,e,b2,e2) = (c2,i2,m2)) ==>
        ?h4 f4. gc_inv (h1,roots1,h4,f4) (b,i2,i2,e,b2,e2,m2,{}) /\ j <= i2 /\ c2 /\
                !a. f a <> a ==> (f4 a = f a)``,
  completeInduct_on `e - i` \\ NTAC 4 STRIP_TAC \\ Cases_on `i = j`
  \\ ONCE_REWRITE_TAC [rel_gc_loop_def] \\ ASM_SIMP_TAC std_ss [CUT_EMPTY] THEN1 SET_TAC
  \\ NTAC 7 STRIP_TAC \\ `?i3 j3 m3 c3. rel_gc_step (i,j,m,b,e,b2,e2) = (c3,i3,j3,m3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC gc_step_thm
  \\ `i < j /\ j <= e` by RANGE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxxx = (c2,i2,m2)` MP_TAC
  \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
  \\ SIMP_TAC bool_ss [PAIR] \\ REPEAT STRIP_TAC
  \\ `(e - i3 < e - i) /\ (e - i3 = e - i3)`  by RANGE_TAC
  \\ RES_TAC \\ IMP_RES_TAC LESS_EQ_TRANS \\ ASM_SIMP_TAC std_ss [] \\ SET_TAC);

val ok_full_heap_def = Define `
  ok_full_heap (h,roots) (b,i,e,b2,e2,m) =
     b <= i /\ i <= e /\ b2 <= e2 /\ (e2 - b2 = e - b) /\ (~(e2 <= b) ==> e <= b2) /\
     (!k. ~RANGE (b,i) k ==> (m k = H_EMP)) /\
     (?t. part_heap b i m t) /\ ref_heap_mem (h,I) m /\ ok_heap (h,roots)`;

val ok_full_heap_IMP = store_thm("ok_full_heap_IMP",
  ``ok_full_heap (h,roots) (b2,i,e2,b,e,m) ==>
    gc_inv (h,roots,h,I) (b,b,b,e,b2,e2,m,ADDR_SET roots) /\
    ADDR_SET roots SUBSET DR0 (CUT (b2,e2) m)``,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [gc_inv_def,ok_full_heap_def,full_heap_REFL]
  \\ IMP_RES_TAC ok_heap_IMP \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [CUT_EMPTY]
  THEN1 (Q.PAT_X_ASSUM `!k.bb` MATCH_MP_TAC \\ RANGE_TAC)
  THEN1 (`part_heap i e2 m 0` by
        (MATCH_MP_TAC part_heap_EMP_RANGE \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
         \\ REPEAT STRIP_TAC \\ `~RANGE (b2,i) k` by RANGE_TAC \\ RES_TAC)
      \\ IMP_RES_TAC part_heap_TRANS \\ Q.EXISTS_TAC `t` \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC part_heap_LENGTH_LESS_EQ)
  \\ SIMP_TAC std_ss [abs_steps_def,RTC_REFL]
  \\ FULL_SIMP_TAC std_ss [ok_heap_def,UNION_SUBSET]
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ SIMP_TAC std_ss [DR0,D0,R0,CUT_EQ,IN_DEF] \\ DISJ1_TAC
  \\ `?x1 x2 x3. h ' x = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ Cases_on `m x` \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def,heap_element_distinct]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [heap_element_11]
  \\ `RANGE (b2,i) x` by METIS_TAC [heap_element_distinct]
  \\ REPEAT STRIP_TAC \\ RANGE_TAC);

val full_heap_IMP_part_heap = store_thm("full_heap_IMP_part_heap",
  ``!b e m. full_heap b e m ==> part_heap b e m (e-b)``,
  HO_MATCH_MP_TAC full_heap_ind \\ REPEAT STRIP_TAC
  THEN1 (SIMP_TAC std_ss [] \\ METIS_TAC [part_heap_cases])
  \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ2_TAC
  \\ ASM_SIMP_TAC std_ss [CUT_EQ,heap_element_11]
  \\ Q.EXISTS_TAC `e - (b + n + 1)` \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC full_heap_LESS_EQ \\ DECIDE_TAC);

val gc_thm = store_thm("gc_thm",
  ``ok_full_heap (h,roots) (b2,i,e2,b,e,m) ==>
    (rel_gc (b2,e2,b,e,roots,m) = (c,b,i2,e,b2,e2,roots2,m2)) ==>
    ?h2. ok_full_heap (h2,roots2) (b,i2,e,b2,e2,m2) /\
         gc_exec (h,roots) (h2,roots2) /\ full_heap b i2 m2 /\ c``,
  STRIP_TAC \\ IMP_RES_TAC ok_full_heap_IMP
  \\ SIMP_TAC std_ss [rel_gc_def,LET_DEF]
  \\ `?r3 b3 m3 c3. rel_move_list (roots,b,m,b,e,b2,e2) = (c3,r3,b3,m3)` by METIS_TAC [PAIR]
  \\ `?i4 m4 c4. rel_gc_loop (b,b3,m3,b,e,b2,e2) = (c4,i4,m4)` by METIS_TAC [PAIR]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (RW [UNION_EMPTY] (helperLib.SUBST_INST [``z:num set``|->``{}:num set``] move_list_thm))
  \\ Q.PAT_X_ASSUM `gc_inv (h,roots,h3,f3) ttt` MP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `gc_inv xxx yyy` (K ALL_TAC)) \\ STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL (RW [] (Q.INST [`c`|->`T`] (SPEC_ALL gc_loop_thm))))
  \\ Q.PAT_X_ASSUM `r3 = ADDR_MAP f3 roots` MP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `r3 = ADDR_MAP xx roots` (K ALL_TAC)) \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `f3 o f3 = I` by
      (FULL_SIMP_TAC std_ss [gc_inv_def]
       \\ IMP_RES_TAC ok_heap_IMP \\ IMP_RES_TAC abs_steps_thm
       \\ FULL_SIMP_TAC std_ss [abs_gc_inv_def,LET_DEF,gc_inv_def])
  \\ Q.PAT_X_ASSUM `gc_inv (h,roots,h4,f4) ttt` MP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `gc_inv xxx yyy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [gc_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `DRESTRICT h4 (D0 (CUT (b,i4) m4))`
  \\ FULL_SIMP_TAC std_ss [CUT_EMPTY] \\ helperLib.CLEAN_TAC
  \\ `gc_exec (h,roots) (DRESTRICT h4 (D0 (CUT (b,i4) m4)),ADDR_MAP f3 roots)` by
      (MATCH_MP_TAC abs_gc_thm \\ ASM_SIMP_TAC std_ss []
       \\ SIMP_TAC std_ss [abs_gc_cases]
       \\ Q.LIST_EXISTS_TAC [`h4`,`f4`,`(D0 (CUT (b,i4) m4))`]
       \\ ASM_SIMP_TAC std_ss [ADDR_MAP_EQ_ADDR_MAP]
       \\ FULL_SIMP_TAC std_ss [SET_TRANSLATE_MAP,SET_TRANSLATE_def]
       \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ SET_TAC)
  \\ IMP_RES_TAC gc_exec_thm \\ ASM_SIMP_TAC std_ss []
  \\ `full_heap b i4 (CUT (b,i4) m4)` by
    (MATCH_MP_TAC full_heap_IGNORE \\ Q.EXISTS_TAC `m4`
     \\ ASM_SIMP_TAC std_ss [CUT_def])
  \\ FULL_SIMP_TAC std_ss [ok_full_heap_def] \\ REPEAT STRIP_TAC
  THEN1 RANGE_TAC THEN1 FULL_SIMP_TAC std_ss [CUT_def,IN_DEF]
  THEN1 METIS_TAC [full_heap_IMP_part_heap,EQ_RANGE_full_heap,EQ_RANGE_CUT]
  \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def,FUN_EQ_THM,FDOM_DRESTRICT,IN_INTER]
  \\ ASM_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ]
  \\ REPEAT STRIP_TAC \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [CUT_def]))
  \\ Cases_on `RANGE (b,i4) a` \\ ASM_SIMP_TAC std_ss [IN_DEF]
  \\ Cases_on `FDOM h4 a` \\ ASM_SIMP_TAC std_ss [IN_DEF] THEN1
     (`?x1 x2 x3. h4 ' a = (x1,x2,x3)` by METIS_TAC [PAIR]
      \\ ASM_SIMP_TAC std_ss [heap_element_11,DRESTRICT_DEF,IN_INTER]
      \\ FULL_SIMP_TAC std_ss [IN_DEF,D0,CUT_EQ,heap_element_11])
  \\ Cases_on `f4 a = a` \\ ASM_SIMP_TAC std_ss [heap_element_distinct]
  \\ FULL_SIMP_TAC std_ss [abs_gc_inv_def,LET_DEF,NOT_IN_EMPTY,IN_UNION]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ `R0 m4 a` by FULL_SIMP_TAC std_ss [R0,IN_DEF,heap_element_11]
  \\ METIS_TAC [full_heap_R0]);

(* split the memory *)

val split_move_def = Define `
  (split_move (H_DATA x,j,mF,mT,e) = (T,H_DATA x,j,mF,mT)) /\
  (split_move (H_ADDR a,j,mF,mT,e) =
     case mF a of
        H_EMP => (F,ARB)
      | H_REF i => (a < e,H_ADDR i,j,mF,mT)
      | H_BLOCK (xs,n,d) => let cond = a < e in
                            let mF = (a =+ H_REF j) mF in
                            let cond = j < e /\ (mT j = H_EMP) /\ cond in
                            let mT = (j =+ H_BLOCK (xs,n,d)) mT in
                              (cond,H_ADDR j,j + n + 1,mF,mT))`;

val split_move_list_def = Define `
  (split_move_list ([],j,mF,mT,e) = (T,[],j,mF,mT)) /\
  (split_move_list (x::xs,j,mF,mT,e) =
     let (c1,x,j,mF,mT) = split_move (x,j,mF,mT,e) in
     let (c2,xs,j,mF,mT) = split_move_list (xs,j,mF,mT,e) in
       (c1 /\ c2,x::xs,j,mF,mT))`;

val split_gc_step_def = Define `
  split_gc_step (i,j,mF,mT,e) =
    let cond = isBLOCK (mT i) /\ i < e in
    let (xs,n,d) = getBLOCK (mT i) in
    let (c2,ys,j,mF,mT) = split_move_list (xs,j,mF,mT,e) in
    let cond = cond /\ (mT i = H_BLOCK (xs,n,d)) /\ c2 in
    let mT = (i =+ H_BLOCK (ys,n,d)) mT in
    let i = i + n + 1 in
    let cond = cond /\ i <= j in
      (cond,i,j,mF,mT)`;

val split_gc_loop_def = tDefine "split_gc_loop" `
  split_gc_loop (i,j,mF,mT,e) =
    if i = j then (T,i,mF,mT) else
    if ~(i < j /\ j <= e) then (F,ARB) else
      let (c1,i,j,mF,mT) = split_gc_step (i,j,mF,mT,e) in
      let (c2,i,mF,mT) = split_gc_loop (i,j,mF,mT,e) in
        (c1 /\ c2,i,mF,mT)`
 (WF_REL_TAC `measure (\(i,j,mF,mT,e). e - i)`
  \\ SIMP_TAC std_ss [split_gc_step_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val split_gc_def = Define `
  split_gc (roots,mF,mT,e) =
    let (cond,roots,j,mF,mT) = split_move_list (roots,0,mF,mT,e) in
    let (c,i,mF,mT) = split_gc_loop (0,j,mF,mT,e) in
    let mT = CUT (0,i) mT in
      (c /\ cond,i,roots,mT,e)`;

(* connection *)

val ADDR_APPLY_def = Define `
  (ADDR_APPLY f (H_ADDR a) = H_ADDR (f a)) /\
  (ADDR_APPLY f (H_DATA x) = H_DATA x)`;

val BLOCK_APPLY_def = Define `
  (BLOCK_APPLY f (H_BLOCK (xs,d)) = H_BLOCK (ADDR_MAP f xs,d)) /\
  (BLOCK_APPLY f (H_REF i) = H_REF i) /\
  (BLOCK_APPLY f (H_EMP) = H_EMP)`;

val memF_def = Define `
  memF m e = \a. if a < e then BLOCK_APPLY (\a. a - e) (m (a+e:num)) else H_EMP`;

val memT_def = Define `
  memT m e i = \a. if e <= a:num then H_EMP else
                   if a < i then m a else BLOCK_APPLY (\a. a - e) (m a)`;

val memF_UPDATE = prove(
  ``(j < e ==> (memF ((j =+ x) m) e = memF m e)) /\
    (RANGE (e,e + e) n ==> (memF ((n =+ x) m) e = (n - e =+ BLOCK_APPLY (\a. a - e) x) (memF m e)))``,
  REPEAT STRIP_TAC THEN1
   (`!a. ~(j = a + e)` by (STRIP_TAC \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [memF_def,APPLY_UPDATE_THM])
  \\ ASM_SIMP_TAC std_ss [memF_def,APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ Cases_on `x' = n - e`
  THEN1 (`n - e < e /\ (n - e + e = n)` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ `~(n = x' + e)` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []);

val memT_UPDATE = prove(
  ``((RANGE (e,e + e) n ==> (memT ((n =+ x) m) e i = memT m e i))) /\
    (i <= j /\ j < e ==>
       (memT ((j =+ x) m) e i = (j =+ BLOCK_APPLY (\a. a - e) x) (memT m e i)))``,
  REPEAT STRIP_TAC THEN1
   (ASM_SIMP_TAC std_ss [memT_def,APPLY_UPDATE_THM,FUN_EQ_THM]
    \\ STRIP_TAC \\ Q.SPEC_TAC (`x'`,`a`)
    \\ STRIP_TAC \\ Cases_on `e <= a` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `a < i` \\ ASM_SIMP_TAC std_ss []
    \\ `~(n = a)` by RANGE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [memT_def,APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ STRIP_TAC \\ Q.SPEC_TAC (`x'`,`a`) \\ STRIP_TAC
  \\ Cases_on `j = a` \\ ASM_SIMP_TAC std_ss []
  \\ `~(e <= a) /\ ~(a < i)` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []);

val spilt_move_thm = prove(
  ``(rel_move (x,j,m,0,e,e,e+e) = (T,x2,j2,m2)) /\ i <= j ==>
    (split_move (ADDR_APPLY (\a. a - e) x,j,memF m e,memT m e i,e) =
       (T,x2,j2,memF m2 e,memT m2 e i)) /\ j <= j2``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REVERSE (Cases_on `x`)
  \\ SIMP_TAC std_ss [rel_move_def,split_move_def,ADDR_APPLY_def]
  \\ Cases_on `m n` \\ ASM_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC THEN1
   (`memF m e (n - e) = H_REF n'` by
     (FULL_SIMP_TAC std_ss [memF_def]
      \\ `n < e + e /\ 0 < e /\ (n - e + e = n)` by RANGE_TAC
      \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_def])
    \\ ASM_SIMP_TAC (srw_ss()) [] \\ RANGE_TAC)
  \\ `?xs n d. p = (xs,n,d)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ `n < e + e /\ 0 < e /\ (n - e + e = n) /\ j < e /\ ~(n = j)` by RANGE_TAC
  \\ `memF m e (n - e) = H_BLOCK (ADDR_MAP (\a. a - e) xs,n',d)` by
   (ASM_SIMP_TAC std_ss [memF_def]
    \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_def])
  \\ ASM_SIMP_TAC (srw_ss()) [DECIDE ``j <= j + n + 1``]
  \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [memT_def,BLOCK_APPLY_def,APPLY_UPDATE_THM])
  \\ ASM_SIMP_TAC std_ss [memF_UPDATE,BLOCK_APPLY_def,memT_UPDATE]);

val ADDR_MAP_CONS = prove(
  ``!x xs f. ADDR_MAP f (x::xs) = ADDR_APPLY f x :: ADDR_MAP f xs``,
  Cases \\ ASM_SIMP_TAC std_ss [ADDR_APPLY_def,ADDR_MAP_def]);

val spilt_move_list_thm = prove(
  ``!xs j m xs2 j2 m2.
      (rel_move_list (xs,j,m,0,e,e,e+e) = (T,xs2,j2,m2)) /\ i <= j ==>
      (split_move_list (ADDR_MAP (\a. a - e) xs,j,memF m e,memT m e i,e) =
         (T,xs2,j2,memF m2 e,memT m2 e i))``,
  Induct \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [rel_move_list_def,ADDR_MAP_def,split_move_list_def]
  \\ NTAC 3 STRIP_TAC
  \\ `?c1 x1 j1 m1. rel_move (h,j,m,0,e,e,e + e) = (c1,x1,j1,m1)` by METIS_TAC [PAIR]
  \\ `?c3 xs3 j3 m3. rel_move_list (xs,j1,m1,0,e,e,e + e) = (c3,xs3,j3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC spilt_move_thm
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_CONS,split_move_list_def,LET_DEF]
  \\ `i <= j1` by DECIDE_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val spilt_gc_step_thm = prove(
  ``(rel_gc_step (i,j,m,0,e,e,e+e) = (T,i2,j2,m2)) /\ i <= j /\ i <= e ==>
    (split_gc_step (i,j,memF m e,memT m e i,e) = (T,i2,j2,memF m2 e,memT m2 e i2)) /\ i2 <= j2 /\ i < i2``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [rel_gc_step_def,split_gc_step_def]
  \\ `?xs n d. getBLOCK (m i) = (xs,n,d)` by METIS_TAC [PAIR]
  \\ `?c3 xs3 j3 m3. rel_move_list (xs,j,m,0,e,e,e + e) = (c3,xs3,j3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DECIDE ``i < i + n + 1:num``]
  \\ IMP_RES_TAC spilt_move_list_thm
  \\ Q.PAT_X_ASSUM `!x.bb` (K ALL_TAC)
  \\ `i < e` by RANGE_TAC
  \\ `~(e <= i)` by RANGE_TAC
  \\ `memT m e i i = H_BLOCK (ADDR_MAP (\a. a - e) xs,n,d)` by
   (ASM_SIMP_TAC std_ss [memT_def] \\ Cases_on `m i`
    \\ FULL_SIMP_TAC (srw_ss()) [isBLOCK_def,getBLOCK_def,BLOCK_APPLY_def])
  \\ ASM_SIMP_TAC std_ss [getBLOCK_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1 METIS_TAC [isBLOCK_def]
  \\ ASM_SIMP_TAC std_ss [memF_UPDATE]
  \\ ASM_SIMP_TAC std_ss [memT_def,BLOCK_APPLY_def]
  \\ SIMP_TAC std_ss [FUN_EQ_THM,APPLY_UPDATE_THM] \\ STRIP_TAC
  \\ Cases_on `i = a` \\ ASM_SIMP_TAC std_ss []
  THEN1 (`~(e <= a) /\ a < a + n + 1` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `e <= a` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `a < i` \\ ASM_SIMP_TAC std_ss []
  THEN1 (`a < i + n + 1` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `a < i + n + 1` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF]
  \\ `RANGE (i + 1,i + n + 1) a` by RANGE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [BLOCK_APPLY_def]);

val spilt_gc_loop_thm = prove(
  ``!i e j m i2 m2.
      (rel_gc_loop (i,j,m,0,e,e,e+e) = (T,i2,m2)) /\ i <= j ==>
      (split_gc_loop (i,j,memF m e,memT m e i,e) = (T,i2,memF m2 e,memT m2 e i2))``,
  completeInduct_on `e-i:num` \\ NTAC 7 STRIP_TAC
  \\ ONCE_REWRITE_TAC [split_gc_loop_def,rel_gc_loop_def]
  \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `i < j` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `j <= e` \\ ASM_SIMP_TAC std_ss []
  \\ `?c3 i3 j3 m3. rel_gc_step (i,j,m,0,e,e,e + e) = (c3,i3,j3,m3)` by METIS_TAC [PAIR]
  \\ `?c4 i4 m4. rel_gc_loop (i3,j3,m3,0,e,e,e + e) = (c4,i4,m4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ `i <= e /\ i < j` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC spilt_gc_step_thm \\ REPEAT (Q.PAT_X_ASSUM `!x y.bb` (K ALL_TAC))
  \\ ASM_SIMP_TAC std_ss []
  \\ `e - i3 < e - i /\ (e - i3 = e - i3)` by DECIDE_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val spilt_gc_thm = prove(
  ``(rel_gc (e,e+e,0,e,roots,m) = (T,b2,i2,e2,x1,x2,roots2,m2)) ==>
    (split_gc (ADDR_MAP (\a. a - e) roots,memF m e,memT m e 0,e) = (T,i2,roots2,m2,e))``,
  SIMP_TAC std_ss [rel_gc_def,LET_DEF] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ `?c1 xs1 j1 m1. rel_move_list (roots,0,m,0,e,e,e + e) = (c1,xs1,j1,m1)` by METIS_TAC [PAIR]
  \\ `?c2 i2 m2. rel_gc_loop (0,j1,m1,0,e,e,e + e) = (c2,i2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [split_gc_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (RW [LESS_EQ_REFL] (Q.INST [`i`|->`0`] (Q.SPECL [`xs`,`0`] spilt_move_list_thm)))
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC (RW [DECIDE ``0 <= n:num``] (Q.SPEC `0` spilt_gc_loop_thm))
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [memT_def,CUT_def]
  \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `e <= k` \\ ASM_SIMP_TAC std_ss [RANGE_def,BLOCK_APPLY_def]
  \\ SRW_TAC [] [] \\ `F` by DECIDE_TAC);

val split_lemma = prove(
  ``ok_full_heap (h,roots) (e,i,e+e,0,e,m) ==>
    ?h2 m2 i2 roots2.
       (split_gc (ADDR_MAP (\a. a - e) roots,memF m e,memT m e 0,e) = (T,i2,roots2,m2,e)) /\
       ok_full_heap (h2,roots2) (0,i2,e,e,e + e,m2) /\ gc_exec (h,roots) (h2,roots2) /\
       full_heap 0 i2 m2``,
  REPEAT STRIP_TAC
  \\ `?i2 m2 roots2 c. (rel_gc (e,e + e,0,e,roots,m) = (c,0,i2,e,e,e + e,roots2,m2))` by
       (SIMP_TAC std_ss [rel_gc_def,LET_DEF]
        \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
        \\ SIMP_TAC std_ss [])
  \\ IMP_RES_TAC gc_thm \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC spilt_gc_thm \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val memI_def = Define `
  memI m e = (\a. if a < e then H_EMP else BLOCK_APPLY (\a. a + e) (m (a - e)))`;

val heapI_def = Define `
  heapI h e = FUN_FMAP (\a. getBLOCK (BLOCK_APPLY (\a. a + e) (H_BLOCK (h ' (a - e)))))
                       (\a. if a < e then F else (a - e:num) IN FDOM h)`;

val ADDR_MAP_ID = prove(
  ``!xs g f. (g o f = I) ==> (ADDR_MAP g (ADDR_MAP f xs) = xs)``,
  Induct \\ SIMP_TAC std_ss [ADDR_MAP_def] \\ Cases
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,FUN_EQ_THM]);

val BLOCK_APPLY_ID = prove(
  ``!h g. (h o g = I) ==> !x. BLOCK_APPLY h (BLOCK_APPLY g x) = x``,
  REPEAT STRIP_TAC \\ Cases_on `x`
  \\ FULL_SIMP_TAC std_ss [BLOCK_APPLY_def,FUN_EQ_THM]
  \\ Q.SPEC_TAC (`p`,`p`) \\ ASM_SIMP_TAC std_ss [FORALL_PROD,BLOCK_APPLY_def]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [FUN_EQ_THM] ADDR_MAP_ID)
  \\ ASM_SIMP_TAC std_ss []);

val part_heap_memI = prove(
  ``!k b e m t.
      part_heap b e m t ==>
      part_heap (b + k) (e + k) (memI m k) t``,
  STRIP_TAC \\ HO_MATCH_MP_TAC part_heap_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [part_heap_cases] \\ ASM_SIMP_TAC std_ss [] THEN1
   (DISJ2_TAC \\ DISJ1_TAC \\ FULL_SIMP_TAC std_ss [memI_def]
    \\ ASM_SIMP_TAC std_ss [DECIDE ``~(b+k<k:num)``]
    \\ STRIP_TAC THEN1
     (Cases_on `m b` \\ ASM_SIMP_TAC (srw_ss()) [isBLOCK_def,BLOCK_APPLY_def]
      \\ Cases_on `p` \\ Cases_on `r`
      \\ FULL_SIMP_TAC (srw_ss()) [isBLOCK_def,BLOCK_APPLY_def])
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ FULL_SIMP_TAC (srw_ss()) [memI_def,BLOCK_APPLY_def,DECIDE ``~(b+k<k:num)``,
       isBLOCK_def,AC ADD_COMM ADD_ASSOC] \\ REPEAT (Q.EXISTS_TAC `t`)
  \\ FULL_SIMP_TAC (srw_ss()) [AC ADD_COMM ADD_ASSOC,BLOCK_APPLY_def]
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `a < k` \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ `RANGE (b + 1,b + (n + 1)) (a - k)` by RANGE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [AC ADD_COMM ADD_ASSOC,BLOCK_APPLY_def]);

val FINITE_heapI = prove(
  ``FINITE (\a. ~(a < e) /\ a - (e:num) IN FDOM h)``,
  SUBGOAL `(\a. ~(a < e) /\ a - (e:num) IN FDOM h) =
           (IMAGE (\a. a + e) (FDOM h)) DIFF {a | (a < e)}`
  \\ ASM_SIMP_TAC std_ss []
  THEN1 METIS_TAC [FINITE_DIFF,IMAGE_FINITE,FDOM_FINITE]
  \\ ASM_SIMP_TAC std_ss [EXTENSION,IN_DIFF,GSPECIFICATION,IN_IMAGE]
  \\ ASM_SIMP_TAC std_ss [IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `x < e` \\ ASM_SIMP_TAC std_ss []
  \\ `!a. (x = a + e) = (a = x - e)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val FDOM_heapI = prove(
  ``!h a e. a IN FDOM (heapI h e) = ~(a < e) /\ a - e IN FDOM h``,
  SIMP_TAC std_ss [heapI_def,FUN_FMAP_DEF,FINITE_heapI]
  \\ SIMP_TAC std_ss [IN_DEF]);

val APPLY_heapI = prove(
  ``!a h e.
      a IN FDOM (heapI h e) ==>
      (heapI h e ' a = getBLOCK (BLOCK_APPLY (\a. a + e) (H_BLOCK (h ' (a - e)))))``,
  SIMP_TAC std_ss [heapI_def,FUN_FMAP_DEF,FINITE_heapI]);

val IN_ADDR_SET_ADDR_MAP_LEMMA = prove(
  ``!xs x e.
      x IN ADDR_SET (ADDR_MAP (\a. a + e) xs) ==>
      ~(x < e) /\ x - e IN ADDR_SET xs``,
  Induct \\ SIMP_TAC std_ss [ADDR_SET_def,ADDR_MAP_def,MEM] \\ Cases
  \\ FULL_SIMP_TAC (srw_ss()) [ADDR_SET_def,ADDR_MAP_def,MEM]
  \\ REVERSE (NTAC 3 STRIP_TAC) THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val ok_full_heap_IMP_heapI = store_thm("ok_full_heap_IMP_heapI",
  ``ok_full_heap (h,roots) (0,i,e,e,e+e,m) ==>
    ok_full_heap (heapI h e,
                  ADDR_MAP (\a. a + e) roots)
                 (e,e+i,e+e,0,e,memI m e) /\
    (memF (memI m e) e = m) /\
    (memT (memI m e) e 0 = \x.H_EMP)``,
  FULL_SIMP_TAC std_ss [ok_full_heap_def] \\ REPEAT STRIP_TAC
  THEN1
   (Cases_on `k < e` \\ ASM_SIMP_TAC std_ss [memI_def]
    \\ `~RANGE (0,i) (k - e)` by RANGE_TAC
    \\ RES_TAC \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_def])
  THEN1
   (Q.EXISTS_TAC `t` \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ MATCH_MP_TAC (RW [ADD_CLAUSES] (Q.SPECL [`e`,`0`,`i`] part_heap_memI))
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (FULL_SIMP_TAC std_ss [ref_heap_mem_def,memI_def,APPLY_heapI]
    \\ FULL_SIMP_TAC std_ss [FDOM_heapI] \\ REPEAT STRIP_TAC
    \\ Cases_on `a < e` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `a - e IN FDOM h` \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_def]
    \\ Cases_on `h ' (a - e)` \\ Cases_on `r`
    \\ FULL_SIMP_TAC std_ss [BLOCK_APPLY_def,getBLOCK_def])
  THEN1
   (FULL_SIMP_TAC std_ss [ok_heap_def,memI_def,APPLY_heapI]
    \\ FULL_SIMP_TAC std_ss [POINTERS_def,SUBSET_DEF,IN_UNION,IN_UNIV]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 METIS_TAC [IN_ADDR_SET_ADDR_MAP_LEMMA,FDOM_heapI]
    \\ Q.PAT_X_ASSUM `b IN FDOM (heapI h e)` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [APPLY_heapI]
    \\ Q.PAT_X_ASSUM `xxx = (zs,d)` MP_TAC
    \\ `?xs n2 d2. h ' (b - e) = (xs,n2,d2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [BLOCK_APPLY_def,getBLOCK_def]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC IN_ADDR_SET_ADDR_MAP_LEMMA
    \\ METIS_TAC [IN_ADDR_SET_ADDR_MAP_LEMMA,FDOM_heapI])
  THEN1
   (SIMP_TAC std_ss [memF_def,FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ Cases_on `x < e` \\ ASM_SIMP_TAC std_ss [] THEN1
     (`~(x + e < e)` by RANGE_TAC \\ ASM_SIMP_TAC std_ss [memI_def]
      \\ SUBGOAL `(\a. a - e) o (\a. a + e:num) = I`
      THEN1 METIS_TAC [BLOCK_APPLY_ID]
      \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM])
    \\ `~RANGE (0,i) x` by RANGE_TAC \\ METIS_TAC [])
  THEN
   (SIMP_TAC std_ss [memT_def,FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ Cases_on `e <= x` \\ ASM_SIMP_TAC std_ss [memI_def]
    \\ Cases_on `x < e` \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_def]
    \\ `(\a. a - e) o (\a. a + e:num) = I` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ ASM_SIMP_TAC std_ss [BLOCK_APPLY_ID]
    \\ `~RANGE (0,i) (x-e)` by RANGE_TAC \\ METIS_TAC []));

val split_gc_thm = store_thm("split_gc_thm",
  ``ok_full_heap (h,roots) (0,i,e,e,e+e,m) ==>
    ?h2 m2 i2 roots2.
       (split_gc (roots,m,(\x.H_EMP),e) = (T,i2,roots2,m2,e)) /\
       ok_full_heap (h2,roots2) (0,i2,e,e,e + e,m2) /\
       full_heap 0 i2 m2 /\
       gc_exec (heapI h e,ADDR_MAP (\a. a + e) roots) (h2,roots2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ok_full_heap_IMP_heapI
  \\ IMP_RES_TAC split_lemma \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `(\a. a - e) o (\a. a + e:num) = I` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_ID] \\ METIS_TAC []);


(* representation of s-expressions in abstract heap, given symbol-table sym *)

open lisp_sexpTheory;

val LIST_FIND_def = Define `
  (LIST_FIND n x [] = NONE) /\
  (LIST_FIND n x (y::ys) = if x = y then SOME n else LIST_FIND (n+1) x ys)`;

val LIST_FIND_LESS_EQ = store_thm("LIST_FIND_LESS_EQ",
  ``!xs x k d. (LIST_FIND k x xs = SOME d) ==> k <= d``,
  Induct \\ SIMP_TAC std_ss [LIST_FIND_def,APPEND] \\ REPEAT STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val lisp_x_def = Define `
  (lisp_x (m,sym) (a,Val k) =
        (a = H_DATA (INL ((n2w k):word30))) /\ k < 2**30) /\
  (lisp_x (m,sym) (a,Sym s) =
    ?k. (LIST_FIND 0 s sym = SOME k) /\
        (a = H_DATA (INR ((n2w k):29 word))) /\ k < 2**29) /\
  (lisp_x (m,sym) (a,Dot x y) =
    ?ax ay k.
        (a = H_ADDR k) /\ (m k = H_BLOCK ([ax;ay],0,())) /\
        lisp_x (m,sym) (ax,x) /\ lisp_x (m,sym) (ay,y))`

val ADDR_MAP_TWICE = prove(
  ``!xs. ADDR_MAP f (ADDR_MAP g xs) = ADDR_MAP (f o g) xs``,
  Induct \\ SIMP_TAC std_ss [ADDR_MAP_def] \\ Cases
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def]);

val EL_ADDR_MAP = prove(
  ``!xs k. k < LENGTH xs ==> (EL k (ADDR_MAP f xs) = ADDR_APPLY f (EL k xs))``,
  Induct \\ SIMP_TAC std_ss [LENGTH] \\ Cases \\ Cases
  \\ ASM_SIMP_TAC std_ss [LENGTH,ADDR_APPLY_def,ADDR_MAP_def,EL,HD,TL]);

val ADDR_APPLY_EQ_DATA = prove(
  ``!x y f. (ADDR_APPLY f x = H_DATA y) = (x = H_DATA y)``,
  Cases \\ SRW_TAC [] [ADDR_APPLY_def]);

val PAIR_TRANSLATE_FLIP = prove(
  ``!x y f. (f o f = I) ==> ((PAIR_TRANSLATE f x = y) = (x = PAIR_TRANSLATE f y))``,
  SIMP_TAC std_ss [FORALL_PROD,PAIR_TRANSLATE_def] \\ METIS_TAC [ADDR_MAP_ID]);

val ADDR_MAP_THM = prove(
  ``!xs f. ADDR_MAP f xs = MAP (ADDR_APPLY f) xs``,
  Induct \\ SIMP_TAC std_ss [ADDR_MAP_def,ADDR_APPLY_def,MAP] \\ Cases
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_def,ADDR_APPLY_def,MAP]);

val lisp_x_gc_thm = store_thm("lisp_x_gc_thm",
  ``ok_full_heap (h,roots) (0,i,e,e,e+e,m) /\ k < LENGTH roots /\
    (split_gc (roots,m,(\x.H_EMP),e) = (c2,i2,roots2,m2,e)) ==>
    lisp_x (m,sym) (EL k roots,x) ==>
    lisp_x (m2,sym) (EL k roots2,x)``,
  STRIP_TAC
  \\ IMP_RES_TAC split_gc_thm
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ Q.PAT_X_ASSUM `k < LENGTH roots` MP_TAC
  \\ Q.PAT_X_ASSUM `ok_full_heap (h2,roots2) (0,i2,e,e,e + e,m2)` MP_TAC
  \\ IMP_RES_TAC ok_full_heap_IMP_heapI
  \\ Q.PAT_X_ASSUM `ok_full_heap (heapI h e,yy) xxx` MP_TAC
  \\ Q.SPEC_TAC (`heapI h e`,`h1`) \\ STRIP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [gc_exec_def,gc_copy_def,gc_filter_def]
  \\ FULL_SIMP_TAC std_ss [ADDR_MAP_TWICE,EL_ADDR_MAP]
  \\ `?r. EL k roots = r` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss []
  \\ `ADDR_SET (ADDR_MAP (\a. a + e) [r]) SUBSET gc_reachable (h1,ADDR_MAP (\a. a + e) roots)` by
   (REVERSE (Cases_on `r`)
    \\ SIMP_TAC std_ss [ADDR_MAP_def,ADDR_SET_THM,EMPTY_SUBSET,INSERT_SUBSET]
    \\ SIMP_TAC std_ss [IN_DEF] \\ ONCE_REWRITE_TAC [gc_reachable_cases] \\ DISJ1_TAC
    \\ SIMP_TAC std_ss [ADDR_SET_def]
    \\ `MEM (H_ADDR n) roots` by METIS_TAC [rich_listTheory.EL_IS_EL]
    \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `roots` \\ SIMP_TAC std_ss [MEM] \\ Cases
    \\ SIMP_TAC (srw_ss()) [ADDR_MAP_def] \\ METIS_TAC [])
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ Q.SPEC_TAC (`r`,`r`) \\ Q.SPEC_TAC (`x`,`x`)
  \\ REVERSE Induct
  THEN1 (SIMP_TAC std_ss [lisp_x_def,ADDR_APPLY_EQ_DATA])
  THEN1 (SIMP_TAC std_ss [lisp_x_def,ADDR_APPLY_EQ_DATA])
  \\ SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [ADDR_APPLY_def]
  \\ `(k' + e) IN FDOM h1 /\ (h1 ' (k' + e) = (ADDR_MAP (\a. a + e) [ax; ay],0,()))` by
   (Q.PAT_X_ASSUM `ok_full_heap (h1,ADDR_MAP (\a. a + e) roots) xxx` MP_TAC
    \\ SIMP_TAC std_ss [ok_full_heap_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def]
    \\ Q.PAT_X_ASSUM `!a.bbb` (MP_TAC o Q.SPEC `k' + e`)
    \\ ASM_SIMP_TAC std_ss [memI_def,BLOCK_APPLY_def,DECIDE ``~(k+e<e:num)``]
    \\ Cases_on `k' + e IN FDOM h1` \\ ASM_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [ADDR_MAP_def,INSERT_SUBSET,EMPTY_SUBSET,ADDR_SET_THM]
  \\ FULL_SIMP_TAC std_ss [FDOM_DRESTRICT,IN_INTER]
  \\ `h1 ' (k' + e) = PAIR_TRANSLATE f (h2 ' (f (k' + e)))` by
   (RES_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [DRESTRICT_DEF,FDOM_DRESTRICT,IN_INTER] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `f o f = I` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [PAIR_TRANSLATE_FLIP]
  \\ FULL_SIMP_TAC std_ss [PAIR_TRANSLATE_def,ADDR_MAP_TWICE]
  \\ `(f (k' + e)) IN FDOM h2` by
    (FULL_SIMP_TAC std_ss [EXTENSION,SET_TRANSLATE_def,IN_INTER] \\ RES_TAC)
  \\ `m2 (f (k' + e)) = H_BLOCK (h2 ' (f (k' + e)))` by
    (FULL_SIMP_TAC std_ss [ok_full_heap_def,ref_heap_mem_def])
  \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [ADDR_MAP_THM,MAP] \\ STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC THEN1
   (Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `!x.bbb` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def]
    \\ Cases_on `ax` \\ FULL_SIMP_TAC (srw_ss()) [MEM,ADDR_MAP_def]
    \\ SIMP_TAC std_ss [IN_DEF]
    \\ ONCE_REWRITE_TAC [gc_reachable_cases] \\ DISJ2_TAC
    \\ SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `k' + e`
    \\ ASM_SIMP_TAC std_ss [PAIR_TRANSLATE_def,ADDR_SET_def,MEM,ADDR_MAP_def]
    \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,IN_DEF])
  THEN1
   (Q.PAT_X_ASSUM `!x.bbb` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def]
    \\ Cases_on `ay` \\ FULL_SIMP_TAC (srw_ss()) [MEM,ADDR_MAP_def]
    \\ SIMP_TAC std_ss [IN_DEF]
    \\ ONCE_REWRITE_TAC [gc_reachable_cases] \\ DISJ2_TAC
    \\ SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `k' + e`
    \\ ASM_SIMP_TAC std_ss [PAIR_TRANSLATE_def,ADDR_SET_def,MEM,ADDR_MAP_def]
    \\ SIMP_TAC std_ss [ADDR_MAP_THM,MAP,MEM,ADDR_APPLY_def]
    \\ FULL_SIMP_TAC std_ss [ADDR_MAP_THM,FUN_EQ_THM,IN_DEF]));


val _ = export_theory();
