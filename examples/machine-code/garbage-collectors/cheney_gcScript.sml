
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory finite_mapTheory;


val _ = new_theory "cheney_gc";
val _ = ParseExtras.temp_loose_equality()

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val bool_ss = bool_ss -* ["lift_disj_eq", "list_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "list_imp_disj"]

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

(* -- abstraction -- *)

val SUBSET0_DEF = new_infixr_definition
    ("SUBSET0_DEF", “SUBSET0 s t = s SUBSET (0 INSERT t)”,451);

val SUBSET0_TRANS = store_thm("SUBSET0_TRANS",
  ``!x y z. x SUBSET0 y /\ y SUBSET0 z ==> x SUBSET0 z``,
  REWRITE_TAC [SUBSET0_DEF,SUBSET_DEF,IN_INSERT] \\ METIS_TAC []);

val _ = Hol_datatype `
  heap_type = EMP | REF of num | DATA of num # num # 'a`;

val isREF_def = Define `isREF x = ?i. x = REF i`;
val getREF_def = Define `getREF (REF x) = x`;
val getDATA_def = Define `getDATA (DATA y) = y`;

val heap_type_distinct = fetch "-" "heap_type_distinct"
val heap_type_11 = fetch "-" "heap_type_11"

val RANGE_def = Define `RANGE(i:num,j) k = i <= k /\ k < j`;
val IRANGE_def = Define `IRANGE(i:num,j) k = ~(i <= k /\ k < j)`;

val CUT_def = Define `CUT (i,j) m = \k. if RANGE (i,j) k then m k else EMP`;
val ICUT_def = Define `ICUT (i,j) m = \k. if IRANGE (i,j) k then m k else EMP`;

val D0 = Define `D0 m k = ?x y z. m (k:num) = DATA(x,y,z)`;
val D1 = Define `D1 m x = ?k y z. (m (k:num) = DATA(x,y,z)) \/ (m k = DATA(y,x,z))`;
val R0 = Define `R0 m k = ?a. m (k:num) = REF a`;
val R1 = Define `R1 m a = ?k. m (k:num) = REF a`;
val DR0 = Define `DR0 m k = D0 m k \/ R0 m k`
val DR1 = Define `DR1 m k = D1 m k \/ R1 m k`

val ADDR_def = Define `
  (ADDR k n EMP = (n = k)) /\
  (ADDR k n (REF i) = (n = i)) /\
  (ADDR k n (DATA x) = (n = k))`;

val abs_def = Define `
  abs m (a,n,n',d) =
    ?k k'. (m a = DATA(k,k',d)) /\ ADDR k n (m k) /\ ADDR k' n' (m k')`;

val basic_abs = Define `
  basic_abs m (a,n,n',d) = (m a = DATA(n,n',d))`;

val apply_def = Define `apply h s (a,n,n',d) = (h a,h n,h n',d) IN s`;

val PATH_def = Define `
  (PATH (x,[]) s = T) /\
  (PATH (x,y::ys) s = PATH (y,ys) s /\ ?z d. (x,y,z,d) IN s \/ (x,z,y,d) IN s)`;

val reachable_def = Define `
  reachable r s i = (r = i) \/ ?p. PATH (r,p++[i]) s`;

val UPDATE_thm = prove(
  ``!a b. a =+ b = (\f k. (if k = a then b else f k))``,
  SIMP_TAC std_ss [UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val roots_inv_def = Define `
  roots_inv (b,j,m,xx) =
    ?v. (v o v = I) /\ (xx = apply v (abs m)) /\
        (!k. ~isREF(m k) /\ ~RANGE(b,j)k ==> (v k = k)) /\
        (!k i. (m k = REF i) ==> (v k = i))`;

val cheney_inv_def = Define `
  cheney_inv(b,b',i,j,j',e,f,m,x,xx,r) =
    (0 < b /\ b <= b' /\ b' <= j /\ b <= i /\ i <= j /\ j <= e /\ e <= f) /\
    (!k. j <= k /\ k < e \/ f < k ==> (m k = EMP)) /\    (* all EMP between j and e *)
    (D0(CUT(b,j)m) = RANGE(b,j)) /\                      (* all DATA between b and j *)
    (D1(CUT(b,i)m) SUBSET0 RANGE(b,j)) /\                (* b-i links only to b-j and nil *)
    (RANGE(i,j') SUBSET (r UNION D1(CUT(b,i)m))) /\      (* every i-j is linked to by some b-i *)
    (D1(CUT(i,j)m) SUBSET0 DR0(ICUT(b,e)m)) /\           (* i-j links only outside of b-e *)
    (D1(ICUT(b,e)m) SUBSET0 DR0(ICUT(b,e)m)) /\          (* outside of b-e links only to outside b-e *)
    (R1(m) = RANGE(b,j)) /\                              (* all REFs refer to b-j elements *)
    (!i j k. (m i = REF k) /\ (m j = REF k) ==> (i = j)) /\ (* REFs are injective *)
    (CARD(D0(ICUT(b,e)m)) <= e-j) /\                     (* num of elements outside b-e fit into e-j *)
    FINITE (D0(ICUT(b,e)m)) /\                           (* the set is finite *)
    (m 0 = EMP) /\                                       (* 0 points at no data *)
    RANGE(b,i) SUBSET                                    (* all of b-i is reachable from r *)
    (\x. ?t. t IN r /\ x IN reachable t (basic_abs(CUT(b,i)m))) /\
    (!k i. (x k = REF i) ==> (m k = REF i)) /\           (* refernces are reserved *)
    roots_inv (b,j,m,abs xx)                             (* memory is permuted *)`;

val ok_state_def = Define `
  ok_state (i,e,r,l,u,m) =
    let a = (if u then 1 + l else 1) in
    let s = RANGE(a,i) in
        a <= i /\ i <= e /\ (e = a + l) /\
        (!k. MEM k r /\ ~(k = 0) ==> k IN s) /\
        (!k. ~(k IN s) ==> (m k = EMP)) /\
        (!k. k IN s ==> ?x y d. (m k = DATA(x,y,d)) /\ {x;y} SUBSET0 s)`;

val move_def = Define `
  move(x,j,m) =
    if x = 0 then (x,j,m) else
    if isREF (m x) then (getREF (m x),j,m) else
      let m = (j =+ m x) m in
      let m = (x =+ REF j) m in
        (j,j+1,m)`;

val cheney_step_def = Define `
  cheney_step (i,j,e,m) =
    let (x,y,d) = getDATA (m i) in
    let (x,j,m) = move (x,j,m) in
    let (y,j,m) = move (y,j,m) in
    let m = (i =+ DATA (x,y,d)) m in
      (i+1,j,e,m)`;

val cheney_def = tDefine "cheney" `
  cheney(i,j,e,m) =
    if (i = j) \/ e < i then (i,m) else
      cheney(cheney_step(i,j,e,m))`
 (WF_REL_TAC `measure (\(i,j,e,m). (e + 1) - i)`
  \\ REWRITE_TAC [cheney_step_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
  \\ REWRITE_TAC [FST,SND] \\ DECIDE_TAC);

val cheney_ind = fetch "-" "cheney_ind";

val m_DATA = store_thm("m_DATA",
  ``cheney_inv(b,b',i,j,j',e,f,m,x,xx,r) /\ ~(i = j) ==> ?ax ay ad. m i = DATA (ax,ay,ad)``,
  SIMP_TAC std_ss [cheney_inv_def,FUN_EQ_THM,D0,IN_DEF,RANGE_def,CUT_def]
  \\ REPEAT STRIP_TAC \\ `b <= i /\ i < j` by DECIDE_TAC \\ METIS_TAC []);

val IN_EQ_SUBSET =
  GEN_ALL (GSYM (REWRITE_CONV [INSERT_SUBSET,EMPTY_SUBSET] ``{i:'a} SUBSET x``));

val RANGE_IRANGE = prove(
  ``!b e x y. RANGE (b,e) x /\ IRANGE (b,e) y ==> ~(x = y)``,
  REWRITE_TAC [RANGE_def,IRANGE_def] \\ DECIDE_TAC);

val RANGE_expand = prove(
  ``!i j k x. RANGE (i,j) x /\ j <= k ==> RANGE (i,k) x``,
  REWRITE_TAC [RANGE_def,IRANGE_def] \\ DECIDE_TAC);

val RANGE_expand_left = prove(
  ``!i j k x. RANGE (i,j) x /\ k <= i ==> RANGE (k,j) x``,
  REWRITE_TAC [RANGE_def,IRANGE_def] \\ DECIDE_TAC);

val CUT_update = prove(
  ``~RANGE (i,j) k ==> (CUT (i,j) ((k =+ x) m) = CUT (i,j) m)``,
  SIMP_TAC std_ss [CUT_def,UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val ICUT_update = prove(
  ``~IRANGE (i,j) k ==> (ICUT (i,j) ((k =+ x) m) = ICUT (i,j) m)``,
  SIMP_TAC std_ss [ICUT_def,UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val update_update = prove(
  ``!m i x y. (i =+ y) ((i =+ x) m) = (i=+ y) m``,
  SIMP_TAC std_ss [FUN_EQ_THM,UPDATE_def]);

val expand_CUT = prove(
  ``RANGE (a,b) SUBSET RANGE (c,d) /\ (CUT(c,d)m=CUT(c,d)n) ==> (CUT(a,b)m=CUT(a,b)n)``,
  SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,FUN_EQ_THM,RANGE_def,CUT_def] \\ METIS_TAC []);

val D1_SUBSET0 = prove(
  ``D1 (CUT(j,j+1)m) SUBSET0 s /\ D1 (CUT(i,j)m) SUBSET0 s ==>
    D1 (CUT(i,j+1)m) SUBSET0 s``,
  REWRITE_TAC [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ SIMP_TAC std_ss [IN_DEF,D1,CUT_def,RANGE_def,DECIDE ``k<n+1=k<=n``]
  \\ METIS_TAC [DECIDE ``n <= k \/ k < n:num``,fetch "-" "heap_type_distinct"]);

val swap_def = Define `
  swap i j = \k. if k = i then j else if k = j then i else k`;

val swap_swap = store_thm("swap_swap",
  ``!i:'a j. swap i j o swap i j = I``,
  SIMP_TAC std_ss [swap_def,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ Cases_on `x = i` \\ Cases_on `x = j` \\ Cases_on `i = j`
  \\ ASM_SIMP_TAC std_ss []);

val swap_swap2 = prove(
  ``!i:'a j x. swap i j (swap i j x) = x``,
  SIMP_TAC std_ss [swap_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `x = i` \\ Cases_on `x = j` \\ Cases_on `i = j`
  \\ ASM_SIMP_TAC std_ss []);

val swap_id = prove(
  ``!i j k. ~(i = k) /\ ~(j = k) ==> (swap i j k = k)``,
  SIMP_TAC std_ss [swap_def]);

val apply_apply = store_thm("apply_apply",
  ``!s f g. apply f (apply g s) = apply (g o f) s``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ SIMP_TAC std_ss [apply_def,IN_DEF]);

val apply_I = store_thm("apply_I",
  ``!s. apply I s = s``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ SIMP_TAC std_ss [apply_def,IN_DEF]);

val RANGE_IMP_NOT_DR0 = prove(
  ``!i j x m. RANGE (i,j) x ==> ~DR0 (ICUT(i,j)m) x``,
  SIMP_TAC std_ss [DR0,D0,R0,ICUT_def,IRANGE_def,RANGE_def,heap_type_distinct]);

val D0_IMP = prove(
  ``D0 (CUT (b,j) m) i ==> ?h g dd. RANGE(b,j)i /\ (m i = DATA(h,g,dd))``,
  SIMP_TAC std_ss [D0,CUT_def] \\ METIS_TAC [heap_type_distinct]);

val D1_IMP = prove(
  ``D1 (CUT (b,i) m) j ==>
    ?h g dd. RANGE(b,i)h /\ (~(m h = DATA(j,g,dd)) ==> (m h = DATA(g,j,dd)))``,
  SIMP_TAC std_ss [D1,CUT_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `k` \\ Cases_on `RANGE (b,i) k`
  \\ FULL_SIMP_TAC std_ss [heap_type_distinct,heap_type_11] \\ METIS_TAC []);

val lemma2 = prove(
  ``k IN D1 m /\ ~(j = x) /\ IRANGE(b,e)x /\ ~(j = e) /\
    cheney_inv (b,b',i,j,j',e,f,m,w,xx,r) /\ (m x = DATA (n',n'',d')) /\ (m j = EMP) ==>
      (ADDR k (swap j x t) (((x =+ REF j) ((j =+ (DATA (n',n'',d'))) m)) k) =
       ADDR k t (m k))``,
  SIMP_TAC std_ss [UPDATE_def,swap_def] \\ Cases_on `k = j` \\ ASM_REWRITE_TAC [] THENL [
    REPEAT STRIP_TAC
    \\ `{j} SUBSET D1 m` by METIS_TAC [IN_EQ_SUBSET] \\ FULL_SIMP_TAC std_ss [cheney_inv_def]
    \\ `{j} SUBSET (D1 (ICUT (b,e) m)) \/ {j} SUBSET (D1 (CUT (b,i) m)) \/
        {j} SUBSET (D1 (CUT (i,j) m)) \/ {j} SUBSET (D1 (CUT (j,e) m))` by
     (FULL_SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF,D1,GSYM RANGE_def]
      \\ SIMP_TAC std_ss [CUT_def,ICUT_def]
      \\ `IRANGE(b,e)k' \/ RANGE(b,i)k' \/ RANGE(i,j)k' \/ RANGE(j,e)k'` by
         (REWRITE_TAC [RANGE_def,IRANGE_def] \\ DECIDE_TAC)
      \\ METIS_TAC [heap_type_distinct])
    THENL [
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]
      \\ `{j} SUBSET 0 INSERT DR0 (ICUT (b,e) m)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF] THEN1 `F` by DECIDE_TAC
      \\ `RANGE (b,e) j` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC RANGE_IMP_NOT_DR0,
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]
      \\ `{j} SUBSET 0 INSERT RANGE (b,j)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF,RANGE_def]
      \\ `F` by DECIDE_TAC,
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]
      \\ `{j} SUBSET 0 INSERT DR0 (ICUT (b,e) m)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF] THEN1 `F` by DECIDE_TAC
      \\ `RANGE (b,e) j` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC RANGE_IMP_NOT_DR0,
      FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF,D1,CUT_def,RANGE_def]
      \\ `F` by METIS_TAC [heap_type_distinct]],
    Cases_on `k = x` \\ ASM_SIMP_TAC std_ss [ADDR_def] THEN1 METIS_TAC []
    \\ Cases_on `m k` \\ ASM_REWRITE_TAC [ADDR_def] THENL [
      Cases_on `t = j` \\ Cases_on `t = x` \\ FULL_SIMP_TAC bool_ss [],
      REPEAT STRIP_TAC
      \\ `~(n = x)` by
       (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
        \\ `{x} SUBSET R1 m` by (SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF] \\ METIS_TAC [R1])
        \\ `{x} SUBSET RANGE (b,j)` by METIS_TAC [cheney_inv_def,SUBSET_TRANS]
        \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,RANGE_def,IRANGE_def,cheney_inv_def]
        \\ DECIDE_TAC)
      \\ `~(n = j)` by
       (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
        \\ `{j} SUBSET R1 m` by (SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF] \\ METIS_TAC [R1])
        \\ `{j} SUBSET RANGE (b,j)` by METIS_TAC [cheney_inv_def,SUBSET_TRANS]
        \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,RANGE_def,IRANGE_def,cheney_inv_def]
        \\ DECIDE_TAC)
      \\ METIS_TAC [],
      Cases_on `t = j` \\ Cases_on `t = x` \\ FULL_SIMP_TAC bool_ss []]]);

val lemma = prove(
  ``(m x = DATA (n',n'',d')) /\ (m j = EMP) ==>
    (((x =+ REF j) ((j =+ DATA (n',n'',d')) m) (swap j x a) = DATA (k,k',v)) =
     (m a = DATA (k,k',v)))``,
  SIMP_TAC std_ss [UPDATE_def,swap_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Cases_on `a = j` \\ FULL_SIMP_TAC bool_ss [swap_def,heap_type_distinct]
  \\ Cases_on `a = x` \\ FULL_SIMP_TAC bool_ss [swap_def,heap_type_11,PAIR_EQ]);

val move_lemma_lemma = prove(
  ``!d' b b' i j j' e m w r x n' n''.
    (m x = DATA (n',n'',d')) /\ (m j = EMP) /\ ~(j = e) /\
    cheney_inv (b,b',i,j,j',e,f,m,w,xx,r) /\ IRANGE (b,e) x /\ ~(x = 0) ==>
      (apply (swap j x) (abs((x =+ REF j) ((j =+ m x) m))) = abs m)``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a t u v. x' = (a,t,u,v)` by METIS_TAC [PAIR_EQ,PAIR]
  \\ ASM_SIMP_TAC std_ss [apply_def,IN_DEF,abs_def,lemma]
  \\ `~(j = x)` by (FULL_SIMP_TAC bool_ss [IRANGE_def,cheney_inv_def] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `k` \\ Q.EXISTS_TAC `k'`
  \\ `k IN D1 m /\ k' IN D1 m` by (SIMP_TAC std_ss [IN_DEF,D1] \\ METIS_TAC [])
  \\ ASSUME_TAC (GSYM (UNDISCH_ALL (RW [GSYM AND_IMP_INTRO] (Q.INST [`d`|->`v`] lemma2))))
  \\ ASSUME_TAC (GSYM (UNDISCH_ALL (RW [GSYM AND_IMP_INTRO]
       (Q.INST [`d`|->`v`,`k`|->`k'`,`t`|->`u`] lemma2))))
  \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val move_lemma2 = prove(
  ``!i j s t. (apply (swap i j) s = t) = (s = apply (swap i j) t)``,
  REWRITE_TAC [apply_def,swap_def,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ POP_ASSUM (ASSUME_TAC o
       Q.SPECL [`(swap i j q,swap i j q',swap i j q'',r)`])
  \\ FULL_SIMP_TAC std_ss [apply_def,swap_def,IN_DEF]
  \\ Cases_on `q= i` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `q'= i` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `q''= i` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `q= j` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `q'= j` \\ FULL_SIMP_TAC bool_ss []
  \\ Cases_on `q''= j` \\ FULL_SIMP_TAC bool_ss []);

val cheney_inv_CUT_lemma = prove(
  ``cheney_inv (b,b',i,j,j3,e,f,m,w,xx,r) /\ ~(j = e) /\ IRANGE(b,e)x ==>
    (RANGE (b,i) SUBSET RANGE (b,j)) /\ ~RANGE(b,j+1)x /\ ~RANGE(b,i)j /\ ~RANGE(b,i)x /\
    (RANGE (b,j+1) SUBSET RANGE (b,e)) /\ RANGE (b,j) SUBSET0 RANGE (b,j + 1) /\
    (RANGE (i,j+1) SUBSET RANGE (b,j+1)) /\ ~RANGE(i,j+1)x /\ ~RANGE(b,b')j /\ ~RANGE(b,b')x /\
    ~RANGE(i,j)j /\ ~RANGE(b,e)x /\ ~RANGE(b,j)j /\ ~RANGE(b,j)x``,
  FULL_SIMP_TAC bool_ss [SUBSET_DEF,SUBSET0_DEF,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [IN_DEF,cheney_inv_def,RANGE_def,IRANGE_def]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val RANGE_simp = prove(
  ``!i j k. ~(i = j) ==> (RANGE(k,i+1)j = RANGE(k,i)j)``,
  SIMP_TAC bool_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC);

Theorem move_lemma:
  cheney_inv (b,b',i,j,j3,e,f,m,w,xx,r) /\ {x} SUBSET0 DR0(ICUT(b,e)m) ==>
  (move(x,j,m) = (x2,j2,m2)) ==>
  cheney_inv(b,b',i,j2,j3,e,f,m2,w,xx,r) /\ {x2} SUBSET0 RANGE(b,j2) /\
  j <= j2 /\
  (CUT(b,j)m = CUT(b,j)m2) /\ (DR0 (ICUT(b,e)m) = DR0 (ICUT(b,e)m2)) /\
  (if x = 0 then x2 = 0 else (m2 x = REF x2) /\ D0 (CUT(b,j2)m2) x2) /\
  (!a i. (m a = REF i) ==> (m2 a = REF i)) /\
  (if ~(x = 0) /\ (m2 x = REF j) then j2 = j + 1 else j2 = j) /\
  (~(x = 0) /\ ~isREF (m x) ==> (abs m = apply (swap j x) (abs m2))) /\ x <= f
Proof
  Cases_on `x = 0` \\ ASM_SIMP_TAC bool_ss [move_def,PAIR_EQ,LESS_EQ_REFL]
  \\ ASM_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [ZERO_LESS_EQ])
  \\ STRIP_TAC
  \\ `x <= f` by
   (Cases_on `IRANGE (b,e) x` \\ FULL_SIMP_TAC bool_ss [IN_DEF,DR0,D0,R0,
      ICUT_def,heap_type_distinct,cheney_inv_def,DECIDE ``x < j = ~(j <= x:num)``]
    \\ METIS_TAC [heap_type_distinct]) \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `isREF (m x)` \\ ASM_REWRITE_TAC []
  THEN1
   (FULL_SIMP_TAC bool_ss [isREF_def,getREF_def,PAIR_EQ]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ,SUBSET_REFL,LESS_EQ_REFL]
    \\ ASM_SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC bool_ss [cheney_inv_def,heap_type_11] THENL [
      Q.PAT_X_ASSUM `R1 m = RANGE (b,j)` (fn th => REWRITE_TAC [GSYM th]) \\ DISJ2_TAC
      \\ SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,R1] \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [cheney_inv_def,SUBSET_DEF,IN_DEF]
      \\ `R1 m i'` by (REWRITE_TAC [R1] \\ METIS_TAC []) \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [cheney_inv_def,SUBSET_DEF,IN_DEF]
      \\ `~RANGE (b,i') i'` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ `R1 m i'` by (REWRITE_TAC [R1] \\ METIS_TAC []) \\ METIS_TAC []])
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
  \\ `IRANGE (b,e) x /\ ?t u v. m x = DATA (t,u,v)` by
    (FULL_SIMP_TAC bool_ss [IN_DEF,DR0,isREF_def,D0,R0,ICUT_def]
     \\ Cases_on `IRANGE (b,e) x`
     \\ FULL_SIMP_TAC bool_ss [heap_type_distinct] \\ METIS_TAC [])
  \\ `~(j = e)` by
    (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [DECIDE ``m <= n - n = (m = 0)``,cheney_inv_def]
     \\ `x IN D0 (ICUT(b,e)m)`
          by (FULL_SIMP_TAC bool_ss [IN_DEF,D0,ICUT_def] \\ METIS_TAC[])
     \\ METIS_TAC [CARD_EQ_0,NOT_IN_EMPTY])
  \\ `ICUT(b,e) ((x =+ (REF j)) ((j =+ m x) m)) =
      ICUT(b,e) ((x =+ (REF j)) m)` by
     (Cases_on `x = j` \\ ASM_REWRITE_TAC [update_update]
      \\ SIMP_TAC std_ss [ICUT_def,FUN_EQ_THM,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `IRANGE (b,e) x'` \\ ASM_REWRITE_TAC []
      \\ Cases_on `x = x'` \\ ASM_REWRITE_TAC []
      \\ `~(j = x')` by (FULL_SIMP_TAC bool_ss [cheney_inv_def,IRANGE_def] \\ DECIDE_TAC)
      \\ ASM_REWRITE_TAC [])
  \\ `abs ((x =+ REF j) ((j =+ DATA (t,u,v)) m)) = apply (swap j x) (abs m)` by
       (Q.PAT_X_ASSUM `m x = DATA (t,u,v)` (fn th => REWRITE_TAC [GSYM th] \\ ASSUME_TAC th)
        \\ REWRITE_TAC [GSYM move_lemma2]
        \\ MATCH_MP_TAC (GEN_ALL move_lemma_lemma)
        \\ Q.EXISTS_TAC `xx` \\ Q.EXISTS_TAC `f` \\ Q.EXISTS_TAC `v`
        \\ Q.EXISTS_TAC `b` \\ Q.EXISTS_TAC `b'` \\ Q.EXISTS_TAC `i`
        \\ Q.EXISTS_TAC `j3` \\ Q.EXISTS_TAC `e` \\ Q.EXISTS_TAC `w`
        \\ Q.EXISTS_TAC `r` \\ Q.EXISTS_TAC `t` \\ Q.EXISTS_TAC `u`
        \\ FULL_SIMP_TAC std_ss [cheney_inv_def]
        \\ `j <= j /\ j < e` by DECIDE_TAC
        \\ METIS_TAC [])
  \\ IMP_RES_TAC cheney_inv_CUT_lemma
  \\ REPEAT (Q.PAT_X_ASSUM `!tyu.fgh` (fn th => ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [cheney_inv_def]
  \\ ASM_SIMP_TAC bool_ss [CUT_update,apply_apply,swap_swap,apply_I]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
  THEN1
     (`~(k = j) /\ ~(k = x)` by (FULL_SIMP_TAC bool_ss [IRANGE_def] \\ DECIDE_TAC)
      \\ ASM_SIMP_TAC bool_ss [UPDATE_def] \\ METIS_TAC [DECIDE ``j + 1 <= k ==> j <= k``])
  THEN1
     (`~(k = j) /\ ~(x = k)` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [UPDATE_def])
  THEN1
     (ASM_SIMP_TAC std_ss [FUN_EQ_THM,D0,CUT_def,RANGE_def,IN_DEF]
      \\ STRIP_TAC \\ Cases_on `x' = j` \\ ASM_REWRITE_TAC []
      \\ ASM_SIMP_TAC std_ss [UPDATE_def] THEN1 METIS_TAC [heap_type_distinct]
      \\ ASM_SIMP_TAC bool_ss [DECIDE ``~(x = n) ==> (x < n + 1 = x < n)``]
      \\ REWRITE_TAC [GSYM RANGE_def]
      \\ Cases_on ` RANGE (b,j) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
      \\ FULL_SIMP_TAC bool_ss [D0,FUN_EQ_THM,CUT_def] \\ METIS_TAC [])
  THEN1
     (MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `RANGE (b,j)` \\ ASM_REWRITE_TAC [])
  THEN1
     (Q.PAT_X_ASSUM `m x = DATA (t,u,v)` (ASSUME_TAC o GSYM) \\ ASM_REWRITE_TAC []
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `DR0 (ICUT (b,e) m)`
      \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ STRIP_TAC THEN1
       (REWRITE_TAC [DR0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
        \\ SIMP_TAC std_ss [IN_DEF,DR0,UPDATE_def,ICUT_def,FUN_EQ_THM,D0,R0]
        \\ STRIP_TAC \\ Cases_on `IRANGE (b,e) x'`
        \\ ASM_REWRITE_TAC [heap_type_distinct] \\ METIS_TAC [])
      \\ MATCH_MP_TAC D1_SUBSET0 \\ ASM_SIMP_TAC bool_ss [CUT_update]
      \\ Q.PAT_X_ASSUM `DATA (t,u,v) = m x` (ASSUME_TAC o GSYM) \\ ASM_REWRITE_TAC []
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `{t;u}` \\ STRIP_TAC THEN1
       (REWRITE_TAC [DR0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,CUT_def]
        \\ SIMP_TAC std_ss [IN_DEF,DR0,UPDATE_def,ICUT_def,FUN_EQ_THM,D0,R0]
        \\ SIMP_TAC std_ss [RANGE_def,DECIDE ``j <= k /\ k < j+1 = (j = k)``,D1]
        \\ REPEAT (POP_ASSUM (fn th => ALL_TAC))
        \\ REPEAT STRIP_TAC \\ Cases_on `j = k`
        \\ FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ,heap_type_distinct])
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `D1 (ICUT (b,e) m)` \\ STRIP_TAC THEN1
       (REWRITE_TAC [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
        \\ MATCH_MP_TAC (METIS_PROVE [] ``x /\ y ==> (t \/ x) /\ (d:bool \/ y)``)
        \\ SIMP_TAC std_ss [IN_DEF,D1,ICUT_def] \\ METIS_TAC [])
      \\ ASM_REWRITE_TAC [])
  THEN1
     (MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `D1 (ICUT (b,e) m)` \\ STRIP_TAC THEN1
       (REWRITE_TAC [DR0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,CUT_def,D1]
        \\ SIMP_TAC std_ss [IN_DEF,DR0,UPDATE_def,ICUT_def,FUN_EQ_THM,D0,R0,D1]
        \\ METIS_TAC [heap_type_11,PAIR_EQ,heap_type_distinct])
      \\ MATCH_MP_TAC SUBSET0_TRANS
      \\ Q.EXISTS_TAC `DR0 (ICUT (b,e) m)` \\ ASM_REWRITE_TAC []
      \\ REWRITE_TAC [DR0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,CUT_def,D1]
      \\ SIMP_TAC std_ss [IN_DEF,DR0,UPDATE_def,ICUT_def,FUN_EQ_THM,D0,R0]
      \\ METIS_TAC [heap_type_11,PAIR_EQ,heap_type_distinct])
  THEN1
     (`j < e` by DECIDE_TAC
      \\ `m j = EMP` by METIS_TAC [LESS_EQ_REFL]
      \\ sg `!xx. R1 ((x =+ REF j) ((j =+ DATA (t,u,v)) m)) xx = (j = xx) \/ R1 m xx`
      THENL [ALL_TAC,ASM_SIMP_TAC bool_ss [FUN_EQ_THM,RANGE_def] \\ DECIDE_TAC]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC bool_ss [R1,UPDATE_def] THENL [
        Cases_on `x = k` \\ FULL_SIMP_TAC bool_ss [heap_type_11]
        \\ Cases_on `j = k` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct] \\ METIS_TAC [],
        Q.EXISTS_TAC `x` \\ METIS_TAC [],
        Q.EXISTS_TAC `k` \\ Cases_on `k = x` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]
        \\ Cases_on `j = k` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]])
  THEN1
   (Cases_on `k = j` THENL [
      Cases_on `i' = x` THENL [ALL_TAC,
        Cases_on `j = i'` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
        \\ FULL_SIMP_TAC bool_ss [FUN_EQ_THM,R1] \\ METIS_TAC []]
      \\ Cases_on `j' = x` THENL [ALL_TAC,
        Cases_on `j = j'` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
        \\ FULL_SIMP_TAC bool_ss [FUN_EQ_THM,R1] \\ METIS_TAC []]
      \\ ASM_SIMP_TAC bool_ss [],
      `m i' = REF k` by
       (Cases_on `x = i'` \\ Cases_on `j = i'`
        \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct,heap_type_11] \\ METIS_TAC [])
      \\ `m j' = REF k` by
       (Cases_on `x = j'` \\ Cases_on `j = j'`
        \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct,heap_type_11] \\ METIS_TAC [])
      \\ METIS_TAC []])
  THEN1
     (REWRITE_TAC [SUB_PLUS]
      \\ `D0 (ICUT (b,e) ((x =+ REF j) m)) = D0 (ICUT (b,e) m) DELETE x` by
       (REWRITE_TAC [EXTENSION,IN_DELETE]
        \\ SIMP_TAC std_ss [IN_DEF,ICUT_def,D0,UPDATE_def] \\ STRIP_TAC
        \\ Cases_on `IRANGE (b,e) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
        \\ Cases_on `x' = x` \\ ASM_REWRITE_TAC [heap_type_distinct]
        \\ simp[])
      \\ ASM_SIMP_TAC bool_ss [CARD_DELETE]
      \\ `x IN D0 (ICUT (b,e) m)` by
        (ASM_SIMP_TAC std_ss [IN_DEF,D0,ICUT_def] \\ METIS_TAC [])
      \\ ASM_SIMP_TAC bool_ss [] \\ DECIDE_TAC)
  THEN1
     (`D0 (ICUT (b,e) ((x =+ REF j) m)) = D0 (ICUT (b,e) m) DELETE x` by
       (REWRITE_TAC [EXTENSION,IN_DELETE]
        \\ SIMP_TAC std_ss [IN_DEF,ICUT_def,D0,UPDATE_def] \\ STRIP_TAC
        \\ Cases_on `IRANGE (b,e) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
        \\ Cases_on `x = x'` \\ ASM_REWRITE_TAC [heap_type_distinct] \\ METIS_TAC [])
      \\ ASM_SIMP_TAC std_ss [FINITE_DELETE])
  THEN1
     (`~(0 = j)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
     (`j < e` by DECIDE_TAC
      \\ `(m j = EMP) /\ (m k = REF i')` by METIS_TAC [LESS_EQ_REFL]
      \\ Cases_on `k = j` THEN1 METIS_TAC [heap_type_distinct]
      \\ Cases_on `k = x` THEN1 METIS_TAC [heap_type_distinct]
      \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
     (FULL_SIMP_TAC bool_ss [roots_inv_def]
      \\ ASM_REWRITE_TAC [apply_apply]
      \\ Q.EXISTS_TAC `swap j x o v'` \\ REWRITE_TAC []
      \\ REWRITE_TAC [GSYM (SIMP_CONV std_ss [] ``(f o g) o h``),swap_swap]
      \\ SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [UPDATE_def]
      \\ `m j = EMP` by METIS_TAC [LESS_OR_EQ,LESS_EQ_REFL,cheney_inv_def]
      \\ `~isREF(m j) /\ ~isREF(m x)` by METIS_TAC [heap_type_distinct,isREF_def]
      \\ `(v' j = j) /\ (v' x = x)` by METIS_TAC []
      \\ STRIP_TAC THEN1
       (SIMP_TAC std_ss [FUN_EQ_THM,swap_def] \\ STRIP_TAC
        \\ `!k. v' (v' k) = k` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
       \\ Cases_on `x' = r''` \\ Cases_on `x' = h` \\ METIS_TAC [])
      \\ STRIP_TAC THENL [
        STRIP_TAC \\ Cases_on `x = k` \\ ASM_SIMP_TAC bool_ss [isREF_def,heap_type_11]
        \\ Cases_on `k = j` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]
        \\ REPEAT STRIP_TAC THENL [
          `b <=i /\ i <= j ==> RANGE(b,j+1)j` by (REPEAT (POP_ASSUM (K ALL_TAC))
             \\ SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
          \\ METIS_TAC [],
          `~RANGE(b,j)k` by METIS_TAC [RANGE_simp]
          \\ `v' k = k` by METIS_TAC [isREF_def]
          \\ ASM_SIMP_TAC bool_ss [swap_def]],
        STRIP_TAC \\ Cases_on `k = x` \\ ASM_SIMP_TAC bool_ss [heap_type_11]
        THEN1 (SIMP_TAC std_ss [swap_def] \\ METIS_TAC [])
        \\ Cases_on `k = j` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]
        \\ REPEAT STRIP_TAC \\ `v' k = i'` by METIS_TAC []
        \\ ASM_SIMP_TAC std_ss []
        \\ `R1 m i'` by METIS_TAC [R1]
        \\ `RANGE(b,j)i'` by METIS_TAC [cheney_inv_def]
        \\ `~(j = i') /\ ~(x = i')` by METIS_TAC []
        \\ ASM_SIMP_TAC std_ss [swap_def]])
  THEN1 (SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC)
  THEN1
     (ASM_SIMP_TAC std_ss [DR0,D0,R0,ICUT_def,FUN_EQ_THM,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `IRANGE (b,e) x'` \\ ASM_REWRITE_TAC []
      \\ Cases_on `x = x'` \\ ASM_SIMP_TAC std_ss [heap_type_11] THEN1 METIS_TAC [])
  THEN1 (IMP_RES_TAC LESS_EQ_TRANS
         \\ ASM_SIMP_TAC std_ss [D0,CUT_def,RANGE_def,UPDATE_def] \\ METIS_TAC [])
  THEN1
     (Cases_on `a = x` \\ FULL_SIMP_TAC bool_ss [] THEN1 METIS_TAC [heap_type_distinct]
      \\ `j < e` by DECIDE_TAC
      \\ `m j = EMP` by METIS_TAC [LESS_EQ_REFL]
      \\ Cases_on `a = j` \\ FULL_SIMP_TAC bool_ss [] THEN1 METIS_TAC [heap_type_distinct]
      \\ ASM_SIMP_TAC std_ss [UPDATE_def])
QED

val abs_update_lemma = prove(
  ``!m i x y d x' y'.
      (m i = DATA (x,y,d)) /\ (m 0 = EMP) /\
      (if x = 0 then x' = 0 else (m x = REF x') /\ D0 m x') /\
      (if y = 0 then y' = 0 else (m y = REF y') /\ D0 m y') ==>
      (abs ((i =+ DATA (x',y',d))m) = abs m)``,
  REWRITE_TAC [FUN_EQ_THM,D0] \\ REPEAT STRIP_TAC
  \\ `?a0 x0 y0 D0. x'' = (a0,x0,y0,D0)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC bool_ss [abs_def,UPDATE_thm]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
    Cases_on `a0 = i` THENL [
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      THENL [Cases_on `x = 0`,Cases_on `y = 0`]
      \\ FULL_SIMP_TAC bool_ss [ADDR_def] \\ METIS_TAC [ADDR_def],
      FULL_SIMP_TAC std_ss [heap_type_11]
      \\ Cases_on `k = i` \\ Cases_on `k' = i`
      \\ FULL_SIMP_TAC bool_ss [ADDR_def]],
    Cases_on `a0 = i` THENL [
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      THENL [Cases_on `x = 0`,Cases_on `y = 0`]
      \\ FULL_SIMP_TAC bool_ss [ADDR_def] \\ METIS_TAC [ADDR_def],
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      \\ Cases_on `k = i` \\ Cases_on `k' = i`
      \\ FULL_SIMP_TAC bool_ss [ADDR_def] \\ METIS_TAC [ADDR_def]]]);

val maintain_lemma = prove(
  ``!b i j j2 m x y.
      b <= i /\ i <= j /\
      RANGE (i,j) SUBSET (r UNION D1 (CUT (b,i) m)) /\
      RANGE (j,j2) SUBSET {x;y} ==>
      RANGE (i + 1,j2) SUBSET (r UNION D1 (CUT (b,i + 1) ((i =+ DATA (x,y,d)) m)))``,
  SIMP_TAC bool_ss [SUBSET_DEF,IN_UNION,NOT_IN_EMPTY,IN_INSERT]
  \\ SIMP_TAC bool_ss [IN_DEF,D1,CUT_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `r x'` \\ ASM_REWRITE_TAC []
  \\ sg `RANGE (j,j2) x' \/ RANGE (i,j) x'` THENL [
    FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC,
    `RANGE (b,i + 1) i` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `i` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_type_11] \\ METIS_TAC [],
    RES_TAC \\ Cases_on `RANGE(b,i)k` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]
    \\ `RANGE (b,i + 1) k /\ ~(i = k)` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `k` \\ ASM_SIMP_TAC std_ss [UPDATE_def,heap_type_11] \\ METIS_TAC []]);

val RANGE_split = prove(
  ``j <= j' ==> j' <= j'' ==> (RANGE(j,j'') = RANGE (j,j') UNION RANGE(j',j''))``,
  REWRITE_TAC [EXTENSION,IN_UNION] \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val RANGE_lemmas = store_thm("RANGE_lemmas",
  ``!n. (RANGE(n,n+1) = {n}) /\ (RANGE(n,n) = {})``,
  REWRITE_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
  \\ SIMP_TAC bool_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC);

val PATH_CUT_expand = prove(
  ``!p r b i j m. PATH (r,p) (basic_abs(CUT (b,i) m)) /\ i <= j ==>
                  PATH (r,p) (basic_abs(CUT (b,j) m))``,
  Induct \\ REWRITE_TAC [PATH_def] \\ REPEAT STRIP_TAC
  \\ `RANGE (b,i) r ==> RANGE (b,j) r` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [CUT_def,basic_abs,IN_DEF]
  \\ METIS_TAC [heap_type_distinct]);

val reachable_CUT_expand = prove(
  ``!r b i j m. reachable r (basic_abs (CUT (b,i) m)) x /\ i <= j ==>
                reachable r (basic_abs (CUT (b,j) m)) x``,
  SIMP_TAC bool_ss [reachable_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [PATH_CUT_expand]);

val CUT_EQ_EMP_IMP = prove(
  ``(CUT (b,i) m x = EMP) /\ RANGE(b,i)x ==> (m x = EMP)``,
  SIMP_TAC std_ss [D0,CUT_def] \\ METIS_TAC []);

val PATH_snoc = prove(
  ``!ys x y z m. PATH(x,ys++[y])m /\ PATH(y,[z])m ==> PATH(x,ys++[y]++[z])m``,
  Induct THEN1 (REWRITE_TAC [APPEND,PATH_def] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [PATH_def,APPEND]);

val move_IMP = prove(
  ``!x j m x' j' m'. (move (x,j,m) = (x',j',m')) ==> j <= j'``,
  SIMP_TAC std_ss [move_def,LET_DEF] \\ NTAC 6 STRIP_TAC
  \\ Cases_on `x = 0` \\ ASM_SIMP_TAC std_ss [PAIR_EQ]
  \\ Cases_on `isREF (m x)` \\ ASM_SIMP_TAC std_ss [PAIR_EQ]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [] \\ DECIDE_TAC);

val cheney_inv_step = store_thm("cheney_inv_step",
  ``cheney_inv(b,b',i,j,j,e,f,m,w,xx,r) /\ ~(i = j) /\
    (cheney_step(i,j,e,m) = (i2,j2,e2,m2)) ==> (e2 = e) /\ j <= j2 /\
    cheney_inv(b,b',i2,j2,j2,e2,f,m2,w,xx,r)``,
  REWRITE_TAC [cheney_step_def]
  \\ `?x y d. getDATA (m i) = (x,y,d)` by METIS_TAC [PAIR]
  \\ `?x' j' m'. move (x,j,m) = (x',j',m')` by METIS_TAC [PAIR]
  \\ `?y' j'' m''. move (y,j',m') = (y',j'',m'')` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC bool_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `i + 1 = i2` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `j'' = j2` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `e = e2` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `(i =+ DATA (x',y',d)) m'' = m2` (K ALL_TAC)
  \\ `i <= e` by (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `_ <> _` (ASSUME_TAC o GSYM)
  \\ `?ax ay ad. m i = DATA (ax,ay,ad)` by METIS_TAC [m_DATA]
  \\ `~IRANGE (b,e) i /\ i + 1 <= j /\ b <= i /\ i <= j /\ ~RANGE(b,i)i /\ RANGE(i,j) i` by
     (FULL_SIMP_TAC bool_ss [cheney_inv_def,IRANGE_def,RANGE_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [getDATA_def,PAIR_EQ]
  \\ `{x;y} SUBSET0 D1 (CUT(i,j)m)` by
   (SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,D1,RANGE_def,cheney_inv_def,CUT_def]
    \\ `i <= i /\ i < j` by DECIDE_TAC
    \\ STRIP_TAC \\ DISJ2_TAC \\ Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [])
  \\ `{x;y} SUBSET0 DR0 (ICUT(b,e)m)` by
    (MATCH_MP_TAC SUBSET0_TRANS \\ METIS_TAC [cheney_inv_def])
  \\ `{x} SUBSET0 DR0 (ICUT(b,e)m)` by
    FULL_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ IMP_RES_TAC move_lemma
  \\ `{y} SUBSET0 DR0 (ICUT(b,e)m')` by
    FULL_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ IMP_RES_TAC move_lemma
  \\ Q.PAT_X_ASSUM `cheney_inv (b,b',i,j,j,e,f,m,w,xx,r)` (fn th => ALL_TAC)
  \\ Q.PAT_X_ASSUM `cheney_inv (b,b',i,j',j,e,f,m',w,xx,r)` (fn th => ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [cheney_inv_def]
  \\ ASM_SIMP_TAC bool_ss [ICUT_update] THEN1 DECIDE_TAC
  \\ REPEAT STRIP_TAC
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  THEN1
   (`~(k = i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
   (`~(k = i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
   (sg `D0 (CUT (b,j'') ((i =+ DATA (x',y',d)) m'')) =
     i INSERT D0 (CUT (b,j'') m'')` THENL [
      SIMP_TAC std_ss [EXTENSION,D0,CUT_def,IN_INSERT]
      \\ SIMP_TAC std_ss [IN_DEF,D0,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `RANGE (b,j'') x''` \\ ASM_SIMP_TAC std_ss [heap_type_distinct]
      THEN1 (Cases_on `x'' = i` \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
      \\ FULL_SIMP_TAC bool_ss [RANGE_def,IRANGE_def] \\ DECIDE_TAC,
      ASM_SIMP_TAC std_ss [EXTENSION,IN_INSERT]
      \\ SIMP_TAC std_ss [RANGE_def,IN_DEF]
      \\ STRIP_TAC \\ Cases_on `x'' = i` \\ ASM_SIMP_TAC std_ss  [] \\ DECIDE_TAC])
  THEN1
   (MATCH_MP_TAC D1_SUBSET0
    \\ `~RANGE(b,i)i` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [CUT_update]
    \\ sg `D1 (CUT (i,i + 1) ((i =+ DATA (x',y',d))m'')) = {x';y'}` THENL [
      ASM_SIMP_TAC std_ss [D1,EXTENSION,IN_INSERT,NOT_IN_EMPTY]
      \\ ASM_SIMP_TAC std_ss [D1,IN_DEF,CUT_def,RANGE_def,DECIDE ``i<=k/\k<i+1 = (k = i)``]
      \\ SIMP_TAC bool_ss [UPDATE_def]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ Cases_on `k = i` \\ FULL_SIMP_TAC bool_ss [heap_type_11,heap_type_distinct,PAIR_EQ]
      \\ METIS_TAC [],
      ASM_REWRITE_TAC []
      \\ `RANGE(b,j') SUBSET RANGE(b,j'')` by
         (SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,RANGE_def] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET]
      \\ METIS_TAC [IN_INSERT,SUBSET_DEF]])
  THEN1
   (MATCH_MP_TAC maintain_lemma \\ Q.EXISTS_TAC `j`
    \\ ASSUME_TAC (UNDISCH_ALL RANGE_split)
    \\ ASM_SIMP_TAC bool_ss [UNION_SUBSET] \\ STRIP_TAC
    THENL [Cases_on `~(x = 0) /\ (m' x = REF j)`,Cases_on `~(y = 0) /\ (m'' y = REF j')`]
    \\ NTAC 2 (FULL_SIMP_TAC bool_ss
        [heap_type_11,RANGE_lemmas,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]))
  THEN1
   (`~(RANGE(i+1,j'')i)` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [CUT_update]
    \\ MATCH_MP_TAC SUBSET0_TRANS
    \\ Q.EXISTS_TAC `D1 (CUT (i,j'') m'')` \\ ASM_SIMP_TAC bool_ss []
    \\ SIMP_TAC std_ss [D1,SUBSET_DEF,SUBSET0_DEF,IN_INSERT]
    \\ SIMP_TAC std_ss [D1,IN_DEF,CUT_def,RANGE_def]
    \\ METIS_TAC [DECIDE ``i + 1 <= k /\ k < j'' ==> i <= k /\ k < j''``,heap_type_distinct])
  THEN1
   (Q.PAT_X_ASSUM `R1 m'' = RANGE (b,j'')` (fn th => REWRITE_TAC [GSYM th])
    \\ `m'' i = DATA (ax,ay,ad)` by
     (sg `RANGE (b,j) i /\ RANGE (b,j') i`
      \\ FULL_SIMP_TAC bool_ss [CUT_def,FUN_EQ_THM]
      THEN1 (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)\\ METIS_TAC [])
    \\ SIMP_TAC std_ss [R1,IN_DEF,CUT_def,RANGE_def,SUBSET_DEF,UPDATE_def,FUN_EQ_THM]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC [heap_type_distinct])
  THEN1
   (Cases_on `i = j'''` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct,UPDATE_def]
    \\ Cases_on `i = i'` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct,UPDATE_def] \\ METIS_TAC [])
  THEN1
   (`~(i = 0)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
   (MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `i INSERT RANGE(b,i)` \\ STRIP_TAC
    THEN1 (REWRITE_TAC [SUBSET_DEF,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
    \\ REWRITE_TAC [INSERT_SUBSET] \\ SIMP_TAC std_ss [IN_DEF] \\ STRIP_TAC THENL [
      SIMP_TAC std_ss [reachable_def,basic_abs]
      \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT,IN_UNION]
      \\ FULL_SIMP_TAC bool_ss [IN_DEF]
      \\ `(r i) \/ D1 (CUT (b,i) m'') i` by METIS_TAC []
      THEN1 METIS_TAC [] \\ IMP_RES_TAC D1_IMP
      \\ `?t. r t /\ reachable t (basic_abs (CUT (b,i) m'')) h` by METIS_TAC []
      \\ `PATH (h,[i]) (basic_abs (CUT (b,i + 1) ((i =+ DATA (x',y',d))m'')))` by
       (`RANGE (b,i+1) h /\ ~(h = i)` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
        \\ ASM_SIMP_TAC std_ss [PATH_def,APPEND,IN_DEF,basic_abs,CUT_def,UPDATE_def]
        \\ METIS_TAC [])
      \\ Q.EXISTS_TAC `t` \\ FULL_SIMP_TAC bool_ss [reachable_def]  \\ DISJ2_TAC
      THEN1 (Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [APPEND])
      \\ Q.EXISTS_TAC `p ++ [h]` \\ MATCH_MP_TAC PATH_snoc \\ ASM_SIMP_TAC bool_ss []
      \\ MATCH_MP_TAC PATH_CUT_expand \\ Q.EXISTS_TAC `i`
      \\ ASM_SIMP_TAC bool_ss [CUT_update] \\ DECIDE_TAC,
      FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ `?t. r t /\ reachable t (basic_abs (CUT (b,i) m'')) x''`  by METIS_TAC []
      \\ Q.EXISTS_TAC `t` \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC reachable_CUT_expand \\ Q.EXISTS_TAC `i`
      \\ ASM_SIMP_TAC bool_ss [CUT_update] \\ DECIDE_TAC])
  THEN1
   (`m'' k = REF i'` by METIS_TAC []
    \\ Cases_on `k = i` \\ ASM_SIMP_TAC bool_ss [UPDATE_def]
    \\ `RANGE(b,j'')i` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
    \\ `D0 (CUT (b,j'') m'') i` by METIS_TAC [] \\ IMP_RES_TAC D0_IMP
    \\ `F` by METIS_TAC [heap_type_distinct])
  THEN1
   (`!x i j m. D0 (CUT (i,j) m) x ==> D0 m x` by
      (SIMP_TAC bool_ss [D0,CUT_def] \\ METIS_TAC [heap_type_distinct])
    \\ sg `abs ((i =+ DATA (x',y',d))m'') = abs m''` THENL [
      MATCH_MP_TAC (GEN_ALL abs_update_lemma)
      \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC bool_ss [heap_type_11]
      \\ REPEAT (Q.PAT_X_ASSUM `fgh SUBSET0 jkl` (fn th => ALL_TAC))
      \\ `RANGE(b,j) i /\ RANGE(b,j') i` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ `(m'' i = m i)` by (FULL_SIMP_TAC bool_ss [CUT_def,FUN_EQ_THM] \\ METIS_TAC [])
      \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
      THEN1 (Cases_on `x = 0` \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC [])
      THEN1 (Cases_on `y = 0` \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC []),
      FULL_SIMP_TAC bool_ss [roots_inv_def] \\ Q.EXISTS_TAC `v`
      \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC \\ STRIP_TAC
      \\ `RANGE(b,j'') i` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ Cases_on `k = i` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_type_distinct]
      \\ METIS_TAC []]));

val cheney_inv_maintained = (SIMP_RULE std_ss [] o prove)(
  ``!i j e m.
      (\(i,j,e,m).
      !r. cheney_inv(b,b',i,j,j,e,f,m,w,xx,r) ==>
          !i2 m2. (cheney(i,j,e,m) = (i2,m2)) ==>
                  cheney_inv(b,b',i2,i2,i2,e,f,m2,w,xx,r) /\ j <= i2) (i,j,e,m)``,
  MATCH_MP_TAC cheney_ind \\ SIMP_TAC std_ss [] \\ NTAC 5 STRIP_TAC
  \\ `?i2 j2 e2 m2. cheney_step (i,j,e,m) = (i2,j2,e2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `(i = j) \/ (e < i)`
  \\ FULL_SIMP_TAC bool_ss [] \\ NTAC 3 STRIP_TAC \\ ONCE_REWRITE_TAC [cheney_def]
  THEN1 (REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [LESS_EQ_REFL])
  THEN1 (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC cheney_inv_step \\ METIS_TAC [LESS_EQ_TRANS]);

val move_roots_def = Define `
  (move_roots ([],j,m) = ([],j,m)) /\
  (move_roots (r::rs,j,m) =
    let (r,j,m) = move(r,j,m) in
    let (rs,j,m) = move_roots(rs,j,m) in
      (r::rs,j,m))`;

val cheney_collect_def = Define `
  cheney_collector(i:num,e:num,root,l,u,m) =
    let u = ~u:bool in
    let i = (if u then 1+l else 1) in
    let (root,j,m) = move_roots(root,i,m) in
    let (j,m) = cheney(i,j,i+l,m) in
    let m = CUT (i,i+l) m in
      (j,i+l,root,l,u,m)`;

val CUT_EMPTY = prove(
  ``!b m. (CUT (b,b) m = \x.EMP) /\ (ICUT (b,b) m = m) /\
          (RANGE(b,b) = \x.F) /\ (IRANGE(b,b) = \x.T)``,
  SIMP_TAC std_ss [FUN_EQ_THM,RANGE_def,CUT_def,ICUT_def,RANGE_def,IRANGE_def]
  \\ METIS_TAC [DECIDE ``~(b <= n /\ n < b:num)``]);

val FINITE_RANGE = prove(
  ``!j i. FINITE (RANGE(i,i+j)) /\ (CARD (RANGE(i,i+j)) = j)``,
  Induct \\ REWRITE_TAC [CUT_EMPTY,ADD_0,FINITE_EMPTY,CARD_EMPTY,GSYM EMPTY_DEF] \\ STRIP_TAC
  \\ sg `(RANGE (i,i + SUC j) = (i + j) INSERT RANGE (i,i + j)) /\
     ~((i + j) IN RANGE (i,i + j))`
  \\ ASM_SIMP_TAC bool_ss [FINITE_INSERT,CARD_INSERT,EXTENSION,IN_INSERT]
  \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val FINITE_RANGE = store_thm("FINITE_RANGE",
  ``!i j. FINITE (RANGE(i,j)) /\ (CARD (RANGE(i,j)) = j - i)``,
  NTAC 2 STRIP_TAC \\ Cases_on `i <= j`
  THEN1 (FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,FINITE_RANGE] \\ DECIDE_TAC)
  \\ sg `RANGE (i,j) = EMPTY` \\ ASM_REWRITE_TAC [FINITE_EMPTY,CARD_EMPTY]
  \\ FULL_SIMP_TAC bool_ss [EXTENSION,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val ok_state_IMP_cheney_inv = store_thm("ok_state_IMP_cheney_inv",
  ``ok_state (i,e6,r,l,u,m) ==>
    let b = if ~u then 1 + l else 1 in
      cheney_inv (b,b,b,b,b,b + l,l+l+1,m,m,m,{}) /\
      !k. MEM k r ==> {k} SUBSET0 DR0 (ICUT (b,b+l) m)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF,cheney_inv_def,ok_state_def,CUT_EMPTY]
  \\ Q.ABBREV_TAC `b = if u then 1 + l else 1`
  \\ Q.ABBREV_TAC `b2 = if ~u then 1 + l else 1`
  \\ `(ICUT (b2,b2 + l) m) = m` by
   (FULL_SIMP_TAC bool_ss [ICUT_def,FUN_EQ_THM,IN_DEF]
    \\ sg `!k. RANGE(b,i)k ==> IRANGE (b2,b2 + l) k`
    THENL [ALL_TAC,METIS_TAC []] \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2`
    \\ Cases_on `u` \\ FULL_SIMP_TAC bool_ss [IRANGE_def,RANGE_def] \\ DECIDE_TAC)
  \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  THEN1 (Q.UNABBREV_TAC `b2` \\ Cases_on `u` \\ DECIDE_TAC)
  THEN1 (Q.UNABBREV_TAC `b2` \\ Cases_on `u` \\ DECIDE_TAC)
  THEN1
   (Q.PAT_X_ASSUM `!k. ~bb:bool ==> c` MATCH_MP_TAC
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
    \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2` \\ DECIDE_TAC)
  THEN1
   (Q.PAT_X_ASSUM `!k. ~bbb:bool ==> c` MATCH_MP_TAC
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
    \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2` \\ DECIDE_TAC)
  THEN1 (SIMP_TAC std_ss [FUN_EQ_THM,D0,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,D1,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,D1,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,D1,heap_type_distinct])
  THEN1
   (FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,DR0,D1,D0,ICUT_def] \\ REPEAT STRIP_TAC
    \\ `RANGE(b,i)k` by METIS_TAC [heap_type_distinct]
    \\ Cases_on `x = 0` \\ ASM_SIMP_TAC bool_ss []
    \\ `RANGE(b,i)x` by METIS_TAC [heap_type_11,PAIR_EQ]
    \\ ASM_REWRITE_TAC [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC std_ss [FUN_EQ_THM,R1] \\ METIS_TAC [heap_type_distinct])
  THEN1 METIS_TAC [heap_type_distinct]
  THEN1
   (MATCH_MP_TAC LESS_EQ_TRANS \\ Q.EXISTS_TAC `CARD (RANGE(b,i))` \\ STRIP_TAC
    THENL [ALL_TAC, REWRITE_TAC [FINITE_RANGE] \\ DECIDE_TAC]
    \\ MATCH_MP_TAC ((GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o
                     SPEC_ALL o UNDISCH o SPEC_ALL) CARD_SUBSET)
    \\ FULL_SIMP_TAC std_ss [FINITE_RANGE,SUBSET_DEF,IN_DEF,D0]
    \\ METIS_TAC [heap_type_distinct])
  THEN1
   (MATCH_MP_TAC ((GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o
                  SPEC_ALL o UNDISCH o SPEC_ALL) SUBSET_FINITE)
    \\ Q.EXISTS_TAC `RANGE(b,i)` \\ FULL_SIMP_TAC std_ss [D0,SUBSET_DEF,IN_DEF,ICUT_def,FINITE_RANGE]
    \\ METIS_TAC [heap_type_distinct])
  THEN1
   (Q.PAT_X_ASSUM `!k. ~bbb:bool ==> c` MATCH_MP_TAC
    \\ Q.UNABBREV_TAC `b` \\ Cases_on `u` \\ FULL_SIMP_TAC bool_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC)
  THEN1 REWRITE_TAC [GSYM EMPTY_DEF,EMPTY_SUBSET]
  THEN1
   (REWRITE_TAC [roots_inv_def] \\ Q.EXISTS_TAC `I` \\ ASM_SIMP_TAC std_ss [apply_I]
    \\ METIS_TAC [heap_type_distinct])
  THEN1
   (Cases_on `k = 0` THEN1 ASM_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ REWRITE_TAC [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ RES_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [IN_DEF,DR0,D0,heap_type_11] \\ METIS_TAC []));

val reachables_def = Define `
  reachables rs h (a,x,y,d) = (a,x,y,d) IN h /\ ?r. MEM r rs /\ a IN reachable r h`;

val basic_abs_EQ_abs = prove(
  ``!m. (!k i. ~(m k = REF i)) ==> (basic_abs m = abs m)``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a y z d. x = (a,y,z,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [abs_def,basic_abs]
  \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `y` \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC []
    \\ STRIP_TAC THENL [Cases_on `m y`,Cases_on `m z`]
    \\ FULL_SIMP_TAC bool_ss [ADDR_def] \\ METIS_TAC [],
    FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ]
    \\ STRIP_TAC THENL [Cases_on `m k`,Cases_on `m k'`]
    \\ FULL_SIMP_TAC bool_ss [ADDR_def] \\ METIS_TAC []]);

val apply_reachables_lemma = prove(
  ``(!x. f (g x) = x) /\ (!x. g (f x) = x) ==>
    PATH (r,p ++ [g a]) s ==> PATH (f r,MAP f p ++ [a]) (apply g s)``,
  STRIP_TAC \\ Q.SPEC_TAC (`r`,`r`) \\ Q.SPEC_TAC (`p`,`p`) \\ Induct
  \\ ASM_SIMP_TAC std_ss [APPEND,MAP,PATH_def,IN_DEF,apply_def] \\ METIS_TAC []);

val apply_reachables = store_thm("apply_reachables",
  ``!r f g s. (f o g = I) /\ (g o f = I) ==>
              (apply g (reachables r s) = reachables (MAP f r) (apply g s))``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a y z d. x = (a,y,z,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [reachables_def,IN_DEF,apply_def,reachable_def,MEM_MAP]
  \\ Cases_on `s (g a,g y,g z,d)` \\ ASM_REWRITE_TAC []
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 METIS_TAC [apply_reachables_lemma]
  THEN1 METIS_TAC [apply_reachables_lemma]
  THEN1 METIS_TAC [apply_reachables_lemma]
  \\ Q.EXISTS_TAC `y'` \\ ASM_REWRITE_TAC []
  \\ DISJ2_TAC \\ Q.EXISTS_TAC `MAP g p`
  \\ Q.UNDISCH_TAC `PATH (r',p ++ [a]) (apply g s)`
  \\ ASM_REWRITE_TAC []
  \\ Q.SPEC_TAC (`y'`,`yy`) \\ Induct_on `p`
  \\ ASM_SIMP_TAC std_ss [APPEND,MAP,PATH_def,IN_DEF,apply_def] \\ METIS_TAC []);

val PATH_CUT = prove(
  ``!p r x i j m.
      RANGE(i,j)r /\ ~RANGE(i,j)x /\ PATH (r,p ++ [x]) (abs m) /\ ~(x = 0) /\ (m 0 = EMP) ==>
      ?s d. PATH(s,[d]) (abs m) /\ RANGE(i,j)s /\ ~RANGE(i,j)d /\ ~(d = 0)``,
  Induct THEN1 (REWRITE_TAC [APPEND] \\ METIS_TAC [])
  \\ NTAC 6 STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (REWRITE_CONV [PATH_def,APPEND]))
  \\ Cases_on `RANGE(i,j)h` THEN1 METIS_TAC []
  \\ REWRITE_TAC [PATH_def] \\ REPEAT STRIP_TAC
  \\ `~(h = 0)` by (CCONTR_TAC \\ Cases_on `p`
    \\ FULL_SIMP_TAC bool_ss [APPEND,PATH_def,IN_DEF,abs_def,heap_type_distinct])
  \\ METIS_TAC []);

val fix_ADDR = prove(
  ``!m ax ay az k k' ad b j e.
      (m ax = DATA (k,k',ad)) /\ (!k. j <= k /\ k < e ==> (m k = EMP)) /\
      RANGE (b,e) ax /\ (D1 (CUT (b,j) m) SUBSET0 RANGE (b,j)) /\ (m 0 = EMP) /\
      (D0 (CUT (b,j) m) = RANGE (b,j)) ==>
      (ADDR k ay (m k) = (ay = k)) /\ (ADDR k' az (m k') = (az = k'))``,
  REPEAT STRIP_TAC THENL [
    Cases_on `m k` \\ ASM_SIMP_TAC bool_ss [ADDR_def]
    \\ Cases_on `j <= ax` THEN1 METIS_TAC [heap_type_distinct,RANGE_def]
    \\ `RANGE(b,j) ax` by FULL_SIMP_TAC bool_ss [RANGE_def,DECIDE ``~(m<=n) = n < m:num``]
    \\ `D1 (CUT (b,j) m) k` by (ASM_SIMP_TAC std_ss [D1,CUT_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF]
    \\ `RANGE (b,j) k` by METIS_TAC [heap_type_distinct]
    \\ `D0 (CUT (b,j) m) k` by METIS_TAC []
    \\ IMP_RES_TAC D0_IMP \\ METIS_TAC [heap_type_distinct],
    Cases_on `m k'` \\ ASM_SIMP_TAC bool_ss [ADDR_def]
    \\ Cases_on `j <= ax` THEN1 METIS_TAC [heap_type_distinct,RANGE_def]
    \\ `RANGE(b,j) ax` by FULL_SIMP_TAC bool_ss [RANGE_def,DECIDE ``~(m<=n) = n < m:num``]
    \\ `D1 (CUT (b,j) m) k'` by (ASM_SIMP_TAC std_ss [D1,CUT_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF]
    \\ `RANGE (b,j) k'` by METIS_TAC [heap_type_distinct]
    \\ `D0 (CUT (b,j) m) k'` by METIS_TAC []
    \\ IMP_RES_TAC D0_IMP \\ METIS_TAC [heap_type_distinct]]);

val CUT_EQ_DATA_IMP = prove(
  ``(CUT (i,j) m y = DATA x) ==> (m y = DATA x) /\ RANGE(i,j)y``,
  SIMP_TAC std_ss [CUT_def] \\ METIS_TAC [heap_type_distinct]);

val PATH_CUT_IMP = prove(
  ``!p b i j m.
      (D1 (CUT (i,j) m) SUBSET0 RANGE (i,j)) /\ (D0 (CUT (i,j) m) = RANGE (i,j)) /\ (m 0 = EMP) /\
      PATH (b,p) (abs (CUT (i,j) m)) ==> PATH (b,p) (abs m)``,
  Induct \\ FULL_SIMP_TAC std_ss [PATH_def,IN_DEF,abs_def,CUT_def,APPEND]
  \\ FULL_SIMP_TAC bool_ss [GSYM CUT_def] \\ REPEAT STRIP_TAC
  THENL [METIS_TAC [heap_type_distinct],ALL_TAC,METIS_TAC [heap_type_distinct],ALL_TAC]
  \\ Cases_on `RANGE(i,j)b` \\ FULL_SIMP_TAC std_ss [heap_type_distinct,heap_type_11]
  \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ `D1 (CUT (i,j) m) k /\ D1 (CUT (i,j) m) k'` by
      (SIMP_TAC std_ss [D1,CUT_def] \\ METIS_TAC [heap_type_distinct])
  \\ `~(k = 0) ==> D0 (CUT (i,j) m) k` by METIS_TAC []
  \\ `~(k' = 0) ==> D0 (CUT (i,j) m) k'` by METIS_TAC []
  THENL [Q.EXISTS_TAC `k'`,Q.EXISTS_TAC `k`] \\ Q.EXISTS_TAC `d`
  THENL [DISJ1_TAC,DISJ2_TAC] \\ REWRITE_TAC []
  \\ Cases_on `k = 0` \\ Cases_on `k' = 0` \\ FULL_SIMP_TAC std_ss [ADDR_def]
  \\ IMP_RES_TAC D0_IMP \\ FULL_SIMP_TAC bool_ss [ADDR_def]
  \\ METIS_TAC [ADDR_def]);

val reachable_IMP = prove(
  ``!b m i j x.
     (D1 (CUT (i,j) m) SUBSET0 RANGE (i,j)) /\ (D0 (CUT (i,j) m) = RANGE (i,j)) /\ (m 0 = EMP) /\
     reachable b (abs (CUT (i,j) m)) x ==> reachable b (abs m) x``,
  REWRITE_TAC [reachable_def] \\ METIS_TAC [PATH_CUT_IMP]);

val MAP_INV = prove(
  ``!g f. (g o f = I) /\ (f o g = I) ==> !xs ys. (xs = MAP f ys) = (MAP g xs = ys)``,
  NTAC 3 STRIP_TAC \\ Induct
  \\ Cases_on `ys` \\ ASM_SIMP_TAC std_ss [MAP,NOT_CONS_NIL,CONS_11]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC []);

val move_roots_spec = prove(
  ``!a. ((if ~u then a + l else a) = b) ==>
    !r j m r' j' m' w ww xx.
      cheney_inv (b,b,b,j,b,b+l,f,m,w:num->'a heap_type,xx:num->'a heap_type,ww) /\
      (!k. MEM k r ==> {k} SUBSET0 DR0 (ICUT (b,b + l) m)) /\
      (move_roots (r,j,m) = (r',j',m')) ==>
      cheney_inv (b,b,b,j',b,b+l,f,m',w,xx,ww) /\ j <= j' /\
      (!k. MEM k r' /\ ~(k = 0) ==> RANGE (b,j') k)  /\
      (!k. RANGE(j,j') k ==> MEM k r') /\
      (!k i. (m k = REF i) ==> (m' k = REF i)) /\
      (LENGTH r = LENGTH r') /\
      (!k. MEM k r /\ ~(k = 0) \/ isREF (m k) ==> isREF(m' k)) /\
      (!k k'. MEM (k,k') (ZIP(r,r')) ==> if k = 0 then k' = 0 else (m' k = REF k'))``,
  STRIP_TAC \\ STRIP_TAC \\ Induct THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [PAIR_EQ,move_roots_def,MEM,RANGE_lemmas,EMPTY_DEF,
         LESS_EQ_REFL,MAP,apply_I,ZIP])
  \\ NTAC 9 STRIP_TAC
  \\ `?r' j' m'.  move (h,j,m) = (r',j',m')` by METIS_TAC [PAIR]
  \\ `?rs3 j3 m3.  move_roots (r,j'',m'') = (rs3,j3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [move_roots_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [MEM] \\ STRIP_TAC
  \\ `{h} SUBSET0 DR0 (ICUT (b,b + l) m)` by METIS_TAC []
  \\ IMP_RES_TAC move_lemma
  \\ `!k. MEM k r ==> {k} SUBSET0 DR0 (ICUT (b,b + l) m'')` by METIS_TAC []
  \\ Q.PAT_X_ASSUM `!j m r'. bb` (STRIP_ASSUME_TAC o UNDISCH_ALL o
       RW [GSYM AND_IMP_INTRO] o Q.SPECL [`j''`,`m''`,`rs3`,`j3`,`m3`,`w`,`ww`,`xx`])
  \\ STRIP_TAC THEN1 METIS_TAC []
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ Cases_on `h = 0` THEN1 METIS_TAC [] \\ FULL_SIMP_TAC bool_ss []
    \\ IMP_RES_TAC D0_IMP \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ Cases_on `k = r''` THEN1 METIS_TAC [] \\ DISJ2_TAC
    \\ Cases_on `h = 0` THEN1 METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [] \\ IMP_RES_TAC D0_IMP
    \\ Q.PAT_X_ASSUM `!k. RANGE (_,_) k ==> MEM k rs3` MATCH_MP_TAC
    \\ Cases_on ` m'' h = REF j` \\ FULL_SIMP_TAC bool_ss [heap_type_11]
    \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [LENGTH,ZIP,MEM]
  \\ STRIP_TAC THEN1
   (STRIP_TAC \\ Cases_on `isREF(m k)` \\ ASM_SIMP_TAC bool_ss [] THEN1 METIS_TAC [isREF_def]
    \\ REPEAT STRIP_TAC THENL [ALL_TAC,METIS_TAC []]
    \\ `~(h = 0)` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [move_def,LET_DEF,PAIR_EQ]
    \\ Q.PAT_X_ASSUM `!k. bbb ==> isREF (m3 k)` MATCH_MP_TAC \\ DISJ2_TAC
    \\ Q.PAT_X_ASSUM `(h =+ REF j) ((j =+ m h) m) = m''` (fn th => REWRITE_TAC [GSYM th])
    \\ SIMP_TAC std_ss [isREF_def,UPDATE_def,heap_type_11])
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ Cases_on `k = 0` \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);

val cheney_inv_setup = store_thm("cheney_inv_setup",
  ``cheney_inv (b,b,b,j,b,e,f,m',m,m,{}) ==> cheney_inv (b,j,b,j,j,e,f,m',m',m,RANGE(b,j))``,
  SIMP_TAC bool_ss [cheney_inv_def,LESS_EQ_REFL] \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  THEN1 (REWRITE_TAC [SUBSET_DEF,IN_UNION] \\ SIMP_TAC bool_ss [IN_DEF])
  THEN1 METIS_TAC [] \\ REWRITE_TAC [RANGE_lemmas,EMPTY_SUBSET]);

val list_RANGE_aux_def = Define `
  (list_RANGE_aux 0 n = []) /\
  (list_RANGE_aux (SUC m) n = n::list_RANGE_aux m (n+1))`;

val list_RANGE_def = Define `
  list_RANGE(i,j) = list_RANGE_aux (j-i) i`;

val list_RANGE_aux_thm = prove(
  ``!j i k. MEM k (list_RANGE_aux j i) = RANGE(i,i+j) k``,
  Induct \\ ASM_REWRITE_TAC [list_RANGE_aux_def,MEM,RANGE_lemmas,ADD_0,EMPTY_DEF]
  \\ REWRITE_TAC [RANGE_def] \\ DECIDE_TAC);

val list_RANGE_thm = prove(
  ``!i j k. MEM k (list_RANGE(i,j)) = RANGE(i,j) k``,
  REWRITE_TAC [list_RANGE_def] \\ REPEAT STRIP_TAC \\ Cases_on `i <= j` THENL [
    FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS] \\ `i + p - i = p` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,list_RANGE_aux_thm],
    `j - i = 0` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [list_RANGE_aux_def,RANGE_def,MEM]
    \\ DECIDE_TAC]);

val cheney_collector_spec = store_thm("cheney_collector_spec",
  ``ok_state(j6,e6,r,l,u,m) /\ (cheney_collector (j6,e6,r,l,u,m) = (j2,e2,r2',l2,u2,m2)) ==>
    ok_state(j2,e2,r2',l2,u2,m2) /\ (l = l2) /\
    ?f. (f o f = I) /\ (MAP f r = r2') /\ (f 0 = 0) /\
        (apply f (reachables r (basic_abs m)) = basic_abs m2)``,
  ASM_SIMP_TAC std_ss [cheney_collect_def,LET_DEF]
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ Q.ABBREV_TAC `e = b + l`
  \\ `?r' j' m'. move_roots (r,b,m) = (r',j',m')` by METIS_TAC [PAIR]
  \\ `?j'' m''. cheney (b,j',e,m') = (j'',m'')` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Q.UNABBREV_TAC `b`
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] ok_state_IMP_cheney_inv)
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ `(if ~u then 1 + l else 1) = b` by METIS_TAC []
  \\ (STRIP_ASSUME_TAC o RW [AND_IMP_INTRO] o
     UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.INST [`f`|->`l+l+1`] o
     Q.SPECL [`r`,`b`,`m`,`r'`,`j'`,`m'`,`m`,`{}`,`m`] o UNDISCH o Q.SPEC `1`) move_roots_spec
  \\ `cheney_inv (b,j',b,j',j',b + l,l+l+1,m',m',m,RANGE(b,j'))` by METIS_TAC [cheney_inv_setup]
  \\ Q.UNABBREV_TAC `e` \\ Q.ABBREV_TAC `e = b + l`
  \\ `cheney_inv (b,j',j'',j'',j'',e,l+l+1,m'',m',m,RANGE (b,j')) /\ j' <= j''` by METIS_TAC [cheney_inv_maintained]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [cheney_inv_def,ok_state_def,LET_DEF,IN_DEF]
    \\ `!k. RANGE(b,j') k ==> RANGE(b,j'')k` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC THEN1 METIS_TAC [] THENL [
      Cases_on `RANGE(b,e)k` \\ ASM_SIMP_TAC std_ss [CUT_def]
      \\ Q.PAT_X_ASSUM `!k. bb ==> (m'' k = EMP)` MATCH_MP_TAC
      \\ FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC,
      `D0 (CUT (b,j'') m'') k` by METIS_TAC [] \\ IMP_RES_TAC D0_IMP
      \\ Q.EXISTS_TAC `h` \\ Q.EXISTS_TAC `g` \\ Q.EXISTS_TAC `dd`
      \\ `RANGE(b,e)k` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
      \\ ASM_SIMP_TAC std_ss [CUT_def]
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `D1 (CUT (b,j'') m'')`
      \\ ASM_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ ASM_SIMP_TAC std_ss [IN_DEF,D1,CUT_def] \\ METIS_TAC []])
  \\ `basic_abs m = abs m` by
     (MATCH_MP_TAC basic_abs_EQ_abs \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF]
      \\ METIS_TAC [heap_type_distinct])
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.PAT_X_ASSUM `cheney_inv (b,b,b,b,b,e,l+l+1,m,m,m,{})` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `cheney_inv (b,j',b,j',j',e,l+l+1,m',m',m,RANGE (b,j'))` (K ALL_TAC)
  \\ `m' 0 = EMP` by METIS_TAC [cheney_inv_def]
  \\ Q.PAT_X_ASSUM `cheney_inv (b,b,b,j',b,e,l+l+1,m',m,m,{})` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [cheney_inv_def]
  \\ `(\x. ?t. t IN RANGE(b,j') /\ x IN reachable t (abs m''))
     SUBSET (0 INSERT RANGE (b,b+l))` by
     (Q.UNABBREV_TAC `e` \\ Cases_on `l = 0` THEN1
       (`b = j'` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [RANGE_lemmas,NOT_IN_EMPTY]
        \\ REWRITE_TAC [GSYM EMPTY_DEF,EMPTY_SUBSET])
      \\ REWRITE_TAC [SUBSET_DEF,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF,reachable_def]
      \\ REPEAT STRIP_TAC THEN1 (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
      \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
      \\ `RANGE (b,b + l) t` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
      \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
          Q.SPECL [`p`,`t`,`x`,`b`,`b+l`,`m''`]) PATH_CUT
      \\ FULL_SIMP_TAC bool_ss [PATH_def,IN_DEF,abs_def]
      \\ (Cases_on `j'' <= s`
          THEN1 (`s < b + l` by FULL_SIMP_TAC bool_ss [RANGE_def] \\ METIS_TAC [heap_type_distinct])
          \\ `s < j''` by DECIDE_TAC
          \\ `RANGE(b,j'')s` by FULL_SIMP_TAC std_ss [RANGE_def]
          \\ `D1 (CUT (b,j'') m'') k /\ D1 (CUT (b,j'') m'') k'` by
           (FULL_SIMP_TAC std_ss [D1,CUT_def] \\ METIS_TAC [])
          \\ `~(k = 0) ==> RANGE(b,j'')k` by
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC [])
          \\ `~(k' = 0) ==> RANGE(b,j'')k'` by
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC []))
      THENL [
          `d = k` by
           (Cases_on `k = 0` THEN1 METIS_TAC [ADDR_def]
            \\ `D0 (CUT (b,j'') m'') k` by METIS_TAC []
            \\ IMP_RES_TAC D0_IMP \\ METIS_TAC [ADDR_def]),
          `d = k'` by
           (Cases_on `k' = 0` THEN1 METIS_TAC [ADDR_def]
            \\ `D0 (CUT (b,j'') m'') k'` by METIS_TAC []
            \\ IMP_RES_TAC D0_IMP \\ METIS_TAC [ADDR_def])]
      \\ `~RANGE(b,j'')d` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
      \\ METIS_TAC [])
  \\ `basic_abs (CUT(b,e)m'') = reachables r' (abs m'')` by
   (REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ ASM_SIMP_TAC bool_ss [reachables_def]
    \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,basic_abs,abs_def]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC THENL [
        IMP_RES_TAC CUT_EQ_DATA_IMP
        \\ ASM_SIMP_TAC std_ss [heap_type_11]
        \\ Cases_on `x = 0` THEN1 (`F` by METIS_TAC [heap_type_distinct])
        \\ Cases_on `j'' <= x` THEN1 (`F` by METIS_TAC [RANGE_def,heap_type_distinct])
        \\ `RANGE(b,j'')x` by FULL_SIMP_TAC bool_ss [DECIDE ``~(m<=n)=n<m:num``,RANGE_def]
        \\ REPEAT STRIP_TAC THENL [
          `D1 (CUT (b,j'') m'') y` by (SIMP_TAC bool_ss [CUT_def,D1] \\ METIS_TAC [])
          \\ Cases_on `y = 0` THEN1 METIS_TAC [ADDR_def]
          \\ `RANGE(b,j'')y` by
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC [])
          \\ `D0 (CUT (b,j'') m'') y` by METIS_TAC []
          \\ IMP_RES_TAC D0_IMP \\ ASM_SIMP_TAC bool_ss [ADDR_def],
          `D1 (CUT (b,j'') m'') z` by (SIMP_TAC bool_ss [CUT_def,D1] \\ METIS_TAC [])
          \\ Cases_on `z = 0` THEN1 METIS_TAC [ADDR_def]
          \\ `RANGE(b,j'')z` by
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC [])
          \\ `D0 (CUT (b,j'') m'') z` by METIS_TAC []
          \\ IMP_RES_TAC D0_IMP \\ ASM_SIMP_TAC bool_ss [ADDR_def],
          RES_TAC \\ Q.EXISTS_TAC `t` \\ STRIP_TAC THEN1 METIS_TAC []
          \\ MATCH_MP_TAC reachable_IMP
          \\ Q.EXISTS_TAC `b` \\ Q.EXISTS_TAC `j''` \\ ASM_SIMP_TAC bool_ss []
          \\ sg `abs (CUT (b,j'')m'') = basic_abs (CUT (b,j'') m'')`
          THENL [ALL_TAC,METIS_TAC []]
          \\ MATCH_MP_TAC (GSYM basic_abs_EQ_abs)
          \\ SIMP_TAC bool_ss [CUT_def] \\ NTAC 2 STRIP_TAC
          \\ Cases_on `RANGE(b,j'')k` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]
          \\ `D0 (CUT (b,j'') m'') k` by METIS_TAC []
          \\ IMP_RES_TAC D0_IMP \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]],
        Q.UNABBREV_TAC `e` \\ Cases_on `r'' = 0` THENL [
          FULL_SIMP_TAC bool_ss [reachable_def] THEN1 METIS_TAC [heap_type_distinct]
          \\ FULL_SIMP_TAC bool_ss [PATH_def,APPEND,IN_DEF,abs_def]
          \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [PATH_def,APPEND,IN_DEF,abs_def]
          \\ METIS_TAC [heap_type_distinct],
          `(x = 0) \/ RANGE (b,b + l) x` by METIS_TAC []
          THEN1 METIS_TAC [heap_type_distinct]
          \\ ASM_SIMP_TAC bool_ss [CUT_def,heap_type_11,PAIR_EQ]
          \\ FULL_SIMP_TAC bool_ss [GSYM AND_IMP_INTRO]
          \\ `!k. j'' <= k /\ k < b + l ==> (m'' k = EMP)` by METIS_TAC []
          \\ `(ADDR k y (m'' k) = (y = k)) /\ (ADDR k' z (m'' k') = (z = k'))` by
            (MATCH_MP_TAC fix_ADDR \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `d` \\ Q.EXISTS_TAC `b`
             \\ Q.EXISTS_TAC `j''` \\ Q.EXISTS_TAC `b+l` \\ ASM_SIMP_TAC bool_ss [])
          \\ FULL_SIMP_TAC bool_ss []]])
  \\ Q.PAT_X_ASSUM `roots_inv (b,j'',m'',abs m)` (STRIP_ASSUME_TAC o RW [roots_inv_def])
  \\ Q.EXISTS_TAC `v` \\ ASM_SIMP_TAC bool_ss [apply_apply]
  \\ `apply v (reachables r (apply v (abs m''))) =
      reachables (MAP v r) (apply v (apply v (abs m'')))` by METIS_TAC [apply_reachables]
  \\ ASM_SIMP_TAC bool_ss [apply_apply,apply_I]
  \\ `v 0 = 0` by
    (`~isREF(m'' 0)` by METIS_TAC [isREF_def,heap_type_distinct]
     \\ `~RANGE(b,j'')0` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
     \\ METIS_TAC [])
  \\ ASM_SIMP_TAC bool_ss []
  \\ ONCE_REWRITE_TAC [METIS_PROVE [] ``b /\ c = b /\ (b ==> c:bool)``]
  \\ SIMP_TAC bool_ss []
  \\ `!k k'. MEM (k,k') (ZIP (r,r')) ==> (v k = k')` by METIS_TAC []
  \\ Q.UNDISCH_TAC `!k k'. MEM (k,k') (ZIP (r,r')) ==> (v k = k')`
  \\ Q.UNDISCH_TAC `LENGTH r = LENGTH r'`
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ Q.SPEC_TAC (`r'`,`ys`) \\ Q.SPEC_TAC (`r`,`xs`)
  \\ Induct THENL [ALL_TAC,STRIP_TAC] \\ Cases
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,MAP,ADD,EQ_ADD_RCANCEL,ZIP,MEM,CONS_11]
  \\ METIS_TAC [PAIR_EQ]);

val _ = export_theory();
