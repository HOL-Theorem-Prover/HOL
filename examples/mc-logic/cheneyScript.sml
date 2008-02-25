
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory finite_mapTheory;


val _ = new_theory "cheney";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = Parse.hide "set";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;



(* -- abstraction -- *)

val SUBSET0_DEF = new_infixr_definition
    ("SUBSET0_DEF", (--`SUBSET0 s t = s SUBSET (0 INSERT t)`--),450);

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

val range_def = Define `range(i:num,j) k = i <= k /\ k < j`;
val irange_def = Define `irange(i:num,j) k = ~(i <= k /\ k < j)`;

val cut_def = Define `cut (i,j) m = \k. if range (i,j) k then m k else EMP`;
val icut_def = Define `icut (i,j) m = \k. if irange (i,j) k then m k else EMP`;

val d0 = Define `d0 m k = ?x y z. m (k:num) = DATA(x,y,z)`;
val d1 = Define `d1 m x = ?k y z. (m (k:num) = DATA(x,y,z)) \/ (m k = DATA(y,x,z))`;
val r0 = Define `r0 m k = ?a. m (k:num) = REF a`;
val r1 = Define `r1 m a = ?k. m (k:num) = REF a`;
val dr0 = Define `dr0 m k = d0 m k \/ r0 m k`
val dr1 = Define `dr1 m k = d1 m k \/ r1 m k`

val bijection_def = Define `bijection g = ONTO g /\ ONE_ONE g`;

val addr_def = Define `
  (addr k n EMP = (n = k)) /\
  (addr k n (REF i) = (n = i)) /\
  (addr k n (DATA x) = (n = k))`;

val abs_def = Define `
  abs m (a,n,n',d) =  
    ?k k'. (m a = DATA(k,k',d)) /\ addr k n (m k) /\ addr k' n' (m k')`;

val basic_abs = Define `
  basic_abs m (a,n,n',d) = (m a = DATA(n,n',d))`;

val apply_def = Define `apply h s (a,n,n',d) = (h a,h n,h n',d) IN s`;

val path_def = Define `
  (path (x,[]) s = T) /\
  (path (x,y::ys) s = path (y,ys) s /\ ?z d. (x,y,z,d) IN s \/ (x,z,y,d) IN s)`;

val reachable_def = Define `
  reachable r set i = (r = i) \/ ?p. path (r,p++[i]) set`;

val UPDATE_thm = prove(
  ``!a b. a =+ b = (\f k. (if k = a then b else f k))``,
  SIMP_TAC std_ss [UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val roots_inv_def = Define `
  roots_inv (b,j,m,xx) =
    ?v. (v o v = I) /\ (xx = apply v (abs m)) /\ 
        (!k. ~isREF(m k) /\ ~range(b,j)k ==> (v k = k)) /\
        (!k i. (m k = REF i) ==> (v k = i))`;

val cheney_inv_def = Define `
  cheney_inv(b,b',i,j,j',e,f,m,x,xx,r) = 
    (0 < b /\ b <= b' /\ b' <= j /\ b <= i /\ i <= j /\ j <= e /\ e <= f) /\
    (!k. j <= k /\ k < e \/ f < k ==> (m k = EMP)) /\    (* all EMP between j and e *)           
    (d0(cut(b,j)m) = range(b,j)) /\                      (* all DATA between b and j *)
    (d1(cut(b,i)m) SUBSET0 range(b,j)) /\                (* b-i links only to b-j and nil *)
    (range(i,j') SUBSET (r UNION d1(cut(b,i)m))) /\      (* every i-j is linked to by some b-i *)
    (d1(cut(i,j)m) SUBSET0 dr0(icut(b,e)m)) /\           (* i-j links only outside of b-e *)
    (d1(icut(b,e)m) SUBSET0 dr0(icut(b,e)m)) /\          (* outside of b-e links only to outside b-e *)
    (r1(m) = range(b,j)) /\                              (* all REFs refer to b-j elements *)
    (!i j k. (m i = REF k) /\ (m j = REF k) ==> (i = j)) /\ (* REFs are injective *)
    (CARD(d0(icut(b,e)m)) <= e-j) /\                     (* num of elements outside b-e fit into e-j *)
    FINITE (d0(icut(b,e)m)) /\                           (* the set is finite *)
    (m 0 = EMP) /\                                       (* 0 points at no data *)
    range(b,i) SUBSET                                    (* all of b-i is reachable from r *)
    (\x. ?t. t IN r /\ x IN reachable t (basic_abs(cut(b,i)m))) /\ 
    (!k i. (x k = REF i) ==> (m k = REF i)) /\           (* refernces are reserved *)
    roots_inv (b,j,m,abs xx)                             (* memory is permuted *)`;

val ok_state_def = Define `
  ok_state (i,e,r,l,u,m) = 
    let a = (if u then 1 + l else 1) in
    let s = range(a,i) in
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
  \\ CONV_TAC (DEPTH_CONV (arm_progLib.FORCE_PBETA_CONV))
  \\ REWRITE_TAC [FST,SND] \\ DECIDE_TAC);

val cheney_ind = fetch "-" "cheney_ind";

val m_DATA = store_thm("m_DATA",
  ``cheney_inv(b,b',i,j,j',e,f,m,x,xx,r) /\ ~(i = j) ==> ?ax ay ad. m i = DATA (ax,ay,ad)``,
  SIMP_TAC std_ss [cheney_inv_def,FUN_EQ_THM,d0,IN_DEF,range_def,cut_def]
  \\ REPEAT STRIP_TAC \\ `b <= i /\ i < j` by DECIDE_TAC \\ METIS_TAC []);

val IN_EQ_SUBSET = 
  GEN_ALL (GSYM (REWRITE_CONV [INSERT_SUBSET,EMPTY_SUBSET] ``{i:'a} SUBSET x``));

val range_irange = prove(
  ``!b e x y. range (b,e) x /\ irange (b,e) y ==> ~(x = y)``,
  REWRITE_TAC [range_def,irange_def] \\ DECIDE_TAC);

val range_expand = prove(
  ``!i j k x. range (i,j) x /\ j <= k ==> range (i,k) x``,
  REWRITE_TAC [range_def,irange_def] \\ DECIDE_TAC);

val range_expand_left = prove(
  ``!i j k x. range (i,j) x /\ k <= i ==> range (k,j) x``,
  REWRITE_TAC [range_def,irange_def] \\ DECIDE_TAC);

val cut_update = prove(
  ``~range (i,j) k ==> (cut (i,j) ((k =+ x) m) = cut (i,j) m)``,
  SIMP_TAC std_ss [cut_def,UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val icut_update = prove(
  ``~irange (i,j) k ==> (icut (i,j) ((k =+ x) m) = icut (i,j) m)``,
  SIMP_TAC std_ss [icut_def,UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val update_update = prove(
  ``!m i x y. (i =+ y) ((i =+ x) m) = (i=+ y) m``,
  SIMP_TAC std_ss [FUN_EQ_THM,UPDATE_def]);

val expand_cut = prove(
  ``range (a,b) SUBSET range (c,d) /\ (cut(c,d)m=cut(c,d)n) ==> (cut(a,b)m=cut(a,b)n)``,
  SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,FUN_EQ_THM,range_def,cut_def] \\ METIS_TAC []);

val d1_SUBSET0 = prove(
  ``d1 (cut(j,j+1)m) SUBSET0 s /\ d1 (cut(i,j)m) SUBSET0 s ==> 
    d1 (cut(i,j+1)m) SUBSET0 s``,
  REWRITE_TAC [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ SIMP_TAC std_ss [IN_DEF,d1,cut_def,range_def,DECIDE ``k<n+1=k<=n``]
  \\ METIS_TAC [DECIDE ``n <= k \/ k < n:num``,fetch "-" "heap_type_distinct"]);

val swap_def = Define `
  swap i j = \k. if k = i then j else if k = j then i else k`;

val swap_swap = prove(
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
    
val bijection_swap = prove(
  ``!i j. bijection (swap i j)``,
  SIMP_TAC std_ss [bijection_def,ONTO_DEF,ONE_ONE_THM,swap_def]
  \\ REPEAT STRIP_TAC << [
    Cases_on `y = i` THEN1 (Q.EXISTS_TAC `j` \\ Cases_on `j = i` \\ ASM_REWRITE_TAC [])
    \\ Cases_on `y = j` THEN1 (Q.EXISTS_TAC `i` \\ Cases_on `j = i` \\ ASM_REWRITE_TAC [])
    \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [],    
    Cases_on `x1 = i` \\ Cases_on `x2 = i`
    \\ Cases_on `x1 = j` \\ Cases_on `x2 = j` \\ FULL_SIMP_TAC bool_ss []]);

val bijection_bijection = prove(
  ``!f g. bijection f /\ bijection g ==> bijection (f o g)``,
  SIMP_TAC std_ss [bijection_def,ONTO_DEF,ONE_ONE_THM] \\ METIS_TAC []);

val apply_apply = prove(
  ``!s f g. apply f (apply g s) = apply (g o f) s``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ SIMP_TAC std_ss [apply_def,IN_DEF]);

val apply_I = prove(
  ``!set. apply I set = set``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC 
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ SIMP_TAC std_ss [apply_def,IN_DEF]);

val range_IMP_NOT_dr0 = prove(
  ``!i j x m. range (i,j) x ==> ~dr0 (icut(i,j)m) x``,
  SIMP_TAC std_ss [dr0,d0,r0,icut_def,irange_def,range_def,heap_type_distinct]);

val d0_IMP = prove(
  ``d0 (cut (b,j) m) i ==> ?h g dd. range(b,j)i /\ (m i = DATA(h,g,dd))``,
  SIMP_TAC std_ss [d0,cut_def] \\ METIS_TAC [heap_type_distinct]);

val d1_IMP = prove(
  ``d1 (cut (b,i) m) j ==> 
    ?h g dd. range(b,i)h /\ (~(m h = DATA(j,g,dd)) ==> (m h = DATA(g,j,dd)))``,
  SIMP_TAC std_ss [d1,cut_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `k` \\ Cases_on `range (b,i) k` 
  \\ FULL_SIMP_TAC std_ss [heap_type_distinct,heap_type_11] \\ METIS_TAC []);

val lemma2 = prove(
  ``k IN d1 m /\ ~(j = x) /\ irange(b,e)x /\ ~(j = e) /\
    cheney_inv (b,b',i,j,j',e,f,m,w,xx,r) /\ (m x = DATA (n',n'',d')) /\ (m j = EMP) ==>
      (addr k (swap j x t) (((x =+ REF j) ((j =+ (DATA (n',n'',d'))) m)) k) =
       addr k t (m k))``,
  SIMP_TAC std_ss [UPDATE_def,swap_def] \\ Cases_on `k = j` \\ ASM_REWRITE_TAC [] << [      
    REPEAT STRIP_TAC 
    \\ `{j} SUBSET d1 m` by METIS_TAC [IN_EQ_SUBSET] \\ FULL_SIMP_TAC std_ss [cheney_inv_def]
    \\ `{j} SUBSET (d1 (icut (b,e) m)) \/ {j} SUBSET (d1 (cut (b,i) m)) \/ 
        {j} SUBSET (d1 (cut (i,j) m)) \/ {j} SUBSET (d1 (cut (j,e) m))` by
     (FULL_SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF,d1,GSYM range_def]
      \\ SIMP_TAC std_ss [cut_def,icut_def]
      \\ `irange(b,e)k' \/ range(b,i)k' \/ range(i,j)k' \/ range(j,e)k'` by 
         (REWRITE_TAC [range_def,irange_def] \\ DECIDE_TAC)
      \\ METIS_TAC [heap_type_distinct])
    THENL [
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]      
      \\ `{j} SUBSET 0 INSERT dr0 (icut (b,e) m)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF] THEN1 `F` by DECIDE_TAC
      \\ `range (b,e) j` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC range_IMP_NOT_dr0,
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]      
      \\ `{j} SUBSET 0 INSERT range (b,j)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF,range_def] 
      \\ `F` by DECIDE_TAC,
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF]      
      \\ `{j} SUBSET 0 INSERT dr0 (icut (b,e) m)` by METIS_TAC [SUBSET_TRANS]
      \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF] THEN1 `F` by DECIDE_TAC
      \\ `range (b,e) j` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC range_IMP_NOT_dr0,      
      FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_INSERT,IN_DEF,d1,cut_def,range_def]
      \\ `F` by METIS_TAC [heap_type_distinct]],    
    Cases_on `k = x` \\ ASM_SIMP_TAC std_ss [addr_def] THEN1 METIS_TAC []
    \\ Cases_on `m k` \\ ASM_REWRITE_TAC [addr_def] << [
      Cases_on `t = j` \\ Cases_on `t = x` \\ FULL_SIMP_TAC bool_ss [],
      REPEAT STRIP_TAC 
      \\ `~(n = x)` by 
       (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
        \\ `{x} SUBSET r1 m` by (SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF] \\ METIS_TAC [r1])
        \\ `{x} SUBSET range (b,j)` by METIS_TAC [cheney_inv_def,SUBSET_TRANS]
        \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,range_def,irange_def,cheney_inv_def]        
        \\ DECIDE_TAC)
      \\ `~(n = j)` by 
       (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
        \\ `{j} SUBSET r1 m` by (SIMP_TAC std_ss [GSYM IN_EQ_SUBSET,IN_DEF] \\ METIS_TAC [r1])
        \\ `{j} SUBSET range (b,j)` by METIS_TAC [cheney_inv_def,SUBSET_TRANS]
        \\ FULL_SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,range_def,irange_def,cheney_inv_def]        
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
    cheney_inv (b,b',i,j,j',e,f,m,w,xx,r) /\ irange (b,e) x /\ ~(x = 0) ==>
      (apply (swap j x) (abs((x =+ REF j) ((j =+ m x) m))) = abs m)``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a t u v. x' = (a,t,u,v)` by METIS_TAC [PAIR_EQ,PAIR]
  \\ ASM_SIMP_TAC std_ss [apply_def,IN_DEF,abs_def,lemma]    
  \\ `~(j = x)` by (FULL_SIMP_TAC bool_ss [irange_def,cheney_inv_def] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC 
  \\ Q.EXISTS_TAC `k` \\ Q.EXISTS_TAC `k'`
  \\ `k IN d1 m /\ k' IN d1 m` by (SIMP_TAC std_ss [IN_DEF,d1] \\ METIS_TAC [])
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

val cheney_inv_cut_lemma = prove(
  ``cheney_inv (b,b',i,j,j3,e,f,m,w,xx,r) /\ ~(j = e) /\ irange(b,e)x ==>
    (range (b,i) SUBSET range (b,j)) /\ ~range(b,j+1)x /\ ~range(b,i)j /\ ~range(b,i)x /\
    (range (b,j+1) SUBSET range (b,e)) /\ range (b,j) SUBSET0 range (b,j + 1) /\
    (range (i,j+1) SUBSET range (b,j+1)) /\ ~range(i,j+1)x /\ ~range(b,b')j /\ ~range(b,b')x /\
    ~range(i,j)j /\ ~range(b,e)x /\ ~range(b,j)j /\ ~range(b,j)x``,
  FULL_SIMP_TAC bool_ss [SUBSET_DEF,SUBSET0_DEF,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [IN_DEF,cheney_inv_def,range_def,irange_def] 
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val range_simp = prove(
  ``!i j k. ~(i = j) ==> (range(k,i+1)j = range(k,i)j)``,
  SIMP_TAC bool_ss [range_def,IN_DEF] \\ DECIDE_TAC);

val move_lemma = store_thm("move_lemma",
  ``cheney_inv (b,b',i,j,j3,e,f,m,w,xx,r) /\ {x} SUBSET0 dr0(icut(b,e)m) ==>
    (move(x,j,m) = (x2,j2,m2)) ==> 
    cheney_inv(b,b',i,j2,j3,e,f,m2,w,xx,r) /\ {x2} SUBSET0 range(b,j2) /\ j <= j2 /\
    (cut(b,j)m = cut(b,j)m2) /\ (dr0 (icut(b,e)m) = dr0 (icut(b,e)m2)) /\ 
    (if x = 0 then x2 = 0 else (m2 x = REF x2) /\ d0 (cut(b,j2)m2) x2) /\
    (!a i. (m a = REF i) ==> (m2 a = REF i)) /\
    (if ~(x = 0) /\ (m2 x = REF j) then j2 = j + 1 else j2 = j) /\
    (~(x = 0) /\ ~isREF (m x) ==> (abs m = apply (swap j x) (abs m2))) /\ x <= f``,
  Cases_on `x = 0` \\ ASM_SIMP_TAC bool_ss [move_def,PAIR_EQ,LESS_EQ_REFL] 
  \\ ASM_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT] 
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [ZERO_LESS_EQ]) \\ STRIP_TAC
  \\ `x <= f` by 
   (Cases_on `irange (b,e) x` \\ FULL_SIMP_TAC bool_ss [IN_DEF,dr0,d0,r0,
      icut_def,heap_type_distinct,cheney_inv_def,DECIDE ``x < j = ~(j <= x:num)``]    
    \\ METIS_TAC [heap_type_distinct]) \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `isREF (m x)` \\ ASM_REWRITE_TAC []  
  THEN1
   (FULL_SIMP_TAC bool_ss [isREF_def,getREF_def,PAIR_EQ]   
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ,SUBSET_REFL,LESS_EQ_REFL] 
    \\ ASM_SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC bool_ss [cheney_inv_def,heap_type_11] << [    
      Q.PAT_ASSUM `r1 m = range (b,j)` (fn th => REWRITE_TAC [GSYM th]) \\ DISJ2_TAC
      \\ SIMP_TAC bool_ss [GSYM IN_EQ_SUBSET,IN_DEF,r1] \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [cheney_inv_def,SUBSET_DEF,IN_DEF]
      \\ `r1 m i'` by (REWRITE_TAC [r1] \\ METIS_TAC []) \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [cheney_inv_def,SUBSET_DEF,IN_DEF]
      \\ `~range (b,i') i'` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
      \\ `r1 m i'` by (REWRITE_TAC [r1] \\ METIS_TAC []) \\ METIS_TAC []])
  \\ SIMP_TAC std_ss [LET_DEF]    
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
  \\ `irange (b,e) x /\ ?t u v. m x = DATA (t,u,v)` by 
    (FULL_SIMP_TAC bool_ss [IN_DEF,dr0,isREF_def,d0,r0,icut_def]
     \\ Cases_on `irange (b,e) x` 
     \\ FULL_SIMP_TAC bool_ss [heap_type_distinct] \\ METIS_TAC [])
  \\ `~(j = e)` by 
    (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [DECIDE ``m <= n - n = (m = 0)``,cheney_inv_def]     
     \\ `x IN d0 (icut(b,e)m)` by FULL_SIMP_TAC bool_ss [IN_DEF,d0,icut_def]
     \\ METIS_TAC [CARD_EQ_0,NOT_IN_EMPTY])
  \\ `icut(b,e) ((x =+ (REF j)) ((j =+ m x) m)) = 
      icut(b,e) ((x =+ (REF j)) m)` by   
     (Cases_on `x = j` \\ ASM_REWRITE_TAC [update_update]
      \\ SIMP_TAC std_ss [icut_def,FUN_EQ_THM,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `irange (b,e) x'` \\ ASM_REWRITE_TAC []
      \\ Cases_on `x = x'` \\ ASM_REWRITE_TAC []
      \\ `~(j = x')` by (FULL_SIMP_TAC bool_ss [cheney_inv_def,irange_def] \\ DECIDE_TAC)
      \\ ASM_REWRITE_TAC []) 
  \\ `abs ((x =+ REF j) ((j =+ DATA (t,u,v)) m)) = apply (swap j x) (abs m)` by 
       (Q.PAT_ASSUM `m x = DATA (t,u,v)` (fn th => REWRITE_TAC [GSYM th] \\ ASSUME_TAC th)
        \\ REWRITE_TAC [GSYM move_lemma2]     
        \\ MATCH_MP_TAC (GEN_ALL move_lemma_lemma)
        \\ Q.EXISTS_TAC `xx` \\ Q.EXISTS_TAC `f` \\ Q.EXISTS_TAC `v` 
        \\ Q.EXISTS_TAC `b` \\ Q.EXISTS_TAC `b'` \\ Q.EXISTS_TAC `i`
        \\ Q.EXISTS_TAC `j3` \\ Q.EXISTS_TAC `e` \\ Q.EXISTS_TAC `w`
        \\ Q.EXISTS_TAC `r` \\ Q.EXISTS_TAC `t` \\ Q.EXISTS_TAC `u`
        \\ FULL_SIMP_TAC std_ss [cheney_inv_def] 
        \\ `j <= j /\ j < e` by DECIDE_TAC
        \\ METIS_TAC [])
  \\ IMP_RES_TAC cheney_inv_cut_lemma
  \\ REPEAT (Q.PAT_ASSUM `!tyu.fgh` (fn th => ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [cheney_inv_def] 
  \\ ASM_SIMP_TAC bool_ss [cut_update,apply_apply,swap_swap,apply_I]
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC THEN1 DECIDE_TAC
  THEN1    
     (`~(k = j) /\ ~(k = x)` by (FULL_SIMP_TAC bool_ss [irange_def] \\ DECIDE_TAC)
      \\ ASM_SIMP_TAC bool_ss [UPDATE_def] \\ METIS_TAC [DECIDE ``j + 1 <= k ==> j <= k``])
  THEN1
     (`~(k = j) /\ ~(x = k)` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [UPDATE_def])
  THEN1
     (ASM_SIMP_TAC std_ss [FUN_EQ_THM,d0,cut_def,range_def,IN_DEF]
      \\ STRIP_TAC \\ Cases_on `x' = j` \\ ASM_REWRITE_TAC []
      \\ ASM_SIMP_TAC std_ss [UPDATE_def] THEN1 METIS_TAC [heap_type_distinct]     
      \\ ASM_SIMP_TAC bool_ss [DECIDE ``~(x = n) ==> (x < n + 1 = x < n)``]
      \\ REWRITE_TAC [GSYM range_def]
      \\ Cases_on ` range (b,j) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
      \\ FULL_SIMP_TAC bool_ss [d0,FUN_EQ_THM,cut_def] \\ METIS_TAC [])
  THEN1
     (MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `range (b,j)` \\ ASM_REWRITE_TAC [])
  THEN1      
     (Q.PAT_ASSUM `m x = DATA (t,u,v)` (ASSUME_TAC o GSYM) \\ ASM_REWRITE_TAC []
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `dr0 (icut (b,e) m)`
      \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ STRIP_TAC THEN1
       (REWRITE_TAC [dr0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
        \\ SIMP_TAC std_ss [IN_DEF,dr0,UPDATE_def,icut_def,FUN_EQ_THM,d0,r0]
        \\ STRIP_TAC \\ Cases_on `irange (b,e) x'` 
        \\ ASM_REWRITE_TAC [heap_type_distinct] \\ METIS_TAC [])
      \\ MATCH_MP_TAC d1_SUBSET0 \\ ASM_SIMP_TAC bool_ss [cut_update]
      \\ Q.PAT_ASSUM `DATA (t,u,v) = m x` (ASSUME_TAC o GSYM) \\ ASM_REWRITE_TAC []
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `{t;u}` \\ STRIP_TAC THEN1      
       (REWRITE_TAC [dr0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,cut_def]
        \\ SIMP_TAC std_ss [IN_DEF,dr0,UPDATE_def,icut_def,FUN_EQ_THM,d0,r0]
        \\ SIMP_TAC std_ss [range_def,DECIDE ``j <= k /\ k < j+1 = (j = k)``,d1]
        \\ REPEAT (POP_ASSUM (fn th => ALL_TAC))
        \\ REPEAT STRIP_TAC \\ Cases_on `j = k` 
        \\ FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ,heap_type_distinct])
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `d1 (icut (b,e) m)` \\ STRIP_TAC THEN1
       (REWRITE_TAC [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
        \\ MATCH_MP_TAC (METIS_PROVE [] ``x /\ y ==> (t \/ x) /\ (d:bool \/ y)``)
        \\ SIMP_TAC std_ss [IN_DEF,d1,icut_def] \\ METIS_TAC [])
      \\ ASM_REWRITE_TAC [])
  THEN1
     (MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `d1 (icut (b,e) m)` \\ STRIP_TAC THEN1
       (REWRITE_TAC [dr0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,cut_def,d1]
        \\ SIMP_TAC std_ss [IN_DEF,dr0,UPDATE_def,icut_def,FUN_EQ_THM,d0,r0,d1]
        \\ METIS_TAC [heap_type_11,PAIR_EQ,heap_type_distinct])
      \\ MATCH_MP_TAC SUBSET0_TRANS
      \\ Q.EXISTS_TAC `dr0 (icut (b,e) m)` \\ ASM_REWRITE_TAC []
      \\ REWRITE_TAC [dr0,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,cut_def,d1]
      \\ SIMP_TAC std_ss [IN_DEF,dr0,UPDATE_def,icut_def,FUN_EQ_THM,d0,r0]
      \\ METIS_TAC [heap_type_11,PAIR_EQ,heap_type_distinct])
  THEN1 
     (`j < e` by DECIDE_TAC
      \\ `m j = EMP` by METIS_TAC [LESS_EQ_REFL]
      \\ `!xx. r1 ((x =+ REF j) ((j =+ DATA (t,u,v)) m)) xx = (j = xx) \/ r1 m xx` by ALL_TAC 
      THENL [ALL_TAC,ASM_SIMP_TAC bool_ss [FUN_EQ_THM,range_def] \\ DECIDE_TAC]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC bool_ss [r1,UPDATE_def] << [        
        Cases_on `x = k` \\ FULL_SIMP_TAC bool_ss [heap_type_11]
        \\ Cases_on `j = k` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct] \\ METIS_TAC [],        
        Q.EXISTS_TAC `x` \\ METIS_TAC [],
        Q.EXISTS_TAC `k` \\ Cases_on `k = x` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]
        \\ Cases_on `j = k` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]])
  THEN1
   (Cases_on `k = j` << [
      Cases_on `i' = x` THENL [ALL_TAC,
        Cases_on `j = i'` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
        \\ FULL_SIMP_TAC bool_ss [FUN_EQ_THM,r1] \\ METIS_TAC []]
      \\ Cases_on `j' = x` THENL [ALL_TAC,
        Cases_on `j = j'` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
        \\ FULL_SIMP_TAC bool_ss [FUN_EQ_THM,r1] \\ METIS_TAC []]
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
      \\ `d0 (icut (b,e) ((x =+ REF j) m)) = d0 (icut (b,e) m) DELETE x` by      
       (REWRITE_TAC [EXTENSION,IN_DELETE]
        \\ SIMP_TAC std_ss [IN_DEF,icut_def,d0,UPDATE_def] \\ STRIP_TAC 
        \\ Cases_on `irange (b,e) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
        \\ Cases_on `x' = x` \\ ASM_REWRITE_TAC [heap_type_distinct])        
      \\ ASM_SIMP_TAC bool_ss [CARD_DELETE]   
      \\ `x IN d0 (icut (b,e) m)` by 
        (ASM_SIMP_TAC std_ss [IN_DEF,d0,icut_def] \\ METIS_TAC [])
      \\ ASM_SIMP_TAC bool_ss [] \\ DECIDE_TAC)
  THEN1
     (`d0 (icut (b,e) ((x =+ REF j) m)) = d0 (icut (b,e) m) DELETE x` by      
       (REWRITE_TAC [EXTENSION,IN_DELETE]
        \\ SIMP_TAC std_ss [IN_DEF,icut_def,d0,UPDATE_def] \\ STRIP_TAC 
        \\ Cases_on `irange (b,e) x'` \\ ASM_REWRITE_TAC [heap_type_distinct]
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
      \\ STRIP_TAC << [
        STRIP_TAC \\ Cases_on `x = k` \\ ASM_SIMP_TAC bool_ss [isREF_def,heap_type_11]
        \\ Cases_on `k = j` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]
        \\ REPEAT STRIP_TAC << [
          `b <=i /\ i <= j ==> range(b,j+1)j` by (REPEAT (POP_ASSUM (K ALL_TAC)) 
             \\ SIMP_TAC std_ss [range_def] \\ DECIDE_TAC)
          \\ METIS_TAC [],        
          `~range(b,j)k` by METIS_TAC [range_simp]
          \\ `v' k = k` by METIS_TAC [isREF_def]
          \\ ASM_SIMP_TAC bool_ss [swap_def]],
        STRIP_TAC \\ Cases_on `k = x` \\ ASM_SIMP_TAC bool_ss [heap_type_11] 
        THEN1 (SIMP_TAC std_ss [swap_def] \\ METIS_TAC [])
        \\ Cases_on `k = j` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]    
        \\ REPEAT STRIP_TAC \\ `v' k = i'` by METIS_TAC []
        \\ ASM_SIMP_TAC std_ss []
        \\ `r1 m i'` by METIS_TAC [r1]
        \\ `range(b,j)i'` by METIS_TAC [cheney_inv_def]
        \\ `~(j = i') /\ ~(x = i')` by METIS_TAC [] 
        \\ ASM_SIMP_TAC std_ss [swap_def]])
  THEN1 (SIMP_TAC std_ss [range_def,IN_DEF] \\ DECIDE_TAC)
  THEN1
     (ASM_SIMP_TAC std_ss [dr0,d0,r0,icut_def,FUN_EQ_THM,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `irange (b,e) x'` \\ ASM_REWRITE_TAC []
      \\ Cases_on `x = x'` \\ ASM_SIMP_TAC std_ss [heap_type_11] THEN1 METIS_TAC [])    
  THEN1 (SIMP_TAC bool_ss [UPDATE_def])  
  THEN1 (IMP_RES_TAC LESS_EQ_TRANS 
         \\ ASM_SIMP_TAC std_ss [d0,cut_def,range_def,UPDATE_def] \\ METIS_TAC [])
  THEN1
     (Cases_on `a = x` \\ FULL_SIMP_TAC bool_ss [] THEN1 METIS_TAC [heap_type_distinct]
      \\ `j < e` by DECIDE_TAC 
      \\ `m j = EMP` by METIS_TAC [LESS_EQ_REFL]      
      \\ Cases_on `a = j` \\ FULL_SIMP_TAC bool_ss [] THEN1 METIS_TAC [heap_type_distinct]
      \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1 SIMP_TAC std_ss [UPDATE_def]);

val abs_update_lemma = prove(
  ``!m i x y d x' y'.
      (m i = DATA (x,y,d)) /\ (m 0 = EMP) /\
      (if x = 0 then x' = 0 else (m x = REF x') /\ d0 m x') /\ 
      (if y = 0 then y' = 0 else (m y = REF y') /\ d0 m y') ==>
      (abs ((i =+ DATA (x',y',d))m) = abs m)``,
  REWRITE_TAC [FUN_EQ_THM,d0] \\ REPEAT STRIP_TAC
  \\ `?a0 x0 y0 d0. x'' = (a0,x0,y0,d0)` by METIS_TAC [PAIR]  
  \\ ASM_SIMP_TAC bool_ss [abs_def,UPDATE_thm] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Cases_on `a0 = i` << [
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      THENL [Cases_on `x = 0`,Cases_on `y = 0`]        
      \\ FULL_SIMP_TAC bool_ss [addr_def] \\ METIS_TAC [addr_def],
      FULL_SIMP_TAC std_ss [heap_type_11]
      \\ Cases_on `k = i` \\ Cases_on `k' = i`
      \\ FULL_SIMP_TAC bool_ss [addr_def]],
    Cases_on `a0 = i` << [    
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      THENL [Cases_on `x = 0`,Cases_on `y = 0`]        
      \\ FULL_SIMP_TAC bool_ss [addr_def] \\ METIS_TAC [addr_def],
      FULL_SIMP_TAC std_ss [heap_type_11] \\ STRIP_TAC
      \\ Cases_on `k = i` \\ Cases_on `k' = i`
      \\ FULL_SIMP_TAC bool_ss [addr_def] \\ METIS_TAC [addr_def]]]);

val maintain_lemma = prove(
  ``!b i j j2 m x y.
      b <= i /\ i <= j /\ 
      range (i,j) SUBSET (r UNION d1 (cut (b,i) m)) /\ 
      range (j,j2) SUBSET {x;y} ==>
      range (i + 1,j2) SUBSET (r UNION d1 (cut (b,i + 1) ((i =+ DATA (x,y,d)) m)))``,
  SIMP_TAC bool_ss [SUBSET_DEF,IN_UNION,NOT_IN_EMPTY,IN_INSERT] 
  \\ SIMP_TAC bool_ss [IN_DEF,d1,cut_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `r x'` \\ ASM_REWRITE_TAC []    
  \\ `range (j,j2) x' \/ range (i,j) x'` by ALL_TAC << [
    FULL_SIMP_TAC std_ss [range_def] \\ DECIDE_TAC,  
    `range (b,i + 1) i` by (FULL_SIMP_TAC std_ss [range_def] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `i` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_type_11] \\ METIS_TAC [],
    RES_TAC \\ Cases_on `range(b,i)k` \\ FULL_SIMP_TAC std_ss [heap_type_distinct]
    \\ `range (b,i + 1) k /\ ~(i = k)` by (FULL_SIMP_TAC std_ss [range_def] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `k` \\ ASM_SIMP_TAC std_ss [UPDATE_def,heap_type_11] \\ METIS_TAC []]);

val range_split = prove(
  ``j <= j' ==> j' <= j'' ==> (range(j,j'') = range (j,j') UNION range(j',j''))``,
  REWRITE_TAC [EXTENSION,IN_UNION] \\ SIMP_TAC std_ss [IN_DEF,range_def] \\ DECIDE_TAC);

val range_lemmas = prove(
  ``!n. (range(n,n+1) = {n}) /\ (range(n,n) = {})``,
  REWRITE_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY] 
  \\ SIMP_TAC bool_ss [range_def,IN_DEF] \\ DECIDE_TAC);

val path_cut_expand = prove(
  ``!p r b i j m. path (r,p) (basic_abs(cut (b,i) m)) /\ i <= j ==> 
                  path (r,p) (basic_abs(cut (b,j) m))``,
  Induct \\ REWRITE_TAC [path_def] \\ REPEAT STRIP_TAC 
  \\ `range (b,i) r ==> range (b,j) r` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [cut_def,basic_abs,IN_DEF] 
  \\ METIS_TAC [heap_type_distinct]);

val reachable_cut_expand = prove(
  ``!r b i j m. reachable r (basic_abs (cut (b,i) m)) x /\ i <= j ==>
                reachable r (basic_abs (cut (b,j) m)) x``,
  SIMP_TAC bool_ss [reachable_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [path_cut_expand]);
    
val cut_EQ_EMP_IMP = prove(
  ``(cut (b,i) m x = EMP) /\ range(b,i)x ==> (m x = EMP)``,
  SIMP_TAC std_ss [d0,cut_def] \\ METIS_TAC []);

val path_snoc = prove(
  ``!ys x y z m. path(x,ys++[y])m /\ path(y,[z])m ==> path(x,ys++[y]++[z])m``, 
  Induct THEN1 (REWRITE_TAC [APPEND,path_def] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [path_def,APPEND]);

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
  \\ Q.PAT_ASSUM `i + 1 = i2` (K ALL_TAC)
  \\ Q.PAT_ASSUM `j'' = j2` (K ALL_TAC)
  \\ Q.PAT_ASSUM `e = e2` (K ALL_TAC)
  \\ Q.PAT_ASSUM `(i =+ DATA (x',y',d)) m'' = m2` (K ALL_TAC)
  \\ `i <= e` by (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)  
  \\ Q.PAT_ASSUM `~(j = i)` (ASSUME_TAC o GSYM)
  \\ `?ax ay ad. m i = DATA (ax,ay,ad)` by METIS_TAC [m_DATA]
  \\ `~irange (b,e) i /\ i + 1 <= j /\ b <= i /\ i <= j /\ ~range(b,i)i /\ range(i,j) i` by 
     (FULL_SIMP_TAC bool_ss [cheney_inv_def,irange_def,range_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [getDATA_def,PAIR_EQ]
  \\ `{x;y} SUBSET0 d1 (cut(i,j)m)` by 
   (SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]   
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,d1,range_def,cheney_inv_def,cut_def] 
    \\ `i <= i /\ i < j` by DECIDE_TAC
    \\ STRIP_TAC \\ DISJ2_TAC \\ Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [])
  \\ `{x;y} SUBSET0 dr0 (icut(b,e)m)` by 
    (MATCH_MP_TAC SUBSET0_TRANS \\ METIS_TAC [cheney_inv_def])
  \\ `{x} SUBSET0 dr0 (icut(b,e)m)` by 
    FULL_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ IMP_RES_TAC move_lemma
  \\ `{y} SUBSET0 dr0 (icut(b,e)m')` by
    FULL_SIMP_TAC bool_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ IMP_RES_TAC move_lemma
  \\ Q.PAT_ASSUM `cheney_inv (b,b',i,j,j,e,f,m,w,xx,r)` (fn th => ALL_TAC)
  \\ Q.PAT_ASSUM `cheney_inv (b,b',i,j',j,e,f,m',w,xx,r)` (fn th => ALL_TAC)  
  \\ FULL_SIMP_TAC bool_ss [cheney_inv_def]
  \\ ASM_SIMP_TAC bool_ss [icut_update] THEN1 DECIDE_TAC
  \\ REPEAT STRIP_TAC
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  THEN1 
   (`~(k = i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1 
   (`~(k = i)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])  
  THEN1
   (`d0 (cut (b,j'') ((i =+ DATA (x',y',d)) m'')) = 
     i INSERT d0 (cut (b,j'') m'')` by ALL_TAC << [
      SIMP_TAC std_ss [EXTENSION,d0,cut_def,IN_INSERT]
      \\ SIMP_TAC std_ss [IN_DEF,d0,UPDATE_def] \\ STRIP_TAC
      \\ Cases_on `range (b,j'') x''` \\ ASM_SIMP_TAC std_ss [heap_type_distinct]
      THEN1 (Cases_on `x'' = i` \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
      \\ FULL_SIMP_TAC bool_ss [range_def,irange_def] \\ DECIDE_TAC,      
      ASM_SIMP_TAC std_ss [EXTENSION,IN_INSERT]    
      \\ SIMP_TAC std_ss [range_def,IN_DEF]
      \\ STRIP_TAC \\ Cases_on `x'' = i` \\ ASM_SIMP_TAC std_ss  [] \\ DECIDE_TAC])
  THEN1
   (MATCH_MP_TAC d1_SUBSET0
    \\ `~range(b,i)i` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [cut_update]
    \\ `d1 (cut (i,i + 1) ((i =+ DATA (x',y',d))m'')) = {x';y'}` by ALL_TAC << [
      ASM_SIMP_TAC std_ss [d1,EXTENSION,IN_INSERT,NOT_IN_EMPTY]
      \\ ASM_SIMP_TAC std_ss [d1,IN_DEF,cut_def,range_def,DECIDE ``i<=k/\k<i+1 = (k = i)``]
      \\ SIMP_TAC bool_ss [UPDATE_def] 
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ Cases_on `k = i` \\ FULL_SIMP_TAC bool_ss [heap_type_11,heap_type_distinct,PAIR_EQ]
      \\ METIS_TAC [],    
      ASM_REWRITE_TAC []
      \\ `range(b,j') SUBSET range(b,j'')` by 
         (SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,range_def] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET]      
      \\ METIS_TAC [IN_INSERT,SUBSET_DEF]])
  THEN1
   (MATCH_MP_TAC maintain_lemma \\ Q.EXISTS_TAC `j`
    \\ ASSUME_TAC (UNDISCH_ALL range_split) 
    \\ ASM_SIMP_TAC bool_ss [UNION_SUBSET] \\ STRIP_TAC
    THENL [Cases_on `~(x = 0) /\ (m' x = REF j)`,Cases_on `~(y = 0) /\ (m'' y = REF j')`]    
    \\ NTAC 2 (FULL_SIMP_TAC bool_ss 
        [heap_type_11,range_lemmas,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]))
  THEN1
   (`~(range(i+1,j'')i)` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [cut_update]  
    \\ MATCH_MP_TAC SUBSET0_TRANS
    \\ Q.EXISTS_TAC `d1 (cut (i,j'') m'')` \\ ASM_SIMP_TAC bool_ss []
    \\ SIMP_TAC std_ss [d1,SUBSET_DEF,SUBSET0_DEF,IN_INSERT]  
    \\ SIMP_TAC std_ss [d1,IN_DEF,cut_def,range_def]  
    \\ METIS_TAC [DECIDE ``i + 1 <= k /\ k < j'' ==> i <= k /\ k < j''``,heap_type_distinct])
  THEN1
   (Q.PAT_ASSUM `r1 m'' = range (b,j'')` (fn th => REWRITE_TAC [GSYM th])
    \\ `m'' i = DATA (ax,ay,ad)` by 
     (`range (b,j) i /\ range (b,j') i` by ALL_TAC
      \\ FULL_SIMP_TAC bool_ss [cut_def,FUN_EQ_THM]
      THEN1 (REWRITE_TAC [range_def] \\ DECIDE_TAC)\\ METIS_TAC [])
    \\ SIMP_TAC std_ss [r1,IN_DEF,cut_def,range_def,SUBSET_DEF,UPDATE_def,FUN_EQ_THM]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC [heap_type_distinct])
  THEN1
   (Cases_on `i = j'''` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct,UPDATE_def]
    \\ Cases_on `i = i'` \\ FULL_SIMP_TAC bool_ss [heap_type_distinct,UPDATE_def] \\ METIS_TAC [])
  THEN1
   (`~(i = 0)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [UPDATE_def])
  THEN1
   (MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `i INSERT range(b,i)` \\ STRIP_TAC
    THEN1 (REWRITE_TAC [SUBSET_DEF,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF,range_def] \\ DECIDE_TAC)
    \\ REWRITE_TAC [INSERT_SUBSET] \\ SIMP_TAC std_ss [IN_DEF] \\ STRIP_TAC << [     
      SIMP_TAC std_ss [reachable_def,basic_abs]
      \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT,IN_UNION]
      \\ FULL_SIMP_TAC bool_ss [IN_DEF]
      \\ `(r i) \/ d1 (cut (b,i) m'') i` by METIS_TAC [] 
      THEN1 METIS_TAC [] \\ IMP_RES_TAC d1_IMP      
      \\ `?t. r t /\ reachable t (basic_abs (cut (b,i) m'')) h` by METIS_TAC []
      \\ `path (h,[i]) (basic_abs (cut (b,i + 1) ((i =+ DATA (x',y',d))m'')))` by
       (`range (b,i+1) h /\ ~(h = i)` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)        
        \\ ASM_SIMP_TAC std_ss [path_def,APPEND,IN_DEF,basic_abs,cut_def,UPDATE_def]
        \\ METIS_TAC [])
      \\ Q.EXISTS_TAC `t` \\ FULL_SIMP_TAC bool_ss [reachable_def]  \\ DISJ2_TAC
      THEN1 (Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [APPEND])
      \\ Q.EXISTS_TAC `p ++ [h]` \\ MATCH_MP_TAC path_snoc \\ ASM_SIMP_TAC bool_ss []
      \\ MATCH_MP_TAC path_cut_expand \\ Q.EXISTS_TAC `i` 
      \\ ASM_SIMP_TAC bool_ss [cut_update] \\ DECIDE_TAC,
      FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ `?t. r t /\ reachable t (basic_abs (cut (b,i) m'')) x''`  by METIS_TAC []
      \\ Q.EXISTS_TAC `t` \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC reachable_cut_expand \\ Q.EXISTS_TAC `i` 
      \\ ASM_SIMP_TAC bool_ss [cut_update] \\ DECIDE_TAC])
  THEN1
   (`m'' k = REF i'` by METIS_TAC []
    \\ Cases_on `k = i` \\ ASM_SIMP_TAC bool_ss [UPDATE_def]
    \\ `range(b,j'')i` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
    \\ `d0 (cut (b,j'') m'') i` by METIS_TAC [] \\ IMP_RES_TAC d0_IMP
    \\ `F` by METIS_TAC [heap_type_distinct])
  THEN1   
   (`!x i j m. d0 (cut (i,j) m) x ==> d0 m x` by
      (SIMP_TAC bool_ss [d0,cut_def] \\ METIS_TAC [heap_type_distinct])
    \\ `abs ((i =+ DATA (x',y',d))m'') = abs m''` by ALL_TAC << [
      MATCH_MP_TAC (GEN_ALL abs_update_lemma) 
      \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `y` \\ ASM_SIMP_TAC bool_ss [heap_type_11]
      \\ REPEAT (Q.PAT_ASSUM `fgh SUBSET0 jkl` (fn th => ALL_TAC))
      \\ `range(b,j) i /\ range(b,j') i` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
      \\ `(m'' i = m i)` by (FULL_SIMP_TAC bool_ss [cut_def,FUN_EQ_THM] \\ METIS_TAC [])
      \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC 
      THEN1 (Cases_on `x = 0` \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC [])
      THEN1 (Cases_on `y = 0` \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC []),
      FULL_SIMP_TAC bool_ss [roots_inv_def] \\ Q.EXISTS_TAC `v`
      \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC \\ STRIP_TAC
      \\ `range(b,j'') i` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
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
    let m = cut (i,i+l) m in
      (j,i+l,root,l,u,m)`;

val cheney_alloc_aux_def = Define `
  cheney_alloc_aux (i,e,root,l,u,m) =
    if i < e then (i,e,root,l,u,m) else cheney_collector(i,e,root,l,u,m)`;

val cheney_alloc_aux2_def = Define `
  cheney_alloc_aux2 (i,e,root,l,u,m) d =
    if i = e then (i,e,root,l,u,m) else
      let m = (i =+ DATA(HD root,HD (TL root),d)) m in
        (i+1,e,i::TL root,l,u,m)`;

val cheney_alloc_def = Define `
  cheney_alloc(i,e,root,l,u,m) d = cheney_alloc_aux2 (cheney_alloc_aux(i,e,root,l,u,m)) d`;

val cut_EMPTY = prove(
  ``!b m. (cut (b,b) m = \x.EMP) /\ (icut (b,b) m = m) /\ 
          (range(b,b) = \x.F) /\ (irange(b,b) = \x.T)``,
  SIMP_TAC std_ss [FUN_EQ_THM,range_def,cut_def,icut_def,range_def,irange_def]
  \\ METIS_TAC [DECIDE ``~(b <= n /\ n < b:num)``]);
  
val FINITE_range = prove(
  ``!j i. FINITE (range(i,i+j)) /\ (CARD (range(i,i+j)) = j)``,
  Induct \\ REWRITE_TAC [cut_EMPTY,ADD_0,FINITE_EMPTY,CARD_EMPTY,GSYM EMPTY_DEF] \\ STRIP_TAC
  \\ `(range (i,i + SUC j) = (i + j) INSERT range (i,i + j)) /\
     ~((i + j) IN range (i,i + j))` by ALL_TAC
  \\ ASM_SIMP_TAC bool_ss [FINITE_INSERT,CARD_INSERT,EXTENSION,IN_INSERT]
  \\ SIMP_TAC std_ss [IN_DEF,range_def] \\ DECIDE_TAC);

val FINITE_range2 = prove(
  ``!i j. FINITE (range(i,j)) /\ (CARD (range(i,j)) = j - i)``,
  NTAC 2 STRIP_TAC \\ Cases_on `i <= j`  
  THEN1 (FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,FINITE_range] \\ DECIDE_TAC)
  \\ `range (i,j) = EMPTY` by ALL_TAC \\ ASM_REWRITE_TAC [FINITE_EMPTY,CARD_EMPTY]
  \\ FULL_SIMP_TAC bool_ss [EXTENSION,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [IN_DEF,range_def] \\ DECIDE_TAC);

val WFS_inv_IMP_cheney_inv = store_thm("ok_state_IMP_cheney_inv",
  ``ok_state (i,e6,r,l,u,m) ==>
    let b = if ~u then 1 + l else 1 in
      cheney_inv (b,b,b,b,b,b + l,l+l+1,m,m,m,{}) /\
      !k. MEM k r ==> {k} SUBSET0 dr0 (icut (b,b+l) m)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF,cheney_inv_def,ok_state_def,cut_EMPTY]  
  \\ Q.ABBREV_TAC `b = if u then 1 + l else 1`
  \\ Q.ABBREV_TAC `b2 = if ~u then 1 + l else 1`
  \\ `(icut (b2,b2 + l) m) = m` by 
   (FULL_SIMP_TAC bool_ss [icut_def,FUN_EQ_THM,IN_DEF]
    \\ `!k. range(b,i)k ==> irange (b2,b2 + l) k` by ALL_TAC
    THENL [ALL_TAC,METIS_TAC []] \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2`
    \\ Cases_on `u` \\ FULL_SIMP_TAC bool_ss [irange_def,range_def] \\ DECIDE_TAC)    
  \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  THEN1 (Q.UNABBREV_TAC `b2` \\ Cases_on `u` \\ DECIDE_TAC)
  THEN1 (Q.UNABBREV_TAC `b2` \\ Cases_on `u` \\ DECIDE_TAC)  
  THEN1 
   (Q.PAT_ASSUM `!k. ~b:bool ==> c` MATCH_MP_TAC  
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,range_def] 
    \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2` \\ DECIDE_TAC)
  THEN1 
   (Q.PAT_ASSUM `!k. ~b:bool ==> c` MATCH_MP_TAC  
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,range_def] 
    \\ Q.UNABBREV_TAC `b` \\ Q.UNABBREV_TAC `b2` \\ DECIDE_TAC)
  THEN1 (SIMP_TAC std_ss [FUN_EQ_THM,d0,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,d1,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,d1,heap_type_distinct])
  THEN1 (SIMP_TAC std_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
    \\ SIMP_TAC std_ss [IN_DEF,d1,heap_type_distinct])
  THEN1 
   (FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,dr0,d1,d0,icut_def] \\ REPEAT STRIP_TAC
    \\ `range(b,i)k` by METIS_TAC [heap_type_distinct]
    \\ Cases_on `x = 0` \\ ASM_SIMP_TAC bool_ss []
    \\ `range(b,i)x` by METIS_TAC [heap_type_11,PAIR_EQ]
    \\ ASM_REWRITE_TAC [] \\ METIS_TAC [])
  THEN1 (ASM_SIMP_TAC std_ss [FUN_EQ_THM,r1] \\ METIS_TAC [heap_type_distinct])
  THEN1 METIS_TAC [heap_type_distinct]
  THEN1 
   (MATCH_MP_TAC LESS_EQ_TRANS \\ Q.EXISTS_TAC `CARD (range(b,i))` \\ STRIP_TAC 
    THENL [ALL_TAC, REWRITE_TAC [FINITE_range2] \\ DECIDE_TAC]     
    \\ MATCH_MP_TAC ((GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o 
                     SPEC_ALL o UNDISCH o SPEC_ALL) CARD_SUBSET)
    \\ FULL_SIMP_TAC std_ss [FINITE_range2,SUBSET_DEF,IN_DEF,d0]
    \\ METIS_TAC [heap_type_distinct])
  THEN1
   (MATCH_MP_TAC ((GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o 
                  SPEC_ALL o UNDISCH o SPEC_ALL) SUBSET_FINITE)
    \\ Q.EXISTS_TAC `range(b,i)` \\ FULL_SIMP_TAC std_ss [d0,SUBSET_DEF,IN_DEF,icut_def,FINITE_range2]
    \\ METIS_TAC [heap_type_distinct])
  THEN1  
   (Q.PAT_ASSUM `!k. ~b:bool ==> c` MATCH_MP_TAC  
    \\ Q.UNABBREV_TAC `b` \\ Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def,IN_DEF] \\ DECIDE_TAC)
  THEN1 REWRITE_TAC [GSYM EMPTY_DEF,EMPTY_SUBSET]
  THEN1 
   (REWRITE_TAC [roots_inv_def] \\ Q.EXISTS_TAC `I` \\ ASM_SIMP_TAC std_ss [apply_I] 
    \\ METIS_TAC [heap_type_distinct])
  THEN1
   (Cases_on `k = 0` THEN1 ASM_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ REWRITE_TAC [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ RES_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [IN_DEF,dr0,d0,heap_type_11] \\ METIS_TAC []));    

val bijection_inv = prove(
  ``!f. bijection f ==> ?g. (f o g = I) /\ (g o f = I) /\ bijection g``,
  SIMP_TAC std_ss [bijection_def,ONE_ONE_DEF,ONTO_DEF,FUN_EQ_THM] 
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `\x. @y. f y = x` \\ METIS_TAC []);

val reachables_def = Define `
  reachables rs h (a,x,y,d) = (a,x,y,d) IN h /\ ?r. MEM r rs /\ a IN reachable r h`;
 
val basic_abs_EQ_abs = prove(
  ``!m. (!k i. ~(m k = REF i)) ==> (basic_abs m = abs m)``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a y z d. x = (a,y,z,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [abs_def,basic_abs]  
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [  
    Q.EXISTS_TAC `y` \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC [] 
    \\ STRIP_TAC THENL [Cases_on `m y`,Cases_on `m z`]
    \\ FULL_SIMP_TAC bool_ss [addr_def] \\ METIS_TAC [],
    FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ] 
    \\ STRIP_TAC THENL [Cases_on `m k`,Cases_on `m k'`]
    \\ FULL_SIMP_TAC bool_ss [addr_def] \\ METIS_TAC []]);

val apply_reachables_lemma = prove(
  ``(!x. f (g x) = x) /\ (!x. g (f x) = x) ==> 
    path (r,p ++ [g a]) set ==> path (f r,MAP f p ++ [a]) (apply g set)``,
  STRIP_TAC \\ Q.SPEC_TAC (`r`,`r`) \\ Q.SPEC_TAC (`p`,`p`) \\ Induct
  \\ ASM_SIMP_TAC std_ss [APPEND,MAP,path_def,IN_DEF,apply_def] \\ METIS_TAC []);

val apply_reachables = prove(
  ``!r f g set. (f o g = I) /\ (g o f = I) ==> 
                (apply g (reachables r set) = reachables (MAP f r) (apply g set))``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `?a y z d. x = (a,y,z,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [reachables_def,IN_DEF,apply_def,reachable_def,MEM_MAP]  
  \\ Cases_on `set (g a,g y,g z,d)` \\ ASM_REWRITE_TAC [] 
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 METIS_TAC [apply_reachables_lemma]  
  THEN1 METIS_TAC [apply_reachables_lemma]  
  THEN1 METIS_TAC [apply_reachables_lemma]  
  \\ Q.EXISTS_TAC `y'` \\ ASM_REWRITE_TAC [] 
  \\ DISJ2_TAC \\ Q.EXISTS_TAC `MAP g p`
  \\ Q.UNDISCH_TAC `path (r',p ++ [a]) (apply g set)`
  \\ ASM_REWRITE_TAC []
  \\ Q.SPEC_TAC (`y'`,`yy`) \\ Induct_on `p`
  \\ ASM_SIMP_TAC std_ss [APPEND,MAP,path_def,IN_DEF,apply_def] \\ METIS_TAC []);

val path_cut = prove(
  ``!p r x i j m. 
      range(i,j)r /\ ~range(i,j)x /\ path (r,p ++ [x]) (abs m) /\ ~(x = 0) /\ (m 0 = EMP) ==> 
      ?s d. path(s,[d]) (abs m) /\ range(i,j)s /\ ~range(i,j)d /\ ~(d = 0)``,
  Induct THEN1 (REWRITE_TAC [APPEND] \\ METIS_TAC []) 
  \\ NTAC 6 STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (REWRITE_CONV [path_def,APPEND]))
  \\ Cases_on `range(i,j)h` THEN1 METIS_TAC []
  \\ REWRITE_TAC [path_def] \\ REPEAT STRIP_TAC 
  \\ `~(h = 0)` by (CCONTR_TAC \\ Cases_on `p` 
    \\ FULL_SIMP_TAC bool_ss [APPEND,path_def,IN_DEF,abs_def,heap_type_distinct])
  \\ METIS_TAC []);

val fix_addr = prove(  
  ``!m ax ay az k k' ad b j e.
      (m ax = DATA (k,k',ad)) /\ (!k. j <= k /\ k < e ==> (m k = EMP)) /\
      range (b,e) ax /\ (d1 (cut (b,j) m) SUBSET0 range (b,j)) /\ (m 0 = EMP) /\
      (d0 (cut (b,j) m) = range (b,j)) ==>
      (addr k ay (m k) = (ay = k)) /\ (addr k' az (m k') = (az = k'))``,
  REPEAT STRIP_TAC << [
    Cases_on `m k` \\ ASM_SIMP_TAC bool_ss [addr_def]
    \\ Cases_on `j <= ax` THEN1 METIS_TAC [heap_type_distinct,range_def]
    \\ `range(b,j) ax` by FULL_SIMP_TAC bool_ss [range_def,DECIDE ``~(m<=n) = n < m:num``]
    \\ `d1 (cut (b,j) m) k` by (ASM_SIMP_TAC std_ss [d1,cut_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]    
    \\ FULL_SIMP_TAC bool_ss [IN_DEF]    
    \\ `range (b,j) k` by METIS_TAC [heap_type_distinct]
    \\ `d0 (cut (b,j) m) k` by METIS_TAC []
    \\ IMP_RES_TAC d0_IMP \\ METIS_TAC [heap_type_distinct],
    Cases_on `m k'` \\ ASM_SIMP_TAC bool_ss [addr_def]
    \\ Cases_on `j <= ax` THEN1 METIS_TAC [heap_type_distinct,range_def]
    \\ `range(b,j) ax` by FULL_SIMP_TAC bool_ss [range_def,DECIDE ``~(m<=n) = n < m:num``]
    \\ `d1 (cut (b,j) m) k'` by (ASM_SIMP_TAC std_ss [d1,cut_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]    
    \\ FULL_SIMP_TAC bool_ss [IN_DEF]    
    \\ `range (b,j) k'` by METIS_TAC [heap_type_distinct]
    \\ `d0 (cut (b,j) m) k'` by METIS_TAC []
    \\ IMP_RES_TAC d0_IMP \\ METIS_TAC [heap_type_distinct]]);

val cut_EQ_DATA_IMP = prove(
  ``(cut (i,j) m y = DATA x) ==> (m y = DATA x) /\ range(i,j)y``,
  SIMP_TAC std_ss [cut_def] \\ METIS_TAC [heap_type_distinct]);

val path_cut_IMP = prove(
  ``!p b i j m. 
      (d1 (cut (i,j) m) SUBSET0 range (i,j)) /\ (d0 (cut (i,j) m) = range (i,j)) /\ (m 0 = EMP) /\
      path (b,p) (abs (cut (i,j) m)) ==> path (b,p) (abs m)``,
  Induct \\ FULL_SIMP_TAC std_ss [path_def,IN_DEF,abs_def,cut_def,APPEND]
  \\ FULL_SIMP_TAC bool_ss [GSYM cut_def] \\ REPEAT STRIP_TAC
  THENL [METIS_TAC [heap_type_distinct],ALL_TAC,METIS_TAC [heap_type_distinct],ALL_TAC]
  \\ Cases_on `range(i,j)b` \\ FULL_SIMP_TAC std_ss [heap_type_distinct,heap_type_11]
  \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [IN_DEF]
  \\ `d1 (cut (i,j) m) k /\ d1 (cut (i,j) m) k'` by 
      (SIMP_TAC std_ss [d1,cut_def] \\ METIS_TAC [heap_type_distinct])   
  \\ `~(k = 0) ==> d0 (cut (i,j) m) k` by METIS_TAC []
  \\ `~(k' = 0) ==> d0 (cut (i,j) m) k'` by METIS_TAC []
  THENL [Q.EXISTS_TAC `k'`,Q.EXISTS_TAC `k`] \\ Q.EXISTS_TAC `d` 
  THENL [DISJ1_TAC,DISJ2_TAC] \\ REWRITE_TAC []
  \\ Cases_on `k = 0` \\ Cases_on `k' = 0` \\ FULL_SIMP_TAC std_ss [addr_def]
  \\ IMP_RES_TAC d0_IMP \\ FULL_SIMP_TAC bool_ss [addr_def]
  \\ METIS_TAC [addr_def]);

val reachable_IMP = prove(
  ``!b m i j x. 
     (d1 (cut (i,j) m) SUBSET0 range (i,j)) /\ (d0 (cut (i,j) m) = range (i,j)) /\ (m 0 = EMP) /\
     reachable b (abs (cut (i,j) m)) x ==> reachable b (abs m) x``,
  REWRITE_TAC [reachable_def] \\ METIS_TAC [path_cut_IMP]);

val MAP_INV = prove(
  ``!g f. (g o f = I) /\ (f o g = I) ==> !xs ys. (xs = MAP f ys) = (MAP g xs = ys)``,
  NTAC 3 STRIP_TAC \\ Induct
  \\ Cases_on `ys` \\ ASM_SIMP_TAC std_ss [MAP,NOT_CONS_NIL,CONS_11]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC []);

val move_roots_spec = prove(
  ``!a. ((if ~u then a + l else a) = b) ==>
    !r j m r' j' m' w ww xx.
      cheney_inv (b,b,b,j,b,b+l,f,m,w:num->'a heap_type,xx:num->'a heap_type,ww) /\ 
      (!k. MEM k r ==> {k} SUBSET0 dr0 (icut (b,b + l) m)) /\
      (move_roots (r,j,m) = (r',j',m')) ==>
      cheney_inv (b,b,b,j',b,b+l,f,m',w,xx,ww) /\ j <= j' /\
      (!k. MEM k r' /\ ~(k = 0) ==> range (b,j') k)  /\
      (!k. range(j,j') k ==> MEM k r') /\ 
      (!k i. (m k = REF i) ==> (m' k = REF i)) /\
      (LENGTH r = LENGTH r') /\  
      (!k. MEM k r /\ ~(k = 0) \/ isREF (m k) ==> isREF(m' k)) /\ 
      (!k k'. MEM (k,k') (ZIP(r,r')) ==> if k = 0 then k' = 0 else (m' k = REF k'))``, 
  STRIP_TAC \\ STRIP_TAC \\ Induct THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [PAIR_EQ,move_roots_def,MEM,range_lemmas,EMPTY_DEF,
         LESS_EQ_REFL,MAP,apply_I,ZIP])
  \\ NTAC 9 STRIP_TAC
  \\ `?r' j' m'.  move (h,j,m) = (r',j',m')` by METIS_TAC [PAIR]
  \\ `?rs3 j3 m3.  move_roots (r,j'',m'') = (rs3,j3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [move_roots_def,LET_DEF]  
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [MEM] \\ STRIP_TAC
  \\ `{h} SUBSET0 dr0 (icut (b,b + l) m)` by METIS_TAC []
  \\ IMP_RES_TAC move_lemma
  \\ `!k. MEM k r ==> {k} SUBSET0 dr0 (icut (b,b + l) m'')` by METIS_TAC []
  \\ Q.PAT_ASSUM `!j m r'. bb` (STRIP_ASSUME_TAC o UNDISCH_ALL o
       RW [GSYM AND_IMP_INTRO] o Q.SPECL [`j''`,`m''`,`rs3`,`j3`,`m3`,`w`,`ww`,`xx`])
  \\ STRIP_TAC THEN1 METIS_TAC [] 
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ Cases_on `h = 0` THEN1 METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [] 
    \\ IMP_RES_TAC d0_IMP \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ Cases_on `k = r''` THEN1 METIS_TAC [] \\ DISJ2_TAC 
    \\ Cases_on `h = 0` THEN1 METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [] \\ IMP_RES_TAC d0_IMP 
    \\ Q.PAT_ASSUM `!k. range (j',j3) k ==> MEM k rs3` MATCH_MP_TAC
    \\ Cases_on ` m'' h = REF j` \\ FULL_SIMP_TAC bool_ss [heap_type_11]
    \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [LENGTH,ZIP,MEM]
  \\ STRIP_TAC THEN1
   (STRIP_TAC \\ Cases_on `isREF(m k)` \\ ASM_SIMP_TAC bool_ss [] THEN1 METIS_TAC [isREF_def]
    \\ REPEAT STRIP_TAC THENL [ALL_TAC,METIS_TAC []] 
    \\ `~(h = 0)` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [move_def,LET_DEF,PAIR_EQ]
    \\ Q.PAT_ASSUM `!k. bbb ==> isREF (m3 k)` MATCH_MP_TAC \\ DISJ2_TAC
    \\ Q.PAT_ASSUM `(h =+ REF j) ((j =+ m h) m) = m''` (fn th => REWRITE_TAC [GSYM th])
    \\ SIMP_TAC std_ss [isREF_def,UPDATE_def,heap_type_11])
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ Cases_on `k = 0` \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);  
    
val cheney_inv_intro = store_thm("cheney_inv_setup",
  ``cheney_inv (b,b,b,j,b,e,f,m',m,m,{}) ==> cheney_inv (b,j,b,j,j,e,f,m',m',m,range(b,j))``,
  SIMP_TAC bool_ss [cheney_inv_def,LESS_EQ_REFL] \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  THEN1 (REWRITE_TAC [SUBSET_DEF,IN_UNION] \\ SIMP_TAC bool_ss [IN_DEF])
  THEN1 METIS_TAC [] \\ REWRITE_TAC [range_lemmas,EMPTY_SUBSET]);

val list_range_aux_def = Define `
  (list_range_aux 0 n = []) /\
  (list_range_aux (SUC m) n = n::list_range_aux m (n+1))`;

val list_range_def = Define `
  list_range(i,j) = list_range_aux (j-i) i`;

val list_range_aux_thm = prove(
  ``!j i k. MEM k (list_range_aux j i) = range(i,i+j) k``,
  Induct \\ ASM_REWRITE_TAC [list_range_aux_def,MEM,range_lemmas,ADD_0,EMPTY_DEF]
  \\ REWRITE_TAC [range_def] \\ DECIDE_TAC);

val list_range_thm = prove(
  ``!i j k. MEM k (list_range(i,j)) = range(i,j) k``,
  REWRITE_TAC [list_range_def] \\ REPEAT STRIP_TAC \\ Cases_on `i <= j` << [
    FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS] \\ `i + p - i = p` by DECIDE_TAC 
    \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,list_range_aux_thm],
    `j - i = 0` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [list_range_aux_def,range_def,MEM] 
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
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] WFS_inv_IMP_cheney_inv)
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ `(if ~u then 1 + l else 1) = b` by METIS_TAC []   
  \\ (STRIP_ASSUME_TAC o RW [AND_IMP_INTRO] o 
     UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o Q.INST [`f`|->`l+l+1`] o
     Q.SPECL [`r`,`b`,`m`,`r'`,`j'`,`m'`,`m`,`{}`,`m`] o UNDISCH o Q.SPEC `1`) move_roots_spec
  \\ `cheney_inv (b,j',b,j',j',b + l,l+l+1,m',m',m,range(b,j'))` by METIS_TAC [cheney_inv_intro]
  \\ Q.UNABBREV_TAC `e` \\ Q.ABBREV_TAC `e = b + l`
  \\ `cheney_inv (b,j',j'',j'',j'',e,l+l+1,m'',m',m,range (b,j')) /\ j' <= j''` by METIS_TAC [cheney_inv_maintained]  
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [cheney_inv_def,ok_state_def,LET_DEF,IN_DEF]
    \\ `!k. range(b,j') k ==> range(b,j'')k` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)         
    \\ REPEAT STRIP_TAC THEN1 METIS_TAC [] << [    
      Cases_on `range(b,e)k` \\ ASM_SIMP_TAC std_ss [cut_def]
      \\ Q.PAT_ASSUM `!k. bb ==> (m'' k = EMP)` MATCH_MP_TAC 
      \\ FULL_SIMP_TAC std_ss [range_def] \\ DECIDE_TAC,  
      `d0 (cut (b,j'') m'') k` by METIS_TAC [] \\ IMP_RES_TAC d0_IMP
      \\ Q.EXISTS_TAC `h` \\ Q.EXISTS_TAC `g` \\ Q.EXISTS_TAC `dd`
      \\ `range(b,e)k` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
      \\ ASM_SIMP_TAC std_ss [cut_def]
      \\ MATCH_MP_TAC SUBSET0_TRANS \\ Q.EXISTS_TAC `d1 (cut (b,j'') m'')`
      \\ ASM_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ ASM_SIMP_TAC std_ss [IN_DEF,d1,cut_def] \\ METIS_TAC []])
  \\ `basic_abs m = abs m` by 
     (MATCH_MP_TAC basic_abs_EQ_abs \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF]
      \\ METIS_TAC [heap_type_distinct])
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.PAT_ASSUM `cheney_inv (b,b,b,b,b,e,l+l+1,m,m,m,{})` (K ALL_TAC)
  \\ Q.PAT_ASSUM `cheney_inv (b,j',b,j',j',e,l+l+1,m',m',m,range (b,j'))` (K ALL_TAC)
  \\ `m' 0 = EMP` by METIS_TAC [cheney_inv_def]
  \\ Q.PAT_ASSUM `cheney_inv (b,b,b,j',b,e,l+l+1,m',m,m,{})` (K ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [cheney_inv_def]  
  \\ `(\x. ?t. t IN range(b,j') /\ x IN reachable t (abs m'')) 
     SUBSET (0 INSERT range (b,b+l))` by 
     (Q.UNABBREV_TAC `e` \\ Cases_on `l = 0` THEN1
       (`b = j'` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [range_lemmas,NOT_IN_EMPTY]
        \\ REWRITE_TAC [GSYM EMPTY_DEF,EMPTY_SUBSET])
      \\ REWRITE_TAC [SUBSET_DEF,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF,reachable_def]
      \\ REPEAT STRIP_TAC THEN1 (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
      \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
      \\ `range (b,b + l) t` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
      \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o 
          Q.SPECL [`p`,`t`,`x`,`b`,`b+l`,`m''`]) path_cut
      \\ FULL_SIMP_TAC bool_ss [path_def,IN_DEF,abs_def] 
      \\ (Cases_on `j'' <= s`
          THEN1 (`s < b + l` by FULL_SIMP_TAC bool_ss [range_def] \\ METIS_TAC [heap_type_distinct])
          \\ `s < j''` by DECIDE_TAC
          \\ `range(b,j'')s` by FULL_SIMP_TAC std_ss [range_def]        
          \\ `d1 (cut (b,j'') m'') k /\ d1 (cut (b,j'') m'') k'` by
           (FULL_SIMP_TAC std_ss [d1,cut_def] \\ METIS_TAC [])  
          \\ `~(k = 0) ==> range(b,j'')k` by  
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC []) 
          \\ `~(k' = 0) ==> range(b,j'')k'` by  
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC [])) 
      THENL [
          `d = k` by 
           (Cases_on `k = 0` THEN1 METIS_TAC [addr_def]
            \\ `d0 (cut (b,j'') m'') k` by METIS_TAC []
            \\ IMP_RES_TAC d0_IMP \\ METIS_TAC [addr_def]),
          `d = k'` by 
           (Cases_on `k' = 0` THEN1 METIS_TAC [addr_def]
            \\ `d0 (cut (b,j'') m'') k'` by METIS_TAC []
            \\ IMP_RES_TAC d0_IMP \\ METIS_TAC [addr_def])]                   
      \\ `~range(b,j'')d` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
      \\ METIS_TAC [])          
  \\ `basic_abs (cut(b,e)m'') = reachables r' (abs m'')` by 
   (REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ ASM_SIMP_TAC bool_ss [reachables_def]
    \\ FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT]          
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,basic_abs,abs_def]          
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [    
        IMP_RES_TAC cut_EQ_DATA_IMP
        \\ ASM_SIMP_TAC std_ss [heap_type_11]
        \\ Cases_on `x = 0` THEN1 (`F` by METIS_TAC [heap_type_distinct]) 
        \\ Cases_on `j'' <= x` THEN1 (`F` by METIS_TAC [range_def,heap_type_distinct])
        \\ `range(b,j'')x` by FULL_SIMP_TAC bool_ss [DECIDE ``~(m<=n)=n<m:num``,range_def]
        \\ REPEAT STRIP_TAC << [
          `d1 (cut (b,j'') m'') y` by (SIMP_TAC bool_ss [cut_def,d1] \\ METIS_TAC [])
          \\ Cases_on `y = 0` THEN1 METIS_TAC [addr_def]
          \\ `range(b,j'')y` by  
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC []) 
          \\ `d0 (cut (b,j'') m'') y` by METIS_TAC []
          \\ IMP_RES_TAC d0_IMP \\ ASM_SIMP_TAC bool_ss [addr_def],
          `d1 (cut (b,j'') m'') z` by (SIMP_TAC bool_ss [cut_def,d1] \\ METIS_TAC [])
          \\ Cases_on `z = 0` THEN1 METIS_TAC [addr_def]
          \\ `range(b,j'')z` by  
           (FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
            \\ FULL_SIMP_TAC bool_ss [IN_DEF] \\ METIS_TAC []) 
          \\ `d0 (cut (b,j'') m'') z` by METIS_TAC []
          \\ IMP_RES_TAC d0_IMP \\ ASM_SIMP_TAC bool_ss [addr_def],
          RES_TAC \\ Q.EXISTS_TAC `t` \\ STRIP_TAC THEN1 METIS_TAC []
          \\ MATCH_MP_TAC reachable_IMP
          \\ Q.EXISTS_TAC `b` \\ Q.EXISTS_TAC `j''` \\ ASM_SIMP_TAC bool_ss []
          \\ `abs (cut (b,j'')m'') = basic_abs (cut (b,j'') m'')` by ALL_TAC
          THENL [ALL_TAC,METIS_TAC []]
          \\ MATCH_MP_TAC (GSYM basic_abs_EQ_abs)
          \\ SIMP_TAC bool_ss [cut_def] \\ NTAC 2 STRIP_TAC
          \\ Cases_on `range(b,j'')k` \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]
          \\ `d0 (cut (b,j'') m'') k` by METIS_TAC []
          \\ IMP_RES_TAC d0_IMP \\ ASM_SIMP_TAC bool_ss [heap_type_distinct]],
        Q.UNABBREV_TAC `e` \\ Cases_on `r'' = 0` << [ 
          FULL_SIMP_TAC bool_ss [reachable_def] THEN1 METIS_TAC [heap_type_distinct]
          \\ FULL_SIMP_TAC bool_ss [path_def,APPEND,IN_DEF,abs_def]
          \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [path_def,APPEND,IN_DEF,abs_def]
          \\ METIS_TAC [heap_type_distinct],
          `(x = 0) \/ range (b,b + l) x` by METIS_TAC []
          THEN1 METIS_TAC [heap_type_distinct]
          \\ ASM_SIMP_TAC bool_ss [cut_def,heap_type_11,PAIR_EQ]
          \\ FULL_SIMP_TAC bool_ss [GSYM AND_IMP_INTRO]          
          \\ `!k. j'' <= k /\ k < b + l ==> (m'' k = EMP)` by METIS_TAC []
          \\ `(addr k y (m'' k) = (y = k)) /\ (addr k' z (m'' k') = (z = k'))` by 
            (MATCH_MP_TAC fix_addr \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `d` \\ Q.EXISTS_TAC `b`
             \\ Q.EXISTS_TAC `j''` \\ Q.EXISTS_TAC `b+l` \\ ASM_SIMP_TAC bool_ss [])
          \\ FULL_SIMP_TAC bool_ss []]])
  \\ Q.PAT_ASSUM `roots_inv (b,j'',m'',abs m)` (STRIP_ASSUME_TAC o RW [roots_inv_def])
  \\ Q.EXISTS_TAC `v` \\ ASM_SIMP_TAC bool_ss [apply_apply]
  \\ `apply v (reachables r (apply v (abs m''))) = 
      reachables (MAP v r) (apply v (apply v (abs m'')))` by METIS_TAC [apply_reachables]
  \\ ASM_SIMP_TAC bool_ss [apply_apply,apply_I]  
  \\ `v 0 = 0` by 
    (`~isREF(m'' 0)` by METIS_TAC [isREF_def,heap_type_distinct]
     \\ `~range(b,j'')0` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
     \\ METIS_TAC [])
  \\ ASM_SIMP_TAC bool_ss []
  \\ ONCE_REWRITE_TAC [METIS_PROVE [] ``b /\ c = b /\ (b ==> c:bool)``]
  \\ SIMP_TAC bool_ss []
  \\ `!k k'. MEM (k,k') (ZIP (r,r')) ==> (v k = k')` by METIS_TAC []
  \\ Q.UNDISCH_TAC `!k k'. MEM (k,k') (ZIP (r,r')) ==> (v k = k')`
  \\ Q.UNDISCH_TAC `LENGTH r = LENGTH r'`
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ Q.SPEC_TAC (`r'`,`ys`) \\ Q.SPEC_TAC (`r`,`xs`)
  \\ Induct THENL [ALL_TAC,STRIP_TAC] \\ Cases 
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,MAP,ADD1,EQ_ADD_RCANCEL,ZIP,MEM,CONS_11]
  \\ METIS_TAC [PAIR_EQ]);

val ok_abs_def = Define `
  ok_abs (r,h:(num|->(num#num#'a)),l:num) = 
    ~(0 IN FDOM h) /\ FEVERY (\(x,y,z,d). {y;z} SUBSET0 FDOM h) h /\
    (!k. MEM k r /\ ~(k = 0) ==> k IN FDOM h)`;

val set_def = Define `set h (x,y,z,d) = (h ' x = (y,z,d)) /\ x IN FDOM h`;

val abstract_def = Define `
  abstract(b,m) = { (b(x), b(y), b(z), d) |(x,y,z,d)| m(x) = DATA(y,z,d) }`;

val ch_inv_def = Define `
  ch_inv (r,h,l) (i,e,c,l',u,m) =
    ok_state (i,e,c,l,u,m) /\ ok_abs (r,h,l) /\ (l = l') /\
    ?b. bijection b /\ (b 0 = 0) /\ (MAP b c = r) /\ 
        reachables r (set(h)) SUBSET abstract(b,m) /\ abstract(b,m) SUBSET set(h)`;

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
          (basic_abs m SUBSET apply b (set h)) /\
          (apply b (reachables r (set h)) SUBSET basic_abs m)``,
  METIS_TAC [SUBSET_EQ_apply_SUBSET,apply_abstract,ch_inv_def]);  

val INFINITE_num = prove(
  ``INFINITE (UNIV:num->bool)``,
  REWRITE_TAC [INFINITE_UNIV] \\ Q.EXISTS_TAC `SUC`
  \\ SIMP_TAC std_ss []  \\ Q.EXISTS_TAC `0` \\ DECIDE_TAC);

val fresh_def = Define `fresh (h:num|->(num#num#'a)) = @x:num. ~(x IN 0 INSERT FDOM h)`;

val fresh_NOT_IN_FDOM = (SIMP_RULE std_ss [IN_INSERT] o prove)(
  ``!h. ~(fresh h IN 0 INSERT FDOM h)``,
  REWRITE_TAC [fresh_def] \\ METIS_TAC [NOT_IN_FINITE,INFINITE_num,FINITE_INSERT,FDOM_FINITE]);

val fresh_THM = prove(
  ``FEVERY (\(x,y,z,d). {y; z} SUBSET0 FDOM h) h ==> 
    !y z d. ~((fresh h,y,z,d) IN set h) /\ ~((z,fresh h,y,d) IN set h) /\ 
            ~((y,z,fresh h,d) IN set h) /\ ~(fresh h = 0)``,
  SIMP_TAC std_ss [fresh_NOT_IN_FDOM,IN_DEF,set_def,FEVERY_DEF,
    SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
  \\ METIS_TAC [FST,SND,SIMP_RULE std_ss [IN_DEF] fresh_NOT_IN_FDOM]);

val INSERT_THM = prove(
  ``!x s. x INSERT s = \y. (x = y) \/ s y``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT] \\ SIMP_TAC std_ss [IN_DEF] \\ METIS_TAC []);

val apply_INSERT = prove(
  ``!k f. (f o k = I) ==> (k o f = I) ==> !x y z d set.
      (apply f ((x:num,y,z,d:'a) INSERT set) = ((k x):num,k y,k z,d) INSERT apply f set)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ SIMP_TAC std_ss [apply_def,IN_DEF,INSERT_THM,FUN_EQ_THM] \\ METIS_TAC []);

val path_SUBSET = prove(
  ``!xs x s t. path (x,xs) s /\ s SUBSET t ==> path (x,xs) t``,
  Induct \\ FULL_SIMP_TAC std_ss[path_def,SUBSET_DEF] \\ METIS_TAC []);

val reachables_reachables = prove(
  ``!c s. reachables c (reachables c s) = reachables c s``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [reachables_def,IN_DEF]
  \\ EQ_TAC \\ SIMP_TAC std_ss [] \\ REWRITE_TAC [reachable_def] 
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`  
  \\ REPEAT (POP_ASSUM (fn th => ASSUME_TAC th \\ UNDISCH_TAC (concl th)))  
  \\ Q.SPEC_TAC(`d`,`d`) \\ Q.SPEC_TAC(`z`,`z`) \\ Q.SPEC_TAC(`y`,`y`) 
  \\ Q.SPEC_TAC(`x`,`x`) \\ Q.SPEC_TAC(`c`,`c`) \\ Q.SPEC_TAC(`r`,`r`) 
  \\ Induct_on `p` \\ REWRITE_TAC [APPEND,path_def]
  THEN1 (SIMP_TAC std_ss [path_def,IN_DEF,reachables_def,reachable_def] \\ METIS_TAC [])
  \\ NTAC 8 STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF,reachable_def] \\ REPEAT STRIP_TAC
  THENL [ALL_TAC,METIS_TAC [],ALL_TAC,METIS_TAC []]
  \\ MATCH_MP_TAC path_SUBSET \\ Q.EXISTS_TAC `reachables [h] s`
  \\ (STRIP_TAC THEN1 METIS_TAC [MEM])
  \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF]    
  \\ Cases \\ Cases_on `r'` \\ Cases_on `r''`
  \\ SIMP_TAC std_ss [reachables_def,IN_DEF,reachable_def,MEM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC bool_ss [] \\ DISJ2_TAC THENL [
    Q.EXISTS_TAC `[]` \\ ASM_REWRITE_TAC [APPEND,path_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `h::p'` \\ ASM_REWRITE_TAC [APPEND,path_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `[]` \\ ASM_REWRITE_TAC [APPEND,path_def,IN_DEF] \\ METIS_TAC [],
    Q.EXISTS_TAC `h::p'` \\ ASM_REWRITE_TAC [APPEND,path_def,IN_DEF] \\ METIS_TAC []]);
  
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
  \\ `!x. b (g x) = x` by ALL_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,IN_DEF]);

val CARD_EQ_CARD_apply = prove(
  ``!s:('a#'a#'a#'b)set b:'a->'a. FINITE s /\ bijection b ==> (CARD s = CARD (apply b s))``,
  REPEAT STRIP_TAC \\ (MATCH_MP_TAC o RW [AND_IMP_INTRO] o 
    Q.GEN `f` o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) FINITE_BIJ_CARD_EQ  
  \\ ASM_REWRITE_TAC []
  \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ Q.EXISTS_TAC `\x. (k (FST x),k (FST (SND x)),k (FST (SND (SND x))),SND (SND (SND x)))`  
  \\ SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF] \\ REPEAT STRIP_TAC << [
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
    !k. if ~range(i,j) k then m k = EMP else ?y z d. m k = DATA (y,z,d)`;

val WFS_part_IMP_cut = prove(
  ``ok_state_part(i,j,m) ==> (m = cut (i,j)m)``,
  SIMP_TAC std_ss [ok_state_part_def,LET_DEF,IN_DEF,cut_def,FUN_EQ_THM] 
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val WFS_IMP_cut = prove(
  ``ok_state(i,e,r,l,u,m) ==> (m = cut (if u then 1 + l else 1,i)m)``,
  SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF,cut_def,FUN_EQ_THM] 
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val FINITE_basic_abs_cut = prove(
  ``!j i m. FINITE (basic_abs (cut(i,j)m))``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (INST_TYPE [``:'a``|->``:(num#num#num#'a)``,``:'b``|->``:num``] FINITE_INJ)
  \\ Q.EXISTS_TAC `FST` \\ Q.EXISTS_TAC `range(i,j)`
  \\ SIMP_TAC std_ss [INJ_DEF,FINITE_range2] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  THEN1 (FULL_SIMP_TAC std_ss [IN_DEF,basic_abs,cut_def] \\ METIS_TAC [heap_type_distinct])
  \\ Cases_on `y` \\ Cases_on `r'` \\ Cases_on `r''`
  \\ FULL_SIMP_TAC std_ss [IN_DEF,basic_abs,cut_def,heap_type_11] \\ METIS_TAC []);
    
val ok_state_CARD_EQ_lemma = prove(
  ``!j i m. ok_state_part (i,i+j,m) ==> (CARD (basic_abs m) = j)``,
  Induct << [
    SIMP_TAC std_ss [ok_state_part_def,LET_DEF,range_lemmas,EMPTY_DEF]
    \\ REPEAT STRIP_TAC \\ `basic_abs m = {}` by ALL_TAC \\ ASM_REWRITE_TAC [CARD_EMPTY]
    \\ SIMP_TAC std_ss[FUN_EQ_THM,EMPTY_DEF]      
    \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
    \\ ASM_SIMP_TAC std_ss[basic_abs,heap_type_distinct],
    REPEAT STRIP_TAC \\ `ok_state_part (i,i+j,(i+j =+ EMP) m)` by ALL_TAC << [
      FULL_SIMP_TAC std_ss [ok_state_part_def,LET_DEF] \\ REPEAT STRIP_TAC 
      \\ Cases_on `range(i,i+j)k` \\ ASM_SIMP_TAC std_ss [UPDATE_def] << [ 
        `~(i + j = k) /\ range(i,i+SUC j)k` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
        \\ METIS_TAC [],        
        Cases_on `i + j = k` \\ ASM_SIMP_TAC bool_ss []
        \\ `~range(i,i+SUC j)k` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
        \\ METIS_TAC []],  
      RES_TAC
      \\ `range(i,i+SUC j)(i+j)` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
      \\ `?x y d. m (i + j) = DATA(x,y,d)` by METIS_TAC [ok_state_part_def]
      \\ Q.ABBREV_TAC `xxx = basic_abs ((i+j =+ EMP) m)`
      \\ `(basic_abs m = (i+j,x,y,d) INSERT xxx) /\ ~((i+j,x,y,d) IN xxx)` by ALL_TAC
      \\ REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
      \\ Q.UNABBREV_TAC `xxx` << [
        SIMP_TAC std_ss [INSERT_THM,IN_DEF,basic_abs,UPDATE_def,heap_type_distinct] 
        \\ REPEAT STRIP_TAC
        \\ Cases_on `x' = i + j` \\ ASM_SIMP_TAC std_ss [heap_type_11,heap_type_distinct],
        `FINITE (basic_abs m)` by METIS_TAC [WFS_part_IMP_cut,FINITE_basic_abs_cut]
        \\ METIS_TAC [CARD_INSERT,FINITE_INSERT]]]]);

val ok_state_CARD_EQ = prove(
  ``!j i m. ok_state_part (i,j,m) ==> (CARD (basic_abs m) = j - i)``,
  NTAC 3 STRIP_TAC \\ Cases_on `i <= j` << [
    FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS]
    \\ `i + p - i = p` by DECIDE_TAC \\ METIS_TAC [ok_state_CARD_EQ_lemma],
    ` (j - i = 0) /\ !k.~range(i,j)k` by (REWRITE_TAC [range_def] \\ DECIDE_TAC) 
    \\ ASM_SIMP_TAC bool_ss [ok_state_part_def] \\ STRIP_TAC        
    \\ `basic_abs m = {}` by ALL_TAC \\ ASM_SIMP_TAC bool_ss [CARD_EMPTY]
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
  ``!h:num|->num#num#'a. FINITE (set h)``,
  CONV_TAC (QUANT_CONV (UNBETA_CONV ``h:num|->num#num#'a``))
  \\ MATCH_MP_TAC fmap_INDUCT \\ SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC << [   
    `set (FEMPTY:num|->num#num#'a) = {}` by ALL_TAC 
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY]
    \\ ASM_SIMP_TAC bool_ss [FINITE_EMPTY,set_def,EMPTY_DEF,FDOM_FEMPTY,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``],    
    `set ((f |+ (x,y)):num|->num#num#'a) = (x,y) INSERT set f` by ALL_TAC 
    \\ ASM_SIMP_TAC std_ss [FINITE_INSERT]
    \\ FULL_SIMP_TAC bool_ss [set_def,INSERT_THM,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_DEF,
         METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ Cases_on `y` \\ Cases_on `r` \\ METIS_TAC [PAIR_EQ]]);

val cheney_alloc_aux_spec = prove(
  ``(cheney_alloc_aux (i,e,c,l,u,m) = (i',e',c',l',u',m')) ==>
    ch_inv (r,h,l) (i,e,c,l,u,m) /\ CARD (reachables r (set h)) < l ==>
    i' < e' /\ ch_inv (r,h,l) (i',e',c',l',u',m')``,
  Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss [PAIR_EQ,cheney_alloc_aux_def] THEN1 METIS_TAC []
  \\ POP_ASSUM (K ALL_TAC) 
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [ch_inv_thm]  
  \\ IMP_RES_TAC cheney_collector_spec \\ ASM_SIMP_TAC bool_ss [] 
  \\ `bijection f` by (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def])
  \\ `apply b (reachables r (set h)) = apply f (basic_abs m')` by 
   (REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !x y z d. f (x,y,z,d) = g (x,y,z,d)``]
    \\ Q.PAT_ASSUM `apply f (reachables c (basic_abs m)) = basic_abs m'`
      (fn th => ASM_REWRITE_TAC [GSYM th,apply_apply,apply_I])
    \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
    \\ IMP_RES_TAC (Q.ISPECL [`r:num list`,`f:num->num`,`g:num->num`,`s:(num#num#num#'a)set`] apply_reachables)
    \\ IMP_RES_TAC MAP_INV \\ FULL_SIMP_TAC bool_ss []
    \\ REPEAT (Q.PAT_ASSUM `!hj.jk` (K ALL_TAC))
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
      REWRITE_TAC [reachables_def] 
      \\ STRIP_TAC THEN1 (FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])      
      \\ FULL_SIMP_TAC bool_ss [reachables_def,IN_DEF,reachable_def] THEN1 METIS_TAC []
      \\ Q.EXISTS_TAC `r'` \\ ASM_REWRITE_TAC [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ Q.UNDISCH_TAC `path (r',p ++ [x]) (apply b (set h))`  
      \\ `reachables [r'] (apply b (set h)) SUBSET basic_abs m` by 
       (MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `reachables c (apply b (set h))`
        \\ ASM_SIMP_TAC bool_ss []
        \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF]
        \\ Cases \\ Cases_on `r''` \\ Cases_on `r'''`
        \\ ASM_SIMP_TAC std_ss [reachables_def,MEM] \\ METIS_TAC [])
      \\ Q.UNDISCH_TAC `reachables [r'] (apply b (set h)) SUBSET basic_abs m`
      \\ Q.SPEC_TAC (`r'`,`rr`) \\ Induct_on `p` THEN1              
       (SIMP_TAC bool_ss [APPEND,path_def,EXPAND_SUBSET,reachables_def,MEM,IN_DEF] 
        \\ METIS_TAC [reachable_def])
      \\ SIMP_TAC std_ss [APPEND,path_def] \\ REPEAT STRIP_TAC << [
        `reachables [h'] (apply b (set h)) SUBSET reachables [rr] (apply b (set h))` by 
         (ASM_SIMP_TAC bool_ss [EXPAND_SUBSET,reachables_def,MEM,reachable_def,IN_DEF]
          \\ REPEAT STRIP_TAC \\ DISJ2_TAC << [
            Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC [],
            Q.EXISTS_TAC `h'::p'` \\ ASM_SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC []])
        \\ METIS_TAC [SUBSET_TRANS],           
        `reachables [rr] (apply b (set h)) (rr,h',z',d')` by 
          (FULL_SIMP_TAC std_ss [reachables_def,MEM,IN_DEF,reachable_def] \\ METIS_TAC [])
        \\ FULL_SIMP_TAC bool_ss [IN_DEF,SUBSET_DEF] \\ METIS_TAC [],
        `reachables [h'] (apply b (set h)) SUBSET reachables [rr] (apply b (set h))` by 
         (ASM_SIMP_TAC bool_ss [EXPAND_SUBSET,reachables_def,MEM,reachable_def,IN_DEF]
          \\ REPEAT STRIP_TAC \\ DISJ2_TAC << [
            Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC [],
            Q.EXISTS_TAC `h'::p'` \\ ASM_SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC []])
        \\ METIS_TAC [SUBSET_TRANS],
        `reachables [rr] (apply b (set h)) (rr,z',h',d')` by 
          (FULL_SIMP_TAC std_ss [reachables_def,MEM,IN_DEF,reachable_def] \\ METIS_TAC [])
        \\ FULL_SIMP_TAC bool_ss [IN_DEF,SUBSET_DEF] \\ METIS_TAC []],
      FULL_SIMP_TAC std_ss [reachables_def,SUBSET_DEF,IN_DEF]
      \\ Q.EXISTS_TAC `r'` \\ ASM_REWRITE_TAC []     
      \\ FULL_SIMP_TAC std_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ Q.UNDISCH_TAC `path (r',p ++ [x]) (basic_abs m)`      
      \\ Q.UNDISCH_TAC `!x. basic_abs m x ==> apply b (set h) x`
      \\ Q.SPEC_TAC (`r'`,`rr`) \\ Induct_on `p`
      \\ SIMP_TAC bool_ss [path_def,APPEND,IN_DEF] \\ METIS_TAC []])
  \\ ALL_TAC << [
    `FINITE (reachables r (set h))` by 
     ((MATCH_MP_TAC o RW [AND_IMP_INTRO] o Q.GEN `s` o DISCH_ALL o 
       SPEC_ALL o UNDISCH o SPEC_ALL) SUBSET_FINITE
      \\ Q.EXISTS_TAC `set h` \\ FULL_SIMP_TAC bool_ss [ok_abs_def,FINITE_set]
      \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF]
      \\ Cases \\ Cases_on `r'` \\ Cases_on `r''`
      \\ FULL_SIMP_TAC std_ss [reachables_def,IN_DEF])
    \\ `FINITE (basic_abs m')` by METIS_TAC [FINITE_basic_abs_cut,WFS_IMP_cut]   
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
    \\ `basic_abs m' = apply f (apply b (reachables r (set h)))` by METIS_TAC [apply_switch]
    \\ Q.PAT_ASSUM `apply b (reachables r (set h)) = apply f (basic_abs m')` (K ALL_TAC)
    \\ Q.PAT_ASSUM `apply f (reachables c (basic_abs m)) = basic_abs m'` (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss [GSYM apply_apply]
    \\ METIS_TAC [apply_SUBSET,reachables_SUBSET,SUBSET_REFL]]);
    
val path_INSERT = prove(
  ``(!y z d. ~((x:num,y:num,z:num,d:'a) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(x = y) ==>
    (path (y,p) ((x,y',z,d) INSERT s) = path (y,p) s)``,
  REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC path_SUBSET \\ Q.EXISTS_TAC `s` \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT])
  \\ Q.UNDISCH_TAC `path (y,p) ((x,y',z,d) INSERT s)`
  \\ Q.UNDISCH_TAC `~(x = y)` \\ Q.SPEC_TAC (`(y',z,d)`,`t`)
  \\ Cases \\ Cases_on `r` \\ Q.SPEC_TAC (`y`,`y`)
  \\ Induct_on `p` \\ SIMP_TAC std_ss [path_def,IN_INSERT,PAIR_EQ] 
  \\ REPEAT STRIP_TAC \\ `~(x = h)` by METIS_TAC [] \\ RES_TAC \\ METIS_TAC []);

val reachable_INSERT = prove(
  ``(!y z d. ~((x,y,z,d) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(a = x) /\ ~(x = y) /\ ~(x = z) ==>
    (reachable x ((x:num,y:num,z:num,d:'a) INSERT s) a = reachable y s a \/ reachable z s a)``,
  ASM_SIMP_TAC bool_ss [reachable_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [path_def,APPEND,IN_INSERT] \\ METIS_TAC [],
    Q.EXISTS_TAC `y::p` \\ SIMP_TAC std_ss [path_def,APPEND,IN_INSERT] 
    \\ REVERSE STRIP_TAC \\ METIS_TAC [path_INSERT],    
    Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [path_def,APPEND,IN_INSERT] \\ METIS_TAC [],
    Q.EXISTS_TAC `z::p` \\ SIMP_TAC std_ss [path_def,APPEND,IN_INSERT] 
    \\ REVERSE STRIP_TAC \\ METIS_TAC [path_INSERT],
    Cases_on `p` \\ FULL_SIMP_TAC std_ss [APPEND,path_def,IN_INSERT] THEN1 METIS_TAC []
    \\ METIS_TAC [path_INSERT]]);
    
val reachables_INSERT = prove(
  ``!ts x y z d s.
      (!y z d. ~((x,y,z,d) IN s) /\ ~((z,x,y,d) IN s) /\ ~((y,z,x,d) IN s)) /\ ~(x = y) /\ ~(x = z) ==>
      (reachables (x::ts) ((x:num,y:num,z:num,d:'a) INSERT s) = (x,y,z,d) INSERT reachables (y::z::ts) s)``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !a b c e. f (a,b,c,e) = g (a,b,c,e)``]
  \\ SIMP_TAC std_ss [reachables_def,IN_DEF,INSERT_THM]       
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] << [
    REVERSE (Cases_on `r = x`) \\ FULL_SIMP_TAC bool_ss [GSYM INSERT_THM] << [
      FULL_SIMP_TAC bool_ss [MEM] \\ DISJ2_TAC \\ Q.EXISTS_TAC `r`
      \\ FULL_SIMP_TAC bool_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
      \\ METIS_TAC [SIMP_RULE std_ss [IN_DEF] path_INSERT],
      `reachable y s a \/ reachable z s a` by METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT]
      \\ METIS_TAC [MEM]],        
    Q.EXISTS_TAC `a` \\ SIMP_TAC bool_ss [reachable_def,MEM], 
    FULL_SIMP_TAC bool_ss [MEM,GSYM INSERT_THM]
    THEN1 METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT,MEM]
    THEN1 METIS_TAC [SIMP_RULE std_ss [IN_DEF] reachable_INSERT,MEM]
    \\ Q.EXISTS_TAC `r` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC bool_ss [reachable_def] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
    \\ MATCH_MP_TAC path_SUBSET \\ Q.EXISTS_TAC `s` 
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
  \\ Cases_on ` range (if u then 1 + l else 1,i) k` \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [heap_type_11,heap_type_distinct,PAIR_EQ,range_def] \\ METIS_TAC []);

val MAP_ID =prove(
  ``!xs. (!k. MEM k xs ==> (f k = k)) ==> (MAP f xs = xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [MAP,MEM,CONS_11] \\ METIS_TAC []);

val range_BORDER = prove(``~range(i,j)j``,REWRITE_TAC [range_def] \\ DECIDE_TAC);

val cheney_alloc_lemma = prove(
  ``!i e t l u m x y z d k.
    ok_state (i,e,t,l,u,m) /\ basic_abs m (x,y,z,d) /\ (!a b c. ~basic_abs m (k,a,b,c)) /\ ~(k = 0) ==>
    ~(i = x) /\ ~(i = y) /\ ~(i = z) /\ ~(k = x) /\ ~(k = y) /\ ~(k = z)``,
  SIMP_TAC bool_ss [ok_state_def,LET_DEF,basic_abs,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
  \\ SIMP_TAC bool_ss [IN_DEF] \\ NTAC 12 STRIP_TAC
  \\ `~(i = 0)` by (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
  \\ `range (if u then 1+l else 1,i) x` by METIS_TAC [heap_type_distinct]   
  \\ RES_TAC \\ FULL_SIMP_TAC bool_ss [heap_type_11,PAIR_EQ]
  \\ METIS_TAC [range_BORDER,heap_type_distinct]); 

val set_FUPDATE = prove(
  ``!h x y d. set (h |+ (fresh h,x,y,d)) = (fresh h,x,y,d) INSERT set h``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``!f g. (f = g) = !a b c e. f (a,b,c,e) = g (a,b,c,e)``]
  \\ SIMP_TAC std_ss [set_def,INSERT_THM,FDOM_FUPDATE,IN_DEF,FAPPLY_FUPDATE_THM]  
  \\ METIS_TAC [PAIR_EQ,SIMP_RULE std_ss [IN_DEF,INSERT_THM] fresh_NOT_IN_FDOM]);  

val ok_state_LESS = prove(
  ``!t v i e r l u m d. 
      ok_state (i,e,t::v::r,l,u,m) /\ i < e ==>
      ok_state (i + 1,e,i::v::r,l,u,(i =+ DATA (t,v,d)) m)``,
  SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC)
  THEN1 (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [] \\ DECIDE_TAC) << [  
    Cases_on `k = i` THEN1 (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
    \\ `range ((if u then 1 + l else 1),i) k ==> range ((if u then 1 + l else 1),i + 1) k` by 
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC bool_ss [MEM] \\ METIS_TAC [],
    `~range ((if u then 1 + l else 1),i) k` by
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
    \\ Cases_on `i = k` \\ FULL_SIMP_TAC bool_ss [UPDATE_def,heap_type_distinct]
    \\ Q.ABBREV_TAC `nn = if u then 1 + l else 1`
    \\ `range (nn,k + 1) k` by (REWRITE_TAC [range_def] \\ DECIDE_TAC) \\ METIS_TAC [],
    Cases_on `i = k` \\ FULL_SIMP_TAC bool_ss 
      [UPDATE_def,heap_type_11,PAIR_EQ,SUBSET0_DEF,SUBSET_DEF,INSERT_THM,IN_DEF,EMPTY_DEF,MEM]    
    \\ `!k. range ((if u then 1 + l else 1),i) k ==> range ((if u then 1 + l else 1),i + 1) k` by 
        (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC) THEN1 METIS_TAC []  
    \\ `range ((if u then 1 + l else 1),i) k` by 
         (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
    \\ RES_TAC \\ METIS_TAC []]);

val cheney_alloc_ok = store_thm("cheney_alloc_ok",
  ``!i e t v r l u m d. 
        ok_state (i,e,t::v::r,l,u,m) ==> ok_state (cheney_alloc (i,e,t::v::r,l,u,m) (d:'a))``,
  REWRITE_TAC [cheney_alloc_def,cheney_alloc_aux_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss [cheney_alloc_aux2_def] THEN1 
    (ASM_SIMP_TAC std_ss [LET_DEF,DECIDE ``n<m ==> ~(n=m:num)``,HD,TL]  \\ METIS_TAC [ok_state_LESS])
  \\ `?i2 e2 root2 l2 u2 m2. cheney_collector (i,e,t::v::r,l,u,m) = (i2,e2,root2,l2,u2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC bool_ss [cheney_alloc_aux2_def]
  \\ IMP_RES_TAC cheney_collector_spec 
  \\ Cases_on `i2 = e2` \\ ASM_SIMP_TAC std_ss [LET_DEF] THEN1 METIS_TAC []
  \\ `FST (SND (SND (cheney_collector (i,e,t::v::r,l,u,m)))) = root2` by METIS_TAC [PAIR_EQ,PAIR]
  \\ Q.PAT_ASSUM `FST (SND xx) = yy` (ASSUME_TAC o RW [FST,SND] o 
       CONV_RULE (DEPTH_CONV arm_progLib.FORCE_PBETA_CONV) o 
       SIMP_RULE std_ss [LET_DEF,move_roots_def,cheney_collect_def])
  \\ Cases_on `root2` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11]
  \\ FULL_SIMP_TAC std_ss [HD,TL] \\ MATCH_MP_TAC ok_state_LESS \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `u2` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC);

val cheney_alloc_spec = store_thm("cheney_alloc_spec",
  ``(cheney_alloc s (d:'a) = s') ==>
    ch_inv (t1::t2::ts,h,l) s /\ CARD (reachables (t1::t2::ts) (set h)) < l ==>
    ch_inv (fresh h::t2::ts, h |+ (fresh h,t1,t2,d),l) s'``,
  `?i e root a l u m. s = (i,e,root,l,u,m)` by METIS_TAC [PAIR]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss []
  \\ STRIP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))  
  \\ ASM_SIMP_TAC bool_ss [cheney_alloc_def]  
  \\ Cases_on `~(l' = l)` THEN1 METIS_TAC [ch_inv_def]
  \\ FULL_SIMP_TAC bool_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ `?i' e' c' l' u' m'. (cheney_alloc_aux (i,e,root,l,u,m) = (i',e',c',l',u',m'))` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,cheney_alloc_aux2_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC cheney_alloc_aux_spec
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
       FULL_SIMP_TAC bool_ss [range_def,ok_state_def,IN_DEF,LET_DEF] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1  ASM_SIMP_TAC std_ss [swap_def] 
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC,GSYM rich_listTheory.MAP_MAP_o]
  \\ STRIP_TAC THEN1 ASM_SIMP_TAC std_ss [swap_def]
  \\ `(MAP b' (MAP (swap i' (k (fresh h))) t) = t2::ts)` by 
   (Q.PAT_ASSUM `MAP b' t = t2::ts` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC bool_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
    \\ MATCH_MP_TAC MAP_ID        
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF,IN_DEF,range_def,MEM]
    \\ Cases_on `k' = 0` \\ ASM_SIMP_TAC std_ss [swap_def]
    \\ `~(k' = i')` by METIS_TAC [DECIDE ``m<n:num ==> ~(m=n)``]
    \\ Cases_on `k' = k (fresh h)` \\ ASM_SIMP_TAC bool_ss []
    \\ `?x y d. (m' k' = DATA (x,y,d))` by METIS_TAC []   
    \\ `basic_abs m' (k (fresh h),x,y,d)` by (SIMP_TAC bool_ss [basic_abs] \\ METIS_TAC [])
    \\ `apply b' (set h) (k (fresh h),x,y,d)` by (FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [apply_def,IN_DEF,FUN_EQ_THM,set_def]   
    \\ METIS_TAC [SIMP_RULE std_ss [IN_DEF] fresh_NOT_IN_FDOM])
  \\ ASM_SIMP_TAC bool_ss []
  \\ `m' i' = EMP` by 
    (FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF,range_def,IN_DEF]
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
  \\ `reachables (f::t2::ts) ((f,t1,t2,d) INSERT set h) =
      (f,t1,t2,d) INSERT reachables (t1::t2::ts) (set h)` by
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
    \\ REPEAT STRIP_TAC << [
      Cases_on `range (if u' then 1+l' else 1,i') z` \\ RES_TAC 
      \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [range_def,IN_DEF] \\ METIS_TAC [DECIDE ``~(i<i:num)``],
      Cases_on `range (if u' then 1+l' else 1,i') y` \\ RES_TAC 
      \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [range_def,IN_DEF] \\ METIS_TAC [DECIDE ``~(i<i:num)``],
      `~(b' h' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
      \\ FULL_SIMP_TAC bool_ss [MEM] \\ METIS_TAC [range_BORDER],
      `~(b' h'' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
      \\ FULL_SIMP_TAC bool_ss [MEM] \\ METIS_TAC [range_BORDER]])
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
    \\ METIS_TAC [range_BORDER])        
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
      \\ METIS_TAC [range_BORDER])        
    \\ `x IN range (if u' then 1+l' else 1,i')` by METIS_TAC [heap_type_distinct] 
    \\ `?x' y d. (m' x = DATA (x',y,d)) /\ {x'; y} SUBSET0 range (if u' then 1+l' else 1,i')` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,SUBSET_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC std_ss [IN_DEF] \\ `~(y = i') /\ ~(z = i')` by METIS_TAC [range_BORDER]
    \\ REVERSE (`~(x = k (fresh h)) /\ ~(y = k (fresh h)) /\ ~(z = k (fresh h))` by ALL_TAC)
    THEN1 (ASM_SIMP_TAC std_ss [swap_def] \\ METIS_TAC [basic_abs])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss []
    \\ `range (if u' then 1+l' else 1,i') (k (fresh h))` by METIS_TAC []           
    \\ `?j1 j2 j3. basic_abs m' (k (fresh h),j1,j2,j3)` by METIS_TAC [basic_abs]
    \\ `apply b' (set h) (k (fresh h),j1,j2,j3)` by METIS_TAC []     
    \\ FULL_SIMP_TAC bool_ss [apply_def,IN_DEF] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `xxx SUBSET basic_abs m'` 
       (fn th => MATCH_MP_TAC (RW [EXPAND_SUBSET] th) \\ ASSUME_TAC th)
  \\ Q.ABBREV_TAC `xxx = apply b' (reachables (t1::t2::ts) (set h))`
  \\ Q.PAT_ASSUM `apply (swap i' (k (fresh h))) xxx (x,y,z,d')` 
       (ASSUME_TAC o SIMP_RULE std_ss [apply_def,IN_DEF])
  \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ `basic_abs m' (swap i' (k (fresh h)) x,swap i' (k (fresh h)) y,
              swap i' (k (fresh h)) z,d')` by METIS_TAC []
  \\ Q.ABBREV_TAC `ff = (fresh h)`  
  \\ `(!a5 b5 c5. ~basic_abs m' (k ff,a5,b5,c5))` by 
   (REPEAT STRIP_TAC \\ `apply b' (set h) (k ff,a5,b5,c5)` by METIS_TAC []
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

val cheney_cons_0 = store_thm("cheney_cons_0",
  ``ch_inv (xs,h,l) (i,e,ys,l,u,m) ==> ch_inv (0::xs,h,l) (i,e,0::ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM]  
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC bool_ss [MAP]
  \\ MATCH_MP_TAC SUBSET_TRANS \\ Q.EXISTS_TAC `apply b (reachables xs (set h))`
  \\ ASM_SIMP_TAC bool_ss [] \\ MATCH_MP_TAC apply_SUBSET
  \\ SIMP_TAC std_ss [reachables_def,EXPAND_SUBSET,MEM] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC []    
  \\ Q.UNDISCH_TAC `x IN reachable r (set h)` \\ ASM_SIMP_TAC std_ss [reachable_def,IN_DEF]
  \\ REPEAT STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [IN_DEF,set_def]
  \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [APPEND,path_def,IN_DEF,set_def] \\ METIS_TAC []);

val LENGTH_IMP_APPEND_11 = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> ((xs ++ xs' = ys ++ ys') = (xs = ys) /\ (xs' = ys'))``,
  Induct \\ Cases_on `ys` 
  \\ ASM_SIMP_TAC std_ss [CONS_11,LENGTH,DECIDE ``~(SUC n = 0)``,APPEND] \\ METIS_TAC []);

val cheney_append = store_thm("cheney_append",
  ``(LENGTH xs = LENGTH ys) /\
    ch_inv (xs ++ x::xs2,h,l) (i,e,ys ++ y::ys2,l,u,m) ==> 
    ch_inv (x::xs ++ xs2,h,l) (i,e,y::ys ++ ys2,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,
    APPEND,MEM_APPEND,MAP,MAP_APPEND,CONS_11]  
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
    THEN1 METIS_TAC [LENGTH_IMP_APPEND_11,LENGTH_MAP,CONS_11]
    \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
    \\ FULL_SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MEM_APPEND] \\ METIS_TAC [])  
  \\ METIS_TAC []);

val cheney_delete = store_thm("cheney_delete",
  ``ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==> ch_inv (xs,h,l) (i,e,ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]  
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `b` \\ ASM_SIMP_TAC bool_ss []  
  \\ `?k. bijection k /\ (b o k = I) /\ (k o b = I)` by METIS_TAC [bijection_inv]
  \\ IMP_RES_TAC (Q.ISPECL [`r:num list`,`f:num->num`,`g:num->num`,`s:(num#num#num#'a) set`] apply_reachables)  
  \\ MATCH_MP_TAC SUBSET_TRANS
  \\ Q.EXISTS_TAC `apply b (reachables (x::xs) (set h))`
  \\ ASM_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ FULL_SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MAP] \\ METIS_TAC []);

val cheney_car = store_thm("cheney_car",
  ``((x,x',x'',d) IN set h) /\ (y' = FST (getDATA (m y))) /\
    ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==> 
    ch_inv (x'::x::xs,h,l) (i,e,y'::y::ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]  
  \\ STRIP_TAC  
  \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ `apply b (reachables (x::xs) (set h)) (k x,k x',k x'',d)` by 
   (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM,IN_DEF,reachables_def,MEM]
    \\ Q.EXISTS_TAC `x` \\ REWRITE_TAC [reachable_def])
  \\ `basic_abs m (k x,k x',k x'',d)` by 
    (FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
  \\ `k x = y` by (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [basic_abs,getDATA_def,FST]
  \\ `?x'' y'' d''. (m y = DATA (x'',y'',d'')) /\ {x''; y''} SUBSET0 range (if u then 1+l else 1,i)` by METIS_TAC [heap_type_distinct]
  \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
  \\ STRIP_TAC THEN1 (REPEAT STRIP_TAC \\ METIS_TAC [heap_type_distinct,FST])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC bool_ss [GSYM SUBSET_DEF,EXPAND_SUBSET,basic_abs,apply_def]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,FUN_EQ_THM,FEVERY_DEF]
    \\ FULL_SIMP_TAC bool_ss [reachables_def,IN_DEF,set_def]
    \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `b` \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ FULL_SIMP_TAC std_ss [GSYM SUBSET_DEF]
  \\ MATCH_MP_TAC SUBSET_TRANS
  \\ Q.EXISTS_TAC `apply b (reachables (x::xs) (set h))`
  \\ ASM_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MAP] 
  \\ REPEAT STRIP_TAC THENL [ALL_TAC,METIS_TAC [],METIS_TAC []]
  \\ Q.EXISTS_TAC `x` \\ REWRITE_TAC [reachable_def]
  \\ DISJ2_TAC \\ FULL_SIMP_TAC bool_ss [reachable_def]
  THEN1 (Q.EXISTS_TAC `[]` \\ SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC [])
  \\ (Q.EXISTS_TAC `x'::p` \\ SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC []));

val cheney_cdr = store_thm("cheney_cdr",
  ``((x,x',x'',d) IN set h) /\ (y' = FST (SND (getDATA (m y)))) /\
    ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==> 
    ch_inv (x''::x::xs,h,l) (i,e,y'::y::ys,l,u,m)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]  
  \\ STRIP_TAC  
  \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ `apply b (reachables (x::xs) (set h)) (k x,k x',k x'',d)` by 
   (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM,IN_DEF,reachables_def,MEM]
    \\ Q.EXISTS_TAC `x` \\ REWRITE_TAC [reachable_def])
  \\ `basic_abs m (k x,k x',k x'',d)` by 
    (FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
  \\ `k x = y` by (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [basic_abs,getDATA_def,FST]
  \\ `?x'' y'' d''. (m y = DATA (x'',y'',d'')) /\ {x''; y''} SUBSET0 range (if u then 1+l else 1,i)` by METIS_TAC [heap_type_distinct]
  \\ FULL_SIMP_TAC std_ss [heap_type_11,SUBSET0_DEF,IN_INSERT,SUBSET_DEF]
  \\ STRIP_TAC THEN1 (REPEAT STRIP_TAC \\ METIS_TAC [heap_type_distinct,FST])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC bool_ss [GSYM SUBSET_DEF,EXPAND_SUBSET,basic_abs,apply_def]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,FUN_EQ_THM,FEVERY_DEF]
    \\ FULL_SIMP_TAC bool_ss [reachables_def,IN_DEF,set_def]
    \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `b` \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ FULL_SIMP_TAC std_ss [GSYM SUBSET_DEF]
  \\ MATCH_MP_TAC SUBSET_TRANS
  \\ Q.EXISTS_TAC `apply b (reachables (x::xs) (set h))`
  \\ ASM_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [EXPAND_SUBSET]
  \\ SIMP_TAC bool_ss [apply_def,reachables_def,IN_DEF,MEM,MAP] 
  \\ REPEAT STRIP_TAC THENL [ALL_TAC,METIS_TAC [],METIS_TAC []]
  \\ Q.EXISTS_TAC `x` \\ REWRITE_TAC [reachable_def]
  \\ DISJ2_TAC \\ FULL_SIMP_TAC bool_ss [reachable_def]
  THEN1 (Q.EXISTS_TAC `[]` \\ SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC [])
  \\ (Q.EXISTS_TAC `x''::p` \\ SIMP_TAC bool_ss [path_def,APPEND] \\ METIS_TAC []));

val cheney_data = store_thm("cheney_data",
  ``((x,x',x'',d) IN set h) /\ ch_inv (x::xs,h,l) (i,e,y::ys,l,u,m) ==> 
    (d = SND (SND (getDATA (m y))))``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_abs_def,ok_state_def,LET_DEF,MEM,MAP,CONS_11]  
  \\ STRIP_TAC  
  \\ `?k. (b o k = I) /\ (k o b = I) /\ bijection k` by METIS_TAC [bijection_inv]
  \\ `apply b (reachables (x::xs) (set h)) (k x,k x',k x'',d)` by 
   (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM,IN_DEF,reachables_def,MEM]
    \\ Q.EXISTS_TAC `x` \\ REWRITE_TAC [reachable_def])
  \\ `basic_abs m (k x,k x',k x'',d)` by 
    (FULL_SIMP_TAC bool_ss [SUBSET_DEF,IN_DEF] \\ METIS_TAC [])
  \\ `k x = y` by (FULL_SIMP_TAC std_ss [apply_def,FUN_EQ_THM] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [basic_abs,getDATA_def,FST,SND]);

val cheney_init = store_thm("cheney_init",
  ``!xs l. ch_inv (MAP (\x.0) xs,FEMPTY,l) (1,1+l,MAP (\x.0) (xs:num list),l,F,\x.EMP)``,
  SIMP_TAC bool_ss [ch_inv_thm,ok_state_def,ok_abs_def,FEVERY_FEMPTY,FDOM_FEMPTY,
    LESS_EQ_REFL,LET_DEF,FINITE_EMPTY,MEM_MAP,heap_type_distinct,NOT_IN_EMPTY,
    range_lemmas,DECIDE ``1<=1+l:num``]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (Q.EXISTS_TAC `I` \\ SIMP_TAC std_ss [rich_listTheory.MAP_MAP_o,apply_I,
     bijection_def,ONTO_DEF,EXPAND_SUBSET,reachables_def,EMPTY_DEF,IN_DEF,
     basic_abs,heap_type_distinct,ONE_ONE_DEF,set_def,FDOM_FEMPTY])
  \\ METIS_TAC []);

  
val _ = export_theory();
