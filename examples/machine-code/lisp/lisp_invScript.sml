open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_inv";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory; 
open combinTheory finite_mapTheory stringTheory addressTheory;

open lisp_gcTheory cheney_gcTheory cheney_allocTheory; 
open lisp_typeTheory;

infix \\ 
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* --- definitions --- *)


(* s-expression inv *)

val lisp_ref_def = Define `
  (lisp_ref (Dot x y) (v,vi) h sym = ~(v = 0) /\ v IN FDOM h /\ 
    let (m,n,mi,ni) = h ' v in lisp_ref x (m,mi) h sym /\ lisp_ref y (n,ni) h sym) /\
  (lisp_ref (Num k) (v,vi) h sym = (v = 0) /\ (vi = (n2w k,F)) /\ k < 2**30) /\ 
  (lisp_ref (Sym s) (v,vi) h sym = (v = 0) /\ ?w. (vi = (w,T)) /\ (ADDR32 w,s) IN sym)`;


(* symbol table inv *)

val string_mem_def = Define `
  (string_mem "" (a,m:word32->word8,df) = T) /\
  (string_mem (STRING c s) (a,m,df) = a IN df /\
      (m a = n2w (ORD c)) /\ string_mem s (a+1w,m,df))`;

val string_mem_dom_def = Define `
  (string_mem_dom "" (a:word32) = {}) /\
  (string_mem_dom (STRING c s) a = a INSERT string_mem_dom s (a+1w))`;

val symbol_table_def = Define `
  (symbol_table [] x (a,dm,m,dg,g) = (m a = 0w) /\ a IN dm /\ (x = {})) /\
  (symbol_table (s::xs) x (a,dm,m,dg,g) = ~(s = "") /\ string_mem s (a+8w,g,dg) /\ 
    (m a = n2w (LENGTH s)) /\ {a; a+4w} SUBSET dm /\ ((a,s) IN x) /\
      let a' = a + n2w (8 + (LENGTH s + 3) DIV 4 * 4) in
        a <+ a' /\ (m (a+4w) = a') /\ 
        symbol_table xs (x DELETE (a,s)) (a',dm,m,dg,g))`;

val symbol_table_dom_def = Define `
  (symbol_table_dom [] (a,dm,dg) = ALIGNED a /\ a IN dm) /\
  (symbol_table_dom (s::xs) (a,dm,dg) = ~(s = "") /\ 
    string_mem_dom s (a+8w) SUBSET dg /\ {a; a+4w} SUBSET dm /\
    w2n a + 8 + LENGTH s + 3 < 2**32 /\
      symbol_table_dom xs (a + n2w (8 + (LENGTH s + 3) DIV 4 * 4),dm,dg))`;

val builtin_symbols_def = Define `
  builtin_symbols = 
    ["nil"; "t"; "quote"; "*"; "+"; "-"; "<"; "car"; "cdr"; "cons";
     "equal"; "if"; "consp"; "numberp"; "symbolp"; "lambda"]`;

val set_add_def = Define `set_add a x (b,s) = (b - a, s) IN x`;

val lisp_symbol_table_def = Define `
  lisp_symbol_table x (a,dm,m,dg,g) = 
    ?symbols.
      symbol_table (builtin_symbols ++ symbols) (set_add a x) (a,dm,m,dg,g) /\
      ALL_DISTINCT (builtin_symbols ++ symbols)`;


(* main inv *)

val lisp_inv_def = Define `
  lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,df,f,sym,rest) =
    ?v1 v2 v3 v4 v5 v6 h sa.
      ch_arm ([v1;v2;v3;v4;v5;v6],h,limit) (w1,w2,w3,w4,w5,w6,a,df,f) /\
      lisp_symbol_table sym (sa,rest) /\
      lisp_ref x1 v1 h sym /\ lisp_ref x2 v2 h sym /\ lisp_ref x3 v3 h sym /\ 
      lisp_ref x4 v4 h sym /\ lisp_ref x5 v5 h sym /\ lisp_ref x6 v6 h sym`;

(* old version

val lisp_x_def = Define `
  (lisp_x (Num k) (a,dm,m) sym = (a = n2w (k * 4 + 2)) /\ k < 2**30) /\ 
  (lisp_x (Sym s) (a,dm,m) sym = ((a - 3w) && 3w = 0w) /\ (a - 3w,s) IN sym) /\
  (lisp_x (Dot x y) (a,dm,m) sym = a IN dm /\ (a + 4w) IN dm /\ 
    lisp_x x (m a,dm,m) sym /\ lisp_x y (m (a+4w),dm,m) sym)`;

val lisp_inv_def = Define `
  lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,v,df,f,sym,rest) =
    ?i e u d sa. 
      32 <= w2n v /\ w2n v + 2 * 8 * l + 20 < 2 ** 32 /\
      lisp_symbol_table sym (sa,rest) /\ (df = ref_set v (l+l+1)) /\
      lisp_x x1 (w1,d,f) sym /\ lisp_x x2 (w2,d,f) sym /\ lisp_x x3 (w3,d,f) sym /\
      lisp_x x4 (w4,d,f) sym /\ lisp_x x5 (w5,d,f) sym /\ lisp_x x6 (w6,d,f) sym /\
      (f v = v + 8w * n2w i) /\ (v && 3w = 0w) /\ ~(v = 0w) /\
      (f (v + 4w) = v + 8w * n2w e) /\
      (f (v - 28w) = (if u then 0w else 1w)) /\
      (f (v - 32w) = 8w * n2w l) /\ ~(l = 0) /\
      let a = (if u then 1 + l else 1) in
        a <= i /\ i <= e /\ (e = a + l) /\
        ({ v + 8w * n2w j | a <= j /\ j < i } UNION
         { v + 8w * n2w j + 4w | a <= j /\ j < i } = d)`;

ref_set_def

*)

(* --- theorems --- *)

val CARD_LESS_EQ_LSIZE = prove(
  ``!q x y h. ~(0 IN FDOM h) /\ lisp_ref q (x,y) h sym ==> 
              CARD (reachables [x] (ch_set h)) <= LSIZE q``,
  Induct THEN1
   (SIMP_TAC std_ss [lisp_ref_def,LSIZE_def,ADD1]    
    \\ STRIP_TAC \\ STRIP_TAC
    \\ `?m n mi ni. h ' x = (m,n,mi,ni)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ STRIP_TAC \\ IMP_RES_TAC reachables_NEXT \\ RES_TAC
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `CARD (reachables [n] (ch_set h)) + CARD (reachables [m] (ch_set h)) + 1`
    \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `CARD (reachables [n] (ch_set h) UNION reachables [m] (ch_set h)) + 1`
    \\ ASM_SIMP_TAC std_ss [GSYM CARD_UNION,FINITE_reachables]
    \\ `1 = CARD {(x,m,n,mi,ni)}` by METIS_TAC [CARD_SING]
    \\ ASM_SIMP_TAC std_ss [GSYM CARD_UNION,FINITE_reachables,FINITE_INSERT,FINITE_UNION,FINITE_EMPTY]
    \\ SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM])
  \\ SIMP_TAC bool_ss [lisp_ref_def,LSIZE_def,DECIDE ``n <= 0 = (n = 0)``,CARD_EQ_0,FINITE_reachables]
  \\ SIMP_TAC std_ss [EXTENSION,IN_DEF,EMPTY_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [reachables_def,reachable_def,IN_DEF,ch_set_def,MEM]
  \\ REPEAT (Cases_on `p`)
  \\ FULL_SIMP_TAC std_ss [APPEND,PATH_def,ch_set_def,IN_DEF]
  \\ METIS_TAC []);
    
val LIST_CARD_LESS_EQ_LSIZE = prove(
  ``!xs limit. ~(0 IN FDOM h) /\ SUM_LSIZE (MAP FST xs) < limit /\ 
               EVERY (\(x,y). lisp_ref x y h sym) xs ==>
               CARD (reachables (MAP (FST o SND) xs) (ch_set h)) < limit``,
  Induct 
  THEN1 SIMP_TAC std_ss [SUM_LSIZE_def,MAP,EVERY_DEF,reachables_THM,CARD_EMPTY]
  \\ Cases \\ Cases_on `r`
  \\ SIMP_TAC std_ss [EVERY_DEF,SUM_LSIZE_def,MAP]
  \\ ONCE_REWRITE_TAC [reachables_THM] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (DECIDE ``!m n l. m <= n /\ n < l ==> m < l:num``)  
  \\ Q.EXISTS_TAC `CARD (reachables [q'] (ch_set h)) + 
                   CARD (reachables (MAP (FST o SND) xs) (ch_set h))`
  \\ STRIP_TAC THEN1 SIMP_TAC std_ss [FINITE_reachables,GSYM CARD_UNION]
  \\ `SUM_LSIZE (MAP FST xs) < limit - LSIZE q` by DECIDE_TAC \\ RES_TAC
  \\ MATCH_MP_TAC (DECIDE ``!m n k l. n < l - k /\ m <= k ==> m + n < l:num``)
  \\ Q.EXISTS_TAC `LSIZE q` \\ ASM_SIMP_TAC bool_ss []
  \\ METIS_TAC [CARD_LESS_EQ_LSIZE]);

val lisp_ref_IMP = prove(
  ``!x v h z. lisp_ref x v h sym ==> lisp_ref x v (h |+ (fresh h,z)) sym``,
  Induct \\ STRIP_TAC \\ STRIP_TAC \\ Cases_on `v` \\ REWRITE_TAC [lisp_ref_def]
  \\ SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]  
  \\ REPEAT STRIP_TAC
  \\ `~(q = fresh h)` by METIS_TAC [fresh_NOT_IN_FDOM]
  \\ ASM_SIMP_TAC std_ss []
  \\ `?x4 y4 z4 q4. h ' q = (x4,y4,z4,q4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]);


(* cons *)

val lisp_inv_cons = store_thm("lisp_inv_cons",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs,sym,rest) ==>
     SUM_LSIZE [x1;x2;x3;x4;x5;x6] < limit ==>
     ?w1 w2 w3 w4 w5 w6 a' x' xs'.
     (arm_alloc (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) /\
     lisp_inv (Dot x1 x2,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a',x',xs',sym,rest) /\
     arm_alloc_pre (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) /\ (a' = a) /\ (x' = x)``,
  REWRITE_TAC [lisp_inv_def]
  \\ REPEAT STRIP_TAC
  \\ `?w1 w2 w3 w4 w5 w6 a' x' xs'.
       (arm_alloc (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) =
        (w1,w2,w3,w4,w5,w6,a',x',xs'))` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ `~(0 IN FDOM h)` by FULL_SIMP_TAC std_ss [ch_arm_def,ch_inv_def,ok_abs_def]
  \\ FULL_SIMP_TAC std_ss [SUM_LSIZE_def,ADD_ASSOC]
  \\ `CARD (reachables [FST v1; FST v2; FST v3; FST v4; FST v5; FST v6] (ch_set h)) < limit` by 
     METIS_TAC [(SIMP_RULE std_ss [EVERY_DEF,SUM_LSIZE_def,MAP,ADD_ASSOC] o
       Q.SPECL [`[(x1,v1);(x2,v2);(x3,v3);(x4,v4);(x5,v5);(x6,v6)]`,`limit`]) LIST_CARD_LESS_EQ_LSIZE]
  \\ IMP_RES_TAC (REWRITE_RULE [MAP] (Q.INST [`ts`|->`[t3;t4;t5;t6]`] ch_arm_alloc))
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(fresh h,SND v1)`
  \\ Q.EXISTS_TAC `v2` \\ Q.EXISTS_TAC `v3` \\ Q.EXISTS_TAC `v4` \\ Q.EXISTS_TAC `v5`
  \\ Q.EXISTS_TAC `v6` \\ Q.EXISTS_TAC `h |+ (fresh h,FST v1,FST v2,SND v1,SND v2)`
  \\ Q.EXISTS_TAC `sa` 
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM,LET_DEF]
  \\ REWRITE_TAC [fresh_NOT_IN_FDOM]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC lisp_ref_IMP \\ ASM_REWRITE_TAC []);


(* swap *)

val lisp_inv_swap1 = store_thm("lisp_inv_swap1",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss []);

val lisp_inv_swap2 = store_thm("lisp_inv_swap2",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x2,x1,x3,x4,x5,x6,limit) (w2,w1,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_swap2]);

val lisp_inv_swap3 = store_thm("lisp_inv_swap3",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x3,x2,x1,x4,x5,x6,limit) (w3,w2,w1,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_swap3]);

val lisp_inv_swap4 = store_thm("lisp_inv_swap4",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x4,x2,x3,x1,x5,x6,limit) (w4,w2,w3,w1,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_swap4]);

val lisp_inv_swap5 = store_thm("lisp_inv_swap5",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x5,x2,x3,x4,x1,x6,limit) (w5,w2,w3,w4,w1,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_swap5]);

val lisp_inv_swap6 = store_thm("lisp_inv_swap6",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x6,x2,x3,x4,x5,x1,limit) (w6,w2,w3,w4,w5,w1,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_swap6]);

fun find_swap_thm n = 
  el n [lisp_inv_swap1,lisp_inv_swap2,lisp_inv_swap3,lisp_inv_swap4,lisp_inv_swap5,lisp_inv_swap6]

fun generate_swap i j = 
  if i = 1 then find_swap_thm j else 
  if j = 1 then find_swap_thm i else 
  if i = j then find_swap_thm 1 else 
  DISCH_ALL (MATCH_MP (find_swap_thm i) (MATCH_MP (find_swap_thm j) (UNDISCH (find_swap_thm i))));
  (* e.g. to swap 4 and 5 do generate_swap 4 5 *)


(* copy *)

val lisp_inv_copy = store_thm("lisp_inv_copy",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (x1,x1,x3,x4,x5,x6,limit) (w1,w1,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [ch_arm_copy]);

fun generate_copy i j = 
  if i = j then generate_swap 1 1 else
  if j = 2 then let
    val sw1 = generate_swap 1 i
    val sw2 = generate_swap 1 2
    val th = MATCH_MP lisp_inv_copy (MATCH_MP sw2 (UNDISCH sw1))
    in DISCH_ALL (MATCH_MP sw1 th) end  
  else let
    val sw1 = generate_swap 2 i
    val sw2 = generate_swap 1 j
    val th = MATCH_MP lisp_inv_copy (MATCH_MP sw2 (UNDISCH sw1))
    in DISCH_ALL (MATCH_MP sw1 (MATCH_MP sw2 th)) end;
  (* e.g. to copy 5 into 3 do generate_copy 3 5 *)

val lisp_inv_move = save_thm("lisp_inv_move",let 
  fun pairs x [] = [] | pairs x (y::ys) = (x,y) :: pairs x ys
  fun cross [] ys = [] | cross (x::xs) ys = pairs x ys @ cross xs ys
  val list = filter (fn (x,y) => not (x = y)) (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
  val thms = map (fn (x,y) => UNDISCH (generate_copy y x)) list
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);


(* assignments *)

val lisp_inv_Num = store_thm("lisp_inv_Num",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    !n. n < 2**30 ==>
        lisp_inv (Num n,x2,x3,x4,x5,x6,limit) 
                 (n2w (n*4+2),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC 
  \\ Q.EXISTS_TAC `(0,n2w n, F)`
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_nil]
  \\ `n2w (n * 4 + 2) = ADDR32 (n2w n) + if F then 3w else 2w` by 
    SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w,AC MULT_COMM MULT_ASSOC]
  \\ METIS_TAC [lisp_ref_def,ch_arm_nil]);

val lisp_inv_nil = store_thm("lisp_inv_nil",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (Sym "nil",x2,x3,x4,x5,x6,limit) (3w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `(0,0w, T)`
  \\ IMP_RES_TAC (Q.INST [`b`|->`T`,`w`|->`0w`] ch_arm_nil)
  \\ FULL_SIMP_TAC std_ss [EVAL ``ADDR32 0w + 3w``]
  \\ `(ADDR32 0w,"nil") IN s` by 
   (`?dg dm g m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
    \\ `?xs. builtin_symbols = "nil" :: xs` by METIS_TAC [builtin_symbols_def]
    \\ FULL_SIMP_TAC std_ss [lisp_symbol_table_def]
    \\ FULL_SIMP_TAC std_ss [symbol_table_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,ADDR32_n2w,WORD_SUB_REFL])
  \\ ASM_SIMP_TAC std_ss [lisp_ref_def]
  \\ METIS_TAC [lisp_ref_def,ch_arm_nil]);

val lisp_inv_t = store_thm("lisp_inv_t",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (Sym "t",x2,x3,x4,x5,x6,limit) (15w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def] \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `(0,3w, T)`
  \\ IMP_RES_TAC (Q.INST [`b`|->`T`,`w`|->`3w`] ch_arm_nil)
  \\ FULL_SIMP_TAC std_ss [EVAL ``ADDR32 3w + 3w``]
  \\ `(ADDR32 3w,"t") IN s` by 
   (`?dg dm g m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
    \\ `?xs. builtin_symbols = "nil" :: "t" :: xs` by METIS_TAC [builtin_symbols_def]
    \\ FULL_SIMP_TAC std_ss [lisp_symbol_table_def]
    \\ FULL_SIMP_TAC std_ss [symbol_table_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,IN_DELETE,EVAL ``LENGTH "nil"``]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,ADDR32_n2w,WORD_ADD_SUB2])
  \\ ASM_SIMP_TAC std_ss [lisp_ref_def]
  \\ METIS_TAC [lisp_ref_def,ch_arm_nil]);


(* car and cdr *)

val lisp_inv_car_cdr = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) /\ isDot x1 ==>
    (w1 && 3w = 0w) /\ w1 IN x /\ w1 + 4w IN x /\ 
    lisp_inv (CAR x1,x2,x3,x4,x5,x6,limit) (xs w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) /\ 
    lisp_inv (CDR x1,x2,x3,x4,x5,x6,limit) (xs (w1 + 4w),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  REWRITE_TAC [lisp_inv_def,isDot_thm]    
  \\ STRIP_TAC \\ Cases_on `v1`
  \\ FULL_SIMP_TAC std_ss [CAR_def,lisp_ref_def,CDR_def]  
  \\ `~(q = 0)` by (FULL_SIMP_TAC std_ss [ch_arm_def,ch_inv_def,ok_abs_def] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1 METIS_TAC [FST,ch_arm_zero,ch_arm_addresses,ALIGNED_def]
  \\ STRIP_TAC THEN1 METIS_TAC [FST,ch_arm_zero,ch_arm_addresses,ALIGNED_def]
  \\ STRIP_TAC THEN1 METIS_TAC [FST,ch_arm_zero,ch_arm_addresses,ALIGNED_def]
  \\ IMP_RES_TAC ch_arm_car_cdr \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ `?m n mi ni. h ' q = (m,n,mi,ni)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [PAIR,abs_car_def,abs_cdr_def,LET_DEF]
  \\ METIS_TAC []);

val lisp_inv_car_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> isDot x1 ==> 
    lisp_inv (CAR x1,x2,x3,x4,x5,x6,limit) (xs w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  METIS_TAC [lisp_inv_car_cdr]);

val lisp_inv_cdr_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> isDot x1 ==> 
    lisp_inv (CDR x1,x2,x3,x4,x5,x6,limit) (xs (w1 + 4w),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  METIS_TAC [lisp_inv_car_cdr]);

val lisp_inv_address_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    isDot x1 ==> (w1 && 3w = 0w) /\ w1 IN x /\ w1 + 4w IN x``,
  METIS_TAC [lisp_inv_car_cdr]);

val eq_lemma = METIS_PROVE [] ``(x ==> y) ==> (y ==> x) ==> (x = y:bool)``
fun mk_eq_lemma th = MATCH_MP (MATCH_MP eq_lemma th) th;

fun generate_CAR i j is_car = let
  val th = if is_car then lisp_inv_car_lemma else lisp_inv_cdr_lemma
  val th = MATCH_MP th (UNDISCH (generate_swap 1 i))
  val th = UNDISCH (RW [AND_IMP_INTRO] (DISCH_ALL th))
  val th = DISCH_ALL (RW1 [mk_eq_lemma (generate_swap 1 i)] th)
  val th = RW [GSYM AND_IMP_INTRO] th
  val th = MATCH_MP th (UNDISCH (generate_copy i j))
  in DISCH_ALL th end; 
  (* to put car of 5 in 2 do generate_CAR 2 5 false *)

val lisp_inv_address = save_thm("lisp_inv_address",let 
  val thms = [MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap1),
              MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap2),
              MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap3),
              MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap4),
              MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap5),
              MATCH_MP lisp_inv_address_lemma (UNDISCH lisp_inv_swap6)]
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);

val lisp_inv_car = save_thm("lisp_inv_car",let 
  fun pairs x [] = [] | pairs x (y::ys) = (x,y) :: pairs x ys
  fun cross [] ys = [] | cross (x::xs) ys = pairs x ys @ cross xs ys
  val thms = map (fn (x,y) => UNDISCH (generate_CAR y x true)) (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);

val lisp_inv_cdr = save_thm("lisp_inv_cdr",let 
  fun pairs x [] = [] | pairs x (y::ys) = (x,y) :: pairs x ys
  fun cross [] ys = [] | cross (x::xs) ys = pairs x ys @ cross xs ys
  val thms = map (fn (x,y) => UNDISCH (generate_CAR y x false)) (cross [1,2,3,4,5,6] [1,2,3,4,5,6])
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);


(* test *)

val lisp_inv_isDot = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    (isDot x1 = ALIGNED w1)``,
  SIMP_TAC std_ss [lisp_inv_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GSYM ch_arm_zero) \\ ASM_REWRITE_TAC []
  \\ Cases_on `v1` \\ Cases_on `x1` 
  \\ FULL_SIMP_TAC std_ss [isDot_def,lisp_ref_def,ch_arm_def,ch_inv_def,ok_abs_def]
  \\ METIS_TAC []);

val lisp_inv_test_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    ((w1 && 3w = 0w) = isDot x1) /\ ((w1 && 1w = 0w) = ~isSym x1)``,
  STRIP_TAC \\ IMP_RES_TAC lisp_inv_isDot
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Cases_on `isDot x1` THEN1 
   (`ALIGNED w1` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [isDot_thm,isSym_def]
    \\ Q.PAT_ASSUM `ALIGNED w1` MP_TAC
    \\ Q.SPEC_TAC (`w1`,`w`) \\ Cases_word
    \\ SIMP_TAC std_ss [ALIGNED_def,n2w_and_1,n2w_and_3]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ `n MOD 4 < 4 /\ n MOD 2 < 2` by 
         (STRIP_TAC \\ MATCH_MP_TAC MOD_LESS \\ SIMP_TAC std_ss [])
    \\ `n MOD 4 < 4294967296 /\ n MOD 2 < 4294967296` by DECIDE_TAC   
    \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0 < 4``)))
    \\ STRIP_TAC    
    \\ ONCE_ASM_REWRITE_TAC []
    \\ Q.PAT_ASSUM `n = n DIV 4 * 4 + n MOD 4` (K ALL_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ REWRITE_TAC [GSYM (EVAL ``2*2``),MULT_ASSOC]
    \\ SIMP_TAC bool_ss [MOD_EQ_0,EVAL ``0<2``])
  \\ `(FST v1 = 0)` by   
    (FULL_SIMP_TAC std_ss [ch_arm_def,ch_inv_def,MAP,ch_word_def,CONS_11]
    \\ Cases_on `v1` \\ Cases_on `x1`
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def,isDot_def])
  \\ IMP_RES_TAC ch_arm_const \\ ASM_REWRITE_TAC []
  \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isDot_def,isNum_def,isSym_def]
  \\ Cases_on `v1` \\ FULL_SIMP_TAC std_ss [lisp_ref_def] THENL [
    SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,word_add_n2w,n2w_and_1,n2w_11]  
    \\ REWRITE_TAC [DECIDE ``4*n+2 = (2*n + 1)* 2``]
    \\ REWRITE_TAC [MATCH_MP MOD_EQ_0 (DECIDE ``0<2``)]
    \\ SIMP_TAC std_ss [],
    Q.SPEC_TAC (`w`,`w`) \\ Cases_word
    \\ SIMP_TAC (std_ss++SIZES_ss) [ADDR32_n2w,word_add_n2w,n2w_and_1,n2w_11]  
    \\ REWRITE_TAC [DECIDE ``4*n+3 = (2*n)*2 + 3``]
    \\ REWRITE_TAC [MATCH_MP MOD_TIMES (DECIDE ``0<2``)]
    \\ EVAL_TAC]);
    
val lisp_inv_test = save_thm("lisp_inv_test",let 
  val thms = [MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap1),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap2),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap3),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap4),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap5),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap6)]
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);


(* basic arithmetic *)

val lisp_inv_ADD = store_thm("lisp_inv_ADD",
  ``isNum x1 /\ isNum x2 /\ getNum x1 + getNum x2 < 2**30 ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (LISP_ADD x1 x2,x2,x3,x4,x5,x6,limit) (w1+w2-2w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  STRIP_TAC
  \\ `?a1 a2. (x1 = Num a1) /\ (x2 = Num a2)` by 
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNum_def,SExp_11])
  \\ ASM_SIMP_TAC std_ss [LISP_ADD_def,lisp_inv_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `v1` \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
  \\ IMP_RES_TAC (RW[](GEN_ALL(Q.INST [`b`|->`F`] ch_arm_nil)))
  \\ Q.EXISTS_TAC `(0,n2w (a1+a2),F)`  
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,getNum_def]
  \\ REVERSE (`w1 + w2 - 2w = ADDR32 (n2w (a1 + a2)) + 2w` by ALL_TAC)
  THEN1 (ASM_REWRITE_TAC [] \\ METIS_TAC [ch_arm_nil])      
  \\ Q.PAT_ASSUM `!w. bbb` (K ALL_TAC)    
  \\ Cases_on `v2` 
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
  \\ `(x1' = 0) /\ (x2' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ ASM_SIMP_TAC std_ss [ref_field_def,WORD_ADD_ASSOC,WORD_ADD_SUB,ADDR32_ADD]
  \\ REWRITE_TAC [ADDR32_n2w,word_add_n2w,LEFT_ADD_DISTRIB]
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);
 
val lisp_inv_SUB = store_thm("lisp_inv_SUB",
  ``isNum x1 /\ isNum x2 /\ getNum x2 <= getNum x1 ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    lisp_inv (LISP_SUB x1 x2,x2,x3,x4,x5,x6,limit) (w1 - w2 + 2w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  STRIP_TAC
  \\ `?a1 a2. (x1 = Num a1) /\ (x2 = Num a2)` by 
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNum_def,SExp_11])
  \\ ASM_SIMP_TAC std_ss [LISP_SUB_def,lisp_inv_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `v1` \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
  \\ IMP_RES_TAC (RW[](GEN_ALL(Q.INST [`b`|->`F`] ch_arm_nil)))
  \\ Q.EXISTS_TAC `(0,n2w (a1-a2),F)`  
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,getNum_def]
  \\ `a1 < a2 + 1073741824` by DECIDE_TAC
  \\ REVERSE (`w1 - w2 + 2w = ADDR32 (n2w (a1 - a2)) + 2w` by ALL_TAC)
  THEN1 (ASM_REWRITE_TAC [] \\ METIS_TAC [ch_arm_nil])      
  \\ Q.PAT_ASSUM `!w. bbb` (K ALL_TAC)    
  \\ Cases_on `v2` 
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
  \\ FULL_SIMP_TAC std_ss [CONS_11,MAP]
  \\ `(x1' = 0) /\ (x2' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ ASM_SIMP_TAC std_ss [ref_field_def,ADDR32_SUB,WORD_SUB_PLUS,WORD_SUB_ADD]
  \\ Q.PAT_ASSUM `a2 <= a1` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [WORD_EQ_ADD_LCANCEL,WORD_ADD_SUB_ASSOC,GSYM ADDR32_SUB]
  \\ SIMP_TAC std_ss [GSYM NOT_LESS,word_arith_lemma2]);  

val lisp_inv_LESS = store_thm("lisp_inv_LESS",
  ``isNum x1 /\ isNum x2 ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    (LISP_LESS x1 x2 = w1 <+ w2)``,
  STRIP_TAC
  \\ `?a1 a2. (x1 = Num a1) /\ (x2 = Num a2)` by 
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNum_def,SExp_11])
  \\ ASM_SIMP_TAC std_ss [LISP_LESS_def,lisp_inv_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `v1` \\ Cases_on `v2` 
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
  \\ FULL_SIMP_TAC std_ss [CONS_11,MAP]
  \\ `(x1' = 0) /\ (x2' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ FULL_SIMP_TAC std_ss [ref_field_def] 
  \\ Q.PAT_ASSUM `a1 < 1073741824` MP_TAC
  \\ Q.PAT_ASSUM `a2 < 1073741824` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ REWRITE_TAC [ADDR32_n2w,word_add_n2w]
  \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w] 
  \\ REPEAT STRIP_TAC
  \\ `(4 * a1 + 2) < 4294967296 /\ (4 * a2 + 2) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

(* basic equality *)

val symbol_table_LOWER_EQ = prove(
  ``!xs a sym. symbol_table xs sym (a,dm,m,dg,g) /\ (b,x) IN sym ==> a <=+ b``,
  Induct \\ SIMP_TAC std_ss [symbol_table_def,NOT_IN_EMPTY,LET_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `a = b` THEN1 METIS_TAC [WORD_LOWER_EQ_REFL] 
  \\ `(b,x) IN (sym DELETE (a,h))` by METIS_TAC [IN_DELETE,PAIR_EQ]
  \\ RES_TAC \\ IMP_RES_TAC WORD_LOWER_LOWER_EQ_TRANS
  \\ ASM_SIMP_TAC std_ss [WORD_LOWER_OR_EQ]);

val symbol_tabel_11 = prove(
  ``!xs a sym. symbol_table xs sym (a,dm,m,dg,g) /\ (b,x) IN sym /\ (b,y) IN sym ==> 
               (x = y)``,
  Induct \\ SIMP_TAC std_ss [symbol_table_def,NOT_IN_EMPTY,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `a = b`) THEN1
   (`(b,x) IN (sym DELETE (a,h)) /\ (b,y) IN (sym DELETE (a,h))` by 
         METIS_TAC [IN_DELETE,PAIR_EQ]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `a2 = b + n2w (8 + (LENGTH h + 3) DIV 4 * 4)`
  \\ Cases_on `(b,x) IN (sym DELETE (a,h))` THEN1
    (`a2 <=+ b` by METIS_TAC [symbol_table_LOWER_EQ]
     \\ METIS_TAC [WORD_LOWER_EQ_ANTISYM])
  \\ Cases_on `(b,y) IN (sym DELETE (a,h))` THEN1
    (`a2 <=+ b` by METIS_TAC [symbol_table_LOWER_EQ]
     \\ METIS_TAC [WORD_LOWER_EQ_ANTISYM])
  \\ METIS_TAC [IN_DELETE,PAIR_EQ]);

val symbol_table_MEM = prove(
  ``!xs a sym. symbol_table xs sym (a,dm,m,dg,g) /\ (b,x) IN sym ==> 
               MEM x xs``,
  Induct THEN1 SIMP_TAC std_ss [symbol_table_def,NOT_IN_EMPTY,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `!y. (b,y) IN sym ==> (x = y)` by METIS_TAC [symbol_tabel_11]
  \\ Cases_on `b = a`
  \\ FULL_SIMP_TAC std_ss [symbol_table_def,MEM,LET_DEF] 
  \\ METIS_TAC [IN_DELETE,PAIR_EQ]);
          
val symbol_table_eq = store_thm("symbol_table_eq",
  ``!xs sym a. 
      symbol_table xs sym (a,dm,m,dg,g) /\ ALL_DISTINCT xs ==>
      (w1,s1) IN sym /\ (w2,s2) IN sym ==> ((w1 = w2) = (s1 = s2))``,
  Induct THEN1 SIMP_TAC std_ss [symbol_table_def,NOT_IN_EMPTY]
  \\ REWRITE_TAC [symbol_table_def]
  \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ Q.ABBREV_TAC `a2 = a + n2w (8 + (LENGTH h + 3) DIV 4 * 4)`
  \\ SIMP_TAC std_ss [LET_DEF,ALL_DISTINCT]    
  \\ REPEAT STRIP_TAC
  \\ Cases_on `(w1,s1) IN (sym DELETE (a,h))`
  \\ Cases_on `(w2,s2) IN (sym DELETE (a,h))`
  THEN1 METIS_TAC [] THENL [ 
    `(w2 = a) /\ (s2 = h)` by (FULL_SIMP_TAC std_ss [IN_DELETE] \\ METIS_TAC [])
    \\ `a2 <=+ w1 /\ MEM s1 xs` by METIS_TAC [symbol_table_LOWER_EQ,symbol_table_MEM]
    \\ IMP_RES_TAC WORD_LOWER_LOWER_EQ_TRANS 
    \\ METIS_TAC [WORD_LOWER_NOT_EQ],
    `(w1 = a) /\ (s1 = h)` by (FULL_SIMP_TAC std_ss [IN_DELETE] \\ METIS_TAC [])
    \\ `a2 <=+ w2 /\ MEM s2 xs` by METIS_TAC [symbol_table_LOWER_EQ,symbol_table_MEM]
    \\ IMP_RES_TAC WORD_LOWER_LOWER_EQ_TRANS 
    \\ METIS_TAC [WORD_LOWER_NOT_EQ],
    `(w1 = a) /\ (s1 = h)` by (FULL_SIMP_TAC std_ss [IN_DELETE] \\ METIS_TAC [])
    \\ `(w2 = a) /\ (s2 = h)` by (FULL_SIMP_TAC std_ss [IN_DELETE] \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss []]);

val lisp_inv_eq_lemma = prove(
  ``(isNum x1 /\ isNum x2) \/ (isSym x1 /\ isSym x2) ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    ((x1 = x2) = (w1 = w2))``,
  STRIP_TAC THEN1
   (`?a1 a2. (x1 = Num a1) /\ (x2 = Num a2)` by 
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNum_def,SExp_11])
    \\ ASM_SIMP_TAC std_ss [LISP_LESS_def,lisp_inv_def]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `v1` \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
    \\ Cases_on `v2` 
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def,ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]  
    \\ FULL_SIMP_TAC std_ss [CONS_11,MAP]
    \\ `(x1' = 0) /\ (x2' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
    \\ FULL_SIMP_TAC std_ss [ref_field_def,SExp_11,WORD_EQ_ADD_RCANCEL,ADDR32_11]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ `?a1 a2. (x1 = Sym a1) /\ (x2 = Sym a2)` by 
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isSym_def,SExp_11])
  \\ ASM_SIMP_TAC std_ss [SExp_11]
  \\ `?dg dm g m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,lisp_symbol_table_def]
  \\ STRIP_TAC \\ Cases_on `v1` \\ Cases_on `v2`
  \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
  \\ `(ADDR32 w + sa,a1) IN (set_add sa s) /\
      (ADDR32 w' + sa,a2) IN (set_add sa s)` by 
     FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ `(ADDR32 w + sa = ADDR32 w' + sa) = (a1 = a2)`by METIS_TAC [symbol_table_eq]
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11]
  \\ FULL_SIMP_TAC std_ss [ch_arm_def,ch_inv_def,ch_word_def,MAP,CONS_11]
  \\ FULL_SIMP_TAC std_ss [ch_arm_def,ch_inv_def,ch_word_def,MAP,CONS_11]
  \\ `(x1' = 0) /\ (x2' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
  \\ FULL_SIMP_TAC std_ss [ref_field_def,SExp_11,WORD_EQ_ADD_RCANCEL,ADDR32_11]
  \\ Cases_on `y1` \\ Cases_on `y2`
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11] 
  \\ METIS_TAC []);

val lisp_inv_eq = store_thm("lisp_inv_eq",
  ``~isDot x1 \/ ~isDot x2 ==> 
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    ((x1 = x2) = (w1 = w2))``,
  STRIP_TAC THENL [
    Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isDot_def]
    \\ Cases_on `x2` \\ STRIP_TAC \\ SIMP_TAC std_ss [SExp_distinct]
    \\ IMP_RES_TAC lisp_inv_test
    \\ FULL_SIMP_TAC std_ss [isNum_def,isSym_def,isDot_def]
    \\ METIS_TAC [lisp_inv_eq_lemma,isNum_def,isSym_def],
    Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isDot_def]
    \\ Cases_on `x1` \\ STRIP_TAC \\ SIMP_TAC std_ss [SExp_distinct]
    \\ IMP_RES_TAC lisp_inv_test
    \\ FULL_SIMP_TAC std_ss [isNum_def,isSym_def,isDot_def]
    \\ METIS_TAC [lisp_inv_eq_lemma,isNum_def,isSym_def]]);


(* symbol test *)

val builti_symbols_thm = prove(
  ``lisp_symbol_table s (sa,rest) ==>
    (ADDR32 0w,"nil") IN s /\ (ADDR32 3w,"t") IN s /\ 
    (ADDR32 6w,"quote") IN s /\ (ADDR32 10w,"*") IN s /\ 
    (ADDR32 13w,"+") IN s /\ (ADDR32 16w,"-") IN s /\ 
    (ADDR32 19w,"<") IN s /\ (ADDR32 22w,"car") IN s /\ 
    (ADDR32 25w,"cdr") IN s /\ (ADDR32 28w,"cons") IN s /\ 
    (ADDR32 31w,"equal") IN s /\ (ADDR32 35w,"if") IN s /\ 
    (ADDR32 38w,"consp") IN s /\ (ADDR32 42w,"numberp") IN s /\ 
    (ADDR32 46w,"symbolp") IN s /\ (ADDR32 50w,"lambda") IN s``,
  `?dg g dm m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [lisp_symbol_table_def]  
  \\ POP_ASSUM (K ALL_TAC)
  \\ STRIP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [builtin_symbols_def,APPEND]
  \\ ONCE_REWRITE_TAC [symbol_table_def]
  \\ SIMP_TAC std_ss [LENGTH,LET_DEF]
  \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_SUB_REFL]
  \\ ONCE_REWRITE_TAC [symbol_table_def]
  \\ SIMP_TAC std_ss [LENGTH,LET_DEF,IN_DELETE]
  \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB2,ADDR32_n2w]
  \\ NTAC 20 (SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ ONCE_REWRITE_TAC [symbol_table_def]
  \\ SIMP_TAC std_ss [LENGTH,LET_DEF,IN_DELETE]
  \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB2,ADDR32_n2w]));
  
val lisp_symbol_table_11 = prove(
  ``lisp_symbol_table s (sa,rest) /\
    (ADDR32 x1,s1) IN s /\ (ADDR32 x2,s2) IN s ==>
    ((x1 = x2) = (s1 = s2))``,    
  `?dg g dm m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [lisp_symbol_table_def]
  \\ REPEAT STRIP_TAC
  \\ `(ADDR32 x1 + sa,s1) IN (set_add sa s)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ `(ADDR32 x2 + sa,s2) IN (set_add sa s)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC symbol_table_eq
  \\ METIS_TAC [WORD_EQ_ADD_RCANCEL,ADDR32_11]);
  
val lisp_inv_test_builtin_lemma = prove( 
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> 
    ((w1 = ADDR32 0w + 3w) = (x1 = Sym "nil")) /\ 
    ((w1 = ADDR32 3w + 3w) = (x1 = Sym "t")) /\ 
    ((w1 = ADDR32 6w + 3w) = (x1 = Sym "quote")) /\ 
    ((w1 = ADDR32 10w + 3w) = (x1 = Sym "*")) /\ 
    ((w1 = ADDR32 13w + 3w) = (x1 = Sym "+")) /\ 
    ((w1 = ADDR32 16w + 3w) = (x1 = Sym "-")) /\ 
    ((w1 = ADDR32 19w + 3w) = (x1 = Sym "<")) /\ 
    ((w1 = ADDR32 22w + 3w) = (x1 = Sym "car")) /\ 
    ((w1 = ADDR32 25w + 3w) = (x1 = Sym "cdr")) /\ 
    ((w1 = ADDR32 28w + 3w) = (x1 = Sym "cons")) /\ 
    ((w1 = ADDR32 31w + 3w) = (x1 = Sym "equal")) /\ 
    ((w1 = ADDR32 35w + 3w) = (x1 = Sym "if")) /\ 
    ((w1 = ADDR32 38w + 3w) = (x1 = Sym "consp")) /\ 
    ((w1 = ADDR32 42w + 3w) = (x1 = Sym "numberp")) /\ 
    ((w1 = ADDR32 46w + 3w) = (x1 = Sym "symbolp")) /\ 
    ((w1 = ADDR32 50w + 3w) = (x1 = Sym "lambda"))``,
  STRIP_TAC \\ REVERSE (Cases_on `isSym x1 `) THEN1
   (`w1 && 1w = 0w` by METIS_TAC [lisp_inv_test]
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss 
         [isDot_def,isNum_def,isSym_def,SExp_distinct]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w,n2w_and_1]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ `?w. (v1 = (0,w,T)) /\ (w1 = ADDR32 w + 3w)` by 
   (FULL_SIMP_TAC std_ss [ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]
    \\ FULL_SIMP_TAC std_ss [ch_arm_def,ch_word_def,ch_inv_def,MAP,CONS_11]
    \\ FULL_SIMP_TAC std_ss [isSym_thm]        
    \\ Cases_on `v1` \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_ref_def]        
    \\ `(x1' = 0)` by METIS_TAC [bijection_def,ONE_ONE_DEF]
    \\ ASM_SIMP_TAC std_ss [ref_field_def])
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11]
  \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_ref_def]
  \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_ref_def,SExp_11]
  \\ Q.PAT_ASSUM `xx IN s` MP_TAC
  \\ Q.PAT_ASSUM `lisp_symbol_table sss ssss` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC
  \\ IMP_RES_TAC builti_symbols_thm
  \\ REPEAT STRIP_TAC
  \\ (MATCH_MP_TAC lisp_symbol_table_11 \\ ASM_SIMP_TAC std_ss []));
  
val lisp_inv_builtin = save_thm("lisp_inv_builtin",
  SIMP_RULE std_ss [ADDR32_n2w,word_add_n2w]
  lisp_inv_test_builtin_lemma);


(* LDEPTH *)

val lisp_ref_PATH_def = Define `
  (lisp_ref_PATH [] h = F) /\
  (lisp_ref_PATH [x] h = ~(x = 0) /\ x IN FDOM h) /\
  (lisp_ref_PATH (x::y::xs) h = ~(x = 0) /\ x IN FDOM h /\
    let (m,n,mi,ni) = h ' x in ((m = y) \/ (n = y)) /\ lisp_ref_PATH (y::xs) h)`;

val lisp_ref_reachable_def = Define `
  lisp_ref_reachable m n h = ?xs. lisp_ref_PATH ([m] ++ xs ++ [n]) h`;

val lisp_ref_reachable_step = prove(
  ``lisp_ref_reachable m r h /\ lisp_ref x (m,mi) h sym /\ ~(q = 0) /\
    q IN FDOM h /\ ((h ' q = (m,n,mi,ni)) \/ (h ' q = (n,m,ni,mi))) ==> 
    lisp_ref_reachable q r h``,
  SIMP_TAC std_ss [lisp_ref_reachable_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `m::xs`
  \\ FULL_SIMP_TAC std_ss [lisp_ref_PATH_def,APPEND_ASSOC,APPEND,LET_DEF]);
    
val lisp_ref_reachable_intro = prove(
  ``!x q r h t.
      lisp_ref x (q,r) h sym /\ ~(lisp_ref x (q,r) (h \\ t) sym) /\ ~(q = t) ==>
      lisp_ref_reachable q t h``,
  REVERSE Induct \\ SIMP_TAC std_ss [lisp_ref_def]
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ NTAC 3 STRIP_TAC  
  \\ `?m n mi ni. h ' q = (m,n,mi,ni)` by METIS_TAC [PAIR]   
  \\ ASM_SIMP_TAC std_ss [GSYM AND_IMP_INTRO,FDOM_DOMSUB,IN_DELETE,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM]
  \\ Cases_on `t = q` \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC THENL [
    REVERSE (Cases_on `m = t`)
    THEN1 (METIS_TAC [lisp_ref_reachable_step])
    \\ SIMP_TAC std_ss [lisp_ref_reachable_def]
    \\ Q.EXISTS_TAC `[]`  
    \\ ASM_SIMP_TAC std_ss [lisp_ref_PATH_def,APPEND,LET_DEF]
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
    \\ METIS_TAC [],
    REVERSE (Cases_on `n = t`)
    THEN1 (METIS_TAC [lisp_ref_reachable_step])
    \\ SIMP_TAC std_ss [lisp_ref_reachable_def]
    \\ Q.EXISTS_TAC `[]`  
    \\ ASM_SIMP_TAC std_ss [lisp_ref_PATH_def,APPEND,LET_DEF]
    \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
    \\ METIS_TAC []]);

val lisp_ref_LESS = prove(  
  ``lisp_ref_reachable m n h /\ lisp_ref x (m,mi) h sym ==>
    ?y ni. lisp_ref y (n,ni) h sym /\ LSIZE y < LSIZE x``,
  REWRITE_TAC [lisp_ref_reachable_def]
  \\ STRIP_TAC \\ REPEAT (POP_ASSUM MP_TAC)
  \\ Q.SPEC_TAC (`mi`,`mi`) \\ Q.SPEC_TAC (`ni`,`ni`) \\ Q.SPEC_TAC (`m`,`m`)
  \\ Q.SPEC_TAC (`n`,`n`) \\ Q.SPEC_TAC (`h`,`hh`) \\ Q.SPEC_TAC (`x`,`x`)
  \\ Q.SPEC_TAC (`y`,`y`) \\ Induct_on `xs` THENL [
    SIMP_TAC std_ss [lisp_ref_PATH_def,APPEND]
    \\ NTAC 5 STRIP_TAC
    \\ `?q n mi ni. hh ' m = (q,n,mi,ni)` by METIS_TAC [PAIR]   
    \\ Cases_on `x` \\ ASM_SIMP_TAC std_ss [LET_DEF,lisp_ref_def,LSIZE_def]
    \\ METIS_TAC [DECIDE ``n < SUC (n + m) /\ m < SUC (n+m)``],
    REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ FULL_SIMP_TAC std_ss [lisp_ref_PATH_def,APPEND_ASSOC,APPEND]
    \\ `?q n mi ni. hh ' m = (q,n,mi,ni)` by METIS_TAC [PAIR]   
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [lisp_ref_def,LET_DEF]
    \\ Q.PAT_ASSUM `qq = h` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ RES_TAC
    \\ Q.EXISTS_TAC `y'` \\ Q.EXISTS_TAC `ni''`
    \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC]);

val lisp_ref_11 = prove(
  ``!x y m mi ni h.
      lisp_ref x (m,mi) h sym /\ lisp_ref y (m,ni) h sym ==> 
      (LSIZE x = LSIZE y)``,
  REVERSE Induct 
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO, lisp_ref_def, LSIZE_def]
  THEN1
   (STRIP_TAC \\ Cases \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def,LSIZE_def])
  THEN1
   (STRIP_TAC \\ Cases \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def,LSIZE_def])
  \\ NTAC 4 STRIP_TAC \\ Cases_on `y`
  \\ `?q n mi ni. h ' m = (q,n,mi,ni)` by METIS_TAC [PAIR]   
  \\ ASM_SIMP_TAC std_ss [LET_DEF,lisp_ref_def,LSIZE_def]
  \\ METIS_TAC []);   

val NOT_lisp_ref = prove(
  ``!m mi h x. lisp_ref_reachable m m h ==> ~lisp_ref x (m,mi) h sym``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_ref_LESS
  \\ IMP_RES_TAC lisp_ref_11 \\ DECIDE_TAC);

val LDEPTH_LE_CARD_LEMMA = prove( 
  ``!x m mi h q. lisp_ref x (m,mi) (h \\ q) sym /\ ~(0 IN FDOM h) ==>
      ~((q,t1,t2,q1,q2) IN reachables [m] (ch_set h))``,
  REVERSE Induct
  \\ SIMP_TAC std_ss [lisp_ref_def,reachables_EQ_EMPTY,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO,FDOM_DOMSUB,IN_DELETE]
  \\ NTAC 3 STRIP_TAC
  \\ `?t1 t2 q1 q2. h ' m = (t1,t2,q1,q2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM,LET_DEF]
  \\ NTAC 5 STRIP_TAC
  \\ IMP_RES_TAC reachables_NEXT
  \\ ASM_SIMP_TAC std_ss [IN_UNION,IN_INSERT,NOT_IN_EMPTY,PAIR_EQ] 
  \\ METIS_TAC []);

val CARD_UNION_LESS_EQ = prove(
  ``!x y:'a set. FINITE x /\ FINITE y ==> CARD x <= CARD (x UNION y)``,
  REPEAT STRIP_TAC \\ (MATCH_MP_TAC o RW [AND_IMP_INTRO] o 
    DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) CARD_SUBSET  
  \\ ASM_SIMP_TAC std_ss [FINITE_UNION,SUBSET_UNION]);

val LDEPTH_LE_CARD = prove( 
  ``!x q r h. lisp_ref x (q,r) h sym /\ ~(0 IN FDOM h) ==> 
              LDEPTH x <= CARD (reachables [q] (ch_set h))``,
  Induct \\ SIMP_TAC std_ss [LDEPTH_def,lisp_ref_def] \\ STRIP_TAC \\ STRIP_TAC
  \\ `?m n mi ni. h ' q = (m,n,mi,ni)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ RES_TAC 
  \\ REVERSE (`lisp_ref x (m,mi) (h \\ q) sym /\ lisp_ref x' (n,ni) (h \\ q) sym` by ALL_TAC) 
  THENL [
    IMP_RES_TAC reachables_NEXT \\ ASM_SIMP_TAC std_ss []
    \\ REWRITE_TAC [GSYM UNION_ASSOC]
    \\ ASM_SIMP_TAC std_ss [GSYM INSERT_SING_UNION, CARD_INSERT,
         FINITE_reachables,FINITE_UNION,IN_UNION] 
    \\ IMP_RES_TAC LDEPTH_LE_CARD_LEMMA
    \\ ASM_REWRITE_TAC [DECIDE ``SUC n <= SUC m = n <= m:num``]
    \\ `FINITE (reachables [m] (ch_set h))` by METIS_TAC [FINITE_reachables]
    \\ `FINITE (reachables [n] (ch_set h))` by METIS_TAC [FINITE_reachables]
    \\ Q.ABBREV_TAC `sx = reachables [m] (ch_set h)`
    \\ Q.ABBREV_TAC `sy = reachables [n] (ch_set h)`
    \\ SIMP_TAC std_ss [MAX_DEF]
    \\ METIS_TAC [CARD_UNION_LESS_EQ,LESS_EQ_TRANS,UNION_COMM],
    CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `lisp_ref (Dot x x') (q,mi) h sym` by FULL_SIMP_TAC std_ss [lisp_ref_def,LET_DEF]
    THENL [
      REVERSE (`lisp_ref_reachable q q h` by ALL_TAC)
      THEN1 (METIS_TAC [NOT_lisp_ref])
      \\ REVERSE (Cases_on `m = q`) 
      THEN1 (METIS_TAC [lisp_ref_reachable_intro,lisp_ref_reachable_step])
      \\ SIMP_TAC std_ss [lisp_ref_reachable_def] \\ Q.EXISTS_TAC `[]`
      \\ ASM_SIMP_TAC std_ss [APPEND,lisp_ref_PATH_def,LET_DEF],    
      REVERSE (`lisp_ref_reachable q q h` by ALL_TAC)
      THEN1 METIS_TAC [NOT_lisp_ref]
      \\ REVERSE (Cases_on `n = q`) 
      THEN1 (METIS_TAC [lisp_ref_reachable_intro,lisp_ref_reachable_step])
      \\ SIMP_TAC std_ss [lisp_ref_reachable_def] \\ Q.EXISTS_TAC `[]`
      \\ ASM_SIMP_TAC std_ss [APPEND,lisp_ref_PATH_def,LET_DEF]]]); 

val oks_def = Define `
  oks (i,j,m) = !k. if RANGE(i,j)k then ?x. m k = DATA x else m k = EMP`; 

val CARD_abstract_LEMMA = prove(
  ``!b j i m. oks (i,i+j,m) ==> 
      FINITE (abstract(b,m)) /\ CARD (abstract(b,m)) <= j``,
  STRIP_TAC \\ Induct THENL [
    REPEAT STRIP_TAC
    \\ `!i k. ~RANGE (i,i) k` by (SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [oks_def]
    \\ `abstract(b,m) = {}` by ALL_TAC   
    \\ ASM_SIMP_TAC std_ss [FINITE_EMPTY,CARD_EMPTY]
    \\ SIMP_TAC std_ss [abstract_def,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC std_ss [heap_type_distinct]
    \\ Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'` 
    \\ SIMP_TAC std_ss [],
    NTAC 3 STRIP_TAC   
    \\ `oks (i,i+j,\k. if i+j = k then EMP else m k)` by ALL_TAC
    THENL [  
      FULL_SIMP_TAC std_ss [oks_def] \\ STRIP_TAC     
      \\ Cases_on `RANGE (i,i+j)k`
      \\ ASM_SIMP_TAC std_ss [] THENL [      
        FULL_SIMP_TAC std_ss [RANGE_def]
        \\ `~(i+j = k) /\ k < i + SUC j` by DECIDE_TAC       
        \\ METIS_TAC [],
        Cases_on `i + j = k` \\ ASM_SIMP_TAC std_ss []
        \\ `~(RANGE(i,i+SUC j)k)` by 
           (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
        \\ METIS_TAC []],
      Q.ABBREV_TAC `m2 = \k. if i+j = k then EMP else m k`
      \\ `?y2 z2 d2. m (i+j) = DATA (y2,z2,d2)` by        
        (FULL_SIMP_TAC std_ss [oks_def,RANGE_def]
        \\ METIS_TAC [DECIDE ``i <= i+j /\ i + j < i + SUC j``,PAIR])
      \\ `abstract(b,m) = (b (i+j),b y2, b z2, d2) INSERT abstract(b,m2)` by ALL_TAC 
      THENL [
        FULL_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INSERT,abstract_def]
        \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [
          Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'`
          \\ FULL_SIMP_TAC std_ss []       
          \\ Cases_on `q = i + j`
          THEN1 FULL_SIMP_TAC std_ss [heap_type_11]
          \\ DISJ2_TAC
          \\ Q.EXISTS_TAC `(q,q',q'',r)`
          \\ Q.UNABBREV_TAC `m2`
          \\ ASM_SIMP_TAC std_ss [],
          Q.EXISTS_TAC `(i+j,y2,z2,d2)`
          \\ ASM_SIMP_TAC std_ss [],
          Cases_on `x'` \\ Cases_on `r` \\ Cases_on `r'`
          \\ Q.UNABBREV_TAC `m2`
          \\ Cases_on `q = i + j`
          \\ Q.EXISTS_TAC `(q,q',q'',r)`
          \\ FULL_SIMP_TAC std_ss [heap_type_distinct]],          
        RES_TAC
        \\ ASM_SIMP_TAC std_ss [FINITE_INSERT,CARD_INSERT]
        \\ Cases_on `(b (i + j),b y2,b z2,d2) IN abstract (b,m2)`
        \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC]]]);

val CARD_abstract = prove(
  ``ok_state (i,e,r,l,u,m) ==>
    FINITE (abstract(b:(num->num),m)) /\ CARD (abstract(b:(num->num),m)) <= l``,
  STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF]
  \\ Q.ABBREV_TAC `a = if u then 1 + l else 1`
  \\ `oks(a,a+(i-a),m)` by ALL_TAC THENL [
    `a + (i - a) = i` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [oks_def,IN_DEF]
    \\ METIS_TAC [],
    STRIP_TAC THEN1 (METIS_TAC [CARD_abstract_LEMMA])
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `i-a`
    \\ STRIP_TAC THEN1 (METIS_TAC [CARD_abstract_LEMMA])
    \\ DECIDE_TAC]);      

val MEM_reachables = prove(
  ``!r m h. MEM m r ==>
            reachables [m] (ch_set h) SUBSET reachables r (ch_set h)``,
  Induct \\ REWRITE_TAC [MEM] \\ REPEAT STRIP_TAC THENL [
    ONCE_REWRITE_TAC [reachables_THM]
    \\ ASM_SIMP_TAC std_ss[UNION_SUBSET,SUBSET_UNION] 
    \\ ONCE_REWRITE_TAC [reachables_THM]
    \\ SIMP_TAC std_ss [EMPTY_SUBSET],
    CONV_TAC ((RAND_CONV) (ONCE_REWRITE_CONV [reachables_THM]))
    \\ RES_TAC \\ METIS_TAC [SUBSET_DEF,IN_UNION]]);

val ch_inv_LDEPTH_LEMMA = prove(
  ``ch_inv (r,h,l) (i,e,c,l',u,m) /\ lisp_ref x (q,gw) h sym /\ MEM q r ==>
    LDEPTH x <= l``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ch_inv_def,ok_abs_def]
  \\ IMP_RES_TAC (GEN_ALL CARD_abstract)
  \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (ASSUME_TAC o SPEC_ALL))
  \\ `reachables [q] (ch_set h) SUBSET abstract(b,m)` by 
        METIS_TAC [MEM_reachables,CARD_SUBSET,SUBSET_TRANS]
  \\ `CARD (reachables [q] (ch_set h)) <= l` by 
        METIS_TAC [CARD_SUBSET,LESS_EQ_TRANS]
  \\ METIS_TAC [LDEPTH_LE_CARD,LESS_EQ_TRANS]);

val lisp_inv_LDEPTH = store_thm("lisp_inv_LDEPTH",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,df,f,s,rest) ==>
    LDEPTH x1 <= limit /\ LDEPTH x2 <= limit /\ LDEPTH x3 <= limit /\ 
    LDEPTH x4 <= limit /\ LDEPTH x5 <= limit /\ LDEPTH x6 <= limit``,
  REWRITE_TAC [lisp_inv_def,ch_arm_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `v1` \\ Cases_on `v2` \\ Cases_on `v3` 
  \\ Cases_on `v4` \\ Cases_on `v5` \\ Cases_on `v6` 
  \\ FULL_SIMP_TAC std_ss [MAP]
  \\ METIS_TAC [ch_inv_LDEPTH_LEMMA,MEM]);


val _ = export_theory();
