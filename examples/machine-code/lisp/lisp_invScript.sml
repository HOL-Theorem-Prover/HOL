open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_inv";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory stringTheory addressTheory;

open lisp_gcTheory cheney_gcTheory cheney_allocTheory;
open lisp_typeTheory divideTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(* --- definitions --- *)


(* s-expression assertion *)

val lisp_x_def = Define `
  (lisp_x (Val k) (a,dm,m) sym <=> (a = n2w (k * 4 + 2)) /\ k < 2 ** 30) /\
  (lisp_x (Sym s) (a,dm,m) sym <=>
    ((a - 3w) && 3w = 0w) /\ (a - 3w,s) IN sym) /\
  (lisp_x (Dot x y) (a,dm,m) sym <=> a IN dm /\ ALIGNED a /\
    lisp_x x (m a,dm,m) sym /\ lisp_x y (m (a+4w),dm,m) sym)`;

(* symbol table inv *)

val string_mem_def = Define `
  (string_mem "" (a,m:word32->word8,df) = T) /\
  (string_mem (STRING c s) (a,m,df) <=> a IN df /\
      (m a = n2w (ORD c)) /\ string_mem s (a+1w,m,df))`;

val string_mem_dom_def = Define `
  (string_mem_dom "" (a:word32) = {}) /\
  (string_mem_dom (STRING c s) a = a INSERT string_mem_dom s (a+1w))`;

val symbol_table_def = Define `
  (symbol_table [] x (a,dm,m,dg,g) <=> (m a = 0w) /\ a IN dm /\ (x = {})) /\
  (symbol_table (s::xs) x (a,dm,m,dg,g) <=>
    s <> "" /\ string_mem s (a+8w,g,dg) /\
    (m a = n2w (LENGTH s)) /\ {a; a+4w} SUBSET dm /\ ((a,s) IN x) /\
      let a' = a + n2w (8 + (LENGTH s + 3) DIV 4 * 4) in
        a <+ a' /\ (m (a+4w) = a') /\
        symbol_table xs (x DELETE (a,s)) (a',dm,m,dg,g))`;

val symbol_table_dom_def = Define `
  (symbol_table_dom [] (a,dm,dg) <=> ALIGNED a /\ a IN dm) /\
  (symbol_table_dom (s::xs) (a,dm,dg) <=> ~(s = "") /\
    string_mem_dom s (a+8w) SUBSET dg /\ {a; a+4w} SUBSET dm /\
    w2n a + 8 + LENGTH s + 3 < 2**32 /\
    a <+ a + n2w (8 + (LENGTH s + 3) DIV 4 * 4) /\
      symbol_table_dom xs (a + n2w (8 + (LENGTH s + 3) DIV 4 * 4),dm,dg))`;

val builtin_symbols_def = Define `
  builtin_symbols =
    ["nil"; "t"; "quote"; "+"; "-"; "*"; "div"; "mod"; "<"; "car"; "cdr";
     "cons"; "equal"; "cond"; "atomp"; "consp"; "numberp"; "symbolp"; "lambda"]`;

val builtin_symbols_set_def = Define `
  builtin_symbols_set (w:word32) =
     {(w,"nil"); (w + 12w,"t"); (w + 24w,"quote"); (w + 40w,"+");
      (w + 52w,"-"); (w + 64w,"*"); (w + 76w,"div"); (w + 88w,"mod");
      (w + 100w,"<"); (w + 112w,"car"); (w + 124w,"cdr");
      (w + 136w,"cons"); (w + 148w,"equal"); (w + 164w,"cond");
      (w + 176w,"atomp"); (w + 192w,"consp"); (w + 208w,"numberp");
      (w + 224w,"symbolp"); (w + 240w,"lambda")}`;

Definition set_add_def:
  set_add a x (b,s) <=> (b - (a:'a word), s) IN x
End

val lisp_symbol_table_def = Define `
  lisp_symbol_table x (a,dm,m,dg,g) =
    ?symbols.
      symbol_table (builtin_symbols ++ symbols) (set_add a x) (a,dm,m,dg,g) /\
      ALL_DISTINCT (builtin_symbols ++ symbols)`;

(* main heap inv *)

val lisp_inv_def = Define `
  lisp_inv (t1,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,a,dm,m,sym,rest) =
    ?i u.
      let v = if u then 1 + l else 1 in
      let d = ch_active_set (a,v,i) in
        32 <= w2n a /\ w2n a + 2 * 8 * l + 20 < 2 ** 32 /\ l <> 0 /\
        (m a = a + n2w (8 * i)) /\ ALIGNED a /\ v <= i /\
        i <= v + l /\ (m (a + 4w) = a + n2w (8 * (v + l))) /\
        (m (a - 28w) = if u then 0w else 1w) /\
        (m (a - 32w) = n2w (8 * l)) /\ (dm = ref_set a (l + l + 1)) /\
        lisp_symbol_table sym (a + 16w * n2w l + 24w,rest) /\
        lisp_x t1 (w1,d,m) sym /\ lisp_x t2 (w2,d,m) sym /\
        lisp_x t3 (w3,d,m) sym /\ lisp_x t4 (w4,d,m) sym /\
        lisp_x t5 (w5,d,m) sym /\ lisp_x t6 (w6,d,m) sym /\
        !w. w IN d ==> ok_data (m w) d /\ ok_data (m (w + 4w)) d`;


(* --- theorems --- *)

val lisp_x_word_tree = prove(
  ``!x a dm m sym.
      lisp_x x (a,dm,m) sym ==>
      ?t. word_tree t (a,m) dm /\ (LSIZE x = XSIZE t) /\ (LDEPTH x = XDEPTH t) /\
          !a2 m2 dm2. word_tree t (a2,m2) dm2 ==> lisp_x x (a2,dm2,m2) sym``,
  REVERSE Induct \\ REWRITE_TAC [lisp_x_def,ALIGNED_INTRO]
  \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `XSym (ADDR30 a)`
    \\ REWRITE_TAC [word_tree_def,XSIZE_def,LSIZE_def,XDEPTH_def,LDEPTH_def]
    \\ STRIP_ASSUME_TAC (Q.SPEC `a` EXISTS_ADDR32)
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma4,ALIGNED_ADDR32,
          ALIGNED_ADD_EQ,ALIGNED_n2w,ADDR30_ADDR32])
  THEN1
   (Q.EXISTS_TAC `XVal (n2w n)`
    \\ REWRITE_TAC [word_tree_def,XSIZE_def,LSIZE_def,XDEPTH_def,LDEPTH_def]
    \\ ASM_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w,AC MULT_ASSOC MULT_COMM])
  \\ Q.PAT_X_ASSUM `!a. bbb` IMP_RES_TAC
  \\ Q.PAT_X_ASSUM `!a dm m sym. bbb` IMP_RES_TAC
  \\ Q.EXISTS_TAC `XDot t' t`
  \\ ASM_SIMP_TAC std_ss [word_tree_def,XSIZE_def,LSIZE_def,XDEPTH_def,LDEPTH_def]);


(* cons *)

val lisp_inv_cons = store_thm("lisp_inv_cons",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs,sym,rest) ==>
    SUM_LSIZE [x1;x2;x3;x4;x5;x6] < limit ==>
    ?w1 w2 w3 w4 w5 w6 a' x' xs'.
    (arm_alloc (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) /\
    lisp_inv (Dot x1 x2,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a',x',xs',sym,rest) /\
    arm_alloc_pre (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) /\ (a' = a) /\ (x' = x)``,
  SIMP_TAC std_ss [lisp_inv_def,SUM_LSIZE_def,ADD_ASSOC,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `s = ch_active_set (a,if u then 1 + limit else 1,i)`
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x1`,`ww1`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x2`,`ww2`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x3`,`ww3`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x4`,`ww4`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x5`,`ww5`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`x6`,`ww6`,`s`,`xs`,`sym`]) lisp_x_word_tree
  \\ Q.ABBREV_TAC `t1 = t`
  \\ Q.ABBREV_TAC `t2 = t'`
  \\ Q.ABBREV_TAC `t3 = t''`
  \\ Q.ABBREV_TAC `t4 = t'''`
  \\ Q.ABBREV_TAC `t5 = t''''`
  \\ Q.ABBREV_TAC `t6 = t'''''`
  \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
  \\ `?w1 w2 w3 w4 w5 w6 a' x' xs'.
       (arm_alloc (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs) =
        (w1,w2,w3,w4,w5,w6,a',x',xs'))` by METIS_TAC [PAIR]
  \\ Q.ABBREV_TAC `v = if u then 1 + limit else 1`
  \\ `ch_tree (t1,t2,t3,t4,t5,t6,limit) (ww1,ww2,ww3,ww4,ww5,ww6,a,x,xs,a + n2w (8 * v),i-v)` by
    (FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]
     \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ Q.UNABBREV_TAC `v`
     \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ch_tree_alloc
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [ch_tree_def,LET_DEF]
  \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `a' = a` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ Q.EXISTS_TAC `i'` \\ Q.EXISTS_TAC `u'`
  \\ FULL_SIMP_TAC std_ss [word_tree_def,lisp_x_def] \\ METIS_TAC []);


(* swap *)

val lisp_inv_swap1 = store_thm("lisp_inv_swap1",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_swap2 = store_thm("lisp_inv_swap2",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x2,x1,x3,x4,x5,x6,limit) (w2,w1,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_swap3 = store_thm("lisp_inv_swap3",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x3,x2,x1,x4,x5,x6,limit) (w3,w2,w1,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_swap4 = store_thm("lisp_inv_swap4",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x4,x2,x3,x1,x5,x6,limit) (w4,w2,w3,w1,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_swap5 = store_thm("lisp_inv_swap5",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x5,x2,x3,x4,x1,x6,limit) (w5,w2,w3,w4,w1,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_swap6 = store_thm("lisp_inv_swap6",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (x6,x2,x3,x4,x5,x1,limit) (w6,w2,w3,w4,w5,w1,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

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
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss []);

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

val lisp_inv_Val = store_thm("lisp_inv_Val",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    !n. n < 2 ** 30 ==>
        lisp_inv (Val n,x2,x3,x4,x5,x6,limit)
                 (n2w (n * 4 + 2),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u` \\ ASM_SIMP_TAC std_ss [lisp_x_def]);


(* car and cdr *)

val lisp_inv_car_cdr = store_thm("lisp_inv_car_cdr",
  ``lisp_inv (Dot y1 y2,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    (w1 && 3w = 0w) /\ w1 IN x /\ w1 + 4w IN x /\
    lisp_inv (y1,x2,x3,x4,x5,x6,limit) (xs w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) /\
    lisp_inv (y2,x2,x3,x4,x5,x6,limit) (xs (w1 + 4w),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,ALIGNED_INTRO]
  \\ REPEAT (Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`)
  \\ ASM_SIMP_TAC std_ss [lisp_x_def]
  \\ FULL_SIMP_TAC std_ss [ref_set_def,ch_active_set_def,IN_UNION,GSPECIFICATION]
  \\ DISJ1_TAC \\ REWRITE_TAC [word_mul_n2w,word_add_n2w,GSYM WORD_ADD_ASSOC] THENL [
    Q.EXISTS_TAC `2 * j + 1`
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC,
    Q.EXISTS_TAC `2 * j`
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC]);

val lisp_inv_car_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> isDot x1 ==>
    lisp_inv (CAR x1,x2,x3,x4,x5,x6,limit) (xs w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  METIS_TAC [lisp_inv_car_cdr,isDot_thm,CAR_def]);

val lisp_inv_cdr_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==> isDot x1 ==>
    lisp_inv (CDR x1,x2,x3,x4,x5,x6,limit) (xs (w1 + 4w),w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  METIS_TAC [lisp_inv_car_cdr,isDot_thm,CDR_def]);

val lisp_inv_address_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    isDot x1 ==> (w1 && 3w = 0w) /\ w1 IN x /\ w1 + 4w IN x``,
  METIS_TAC [lisp_inv_car_cdr,isDot_thm]);

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

val n2w_and_1_lemma = prove(
  ``!w:word32. ((2w * w) && 1w = 0w) /\ ~((2w * w + 1w) && 1w = 0w)``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,
       n2w_and_1,n2w_11,RW1[MULT_COMM]MOD_EQ_0,RW1[MULT_COMM]MOD_MULT]);

val lisp_inv_test_lemma = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    ((w1 && 3w = 0w) = isDot x1) /\ ((w1 && 1w = 0w) = ~isSym x1)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isDot_def,isSym_def,
       lisp_x_def,ALIGNED_INTRO, GSYM word_add_n2w]
  \\ REWRITE_TAC [GSYM (RW1 [MULT_COMM] ADDR32_n2w)]
  \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w]
  THEN1 (IMP_RES_TAC NOT_ALIGNED \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD])
  \\ FULL_SIMP_TAC std_ss [ALIGNED_and_1]
  \\ FULL_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w]
  \\ REWRITE_TAC [DECIDE ``4 * n + 2 = 2 * (2 * n + 1):num``]
  \\ REWRITE_TAC [GSYM word_mul_n2w,n2w_and_1_lemma]
  \\ STRIP_ASSUME_TAC (Q.SPEC `w1` EXISTS_ADDR32)
  \\ FULL_SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_ADD_EQ,
       word_arith_lemma4,ALIGNED_n2w]
  \\ Q.SPEC_TAC (`a'`,`q`) \\ Cases_word
  \\ REWRITE_TAC [ADDR32_n2w,word_add_n2w,DECIDE ``4*n+3 = 2*(2*n+1)+1:num``]
  \\ REWRITE_TAC [GSYM word_mul_n2w,GSYM word_add_n2w,n2w_and_1_lemma]);

val lisp_inv_test = save_thm("lisp_inv_test",let
  val thms = [MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap1),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap2),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap3),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap4),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap5),
              MATCH_MP lisp_inv_test_lemma (UNDISCH lisp_inv_swap6)]
  in RW [] (DISCH_ALL (foldr (uncurry CONJ) TRUTH thms)) end);


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

val symbol_table_MEM = store_thm("symbol_table_MEM",
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
  ``(isVal x1 /\ isVal x2) \/ (isSym x1 /\ isSym x2) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    ((x1 = x2) = (w1 = w2))``,
  STRIP_TAC THEN1
   (`?a1 a2. (x1 = Val a1) /\ (x2 = Val a2)` by
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isVal_def,SExp_11])
    \\ ASM_SIMP_TAC std_ss [LISP_LESS_def,lisp_inv_def,LET_DEF]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [lisp_x_def,GSYM word_add_n2w,ADDR32_11,
         WORD_EQ_ADD_RCANCEL, GSYM (RW1 [MULT_COMM] ADDR32_n2w)]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,SExp_11])
  \\ `?a1 a2. (x1 = Sym a1) /\ (x2 = Sym a2)` by
    (Cases_on `x1` \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isSym_def,SExp_11])
  \\ ASM_SIMP_TAC std_ss [SExp_11]
  \\ `?dg dm g m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,lisp_symbol_table_def,
       LET_DEF,lisp_x_def] \\ STRIP_TAC
  \\ Q.ABBREV_TAC `ww = a + 16w * n2w limit + 24w`
  \\ `((w1 - 3w) + ww,a1) IN (set_add ww s)` by
        FULL_SIMP_TAC std_ss [set_add_def,set_add_def,IN_DEF,WORD_ADD_SUB]
  \\ `((w2 - 3w) + ww,a2) IN (set_add ww s)` by
        FULL_SIMP_TAC std_ss [set_add_def,set_add_def,IN_DEF,WORD_ADD_SUB]
  \\ IMP_RES_TAC (GSYM symbol_table_eq)
  \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL]
  \\ ONCE_REWRITE_TAC [Q.SPECL [`x`,`3w`,`y`] (GSYM WORD_EQ_ADD_RCANCEL)]
  \\ REWRITE_TAC [WORD_SUB_ADD]
  \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL]);

val lisp_inv_eq = store_thm("lisp_inv_eq",
  ``~isDot x1 \/ ~isDot x2 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    ((x1 = x2) = (w1 = w2))``,
  STRIP_TAC THENL [
    Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isDot_def]
    \\ Cases_on `x2` \\ STRIP_TAC \\ SIMP_TAC std_ss [SExp_distinct]
    \\ IMP_RES_TAC lisp_inv_test
    \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,isDot_def]
    \\ METIS_TAC [lisp_inv_eq_lemma,isVal_def,isSym_def],
    Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isDot_def]
    \\ Cases_on `x1` \\ STRIP_TAC \\ SIMP_TAC std_ss [SExp_distinct]
    \\ IMP_RES_TAC lisp_inv_test
    \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,isDot_def]
    \\ METIS_TAC [lisp_inv_eq_lemma,isVal_def,isSym_def]]);

val lisp_inv_eq_0 = store_thm("lisp_inv_eq_0",
  ``!n. n < 2 ** 30 ==>
        lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
        ((x1 = Val n) = (w1 = n2w (n * 4 + 2)))``,
  REPEAT STRIP_TAC
  \\ `lisp_inv (x1,x1,x3,x4,x5,x6,limit) (w1,w1,w3,w4,w5,w6,a,x,xs,s,rest)` by
      METIS_TAC [lisp_inv_move]
  \\ (IMP_RES_TAC o DISCH ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)`` o
      UNDISCH o Q.SPEC `n` o UNDISCH) lisp_inv_Val
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] lisp_inv_eq)
  \\ REWRITE_TAC [isDot_def]
  \\ (IMP_RES_TAC o DISCH ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest)`` o
      MATCH_MP lisp_inv_swap2 o UNDISCH o Q.SPEC `n` o UNDISCH) lisp_inv_Val);


(* symbol test *)

val builti_symbols_thm = store_thm("builti_symbols_thm",
  ``lisp_symbol_table s (sa,rest) ==>
    (ADDR32 0w,"nil") IN s /\
    (ADDR32 3w,"t") IN s /\
    (ADDR32 6w,"quote") IN s /\
    (ADDR32 10w,"+") IN s /\
    (ADDR32 13w,"-") IN s /\
    (ADDR32 16w,"*") IN s /\
    (ADDR32 19w,"div") IN s /\
    (ADDR32 22w,"mod") IN s /\
    (ADDR32 25w,"<") IN s /\
    (ADDR32 28w,"car") IN s /\
    (ADDR32 31w,"cdr") IN s /\
    (ADDR32 34w,"cons") IN s /\
    (ADDR32 37w,"equal") IN s /\
    (ADDR32 41w,"cond") IN s /\
    (ADDR32 44w,"atomp") IN s /\
    (ADDR32 48w,"consp") IN s /\
    (ADDR32 52w,"numberp") IN s /\
    (ADDR32 56w,"symbolp") IN s /\
    (ADDR32 60w,"lambda") IN s``,
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
  \\ NTAC 30 (SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ ONCE_REWRITE_TAC [symbol_table_def]
  \\ SIMP_TAC std_ss [LENGTH,LET_DEF,IN_DELETE]
  \\ SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB2,ADDR32_n2w]))

val lisp_symbol_table_11 = store_thm("lisp_symbol_table_11",
  ``lisp_symbol_table s (sa,rest) /\
    (x1,s1) IN s /\ (x2,s2) IN s ==>
    ((x1 = x2) = (s1 = s2))``,
  `?dg g dm m. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [lisp_symbol_table_def]
  \\ REPEAT STRIP_TAC
  \\ `(x1 + sa,s1) IN (set_add sa s)` by
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ `(x2 + sa,s2) IN (set_add sa s)` by
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC symbol_table_eq
  \\ METIS_TAC [WORD_EQ_ADD_RCANCEL,ADDR32_11]);

val lisp_symbol_table_11_ADDR32 = prove(
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
    ((w1 = ADDR32 10w + 3w) = (x1 = Sym "+")) /\
    ((w1 = ADDR32 13w + 3w) = (x1 = Sym "-")) /\
    ((w1 = ADDR32 16w + 3w) = (x1 = Sym "*")) /\
    ((w1 = ADDR32 19w + 3w) = (x1 = Sym "div")) /\
    ((w1 = ADDR32 22w + 3w) = (x1 = Sym "mod")) /\
    ((w1 = ADDR32 25w + 3w) = (x1 = Sym "<")) /\
    ((w1 = ADDR32 28w + 3w) = (x1 = Sym "car")) /\
    ((w1 = ADDR32 31w + 3w) = (x1 = Sym "cdr")) /\
    ((w1 = ADDR32 34w + 3w) = (x1 = Sym "cons")) /\
    ((w1 = ADDR32 37w + 3w) = (x1 = Sym "equal")) /\
    ((w1 = ADDR32 41w + 3w) = (x1 = Sym "cond")) /\
    ((w1 = ADDR32 44w + 3w) = (x1 = Sym "atomp")) /\
    ((w1 = ADDR32 48w + 3w) = (x1 = Sym "consp")) /\
    ((w1 = ADDR32 52w + 3w) = (x1 = Sym "numberp")) /\
    ((w1 = ADDR32 56w + 3w) = (x1 = Sym "symbolp")) /\
    ((w1 = ADDR32 60w + 3w) = (x1 = Sym "lambda"))``,
  STRIP_TAC \\ REVERSE (Cases_on `isSym x1 `) THEN1
   (`w1 && 1w = 0w` by METIS_TAC [lisp_inv_test]
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss
         [isDot_def,isVal_def,isSym_def,SExp_distinct]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w,n2w_and_1]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ Q.ABBREV_TAC `sa = a + 16w * n2w limit + 24w`
  \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_x_def,SExp_11]
  \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_x_def,SExp_11]
  \\ STRIP_ASSUME_TAC (Q.SPEC `w1`EXISTS_ADDR32)
  \\ FULL_SIMP_TAC std_ss [ALIGNED_INTRO,word_arith_lemma4,
       ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w]
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11]
  \\ Q.PAT_X_ASSUM `xx IN s` MP_TAC
  \\ Q.PAT_X_ASSUM `lisp_symbol_table sss ssss` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC
  \\ IMP_RES_TAC builti_symbols_thm
  \\ REPEAT STRIP_TAC
  \\ (MATCH_MP_TAC lisp_symbol_table_11_ADDR32
      \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]));

val lisp_inv_builtin = save_thm("lisp_inv_builtin",
  SIMP_RULE std_ss [ADDR32_n2w,word_add_n2w]
  lisp_inv_test_builtin_lemma);

val lisp_inv_nil = store_thm("lisp_inv_nil",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (Sym "nil",x2,x3,x4,x5,x6,limit) (3w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ ASM_SIMP_TAC std_ss [lisp_x_def,ALIGNED_INTRO,word_arith_lemma2,
       ALIGNED_n2w] \\ IMP_RES_TAC builti_symbols_thm
  \\ FULL_SIMP_TAC std_ss [ADDR32_n2w]);

val lisp_inv_t = store_thm("lisp_inv_t",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (Sym "t",x2,x3,x4,x5,x6,limit) (15w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ ASM_SIMP_TAC std_ss [lisp_x_def,ALIGNED_INTRO,word_arith_lemma2,
       ALIGNED_n2w] \\ IMP_RES_TAC builti_symbols_thm
  \\ FULL_SIMP_TAC std_ss [ADDR32_n2w]);

val lisp_inv_quote = store_thm("lisp_inv_quote",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (Sym "quote",x2,x3,x4,x5,x6,limit) (27w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ ASM_SIMP_TAC std_ss [lisp_x_def,ALIGNED_INTRO,word_arith_lemma2,
       ALIGNED_n2w] \\ IMP_RES_TAC builti_symbols_thm
  \\ FULL_SIMP_TAC std_ss [ADDR32_n2w]);


(* basic arithmetic *)

val lisp_inv_read_Val = prove(
  ``lisp_inv (Val n,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    n < 2 ** 30 /\ (w1 = n2w (4 * n + 2))``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_x_def,AC MULT_COMM MULT_ASSOC]);

val isVal_TAC =
  REWRITE_TAC [GSYM AND_IMP_INTRO,isVal_thm]
  \\ REPEAT (STRIP_TAC \\ ASM_SIMP_TAC std_ss [getVal_def])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC lisp_inv_read_Val
  \\ IMP_RES_TAC (DISCH_ALL (MATCH_MP lisp_inv_read_Val
        (UNDISCH (Q.INST [`x2`|->`Val n`] lisp_inv_swap2))))

val lisp_inv_ADD = store_thm("lisp_inv_ADD",
  ``isVal x1 /\ isVal x2 /\ getVal x1 + getVal x2 < 2**30 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_ADD x1 x2,x2,x3,x4,x5,x6,limit) (w1+w2-2w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  isVal_TAC
  \\ ASM_REWRITE_TAC [LISP_ADD_def,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ ASM_REWRITE_TAC [word_add_n2w,DECIDE ``4*m+2+4*n = (m+n) * 4 + 2:num``]
  \\ (MATCH_MP_TAC o RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH) lisp_inv_Val
  \\ SIMP_TAC std_ss [] \\ METIS_TAC []);

val lisp_inv_ADD1 = store_thm("lisp_inv_ADD1",
  ``isVal x1 /\ getVal x1 + 1 < 2**30 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_ADD x1 (Val 1),x2,x3,x4,x5,x6,limit) (w1 + 4w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  isVal_TAC
  \\ ASM_REWRITE_TAC [LISP_ADD_def,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ ASM_REWRITE_TAC [word_add_n2w,DECIDE ``4*m+2+4 = (m+1) * 4 + 2:num``]
  \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH) lisp_inv_Val
  \\ SIMP_TAC std_ss [] \\ METIS_TAC []);

val lisp_inv_SUB = store_thm("lisp_inv_SUB",
  ``isVal x1 /\ isVal x2 /\ getVal x2 <= getVal x1 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_SUB x1 x2,x2,x3,x4,x5,x6,limit) (w1 - w2 + 2w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  isVal_TAC
  \\ ASM_REWRITE_TAC [LISP_SUB_def,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ `(n2w (4 * a') + 2w - (n2w (4 * a'') + 2w) + 2w:word32 =
      n2w ((a' - a'') * 4 + 2)) /\ a' < a'' + 1073741824` suffices_by (STRIP_TAC THEN ASM_SIMP_TAC std_ss []
    \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH) lisp_inv_Val
    \\ ASM_SIMP_TAC std_ss [word_add_n2w] \\ METIS_TAC [])
  \\ REVERSE STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REWRITE_TAC [word_add_n2w,word_arith_lemma2]
  \\ `~(4 * a' + 2 < 4 * a'' + 2)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [word_add_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ DECIDE_TAC);

val lisp_inv_SUB1 = store_thm("lisp_inv_SUB1",
  ``isVal x1 /\ 0 < getVal x1 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_SUB x1 (Val 1),x2,x3,x4,x5,x6,limit) (w1 - 4w,w2,w3,w4,w5,w6,a,x,xs,s,rest)``,
  isVal_TAC
  \\ ASM_REWRITE_TAC [LISP_SUB_def,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_SUB]
  \\ `(n2w (4 * a') + 2w - 4w:word32 =
      n2w ((a' - 1) * 4 + 2)) /\ a' < 1073741825` suffices_by (STRIP_TAC THEN ASM_SIMP_TAC std_ss []
    \\ (MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o UNDISCH) lisp_inv_Val
    \\ ASM_SIMP_TAC std_ss [word_add_n2w] \\ METIS_TAC [])
  \\ REVERSE STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REWRITE_TAC [word_add_n2w,word_arith_lemma2]
  \\ `~(4 * a' + 2 < 4)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [word_add_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ DECIDE_TAC);

val word_lsr_n2w = store_thm("word_lsr_n2w",
  ``!m n. m < dimword (:'a) ==>
          (((n2w m):'a word) >>> n = n2w (m DIV (2 ** n)))``,
  ONCE_REWRITE_TAC [GSYM n2w_w2n] THEN REWRITE_TAC [w2n_lsr]
  THEN REWRITE_TAC [n2w_w2n] THEN SIMP_TAC std_ss [w2n_n2w]);

val LEMMA_MULT_4 = DECIDE ``!n. n < 1073741824 ==> 4 * n + 2 < 4294967296:num``

val lisp_inv_Val_nil_nil = let
  val imp = ((UNDISCH o SPEC_ALL o UNDISCH) lisp_inv_Val)
  val imp1 = DISCH_ALL (MATCH_MP lisp_inv_swap2 (UNDISCH lisp_inv_nil))
  val imp2 = DISCH_ALL (MATCH_MP lisp_inv_swap3 (UNDISCH lisp_inv_nil))
  val imp1 = DISCH_ALL (MATCH_MP imp1 (UNDISCH lisp_inv_swap2))
  val imp2 = DISCH_ALL (MATCH_MP imp2 (UNDISCH lisp_inv_swap3))
  val imp = (GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL) (MATCH_MP imp2 (MATCH_MP imp1 imp))
  in imp end;

val lisp_inv_MULT = store_thm("lisp_inv_MULT",
  ``isVal x1 /\ isVal x2 /\ getVal x1 * getVal x2 < 2 ** 30 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_MULT x1 x2, Sym "nil", Sym "nil",x4,x5,x6,limit)
             (((w1 >>> 2) * (w2 >>> 2)) << 2 + 2w, 3w, 3w,w4,w5,w6,a,x,xs,s,rest)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO,isVal_thm]
  \\ STRIP_TAC THEN STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [getVal_def,LISP_MULT_def]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap2
  \\ IMP_RES_TAC lisp_inv_read_Val
  \\ FULL_SIMP_TAC std_ss []
  \\ `(n2w (4 * a' + 2) >>> 2 * n2w (4 * a'' + 2) >>> 2) << 2 + 2w:word32 =
       n2w ((a' * a'') * 4 + 2)` suffices_by (STRIP_TAC THEN ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_inv_Val_nil_nil
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ IMP_RES_TAC LEMMA_MULT_4
  \\ IMP_RES_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] word_lsr_n2w))
  \\ ASM_SIMP_TAC std_ss [DIV_MULT]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ASM_SIMP_TAC std_ss [DIV_MULT,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]);

val LISP_DIV_MOD_LEMMA = prove(
  ``!n. n < 1073741824 ==> (n2w (4 * n + 2) >>> 2 = (n2w n):word32)``,
  REPEAT STRIP_TAC
  \\ `4 * n + 2 < 4 * (n + 1)` by DECIDE_TAC
  \\ `4 * (n + 1) <= 4 * 1073741824` by
        (SIMP_TAC bool_ss [LE_MULT_LCANCEL] \\ DECIDE_TAC)
  \\ IMP_RES_TAC LESS_LESS_EQ_TRANS
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_LSR_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [DIV_MULT]);

val lisp_inv_DIV = store_thm("lisp_inv_DIV",
  ``isVal x1 /\ isVal x2 /\ getVal x2 <> 0 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_DIV x1 x2, Sym "nil", Sym "nil",x4,x5,x6,limit)
             (((w1 >>> 2) // (w2 >>> 2)) << 2 + 2w,3w,3w,w4,w5,w6,a,x,xs,s,rest) /\
    lisp_word_div_pre (w1,w2)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO,isVal_thm]
  \\ STRIP_TAC THEN STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [getVal_def,LISP_DIV_def]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap2
  \\ IMP_RES_TAC lisp_inv_read_Val
  \\ FULL_SIMP_TAC std_ss []
  \\ `(n2w (4 * a' + 2) >>> 2 // n2w (4 * a'' + 2) >>> 2) << 2 + 2w:word32 =
       n2w ((a' DIV a'') * 4 + 2)` by
   (IMP_RES_TAC LEMMA_MULT_4
    \\ IMP_RES_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] word_lsr_n2w))
    \\ ASM_SIMP_TAC std_ss [DIV_MULT]
    \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ ASM_SIMP_TAC std_ss [DIV_MULT,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_div_def,w2n_n2w,word_mul_n2w,word_add_n2w]
    \\ `a'' < 4294967296 /\ a' < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1
   (ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_inv_Val_nil_nil
    \\ `0 < a''` by DECIDE_TAC
    \\ IMP_RES_TAC DIV_LESS_EQ
    \\ `a' <= 1073741823` by DECIDE_TAC
    \\ `a' DIV a'' <= 1073741823` by METIS_TAC [LESS_EQ_TRANS]
    \\ `a' DIV a'' < 1073741824` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [lisp_word_div_pre_def,LET_DEF]
  \\ IMP_RES_TAC LISP_DIV_MOD_LEMMA
  \\ `a' < 4294967296 /\ a'' < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,n2w_11]
  \\ DECIDE_TAC);

val lisp_inv_MOD = store_thm("lisp_inv_MOD",
  ``isVal x1 /\ isVal x2 /\ getVal x2 <> 0 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    lisp_inv (LISP_MOD x1 x2, Sym "nil", Sym "nil",x4,x5,x6,limit)
             ((word_mod (w1 >>> 2) (w2 >>> 2)) << 2 + 2w,3w,3w,w4,w5,w6,a,x,xs,s,rest) /\
    lisp_word_mod_pre (w1,w2)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO,isVal_thm]
  \\ STRIP_TAC THEN STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [getVal_def,LISP_MOD_def]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap2
  \\ IMP_RES_TAC lisp_inv_read_Val
  \\ FULL_SIMP_TAC std_ss []
  \\ `(word_mod (n2w (4 * a' + 2) >>> 2) (n2w (4 * a'' + 2) >>> 2)) << 2 + 2w:word32 =
       n2w ((a' MOD a'') * 4 + 2)` by
   (IMP_RES_TAC LEMMA_MULT_4
    \\ IMP_RES_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] word_lsr_n2w))
    \\ ASM_SIMP_TAC std_ss [DIV_MULT]
    \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ ASM_SIMP_TAC std_ss [DIV_MULT,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_mod_def,w2n_n2w,word_mul_n2w,word_add_n2w]
    \\ `a'' < 4294967296 /\ a' < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1
   (ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_inv_Val_nil_nil
    \\ `0 < a''` by DECIDE_TAC
    \\ IMP_RES_TAC MOD_LESS
    \\ `a' MOD a'' < a''` by METIS_TAC []
    \\ `a' MOD a'' < 1073741824` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [lisp_word_mod_pre_def,LET_DEF]
  \\ IMP_RES_TAC LISP_DIV_MOD_LEMMA
  \\ `a' < 4294967296 /\ a'' < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,n2w_11]
  \\ DECIDE_TAC);

val lisp_inv_LESS = store_thm("lisp_inv_LESS",
  ``isVal x1 /\ isVal x2 ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,x,xs,s,rest) ==>
    (getVal x1 < getVal x2 <=> w1 <+ w2)``,
  isVal_TAC \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,w2n_n2w]
  \\ `(4 * a'' + 2) < 4294967296 /\ (4 * a' + 2) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);


(* LDEPTH *)

val word_tree_11 = prove(
  ``!t a u d m. word_tree t (a,m) d ==> word_tree u (a,m) d ==> (t = u)``,
  REVERSE (Induct_on `t`)
  \\ Cases_on `u` \\ SIMP_TAC std_ss [word_tree_def,ALIGNED_INTRO]
  \\ SIMP_TAC std_ss [ADDR32_NEQ_ADDR32,ALIGNED_ADDR32,ALIGNED_ADD_EQ]
  \\ SIMP_TAC std_ss [ALIGNED_n2w,WORD_EQ_ADD_RCANCEL,ADDR32_11]
  \\ SIMP_TAC std_ss [XExp_11] \\ METIS_TAC []);

val word_tree_IMP_DELETE = prove(
  ``!t a m d. word_tree t (a,m) d ==> ~(word_tree t (a,m) (d DELETE w)) ==>
              ?u. word_tree u (w,m) d /\ XSIZE u <= XSIZE t``,
  Induct \\ SIMP_TAC std_ss [word_tree_def] \\ REPEAT STRIP_TAC
  \\ (Cases_on `a = w` THEN1 METIS_TAC [word_tree_def,LESS_EQ_TRANS,LESS_EQ_REFL])
  \\ FULL_SIMP_TAC std_ss [IN_DELETE,XSIZE_def]
  \\ `XSIZE t <= SUC (XSIZE t + XSIZE t')` by DECIDE_TAC
  \\ `XSIZE t' <= SUC (XSIZE t + XSIZE t')` by DECIDE_TAC
  \\ METIS_TAC [word_tree_def,LESS_EQ_TRANS,LESS_EQ_REFL]);

val word_tree_XDot_IMP = prove(
  ``word_tree (XDot x y) (a,m) dm ==>
      a IN dm /\ ALIGNED a /\
      word_tree x (m a,m) (dm DELETE a) /\
      word_tree y (m (a + 4w),m) (dm DELETE a)``,
  STRIP_TAC
  \\ `!u. word_tree u (a,m) dm ==> (XDot x y = u)` by METIS_TAC [word_tree_11]
  \\ FULL_SIMP_TAC std_ss [word_tree_def]
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC word_tree_IMP_DELETE
  \\ `u = XDot x y` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [XSIZE_def] \\ DECIDE_TAC);

val word_tree_XDEPTH_LEMMA = prove(
  ``!s t m a.
      word_tree t (a,m) s /\ FINITE s ==> XDEPTH t <= CARD s``,
  STRIP_TAC \\ Induct_on `CARD s` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [] THEN1
   (REPEAT STRIP_TAC \\ Cases_on `t`
    \\ SIMP_TAC std_ss [XDEPTH_def]
    \\ IMP_RES_TAC CARD_EQ_0
    \\ FULL_SIMP_TAC std_ss [word_tree_def,NOT_IN_EMPTY])
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `t`)
  \\ FULL_SIMP_TAC std_ss [XDEPTH_def,lisp_x_def]
  \\ IMP_RES_TAC word_tree_XDot_IMP
  \\ `(v = CARD (s DELETE (a:word32))) /\ FINITE (s DELETE a)` suffices_by
  (STRIP_TAC THEN METIS_TAC [])
  \\ IMP_RES_TAC CARD_DELETE
  \\ ASM_SIMP_TAC std_ss [FINITE_DELETE]);

val CARD_ch_active_set = prove(
  ``!k i a.
      (CARD (ch_active_set (a,i,i + k)) <= k) /\
      FINITE (ch_active_set (a,i,i + k))``,
  Induct THENL [
    REPEAT STRIP_TAC
    \\ `ch_active_set (a,i,i + 0) = {}` by
      (FULL_SIMP_TAC std_ss [EXTENSION,ch_active_set_def,NOT_IN_EMPTY,
         GSPECIFICATION] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [CARD_EMPTY,FINITE_EMPTY],
    REPEAT STRIP_TAC
    \\ `(ch_active_set (a,i,i + SUC k) =
      (a + 8w * n2w i) INSERT ch_active_set (a,SUC i,SUC i + k))` by
      (FULL_SIMP_TAC std_ss [EXTENSION,ch_active_set_def,NOT_IN_EMPTY,
         GSPECIFICATION,IN_INSERT]
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
       \\ ASM_SIMP_TAC std_ss [] THENL [
         Cases_on `i = j` \\ ASM_SIMP_TAC std_ss [] \\ DISJ2_TAC
         \\ Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
         Q.EXISTS_TAC `i` \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
         Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC])
    \\ ASM_SIMP_TAC std_ss [CARD_INSERT,FINITE_INSERT]
    \\ Cases_on `a + 8w * n2w i IN ch_active_set (a,SUC i,SUC i + k)`
    \\ ASM_SIMP_TAC std_ss [CARD_INSERT,FINITE_INSERT]
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `SUC (CARD (ch_active_set (a,SUC i,SUC i + k)))`
    \\ ASM_SIMP_TAC std_ss []]);

val word_tree_XDEPTH = prove(
  ``!t a m w v i.
      word_tree t (a,m) (ch_active_set (w,v,i)) /\ v <= i ==> XDEPTH t <= i - v``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPECL [`(i - v)`,`v`,`w`] CARD_ch_active_set)
  \\ `v + (i - v) = i` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC LESS_EQ_TRANS
  \\ Q.EXISTS_TAC `CARD (ch_active_set (w,v,i))`
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC word_tree_XDEPTH_LEMMA
  \\ Q.EXISTS_TAC `m` \\ Q.EXISTS_TAC `a`
  \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_LDEPTH_LEMMA = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,l) (w1,w2,w3,w4,w5,w6,a,df,f,s,rest) ==>
    LDEPTH x1 <= l``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
  \\ MATCH_MP_TAC LESS_EQ_TRANS
  \\ Q.EXISTS_TAC `i - v`
  \\ REVERSE STRIP_TAC THEN1
   (Cases_on `u` \\ Q.UNABBREV_TAC `v`
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ (STRIP_ASSUME_TAC o UNDISCH o
       Q.SPECL [`x1`,`w1`,`ch_active_set (a,v,i)`,`f`,`s`]) lisp_x_word_tree
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC word_tree_XDEPTH
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val lisp_inv_LDEPTH = store_thm("lisp_inv_LDEPTH",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (w1,w2,w3,w4,w5,w6,a,df,f,s,rest) ==>
    LDEPTH x1 <= limit /\ LDEPTH x2 <= limit /\ LDEPTH x3 <= limit /\
    LDEPTH x4 <= limit /\ LDEPTH x5 <= limit /\ LDEPTH x6 <= limit``,
  STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap2
  \\ IMP_RES_TAC lisp_inv_swap3
  \\ IMP_RES_TAC lisp_inv_swap4
  \\ IMP_RES_TAC lisp_inv_swap5
  \\ IMP_RES_TAC lisp_inv_swap6
  \\ IMP_RES_TAC lisp_inv_LDEPTH_LEMMA \\ ASM_SIMP_TAC std_ss []);


val _ = export_theory();
