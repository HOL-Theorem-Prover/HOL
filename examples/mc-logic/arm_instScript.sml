(*
  quietdec := true;
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;

open pred_setTheory res_quanTheory wordsTheory arithmeticTheory;
open arm_rulesTheory arm_rulesLib arm_evalTheory armTheory instructionTheory; 
open combinTheory listTheory rich_listTheory pairTheory sortingTheory;
open relationTheory wordsLib fcpTheory systemTheory bitTheory;
open set_sepTheory set_sepLib progTheory arm_progTheory addressTheory;

val _ = new_theory "arm_inst";

(*
  quietdec := false;
*)


(* ----------------------------------------------------------------------------- *)
(* Setting the environment                                                       *)
(* ----------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = Parse.hide "set";

val arm_state_type = ``:'a arm_sys_state``;

val ARMel_type = ``:'a ARMel``;

val ARM_PROG_type =
  ``:('a ARMset -> bool) ->
     word32 list -> (word32 list # (word30 -> word30) -> bool) ->
     ('a ARMset -> bool) ->
    (('a ARMset -> bool) # 
      (word30 -> word30) -> bool) -> bool``;

val ARM_PROG2_type =
  ``:condition ->
     ('a ARMset -> bool) ->
     word32 list -> (word32 list # (word30 -> word30) -> bool) ->
     ('a ARMset -> bool) ->
    (('a ARMset -> bool) # 
      (word30 -> word30) -> bool) -> bool``;

val ERROR = mk_HOL_ERR "";

val PAIR_EQ = pairTheory.PAIR_EQ;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val UD_ALL = UNDISCH_ALL o RW [GSYM AND_IMP_INTRO];

val INSERT_UNION_COMM = prove(
  ``!x s t. (x INSERT s) UNION t = x INSERT (s UNION t)``,
  ONCE_REWRITE_TAC [INSERT_SING_UNION] \\ REWRITE_TAC [UNION_ASSOC]);

val DISJOINT_SING = prove(
  ``!p s. DISJOINT {p} s = ~(p IN s)``,
  SRW_TAC [] [DISJOINT_DEF,EXTENSION,IN_INTER,IN_INSERT,NOT_IN_EMPTY]);

val SET_APPEND_ss = rewrites [INSERT_UNION_COMM,UNION_EMPTY];

fun can_match x y = can (uncurry match_term) (x,y);
fun subst_fresh x = subst [x |-> genvar (type_of x)];

val comb1 = fst o dest_comb;
val comb2 = snd o dest_comb;
val binop1 = comb2 o comb1;
val binop2 = comb2;

val IF_DISTRIB_LEFT = prove(
  ``(if b then f x else f x') = f (if b then x else x')``,SRW_TAC [] []);

val IF_DISTRIB_RIGHT = prove(
  ``(if b then f x else g x) = (if b then f else g) x``,SRW_TAC [] []);

val PUSH_IF_ss = rewrites [IF_DISTRIB_LEFT,IF_DISTRIB_RIGHT];

(* helpers *)

fun LIST_DISCH ts th = foldr (uncurry DISCH) th ts;

fun ASM_UNABBREV_ALL_RULE th =
  let
    val xs = hyp th  
    val is_Abbrev = can_match ``Abbrev b``; 
    val xs1 = filter is_Abbrev xs
    val xs2 = filter (not o is_Abbrev) xs
    val th = LIST_DISCH xs1 (LIST_DISCH xs2 th)
    fun unabbrev_fst th =
      let
        val (l,r) = (dest_eq o snd o dest_comb o binop1 o concl) th
        val th = INST [l |-> r] th
        val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [markerTheory.Abbrev_def])) th
      in
        MP th TRUTH
      end
    val unabbrev_all = funpow (length xs1) unabbrev_fst
    val undisch_rest = funpow (length xs2) UNDISCH
  in
    undisch_rest (unabbrev_all th)
  end;

val SET_NO_CP = RW [GSYM NEXT_ARM_MEM_def] o Q.INST [`cp`|->`NO_CP`] o SPEC_ALL;


(* ----------------------------------------------------------------------------- *)
(* Lemmas for MEMORY assertions                                                    *)
(* ----------------------------------------------------------------------------- *)

val update_def = prove(
  ``!a b. a =+ b = (\f k. (if k = a then b else f k))``,
  SIMP_TAC std_ss [UPDATE_def,FUN_EQ_THM] \\ METIS_TAC []);

val MEMORY_def = Define `
  MEMORY d f = BIGSTAR { M x (f (addr32 x)) | addr32 x IN d }`;

val list_update_def = Define `
  (list_update x [] f = f) /\
  (list_update x (y::ys) f = list_update (x+4w) ys ((x =+ y) f))`;

val list_read_def = Define `
  (list_read x [] f = []) /\
  (list_read x (y::ys) f = f x :: list_read (x+4w) ys f)`;

val seq_addresses_def = Define `
  (seq_addresses (a:word32) [] = {}) /\ 
  (seq_addresses a (x::xs) = a INSERT seq_addresses (a+4w) xs)`;

val update_update = prove(
  ``!x y q f. (x =+ y) ((x =+ q) f) = (x =+ y) f``,
  SIMP_TAC std_ss [FUN_EQ_THM,update_def]);

val read_update = prove(
  ``!x y f. ((x =+ y) f) x = y``,
  SIMP_TAC std_ss [FUN_EQ_THM,update_def]);

val list_read_MAP = prove(
  ``!xs x g. list_read x (MAP g xs) = list_read x xs ``,
  Induct \\ ASM_REWRITE_TAC [list_read_def,MAP,FUN_EQ_THM]);

val seq_addresses_MAP = prove(
  ``!xs a g. seq_addresses a (MAP g xs) = seq_addresses a xs ``,
  Induct \\ ASM_REWRITE_TAC [seq_addresses_def,MAP]);

val IN_seq_addresses = prove(
  ``!zs z q. q IN seq_addresses z zs = ?k. (q = z + n2w (4 * k)) /\ k < LENGTH zs``,
  Induct \\ REWRITE_TAC [seq_addresses_def,LENGTH,NOT_IN_EMPTY,DECIDE ``~(k < 0)``]        
  \\ ASM_REWRITE_TAC [IN_INSERT] \\ REPEAT STRIP_TAC
  \\ Cases_on `q = z` \\ ASM_REWRITE_TAC []
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [MULT_CLAUSES,DECIDE ``0 < SUC n``,WORD_ADD_0])
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `SUC k`
    \\ ASM_REWRITE_TAC [ADD1,LT_ADD_RCANCEL,GSYM word_add_n2w,GSYM word_mul_n2w]
    \\ REWRITE_TAC [WORD_MULT_CLAUSES,WORD_ADD_ASSOC], 
    Cases_on `k`
    \\ FULL_SIMP_TAC bool_ss [MULT_CLAUSES,WORD_ADD_0,ADD1,LT_ADD_RCANCEL]
    \\ Q.EXISTS_TAC `n` \\ FULL_SIMP_TAC bool_ss 
      [MULT_CLAUSES,WORD_ADD_0,ADD1,LT_ADD_RCANCEL,word_add_n2w,GSYM WORD_ADD_ASSOC]]);

val list_read_update = prove(
  ``!ys x h f:word32->word32. 
      ~(z IN seq_addresses x ys) ==> 
      (list_read x ys ((z =+ h) f) = list_read x ys f)``,
  Induct \\ FULL_SIMP_TAC std_ss 
    [list_read_def,LENGTH,update_def,seq_addresses_def,IN_INSERT]);

val read_list_update = prove(
  ``!ys x z f. ~(z IN seq_addresses x ys) ==> (list_update x ys f z = f z)``,
  Induct \\ FULL_SIMP_TAC std_ss 
    [list_update_def,LENGTH,update_def,seq_addresses_def,IN_INSERT]);

val seq_addresses_LEMMA = prove(
  ``!x ys. LENGTH ys <= 16 ==> ~(x IN seq_addresses (x + 4w) ys)``,
  SIMP_TAC bool_ss [IN_seq_addresses] \\ REPEAT STRIP_TAC    
  \\ Cases_on `k < LENGTH ys` \\ ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC [RW [WORD_ADD_0] (Q.SPECL [`x`,`0w`] WORD_EQ_ADD_LCANCEL)]
  \\ SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,n2w_11]
  \\ REWRITE_TAC [DECIDE ``4*k = k+k+k+k``]
  \\ `4 + (k + k + k + k) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val list_read_list_update = prove(
  ``!qs x (f:word32->word32). LENGTH qs <= 16 ==> (list_read x qs (list_update x qs f) = qs)``,
  Induct \\ ASM_SIMP_TAC bool_ss 
    [list_read_def,list_update_def,CONS_11,DECIDE ``SUC n <= m ==> n <= m``,LENGTH]
  \\ REPEAT STRIP_TAC \\ `LENGTH qs <= 16` by DECIDE_TAC 
  \\ `~(x IN seq_addresses (x + 4w) qs)` by METIS_TAC [seq_addresses_LEMMA]
  \\ ASM_SIMP_TAC bool_ss [read_list_update,read_update]);

val list_update_update = prove(
  ``!ys x z h f q. 
      ~(z = q) ==> (list_update x ys ((z =+ h) f) q = list_update x ys f q)``,
  Induct THEN1 ASM_SIMP_TAC bool_ss [list_update_def,update_def]
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [list_update_def] 
  \\ Cases_on `x = z` \\ ASM_REWRITE_TAC []
  THEN1 SIMP_TAC bool_ss [update_def] 
  \\ METIS_TAC [UPDATE_COMMUTES]);
    
val list_update_list_update = prove(
  ``!qs x (f:word32->word32). 
      LENGTH qs <= 16 ==> 
      (list_update x qs (list_update x qs f) = list_update x qs f)``,
  Induct \\ ASM_SIMP_TAC bool_ss [list_update_def,LENGTH] \\ REPEAT STRIP_TAC
  \\ `LENGTH qs <= 16` by DECIDE_TAC
  \\ `!f. (x =+ h) (list_update (x + 4w) qs f) = 
          list_update (x + 4w) qs ((x =+ h) f)` by ALL_TAC
  \\ ASM_SIMP_TAC bool_ss [FUN_EQ_THM,update_update] \\ REPEAT STRIP_TAC
  \\ Cases_on `x' = x` \\ IMP_RES_TAC seq_addresses_LEMMA
  \\ ASM_SIMP_TAC bool_ss [read_list_update,update_def,list_update_update]);

val LENGTH_list_READ = prove(
  ``!qs x f. LENGTH (list_read x qs f) = LENGTH qs``,
  Induct \\ ASM_REWRITE_TAC [list_read_def,LENGTH]);

val MEMORY_SPLIT = prove(
  ``!f d x. aligned x /\ x IN d ==>
            (MEMORY d f = M (addr30 x) (f x) * 
             MEMORY (d DELETE x) ((x =+ y) f) :'a ARMset -> bool)``,
  REWRITE_TAC [MEMORY_def,aligned_def] \\ REPEAT STRIP_TAC THEN
  `{M x (f (addr32 x)) | addr32 x IN d} = ((M (addr30 x) (f x)):'a ARMset -> bool) INSERT 
   {M x' ((x =+ y) f (addr32 x')) | x' | addr32 x' IN d DELETE x}` by ALL_TAC << [
    IMP_RES_TAC EXISTS_addr30
    \\ FULL_SIMP_TAC bool_ss [addr30_addr32]
    \\ ONCE_REWRITE_TAC [EXTENSION]
    \\ REWRITE_TAC [IN_INSERT,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
      FULL_SIMP_TAC std_ss [] \\ Cases_on `x'' = y'` 
      \\ ASM_SIMP_TAC bool_ss [update_def,addr32_11]
      \\ DISJ2_TAC \\ Q.EXISTS_TAC `x''`      
      \\ ASM_SIMP_TAC bool_ss [IN_DELETE,addr32_11],
      Q.EXISTS_TAC `y'` \\ ASM_SIMP_TAC bool_ss [],
      FULL_SIMP_TAC std_ss [IN_DELETE,update_def]
      \\ Q.EXISTS_TAC `x''` \\ ASM_REWRITE_TAC []],
    ASM_REWRITE_TAC [] \\ MATCH_MP_TAC BIGSTAR_INSERT
    \\ SIMP_TAC std_ss [GSPECIFICATION,IN_DELETE] \\ STRIP_TAC
    \\ IMP_RES_TAC EXISTS_addr30 \\ ASM_REWRITE_TAC [addr32_11] 
    \\ Cases_on `x' = y'` \\ ASM_SIMP_TAC bool_ss [update_def,addr32_11]
    \\ DISJ1_TAC \\ MATCH_MP_TAC M_NEQ_M   
    \\ ASM_SIMP_TAC bool_ss [addr30_addr32] \\ METIS_TAC []]);

val MEMORY_list_SPLIT_LEMMA = prove(
  ``!ys y x. 
      LENGTH (y::ys) <= 16 ==> 
      (seq_addresses x (y::ys) SUBSET d = 
       x IN d /\ seq_addresses (x + 4w) ys SUBSET (d DELETE x))``,
  REWRITE_TAC [seq_addresses_def,INSERT_SUBSET,LENGTH] \\ REPEAT STRIP_TAC
  \\ `LENGTH ys <= 16` by DECIDE_TAC \\ IMP_RES_TAC seq_addresses_LEMMA
  \\ REWRITE_TAC [SUBSET_DEF,IN_DELETE] \\ METIS_TAC []);

val MEMORY_list_SPLIT = prove(
  ``!ys f d x. 
      LENGTH ys <= 16 ==>
      seq_addresses x ys SUBSET d /\ aligned x ==>
      (MEMORY d f = ((ms (addr30 x) (list_read x ys f)):'a ARMset -> bool) * 
                  MEMORY (d DIFF seq_addresses x ys) (list_update x ys f))``,
  Induct THEN1 REWRITE_TAC [ms_def,list_read_def,emp_STAR,seq_addresses_def,
               DIFF_EMPTY,list_update_def,INSERT_SUBSET,DIFF_INSERT]
  \\ SIMP_TAC bool_ss [MEMORY_list_SPLIT_LEMMA]
  \\ REWRITE_TAC [ms_def,list_read_def,emp_STAR,seq_addresses_def,
               DIFF_EMPTY,list_update_def,INSERT_SUBSET,DIFF_INSERT]
  \\ REPEAT STRIP_TAC
  \\ `aligned (x + 4w)` by METIS_TAC [aligned_MULT,EVAL ``4w * 1w:word32``]  
  \\ FULL_SIMP_TAC std_ss [addr30_ADD,LENGTH]
  \\ `LENGTH ys <= 16` by DECIDE_TAC
  \\ Q.PAT_ASSUM `!f.b` IMP_RES_TAC
  \\ IMP_RES_TAC MEMORY_SPLIT  
  \\ Q.PAT_ASSUM `!y f. b` (ASSUME_TAC o Q.SPEC `h`)
  \\ ASM_REWRITE_TAC [GSYM STAR_ASSOC]  
  \\ IMP_RES_TAC seq_addresses_LEMMA
  \\ ASM_SIMP_TAC bool_ss [list_read_update]);

val ARM_PROG_INTRO_SEQ_RD = prove(
  ``(!y. ARM_PROG2 c (P * M (addr30 x) y) code C (Q y * M (addr30 x) y) {}) ==>
    ARM_PROG2 c (P * MEMORY d f * cond (x IN d /\ aligned x)) code C
                (Q (f x) * MEMORY d f) {}``,
  REWRITE_TAC [ARM_PROG_MOVE_COND,ARM_PROG2_def] 
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ IMP_RES_TAC MEMORY_SPLIT \\ ASM_REWRITE_TAC [STAR_ASSOC]
  \\ METIS_TAC [ARM_PROG_FRAME,setSTAR_CLAUSES]);    

val ARM_PROG_INTRO_SEQ_RD_WR = prove(
  ``(!y. ARM_PROG2 c (P * M (addr30 x) y) code C (Q y * M (addr30 x) q) {}) ==>
    ARM_PROG2 c (P * MEMORY d f * cond (x IN d /\ aligned x)) code C 
                (Q (f x) * MEMORY d ((x =+ q) f)) {}``,
  REWRITE_TAC [ARM_PROG_MOVE_COND,ARM_PROG2_def] 
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ IMP_RES_TAC MEMORY_SPLIT \\ ASM_REWRITE_TAC [STAR_ASSOC,update_update,read_update]
  \\ METIS_TAC [ARM_PROG_FRAME,setSTAR_CLAUSES]);    

val ARM_PROG_INTRO_SEQ_WR = 
  SIMP_RULE std_ss [] (Q.INST [`Q`|->`\x. Q`] ARM_PROG_INTRO_SEQ_RD_WR);

val ARM_PROG_INTRO_SEQ_LIST_WR = prove(
  ``(!ys. (LENGTH ys = LENGTH qs) ==> 
          ARM_PROG2 c (P * ms (addr30 x) ys) [code] C (Q * ms (addr30 x) qs) {}) ==>
    ARM_PROG2 c (P * MEMORY d f * cond (seq_addresses x qs SUBSET d /\ aligned x /\ LENGTH qs <= 16)) [code] C 
                (Q * MEMORY d (list_update x qs f)) {}``,
  REWRITE_TAC [ARM_PROG_MOVE_COND,ARM_PROG2_def] 
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ IMP_RES_TAC MEMORY_list_SPLIT
  \\ ASM_SIMP_TAC bool_ss [list_read_list_update,list_update_list_update]
  \\ REWRITE_TAC [STAR_ASSOC] 
  \\ METIS_TAC [ARM_PROG_FRAME,setSTAR_CLAUSES,LENGTH_list_READ]);    

val ARM_PROG_INTRO_SEQ_LIST_RD = prove(
  ``(!ys. (LENGTH ys = LENGTH (qs:word32 list)) ==> 
          ARM_PROG2 c (P * ms (addr30 x) ys) [code] C (Q ys * ms (addr30 x) ys) {}) ==>
    ARM_PROG2 c (P * MEMORY d f * cond (seq_addresses x qs SUBSET d /\ aligned x /\ LENGTH qs <= 16)) [code] C
                (Q (list_read x qs f) * MEMORY d f) {}``,
  REWRITE_TAC [ARM_PROG_MOVE_COND,ARM_PROG2_def] 
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ IMP_RES_TAC MEMORY_list_SPLIT
  \\ ASM_SIMP_TAC bool_ss [list_read_list_update,list_update_list_update]
  \\ REWRITE_TAC [STAR_ASSOC] 
  \\ METIS_TAC [ARM_PROG_FRAME,setSTAR_CLAUSES,LENGTH_list_READ]);  

val ms_address_set_def = Define `
  (ms_address_set a 0 = ({}:word32 set)) /\ 
  (ms_address_set a (SUC n) = 
     addr32 a + 0w INSERT 
     addr32 a + 1w INSERT 
     addr32 a + 2w INSERT 
     addr32 a + 3w INSERT ms_address_set (a+1w) n)`;

val IN_ms_address_set = prove(
  ``!n a b. b IN ms_address_set a n = ?k. k < 4 * n /\ (b = addr32 a + n2w k)``,
  Induct \\ REWRITE_TAC [ms_address_set_def,NOT_IN_EMPTY,EVAL ``k < 4 * 0``,IN_INSERT]
  \\ ASM_REWRITE_TAC []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [ADD1,LEFT_ADD_DISTRIB,EVAL ``4*1``] 
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `1` \\ REWRITE_TAC [] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `2` \\ REWRITE_TAC [] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `3` \\ REWRITE_TAC [] \\ DECIDE_TAC) << [
    Q.EXISTS_TAC `k + 4`
    \\ REWRITE_TAC [addr32_ADD,addr32_n2w,EVAL ``4*1``]
    \\ ONCE_REWRITE_TAC [ADD_COMM] 
    \\ ASM_REWRITE_TAC [LT_ADD_LCANCEL,WORD_ADD_ASSOC,GSYM word_add_n2w],
    Cases_on `k` \\ ASM_REWRITE_TAC []
    \\ Cases_on `n'` \\ ASM_REWRITE_TAC [EVAL ``SUC 0``]
    \\ Cases_on `n''` \\ ASM_REWRITE_TAC [EVAL ``SUC (SUC 0)``]
    \\ Cases_on `n'` \\ ASM_REWRITE_TAC [EVAL ``SUC (SUC (SUC 0))``]
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``SUC (SUC (SUC (SUC n))) = n + 4``,DISJ_ASSOC,
                              ADD1,LEFT_ADD_DISTRIB,EVAL ``4*1``,LT_ADD_RCANCEL]
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `n''` 
    \\ REWRITE_TAC [GSYM word_add_n2w,addr32_ADD,EVAL ``4*1``,addr32_n2w]
    \\ METIS_TAC [WORD_ADD_COMM,WORD_ADD_ASSOC]]);

val FORALL_IN_ms_address_set = prove(
  ``!n z. 2**30 <= n ==> !p. p IN ms_address_set z n``,
  REWRITE_TAC [IN_ms_address_set] \\ REPEAT STRIP_TAC 
  \\ Q.EXISTS_TAC `w2n (($- (addr32 z) + p):word32)`
  \\ REWRITE_TAC [n2w_w2n,WORD_ADD_ASSOC,GSYM word_sub_def,WORD_SUB_REFL,WORD_ADD_0]  
  \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS
  \\ Q.EXISTS_TAC `4 * 2**30`
  \\ ASM_REWRITE_TAC [LE_MULT_LCANCEL]
  \\ ASSUME_TAC (INST_TYPE [``:'a``|->``:32``] w2n_lt)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []);


(* ----------------------------------------------------------------------------- *)
(* Lemmas about registers                                                        *)
(* ----------------------------------------------------------------------------- *)

val REG_WRITE_r15 = prove(
  ``!r m n d. ~(15w = n) ==> ((REG_WRITE r m n d) r15 = r r15)``,
  METIS_TAC [(RW [REG_READ6_def,FETCH_PC_def] o Q.INST [`n2`|->`15w`] o SPEC_ALL) 
             arm_evalTheory.REG_READ_WRITE_NEQ]);

val INC_PC_r15 = prove(
  ``!r. INC_PC r r15 = r r15 + 4w``,
  SRW_TAC [] [INC_PC_def,UPDATE_def]);

val REG_READ_WRITE = prove(
  ``!r m n d. ~(15w = n) ==> (REG_READ (REG_WRITE r m n d) m n = d)``,
  SIMP_TAC bool_ss [REG_READ_def,REG_WRITE_def,UPDATE_def]);

val REG_READ_WRITE_NEQ2 = prove(
  ``!n1 n2 r m1 m2 d. 
      ~(n1 = n2) ==> 
      (REG_READ (REG_WRITE r m1 n1 d) m2 n2 = REG_READ r m2 n2)``,
  REPEAT STRIP_TAC \\ Cases_on `15w = n2`
  THEN1 ASM_SIMP_TAC std_ss [REG_READ_def,REG_READ_WRITE_NEQ,REG_WRITE_r15]
  \\ METIS_TAC [REG_READ6_def,REG_READ_WRITE_NEQ]);

val REG_WRITE_15 = prove(
  ``!regs m x. REG_WRITE regs m 15w x r15 = x``,
  SIMP_TAC bool_ss [REG_WRITE_def,mode_reg2num_def,LET_DEF,EVAL ``w2n (15w:word4)``]
  \\ SIMP_TAC bool_ss [num2register_thm,UPDATE_def]);


val REG_READ_WRITE_NEQ = prove(
  ``!r m1 m2 n1 n2 d.
       ~(15w = n2) /\ ~(n1 = n2) ==>
       (REG_READ (REG_WRITE r m1 n1 d) m2 n2 = REG_READ r m2 n2)``,
  METIS_TAC [REG_READ_WRITE_NEQ,REG_READ6_def]);

val regs_15w_EQ_reg15 = prove(
  ``!s. s.registers r15 = reg 15w s``,  
  SRW_TAC [] [reg_def]);

val REG_WRITE_READ = prove(
  ``!rs m r. ~(r = 15w) ==> (REG_WRITE rs m r (REG_READ rs m r) = rs)``,
  REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC bool_ss [REG_WRITE_def,REG_READ_def] \\ SRW_TAC [] [UPDATE_def]);


(* ----------------------------------------------------------------------------- *)
(* Functions for specialising the address modes                                  *)
(* ----------------------------------------------------------------------------- *)

(* address mode 1 *)

val _ = Hol_datatype `
  abbrev_addr1 = OneReg | 
                 Imm of word8 | 
                 DpImm of word4 # word8 |
                 RegLSR of word5 | 
                 RegLSL of word5 | 
                 RegASR of word5 | 
                 RegROR of word5`;

val ADDR_MODE1_CMD_def = Define `
  (ADDR_MODE1_CMD OneReg Rd = Dp_shift_immediate (LSL Rd) 0w) /\
  (ADDR_MODE1_CMD (RegLSR w) Rd = Dp_shift_immediate (LSR Rd) w) /\
  (ADDR_MODE1_CMD (RegLSL w) Rd = Dp_shift_immediate (LSL Rd) w) /\
  (ADDR_MODE1_CMD (RegASR w) Rd = Dp_shift_immediate (ASR Rd) w) /\
  (ADDR_MODE1_CMD (RegROR w) Rd = Dp_shift_immediate (ROR Rd) w) /\
  (ADDR_MODE1_CMD (Imm k) Rd = Dp_immediate 0w k) /\
  (ADDR_MODE1_CMD (DpImm (q,r)) Rd = Dp_immediate q r)`;

val ADDR_MODE1_VAL_def = Define `
  (ADDR_MODE1_VAL OneReg  x c = (c,x)) /\
  (ADDR_MODE1_VAL (Imm k) x c = (c,w2w k)) /\
  (ADDR_MODE1_VAL (DpImm (i,k)) x c = 
    (FST (IMMEDIATE c ((11 >< 0) (33554432w:word32 !! w2w i << 8 !! w2w k))), 
     SND (IMMEDIATE c ((11 >< 0) (33554432w:word32 !! w2w i << 8 !! w2w k))))) /\
  (ADDR_MODE1_VAL (RegLSL w) x c = (if w = 0w then c else x %% (32 - w2n w),x << w2n w)) /\
  (ADDR_MODE1_VAL (RegASR w) x c = 
     ((if w = 0w then x %% 31 else x %% (w2n w - 1)),
      (if w = 0w then x >> 32 else x >> w2n w))) /\
  (ADDR_MODE1_VAL (RegLSR w) x c = 
     ((if w = 0w then x %% 31 else x %% (w2n w - 1)),
      (if w = 0w then x >>> 32 else x >>> w2n w))) /\
  (ADDR_MODE1_VAL (RegROR w) (x:word32) c = 
     ((if w = 0w then x %% 0 else x %% (w2n w - 1)),
      (if w = 0w then (FCP i. (if i = dimindex (:32) - 1 then c else x >>> 1 %% i))
       else x #>> w2n w)))`;

val ADDR_MODE1_VAL_THM = prove( 
  ``!c. ADDR_MODE1 state.registers mode z
         (IS_DP_IMMEDIATE (ADDR_MODE1_CMD c Rd))
         ((11 >< 0) (addr_mode1_encode (ADDR_MODE1_CMD c Rd))) =
        ADDR_MODE1_VAL c (REG_READ state.registers mode Rd) z``,
  Cases
  \\ REWRITE_TAC [ADDR_MODE1_CMD_def,ADDR_MODE1_VAL_def]
  \\ REWRITE_TAC [IS_DP_IMMEDIATE_def,shift_immediate_shift_register,ADDR_MODE1_def]
  \\ REWRITE_TAC [immediate_enc,shift_immediate_enc]
  THEN1 SRW_TAC [] [ROR_def,w2w_def,LSL_def,LSR_def,word_mul_n2w]
  THEN1 SRW_TAC [] [ROR_def,w2w_def,LSL_def,LSR_def,word_mul_n2w]
  \\ Q.SPEC_TAC (`c'`,`c`)
  THENL [ALL_TAC,Cases,Cases,Cases,Cases]
  \\ ASM_SIMP_TAC bool_ss [n2w_11,LESS_MOD,ZERO_LT_dimword,w2w_def,w2n_n2w] << [
    Cases_on `p` \\ SIMP_TAC (srw_ss()) [ADDR_MODE1_CMD_def,IS_DP_IMMEDIATE_def,
      addr_mode1_encode_def,PAIR,ADDR_MODE1_VAL_def],
    Cases_on `n = 0` 
    \\ ASM_REWRITE_TAC [LSR_def,EVAL ``32w:word8 = 0w``,EVAL ``w2n (32w:word8) - 1``] 
    \\ REWRITE_TAC [WORD_LS,LESS_EQ_REFL,EVAL ``w2n (32w:word8)``]
    THEN1 SRW_TAC [] [ROR_def,w2w_def,LSL_def,LSR_def,word_mul_n2w]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD]    
    \\ `n < 256 /\ n <= 32` by DECIDE_TAC
    \\ `~(n2w n = 0w:word8)` by ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LESS_MOD]    
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD]    
    \\ SRW_TAC [] [ROR_def,w2w_def,LSL_def,LSR_def,word_mul_n2w],
    Cases_on `n = 0` 
    \\ ASM_REWRITE_TAC [LSL_def,EVAL ``32w:word8 = 0w``,SHIFT_ZERO] THEN1 SRW_TAC [] []
    \\ FULL_SIMP_TAC (bool_ss++SIZES_ss) [n2w_11,w2n_n2w,LESS_MOD,EVAL ``0 < 256``,WORD_LS]    
    \\ `n < 256 /\ 32 < 256 /\ n <= 32` by DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [LESS_MOD]
    \\ SRW_TAC [] [],
    Cases_on `n = 0` 
    \\ FULL_SIMP_TAC (bool_ss++SIZES_ss) [ASR_def,EVAL ``32w:word8 = 0w``,SHIFT_ZERO,w2n_n2w,LSL_def]
    \\ `0 < 256 /\ n < 256 /\ 32 < 256 /\ n <= 32` by DECIDE_TAC 
    \\ ASM_SIMP_TAC bool_ss [LESS_MOD,EVAL ``MIN 31 (32-1)``] \\ SRW_TAC [] []
    \\ `~(31 < n - 1)` by DECIDE_TAC \\ REWRITE_TAC [MIN_DEF] 
    \\ FULL_SIMP_TAC (bool_ss++SIZES_ss) [MIN_DEF,LESS_MOD] \\ METIS_TAC [LESS_MOD],
    Cases_on `n = 0` \\ ASM_REWRITE_TAC [word_rrx_def,word_lsb_def,ROR_def]
    \\ `dimword (:5) < dimword (:8)` by SIMP_TAC (std_ss++SIZES_ss) []
    \\ `n < dimword (:8)` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [n2w_11,LESS_MOD,ZERO_LT_dimword,w2n_n2w,w2w_def]
    \\ SRW_TAC [] []]);
     
val FIX_ADDR_MODE1 = 
  RW [ADDR_MODE1_VAL_THM] o
  Q.INST [`Op2`|->`ADDR_MODE1_CMD a_mode Rn`] o
  SPEC_ALL;


(* address mode 2 *)

val ADDRESS_ROTATE = prove(
  ``!q:word32 z:word30. q #>> (8 * w2n ((1 >< 0) (addr32 z):word2)) = q``,
  SIMP_TAC std_ss [addr32_eq_0,EVAL ``w2n (0w:word2)``] \\ STRIP_TAC \\ EVAL_TAC);

val ADDR_MODE2_ADDR'_def = Define `
  ADDR_MODE2_ADDR' opt (imm:word12) (x:word32) = 
    if ~opt.Pre then x else 
      (if opt.Up then x + w2w imm else x - w2w imm)`;

val ADDR_MODE2_WB'_def = Define `
  ADDR_MODE2_WB' opt (imm:word12) (x:word32) =
    if opt.Pre /\ ~opt.Wb then x else
      (if opt.Up then x + w2w imm else x - w2w imm)`;

val ADDR_MODE2_WB'_THM = prove(
  ``!opt imm state. 
        ~(Rn = 15w) ==> 
        ((if
            opt.Pre ==> opt.Wb
          then
            INC_PC
              (REG_WRITE state.registers (state_mode state) Rn
                 (SND
                    (ADDR_MODE2 state.registers (state_mode state)
                       (CPSR_READ state.psrs %% 29)
                       (IS_DT_SHIFT_IMMEDIATE (Dt_immediate imm))
                       opt.Pre opt.Up Rn
                       ((11 >< 0) (addr_mode2_encode (Dt_immediate imm))))))
          else
            INC_PC state.registers) =
          INC_PC (REG_WRITE state.registers (state_mode state) Rn 
            (ADDR_MODE2_WB' opt imm (REG_READ state.registers (state_mode state) Rn))))``,
  Cases \\ Cases_on `b` \\ Cases_on `b0` \\ Cases_on `b1` 
  \\ SRW_TAC [] [ADDR_MODE2_WB'_def,immediate_enc2,IS_DT_SHIFT_IMMEDIATE_def]
  \\ ASM_SIMP_TAC bool_ss [ADDR_MODE2_def,LET_DEF,pairTheory.FST,UP_DOWN_def,
       SND,REG_WRITE_READ] \\ SRW_TAC [] []);

val ADDR_MODE2_ADDR'_THM = prove(
  ``!opt imm state. 
        FST (ADDR_MODE2 state.registers (state_mode state)
             (CPSR_READ state.psrs %% 29)
             (IS_DT_SHIFT_IMMEDIATE (Dt_immediate imm))
             opt.Pre opt.Up
               Rn ((11 >< 0) (addr_mode2_encode (Dt_immediate imm)))) =
        ADDR_MODE2_ADDR' opt imm 
          (REG_READ state.registers (state_mode state) Rn)``,
  Cases \\ Cases_on `b` \\ Cases_on `b0` \\ Cases_on `b1` 
  \\ SRW_TAC [] [ADDR_MODE2_ADDR'_def,immediate_enc2,IS_DT_SHIFT_IMMEDIATE_def]
  \\ ASM_SIMP_TAC bool_ss [ADDR_MODE2_def,LET_DEF,pairTheory.FST,UP_DOWN_def,
       SND,REG_WRITE_READ] \\ SRW_TAC [] []);

val ADDR_MODE2_CASES' = store_thm("ADDR_MODE2_CASES'",
  ``!imm x u.
      (ADDR_MODE2_ADDR' <|Pre := F; Up := F; Wb := u|> imm x = x) /\ 
      (ADDR_MODE2_ADDR' <|Pre := F; Up := T; Wb := u|> imm x = x) /\ 
      (ADDR_MODE2_ADDR' <|Pre := T; Up := F; Wb := u|> imm x = x - w2w imm) /\ 
      (ADDR_MODE2_ADDR' <|Pre := T; Up := T; Wb := u|> imm x = x + w2w imm) /\ 
      (ADDR_MODE2_WB' <|Pre := F; Up := F; Wb := F|> imm x = x - w2w imm) /\  
      (ADDR_MODE2_WB' <|Pre := F; Up := F; Wb := T|> imm x = x - w2w imm) /\  
      (ADDR_MODE2_WB' <|Pre := F; Up := T; Wb := F|> imm x = x + w2w imm) /\  
      (ADDR_MODE2_WB' <|Pre := F; Up := T; Wb := T|> imm x = x + w2w imm) /\  
      (ADDR_MODE2_WB' <|Pre := T; Up := F; Wb := F|> imm x = x) /\  
      (ADDR_MODE2_WB' <|Pre := T; Up := F; Wb := T|> imm x = x - w2w imm) /\  
      (ADDR_MODE2_WB' <|Pre := T; Up := T; Wb := F|> imm x = x) /\  
      (ADDR_MODE2_WB' <|Pre := T; Up := T; Wb := T|> imm x = x + w2w imm)``,
  SRW_TAC [] [ADDR_MODE2_ADDR'_def,ADDR_MODE2_WB'_def]);

(* address mode 2 aligned *)

val ADDR_MODE2_ADDR_def = Define `
  ADDR_MODE2_ADDR opt imm (x:word30) = 
    if ~opt.Pre then x else 
      (if opt.Up then x + w2w imm else x - w2w imm)`;

val ADDR_MODE2_WB_def = Define `
  ADDR_MODE2_WB opt imm (x:word30) =
    if opt.Pre /\ ~opt.Wb then x else
      (if opt.Up then x + w2w imm else x - w2w imm)`;

val n2w_lsl = prove(
  ``!m n. (n2w m):'a word << n = n2w (m * 2 ** n)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [word_lsl_n2w]
  \\ Cases_on `dimindex (:'a) - 1 < n` \\ ASM_REWRITE_TAC []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM n2w_mod]))
  \\ REWRITE_TAC [dimword_def]
  \\ `0 < dimindex (:'a)` by METIS_TAC [DIMINDEX_GT_0]
  \\ `dimindex (:'a) <= n` by DECIDE_TAC
  \\ `?k. n = dimindex (:'a) + k` by METIS_TAC [LESS_EQUAL_ADD]
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ REWRITE_TAC [EXP_ADD,MULT_ASSOC]
  \\ `0 < 2**dimindex(:'a)` by METIS_TAC [ZERO_LT_EXP,EVAL ``0 < 2``]
  \\ ASM_SIMP_TAC bool_ss [MOD_EQ_0]);

val w2w_ror_w2w = prove(
  ``!w. w2w (((w2w (w:word8)):word12) << 2):word32 = (w2w w) << 2``,
  Cases
  \\ REWRITE_TAC [w2w_def,n2w_11,n2w_lsl]
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (x MOD g = y MOD g)``)
  \\ MATCH_MP_TAC LESS_MOD
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n MOD 256 < 256` by METIS_TAC [EVAL ``0 < 256``,DIVISION]
  \\ DECIDE_TAC);

val MULT_MOD_MULT = prove(
  ``!k m n. 0 < k /\ 0 < n ==> ((m MOD k) * n = (m*n) MOD (k*n))``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (UNDISCH (Q.SPECL [`m`,`k`] DA))
  \\ ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC]  
  \\ `0 < k * n` by ASM_SIMP_TAC bool_ss [LESS_MULT2]  
  \\ `r * n < k * n` by ASM_SIMP_TAC bool_ss [LT_MULT_RCANCEL]
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT]);

val ADD_MODE2_ADD_LEMMA = prove(
  ``!x imm. w2w (x:word30) << 2 + w2w (imm:word8) << 2 = (w2w (x + w2w imm) << 2) :word32``,
  NTAC 2 Cases
  \\ REWRITE_TAC [w2w_def,n2w_lsl,word_add_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ REWRITE_TAC [GSYM word_add_n2w]
  \\ REWRITE_TAC [word_add_def] 
  \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n' < 1073741824` by DECIDE_TAC
  \\ `0 < 1073741824 /\ 0 < 4 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,MULT_MOD_MULT]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [MOD_MOD]);
  
val ADD_MODE2_SUB_LEMMA = prove(
  ``!x imm. w2w (x:word30) << 2 - w2w (imm:word8) << 2 = (w2w (x - w2w imm) << 2) :word32``,
  NTAC 2 Cases
  \\ REWRITE_TAC [w2w_def,n2w_lsl]
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD]
  \\ REWRITE_TAC [word_sub_def,word_2comp_n2w]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ `n' * 4 < 4294967296` by DECIDE_TAC
  \\ `n' < 1073741824` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [LESS_MOD,word_add_n2w,w2n_n2w]
  \\ `0 < 1073741824 /\ 0 < 4 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [MULT_MOD_MULT,RIGHT_ADD_DISTRIB,RIGHT_SUB_DISTRIB]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [MOD_MOD]);

val ADDR_MODE2_ADDR_THM = prove(
  ``ADDR_MODE2_ADDR' opt (((w2w (imm:word8)):word12) << 2) (addr32 y) =
    addr32 (ADDR_MODE2_ADDR opt imm y)``,
  REWRITE_TAC [ADDR_MODE2_ADDR_def,ADDR_MODE2_ADDR'_def]
  \\ Cases_on `opt.Pre` \\ Cases_on `opt.Up` 
  \\ ASM_REWRITE_TAC [addr30_addr32,w2w_ror_w2w]
  \\ REWRITE_TAC [addr32_def,ADD_MODE2_SUB_LEMMA,ADD_MODE2_ADD_LEMMA]
  \\ REWRITE_TAC [w2w_def,n2w_lsl,addr30_n2w,n2w_w2n]
  \\ SIMP_TAC std_ss [MULT_DIV,n2w_w2n]);

val ADDR_MODE2_WB_THM = prove(
  ``ADDR_MODE2_WB' opt (((w2w (imm:word8)):word12) << 2) (addr32 y) =
    addr32 (ADDR_MODE2_WB opt imm y)``,
  REWRITE_TAC [ADDR_MODE2_WB_def,ADDR_MODE2_WB'_def]
  \\ Cases_on `opt.Wb` \\ Cases_on `opt.Up` \\ Cases_on `opt.Pre`  
  \\ ASM_REWRITE_TAC [addr30_addr32,w2w_ror_w2w]
  \\ REWRITE_TAC [addr32_def,ADD_MODE2_SUB_LEMMA,ADD_MODE2_ADD_LEMMA]
  \\ REWRITE_TAC [w2w_def,n2w_lsl,addr30_n2w,n2w_w2n]
  \\ SIMP_TAC std_ss [MULT_DIV,n2w_w2n]);
 

(* ----------------------------------------------------------------------------- *)
(* General tools                                                                 *)
(* ----------------------------------------------------------------------------- *)
  
val ARM_PROG2_EQ = let
  val th = Q.SPECL [`P`,`[cmd]`,`Q`,`Q'`,`f`] ARM_PROG_INTRO
  val th = SIMP_RULE (std_ss++sep_ss) [LENGTH,ms_def,pcINC_def,wLENGTH_def] th
  val th = SIMP_RULE std_ss [ARM_RUN_SEMANTICS,ARMpc_def,STAR_ASSOC,R30_def,SEP_DISJ_def,LET_DEF] th
  in GSYM th end;

val ARM_PROG1_EQ = let
  val th = Q.INST [`Q'`|->`SEP_F`] ARM_PROG2_EQ
  val th = SIMP_RULE (bool_ss++sep_ss) [ARM_PROG_FALSE_POST,SEP_F_def,LET_DEF] th
  in th end;

val STATE_ARM_MEM_1 = 
  REWRITE_CONV [GSYM (EVAL ``SUC 0``),STATE_ARM_MEM_def,STATE_ARM_MMU_def,GSYM NEXT_ARM_MEM_def] ``STATE_ARM_MEM 1 s``;

val ARM_PROG_INIT_TAC = 
  REWRITE_TAC [ARM_PROG1_EQ,ARM_PROG2_EQ,PASS_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `1` \\ REWRITE_TAC [STATE_ARM_MEM_1];


(* ----------------------------------------------------------------------------- *)
(* Semantics of ``R a1 x1  * ... * R an xn * ms b1 y1 * ... * ms bm ym * ...``   *)
(* ----------------------------------------------------------------------------- *)

val xR_list_def = Define `
  (xR_list [] = emp) /\
  (xR_list ((r,NONE)::xs) = ~R r * xR_list xs) /\
  (xR_list ((r,SOME x)::xs) = R r x * xR_list xs)`;

val xR_list_sem_def = Define `
  (xR_list_sem [] s = T) /\
  (xR_list_sem ((r,NONE)::xs) s = xR_list_sem xs s) /\
  (xR_list_sem ((r,SOME x)::xs) s = (reg r s = x) /\ xR_list_sem xs s)`;

val xR_list_lemma = prove(
  ``((R r x * P) (arm2set' (rs,ns,st,ud,rt) s) = 
     (reg r s = x) /\ r IN rs /\ P (arm2set' (rs DELETE r,ns,st,ud,rt) s)) /\ 
    ((~R r * P) (arm2set' (rs,ns,st,ud,rt) s) = 
     r IN rs /\ P (arm2set' (rs DELETE r,ns,st,ud,rt) s))``,
  SIMP_TAC (std_ss++sep2_ss) [R_def,SEP_HIDE_THM] 
  \\ SIMP_TAC std_ss [SEP_EXISTS,one_STAR,IN_arm2set']
  \\ METIS_TAC [DELETE_arm2set']);

val xR_list_thm = prove(
  ``!xs P rs ns st ud rt. 
      (xR_list xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
      xR_list_sem xs s /\ ALL_DISTINCT (MAP FST xs) /\ 
      P (arm2set' (rs DIFF (LIST_TO_SET (MAP FST xs)),ns,st,ud,rt) s) /\
      (LIST_TO_SET (MAP FST xs)) SUBSET rs``,
  Induct << [
    SIMP_TAC (std_ss++sep_ss) 
      [xR_list_def,xR_list_sem_def,MAP,IN_LIST_TO_SET,MEM,SUBSET_DEF,ALL_DISTINCT]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(z = x) ==> (P (f (z,y) s) = P (f (x,y) s))``)
    \\ ONCE_REWRITE_TAC [EXTENSION] \\ REWRITE_TAC [IN_DIFF,IN_LIST_TO_SET,MEM],
    REPEAT STRIP_TAC \\ Cases_on `h` \\ Cases_on `r`
    \\ SIMP_TAC bool_ss [MAP,ALL_DISTINCT,pairTheory.FST,xR_list_sem_def,xR_list_def]
    \\ ASM_REWRITE_TAC [GSYM STAR_ASSOC,xR_list_lemma]
    \\ `LIST_TO_SET (q::MAP FST xs) SUBSET rs =
        q IN rs /\ LIST_TO_SET (MAP FST xs) SUBSET rs` by 
       (SIMP_TAC bool_ss [SUBSET_DEF,IN_LIST_TO_SET,MEM] \\ METIS_TAC [])
    \\ `rs DIFF LIST_TO_SET (q::MAP FST xs) =
        rs DELETE q DIFF LIST_TO_SET (MAP FST xs)` by
      SIMP_TAC bool_ss [EXTENSION,IN_DIFF,IN_DELETE,CONJ_ASSOC,IN_LIST_TO_SET,MEM]
    \\ `LIST_TO_SET (MAP FST xs) SUBSET rs DELETE q =
        ~MEM q (MAP FST xs) /\ LIST_TO_SET (MAP FST xs) SUBSET rs` by
       (SIMP_TAC bool_ss [SUBSET_DEF,IN_DELETE,IN_LIST_TO_SET] \\ METIS_TAC [])
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC bool_ss []]);

val _ = Hol_datatype `
  xM_option = xM_seq of word30 # word32 list | 
              xM_blank of word30 # num |
              xM_byte of word32 # (word8 option)`;

val xM_list_def = Define `
  (xM_list [] = emp) /\
  (xM_list (xM_blank (a,n) ::xs) = blank_ms a n * xM_list xs) /\
  (xM_list (xM_seq (a,x) ::xs) = ms a x * xM_list xs) /\
  (xM_list (xM_byte (b,SOME y) ::xs) = byte b y * xM_list xs) /\
  (xM_list (xM_byte (b,NONE) ::xs) = ~ byte b * xM_list xs)`;

val ms_sem_def = Define `
  (ms_sem a [] s = T) /\ 
  (ms_sem a (x::xs) s = (mem a s = x) /\ ms_sem (a+1w) xs s)`;

val xM_list_sem_def = Define `
  (xM_list_sem [] s = T) /\
  (xM_list_sem ((xM_byte (b,SOME y))::xs) s = (mem_byte b s = y) /\ xM_list_sem xs s) /\
  (xM_list_sem ((xM_byte (b,NONE))::xs) s = xM_list_sem xs s) /\
  (xM_list_sem ((xM_blank (a,n))::xs) s = n <= 2**30 /\ xM_list_sem xs s) /\
  (xM_list_sem ((xM_seq (a,x))::xs) s = 
     ms_sem a x s /\ LENGTH x <= 2**30 /\ xM_list_sem xs s)`;

val xM_list_addresses_def = Define `
  (xM_list_addresses [] = []) /\
  (xM_list_addresses ((xM_byte (b,m))::xs) = 
    {b} :: xM_list_addresses xs) /\
  (xM_list_addresses ((xM_blank (a,n))::xs) = 
    ms_address_set a n :: xM_list_addresses xs) /\
  (xM_list_addresses ((xM_seq (a,x))::xs) = 
    ms_address_set a (LENGTH x) :: xM_list_addresses xs)`;

val xM_list_address_set_def = Define `
  xM_list_address_set xs = FOLDR $UNION EMPTY (xM_list_addresses xs)`;

val ALL_DISJOINT_def = Define `
  (ALL_DISJOINT [] = T) /\
  (ALL_DISJOINT (x::xs) = EVERY (\y. DISJOINT x y) xs /\ ALL_DISJOINT xs)`;

val IN_ms_address_set_ADD1 = prove(
  ``!xs a b. a IN (ms_address_set b xs) = (a+4w) IN (ms_address_set (b+1w) xs)``,
  Induct
  \\ SIMP_TAC std_ss [ms_address_set_def,NOT_IN_EMPTY,IN_INSERT]
  \\ REWRITE_TAC [addr32_ADD,GSYM WORD_ADD_ASSOC,addr32_n2w,EVAL ``4*1``]
  \\ REWRITE_TAC [METIS_PROVE [WORD_ADD_COMM,WORD_ADD_ASSOC] ``a+(b+c)=(a+c)+b:'a word``]  
  \\ REWRITE_TAC [WORD_EQ_ADD_RCANCEL]
  \\ POP_ASSUM (fn thm => REWRITE_TAC [GSYM thm]));

val xM_list_lemma_LEMMA1 = prove(
  ``!a n ns. ~(addr32 a IN ms_address_set (a + 1w) n) ==> SUC n <= 2 ** 30``,
  Cases \\ REWRITE_TAC [IN_ms_address_set,word_add_n2w,addr32_n2w]
  \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``m:num``))
  \\ FULL_SIMP_TAC (bool_ss++wordsLib.SIZES_ss) [dimword_def] \\ REPEAT STRIP_TAC
  \\ CCONTR_TAC \\ `2 ** 30 <= m` by DECIDE_TAC  
  \\ `4 * 2**30 <= 4 * m` by ASM_SIMP_TAC std_ss [EVAL ``0 < 4``,LE_MULT_LCANCEL]
  \\ `4 * 2**30 - 4 < 4 * m` by DECIDE_TAC
  \\ `4 * 2 ** 30 = 2**32` by EVAL_TAC
  \\ Q.PAT_ASSUM `!k.b` (ASSUME_TAC o Q.SPEC `2**32-4`)
  \\ FULL_SIMP_TAC bool_ss [ADD1,LEFT_ADD_DISTRIB,GSYM ADD_ASSOC] THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC (bool_ss++wordsLib.SIZES_ss) [EVAL ``4 * 1 + (2 ** 32 - 4)``,n2w_11] 
  \\ FULL_SIMP_TAC bool_ss [EVAL ``2 * 2147483648``,ADD_MODULUS_LEFT,EVAL ``0 < 4294967296``]);

val xM_list_lemma_LEMMA2 = prove(
  ``!a n ns. SUC n <= 2 ** 30 ==> 
             ~(addr32 a + 0w IN ms_address_set (a + 1w) n) /\ 
             ~(addr32 a + 1w IN ms_address_set (a + 1w) n) /\ 
             ~(addr32 a + 2w IN ms_address_set (a + 1w) n) /\ 
             ~(addr32 a + 3w IN ms_address_set (a + 1w) n)``,
  SIMP_TAC bool_ss [IN_ms_address_set] \\ REPEAT STRIP_TAC
  \\ Cases_on `k < 4 * n` 
  \\ ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC,addr32_n2w,word_add_n2w,addr32_ADD,WORD_EQ_ADD_LCANCEL,EVAL ``4*1``]
  \\ `4 * SUC n <= 4 * 2**30` by ASM_SIMP_TAC bool_ss [EVAL ``0<4``,LE_MULT_LCANCEL] 
  \\ `k + 4 < 4 * n + 4` by ASM_SIMP_TAC bool_ss [LT_ADD_RCANCEL]
  \\ FULL_SIMP_TAC bool_ss [ADD1,LEFT_ADD_DISTRIB,EVAL ``4*1``,EVAL ``4 * 2 ** 30``]
  \\ `k + 4 < 4294967296` by METIS_TAC [LESS_LESS_EQ_TRANS]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ `0 < 4294967296 /\ 1 < 4294967296 /\ 2 < 4294967296 /\ 3 < 4294967296` by EVAL_TAC
  \\ FULL_SIMP_TAC (bool_ss++wordsLib.SIZES_ss) [n2w_11,EVAL ``2 * 2147483648``,LESS_MOD]
  \\ DECIDE_TAC);

val xM_list_lemma1 = prove(
  ``!xs a rs ns st ud rt P.
      ((ms a xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       (ms_sem a xs s) /\ LENGTH xs <= 2**30 /\
       ms_address_set a (LENGTH xs) SUBSET ns /\ 
       P (arm2set' (rs,ns DIFF ms_address_set a (LENGTH xs),st,ud,rt) s))``,
  Induct THEN1 SRW_TAC [sep_ss] [ms_def,ms_sem_def,ms_address_set_def]
  \\ REWRITE_TAC [ms_def,ms_sem_def,GSYM STAR_ASSOC,M_STAR,LENGTH]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [IN_arm2set',INSERT_SUBSET,EMPTY_SUBSET]
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_arm2set',DIFF_EMPTY] 
  \\ `!a1 a2 a3 a4 b1 b2 b3 b4.
       (a1 /\ b1) /\ (a2 /\ b2) /\ (a3 /\ b3) /\ (a4 /\ b4) =
       (a1/\a2/\a3/\a4) /\ (b1/\b2/\b3/\b4):bool` by 
          (REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_REWRITE_TAC [mem_byte_EQ_mem]
  \\ Cases_on `~(mem a s = h)` THEN1 ASM_REWRITE_TAC []
  \\ `h = mem a s` by METIS_TAC [] 
  \\ ASM_REWRITE_TAC [GSYM mem_byte_addr32,DELETE_arm2set',ms_address_set_def]
  \\ ONCE_REWRITE_TAC [METIS_PROVE [INSERT_COMM]
    ``x INSERT y INSERT z INSERT v INSERT s = v INSERT z INSERT y INSERT x INSERT s``]
  \\ REWRITE_TAC [DIFF_INSERT,INSERT_SUBSET,SUBSET_DELETE]
  \\ POP_ASSUM_LIST (fn thms => ALL_TAC)
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC
  THEN1 METIS_TAC [xM_list_lemma_LEMMA1,WORD_ADD_0]
  \\ IMP_RES_TAC xM_list_lemma_LEMMA2 \\ ASM_REWRITE_TAC [] \\ DECIDE_TAC);

val xM_list_lemma2 = prove(
  ``!n a rs ns st ud rt P.
      ((blank_ms a n * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       n <= 2**30 /\ ms_address_set a n SUBSET ns /\ 
       P (arm2set' (rs,ns DIFF ms_address_set a n,st,ud,rt) s))``,
  Induct THEN1 SRW_TAC [sep_ss] [blank_ms_def,ms_sem_def,ms_address_set_def]
  \\ REWRITE_TAC [blank_ms_def,GSYM STAR_ASSOC,M_STAR,LENGTH]
  \\ REWRITE_TAC [SEP_HIDE_THM,SEP_EXISTS_ABSORB_STAR,SEP_EXISTS_THM]
  \\ ONCE_REWRITE_TAC [GSYM (BETA_CONV ``(\v. M a v * (blank_ms (a + 1w) n * P)) v``)] 
  \\ REWRITE_TAC [SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss []))
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [IN_arm2set',INSERT_SUBSET,EMPTY_SUBSET,M_STAR]
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_arm2set',DIFF_EMPTY] 
  \\ `!a1 a2 a3 a4 b1 b2 b3 b4.
       (a1 /\ b1) /\ (a2 /\ b2) /\ (a3 /\ b3) /\ (a4 /\ b4) =
       (a1/\a2/\a3/\a4) /\ (b1/\b2/\b3/\b4):bool` by 
          (REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_REWRITE_TAC [mem_byte_EQ_mem] \\ SIMP_TAC std_ss []
  \\ ASM_REWRITE_TAC [GSYM mem_byte_addr32,DELETE_arm2set',ms_address_set_def]
  \\ ONCE_REWRITE_TAC [METIS_PROVE [INSERT_COMM]
    ``x INSERT y INSERT z INSERT v INSERT s = v INSERT z INSERT y INSERT x INSERT s``]
  \\ REWRITE_TAC [DIFF_INSERT,INSERT_SUBSET,SUBSET_DELETE]
  \\ POP_ASSUM_LIST (fn thms => ALL_TAC)
  \\ REWRITE_TAC [GSYM (EVAL ``2**30``)]
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss [] \\ STRIP_TAC 
  THEN1 METIS_TAC [xM_list_lemma_LEMMA1,WORD_ADD_0]
  \\ IMP_RES_TAC xM_list_lemma_LEMMA2 \\ ASM_REWRITE_TAC [] \\ DECIDE_TAC);

val xM_list_lemma3 = prove(
  ``!n a rs ns st ud rt P.
      ((byte b y * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       (mem_byte b s = y) /\ b IN ns /\ P (arm2set' (rs,ns DELETE b,st,ud,rt) s))``,
  REWRITE_TAC [byte_def,one_STAR,IN_arm2set']
  \\ Cases_on `~(y = mem_byte b s)` \\ FULL_SIMP_TAC bool_ss [DELETE_arm2set']);

val xM_list_lemma3' = prove(
  ``!n a rs ns st ud rt P.
      ((~byte b * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       b IN ns /\ P (arm2set' (rs,ns DELETE b,st,ud,rt) s))``,
  REWRITE_TAC [SEP_HIDE_THM,SEP_EXISTS_ABSORB_STAR,SEP_EXISTS_THM]
  \\ ONCE_REWRITE_TAC [GSYM (BETA_CONV ``(\v. byte b v * P) v``)] 
  \\ REWRITE_TAC [SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss []))
  \\ REWRITE_TAC [byte_def,one_STAR,IN_arm2set'] 
  \\ FULL_SIMP_TAC bool_ss [DELETE_arm2set']);

val EVERY_DISJOINT = prove(
  ``!xs x. EVERY (\y. DISJOINT x y) xs = DISJOINT x (FOLDR $UNION {} xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,FOLDR,DISJOINT_EMPTY]
  \\ SRW_TAC [] [DISJOINT_DEF,EXTENSION] \\ METIS_TAC []);

val xM_list_thm = prove(
  ``!xs P rs ns st ud rt.
      ((xM_list xs * P) (arm2set' (rs,ns,st,ud,rt) s) = 
       xM_list_sem xs s /\ ALL_DISJOINT (xM_list_addresses xs) /\ 
       P (arm2set' (rs,ns DIFF (xM_list_address_set xs),st,ud,rt) s) /\
       xM_list_address_set xs SUBSET ns)``,
  Induct
  THEN1 SRW_TAC [sep_ss] [xM_list_def,xM_list_sem_def,MAP,ALL_DISJOINT_def,
                          xM_list_address_set_def,xM_list_addresses_def]
  \\ `!x y z:word32 set. 
      DISJOINT x y /\ x UNION y SUBSET z = y SUBSET z DIFF x /\ x SUBSET z` by
        (SRW_TAC [] [SUBSET_DEF,DISJOINT_DEF,EXTENSION] \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ Cases_on `h` \\ Cases_on `p` \\ Cases_on `r`
  \\ SIMP_TAC bool_ss [MAP,ALL_DISJOINT_def,pairTheory.FST,xM_list_sem_def,xM_list_def,
                       xM_list_addresses_def,xM_list_address_set_def,FOLDR]
  \\ FULL_SIMP_TAC bool_ss [GSYM xM_list_address_set_def]
  \\ ASM_SIMP_TAC std_ss [xM_list_lemma1,xM_list_lemma2,
                          xM_list_lemma3,xM_list_lemma3',GSYM STAR_ASSOC]
  \\ REWRITE_TAC [INSERT_UNION_COMM,UNION_EMPTY,INSERT_SUBSET,SUBSET_DELETE,DIFF_INSERT]
  \\ SIMP_TAC bool_ss [EVERY_DISJOINT,GSYM xM_list_address_set_def,DISJOINT_SING] 
  \\ ASM_REWRITE_TAC [prove(``!x:'a set y z. x DIFF y DIFF z = x DIFF (y UNION z)``, 
                      SRW_TAC [] [EXTENSION,IN_UNION,IN_DIFF,CONJ_ASSOC])]
  \\ EQ_TAC \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val rest_list_def = Define `
  rest_list (st,ud,rt,cd) (x,y,z,b) = 
    (if st then S x else emp) * 
    (if ud then one (Undef y) else emp) * 
    (if rt then one (Rest z) else emp) * 
    (if cd then cond b else emp)`;

val rest_list_sem_def = Define `
  rest_list_sem (st,ud,rt,cd) (x,y,z,b) s = 
    (if st then (status s = x) else T) /\ 
    (if ud then (s.undefined = y) else T) /\
    (if rt then (owrt_visible s = z) else T) /\ 
    (if cd then b else T)`;

val rest_list_thm = prove(
  ``!st ud rt cd x y z b P rs ns st' ud' rt'. 
      (rest_list (st,ud,rt,cd) (x,y,z,b) * P) (arm2set' (rs,ns,st',ud',rt') s) = 
      rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
      (st ==> st') /\ (ud ==> ud') /\ (rt ==> rt') /\
      P (arm2set' (rs,ns,~st /\ st',~ud /\ ud',~rt /\ rt') s)``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [rest_list_def,rest_list_sem_def,
       prove(``!cd b. (if cd then cond b else emp) = cond (cd ==> b)``,SRW_TAC [sep_ss][])] 
  \\ Cases_on `st` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `x = status s` 
  \\ Cases_on `ud` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `y = s.undefined` 
  \\ Cases_on `rt` \\ SIMP_TAC (bool_ss++sep_ss) [] \\ Cases_on `z = owrt_visible s` 
  \\ ASM_SIMP_TAC bool_ss [GSYM STAR_ASSOC,S_def,one_STAR,IN_arm2set',DELETE_arm2set',cond_STAR]
  \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss []);

val emp_list_thm = prove(
  ``!s rs ns st ud rt.
       emp (arm2set' (rs,ns,st,ud,rt) s) = (rs = {}) /\ (ns = {}) /\ ~st /\ ~ud /\ ~rt``,
  SIMP_TAC std_ss [emp_def,arm2set'_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `st` THEN1 SRW_TAC [] [EXTENSION]
  \\ Cases_on `ud` THEN1 SRW_TAC [] [EXTENSION]
  \\ Cases_on `rt` THEN1 SRW_TAC [] [EXTENSION]
  \\ SRW_TAC [] [EXTENSION,GSPECIFICATION]);

val rest_emp_list_thm = prove(
  ``!st ud rt xs x y z b P rs ns st' ud' rt'. 
      (rest_list (st,ud,rt,cd) (x,y,z,b)) (arm2set' (rs,ns,st',ud',rt') s) = 
      rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
      (rs = {}) /\ (ns = {}) /\ (st = st') /\ (ud = ud') /\ (rt = rt')``,
  REPEAT STRIP_TAC  
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV o RATOR_CONV) 
               (ONCE_REWRITE_CONV [(GSYM o CONJUNCT2 o SPEC_ALL) emp_STAR]))
  \\ REWRITE_TAC [rest_list_thm,emp_list_thm]
  \\ Cases_on `st` \\ Cases_on `st'` \\ Cases_on `ud` \\ Cases_on `ud'`
  \\ Cases_on `rt` \\ Cases_on `rt'` \\ SIMP_TAC bool_ss []);

val spec_list_def = Define `
  spec_list xs ys (st,x) (ud,y) (rt,z) (cd,b) = 
    xR_list xs * xM_list ys * rest_list (st,ud,rt,cd) (x,y,z,b)`;

val spec_list_select_def = Define `
  spec_list_select (xs,ys,st,ud,rt) =
    (LIST_TO_SET (MAP FST xs),xM_list_address_set ys,st,ud,rt)`;
  
val spec_list_sem_def = Define `
  spec_list_sem xs ys (st,x) (ud,y) (rt,z) (cd,b) q s =
    xR_list_sem xs s /\ xM_list_sem ys s /\ rest_list_sem (st,ud,rt,cd) (x,y,z,b) s /\ 
    ALL_DISTINCT (MAP FST xs) /\ ALL_DISJOINT (xM_list_addresses ys) /\
    (q = spec_list_select (xs,ys,st,ud,rt))`;
  
val spec_list_thm = store_thm("spec_list_thm",
  ``!xs ys st ud rt cd q s.
      (spec_list xs ys st ud rt cd) (arm2set' q s) = 
      spec_list_sem xs ys st ud rt cd q s``,
  REPEAT STRIP_TAC
  \\ `?rs ns st' ud' rt'. q = (rs,ns,st',ud',rt')` by METIS_TAC [pairTheory.PAIR]
  \\ `?st' x. st = (st',x)` by METIS_TAC [pairTheory.PAIR]
  \\ `?ud' y. ud = (ud',y)` by METIS_TAC [pairTheory.PAIR]
  \\ `?rt' z. rt = (rt',z)` by METIS_TAC [pairTheory.PAIR]
  \\ `?cd' b. cd = (cd',b)` by METIS_TAC [pairTheory.PAIR]
  \\ ASM_SIMP_TAC bool_ss [spec_list_def,GSYM STAR_ASSOC,xR_list_thm,xM_list_thm]
  \\ ASM_SIMP_TAC bool_ss [rest_emp_list_thm,
       prove(``(x DIFF y = {}) = x SUBSET y``,
       SRW_TAC [] [EXTENSION,SUBSET_DEF] \\ METIS_TAC [])]
  \\ REWRITE_TAC [spec_list_sem_def,pairTheory.PAIR_EQ,spec_list_select_def]
  \\ REWRITE_TAC [SET_EQ_SUBSET,GSYM CONJ_ASSOC]
  \\ EQ_TAC \\ SIMP_TAC std_ss []);

(* function for instantiation *)

val LIST_TO_SET_CLAUSES = prove(
  ``!x xs. (LIST_TO_SET [] = {}) /\ (LIST_TO_SET (x::xs) = x INSERT LIST_TO_SET xs)``,
  SRW_TAC [] [EXTENSION]);

val UNION_APPEND = prove(
  ``!x y z. (x INSERT y) UNION z = x INSERT (y UNION z)``,
  SRW_TAC [] [EXTENSION,DISJ_ASSOC]);

val spec_list_expand_ss = rewrites 
  [spec_list_def,xR_list_def,xM_list_def,rest_list_def,spec_list_sem_def,
   xR_list_sem_def,xM_list_sem_def,rest_list_sem_def,ms_sem_def,
   xM_list_addresses_def,ms_address_set_def,LIST_TO_SET_CLAUSES,spec_list_select_def,
   xM_list_address_set_def,FOLDR,UNION_EMPTY,UNION_APPEND,GSYM CONJ_ASSOC,ms_def,
   MAP,FST,STAR_ASSOC,EVAL ``SUC 0 <= 2**30``,LENGTH,blank_ms_def];

fun sep_pred_semantics (xs,ys,st,ud,rt,cd) = let
  val th = Q.SPECL [xs,ys,st,ud,rt,cd] spec_list_thm
  val th = SIMP_RULE (bool_ss++sep_ss++spec_list_expand_ss) [] th
  in th end;

(* example *)

val xs = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3);(a4,NONE);(a5,NONE);(a6,NONE)]`;
val ys = `[xM_seq (b1,[y1]);xM_seq (b2,[y2]);xM_seq (b3,y3);xM_blank (b4,SUC 0);xM_byte (b5,SOME 5w)]`;
val st = `(T,st)`;
val ud = `(T,ud)`;
val rt = `(F,rt)`;
val cd = `(T,g)`;
val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);


(* ----------------------------------------------------------------------------- *)
(* CLEANING INSTRUCTION RULES                                                    *)
(* ----------------------------------------------------------------------------- *)

val reg_rw = prove(
  ``(!s. s.registers r15 = reg 15w s) /\ 
    !x s. ~(x = 15w) ==> (REG_READ s.registers (state_mode s) x = reg x s)``,
  SRW_TAC [] [reg_def]);

val contract_ss = rewrites ([NZCV_def,reg_rw] @ map GSYM
  [mem_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def,addr30_def,
   state_mode_def]);

fun PAT_DISCH tm th = DISCH (hd (filter (can_match tm) (hyp th))) th;
fun PAT_DISCH_LIST tms th = foldr (uncurry PAT_DISCH) th tms;

fun simple_clean th tms = let
  val th = SPEC_ALL th
  val th = Q.INST [`s:bool`|->`s_flag:bool`] th
  val th = Q.INST [`state`|->`s`] th 
  val th = ASM_UNABBREV_ALL_RULE (UD_ALL th)
  val th = foldr (uncurry DISCH) th tms
  val th = (UNDISCH_ALL o SIMP_RULE (bool_ss++contract_ss) [] o DISCH_ALL) th
  val tm1 = ``~(s:^(ty_antiq arm_state_type)).undefined``
  val tm2 = ``CONDITION_PASSED2 (status (s:^(ty_antiq arm_state_type))) c``
  val tm3 = ``mem (addr30 p) (s:^(ty_antiq arm_state_type)) = enc cmd``
  val th = PAT_DISCH_LIST ([tm1,tm2,tm3] @ tms) th
  in SET_NO_CP th end;


(* ----------------------------------------------------------------------------- *)
(* LDM and STM INSTRUCTIONS                                                      *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  abbrev_addr4 = am4_DA of bool | am4_IA of bool | am4_DB of bool | am4_IB of bool |
                 am4_FA of bool | am4_FD of bool | am4_EA of bool | am4_ED of bool`;

val ADDR_MODE4_CMD_def = Define `
  (ADDR_MODE4_CMD (am4_DA wb) = <| Pre:=F; Up:=F; Wb:=wb |>) /\ 
  (ADDR_MODE4_CMD (am4_FA wb) = <| Pre:=F; Up:=F; Wb:=wb |>) /\ 
  (ADDR_MODE4_CMD (am4_IA wb) = <| Pre:=F; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_FD wb) = <| Pre:=F; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_DB wb) = <| Pre:=T; Up:=F; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_EA wb) = <| Pre:=T; Up:=F; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_IB wb) = <| Pre:=T; Up:=T; Wb:=wb |>) /\
  (ADDR_MODE4_CMD (am4_ED wb) = <| Pre:=T; Up:=T; Wb:=wb |>)`;

val reg_bitmap_def = Define `
  reg_bitmap (xs:word4 list) = (FCP i. MEM (n2w i) xs):word16`;

val MEM_EQ_EXISTS = prove(
  ``!xs. MEM x xs = ?ys zs. xs = ys ++ [x] ++ zs``,
  Induct THEN1 SRW_TAC [] [] 
  \\ ASM_REWRITE_TAC [MEM] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `xs` \\ SRW_TAC [] [])
  THEN1 (Q.EXISTS_TAC `h::ys` \\ Q.EXISTS_TAC `zs` \\ ASM_REWRITE_TAC [APPEND])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC bool_ss [APPEND,CONS_11] \\ METIS_TAC []);

val MEM_MAP_FILTER = prove(
  ``!x xs. MEM x ((MAP SND o FILTER FST) xs) = MEM (T,x) xs``,        
  Induct_on `xs` THEN1 SRW_TAC [] [] 
  \\ Cases_on `h` \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [FILTER,MAP,MEM]);

val MEM_SNOC = prove(
  ``!xs x y. MEM x (SNOC y xs) = MEM x (CONS y xs)``,
  Induct_on `xs` \\ SRW_TAC [] [MEM,SNOC] \\ METIS_TAC []);

val MEM_GENLIST = prove(
  ``!n x f. MEM x (GENLIST f n) = ?i. i < n /\ (x = f i)``,
  Induct THEN1 SIMP_TAC std_ss [MEM,GENLIST]
  \\ SRW_TAC [] [MEM,GENLIST,MEM_SNOC]
  \\ Cases_on `x = f n` \\ ASM_REWRITE_TAC []
  THEN1 (Q.EXISTS_TAC `n` \\ SRW_TAC [] [])
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `i` \\ METIS_TAC [LESS_TRANS,LESS_EQ_IMP_LESS_SUC,LESS_EQ_REFL],
    Cases_on `i = n` THEN1 METIS_TAC [] \\ `i < n` by DECIDE_TAC \\ METIS_TAC []]);

val MEM_PAIR_GENLIST = prove(
  ``!n x f g. 
       MEM (T,x) (GENLIST (\i. (f i, g i)) n) = ?i. i < n /\ f i /\ (x = g i)``,
  SRW_TAC [] [MEM_GENLIST]);

val w2n_FCP_BETA = let
  val th' = Q.INST_TYPE [`:'a`|->`:4`] w2n_lt
  val th' = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th'
  val th = Q.SPEC `w2n (x:word4)` fcpTheory.FCP_BETA
  val th = Q.INST_TYPE [`:'b`|->`:16`] th
  val th = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] th
  in MP th (Q.SPEC `x` th') end;

val MEM_reg_bitmap = prove(
  ``!x xs. MEM x xs = reg_bitmap xs %% w2n x``,
  SIMP_TAC std_ss [reg_bitmap_def,w2n_FCP_BETA,n2w_w2n]);

val MEM_REGISTER_LIST_reg_bitmap = store_thm("MEM_REGISTER_LIST_reg_bitmap",
  ``!xs x. MEM x (REGISTER_LIST (reg_bitmap xs)) = MEM x xs``,  
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [REGISTER_LIST_def,MEM_MAP_FILTER]
  \\ REWRITE_TAC [MEM_reg_bitmap]
  \\ REWRITE_TAC [MEM_PAIR_GENLIST]
  \\ ASSUME_TAC (Q.INST_TYPE [`:'a`|->`:4`] w2n_lt)
  \\ EQ_TAC \\ STRIP_TAC \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2n_n2w]
  \\ Q.EXISTS_TAC `w2n (x:word4)` \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_w2n]);

val SNOC_CONS = prove(
  ``!xs x y. SNOC x (y::xs) = y::(SNOC x xs)``,Induct \\ ASM_REWRITE_TAC [SNOC]);
  
val FILTER_SNOC = prove(
  ``!xs x P. FILTER P (SNOC x xs) = if P x then SNOC x (FILTER P xs) else FILTER P xs``,  
  Induct \\ ASM_REWRITE_TAC [SNOC,FILTER] \\ SRW_TAC [] [SNOC_CONS]);

val MAP_SNOC = prove(
  ``!xs x f. MAP f (SNOC x xs) = SNOC (f x) (MAP f xs)``,
  Induct \\ ASM_REWRITE_TAC [SNOC,MAP] \\ SRW_TAC [] [SNOC_CONS]);
    
val SORTED_SNOC_SNOC = prove(
  ``!xs f x y. SORTED f (SNOC x (SNOC y xs)) = f y x /\ SORTED f (SNOC y xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `xs`
  \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF] \\ METIS_TAC []);

val SORTED_REGISTER_LIST_LEMMA = prove(
  ``!k g:word16. 
      k <= 16 ==> 
      SORTED $<+ ((MAP SND o FILTER FST) (GENLIST (\i. (g %% i,(n2w i):word4)) k))``,
  Induct 
  \\ SIMP_TAC std_ss [GENLIST,FILTER,MAP,SORTED_DEF,FILTER_SNOC]
  \\ REPEAT STRIP_TAC \\ Cases_on `g %% k` 
  \\ `k <= 16` by DECIDE_TAC
  \\ PAT_ASSUM ``!g'. b`` (ASSUME_TAC o UNDISCH o Q.SPEC `g`)
  \\ FULL_SIMP_TAC std_ss [MAP_SNOC]
  \\ STRIP_ASSUME_TAC (Q.ISPEC `MAP SND (FILTER FST 
       (GENLIST (\i. ((g:word16) %% i,((n2w i):word4))) k))` SNOC_CASES)
  \\ FULL_SIMP_TAC std_ss [SNOC,SORTED_DEF,SORTED_SNOC_SNOC]
  \\ `!xs. MEM x (SNOC x xs)` by (Induct \\ SRW_TAC [] [MEM,SNOC])
  \\ `MEM x (MAP SND (FILTER FST (GENLIST (\i. (g %% i,n2w i)) k)))` by METIS_TAC [] 
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,MEM_FILTER,MEM_GENLIST]
  \\ `k < 16 /\ i < 16` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [word_lo_n2w]);

val SORTED_REGISTER_LIST = store_thm("SORTED_REGSITER_LIST",
  ``!g. SORTED $<+ (REGISTER_LIST g)``,
  REWRITE_TAC [REGISTER_LIST_def]
  \\ MATCH_MP_TAC (SPEC_ALL SORTED_REGISTER_LIST_LEMMA) \\ DECIDE_TAC);

val SORTED_CONS_IMP = prove(
  ``!xs h. SORTED $<+ (h::xs) ==> SORTED $<+ xs /\ ~(MEM h xs) /\ EVERY (\x. h <+ x) xs``,
  Induct \\ SRW_TAC [] [MEM,SORTED_DEF] THEN1 METIS_TAC [WORD_NOT_LOWER_EQ]
  \\ `SORTED $<+ (h'::xs)` by (Cases_on `xs` \\ METIS_TAC [SORTED_DEF,WORD_LOWER_TRANS])
  \\ METIS_TAC []);

val SORTED_LO_IMP_EQ = store_thm("SORTED_LOWER_IMP_EQ",
  ``!xs ys. SORTED $<+ xs /\ SORTED $<+ ys /\ (!x. MEM x xs = MEM x ys) ==> (xs = ys)``,
  Induct THEN1 (Cases_on `ys` \\ SRW_TAC [] [MEM] \\ METIS_TAC [])
  \\ REWRITE_TAC [MEM] \\ REPEAT STRIP_TAC 
  \\ `MEM h ys` by METIS_TAC []
  \\ `?hs zs. ys = hs ++ [h] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ Q.PAT_ASSUM `!ys. b ==> (c:bool)` (ASSUME_TAC o Q.SPEC `zs`)
  \\ Cases_on `hs` \\ FULL_SIMP_TAC std_ss [CONS_11,APPEND,MEM]
  THEN1 METIS_TAC [SORTED_CONS_IMP]
  \\ IMP_RES_TAC SORTED_CONS_IMP
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM,EVERY_APPEND,EVERY_DEF]
  \\ `MEM h' xs` by METIS_TAC []
  \\ `?hs' zs'. xs = hs' ++ [h'] ++ zs'` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [EVERY_APPEND,EVERY_DEF] \\ METIS_TAC [WORD_LOWER_ANTISYM]);

val LEAST_MEM_def = Define `
  (LEAST_MEM [x] = x) /\ 
  (LEAST_MEM (x::y::ys) = 
     let m = LEAST_MEM (y::ys) in if x <=+ m then x else m)`;

val LENGTH_FILTER = prove(
  ``!xs P. LENGTH (FILTER P xs) <= LENGTH xs ``,
  Induct \\ SIMP_TAC std_ss [FILTER,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ ASM_REWRITE_TAC [LENGTH] 
  \\ PAT_ASSUM ``!P:'a. b:bool`` (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC );

val LEAST_SORT_LEMMA = prove(
  ``!xs m. MEM m xs ==> LENGTH (FILTER (\x. ~(x = m)) xs) < LENGTH xs``,
  Induct THEN1 SRW_TAC [] []
  \\ SIMP_TAC std_ss [MEM,FILTER,LENGTH] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `h = m` \\ ASM_REWRITE_TAC [LESS_EQ,DECIDE ``n < SUC m = n <= m``]
  THEN1 METIS_TAC [LENGTH_FILTER,LESS_LESS_EQ_TRANS]
  \\ `~(m = h)` by METIS_TAC [] \\ ASM_REWRITE_TAC [LENGTH,GSYM LESS_EQ]);

val MEM_LEAST_MEM = prove(
  ``!xs x. MEM (LEAST_MEM (x::xs)) (x::xs)``,
  Induct \\ ONCE_REWRITE_TAC [LEAST_MEM_def] \\ SIMP_TAC std_ss [LET_DEF]
  THEN1 REWRITE_TAC [MEM]
  \\ Cases_on `x <=+ LEAST_MEM (h::xs)` \\ ASM_REWRITE_TAC []
  THEN1 REWRITE_TAC [MEM] \\ ONCE_REWRITE_TAC [MEM] \\ ASM_REWRITE_TAC []);

val (LEAST_SORT_def,LEAST_SORT_ind) = let
  val d = Defn.Hol_defn "LEAST_SORT" `
    (LEAST_SORT [] = []) /\
    (LEAST_SORT (x::xs) = 
       let m = LEAST_MEM (x::xs) in 
         m :: LEAST_SORT (FILTER (\x. ~(x = m)) (x::xs)))`
  val tac = WF_REL_TAC `measure LENGTH` \\ METIS_TAC [LEAST_SORT_LEMMA,MEM_LEAST_MEM,MEM]
  in Defn.tprove (d,tac) end;

val _ = save_thm("LEAST_SORT_def",LEAST_SORT_def);

val MEM_LEAST_SORT = prove(
  ``!xs x. MEM x (LEAST_SORT xs) = MEM x xs``,
  recInduct LEAST_SORT_ind \\ REWRITE_TAC [LEAST_SORT_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `x' = LEAST_MEM (x::xs)`
  THEN1 (ASM_REWRITE_TAC [MEM_LEAST_MEM] \\ REWRITE_TAC [MEM])
  \\ CONV_TAC (RATOR_CONV (REWRITE_CONV [MEM])) \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `!m. b:bool` 
       (ASSUME_TAC o Q.SPEC `x'` o REWRITE_RULE [] o Q.SPEC `LEAST_MEM (x::xs)`)
  \\ ASM_SIMP_TAC std_ss [MEM_FILTER]);

val SORTED_EQ_LOWER = 
  (REWRITE_RULE [relationTheory.transitive_def,WORD_LOWER_TRANS] o Q.ISPEC `$<+`) SORTED_EQ;

val LEAST_MEM_IMP = prove(
  ``!xs x y. (y = LEAST_MEM (x::xs)) ==> !z. MEM z (x::xs) ==> (y = z) \/ (y <+ z)``,
  Induct \\ REWRITE_TAC [LEAST_MEM_def,MEM] THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [LET_DEF] \\ NTAC 3 STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o REWRITE_RULE [] o Q.SPECL [`h`,`LEAST_MEM (h::xs)`])    
  \\ Cases_on `z = x` \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `x <=+ LEAST_MEM (h::xs)` \\ ASM_REWRITE_TAC []
  THEN1 METIS_TAC [WORD_LOWER_CASES]
  \\ FULL_SIMP_TAC std_ss [MEM,WORD_LOWER_OR_EQ]
  \\ METIS_TAC [WORD_LOWER_TRANS]);

val LEAST_MEM_LOWER_EQ = prove(
  ``!xs x. MEM x xs ==> LEAST_MEM xs <=+ x``,
  Induct \\ SIMP_TAC std_ss [MEM,LEAST_MEM_def]
  \\ Cases_on `xs` \\ SIMP_TAC std_ss [LEAST_MEM_def,LET_DEF]
  THEN1 SRW_TAC [] [MEM,WORD_LOWER_EQ_REFL] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h'` \\ ASM_REWRITE_TAC []
  THEN1 METIS_TAC [WORD_LOWER_EQ_CASES]
  \\ Cases_on `h' <=+ LEAST_MEM (h::t)` \\ ASM_REWRITE_TAC []
  \\ METIS_TAC [WORD_LOWER_EQ_TRANS]);

val SORTED_LEAST_SORT = prove(
  ``!xs. SORTED $<+ (LEAST_SORT xs)``,
  recInduct LEAST_SORT_ind \\ SIMP_TAC std_ss 
    [LEAST_SORT_def,LET_DEF,SORTED_DEF,SORTED_EQ_LOWER,MEM_LEAST_SORT,MEM_FILTER]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC LEAST_MEM_LOWER_EQ
  \\ FULL_SIMP_TAC std_ss [WORD_LOWER_OR_EQ] \\ METIS_TAC [WORD_LOWER_REFL]);

val REGISTER_LIST_EQ_LEAST_SORT = prove(
  ``!xs. REGISTER_LIST (reg_bitmap xs) = LEAST_SORT xs``,
  STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ
  \\ REWRITE_TAC [MEM_REGISTER_LIST_reg_bitmap,MEM_LEAST_SORT,
                  SORTED_LEAST_SORT,SORTED_REGISTER_LIST]);

val ALL_DISTINCT_FILTER = prove(
  ``!xs. ALL_DISTINCT xs ==> !g. ALL_DISTINCT (FILTER g xs)``,
  Induct \\ REWRITE_TAC [ALL_DISTINCT,FILTER] \\ REPEAT STRIP_TAC
  \\ Cases_on `g h` \\ ASM_REWRITE_TAC [ALL_DISTINCT,MEM_FILTER] \\ METIS_TAC []);

val LENGTH_FILTER_NEQ = prove(
  ``!xs y. ALL_DISTINCT xs /\ MEM y xs ==> 
           (LENGTH (FILTER (\x. ~(x = y)) xs) = LENGTH xs - 1)``,
  Induct \\ SIMP_TAC bool_ss [MEM,FILTER,ALL_DISTINCT]
  \\ NTAC 2 STRIP_TAC \\ Cases_on `y = h` \\ ASM_REWRITE_TAC [LENGTH]
  \\ `!xs. ~MEM h xs ==> (FILTER (\x. ~(x = h)) xs = xs)` by (Induct \\ SRW_TAC [] [FILTER])
  \\ ASM_SIMP_TAC std_ss [ADD1,ADD_SUB,LENGTH]
  \\ Cases_on `xs` \\ REWRITE_TAC [MEM,LENGTH,ADD1,ADD_SUB]);

val LENGTH_LEAST_SORT = prove(
  ``!xs. ALL_DISTINCT xs ==> (LENGTH (LEAST_SORT xs) = LENGTH xs)``,
  recInduct LEAST_SORT_ind \\ SIMP_TAC std_ss [LENGTH,LEAST_SORT_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ALL_DISTINCT_FILTER
  \\ Q.PAT_ASSUM `!g.b:bool` (ASSUME_TAC o Q.SPEC `\x'. ~(x' = LEAST_MEM (x::xs))`)
  \\ FULL_SIMP_TAC bool_ss [] 
  \\ ASSUME_TAC (Q.SPECL [`xs`,`x`] MEM_LEAST_MEM)
  \\ IMP_RES_TAC LENGTH_FILTER_NEQ \\ ASM_REWRITE_TAC [LENGTH,ADD1,ADD_SUB]);


val PERM_IMP_MEM_EQUALITY = prove(
  ``!xs ys. PERM xs ys ==> !x. MEM x xs = MEM x ys``,
  REPEAT STRIP_TAC
  \\ `!xs. MEM x xs = ~(FILTER ($= x) xs = [])` by (Induct \\ SRW_TAC [] [MEM,FILTER])
  \\ FULL_SIMP_TAC bool_ss [PERM_DEF]);

val ALL_DISTINCT_MOVE_CONS = prove(
  ``!xs ys. ALL_DISTINCT (xs ++ h::ys) = ALL_DISTINCT (h::xs ++ ys)``,
  Induct \\ ASM_SIMP_TAC bool_ss [APPEND,APPEND_NIL] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [ALL_DISTINCT,APPEND,MEM_APPEND,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val PERM_ALL_DISTINCT = prove(
  ``!xs ys. ALL_DISTINCT xs /\ PERM xs ys ==> ALL_DISTINCT ys``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,ALL_DISTINCT,PERM_CONS_EQ_APPEND]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ IMP_RES_TAC PERM_IMP_MEM_EQUALITY
  \\ REWRITE_TAC [ALL_DISTINCT_MOVE_CONS,ALL_DISTINCT,APPEND] \\ METIS_TAC []);

val QSORT_SORTS_LS = prove(
  ``SORTS QSORT ($<=+ :'a word->'a word->bool)``,
  MATCH_MP_TAC QSORT_SORTS
  \\ REWRITE_TAC [transitive_def,total_def,WORD_LOWER_EQ_TRANS,WORD_LOWER_EQ_CASES]);

val SORTED_LO = prove(
  ``!xs. SORTED $<=+ xs /\ ALL_DISTINCT xs ==> SORTED $<+ (xs:'a word list)``,
  Induct \\ REWRITE_TAC [SORTED_DEF]
  \\ Cases_on `xs` \\ REWRITE_TAC [SORTED_DEF]
  \\ ONCE_REWRITE_TAC [ALL_DISTINCT]
  \\ REWRITE_TAC [MEM] \\ METIS_TAC [WORD_LOWER_OR_EQ]);

val ADDR_MODE4_UP_def = Define `
  (ADDR_MODE4_UP (am4_DA wb) = F) /\ 
  (ADDR_MODE4_UP (am4_FA wb) = F) /\ 
  (ADDR_MODE4_UP (am4_IA wb) = T) /\
  (ADDR_MODE4_UP (am4_FD wb) = T) /\
  (ADDR_MODE4_UP (am4_DB wb) = F) /\
  (ADDR_MODE4_UP (am4_EA wb) = F) /\
  (ADDR_MODE4_UP (am4_IB wb) = T) /\
  (ADDR_MODE4_UP (am4_ED wb) = T)`;

val ADDR_MODE4_wb_def = Define `
  (ADDR_MODE4_wb (am4_DA wb) = wb) /\ 
  (ADDR_MODE4_wb (am4_FA wb) = wb) /\ 
  (ADDR_MODE4_wb (am4_IA wb) = wb) /\
  (ADDR_MODE4_wb (am4_FD wb) = wb) /\
  (ADDR_MODE4_wb (am4_DB wb) = wb) /\
  (ADDR_MODE4_wb (am4_EA wb) = wb) /\
  (ADDR_MODE4_wb (am4_IB wb) = wb) /\
  (ADDR_MODE4_wb (am4_ED wb) = wb)`;

val ADDR_MODE4_WB'_def = Define `
  ADDR_MODE4_WB' am4 x n = 
    (if ADDR_MODE4_UP am4 then $+ else $-) x (n2w n)`;

val ADDR_MODE4_WB32'_def = Define `
  ADDR_MODE4_WB32' am4 x n = 
    (if ADDR_MODE4_UP am4 then $+ else $-) x (n2w (4 * n))`;

val ADDR_MODE4_WB_def = Define `
  ADDR_MODE4_WB am4 x xs = 
    if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x`;

val ADDR_MODE4_WB32_def = Define `
  ADDR_MODE4_WB32 am4 x xs = 
    if ADDR_MODE4_wb am4 then ADDR_MODE4_WB32' am4 x (LENGTH xs) else x`;

val ALL_DISTINCT_IMP_LENGTH_EQ = prove(
  ``!xs ys. ALL_DISTINCT xs /\ ALL_DISTINCT ys /\ (!x. MEM x xs = MEM x ys) ==>
            (LENGTH xs = LENGTH ys)``,
  Induct THEN1 (Cases_on `ys` \\ SRW_TAC [] [] \\ METIS_TAC [])
  \\ REWRITE_TAC [MEM] \\ REPEAT STRIP_TAC
  \\ `MEM h ys` by METIS_TAC []
  \\ `?hs zs. ys = hs ++ [h] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,ALL_DISTINCT_MOVE_CONS,MEM,MEM_APPEND]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM_APPEND,LENGTH,LENGTH_APPEND]
  \\ `!x. MEM x xs = MEM x (hs ++ zs)` by METIS_TAC [MEM_APPEND]
  \\ Q.PAT_ASSUM `!ys'. b ==> (c:bool)` IMP_RES_TAC  
  \\ ASM_REWRITE_TAC [ADD1,LENGTH_APPEND] \\ DECIDE_TAC);

val SORTED_LO_IMP_ALL_DISTINCT = prove(
  ``!xs. SORTED $<+ xs ==> ALL_DISTINCT xs``,
  Induct \\ REWRITE_TAC [SORTED_DEF,ALL_DISTINCT]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SORTED_CONS_IMP \\ METIS_TAC []);

val REGISTER_LIST_LENGTH = prove(
  ``!xs. ALL_DISTINCT xs ==> (LENGTH (REGISTER_LIST (reg_bitmap xs)) = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ALL_DISTINCT_IMP_LENGTH_EQ
  \\ ASM_SIMP_TAC std_ss [MEM_REGISTER_LIST_reg_bitmap]
  \\ MATCH_MP_TAC SORTED_LO_IMP_ALL_DISTINCT \\ REWRITE_TAC [SORTED_REGISTER_LIST]);

val ADDR_MODE4_UP_THM = prove(
  ``!am4. (ADDR_MODE4_CMD am4).Up = ADDR_MODE4_UP am4``,
  Cases_on `am4` \\ SRW_TAC [] [ADDR_MODE4_CMD_def,ADDR_MODE4_UP_def]);

val WB_ADDRESS_EQ_ADDR_MODE4_WB' = prove(
  ``!am4 x xs. ALL_DISTINCT xs ==> 
         (WB_ADDRESS (ADDR_MODE4_CMD am4).Up (addr32 x) 
             (LENGTH (REGISTER_LIST (reg_bitmap xs))) = 
          addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs)))``,
  REWRITE_TAC [ADDR_MODE4_def,ADDR_MODE4_WB'_def,WB_ADDRESS_def,UP_DOWN_def]
  \\ SIMP_TAC bool_ss [REGISTER_LIST_LENGTH,ADDR_MODE4_UP_THM] 
  \\ REPEAT STRIP_TAC \\ Cases_on `ADDR_MODE4_UP am4` 
  \\ ASM_REWRITE_TAC [addr32_ADD,addr32_SUB,addr32_n2w]);

val ADDR_MODE4_ADDR'_def = Define `
  (ADDR_MODE4_ADDR' (am4_DA wb) x y = y + 1w) /\ 
  (ADDR_MODE4_ADDR' (am4_FA wb) x y = y + 1w) /\ 
  (ADDR_MODE4_ADDR' (am4_IA wb) x y = x:word30) /\
  (ADDR_MODE4_ADDR' (am4_FD wb) x y = x) /\
  (ADDR_MODE4_ADDR' (am4_DB wb) x y = y) /\
  (ADDR_MODE4_ADDR' (am4_EA wb) x y = y) /\
  (ADDR_MODE4_ADDR' (am4_IB wb) x y = x + 1w) /\
  (ADDR_MODE4_ADDR' (am4_ED wb) x y = x + 1w)`;

val ADDR_MODE4_ADDR32'_def = Define `
  (ADDR_MODE4_ADDR32' (am4_DA wb) x y = y + 4w) /\ 
  (ADDR_MODE4_ADDR32' (am4_FA wb) x y = y + 4w) /\ 
  (ADDR_MODE4_ADDR32' (am4_IA wb) x y = x:word32) /\
  (ADDR_MODE4_ADDR32' (am4_FD wb) x y = x) /\
  (ADDR_MODE4_ADDR32' (am4_DB wb) x y = y) /\
  (ADDR_MODE4_ADDR32' (am4_EA wb) x y = y) /\
  (ADDR_MODE4_ADDR32' (am4_IB wb) x y = x + 4w) /\
  (ADDR_MODE4_ADDR32' (am4_ED wb) x y = x + 4w)`;

val ADDR_MODE4_ADDR'_THM = prove(
  ``!am4 x xs.
      ALL_DISTINCT xs ==>
      (FIRST_ADDRESS (ADDR_MODE4_CMD am4).Pre (ADDR_MODE4_CMD am4).Up
        (addr32 x) (addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs))) =
       addr32 (ADDR_MODE4_ADDR' am4 x (ADDR_MODE4_WB' am4 x (LENGTH xs))))``,
  Cases \\ SRW_TAC [] [ADDR_MODE4_ADDR'_def,FIRST_ADDRESS_def,ADDR_MODE4_CMD_def,addr32_SUC]);

val ADDR_MODE4_ADDR32'_THM = prove(
  ``!am4 x xs.
      ALL_DISTINCT xs ==>
      (FIRST_ADDRESS (ADDR_MODE4_CMD am4).Pre (ADDR_MODE4_CMD am4).Up
        x (ADDR_MODE4_WB32' am4 x (LENGTH xs)) =
       ADDR_MODE4_ADDR32' am4 x (ADDR_MODE4_WB32' am4 x (LENGTH xs)))``,
  Cases \\ SRW_TAC [] [ADDR_MODE4_ADDR32'_def,FIRST_ADDRESS_def,ADDR_MODE4_CMD_def,addr32_SUC]);

val ADDR_MODE4_ADDR_def = Define `
  ADDR_MODE4_ADDR am4 x xs = ADDR_MODE4_ADDR' am4 x (ADDR_MODE4_WB' am4 x (LENGTH xs))`;

val ADDR_MODE4_ADDR32_def = Define `
  ADDR_MODE4_ADDR32 am4 x xs = ADDR_MODE4_ADDR32' am4 x (ADDR_MODE4_WB32' am4 x (LENGTH xs))`;

val ADDRESS_LIST'_def = Define `
  (ADDRESS_LIST' start 0 = []) /\
  (ADDRESS_LIST' start (SUC n) = start :: ADDRESS_LIST' (start + 4w) n)`;

val GENLIST_EQ = prove(
  ``!xs f n. (!k. k < n ==> (f k = EL k xs)) /\ (n = LENGTH xs) ==> (GENLIST f n = xs)``,
  recInduct SNOC_INDUCT \\ REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC std_ss [LENGTH,GENLIST,LENGTH_SNOC,SNOC_11]
  \\ `!k n. k < n ==> k < SUC n` by DECIDE_TAC
  \\ `!k. k < LENGTH l ==> (f k = EL k l)` by METIS_TAC [EL_SNOC]
  \\ `LENGTH l < SUC (LENGTH l)` by DECIDE_TAC
  \\ `f (LENGTH l) = EL (LENGTH l) (SNOC x l)` by METIS_TAC []     
  \\ ASM_REWRITE_TAC [EL_LENGTH_SNOC] 
  \\ Q.PAT_ASSUM `!f. b ==> (GENLIST f g = l)` MATCH_MP_TAC
  \\ ASM_REWRITE_TAC []);

val ADDRESS_LIST'_INTRO = prove(
  ``!n y. ADDRESS_LIST y n = ADDRESS_LIST' y n``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [ADDRESS_LIST_def] 
  \\ MATCH_MP_TAC GENLIST_EQ \\ SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`y`,`y`)
  \\ Induct_on `n` THEN1 SRW_TAC [] [LENGTH,ADDRESS_LIST'_def]
  \\ REPEAT STRIP_TAC << [
    Cases_on `k` \\ REWRITE_TAC [EL,WORD_MULT_CLAUSES,
       WORD_ADD_0,TL,HD,ADDRESS_LIST'_def,ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [],
    REWRITE_TAC [ADDRESS_LIST'_def,LENGTH] \\ METIS_TAC []]);

val ADDR_MODE4_ADDRESSES_def = Define `
  ADDR_MODE4_ADDRESSES am4 x xs = 
    ADDRESS_LIST' (addr32 (ADDR_MODE4_ADDR am4 x xs)) (LENGTH xs)`;

val ADDR_MODE4_FORMAT = prove(
  ``!am4 x xs.
      ALL_DISTINCT xs ==> 
      (ADDR_MODE4 (ADDR_MODE4_CMD am4).Pre 
          (ADDR_MODE4_CMD am4).Up (addr32 x) 
          (reg_bitmap xs) =
       (LEAST_SORT xs,
        ADDR_MODE4_ADDRESSES am4 x xs,
        addr32 (ADDR_MODE4_WB' am4 x (LENGTH xs))))``,
  SIMP_TAC std_ss [LET_DEF,ADDR_MODE4_def,WB_ADDRESS_EQ_ADDR_MODE4_WB',REGISTER_LIST_LENGTH]
  \\ SIMP_TAC std_ss [REGISTER_LIST_EQ_LEAST_SORT,ADDR_MODE4_ADDRESSES_def,
                      ADDR_MODE4_ADDR'_THM,ADDR_MODE4_ADDR_def,ADDRESS_LIST'_INTRO]);

val ADDR_MODE4_WB_THM = prove(
  ``!am4 p xs. 
      (reg Rd s = addr32 p) ==>
      ((if (ADDR_MODE4_CMD am4).Wb then
         INC_PC (REG_WRITE s.registers (state_mode s) Rd
           (addr32 (ADDR_MODE4_WB' am4 p (LENGTH (MAP FST xs)))))
        else INC_PC s.registers) =
       INC_PC (REG_WRITE s.registers (state_mode s) Rd
         (addr32 (ADDR_MODE4_WB am4 p (MAP FST xs)))))``,
  REPEAT STRIP_TAC 
  \\ `!am4. (ADDR_MODE4_CMD am4).Wb = ADDR_MODE4_wb am4` by 
        (Cases \\ SRW_TAC [] [ADDR_MODE4_CMD_def,ADDR_MODE4_wb_def])
  \\ ASM_REWRITE_TAC [ADDR_MODE4_WB_def] 
  \\ Cases_on `ADDR_MODE4_wb am4` \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `reg Rd s = addr32 p` (ASSUME_TAC o SYM)
  \\ ASM_REWRITE_TAC [reg_def]
  \\ Cases_on `Rd = 15w` \\ ASM_SIMP_TAC std_ss [REG_WRITE_READ]
  \\ ASM_SIMP_TAC (std_ss++wordsLib.SIZES_ss) 
       [REG_WRITE_def,mode_reg2num_def,num2register_thm,LET_DEF,
        EVAL ``w2n (15w:word4)``,INC_PC_def,UPDATE_def]);

val ADDR_MODE4_32_INTRO = prove(
  ``(x && 3w = 0w) ==> 
    (addr32 (ADDR_MODE4_WB a_mode (addr30 x) xs) = ADDR_MODE4_WB32 a_mode x xs) /\
    (addr32 (ADDR_MODE4_ADDR a_mode (addr30 x) xs) = ADDR_MODE4_ADDR32 a_mode x xs)``,
  Cases_on `a_mode` \\ Cases_on `b`
  \\ SIMP_TAC bool_ss [ADDR_MODE4_WB32_def,ADDR_MODE4_WB_def,ADDR_MODE4_WB'_def,
       ADDR_MODE4_UP_def,ADDR_MODE4_wb_def,addr32_SUB,ADDR_MODE4_WB32'_def,
       addr32_n2w,addr32_addr30,addr32_ADD,ADDR_MODE4_ADDR_def,ADDR_MODE4_ADDR'_def,
       ADDR_MODE4_ADDR32_def,ADDR_MODE4_ADDR32'_def,MULT_CLAUSES]);

(* LDM instruction ------------------------------------------------------------- *)

val LDM_VALUES_def = Define `
  LDM_VALUES am4 x xs s = 
    ZIP (LEAST_SORT xs, MAP (s.memory o ADDR30) (ADDR_MODE4_ADDRESSES am4 x xs))`;

val MEM_MAP_FST_ZIP = prove(
  ``!xs ys x. (LENGTH xs = LENGTH ys) ==> (MEM x (MAP FST (ZIP (xs,ys))) = MEM x xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ZIP,MAP,MEM]
  THEN1 REWRITE_TAC [SUC_NOT] THEN1 METIS_TAC [SUC_NOT] \\ ASM_SIMP_TAC std_ss [MEM]);

val ALL_DISTINCT_MAP_FST_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> 
            (ALL_DISTINCT (MAP FST (ZIP (xs,ys))) = ALL_DISTINCT xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH]
  THEN1 SRW_TAC [] [ZIP,MAP,FST,ALL_DISTINCT]
  THEN1 REWRITE_TAC [SUC_NOT] THEN1 METIS_TAC [SUC_NOT]
  \\ ASM_SIMP_TAC bool_ss [ZIP,MAP,FST,ALL_DISTINCT,MEM_MAP_FST_ZIP]);  

val SORTED_LOWER_IMP_ALL_DISTINCT = prove(
  ``!xs. SORTED $<+ xs ==> ALL_DISTINCT xs``,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SORTED_EQ_LOWER \\ METIS_TAC [WORD_LOWER_REFL]);

val ALL_DISTINCT_LEAST_SORT = prove(
  ``!xs. ALL_DISTINCT (LEAST_SORT xs)``,
  STRIP_TAC \\ MATCH_MP_TAC SORTED_LOWER_IMP_ALL_DISTINCT
  \\ REWRITE_TAC [SORTED_LEAST_SORT]);

val REG_WRITEL_INTRO = prove(
  ``!l r m. 
      ALL_DISTINCT (MAP FST l) ==>
      (FOLDL (\reg' (rp,rd). REG_WRITE reg' m rp rd) r l = REG_WRITEL r m l)``,
  Induct \\ SIMP_TAC std_ss [FOLDL,REG_WRITEL_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [REG_WRITEL_def,ALL_DISTINCT,MAP,FST]
  \\ `!l. ~MEM q (MAP FST l) ==> 
    (REG_WRITEL (REG_WRITE r m q r') m l = REG_WRITE (REG_WRITEL r m l) m q r')` 
          by ALL_TAC << [
    Induct \\ SIMP_TAC bool_ss [REG_WRITEL_def,MEM,MAP,FST] \\ REPEAT STRIP_TAC
    \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [REG_WRITEL_def] 
    \\ MATCH_MP_TAC REG_WRITE_WRITE_COMM \\ ASM_REWRITE_TAC [],
  METIS_TAC []]);

val LENGTH_ADDRESS_LIST' = prove(
  ``!n x. LENGTH (ADDRESS_LIST' x n) = n``,
  Induct \\ SRW_TAC [] [LENGTH,ADDRESS_LIST'_def]);

val LDM_WRITEL_INTRO_LEMMA = prove(
  ``!xs. 
      ALL_DISTINCT xs ==> 
      (LENGTH (LEAST_SORT xs) = 
       LENGTH (MAP g (ADDR_MODE4_ADDRESSES am4 x xs)))``,
  SIMP_TAC std_ss 
    [LENGTH_LEAST_SORT,ADDR_MODE4_ADDRESSES_def,LENGTH_ADDRESS_LIST',LENGTH_MAP]);
  
val LDM_WRITEL_INTRO = prove(
  ``!xs r m. 
      ALL_DISTINCT xs ==>
      (FOLDL (\reg' (rp,rd). REG_WRITE reg' m rp rd) r (LDM_VALUES am4 x xs s) = 
       REG_WRITEL r m (LDM_VALUES am4 x xs s))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC REG_WRITEL_INTRO
  \\ `LENGTH (LEAST_SORT xs) = 
      LENGTH (MAP (s.memory o ADDR30) (ADDR_MODE4_ADDRESSES am4 x xs))`
             by ASM_SIMP_TAC std_ss [LENGTH_LEAST_SORT,LENGTH_ADDRESS_LIST',
                                     ADDR_MODE4_ADDRESSES_def,LENGTH_MAP]
  \\ IMP_RES_TAC ALL_DISTINCT_MAP_FST_ZIP
  \\ ASM_SIMP_TAC std_ss [LDM_VALUES_def,ALL_DISTINCT_LEAST_SORT]);

val LDM_STATE_def = Define `
  (LDM_STATE am4 p xs Rd (s:^(ty_antiq arm_state_type))):^(ty_antiq arm_state_type) =
  <|registers :=
            REG_WRITEL
              (INC_PC
                 (REG_WRITE s.registers (state_mode s) Rd
                    (addr32 (ADDR_MODE4_WB am4 p (MAP FST xs)))))
              (state_mode s)
              (ZIP
                 (LEAST_SORT (MAP FST xs),
                  MAP (s.memory o ADDR30)
                    (ADDRESS_LIST'
                       (addr32 (ADDR_MODE4_ADDR am4 p (MAP FST xs)))
                       (LENGTH (MAP FST xs))))); psrs := s.psrs;
          memory := s.memory; undefined := F; cp_state := s.cp_state |>`;

val LDM_STATE2_def = Define `
  (LDM_STATE2 am4 p xs Rd (s:^(ty_antiq arm_state_type))):^(ty_antiq arm_state_type) =
  <|registers :=
            REG_WRITEL
              (INC_PC
                 (REG_WRITE s.registers (state_mode s) Rd
                    (addr32 (ADDR_MODE4_WB am4 p (xs)))))
              (state_mode s)
              (ZIP
                 (LEAST_SORT xs,
                  MAP (s.memory o ADDR30)
                    (ADDRESS_LIST'
                       (addr32 (ADDR_MODE4_ADDR am4 p xs))
                       (LENGTH xs)))); psrs := s.psrs;
          memory := s.memory; undefined := F; cp_state := s.cp_state |>`;

val ldm = simple_clean ARM_LDM [``~(Rd = 15w:word4)``]
val ldm = Q.INST [`opt`|->`ADDR_MODE4_CMD am4`] ldm
val ldm = Q.INST [`list`|->`reg_bitmap (MAP FST (xs:(word4 # word32) list))`] ldm
val ldm = Q.INST [`s_flag`|->`F`] ldm
val ldm = DISCH ``reg Rd s = addr32 p`` ldm
val ldm = DISCH ``ALL_DISTINCT (MAP FST (xs:(word4 # word32) list))`` ldm
val ldm = SIMP_RULE bool_ss [ADDR_MODE4_FORMAT,FST,SND,ADDR_MODE4_WB_THM,
                             GSYM LDM_VALUES_def,LDM_WRITEL_INTRO] ldm
val ldm = REWRITE_RULE [LDM_VALUES_def,GSYM LDM_STATE_def,ADDR_MODE4_ADDRESSES_def] ldm

val MAP_FST_ZIP = prove(
  ``!xs:'a list ys:'b list. (LENGTH xs = LENGTH ys) ==> (MAP FST (ZIP (xs,ys)) = xs)``,
  Induct THEN1 (Cases \\ REWRITE_TAC [ZIP,MAP,FST,LENGTH,DECIDE ``~(0 = SUC n)``])
  \\ STRIP_TAC \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ REWRITE_TAC [ADD1,EQ_ADD_RCANCEL,ZIP,FST,MAP,CONS_11] \\ METIS_TAC []);

val ldm2 = let
  val th = Q.INST [`xs`|->`ZIP(xs,ys)`] ldm
  val th = RW [LDM_STATE_def] th
  val th = DISCH ``LENGTH (xs:word4 list) = LENGTH (ys:word32 list)`` th
  val th = SIMP_RULE bool_ss [MAP_FST_ZIP] th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SYM_CONV)) th
  val th = SIMP_RULE bool_ss [GSYM LDM_STATE2_def] th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SYM_CONV)) th
  in th end;


val reg_values_def = Define ` 
  reg_values = MAP SND o QSORT (\x y. FST x <=+ FST y)`;
  
val LENGTH_reg_values = store_thm("LENGTH_reg_values",
  ``!xs. LENGTH (reg_values xs) = LENGTH (xs:(word4 # word32) list)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [reg_values_def,LENGTH_MAP]
  \\ MATCH_MP_TAC PERM_LENGTH \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ `transitive (\(x:word4 # word32) (y:word4 # word32). FST x <=+ FST y)` by 
      (SIMP_TAC std_ss [transitive_def] \\ METIS_TAC [WORD_LOWER_EQ_TRANS])
  \\ `total (\(x:word4 # word32) (y:word4 # word32). FST x <=+ FST y)` by 
      (SIMP_TAC std_ss [total_def] \\ METIS_TAC [WORD_LOWER_EQ_CASES])
  \\ IMP_RES_TAC (RW [SORTS_DEF] QSORT_SORTS) \\ ASM_REWRITE_TAC []);

val LDM_PRE_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`
  val ys = `[xM_seq (b1,[y1]);xM_seq (b3,y3)]`
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`)
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd)
  in th end;

val LDM_POST_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`
  val ys = `[xM_seq (b1,[y1]);xM_seq (b3,y3)]`
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`)
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd)
  in th end;

val LDM_SIMP_LEMMA = prove(
  ``!xs. (MAP FST (MAP (\x. (FST x,NONE)) xs) = MAP FST xs) /\ 
         (MAP FST (MAP (\x. (FST x,SOME (SND x))) xs) = MAP FST xs)``,
  Induct \\ SRW_TAC [] []);

val MEM_LOWEST = prove(
  ``!xs. 0 < LENGTH xs ==> ?h. MEM h xs /\ !x. MEM x xs ==> h <=+ x``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,MEM] \\ REPEAT STRIP_TAC  
  \\ Cases_on `?y. MEM y xs /\ y <=+ h` << [  
    `?y. MEM y xs /\ y <=+ h` by METIS_TAC []
    \\ Cases_on `xs` THEN1 FULL_SIMP_TAC std_ss [MEM]
    \\ FULL_SIMP_TAC bool_ss [LENGTH,DECIDE ``0 < SUC n = T``]
    \\ Q.EXISTS_TAC `h''` \\ ASM_REWRITE_TAC []
    \\ METIS_TAC [WORD_LOWER_EQ_TRANS],
    Q.EXISTS_TAC `h` \\ FULL_SIMP_TAC bool_ss []
    \\ METIS_TAC [WORD_LOWER_EQ_CASES,WORD_LOWER_EQ_REFL]]);

val PERM_IMPs = prove(
  ``!xs ys. PERM xs ys ==> (LENGTH xs = LENGTH ys) /\ !x. MEM x xs = MEM x ys``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND,LENGTH]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ Q.PAT_ASSUM `!ys. b:bool` IMP_RES_TAC 
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,MEM,MEM_APPEND] THEN1 DECIDE_TAC
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []);

val LDM_mem_SIMP = prove(
  ``!ys y s g. 
      ms_sem y ys <|registers := g; psrs := s.psrs; memory := s.memory; undefined := F|> =
      ms_sem y ys s``,
  Induct \\ SRW_TAC [] [ms_sem_def,mem_def]);

val LDM_VALUES_0 = prove(
  ``!xs.
      (0 = LENGTH xs) ==> 
      (ZIP (LEAST_SORT xs,
            MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 y) (LENGTH xs))) = [])``,
  Cases \\ SRW_TAC [] [LENGTH,LEAST_SORT_def,ADDR_MODE4_ADDRESSES_def,ADDRESS_LIST'_def]);

val LDM_VALUES_SUC = prove(
  ``!xs:word4 list n. 
      ALL_DISTINCT xs ==> (SUC n = LENGTH xs) ==> 
      ?ys. 
        !y. (ZIP
              (LEAST_SORT xs,
                MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 y) (LENGTH xs))) = 
              (LEAST_MEM xs,(s:^(ty_antiq arm_state_type)).memory y)::
                ZIP
                  (LEAST_SORT ys,
                 MAP (s.memory o ADDR30) (ADDRESS_LIST' (addr32 (y+1w)) (LENGTH ys)))) /\
           (n = LENGTH ys) /\ ALL_DISTINCT ys /\ !x. MEM x (LEAST_MEM xs::ys) = MEM x xs``,
  REPEAT STRIP_TAC \\ Cases_on `xs` 
  \\ FULL_SIMP_TAC std_ss [LENGTH] THEN1 METIS_TAC [SUC_NOT]
  \\ FULL_SIMP_TAC std_ss [LEAST_SORT_def,LET_DEF,ADDRESS_LIST'_def,MAP,ADDR30_def,
     GSYM addr30_def,addr30_addr32,ZIP,CONS_11]  
  \\ Q.EXISTS_TAC `FILTER (\x. ~(x = LEAST_MEM (h::t))) (h::t)`  
  \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]
  \\ IMP_RES_TAC LENGTH_FILTER_NEQ  
  \\ FULL_SIMP_TAC bool_ss [LENGTH,ADD1,ADD_SUB,addr32_SUC]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [ALL_DISTINCT_FILTER]  
  \\ SIMP_TAC std_ss [MEM,MEM_FILTER]
  \\ Cases_on `x = LEAST_MEM (h::t)` \\ ASM_REWRITE_TAC []
  \\ METIS_TAC [MEM_LEAST_MEM,MEM]);
  
val MEM_NOT_MEM_IMP_NEQ = prove(
  ``!xs x y. MEM x xs /\ ~MEM y xs ==> ~(x = y)``,
  REPEAT STRIP_TAC
  \\ `?ys zs. xs = ys ++ [x] ++ zs` by METIS_TAC [MEM_EQ_EXISTS]
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM]);

val LDM_STATE2_EQ_LDM_STATE = prove(
  ``LDM_STATE2 am4 x (MAP FST xs) a s = LDM_STATE am4 x xs a s``,
  REWRITE_TAC [LDM_STATE_def,LDM_STATE2_def]);

val fix_LDM_STATE = RW [LDM_STATE2_EQ_LDM_STATE] o
  Q.INST [`xs`|->`MAP FST (xs:(word4 # word32) list)`];

val reg_15_LDM_STATE2 = prove(
  ``ALL_DISTINCT xs /\ (reg 15w s = addr32 p) /\ 
    ~MEM 15w xs /\ ~(a = 15w) ==>
    (reg 15w (LDM_STATE2 am4 x xs a (s:^(ty_antiq arm_state_type))) = addr32 (pcADD 1w p))``,
  SIMP_TAC (srw_ss()) [LDM_STATE2_def,reg_def] 
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x xs)`,`y`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x xs`,`w`)
  \\ Induct_on `LENGTH xs` << [
    SIMP_TAC std_ss [LDM_VALUES_0,REG_WRITEL_def,INC_PC_r15,REG_WRITE_r15,pcADD_def] 
    \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ REWRITE_TAC [addr32_SUC] 
    \\ METIS_TAC [WORD_ADD_COMM],  
    REPEAT STRIP_TAC
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`xs`,`v`]) LDM_VALUES_SUC
    \\ FULL_SIMP_TAC bool_ss [REG_WRITEL_def]    
    \\ Cases_on `xs` THEN1 METIS_TAC [LENGTH,SUC_NOT]
    \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]    
    \\ IMP_RES_TAC MEM_NOT_MEM_IMP_NEQ
    \\ ASM_SIMP_TAC std_ss [REG_WRITE_r15]
    \\ `~MEM 15w ys` by METIS_TAC [MEM]
    \\ `ALL_DISTINCT ys` by METIS_TAC []
    \\ `LENGTH ys = LENGTH ys` by REWRITE_TAC []
    \\ Q.PAT_ASSUM `!xs'. b ==> c:bool` 
           (STRIP_ASSUME_TAC o UD_ALL o Q.SPECL [`w+1w`,`y`] o UD_ALL o Q.SPEC `ys`)]);

val reg_15_LDM_STATE = fix_LDM_STATE reg_15_LDM_STATE2

val state_mode_simp = prove(
  ``state_mode <|registers := r; psrs := s.psrs; memory := m; undefined := b; cp_state := p |> =
    state_mode s``,SRW_TAC [] [state_mode_def]);

val reg_wb_LDM_STATE2 = prove(
  ``ALL_DISTINCT xs /\ ~MEM a xs /\ ~(a = 15w) ==>
    (reg a (LDM_STATE2 am4 x xs a (s:^(ty_antiq arm_state_type))) = 
     addr32 (ADDR_MODE4_WB am4 x xs))``,
  SIMP_TAC (srw_ss()) [LDM_STATE2_def,reg_def,ADDR_MODE4_WB_def] 
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def] 
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x xs)`,`y`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x xs`,`w`)
  \\ SIMP_TAC std_ss [state_mode_simp]
  \\ Induct_on `LENGTH xs`
  THEN1 SIMP_TAC std_ss [LDM_VALUES_0,REG_WRITEL_def,REG_READ_INC_PC,
    REG_READ_WRITE_NEQ,pcADD_def,REG_READ_WRITE] 
  \\ REPEAT STRIP_TAC
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`xs`,`v`]) LDM_VALUES_SUC
  \\ FULL_SIMP_TAC bool_ss [REG_WRITEL_def]    
  \\ Cases_on `xs` THEN1 METIS_TAC [LENGTH,SUC_NOT]
  \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]    
  \\ IMP_RES_TAC MEM_NOT_MEM_IMP_NEQ
  \\ ASM_SIMP_TAC std_ss [REG_READ_WRITE_NEQ2]
  \\ `~MEM a ys` by METIS_TAC [MEM]
  \\ `ALL_DISTINCT ys` by METIS_TAC []
  \\ `LENGTH ys = LENGTH ys` by REWRITE_TAC []
  \\ Q.PAT_ASSUM `!xs'. b ==> c:bool` 
           (STRIP_ASSUME_TAC o UD_ALL o Q.SPECL [`w+1w`,`y`] o UD_ALL o Q.SPEC `ys`));

val reg_wb_LDM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\ ~MEM a (MAP FST xs) /\ ~(a = 15w) ==>
    (reg a (LDM_STATE am4 x xs a (s:^(ty_antiq arm_state_type))) = 
     addr32 (ADDR_MODE4_WB am4 x xs))``,
  SIMP_TAC (srw_ss()) [LDM_STATE_def,reg_def,ADDR_MODE4_WB_def] 
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def] 
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`w`)
  \\ Q.SPEC_TAC (`MAP FST xs`,`xs`) \\ STRIP_TAC
  \\ SIMP_TAC std_ss [state_mode_simp]
  \\ Induct_on `LENGTH xs`
  THEN1 SIMP_TAC std_ss [LDM_VALUES_0,REG_WRITEL_def,REG_READ_INC_PC,
    REG_READ_WRITE_NEQ,pcADD_def,REG_READ_WRITE] 
  \\ REPEAT STRIP_TAC
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`xs`,`v`]) LDM_VALUES_SUC
  \\ FULL_SIMP_TAC bool_ss [REG_WRITEL_def]    
  \\ Cases_on `xs` THEN1 METIS_TAC [LENGTH,SUC_NOT]
  \\ `MEM (LEAST_MEM (h::t)) (h::t)` by METIS_TAC [MEM_LEAST_MEM]    
  \\ IMP_RES_TAC MEM_NOT_MEM_IMP_NEQ
  \\ ASM_SIMP_TAC std_ss [REG_READ_WRITE_NEQ2]
  \\ `~MEM a ys` by METIS_TAC [MEM]
  \\ `ALL_DISTINCT ys` by METIS_TAC []
  \\ `LENGTH ys = LENGTH ys` by REWRITE_TAC []
  \\ Q.PAT_ASSUM `!xs'. b ==> c:bool` 
           (STRIP_ASSUME_TAC o UD_ALL o Q.SPECL [`w+1w`,`y`] o UD_ALL o Q.SPEC `ys`));

val xR_list_sem_PERM_LEMMA = prove(
  ``!xs ys h. xR_list_sem (xs++h::ys) = xR_list_sem (h::(xs++ys))``,
  Induct \\ SIMP_TAC std_ss [xR_list_def,FUN_EQ_THM,APPEND]
  \\ Cases_on `h` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ Cases_on `h'` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss []);

val xR_list_sem_PERM = prove(
  ``!xs ys. PERM xs ys ==> (xR_list_sem xs = xR_list_sem ys)``,
  REWRITE_TAC [FUN_EQ_THM] 
  \\ Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [xR_list_sem_PERM_LEMMA]
  \\ Cases_on `h` \\ Cases_on `r` \\ ASM_REWRITE_TAC [xR_list_sem_def]
  \\ METIS_TAC []);

val PERM_MAP = prove(
  ``!xs ys. PERM xs ys ==> PERM (MAP f xs) (MAP f ys)``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND,PERM_REFL] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [MAP,MAP_APPEND] \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ REWRITE_TAC [APPEND,PERM_CONS_IFF]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ ASM_SIMP_TAC bool_ss [GSYM MAP_APPEND]);

val SORTS_QSORT_FST_LOWER_EQ = prove(
  ``SORTS QSORT (\x y. FST x <=+ FST y)``,
  MATCH_MP_TAC QSORT_SORTS \\ REWRITE_TAC [transitive_def,total_def] 
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [WORD_LOWER_EQ_CASES]
  \\ Cases_on `z` \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC WORD_LOWER_EQ_TRANS 
  \\ Q.EXISTS_TAC `q'` \\ ASM_REWRITE_TAC []);

val LENGTH_reg_values = prove(
  ``!xs. LENGTH (reg_values xs) = LENGTH xs``,
  SIMP_TAC std_ss [reg_values_def,LENGTH_MAP] \\ REPEAT STRIP_TAC 
  \\ MATCH_MP_TAC PERM_LENGTH \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF,PERM_SYM]);

val xR_list_sem_QSORT_INTRO = prove(
  ``!f xs. 
       xR_list_sem (MAP f xs) = xR_list_sem ((MAP f o QSORT (\x y. FST x <=+ FST y)) xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC xR_list_sem_PERM \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC PERM_MAP \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val xR_list_sem_REVERSE_INTRO = prove(
  ``!f xs. xR_list_sem (MAP f xs) = xR_list_sem ((MAP f o REVERSE) xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC xR_list_sem_PERM \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC PERM_MAP \\ Induct_on `xs`
  \\ REWRITE_TAC [PERM_NIL,REVERSE,SNOC_APPEND]
  \\ MATCH_MP_TAC CONS_PERM \\ ASM_REWRITE_TAC [APPEND_NIL]);

val MEM_ALL_MEM_ALL_MAP = prove(
  ``!xs ys. (!a. MEM a xs = MEM a ys) ==> (!a. MEM a (MAP f xs) = MEM a (MAP f ys))``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [MEM_MAP] \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val MEM_MAP_QSORT_INTRO = prove(
  ``!xs a. MEM a (MAP FST xs) = MEM a ((MAP FST o QSORT (\x y. FST x <=+ FST y)) xs)``,
  SIMP_TAC std_ss [] \\ STRIP_TAC \\ MATCH_MP_TAC MEM_ALL_MEM_ALL_MAP
  \\ MATCH_MP_TAC PERM_IMP_MEM_EQUALITY \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val PERM_IMP_ALL_DISTINCT_EQ = prove(
  ``!xs ys. PERM xs ys ==> (ALL_DISTINCT xs = ALL_DISTINCT ys)``,
  Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_CONS_EQ_APPEND] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [ALL_DISTINCT] \\ IMP_RES_TAC PERM_IMP_MEM_EQUALITY
  \\ `!M'. ALL_DISTINCT (M' ++ h::N) = ALL_DISTINCT (h::(M' ++ N))` by     
        (Induct \\ ASM_SIMP_TAC bool_ss [APPEND,ALL_DISTINCT,MEM,MEM_APPEND]
         \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC bool_ss [ALL_DISTINCT] \\ METIS_TAC []);

val ALL_DISTINCT_QSORT_INTRO = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) =
         ALL_DISTINCT ((MAP FST o QSORT (\x y. FST x <=+ FST y)) xs)``,
  STRIP_TAC \\ MATCH_MP_TAC PERM_IMP_ALL_DISTINCT_EQ \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC PERM_MAP \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val LENGTH_QSORT_INTRO = prove(
  ``!xs. LENGTH (MAP FST xs) = LENGTH (QSORT (\x y. FST x <=+ FST y) xs)``,
  STRIP_TAC \\ REWRITE_TAC [LENGTH_MAP] \\ MATCH_MP_TAC PERM_LENGTH 
  \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF]);

val SORTED_MAP = prove(
  ``!xs f g. SORTED g (MAP f xs) = SORTED (\x y. g (f x) (f y)) xs``,
  Induct \\ REWRITE_TAC [SORTED_DEF,MAP]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [SORTED_DEF,MAP]);

val LEAST_SORT_EQ_QSORT_BASIC = prove(
  ``!xs:'a word list. ALL_DISTINCT xs ==> (LEAST_SORT xs = QSORT $<=+ xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ  
  \\ REWRITE_TAC [SORTED_LEAST_SORT,MEM_LEAST_SORT]
  \\ `transitive ($<=+ :('a word->'a word->bool)) /\ total ($<=+ :('a word->'a word->bool))` 
      by REWRITE_TAC [transitive_def,total_def,WORD_LOWER_EQ_TRANS,WORD_LOWER_EQ_CASES]
  \\ IMP_RES_TAC QSORT_SORTS \\ FULL_SIMP_TAC bool_ss [SORTS_DEF]       
  \\ `PERM xs (QSORT $<=+ xs)` by ASM_REWRITE_TAC []  
  \\ IMP_RES_TAC PERM_IMP_ALL_DISTINCT_EQ
  \\ STRIP_TAC THEN1 (MATCH_MP_TAC SORTED_LO \\ ASM_REWRITE_TAC [])
  \\ IMP_RES_TAC PERM_MEM_EQ \\ METIS_TAC []);

val LEAST_SORT_EQ_QSORT = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) ==>
         (LEAST_SORT (MAP FST xs) = MAP FST (QSORT (\x y. FST x <=+ FST y) xs))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ  
  \\ REWRITE_TAC [SORTED_LEAST_SORT,MEM_LEAST_SORT] \\ REPEAT STRIP_TAC << [
    MATCH_MP_TAC SORTED_LO
    \\ ASM_REWRITE_TAC [SIMP_RULE std_ss [] (GSYM ALL_DISTINCT_QSORT_INTRO)]
    \\ REWRITE_TAC [SORTED_MAP] \\ METIS_TAC [SORTS_QSORT_FST_LOWER_EQ,SORTS_DEF],
    SIMP_TAC std_ss [SIMP_RULE std_ss [] (GSYM MEM_MAP_QSORT_INTRO)]]);

val xR_list_sem_IGNORE_REG_WRITE = prove(
  ``!xs r q ax regs.
      ~MEM q (MAP FST xs) ==>
      (xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs)
         (<| registers := REG_WRITE regs (state_mode s) q r; 
            psrs := s.psrs; memory := mt; undefined := bt; cp_state := xx |> 
          :^(ty_antiq arm_state_type)) =
       xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs)
         (<| registers := regs; psrs := s.psrs; memory := mt; 
            undefined := bt; cp_state := xx |> 
          :^(ty_antiq arm_state_type)))``,
  Induct THEN1 REWRITE_TAC [xR_list_sem_def,MAP] \\ Cases
  \\ SIMP_TAC std_ss [MAP,xR_list_sem_def,MEM] \\ Cases_on `q = 15w`
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!s.b` IMP_RES_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [reg_def,state_mode_simp,REG_READ_WRITE_NEQ2]
  \\ `~(15w = q')` by METIS_TAC [] \\ ASM_SIMP_TAC std_ss [REG_WRITE_r15]);

val xR_list_sem_LDM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\ 
    ms_sem (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) s ==>
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) (LDM_STATE am4 x xs a s)``,
  REWRITE_TAC [LDM_STATE_def,ADDR_MODE4_ADDR_def,reg_values_def]     
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_REWRITE_TAC [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def] 
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))`,`y`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ Induct \\ REWRITE_TAC [MAP,xR_list_sem_def]
  \\ Cases \\ SIMP_TAC (srw_ss()) [xR_list_sem_def,reg_def,MEM,state_mode_simp,ms_sem_def]
  \\ SIMP_TAC std_ss [ADDRESS_LIST'_def,MAP,ADDR30_def,GSYM addr30_def,addr30_addr32,ZIP]
  \\ SIMP_TAC bool_ss [REG_WRITEL_def,REG_READ_WRITE,mem_def,REG_WRITE_15]
  \\ ASM_SIMP_TAC bool_ss [xR_list_sem_IGNORE_REG_WRITE,GSYM addr32_SUC] \\ METIS_TAC []);

val xR_list_sem_LDM_STATE2 = prove(
  ``ALL_DISTINCT xs /\ 
    (LENGTH ys = LENGTH xs) /\
    ms_sem (ADDR_MODE4_ADDR a_mode x xs) ys s ==>
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) (ZIP (LEAST_SORT xs,ys)))
      (LDM_STATE2 a_mode x xs a s)``,
  REWRITE_TAC [LDM_STATE2_def,ADDR_MODE4_ADDR_def]     
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def] 
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR a_mode x xs`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB a_mode x xs)`,`y`)
  \\ SIMP_TAC bool_ss [GSYM LENGTH_LEAST_SORT]
  \\ REPEAT STRIP_TAC 
  \\ `LENGTH ys = LENGTH (LEAST_SORT xs)` by METIS_TAC [LENGTH_LEAST_SORT]
  \\ Q.PAT_ASSUM `LENGTH ys = LENGTH xs` (fn th => ALL_TAC)
  \\ Q.PAT_ASSUM `ALL_DISTINCT xs` (fn th => ALL_TAC)
  \\ Q.UNDISCH_TAC `LENGTH ys = LENGTH (LEAST_SORT xs)`
  \\ Q.UNDISCH_TAC `ms_sem ax ys s`
  \\ ASSUME_TAC (Q.ISPEC `xs:word4 list` ALL_DISTINCT_LEAST_SORT)
  \\ Q.UNDISCH_TAC `ALL_DISTINCT (LEAST_SORT xs)`
  \\ Q.SPEC_TAC (`ax`,`ax`)
  \\ Q.SPEC_TAC (`ys`,`ys`)
  \\ Q.SPEC_TAC (`LEAST_SORT xs`,`xs`)
  \\ Induct
  THEN1 (Cases \\ SIMP_TAC bool_ss [ZIP,MAP,xR_list_sem_def,LENGTH,DECIDE ``~(SUC n = 0)``])
  \\ STRIP_TAC \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(0 = SUC n)``]
  \\ SIMP_TAC std_ss [ADDRESS_LIST'_def,MAP,ZIP]
  \\ REWRITE_TAC [ms_sem_def,ADD1,EQ_ADD_RCANCEL,ALL_DISTINCT]  
  \\ SIMP_TAC bool_ss [ADDR30_def,GSYM addr30_def,addr30_addr32,mem_def]
  \\ REWRITE_TAC [xR_list_sem_def,REG_WRITEL_def]  
  \\ SIMP_TAC (srw_ss()) [REG_WRITEL_def,REG_READ_WRITE,mem_def,REG_WRITE_15,reg_def,state_mode_simp]
  \\ REPEAT STRIP_TAC  
  \\ `~MEM h (MAP FST (ZIP (xs,t)))` by METIS_TAC [MAP_FST_ZIP]
  \\ ASM_SIMP_TAC bool_ss [xR_list_sem_IGNORE_REG_WRITE,addr32_ABSORB_CONST]
  \\ METIS_TAC []);

val status_LDM_STATE2 = prove(
  ``status (LDM_STATE2 am4 x xs a s) = status s``,
  SRW_TAC [] [LDM_STATE2_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val mem_LDM_STATE2 = prove(
  ``mem p (LDM_STATE2 am4 x xs a s) = mem p s``,
  SRW_TAC [] [LDM_STATE2_def,mem_def]);

val ms_sem_LDM_STATE2 = prove(
  ``ms_sem x ys (LDM_STATE2 am4 y xs a s) = ms_sem x ys s``,
  Q.SPEC_TAC (`x`,`x`) \\ Induct_on `ys` \\ ASM_REWRITE_TAC [ms_sem_def,mem_LDM_STATE2]);

val undef_LDM_STATE2 = prove(
  ``(LDM_STATE2 am4 x xs a s).undefined = F``, SRW_TAC [] [LDM_STATE2_def]);

val owrt_visible_LDM_STATE2 = prove(
  ``owrt_visible (LDM_STATE2 am4 x xs a s) = owrt_visible s``,
  SRW_TAC [] [owrt_visible_def,LDM_STATE2_def,set_status_def,owrt_visible_regs_def,
              state_mode_simp,REG_OWRT_ALL]);

val status_LDM_STATE = fix_LDM_STATE status_LDM_STATE2; 
val mem_LDM_STATE = fix_LDM_STATE mem_LDM_STATE2
val ms_sem_LDM_STATE = fix_LDM_STATE ms_sem_LDM_STATE2
val undef_LDM_STATE = fix_LDM_STATE undef_LDM_STATE2
val owrt_visible_LDM_STATE = fix_LDM_STATE owrt_visible_LDM_STATE2

val xs = `[(a1,SOME x1)]`;
val ys = `[xM_seq (b1,[y1])]`;
val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`);
val NOP_sem = sep_pred_semantics (xs,ys,st,ud,rt,cd);

val IMP_ARM_NOP = prove(
  ``(!state cpsr.
       (state.memory ((31 >< 2) (state.registers r15)) = cmd) /\
       Abbrev (cpsr = CPSR_READ state.psrs) /\
       ~CONDITION_PASSED2 (NZCV cpsr) c /\ ~state.undefined ==>
       (NEXT_ARM_MEM state =
        (<|registers := INC_PC state.registers; psrs := state.psrs;
          memory := state.memory; undefined := F; cp_state := state.cp_state |>
         :^(ty_antiq arm_state_type)))) ==>
    !x. ARM_PROG (S x * nPASS c x) [cmd] {} ((S x):^(ty_antiq ARMel_type) set -> bool) {}``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [ARM_PROG1_EQ,nPASS_def]   
  \\ MOVE_STAR_TAC `st*cc*mp*pc*ud` `cc*(st*mp*pc*ud)`
  \\ REWRITE_TAC [cond_STAR]
  \\ MOVE_STAR_TAC `st*mp*pc*ud` `pc*mp*st*ud`
  \\ SIMP_TAC bool_ss [NOP_sem,ALL_DISTINCT,MEM,ALL_DISJOINT_def,EVERY_DEF,mem_def,reg_def]
  \\ FULL_SIMP_TAC bool_ss [markerTheory.Abbrev_def,GSYM addr30_def,GSYM status_THM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `1` \\ REWRITE_TAC [STATE_ARM_MEM_1]
  \\ `s.memory (addr30 (s.registers r15)) = cmd` by METIS_TAC [addr30_addr32]
  \\ Q.PAT_ASSUM `!state. b:bool` (STRIP_ASSUME_TAC o Q.SPEC `s`)
  \\ FULL_SIMP_TAC bool_ss [status_THM,INC_PC_r15,pcADD_def,GSYM addr32_SUC]
  \\ STRIP_TAC THEN1 (SRW_TAC [] [INC_PC_r15,addr32_SUC] \\ METIS_TAC [WORD_ADD_COMM]) 
  \\ REWRITE_TAC [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY]
  \\ ASM_SIMP_TAC (srw_ss()) [reg_def,mem_def,REG_READ_INC_PC,state_mode_def,
      owrt_visible_def,set_status_def,owrt_visible_regs_def,REG_OWRT_ALL,mem_byte_def]);  

fun MAKE_ARM_NOP nop_rule = 
  MATCH_MP IMP_ARM_NOP ((Q.GEN `state` o Q.GEN `cpsr` o SPEC_ALL o SET_NO_CP) nop_rule);

val reg_IGNORE_LDM_STATE = prove(
  ``!r. ~(r = 15w) /\ ~(r = a) /\ ~MEM r (MAP FST xs) /\ 
        ALL_DISTINCT (MAP FST xs) ==>
        (reg r s = reg r (LDM_STATE a_mode x xs a s))``,
  SIMP_TAC (srw_ss()) [IN_INSERT,IN_LIST_TO_SET,LDM_STATE_def,reg_def,state_mode_simp]
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP]
  \\ ASM_SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR a_mode x (MAP FST xs)`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB a_mode x (MAP FST xs))`,`y`)
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ Induct \\ REWRITE_TAC [REG_WRITEL_def,MAP,LENGTH,ADDRESS_LIST'_def,ZIP,ALL_DISTINCT]
  \\ ASM_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2,MEM,GSYM addr32_SUC])

val reg_IGNORE_LDM_STATE2 = prove(
  ``!r. ~(r = 15w) /\ ~(r = a) /\ ~MEM r xs /\ ALL_DISTINCT xs ==>
        (reg r s = reg r (LDM_STATE2 a_mode x xs a s))``,
  SIMP_TAC (srw_ss()) [IN_INSERT,IN_LIST_TO_SET,LDM_STATE2_def,reg_def,state_mode_simp]
  \\ SIMP_TAC bool_ss [GSYM LENGTH_LEAST_SORT]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR a_mode x xs`,`ax`)
  \\ Q.SPEC_TAC (`addr32 (ADDR_MODE4_WB a_mode x xs)`,`y`)
  \\ REPEAT STRIP_TAC
  \\ `~(MEM r (LEAST_SORT xs))` by ASM_REWRITE_TAC [MEM_LEAST_SORT]
  \\ Q.PAT_ASSUM `~MEM r xs` (fn th => ALL_TAC)
  \\ Q.PAT_ASSUM `ALL_DISTINCT xs` (fn th => ALL_TAC)
  \\ Q.UNDISCH_TAC `~MEM r (LEAST_SORT xs)`
  \\ Q.SPEC_TAC (`ax`,`ax`)
  \\ Q.SPEC_TAC (`LEAST_SORT xs`,`xs`)
  \\ Induct \\ REWRITE_TAC [REG_WRITEL_def,MAP,LENGTH,ADDRESS_LIST'_def,ZIP,ALL_DISTINCT]
  \\ ASM_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2,MEM,GSYM addr32_SUC]);

val arm_LDM = store_thm("arm_LDM",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R30 a x * 
      xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR a_mode x xs) (reg_values xs) * S (sN,sZ,sC,sV) * 
      PASS c_flag (sN,sZ,sC,sV)) 
     [enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))] {}
     (R30 a (ADDR_MODE4_WB a_mode x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
      ms (ADDR_MODE4_ADDR a_mode x xs) (reg_values xs) * S (sN,sZ,sC,sV)
       :^(ty_antiq ARMel_type) set -> bool) {}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_LDM_NOP] \\ ARM_PROG_INIT_TAC 
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`c`|->`c_flag`,`am4`|->`a_mode`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ STRIP_TAC 
  THEN1 ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
     status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE,mem_byte_def]
  \\ SIMP_TAC std_ss [IN_INSERT,IN_LIST_TO_SET] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC reg_IGNORE_LDM_STATE \\ ASM_REWRITE_TAC []);
  
val arm_LDM_SEQ_LEMMA = prove( 
  ``!zs. MAP FST (MAP (\x. (x,NONE)) zs) = zs``,
  Induct \\ ASM_SIMP_TAC bool_ss [MAP,FST]);

val ALL_DISTINCT_MAP = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) ==> ALL_DISTINCT xs``,
  Induct \\ ASM_SIMP_TAC std_ss [ALL_DISTINCT,MAP,MEM_MAP] \\ METIS_TAC []);

val arm_LDM_SEQ_THM = prove(
  ``!ys. (LENGTH ys = LENGTH xs) ==>
    (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * xR_list (MAP (\x.(FST x,SOME (SND x))) xs) * S (sN,sZ,sC,sV) * cond (x && 3w = 0w) *
      PASS c_flag (sN,sZ,sC,sV) * ms (addr30 (ADDR_MODE4_ADDR32 a_mode x xs)) ys) 
     [enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))] {}
     ((\ys. R a (ADDR_MODE4_WB32 a_mode x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) (ZIP (QSORT $<=+ (MAP FST xs),ys))) *
      S (sN,sZ,sC,sV)) ys * ms (addr30 (ADDR_MODE4_ADDR32 a_mode x xs)) ys
       :^(ty_antiq ARMel_type) set -> bool) {}``,
  REPEAT STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_LDM_NOP]
  \\ SIMP_TAC (bool_ss++sep2_ss) [ARM_PROG_MOVE_COND] \\ STRIP_TAC
  \\ IMP_RES_TAC addr32_addr30
  \\ Q.PAT_ASSUM `addr32 (addr30 x) = x` (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ FULL_SIMP_TAC bool_ss 
    [GSYM (RW [addr30_addr32] (MATCH_MP ADDR_MODE4_32_INTRO (SPEC_ALL addr32_and_3w)))]
  \\ REWRITE_TAC [addr30_addr32]
  \\ Q.PAT_ASSUM `x && 3w = 0w` (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`addr30 x`,`x`) \\ STRIP_TAC \\ REWRITE_TAC [GSYM R30_def]
  \\ ARM_PROG_INIT_TAC 
  \\ FULL_SIMP_TAC (std_ss++sep2_ss) []
  \\ ASM_MOVE_STAR_TAC `a*xs*st*mm*cmd*pc*ud*cd` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*st*mm*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM,arm_LDM_SEQ_LEMMA]
  \\ ASM_SIMP_TAC bool_ss [GSYM LEAST_SORT_EQ_QSORT_BASIC]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ `LENGTH (MAP FST xs) = LENGTH ys` by METIS_TAC [LENGTH_MAP]
  \\ `NEXT_ARM_MEM s = LDM_STATE2 a_mode x (MAP FST xs) a s` by 
   (MATCH_MP_TAC (RW [AND_IMP_INTRO] (GEN_ALL ldm2))
    \\ Q.EXISTS_TAC `ys` \\ Q.EXISTS_TAC `c_flag`
    \\ ASM_SIMP_TAC bool_ss [])
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ STRIP_TAC << [
    `LENGTH (LEAST_SORT (MAP FST xs)) = LENGTH ys` by METIS_TAC [LENGTH_LEAST_SORT] 
    \\ `LIST_TO_SET (LEAST_SORT (MAP FST xs)) = LIST_TO_SET (MAP FST xs)` by
         (REWRITE_TAC [EXTENSION,IN_LIST_TO_SET,MEM_LEAST_SORT])
    \\ ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE2,reg_wb_LDM_STATE2,MAP_FST_ZIP,
         ALL_DISTINCT_LEAST_SORT,MEM_LEAST_SORT,
         status_LDM_STATE2,mem_LDM_STATE2,ms_sem_LDM_STATE2,undef_LDM_STATE2]
    \\ ASM_REWRITE_TAC [ADDR_MODE4_WB_def]
    \\ MATCH_MP_TAC xR_list_sem_LDM_STATE2 \\ ASM_REWRITE_TAC []
    \\ FULL_SIMP_TAC std_ss [ADDR_MODE4_ADDR_def] \\ METIS_TAC [],    
    REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE2,owrt_visible_LDM_STATE2,mem_byte_def]
    \\ SIMP_TAC std_ss [IN_INSERT,IN_LIST_TO_SET] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC reg_IGNORE_LDM_STATE2 \\ ASM_REWRITE_TAC []]);
  
val arm_LDM_SEQ = save_thm("arm_LDM_SEQ",let
  val th = ARM_PROG_INTRO_SEQ_LIST_RD
  val th = Q.INST [`qs`|->`MAP (\x.4w) (qs:(word4 # word32) list)`] th
  val th = RW [LENGTH_MAP,seq_addresses_MAP,list_read_MAP] th
  val th = MATCH_MP th arm_LDM_SEQ_THM
  val th = SIMP_RULE std_ss [] th
  in th end);

val arm_LDM_ADDR = store_thm("arm_LDM_ADDR",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R30 a x * xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR a_mode x ((a,y)::xs)) (reg_values ((a,y)::xs)) * S (sN,sZ,sC,sV) * 
      PASS c_flag (sN,sZ,sC,sV)) 
     [enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (a::MAP FST xs)))] {}
     (xR_list (MAP (\x.(FST x,SOME (SND x))) ((a,y)::xs)) *
      ms (ADDR_MODE4_ADDR a_mode x ((a,y)::xs)) (reg_values ((a,y)::xs)) * S (sN,sZ,sC,sV)
       :^(ty_antiq ARMel_type) set -> bool) {}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_LDM_NOP] \\ ARM_PROG_INIT_TAC 
  \\ FULL_SIMP_TAC bool_ss [xR_list_def,MAP,FST,SND]
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (a::MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((repeat UNDISCH o  RW [MAP,FST,SND,ALL_DISTINCT,GSYM AND_IMP_INTRO] o 
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`c`|->`c_flag`,`am4`|->`a_mode`,`xs`|->`(a,y)::xs`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ STRIP_TAC THEN1
    (ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
     status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
    \\ (IMP_RES_TAC o SIMP_RULE std_ss [ALL_DISTINCT,MAP,FST,xR_list_sem_def,GSYM AND_IMP_INTRO] o 
       Q.INST [`xs`|->`(a,y)::xs`]) xR_list_sem_LDM_STATE
    \\ ASM_REWRITE_TAC []
    \\ MATCH_MP_TAC reg_15_LDM_STATE
    \\ REWRITE_TAC [MAP,FST,ALL_DISTINCT,MEM] \\ METIS_TAC [])      
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE,mem_byte_def]
  \\ SIMP_TAC std_ss [IN_INSERT,IN_LIST_TO_SET]  
  \\ REPEAT STRIP_TAC
  \\ `~MEM r (MAP FST ((a,y)::xs))` by ASM_REWRITE_TAC [MAP,MEM,FST] 
  \\ MATCH_MP_TAC reg_IGNORE_LDM_STATE
  \\ ASM_REWRITE_TAC [ALL_DISTINCT,MAP,FST,MEM]);

val arm_LDM_PC = store_thm("arm_LDM_PC",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR a_mode x ((15w,addr32 p)::xs)) 
         (reg_values ((15w,addr32 p)::xs)) * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV)) 
     [enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (15w :: MAP FST xs)))] {} SEP_F
     {(R30 a (ADDR_MODE4_WB a_mode x ((15w,addr32 p)::xs)) *
       xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
       ms (ADDR_MODE4_ADDR a_mode x ((15w,addr32 p)::xs)) (reg_values ((15w,addr32 p)::xs)) * 
       S (sN,sZ,sC,sV),pcSET p)}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_LDM_NOP]
  \\ ARM_PROG_INIT_TAC \\ SIMP_TAC (bool_ss++sep_ss) [pcSET_def] \\ REWRITE_TAC [SEP_F_def]
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (15w::MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  SIMP_RULE std_ss [MAP,ALL_DISTINCT,GSYM AND_IMP_INTRO] o
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`xs`|->`(15w,addr32 p)::xs`,`am4`|->`a_mode`,`c`|->`c_flag`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ `ALL_DISTINCT (MAP FST ((15w,addr32 p)::xs))` by ASM_SIMP_TAC std_ss [ALL_DISTINCT,MAP]
  \\ `~MEM a (MAP FST ((15w,addr32 p)::xs))` by ASM_SIMP_TAC std_ss [MEM,MAP]
  \\ ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
       status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
  \\ STRIP_TAC THEN1 
    (ONCE_REWRITE_TAC [GSYM xR_list_sem_def]
     \\ `(15w,SOME (addr32 p))::MAP (\x. (FST x,SOME (SND x))) xs = 
         MAP (\x. (FST x,SOME (SND x))) ((15w,addr32 p)::xs)` by SIMP_TAC std_ss [MAP]  
     \\ ASM_SIMP_TAC bool_ss [xR_list_sem_LDM_STATE])
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE,mem_byte_def]
  \\ SIMP_TAC std_ss [IN_INSERT,IN_LIST_TO_SET] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC reg_IGNORE_LDM_STATE 
  \\ ASM_REWRITE_TAC [ALL_DISTINCT,MAP,FST,MEM]);

val arm_LDM_PC_ADDR = store_thm("arm_LDM_PC_ADDR",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,NONE)) xs) * 
      ms (ADDR_MODE4_ADDR a_mode x ((15w,addr32 p)::(a,y)::xs)) 
         (reg_values ((15w,addr32 p)::(a,y)::xs)) * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV)) 
     [enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (15w :: a :: MAP FST xs)))] {} SEP_F
     {(xR_list (MAP (\x.(FST x,SOME (SND x))) ((a,y)::xs)) *
       ms (ADDR_MODE4_ADDR a_mode x ((15w,addr32 p)::(a,y)::xs)) (reg_values ((15w,addr32 p)::(a,y)::xs)) * 
       S (sN,sZ,sC,sV),pcSET p)}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_LDM_NOP]
  \\ SIMP_TAC std_ss [xR_list_def,MAP,FST]
  \\ ARM_PROG_INIT_TAC \\ SIMP_TAC (bool_ss++sep_ss) [pcSET_def] \\ REWRITE_TAC [SEP_F_def]
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,LDM_PRE_EXPANSION,LDM_POST_EXPANSION,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (LDM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (15w::a::MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH_ALL o 
                  SIMP_RULE std_ss [MAP,ALL_DISTINCT,GSYM AND_IMP_INTRO,MEM] o
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`xs`|->`(15w,addr32 p)::(a,y)::xs`,`am4`|->`a_mode`,`c`|->`c_flag`]) ldm)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ `ALL_DISTINCT (MAP FST ((15w,addr32 p)::(a,y)::xs))` by ASM_SIMP_TAC std_ss [ALL_DISTINCT,MAP,MEM]
  \\ `~MEM a (MAP FST ((15w,addr32 p)::xs))` by ASM_SIMP_TAC std_ss [MEM,MAP]
  \\ ASM_SIMP_TAC bool_ss [reg_15_LDM_STATE,reg_wb_LDM_STATE,xR_list_sem_LDM_STATE,
       status_LDM_STATE,mem_LDM_STATE,ms_sem_LDM_STATE,undef_LDM_STATE]
  \\ STRIP_TAC THEN1 (
    (IMP_RES_TAC o REWRITE_RULE [GSYM AND_IMP_INTRO] o
     SIMP_RULE std_ss [ALL_DISTINCT,MAP,FST,MEM,xR_list_sem_def] o 
     Q.INST [`xs`|->`(15w,addr32 p)::(a,y)::xs`]) xR_list_sem_LDM_STATE
    \\ ASM_REWRITE_TAC [])  
  \\ REWRITE_TAC [arm2set''_EQ,mem_LDM_STATE,owrt_visible_LDM_STATE,mem_byte_def]
  \\ SIMP_TAC std_ss [IN_INSERT,IN_LIST_TO_SET] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC reg_IGNORE_LDM_STATE 
  \\ ASM_REWRITE_TAC [ALL_DISTINCT,MAP,FST,MEM]);


(* STM instruction ------------------------------------------------------------- *)

val STM_STATE_def = Define `
  (STM_STATE am4 x xs a (s:^(ty_antiq arm_state_type))):^(ty_antiq arm_state_type) =
           <|registers :=
               INC_PC
                 (REG_WRITE s.registers (state_mode s) a
                    (addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))));
             psrs := s.psrs;
             memory :=
               FOLDL
                 (\mem (rp,rd).
                    MEM_WRITE_WORD mem rd
                      (REG_READ
                         (if HD (LEAST_SORT (MAP FST xs)) = a then
                            INC_PC s.registers
                          else
                            INC_PC
                              (REG_WRITE s.registers (state_mode s) a
                                 (addr32
                                    (ADDR_MODE4_WB am4 x (MAP FST xs)))))
                         (state_mode s) rp)) s.memory
                 (ZIP
                    (LEAST_SORT (MAP FST xs),
                     ADDR_MODE4_ADDRESSES am4 x (MAP FST xs)));
             undefined := F; cp_state := s.cp_state |>`;

val stm = simple_clean ARM_STM [``~(Rd = 15w:word4)``]
val stm = Q.INST [`opt`|->`ADDR_MODE4_CMD am4`] stm
val stm = Q.INST [`list`|->`reg_bitmap (MAP FST (xs:(word4 # word32) list))`] stm
val stm = Q.INST [`s_flag`|->`F`] stm
val stm = DISCH ``reg Rd s = addr32 p`` stm
val stm = DISCH ``ALL_DISTINCT (MAP FST (xs:(word4 # word32) list))`` stm
val stm = SIMP_RULE bool_ss [ADDR_MODE4_FORMAT,FST,SND,ADDR_MODE4_WB_THM] stm
val stm = REWRITE_RULE [GSYM STM_STATE_def] stm

val status_STM_STATE = prove(
  ``status (STM_STATE am4 x xs a s) = status s``,
  SRW_TAC [] [STM_STATE_def,status_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val undef_STM_STATE = prove(
  ``(STM_STATE am4 x xs a s).undefined = F``, SRW_TAC [] [STM_STATE_def]);

val owrt_visible_STM_STATE = prove(
  ``owrt_visible (STM_STATE am4 x xs a s) = owrt_visible s``,
  SRW_TAC [] [owrt_visible_def,STM_STATE_def,set_status_def,owrt_visible_regs_def,
              state_mode_simp,REG_OWRT_ALL]);

val reg_15_STM_STATE = prove(
  ``~(a = 15w) /\ (reg 15w s = addr32 p) ==> 
    (reg 15w (STM_STATE am4 x xs a s) = addr32 (pcADD 1w p))``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,INC_PC_r15,pcADD_def,
                       REG_WRITE_r15,GSYM addr32_SUC] \\ METIS_TAC [WORD_ADD_COMM]);

val reg_wb_STM_STATE = prove(
  ``~(a = 15w) ==> 
    (reg a (STM_STATE am4 x xs a s) = addr32 (ADDR_MODE4_WB am4 x xs))``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,state_mode_simp,REG_READ_INC_PC,
                       REG_READ_WRITE,ADDR_MODE4_WB_def,LENGTH_MAP]);

val reg_STM_STATE = prove(
  ``~(r = 15w) /\ ~(r = a) ==> (reg r (STM_STATE am4 x xs a s) = reg r s)``,
  SIMP_TAC (srw_ss()) [STM_STATE_def,reg_def,state_mode_simp,REG_READ_INC_PC,
                       REG_READ_WRITE_NEQ2,LENGTH_MAP]);

val xR_list_sem_STM_STATE = prove(
  ``xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s /\
    ~MEM 15w (MAP FST xs) /\ ~MEM a (MAP FST xs) ==>
    (xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) (STM_STATE am4 x xs a s) = 
     xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s)``,
  REWRITE_TAC [STM_STATE_def]
  \\ Q.SPEC_TAC (`FOLDL
      (\mem (rp,rd). MEM_WRITE_WORD mem rd (REG_READ
      (if HD (LEAST_SORT (MAP FST xs)) = a then INC_PC s.registers else
      INC_PC (REG_WRITE s.registers (state_mode s) a
      (addr32 (ADDR_MODE4_WB am4 x (MAP FST xs))))) (state_mode s) rp)) s.memory
      (ZIP (LEAST_SORT (MAP FST xs), ADDR_MODE4_ADDRESSES am4 x (MAP FST xs)))`,`fff`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_WB am4 x (MAP FST xs)`,`wbwb`)
  \\ Induct_on `xs` \\ SIMP_TAC std_ss [xR_list_sem_def,MAP]
  \\ Cases \\ Cases_on `q = 15w` \\ ASM_SIMP_TAC std_ss [MEM] 
  \\ ASM_SIMP_TAC (srw_ss()) [MEM,reg_def,state_mode_simp,
       REG_READ_INC_PC,REG_READ_WRITE_NEQ2]);

val xR_list_sem_STM_STATE_PC = prove(
  ``xR_list_sem (MAP (\x. (FST x,SOME (SND x))) ((15w,addr32 p)::xs)) s /\
    ~MEM 15w (MAP FST xs) /\ ~MEM a (MAP FST xs) /\ ~(15w = a) ==>
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) ((15w,addr32 (p+1w))::xs)) (STM_STATE am4 x ((15w,addr32 p)::xs) a s)``,
  REWRITE_TAC [STM_STATE_def]
  \\ Q.PAT_ABBREV_TAC `nnnnn = FOLDL xdfgdfg s.memory (ZIP (y,u))` \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`ADDR_MODE4_WB am4 x (MAP FST ((15w,addr32 p)::xs))`,`wbwb`)
  \\ SIMP_TAC std_ss [xR_list_sem_def,MAP,FST,SND]
  \\ REPEAT STRIP_TAC << [
    REWRITE_TAC [reg_def] \\ SRW_TAC [] [INC_PC_r15,REG_WRITE_r15]
    \\ FULL_SIMP_TAC std_ss [reg_def,addr32_ADD,addr32_n2w],
    Induct_on `xs` \\ SIMP_TAC std_ss [xR_list_sem_def,MAP]
    \\ Cases \\ Cases_on `q = 15w` \\ ASM_SIMP_TAC std_ss [MEM] 
    \\ ASM_SIMP_TAC (srw_ss()) [MEM,reg_def,state_mode_simp,
         REG_READ_INC_PC,REG_READ_WRITE_NEQ2]]);

val xR_list_sem_STM_STATE_IMP = prove(
  ``xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s /\
    ~MEM 15w (MAP FST xs) /\ ~MEM a (MAP FST xs) ==>
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) (STM_STATE am4 x ((15w,0w)::xs) a s)``,
  REWRITE_TAC [STM_STATE_def]
  \\ Q.SPEC_TAC (`FOLDL
      (\mem (rp,rd). MEM_WRITE_WORD mem rd (REG_READ
      (if HD (LEAST_SORT (MAP FST ((15w,0w)::xs))) = a then INC_PC s.registers else
      INC_PC (REG_WRITE s.registers (state_mode s) a
      (addr32 (ADDR_MODE4_WB am4 x (MAP FST ((15w,0w)::xs)))))) (state_mode s) rp)) s.memory
      (ZIP (LEAST_SORT (MAP FST ((15w,0w)::xs)), ADDR_MODE4_ADDRESSES am4 x (MAP FST ((15w,0w)::xs))))`,`fff`)
  \\ Q.SPEC_TAC (`ADDR_MODE4_WB am4 x (MAP FST ((15w,0w)::xs))`,`wbwb`)
  \\ Induct_on `xs` \\ SIMP_TAC std_ss [xR_list_sem_def,MAP]
  \\ Cases \\ Cases_on `q = 15w` \\ ASM_SIMP_TAC std_ss [MEM] 
  \\ ASM_SIMP_TAC (srw_ss()) [MEM,reg_def,state_mode_simp,
       REG_READ_INC_PC,REG_READ_WRITE_NEQ2]);

val mem_STM_STATE = prove(
  ``ALL_DISTINCT (MAP FST xs) /\
    ~(addr32 p IN ms_address_set (ADDR_MODE4_ADDR am4 x xs) (LENGTH xs)) ==>
    (mem p (STM_STATE am4 x xs a s) = mem p s)``,
  REWRITE_TAC [STM_STATE_def,ADDR_MODE4_WB_def,LENGTH_MAP]
  \\ Q.SPEC_TAC (`HD (LEAST_SORT (MAP FST xs)) = a`,`rt`)
  \\ Q.SPEC_TAC (`(if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x)`,`rt'`)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def,ADDR_MODE4_ADDRESSES_def]  
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP] 
  \\ ASM_REWRITE_TAC [ADDR_MODE4_ADDR_def]
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT,mem_def]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ Q.SPEC_TAC (`s.memory`,`mmm`)
  \\ SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (fn th => ALL_TAC)

  \\ Induct \\ ASM_SIMP_TAC std_ss [LENGTH,ADDRESS_LIST'_def,MAP,ZIP,
       FOLDL,GSYM addr32_SUC,ALL_DISTINCT,ms_address_set_def,IN_INSERT,WORD_ADD_0,addr32_11]
  \\ SIMP_TAC std_ss [MEM_WRITE_WORD_def,UPDATE_def,ADDR30_def,GSYM addr30_def,addr30_addr32]);

val ms_sem_STM_STATE_LEMMA = prove(
  ``!mmm bx f. 
      ~MEM (addr32 ax) (ADDRESS_LIST' (addr32 bx) (LENGTH xs)) ==> 
      (FOLDL
         (\mem (rp,rd). MEM_WRITE_WORD mem rd (f rp))
         (MEM_WRITE_WORD mmm (addr32 ax) r)
         (ZIP (MAP FST xs,ADDRESS_LIST' (addr32 bx) (LENGTH xs))) =
      MEM_WRITE_WORD
       (FOLDL
         (\mem (rp,rd). MEM_WRITE_WORD mem rd (f rp)) mmm
         (ZIP (MAP FST xs,ADDRESS_LIST' (addr32 bx) (LENGTH xs))))
     (addr32 ax) r)``,
  Induct_on `xs` 
  \\ SIMP_TAC std_ss [MAP,LENGTH,ADDRESS_LIST'_def,ZIP,FOLDL,MEM,GSYM addr32_SUC]
  \\ Cases \\ REPEAT STRIP_TAC
  \\ `!x. MEM_WRITE_WORD (MEM_WRITE_WORD mmm (addr32 ax) r) (addr32 bx) x = 
          MEM_WRITE_WORD (MEM_WRITE_WORD mmm (addr32 bx) x) (addr32 ax) r` by
        (SRW_TAC [] [MEM_WRITE_WORD_def,UPDATE_def,FUN_EQ_THM,ADDR30_def,
           GSYM addr30_def,addr30_addr32] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC std_ss []);

val MEM_ADDRESS_LIST' = prove(
  ``!n a b. MEM (addr32 a) (ADDRESS_LIST' (addr32 b) n) = addr32 a IN ms_address_set b n``,
  Induct \\ ASM_REWRITE_TAC [ADDRESS_LIST'_def,MEM,ms_address_set_def,
     NOT_IN_EMPTY,IN_INSERT,GSYM addr32_SUC,addr32_11,addr32_NEQ_addr32]);

val no_overlap_ADDRESS_LIST' = prove(
  ``!xs ax. LENGTH xs < 2**30 ==> 
            ~MEM (addr32 ax) (ADDRESS_LIST' (addr32 (ax+1w)) (LENGTH xs))``,
  SIMP_TAC bool_ss [MEM_ADDRESS_LIST',IN_ms_address_set]
  \\ REPEAT STRIP_TAC \\ Cases_on `k < 4 * LENGTH xs` \\ ASM_REWRITE_TAC []
  \\ `n2w k + (ax + 1w) = ax + n2w (k + 1)` by 
       METIS_TAC [word_add_n2w,WORD_ADD_COMM,WORD_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_REWRITE_TAC [WORD_ADD_RID_UNIQ,addr32_ADD,GSYM WORD_ADD_ASSOC,addr32_n2w,word_add_n2w,EVAL ``4*1``]  
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ]
  \\ `4 * SUC (LENGTH xs) <= 4 * 2 ** 30` by ASM_SIMP_TAC std_ss [LE_MULT_LCANCEL]
  \\ FULL_SIMP_TAC bool_ss [GSYM LESS_EQ,ADD1,EVAL ``4*1``,LEFT_ADD_DISTRIB]
  \\ `k + 4 < 4 * LENGTH xs + 4` by ASM_SIMP_TAC std_ss [LT_ADD_RCANCEL]
  \\ `k + 4 < 4 * 2 ** 30` by METIS_TAC [LESS_LESS_EQ_TRANS]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [n2w_11]);
  
val ms_sem_STM_STATE = prove(
  ``LENGTH xs <= 2**30 /\
    ~MEM a (MAP FST xs) /\ ~MEM 15w (MAP FST xs) /\ ALL_DISTINCT (MAP FST xs) /\ 
    xR_list_sem (MAP (\x. (FST x,SOME (SND x))) xs) s ==>
    ms_sem (ADDR_MODE4_ADDR am4 x xs) (reg_values xs) (STM_STATE am4 x xs a s)``,
  REWRITE_TAC [STM_STATE_def,ADDR_MODE4_WB_def,LENGTH_MAP]
  \\ Q.SPEC_TAC (`HD (LEAST_SORT (MAP FST xs)) = a`,`rt`)
  \\ Q.SPEC_TAC (`(if ADDR_MODE4_wb am4 then ADDR_MODE4_WB' am4 x (LENGTH xs) else x)`,`rt'`)
  \\ REWRITE_TAC [GSYM ADDR_MODE4_WB_def,ADDR_MODE4_ADDRESSES_def]  
  \\ `LENGTH xs = LENGTH (MAP FST xs)` by METIS_TAC [LENGTH_MAP] 
  \\ ASM_REWRITE_TAC [ADDR_MODE4_ADDR_def]
  \\ REWRITE_TAC [GSYM ADDR_MODE4_ADDR_def]
  \\ Q.SPEC_TAC (`ADDR_MODE4_ADDR am4 x (MAP FST xs)`,`ax`)
  \\ SIMP_TAC bool_ss [LEAST_SORT_EQ_QSORT,mem_def]
  \\ REWRITE_TAC [xR_list_sem_QSORT_INTRO,MEM_MAP_QSORT_INTRO,
                  ALL_DISTINCT_QSORT_INTRO,LENGTH_QSORT_INTRO]
  \\ Q.SPEC_TAC (`s.memory`,`mmm`)
  \\ SIMP_TAC std_ss [reg_values_def] 
  \\ Q.SPEC_TAC (`QSORT (\x y. FST x <=+ FST y) xs`,`xs`)
  \\ SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Induct THEN1 REWRITE_TAC [ms_sem_def,MAP]
  \\ Cases \\ SIMP_TAC std_ss [MAP,HD,MEM,LENGTH,ADDRESS_LIST'_def,ZIP,FOLDL,
       ALL_DISTINCT,xR_list_sem_def,ms_sem_def,GSYM addr32_SUC] 
  \\ Cases_on `q = 15w` \\ ASM_REWRITE_TAC []
  \\ NTAC 5 STRIP_TAC \\ `LENGTH xs <= 1073741824` by DECIDE_TAC
  \\ `LENGTH xs < 1073741824` by DECIDE_TAC 
  \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``2**30``)] 
  \\ `~MEM (addr32 ax) (ADDRESS_LIST' (addr32 (ax + 1w)) (LENGTH xs))` 
        by METIS_TAC [no_overlap_ADDRESS_LIST']
  \\ ASM_SIMP_TAC bool_ss [ms_sem_STM_STATE_LEMMA]
  \\ SIMP_TAC (srw_ss()) [mem_def,MEM_WRITE_WORD_def,ADDR30_def,
         GSYM addr30_def,addr30_addr32,UPDATE_def]
  \\ `REG_READ s.registers (state_mode s) q = r` by METIS_TAC [reg_def]
  \\ Cases_on `rt` \\ FULL_SIMP_TAC std_ss [REG_READ_INC_PC,REG_READ_WRITE_NEQ2]);

val LEAST_SORT_EXTRACT_15w = prove(
  ``~MEM 15w (MAP FST xs) ==>
    (LEAST_SORT (MAP FST ((15w,addr32 p)::xs)) = LEAST_SORT (MAP FST xs) ++ [15w:word4])``,
  REWRITE_TAC [MAP,FST] \\ Q.SPEC_TAC (`MAP FST xs`,`xs`) \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_LO_IMP_EQ
  \\ REWRITE_TAC [MEM_LEAST_SORT,MEM_APPEND,MEM,SORTED_LEAST_SORT]  
  \\ REPEAT STRIP_TAC << [
    MATCH_MP_TAC SORTED_APPEND
    \\ REWRITE_TAC [MEM_LEAST_SORT,MEM,transitive_def,SORTED_LEAST_SORT]
    \\ REWRITE_TAC [SORTED_DEF,WORD_LOWER_TRANS]
    \\ NTAC 2 Cases
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,word_lo_n2w,LESS_MOD]        
    \\ Cases_on `n = 15` \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ DECIDE_TAC,
    METIS_TAC []]);  

val NOT_IN_PART = prove(
  ``!xs g ys zs. (!y. MEM y xs ==> g y x) ==> (PART (\y. g y x) xs ys zs = (REVERSE xs ++ ys,zs))``,
  Induct \\ FULL_SIMP_TAC std_ss [PART_DEF,MEM,APPEND,APPEND_NIL,REVERSE_DEF] 
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [GSYM APPEND_ASSOC,APPEND]);

val EXTRACT_FROM_QSORT = prove(
  ``!xs x R. (!y. MEM y xs ==> R y x) ==>
             (QSORT R (x::xs) = QSORT R (REVERSE xs) ++ [x])``,
  SIMP_TAC bool_ss [QSORT_DEF,PARTITION_DEF,NOT_IN_PART]
  \\ SIMP_TAC std_ss [LET_DEF,QSORT_DEF,APPEND_NIL]);

val EXTRACT_15_FROM_QSORT = prove(
  ``QSORT (\x y. FST x <=+ FST y) ((15w:word4,0w:word32)::xs) = 
    QSORT (\x y. FST x <=+ FST y) (REVERSE xs) ++ [(15w,0w)]``,
  MATCH_MP_TAC EXTRACT_FROM_QSORT \\ Cases
  \\ ASSUME_TAC (INST_TYPE [``:'a``|->``:4``] w2n_lt)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [FST,WORD_LS,w2n_n2w,DECIDE ``n <= 15 = n < 16``]); 

val ALL_DISTINCT_SNOC = prove(
  ``!xs y. ALL_DISTINCT (xs ++ [y]) = ALL_DISTINCT (y::xs)``,
  Induct \\ ASM_REWRITE_TAC [APPEND,ALL_DISTINCT,MEM,MEM_APPEND] \\ METIS_TAC []);

val ALL_DISTINCT_REVERSE = prove(
  ``!xs. ALL_DISTINCT (REVERSE xs) = ALL_DISTINCT xs``,
  Induct \\ ASM_REWRITE_TAC [ALL_DISTINCT,REVERSE,SNOC_APPEND,MEM_REVERSE,ALL_DISTINCT_SNOC]);

val STM_PRE_EXPANSION = let
  val xs = `(15w,SOME x1)::(a,SOME x2)::xs`;
  val ys = `[xM_seq (b1,[y1]);xM_blank (b3,y3)]`;
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`);
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);
  in th end;

val STM_PRE_EXPANSION_PC = let
  val xs = `(a,SOME x2)::xs`;
  val ys = `[xM_seq (b1,[y1]);xM_blank (b3,y3)]`;
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`);
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd);
  in th end;

val STM_POST_EXPANSION = LDM_POST_EXPANSION;

val STM_POST_EXPANSION_PC = let
  val xs = `(a,SOME x2)::xs`
  val ys = `[xM_seq (b1,[y1]);xM_seq (b3,y3)]`
  val (st,ud,rt,cd) = (`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`)
  val th = sep_pred_semantics (xs,ys,st,ud,rt,cd)
  in th end;

val addr32_ADD_IN_ms_address_set = prove(
  ``!n a b. 
      (addr32 a + 0w IN ms_address_set b n = addr32 a IN ms_address_set b n) /\
      (addr32 a + 1w IN ms_address_set b n = addr32 a IN ms_address_set b n) /\
      (addr32 a + 2w IN ms_address_set b n = addr32 a IN ms_address_set b n) /\
      (addr32 a + 3w IN ms_address_set b n = addr32 a IN ms_address_set b n)``,
  Induct 
  \\ ASM_REWRITE_TAC [NOT_IN_EMPTY,ms_address_set_def,IN_INSERT,addr32_NEQ_addr32,addr32_11]);  

val arm_STM = store_thm("arm_STM",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R30 a x * 
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) * 
      blank_ms (ADDR_MODE4_ADDR a_mode x xs) (LENGTH xs) * 
      S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV)) 
     [enc (STM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))] {}
     (R30 a (ADDR_MODE4_WB a_mode x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) *
      ms (ADDR_MODE4_ADDR a_mode x xs) (reg_values xs) * S (sN,sZ,sC,sV)) {}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_STM_NOP]
  \\ ARM_PROG_INIT_TAC 
  \\ ASM_MOVE_STAR_TAC `a*xs*mm*st*cd*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud*cd`
  \\ MOVE_STAR_TAC `a*xs*mm*st*cmd*pc*ud` `pc*a*xs*cmd*mm*st*ud`
  \\ FULL_SIMP_TAC bool_ss [R30_def,STM_PRE_EXPANSION,STM_POST_EXPANSION,DISJOINT_SING,
         LDM_SIMP_LEMMA,ALL_DISTINCT,MEM,LENGTH_reg_values,ALL_DISJOINT_def,EVERY_DEF]
  \\ `CONDITION_PASSED2 (status s) c_flag` by METIS_TAC []
  \\ `mem (addr30 (reg 15w s)) s =
      enc (STM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))` 
         by METIS_TAC [addr30_addr32]
  \\ `~(a = 15w)` by METIS_TAC []
  \\ ASSUME_TAC ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o UNDISCH o 
                  Q.INST [`p`|->`x`,`Rd`|->`a`,`c`|->`c_flag`,`am4`|->`a_mode`]) stm)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = s'` (fn th => ALL_TAC)
  \\ FULL_SIMP_TAC bool_ss [DISJOINT_INSERT,WORD_ADD_0,DISJOINT_EMPTY]
  \\ ASM_SIMP_TAC bool_ss [status_STM_STATE,undef_STM_STATE,reg_15_STM_STATE,
       reg_wb_STM_STATE,xR_list_sem_STM_STATE,mem_STM_STATE,ms_sem_STM_STATE]
  \\ ASM_SIMP_TAC bool_ss [arm2set''_EQ,owrt_visible_STM_STATE,IN_INSERT,
       reg_STM_STATE,mem_STM_STATE,mem_byte_def]
  \\ STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `p'` EXISTS_addr32)
  \\ ASM_REWRITE_TAC [addr30_addr32,addr32_ADD_IN_ms_address_set] 
  \\ ASM_SIMP_TAC bool_ss [mem_STM_STATE]);

val arm_STM_SEQ_THM = prove(
  ``!ys. (LENGTH ys = LENGTH (reg_values xs)) ==>
    (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R a x * xR_list (MAP (\x.(FST x,SOME (SND x))) xs) * 
      S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * cond (x && 3w = 0w) *
      ms (addr30 (ADDR_MODE4_ADDR32 a_mode x xs)) ys) 
     [enc (STM c_flag F (ADDR_MODE4_CMD a_mode) a (reg_bitmap (MAP FST xs)))] {}
     (R a (ADDR_MODE4_WB32 a_mode x xs) *
      xR_list (MAP (\x.(FST x,SOME (SND x))) xs) * S (sN,sZ,sC,sV) * 
      ms (addr30 (ADDR_MODE4_ADDR32 a_mode x xs)) (reg_values xs)) {}``,
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP ARM_STM_NOP]
  \\ REWRITE_TAC [GSYM ARM_PROG_HIDE_PRE_ms]
  \\ REWRITE_TAC [LENGTH_reg_values]
  \\ SIMP_TAC (bool_ss++sep2_ss) [ARM_PROG_MOVE_COND] \\ STRIP_TAC
  \\ IMP_RES_TAC addr32_addr30
  \\ Q.PAT_ASSUM `addr32 (addr30 x) = x` (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ FULL_SIMP_TAC bool_ss 
    [GSYM (RW [addr30_addr32] (MATCH_MP ADDR_MODE4_32_INTRO (SPEC_ALL addr32_and_3w)))]
  \\ REWRITE_TAC [addr30_addr32]
  \\ Q.PAT_ASSUM `x && 3w = 0w` (fn th => ALL_TAC)
  \\ Q.SPEC_TAC (`addr30 x`,`x`) \\ STRIP_TAC \\ REWRITE_TAC [GSYM R30_def]
  \\ ASSUME_TAC ((CONJUNCT1 o RW [ARM_PROG2_def]) arm_STM)
  \\ FULL_SIMP_TAC (bool_ss++star_ss)  []);

val arm_STM_SEQ = save_thm("arm_STM_SEQ",let
  val th = MATCH_MP ARM_PROG_INTRO_SEQ_LIST_WR arm_STM_SEQ_THM
  in th end);
  
val reg_values_EQ = prove(
  ``!x xs. ~MEM 15w (MAP FST xs) ==>
           (reg_values ((14w:word4,x:word32)::xs) = reg_values ((15w,x)::xs))``,  
  SIMP_TAC std_ss [reg_values_def] \\ REPEAT STRIP_TAC
  \\ `(!y. MEM y xs ==> (\x y. FST x <=+ FST y) y (15w:word4,x:word32))` by
    (REPEAT STRIP_TAC \\ Cases_on `y`
     \\ ASM_SIMP_TAC std_ss [WORD_LS,EVAL ``w2n (15w:word4)``]
     \\ ASSUME_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (Q.ISPEC `q:word4` w2n_lt)) \\ DECIDE_TAC)
  \\ `(!y. MEM y xs ==> (\x y. FST x <=+ FST y) y (14w:word4,x:word32))` by ALL_TAC << [
    REPEAT STRIP_TAC \\ Cases_on `y`
    \\ FULL_SIMP_TAC std_ss [WORD_LS,EVAL ``w2n (14w:word4)``,MEM_MAP]
    \\ ASSUME_TAC (SIMP_RULE (std_ss++SIZES_ss) [] (Q.ISPEC `q:word4` w2n_lt))
    \\ Cases_on `~(w2n (q:word4) = 15)` THEN1 DECIDE_TAC
    \\ Q.PAT_ASSUM `!y. ~(15w = FST y) \/ ~MEM y xs` (ASSUME_TAC o Q.SPEC `(n2w (w2n (q:word4)),r)`)
    \\ FULL_SIMP_TAC bool_ss [FST,n2w_11,LESS_MOD,w2n_lt]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_w2n],    
    IMP_RES_TAC EXTRACT_FROM_QSORT \\ ASM_REWRITE_TAC [MAP_APPEND,MAP,SND]]);
      
val MEM_EQ_APPEND = prove(
  ``!x xs. MEM x xs = ?ys zs. xs = ys ++ x::zs``,
  REPEAT STRIP_TAC \\ Induct_on `xs` \\ SIMP_TAC bool_ss [MEM]
  THEN1 (Induct \\ REWRITE_TAC [APPEND_NIL,NOT_NIL_CONS,APPEND])
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [  
    Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `xs` \\ ASM_REWRITE_TAC [APPEND_NIL],
    FULL_SIMP_TAC bool_ss [] \\ Q.EXISTS_TAC `h::ys` \\ Q.EXISTS_TAC `zs`
    \\ REWRITE_TAC [APPEND],
    Cases_on `ys` \\ FULL_SIMP_TAC bool_ss [CONS_11,APPEND_NIL,APPEND]
    \\ DISJ2_TAC \\ METIS_TAC []])

val xR_list_APPEND = prove(
  ``!xs ys. xR_list (xs ++ ys) = xR_list xs * xR_list ys``,
  Induct \\ REWRITE_TAC [APPEND,xR_list_def,emp_STAR]
  \\ Cases \\ Cases_on `r` \\ ASM_REWRITE_TAC [APPEND,xR_list_def,GSYM STAR_ASSOC]);

val DELETE_MEM_CONDITION = prove(
  ``ARM_PROG 
      (P * xR_list (MAP (\x. (FST x,SOME (SND x))) ((14w,addr32 p)::xs)) * cond ~MEM 15w (MAP FST xs))
      code C Q Z ==>
    ARM_PROG 
      (P * xR_list (MAP (\x. (FST x,SOME (SND x))) ((14w,addr32 p)::xs))) code C Q Z``,
  Cases_on `MEM 15w (MAP FST xs)` \\ ASM_SIMP_TAC (bool_ss++sep_ss) [ARM_PROG_FALSE_PRE]
  \\ `?x. MEM (15w,x) xs` by 
    (FULL_SIMP_TAC bool_ss [MEM_MAP] \\ Cases_on `y` \\ Q.EXISTS_TAC `r` 
     \\ FULL_SIMP_TAC bool_ss [FST] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND,MAP,MAP_APPEND,FST,SND,xR_list_def,xR_list_APPEND]
  \\ MOVE_STAR_TAC `g 15w x * P` `P * g 15w x`
  \\ REWRITE_TAC [STAR_ASSOC,ARM_PROG_R15]);

val arm_STM_R14 = save_thm("arm_STM_R14",let
  val th = RW [ARM_PROG2_def] arm_STM
  val th = Q.INST [`xs`|->`(14w,addr32 p)::xs`] th
  val th2 = CONJUNCT2 th
  val th = CONJUNCT1 th
  val lm = UNDISCH (Q.SPECL [`addr32 p`,`xs`] reg_values_EQ)
  val th = SIMP_RULE bool_ss [] (DISCH (concl lm) th)
  val th = MATCH_MP th lm  
  val th = MOVE_STAR_RULE `x * b * bb * ss* pp` `x * bb * ss* pp * b` th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (DISCH_ALL th)
  val th = MATCH_MP DELETE_MEM_CONDITION th
  val th = MOVE_STAR_RULE `x * bb * ss * pp * b` `x * b * bb * ss* pp` th
  val th = RW [GSYM ARM_PROG2_def] (CONJ th th2)
  in th end);


(* ----------------------------------------------------------------------------- *)
(* Tactics                                                                       *)
(* ----------------------------------------------------------------------------- *)

val mem_EQ_mem_pc = prove(
  ``!p s. (reg 15w s = addr32 p) ==> (mem p s = mem (addr30 (reg 15w s)) s)``,
  METIS_TAC [addr30_addr32])

val mem_SIMP = prove(
  ``(mem_byte a <| registers := r; psrs := p; memory := s.memory; undefined := u; cp_state := cp |> = 
     mem_byte a s) /\ 
    (mem b <| registers := r; psrs := p; memory := s.memory; undefined := u; cp_state := cp |> = 
     mem b s)``,
  SRW_TAC [] [mem_byte_def,mem_def]);

val status_SIMP = prove(
  ``(status <| registers := r; psrs := s.psrs; memory := m; undefined := u; cp_state := cp |> = 
     status s)``,
  SRW_TAC [] [status_def,statusN_def,statusZ_def,statusC_def,statusV_def]);

val status_SIMP2 = prove(
  ``status <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZCV (n,z,c,v) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> = 
    (n,z,c,v)``,
  SRW_TAC [] [status_def,statusN_def,statusZ_def,statusC_def,statusV_def] 
  \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);

val status_SIMP3 = prove(
  ``status <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZ (n,z) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> = 
    (n,z,statusC s,statusV s)``,
  SRW_TAC [] [status_def,statusN_def,statusZ_def,statusC_def,
    statusV_def,SET_NZ_def,SET_NZC_def] \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);

val undefined_SIMP = prove(
  ``<|registers := r; psrs := p; memory := m; undefined := b; cp_state := cp|>.undefined = b``,
  SRW_TAC [] []);

val state_mode_SIMP = prove(
  ``state_mode <| registers := r; psrs := s.psrs; memory := m; undefined := u; cp_state := cp |> = 
    state_mode s``,
  SRW_TAC [] [state_mode_def]);

val state_mode_SIMP2 = prove(
  ``state_mode
           <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZCV (n,z,c,v) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> =
    state_mode s``,
  SIMP_TAC (srw_ss()) [state_mode_def] \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);

val state_mode_SIMP3 = prove(
  ``state_mode
           <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZ (n,z) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> =
    state_mode s``,
  SIMP_TAC (srw_ss()) [state_mode_def,SET_NZ_def,SET_NZC_def] 
  \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);

val pc_SIMP = prove(
  ``!p. addr32 p + 4w = addr32 (pcADD 1w p)``,
  SIMP_TAC bool_ss [pcADD_def,addr32_ADD,addr32_n2w,EVAL ``4*1``] \\ METIS_TAC [WORD_ADD_COMM]);

val set_status_SIMP = prove(
  ``set_status (sN,sZ,sC,sV) <| registers := r; psrs := s.psrs; memory := m; undefined := u; cp_state := cp |> =
    set_status (sN,sZ,sC,sV) s``,
  SRW_TAC [] [set_status_def]);

val set_status_SIMP2 = prove(
  ``set_status (sN,sZ,sC,sV)            
           <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZCV (n,z,c,v) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> =
    set_status (sN,sZ,sC,sV) s``,
  SRW_TAC [] [set_status_def] \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);

val set_status_SIMP3 = prove(
  ``set_status (sN,sZ,sC,sV)            
           <|registers := r;
             psrs := CPSR_WRITE s.psrs (SET_NZ (n,z) (CPSR_READ s.psrs)); 
             memory := s.memory; undefined := u; cp_state := cp|> =
    set_status (sN,sZ,sC,sV) s``,
  SRW_TAC [] [set_status_def,SET_NZ_def,SET_NZC_def] 
  \\ CONV_TAC PSR_CONV \\ REWRITE_TAC []);
  
val DIV_EQ_1 = prove(
  ``!k. 0 < k ==> !n. (n DIV k = 1) = k <= n /\ n < k + k``,
  SIMP_TAC bool_ss [EQ_LESS_EQ,DIV_LE_X,X_LE_DIV,MULT_CLAUSES,EVAL ``1+1``]
  \\ DECIDE_TAC);
  
val BIT32_LEMMA = prove(
  ``!x:word32 y:word32. 
      (BIT 32 (w2n x + w2n y + 1) = 2**32 <= w2n x + w2n y + 1) /\
      (BIT 32 (w2n x + w2n y) = 2**32 <= w2n x + w2n y)``,
  NTAC 2 Cases
  \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD]
  \\ REWRITE_TAC [BIT_def,BITS_def,DIV_2EXP_def,MOD_2EXP_def]
  \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [DIV_MOD_MOD_DIV]
  \\ `n + n' + 1 < 8589934592 /\ n + n' < 8589934592 /\ 0 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD]
  \\ ASM_SIMP_TAC bool_ss [DIV_EQ_1] \\ DECIDE_TAC);

val BIT32_THM = prove(
  ``!c x:word32 y:word32. 
      (BIT 32 (w2n x + w2n y) = 2**32 <= w2n x + w2n y) /\ 
      (BIT 32 (w2n x + w2n y + 1) = 2**32 <= w2n x + w2n y + 1) /\ 
      (BIT 32 (w2n x + w2n y + (if c then 1 else 0)) = 
       2**32 <= w2n x + w2n y + (if c then 1 else 0)) /\ 
      (BIT 32 (w2n x + w2n y + (if c then 0 else 1)) = 
       2**32 <= w2n x + w2n y + (if c then 0 else 1))``,
  Cases \\ REWRITE_TAC [BIT32_LEMMA,ADD_0]);

val WORD_XOR_EQ_ZERO = prove(
  ``!x y. (x ?? y = 0w) = (x = y)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC bool_ss [WORD_XOR_CLAUSES]
  \\ SIMP_TAC bool_ss [fcpTheory.CART_EQ,word_0]
  \\ SIMP_TAC bool_ss [word_xor_def,fcpTheory.FCP_BETA])


(* tactic *)

val ARM_PROG_PROVER_ss = rewrites 
  [reg_def,state_mode_SIMP,state_mode_SIMP2,state_mode_SIMP3,REG_WRITE_r15,INC_PC_r15,pc_SIMP,
   REG_READ_WRITE,REG_READ_WRITE_NEQ2,REG_READ_INC_PC,status_SIMP,status_SIMP2,status_SIMP3,
   GSYM mem_byte_def,IN_INSERT,NOT_IN_EMPTY,owrt_visible_def,set_status_SIMP,
   set_status_SIMP2,set_status_SIMP3,owrt_visible_regs_def,REG_OWRT_ALL,
   REG_WRITE_15,status_def,PAIR_EQ,BIT32_THM,EVAL ``2**32``,WORD_XOR_EQ_ZERO];

fun ARM_PROG2_INIT_TAC nop pre_move pre_move' post_move post_move' =
  REWRITE_TAC [ARM_PROG2_def,MAKE_ARM_NOP nop]
  \\ ARM_PROG_INIT_TAC 
  \\ ASM_MOVE_STAR_TAC pre_move pre_move'
  \\ MOVE_STAR_TAC post_move post_move'
  \\ FULL_SIMP_TAC pure_ss [GSYM STAR_ASSOC] 
  \\ FULL_SIMP_TAC pure_ss [SEP_cond_CLAUSES] 
  \\ FULL_SIMP_TAC (pure_ss++sep_ss) [STAR_ASSOC];

fun ARM_PROG2_EXPAND_TAC' xs ys xs' ys' = let
  val pre_expand = sep_pred_semantics (xs,ys,`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`)
  val post_expand = sep_pred_semantics (xs',ys',`(T,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`)
  in 
  FULL_SIMP_TAC bool_ss [pre_expand,post_expand,R30_def,M30_def] 
  \\ IMP_RES_TAC mem_EQ_mem_pc
  \\ Q.PAT_ASSUM `status s = (sN,sZ,sC,sV)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM]
  end;

fun ARM_PROG2_EXPAND_TAC xs ys = ARM_PROG2_EXPAND_TAC' xs ys xs ys;

fun ARM_PROG2_RULE_TAC facts th =
  IMP_RES_TAC mem_EQ_mem_pc
  \\ Q.PAT_ASSUM `status s = (sN,sZ,sC,sV)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM]
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean th facts))
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = x` (fn th => ALL_TAC);

val ARM_PROG2_HAMMER_TAC = 
  ASM_SIMP_TAC bool_ss [mem_SIMP,status_SIMP,undefined_SIMP,arm2set''_EQ]  
  \\ FULL_SIMP_TAC (srw_ss()++ARM_PROG_PROVER_ss) 
      [SIMP_RULE (srw_ss()) [] WORD_EQ_SUB_ZERO,
       RW1[WORD_ADD_COMM](SIMP_RULE (srw_ss()) [] WORD_EQ_SUB_ZERO)];

val xR1  = `[(a1,SOME x1)]`;
val xR2  = `[(a1,SOME x1);(a2,SOME x2)]`;
val xR2' = `[(a1,NONE);(a2,SOME x2)]`;
val xR3  = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3)]`;
val xR4  = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3);(a4,SOME x4)]`;
val xR5  = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3);(a4,SOME x4);(a5,SOME x5)]`;
val xR6  = `[(a1,SOME x1);(a2,SOME x2);(a3,SOME x3);(a4,SOME x4);(a5,SOME x5);(a6,SOME x6)]`;

val xMm  = `[xM_seq (b1,[y1])]`;
val xMmb = `[xM_seq (b1,[y1]);xM_byte (b2,SOME y2)]`;
val xMmm = `[xM_seq (b1,[y1]);xM_seq (b2,[y2])]`;
val xMmh = `[xM_seq (b1,[y1]);xM_blank (b2,SUC 0)]`;


(* ----------------------------------------------------------------------------- *)
(* LDRB and LDR INSTRUCTIONS                                                     *)
(* ----------------------------------------------------------------------------- *)

val FORMAT_UnsignedWord = SIMP_CONV (srw_ss()) [FORMAT_def] ``FORMAT UnsignedWord x y``;
val FORMAT_UnsignedByte = SIMP_CONV (srw_ss()) [FORMAT_def] ``FORMAT UnsignedByte x y``;

fun FIX_ADDR_MODE2 b th = let
  val th = SPEC_ALL th
  val th = DISCH_ALL (ASM_UNABBREV_ALL_RULE (UD_ALL th))
  val th = RW [GSYM state_mode_def] th
  val th = Q.INST [`offset`|->`Dt_immediate imm`] th
  val th = Q.INST [`b`|->b] th
  val th = SIMP_RULE bool_ss 
    [ADDR_MODE2_WB'_THM,ADDR_MODE2_ADDR'_THM,FORMAT_UnsignedWord,FORMAT_UnsignedByte] th
  in UD_ALL th end;

fun AM2_ALIGN_ADDRESSES var th = let
  val th = Q.INST [var|->`addr32 y`,`imm`|->`(w2w (imm:word8)) << 2`] th 
  val th = RW [ADDR_MODE2_WB_THM,ADDR_MODE2_ADDR_THM] th
  val th = RW [GSYM R30_def,ADDRESS_ROTATE,addr30_addr32] th   
  in th end;

val ldrb = FIX_ADDR_MODE2 `T` ARM_LDR
val ldrb = (UNDISCH_ALL o Q.INST [`Rd`|->`a`,`Rn`|->`b`,`c`|->`c_flag`] o DISCH_ALL) ldrb

val arm_LDRB = store_thm("arm_LDRB",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R a x * R b y * byte (ADDR_MODE2_ADDR' opt imm y) z * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV))
     [enc (LDR c_flag T opt a b (Dt_immediate imm))] {}
     (R a (w2w z) * R b (ADDR_MODE2_WB' opt imm y) * byte (ADDR_MODE2_ADDR' opt imm y) z *
      S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_LDR_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmb
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldrb []))
  \\ ARM_PROG2_HAMMER_TAC);

val ldrb1 = (UNDISCH_ALL o Q.INST [`a`|->`b`] o DISCH_ALL) ldrb

val arm_LDRB1 = store_thm("arm_LDRB1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R b x * byte (ADDR_MODE2_ADDR' opt imm x) z * cond ~opt.Wb * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV))
     [enc (LDR c_flag T opt b b (Dt_immediate imm))] {}
     (R b (w2w z) * byte (ADDR_MODE2_ADDR' opt imm x) z * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_LDR_NOP
      `a*m*cd'*st*cd*cmd*pc*ud` `a*pc*cmd*m*st*ud*cd'*cd`
      `a*m*st*cmd*pc*ud` `a*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMmb
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldrb1 []))
  \\ ARM_PROG2_HAMMER_TAC);

val ldr_pc = FIX_ADDR_MODE2 `F` ARM_LDR_PC
val ldr_pc = (UNDISCH_ALL o Q.INST [`Rd`|->`a`,`c`|->`c_flag`] o DISCH_ALL) ldr_pc

val w2w_and_3 = prove(
   ``!i. ((i:word12) && 3w = 0w) ==> ((w2w i) && 3w:word32 = 0w)``,
   Cases
   \\ `n MOD 4 < 4` by METIS_TAC [DIVISION,DECIDE ``0<4``]
   \\ `n MOD 4 < 4096` by DECIDE_TAC
   \\ `n MOD 4 < 4294967296` by DECIDE_TAC
   \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_and_3,w2w_def,w2n_n2w,n2w_11,LESS_MOD]); 

val arm_LDR_PC_ADDRESS = prove(
  ``addr30 (if opt.Up then addr32 p + 8w + w2w imm else addr32 p + 8w - w2w imm) =
    pcADD (addr30 (if opt.Up then 8w + w2w imm else 8w - w2w imm)) p``,
  Cases_on `opt.Up` 
  \\ ASM_SIMP_TAC std_ss [addr30_addr32_ADD,GSYM WORD_ADD_ASSOC,word_sub_def,pcADD_def,
       AC WORD_ADD_COMM WORD_ADD_ASSOC]);

val arm_LDR_PC_LEMMA1 = prove(
  ``ARM_RUN (M (I p) (enc (LDR c_flag F opt a 15w (Dt_immediate imm))) *
             M (pcADD(addr30 (if opt.Up then 8w + w2w imm else 8w - w2w imm)) p) y *
             R a x * R 15w (addr32 p) * 
             S (sN,sZ,sC,sV) * one (Undef F) * cond (opt.Pre /\ ~opt.Wb /\ (imm && 3w = 0w)) * 
             cond (CONDITION_PASSED2 (sN,sZ,sC,sV) c_flag))
            (M (I p) (enc (LDR c_flag F opt a 15w (Dt_immediate imm))) *
             M (pcADD(addr30 (if opt.Up then 8w + w2w imm else 8w - w2w imm)) p) y *
             R a y * R 15w (addr32 (pcADD 1w p)) * 
             S (sN,sZ,sC,sV) * one (Undef F))``,
  SIMP_TAC (std_ss++sep2_ss) [ARM_RUN_SEMANTICS,GSYM arm_LDR_PC_ADDRESS] 
  \\ SIMP_TAC std_ss [RW1 [WORD_ADD_COMM] pcADD_def]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [STATE_ARM_MEM_1,LET_DEF]
  \\ ASM_MOVE_STAR_TAC `m1*m2*ra*pc*ss*oo*c` `ra*pc*m1*m2*ss*oo*c`
  \\ MOVE_STAR_TAC `m1*m2*ra*pc*ss*oo` `ra*pc*m1*m2*ss*oo`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldr_pc []))
  \\ `(status (NEXT_ARM_MEM s) = status s) /\ ~(NEXT_ARM_MEM s).undefined` by 
    ASM_SIMP_TAC (srw_ss()) [status_def,statusN_def,statusZ_def,statusC_def,statusV_def]
  \\ `!x. mem x (NEXT_ARM_MEM s) = mem x s` by ASM_SIMP_TAC (srw_ss()) [mem_def]
  \\ `owrt_visible (NEXT_ARM_MEM s) = owrt_visible s` by 
    ASM_SIMP_TAC (srw_ss()) [owrt_visible_def,set_status_def,
                             owrt_visible_regs_def,REG_OWRT_ALL,state_mode_def]
 \\ `!b. reg b (NEXT_ARM_MEM s) = if b = 15w then addr32 (p+1w) else if b = a then y else reg b s` by 
   (ASM_SIMP_TAC (srw_ss()) [reg_def,state_mode_def] \\ STRIP_TAC
    \\ Cases_on `b = 15w` \\ ASM_SIMP_TAC bool_ss [] << [      
      REWRITE_TAC [REG_READ6_def,FETCH_PC_def,GSYM INC_PC]
      \\ ASM_SIMP_TAC bool_ss [REG_WRITE_INC_PC,INC_PC_r15,REG_WRITE_r15]
      \\ FULL_SIMP_TAC std_ss [reg_def,addr32_ADD,addr32_n2w],
      Cases_on `b = a` \\ ASM_SIMP_TAC bool_ss [REG_READ_WRITE_NEQ]
      \\ FULL_SIMP_TAC bool_ss [REG_READ_WRITE,GSYM state_mode_def,reg_def]
      \\ FULL_SIMP_TAC bool_ss [REG_READ_def]
      \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = dgd` (fn th => ALL_TAC)     
      \\ `(1 >< 0) (ADDR_MODE2_ADDR' opt imm (addr32 p + 8w)) = 0w:word2` by 
       (Cases_on `opt.Up` \\ ASM_SIMP_TAC bool_ss [ADDR_MODE2_ADDR'_def]
        \\ REWRITE_TAC [GSYM (SIMP_CONV std_ss [addr32_n2w] ``addr32 2w``)]
        \\ IMP_RES_TAC w2w_and_3
        \\ IMP_RES_TAC EXISTS_addr30
        \\ ASM_SIMP_TAC std_ss [GSYM addr32_ADD,GSYM addr32_SUB,addr32_eq_0])
      \\ ASM_SIMP_TAC std_ss [EVAL ``w2n (0w:word2)``,SHIFT_ZERO,ADDR_MODE2_ADDR'_def]])    
  \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = dgd` (fn th => ALL_TAC)     
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.ABBREV_TAC `nnn = addr30 (if opt.Up then addr32 p + 8w + w2w imm else addr32 p + 8w - w2w imm)`
  \\ ASM_SIMP_TAC std_ss [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY,mem_byte_def]);

val arm_LDR_PC_LEMMA2 = prove(
  ``(I p = pcADD (addr30 (if opt.Up then 8w + w2w imm else 8w - w2w imm)) p) /\
    (enc (LDR c_flag F opt a 15w (Dt_immediate imm)) = y) ==>
    ARM_RUN (M (I p) (enc (LDR c_flag F opt a 15w (Dt_immediate imm))) *
             R a x * R 15w (addr32 p) * 
             S (sN,sZ,sC,sV) * one (Undef F) * cond (opt.Pre /\ ~opt.Wb /\ (imm && 3w = 0w)) * 
             cond (CONDITION_PASSED2 (sN,sZ,sC,sV) c_flag))
            (M (I p) (enc (LDR c_flag F opt a 15w (Dt_immediate imm))) *
             R a y * R 15w (addr32 (pcADD 1w p)) * 
             S (sN,sZ,sC,sV) * one (Undef F))``,
  SIMP_TAC (std_ss++sep2_ss) [ARM_RUN_SEMANTICS,GSYM arm_LDR_PC_ADDRESS] 
  \\ SIMP_TAC std_ss [RW1 [WORD_ADD_COMM] pcADD_def]
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
  \\ SIMP_TAC (std_ss++sep2_ss) [ARM_RUN_SEMANTICS,GSYM arm_LDR_PC_ADDRESS] 
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [STATE_ARM_MEM_1,LET_DEF]
  \\ ASM_MOVE_STAR_TAC `m1*ra*pc*ss*oo*c` `ra*pc*m1*ss*oo*c`
  \\ MOVE_STAR_TAC `m1*ra*pc*ss*oo` `ra*pc*m1*ss*oo`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ `mem (addr30 (reg 15w s)) s = enc (LDR c_flag F opt a 15w (Dt_immediate imm))` by METIS_TAC []
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldr_pc []))
  \\ `(status (NEXT_ARM_MEM s) = status s) /\ ~(NEXT_ARM_MEM s).undefined` by 
    ASM_SIMP_TAC (srw_ss()) [status_def,statusN_def,statusZ_def,statusC_def,statusV_def]
  \\ `!x. mem x (NEXT_ARM_MEM s) = mem x s` by ASM_SIMP_TAC (srw_ss()) [mem_def]
  \\ `owrt_visible (NEXT_ARM_MEM s) = owrt_visible s` by 
    ASM_SIMP_TAC (srw_ss()) [owrt_visible_def,set_status_def,
                             owrt_visible_regs_def,REG_OWRT_ALL,state_mode_def]
  \\ `!b. reg b (NEXT_ARM_MEM s) = if b = 15w then addr32 (p+1w) else if b = a then y else reg b s` by 
   (ASM_SIMP_TAC (srw_ss()) [reg_def,state_mode_def] \\ STRIP_TAC
    \\ Cases_on `b = 15w` \\ ASM_SIMP_TAC bool_ss [] << [      
      REWRITE_TAC [REG_READ6_def,FETCH_PC_def,GSYM INC_PC]
      \\ ASM_SIMP_TAC bool_ss [REG_WRITE_INC_PC,INC_PC_r15,REG_WRITE_r15]
      \\ FULL_SIMP_TAC std_ss [reg_def,addr32_ADD,addr32_n2w],
      Cases_on `b = a` \\ ASM_SIMP_TAC bool_ss [REG_READ_WRITE_NEQ]
      \\ FULL_SIMP_TAC bool_ss [REG_READ_WRITE,GSYM state_mode_def,reg_def]
      \\ FULL_SIMP_TAC bool_ss [REG_READ_def]
      \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = dgd` (fn th => ALL_TAC)     
      \\ `(1 >< 0) (ADDR_MODE2_ADDR' opt imm (addr32 p + 8w)) = 0w:word2` by 
       (Cases_on `opt.Up` \\ ASM_SIMP_TAC bool_ss [ADDR_MODE2_ADDR'_def]
        \\ REWRITE_TAC [GSYM (SIMP_CONV std_ss [addr32_n2w] ``addr32 2w``)]
        \\ IMP_RES_TAC w2w_and_3
        \\ IMP_RES_TAC EXISTS_addr30
        \\ ASM_SIMP_TAC std_ss [GSYM addr32_ADD,GSYM addr32_SUB,addr32_eq_0])
      \\ ASM_SIMP_TAC std_ss [EVAL ``w2n (0w:word2)``,SHIFT_ZERO,ADDR_MODE2_ADDR'_def]])    
  \\ Q.PAT_ASSUM `NEXT_ARM_MEM s = dgd` (fn th => ALL_TAC)     
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.ABBREV_TAC `nnn = addr30 (if opt.Up then addr32 p + 8w + w2w imm else addr32 p + 8w - w2w imm)`
  \\ ASM_SIMP_TAC std_ss [arm2set''_EQ,IN_INSERT,NOT_IN_EMPTY,mem_byte_def]);

val lemma = MATCH_MP (RW [GSYM STAR_ASSOC] IMP_ARM_RUN_mpool) (RW [GSYM STAR_ASSOC] arm_LDR_PC_LEMMA1)
val lemma = MATCH_MP lemma (RW [GSYM STAR_ASSOC] arm_LDR_PC_LEMMA2)
val lemma = RW [STAR_ASSOC] lemma
    
val arm_LDR_PC_NONALIGNED = store_thm("arm_LDR_PC_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * 
      cond (opt.Pre /\ ~opt.Wb /\ (imm && 3w = 0w)))
     [enc (LDR c_flag F opt a 15w (Dt_immediate imm))]
     {([y],pcADD (addr30 (if opt.Up then 8w + w2w imm else 8w - w2w imm)))}
     (R a y * S (sN,sZ,sC,sV)) {}``,
  REWRITE_TAC [ARM_PROG2_def] \\ REPEAT STRIP_TAC
  THENL [ALL_TAC,METIS_TAC [MAKE_ARM_NOP ARM_LDR_NOP,UNION_EMPTY,ARM_PROG_ADD_CODE]]
  \\ SIMP_TAC std_ss [ARM_PROG_THM,ARM_GPROG_THM,GPROG_DISJ_CLAUSES,PASS_def,R30_def,
                      pcINC_def,wLENGTH_def,LENGTH,ARMpc_def,STAR_ASSOC]
  \\ STRIP_TAC \\ ASSUME_TAC lemma
  \\ FULL_SIMP_TAC (std_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM,
       AC CONJ_COMM CONJ_ASSOC, AC STAR_ASSOC STAR_COMM]);

val ldr = FIX_ADDR_MODE2 `F` ARM_LDR
val ldr = (UNDISCH_ALL o Q.INST [`Rd`|->`a`,`Rn`|->`b`,`c`|->`c_flag`] o DISCH_ALL) ldr

val arm_LDR_NONALIGNED = store_thm("arm_LDR_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z *
      S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
     [enc (LDR c_flag F opt a b (Dt_immediate imm))] {}
     (R a (z #>> (8 * w2n (((1 >< 0) ((ADDR_MODE2_ADDR' opt imm y))):word2))) *
      R b (ADDR_MODE2_WB' opt imm y) *
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_LDR_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldr []))
  \\ ARM_PROG2_HAMMER_TAC);

val arm_LDR_SEQ_LEMMA = prove(
  ``!z. (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * 
      cond (ADDR_MODE2_ADDR' opt imm y && 3w = 0w) * 
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z)
     [enc (LDR c_flag F opt a b (Dt_immediate imm))] {}
     ((\z. R a z * R b (ADDR_MODE2_WB' opt imm y) * S (sN,sZ,sC,sV)) z *
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z) {}``,
  SIMP_TAC std_ss []
  \\ MOVE_STAR_TAC `a*b*s*m` `a*b*m*s`
  \\ MOVE_STAR_TAC `a*b*s*p*m*c` `a*b*m*s*p*c`
  \\ Cases_on `ADDR_MODE2_ADDR' opt imm y && 3w = 0w`
  \\ ASM_SIMP_TAC (bool_ss++sep_ss) []
  THEN1 (IMP_RES_TAC addr32_addr30 \\ METIS_TAC [ADDRESS_ROTATE,arm_LDR_NONALIGNED])
  \\ REWRITE_TAC [ARM_PROG2_def,ARM_PROG_FALSE_PRE]
  \\ METIS_TAC [arm_LDR_NONALIGNED,ARM_PROG2_def]);

val arm_LDR_SEQ = save_thm("arm_LDR_SEQ",let
  val th = MATCH_MP ARM_PROG_INTRO_SEQ_RD arm_LDR_SEQ_LEMMA
  val th = SPEC_ALL (SIMP_RULE std_ss [] th)
  in th end);

val ldr1 = (UNDISCH_ALL o Q.INST [`a`|->`b`] o DISCH_ALL) ldr

val arm_LDR1_NONALIGNED = store_thm("arm_LDR1_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R b y * M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z * cond ~opt.Wb * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV))
     [enc (LDR c_flag F opt b b (Dt_immediate imm))] {}
     (R b (z #>> (8 * w2n (((1 >< 0) (ADDR_MODE2_ADDR' opt imm y)):word2))) *
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_LDR_NOP
      `a*m*cd'*st*cd*cmd*pc*ud` `a*pc*cmd*m*st*ud*cd'*cd`
      `a*m*st*cmd*pc*ud` `a*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldr1 []))
  \\ ARM_PROG2_HAMMER_TAC);

val arm_LDR1_SEQ_LEMMA = prove(
  ``!z. (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * cond ~opt.Wb *
      cond (ADDR_MODE2_ADDR' opt imm y && 3w = 0w) * 
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z)
     [enc (LDR c_flag F opt b b (Dt_immediate imm))] {}
     ((\z. R b z * S (sN,sZ,sC,sV)) z *
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z) {}``,
  SIMP_TAC std_ss []
  \\ MOVE_STAR_TAC `b*s*m` `b*m*s`
  \\ MOVE_STAR_TAC `b*s*p*c'*m*c` `b*m*c'*s*p*c`
  \\ Cases_on `ADDR_MODE2_ADDR' opt imm y && 3w = 0w`
  \\ ASM_SIMP_TAC (bool_ss++sep_ss) []
  THEN1 (IMP_RES_TAC addr32_addr30 \\ METIS_TAC [ADDRESS_ROTATE,arm_LDR1_NONALIGNED])
  \\ REWRITE_TAC [ARM_PROG2_def,ARM_PROG_FALSE_PRE]
  \\ METIS_TAC [arm_LDR1_NONALIGNED,ARM_PROG2_def]);

val arm_LDR1_SEQ = save_thm("arm_LDR1_SEQ",let
  val th = MATCH_MP ARM_PROG_INTRO_SEQ_RD arm_LDR1_SEQ_LEMMA
  val th = SPEC_ALL (SIMP_RULE std_ss [] th)
  in th end);

val arm_LDR = save_thm("arm_LDR",AM2_ALIGN_ADDRESSES `y` arm_LDR_NONALIGNED);
val arm_LDR1 = save_thm("arm_LDR1",AM2_ALIGN_ADDRESSES `y` arm_LDR1_NONALIGNED);

val ldr_pc = (Q.INST [`a`|->`15w`,`b`|->`a`] o DISCH_ALL) ldr;
val ldr_pc = Q.INST [`imm`|->`(w2w (imm:word8)) << 2`] ldr_pc 

val arm_LDR_PC = store_thm("arm_LDR_PC",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R30 a x * M (ADDR_MODE2_ADDR opt imm x) (addr32 y) * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV))
     [enc (LDR c_flag F opt 15w a (Dt_immediate ((w2w (imm:word8)) << 2)))] {}
     SEP_F
     {(R30 a (ADDR_MODE2_WB opt imm x) * 
       M (ADDR_MODE2_ADDR opt imm x) (addr32 y) * S (sN,sZ,sC,sV),pcSET y)}``,
  ARM_PROG2_INIT_TAC ARM_LDR_NOP
      `a*m*st*cd*cmd*pc*ud` `a*pc*cmd*m*st*ud*cd`
      `a*m*st*cmd*pc*ud` `a*pc*cmd*m*st*ud`
  \\ REWRITE_TAC [SEP_F_def]
  \\ ARM_PROG2_EXPAND_TAC' xR2 xMmm xR2 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ldr_pc []))
  \\ ARM_PROG2_HAMMER_TAC 
  \\ ASM_REWRITE_TAC [ADDR_MODE2_WB_THM,ADDR_MODE2_ADDR_THM,addr30_addr32,
       ADDRESS_ROTATE,pcSET_def]);


(* ----------------------------------------------------------------------------- *)
(* STRB and STR INSTRUCTIONS                                                     *)
(* ----------------------------------------------------------------------------- *)

val strb = FIX_ADDR_MODE2 `T` ARM_STR
val strb = (UNDISCH_ALL o Q.INST [`Rd`|->`a`,`Rn`|->`b`,`c`|->`c_flag`] o DISCH_ALL) strb

val mem_byte_SIMP2 = prove(
  ``~(q = y) ==>
    (mem_byte q
         <|registers := r; psrs := p;
           memory := MEM_WRITE_BYTE s.memory y x; undefined := u; cp_state := cp|> =
     mem_byte q s)``,
  STRIP_TAC 
  \\ STRIP_ASSUME_TAC (Q.SPEC `q` EXISTS_addr32)
  \\ STRIP_ASSUME_TAC (Q.SPEC `y` EXISTS_addr32)
  \\ ASSUME_TAC (EVAL ``((1 >< 0) (0w:word32)):word2``) 
  \\ ASSUME_TAC (EVAL ``((1 >< 0) (1w:word32)):word2``) 
  \\ ASSUME_TAC (EVAL ``((1 >< 0) (2w:word32)):word2``) 
  \\ ASSUME_TAC (EVAL ``((1 >< 0) (3w:word32)):word2``) 
  \\ FULL_SIMP_TAC bool_ss [mem_byte_def,mem_def,MEM_WRITE_BYTE_def,
          UPDATE_def,ADDR30_def,GSYM addr30_def,addr30_addr32,LET_DEF,lower_addr32_ADD,addr32_11]
  \\ SRW_TAC [] [] \\ MATCH_MP_TAC GET_BYTE_SET_BYTE_NEQ \\ EVAL_TAC);

val mem_byte_SIMP3 = prove(
  ``(mem_byte q
         <|registers := r; psrs := p;
           memory := MEM_WRITE_BYTE s.memory q x; undefined := u; cp_state := cp|> =
     x)``,
  SIMP_TAC (srw_ss()) [mem_byte_def,mem_def,MEM_WRITE_BYTE_def,UPDATE_def,ADDR30_def,
    GSYM addr30_def,LET_DEF,GET_BYTE_SET_BYTE]);

val mem_byte_SIMP4 = prove(
  ``~(p' = addr30 q) ==>
    (mem p'
         <|registers := r; psrs := p;
           memory := MEM_WRITE_BYTE s.memory q x; undefined := u; cp_state := cp|> =
     mem p' s)``,
  SIMP_TAC (srw_ss()) [mem_byte_def,mem_def,MEM_WRITE_BYTE_def,UPDATE_def,ADDR30_def,
    GSYM addr30_def,LET_DEF,GET_BYTE_SET_BYTE]);

val arm_STRB = store_thm("arm_STRB",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
     (R a x * R b y * byte (ADDR_MODE2_ADDR' opt imm y) z * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV))
     [enc (STR c_flag T opt a b (Dt_immediate imm))] {}
     (R a x * R b (ADDR_MODE2_WB' opt imm y) * byte (ADDR_MODE2_ADDR' opt imm y) ((7 >< 0) x) *
      S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_STR_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmb
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean strb []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ SIMP_TAC bool_ss [mem_byte_SIMP2,mem_byte_SIMP3]
  \\ FULL_SIMP_TAC std_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,IN_INSERT,NOT_IN_EMPTY]
  \\ Cases_on `p = addr30 (ADDR_MODE2_ADDR' opt imm y)`  
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP4]
  \\ STRIP_ASSUME_TAC (Q.SPEC `ADDR_MODE2_ADDR' opt imm y` EXISTS_addr32) 
  \\ FULL_SIMP_TAC bool_ss [addr32_11,addr30_addr32]);

val str = FIX_ADDR_MODE2 `F` ARM_STR
val str = (UNDISCH_ALL o Q.INST [`Rd`|->`a`,`Rn`|->`b`,`c`|->`c_flag`] o DISCH_ALL) str

val mem_SIMP_EQ = prove(
  ``mem (addr30 z) <|registers := r; psrs := p;
          memory := MEM_WRITE_WORD s.memory z x; undefined := u; cp_state := cp|> = x``,
  SRW_TAC [] [mem_def,MEM_WRITE_WORD_def,UPDATE_def,ADDR30_def,addr30_def]);

val mem_SIMP_avoid_LEMMA = prove(
  ``~(p = addr32 (addr30 y) + 0w) /\
    ~(p = addr32 (addr30 y) + 1w) /\
    ~(p = addr32 (addr30 y) + 2w) /\
    ~(p = addr32 (addr30 y) + 3w) = ~(addr30 p = addr30 y)``,
  STRIP_ASSUME_TAC (Q.SPEC `p` EXISTS_addr32)
  \\ STRIP_ASSUME_TAC (Q.SPEC `y` EXISTS_addr32)
  \\ ASM_SIMP_TAC bool_ss [addr32_11,addr30_addr32,addr32_NEQ_addr32]);

val mem_byte_SIMP_avoid = prove(
  ``~(addr30 p' = addr30 q) ==>
    (mem_byte p'
       <|registers := r; psrs := p;
         memory := MEM_WRITE_WORD s.memory q x; undefined := F; cp_state := cp|> =
     mem_byte p' s)``,
  SIMP_TAC (srw_ss()) [mem_byte_def,mem_def,MEM_WRITE_WORD_def,ADDR30_def,GSYM addr30_def,UPDATE_def]);

val mem_SIMP_avoid = prove(
  ``~(q = addr30 y) ==> (mem q
       <|registers := r; psrs := p;
         memory := MEM_WRITE_WORD s.memory y x; undefined := u; cp_state := cp|> = mem q s)``,
  SRW_TAC [] [mem_def,MEM_WRITE_WORD_def,UPDATE_def,ADDR30_def,addr30_def]);

val arm_STR_NONALIGNED = store_thm("arm_STR_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * M (addr30 (ADDR_MODE2_ADDR' opt imm y)) z *
      S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
     [enc (STR c_flag F opt a b (Dt_immediate imm))] {}
     (R a x * R b (ADDR_MODE2_WB' opt imm y) *
      M (addr30 (ADDR_MODE2_ADDR' opt imm y)) x * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_STR_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean str []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ REWRITE_TAC [RW[WORD_ADD_0]mem_SIMP_avoid_LEMMA]   
  \\ SIMP_TAC bool_ss [mem_byte_SIMP_avoid]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,IN_INSERT,NOT_IN_EMPTY,addr32_11]
  \\ ASM_SIMP_TAC bool_ss [mem_SIMP_EQ,mem_SIMP_avoid]);
  
val arm_STR = save_thm("arm_STR",AM2_ALIGN_ADDRESSES `y` arm_STR_NONALIGNED);

val arm_STR_SEQ = save_thm("arm_STR_SEQ",let
  val MOVE_M = prove(``!x y P. M x y * P = P * M x y``,METIS_TAC [STAR_COMM])
  val th = RW [STAR_ASSOC] (RW1 [MOVE_M] (RW [GSYM STAR_ASSOC] arm_STR_NONALIGNED))
  val th = SPEC_ALL (MATCH_MP ARM_PROG_INTRO_SEQ_WR (Q.GEN `z` th))
  in th end);
  

(* ----------------------------------------------------------------------------- *)
(* SWPB and SWP INSTRUCTIONS                                                     *)
(* ----------------------------------------------------------------------------- *)

val swpb = Q.INST [`b`|->`T`] (SPEC_ALL ARM_SWP)
val swpb = RW [FORMAT_UnsignedWord,FORMAT_UnsignedByte] swpb
val swpb = (Q.INST [`Rm`|->`a`,`Rd`|->`b`,`Rn`|->`c`,`c`|->`c_flag`] o DISCH_ALL) swpb

val arm_SWPB3 = store_thm("arm_SWPB3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * R c z * byte z q * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV)) [enc (SWP c_flag T b a c)] {}
     (R a x * R b (w2w q) * R c z * byte z ((7 >< 0) x) * 
      S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SWP_NOP
      `a*b*c*m*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*m*st*ud*cd`
      `a*b*c*m*st*cmd*pc*ud` `a*b*c*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMmb
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean swpb []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP3,mem_byte_SIMP2]
  \\ FULL_SIMP_TAC std_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,IN_INSERT,NOT_IN_EMPTY]
  \\ Cases_on `p = addr30 z`  
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP4]
  \\ STRIP_ASSUME_TAC (Q.SPEC `z` EXISTS_addr32)
  \\ FULL_SIMP_TAC bool_ss [addr30_addr32,addr32_11]);

val swpb2 = Q.INST [`b`|->`a`,`c`|->`b`] swpb

val arm_SWPB2 = store_thm("arm_SWPB2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * byte y q * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV)) 
     [enc (SWP c_flag T a a b)] {}
     (R a (w2w q) * R b y * byte y ((7 >< 0) x) * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SWP_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmb
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean swpb2 []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP3,mem_byte_SIMP2]
  \\ FULL_SIMP_TAC std_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,IN_INSERT,NOT_IN_EMPTY]
  \\ Cases_on `p = addr30 y`  
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP4]
  \\ STRIP_ASSUME_TAC (Q.SPEC `y` EXISTS_addr32)
  \\ FULL_SIMP_TAC bool_ss [addr30_addr32,addr32_11]);

val swp = Q.INST [`b`|->`F`] (SPEC_ALL ARM_SWP)
val swp = RW [FORMAT_UnsignedWord,FORMAT_UnsignedByte] swp
val swp = (Q.INST [`Rm`|->`a`,`Rd`|->`b`,`Rn`|->`c`,`c`|->`c_flag`] o DISCH_ALL) swp

val arm_SWP3_NONALIGNED = store_thm("arm_SWP3_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * R c z * M (addr30 z) q * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV)) [enc (SWP c_flag F b a c)] {}
     (R a x * R b (q #>> (8 * w2n (((1 >< 0) z):word2))) * R c z *
      M (addr30 z) x * S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SWP_NOP
      `a*b*c*m*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*m*st*ud*cd`
      `a*b*c*m*st*cmd*pc*ud` `a*b*c*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean swp []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ FULL_SIMP_TAC std_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,
       IN_INSERT,NOT_IN_EMPTY,addr32_11]
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP4]
  \\ ASM_SIMP_TAC bool_ss [mem_SIMP_EQ,RW[WORD_ADD_0]mem_SIMP_avoid_LEMMA,
       mem_SIMP_avoid,mem_byte_SIMP_avoid]);

val arm_SWP3_SEQ_LEMMA = prove(
  ``!q. (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * R c z * S (sN,sZ,sC,sV) * cond (z && 3w = 0w) *
      PASS c_flag (sN,sZ,sC,sV) * M (addr30 z) q) [enc (SWP c_flag F b a c)] {}
     ((\q. R a x * R b q * R c z * S (sN,sZ,sC,sV)) q * 
      M (addr30 z) x) {}``,
  SIMP_TAC std_ss []
  \\ MOVE_STAR_TAC `a*b*c*s*m` `a*b*c*m*s`
  \\ MOVE_STAR_TAC `a*b*c*s*c'*m*p` `a*b*c*m*s*p*c'`
  \\ Cases_on `z && 3w = 0w`
  \\ ASM_SIMP_TAC (bool_ss++sep_ss) []
  THEN1 (IMP_RES_TAC addr32_addr30 \\ METIS_TAC [ADDRESS_ROTATE,arm_SWP3_NONALIGNED])
  \\ REWRITE_TAC [ARM_PROG2_def,ARM_PROG_FALSE_PRE]
  \\ METIS_TAC [arm_SWP3_NONALIGNED,ARM_PROG2_def]);

val arm_SWP3_SEQ = save_thm("arm_SWP3_SEQ",let
  val th = MATCH_MP ARM_PROG_INTRO_SEQ_RD_WR arm_SWP3_SEQ_LEMMA
  val th = SPEC_ALL (SIMP_RULE std_ss [] th)
  in th end);

val arm_SWP3 = Q.INST [`z`|->`addr32 z`] arm_SWP3_NONALIGNED
val arm_SWP3 = RW [GSYM R30_def,addr30_addr32,ADDRESS_ROTATE] arm_SWP3
val arm_SWP3 = save_thm("arm_SWP3",arm_SWP3);
  
val swp2 = Q.INST [`b`|->`a`,`c`|->`b`] swp

val arm_SWP2_NONALIGNED = store_thm("arm_SWP2_NONALIGNED",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * M (addr30 y) q * S (sN,sZ,sC,sV) *
      PASS c_flag (sN,sZ,sC,sV)) [enc (SWP c_flag F a a b)] {}
     (R a (q #>> (8 * w2n (((1 >< 0) y):word2))) * R b y * M (addr30 y) x *
      S (sN,sZ,sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SWP_NOP
      `a*b*m*st*cd*cmd*pc*ud` `a*b*pc*cmd*m*st*ud*cd`
      `a*b*m*st*cmd*pc*ud` `a*b*pc*cmd*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMmm
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean swp2 []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ FULL_SIMP_TAC std_ss [ALL_DISJOINT_def,EVERY_DEF,DISJOINT_INSERT,
       IN_INSERT,NOT_IN_EMPTY,addr32_11]
  \\ ASM_SIMP_TAC bool_ss [mem_byte_SIMP4]
  \\ ASM_SIMP_TAC bool_ss [mem_SIMP_EQ,RW[WORD_ADD_0]mem_SIMP_avoid_LEMMA,
       mem_SIMP_avoid,mem_byte_SIMP_avoid]);

val arm_SWP2_SEQ_LEMMA = prove(
  ``!q. (ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
     (R a x * R b y * S (sN,sZ,sC,sV) * cond (y && 3w = 0w) *
      PASS c_flag (sN,sZ,sC,sV) * M (addr30 y) q) [enc (SWP c_flag F a a b)] {}
     ((\q. R a q * R b y * S (sN,sZ,sC,sV)) q * 
      M (addr30 y) x) {}``,
  SIMP_TAC std_ss []
  \\ MOVE_STAR_TAC `a*b*s*m` `a*b*m*s`
  \\ MOVE_STAR_TAC `a*b*s*c'*m*p` `a*b*m*s*p*c'`
  \\ Cases_on `y && 3w = 0w`
  \\ ASM_SIMP_TAC (bool_ss++sep_ss) []
  THEN1 (IMP_RES_TAC addr32_addr30 \\ METIS_TAC [ADDRESS_ROTATE,arm_SWP2_NONALIGNED])
  \\ REWRITE_TAC [ARM_PROG2_def,ARM_PROG_FALSE_PRE]
  \\ METIS_TAC [arm_SWP2_NONALIGNED,ARM_PROG2_def]);

val arm_SWP2_SEQ = save_thm("arm_SWP2_SEQ",let
  val th = MATCH_MP ARM_PROG_INTRO_SEQ_RD_WR arm_SWP2_SEQ_LEMMA
  val th = SPEC_ALL (SIMP_RULE std_ss [] th)
  in th end);

val arm_SWP2 = Q.INST [`y`|->`addr32 y`] arm_SWP2_NONALIGNED
val arm_SWP2 = RW [GSYM R30_def,addr30_addr32,ADDRESS_ROTATE] arm_SWP2
val arm_SWP2 = save_thm("arm_SWP2",arm_SWP2);


(* ----------------------------------------------------------------------------- *)
(* COMPARISON INSTRUCTIONS                                                       *)
(* ----------------------------------------------------------------------------- *)

fun simple_clean_AM1 s th =
  (UNDISCH_ALL ((Q.INST s o Q.INST [`c`|->`c_flag`]) (simple_clean (FIX_ADDR_MODE1 th) [])));

val arm_CMN1 = store_thm("arm_CMN1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (CMN c_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            S
              (word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC)),
               x + SND (ADDR_MODE1_VAL a_mode x sC) = 0w,
               2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode x sC))),
               (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
               ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC))))) {}``,
  ARM_PROG2_INIT_TAC ARM_CMN_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`a`] ARM_CMN)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_CMN2 = store_thm("arm_CMN2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (CMN c_flag a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            S
              (word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC)),
               x + SND (ADDR_MODE1_VAL a_mode y sC) = 0w,
               2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC))),
               (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
               ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC))))) {}``,
  ARM_PROG2_INIT_TAC ARM_CMN_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`b`] ARM_CMN)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_CMP1 = store_thm("arm_CMP1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (CMP c_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            S
              (word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC)),
               x = SND (ADDR_MODE1_VAL a_mode x sC),
               SND (ADDR_MODE1_VAL a_mode x sC) <=+ x,
                ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
               ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC))))) {}``,
  ARM_PROG2_INIT_TAC ARM_CMP_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`a`] ARM_CMP)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_CMP2 = store_thm("arm_CMP2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (CMP c_flag a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            S
              (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC)),
               x = SND (ADDR_MODE1_VAL a_mode y sC),
               SND (ADDR_MODE1_VAL a_mode y sC) <=+ x,
                ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
               ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC))))) {}``,
  ARM_PROG2_INIT_TAC ARM_CMP_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`b`] ARM_CMP)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_TST1 = store_thm("arm_TST1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (TST c_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            S
              (word_msb (x && SND (ADDR_MODE1_VAL a_mode x sC)),
               x && SND (ADDR_MODE1_VAL a_mode x sC) = 0w,
               FST (ADDR_MODE1_VAL a_mode x sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_TST_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`a`] ARM_TST)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_TST2 = store_thm("arm_TST2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (TST c_flag a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            S
              (word_msb (x && SND (ADDR_MODE1_VAL a_mode y sC)),
               x && SND (ADDR_MODE1_VAL a_mode y sC) = 0w,
               FST (ADDR_MODE1_VAL a_mode y sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_TST_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`b`] ARM_TST)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_TEQ1 = store_thm("arm_TEQ1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (TEQ c_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            S
              (word_msb (x ?? SND (ADDR_MODE1_VAL a_mode x sC)),
               x = SND (ADDR_MODE1_VAL a_mode x sC),
               FST (ADDR_MODE1_VAL a_mode x sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_TEQ_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`a`] ARM_TEQ)
  \\ ARM_PROG2_HAMMER_TAC);

val arm_TEQ2 = store_thm("arm_TEQ2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (TEQ c_flag a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            S
              (word_msb (x ?? SND (ADDR_MODE1_VAL a_mode y sC)),
               x = SND (ADDR_MODE1_VAL a_mode y sC),
               FST (ADDR_MODE1_VAL a_mode y sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_TEQ_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC (simple_clean_AM1 [`Rm`|->`a`,`Rn`|->`b`] ARM_TEQ)
  \\ ARM_PROG2_HAMMER_TAC);


(* ----------------------------------------------------------------------------- *)
(* MONOP INSTRUCTIONS                                                            *)
(* ----------------------------------------------------------------------------- *)

val arm_MOV1 = store_thm("arm_MOV1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MOV c_flag s_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) else sN),
               (if s_flag then SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MOV_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MOV)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MOV2 = store_thm("arm_MOV2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MOV c_flag s_flag b (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) else sN),
               (if s_flag then SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MOV_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MOV)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MVN1 = store_thm("arm_MVN1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MVN c_flag s_flag a (ADDR_MODE1_CMD a_mode a))] {}
           (R a ~SND (ADDR_MODE1_VAL a_mode x sC) *
            S
              ((if s_flag then word_msb ~SND (ADDR_MODE1_VAL a_mode x sC) else sN),
               (if s_flag then SND (ADDR_MODE1_VAL a_mode x sC) = UINT_MAXw else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MVN_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MVN)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MVN2 = store_thm("arm_MVN2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MVN c_flag s_flag b (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b ~SND (ADDR_MODE1_VAL a_mode x sC) *
            S
              ((if s_flag then word_msb ~SND (ADDR_MODE1_VAL a_mode x sC) else sN),
               (if s_flag then SND (ADDR_MODE1_VAL a_mode x sC) = UINT_MAXw else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MVN_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MVN)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);


(* ----------------------------------------------------------------------------- *)
(* 32 bit MULTIPLICATION INSTRUCTIONS                                            *)
(* ----------------------------------------------------------------------------- *)

val arm_MUL3 = store_thm("arm_MUL3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MUL c_flag s_flag c a b)] {}
           (R a x * R b y * R c (x * y) *
            S
              ((if s_flag then word_msb (x * y) else sN),
               (if s_flag then x * y = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MUL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_MUL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MUL2 = store_thm("arm_MUL2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MUL c_flag s_flag b a b)] {}
           (R a x * R b (x * y) *
            S
              ((if s_flag then word_msb (x * y) else sN),
               (if s_flag then x * y = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MUL_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ `~(b = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`b`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_MUL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MUL2'' = store_thm("arm_MUL2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MUL c_flag s_flag b a a)] {}
           (R a x * R b (x * x) *
            S
              ((if s_flag then word_msb (x * x) else sN),
               (if s_flag then x * x = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MUL_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ `~(b = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`b`,`Rm`|->`a`,`Rs`|->`a`,`c`|->`c_flag`] (SPEC_ALL ARM_MUL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MLA4 = store_thm("arm_MLA4",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c k * R d z * S (sN,sZ,sC,sV) *
            PASS c_flag (sN,sZ,sC,sV)) [enc (MLA c_flag s_flag d a b c)] {}
           (R a x * R b y * R c k * R d (k + x * y) *
            S
              ((if s_flag then word_msb (k + x * y) else sN),
               (if s_flag then k + x * y = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MLA_NOP
      `a*b*c*d*st*cd*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud*cd`
      `a*b*c*d*st*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR5 xMm
  \\ `~(d = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`d`,`Rm`|->`a`,`Rs`|->`b`,`Rn`|->`c`,`c`|->`c_flag`] (SPEC_ALL ARM_MLA)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MLA3 = store_thm("arm_MLA3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MLA c_flag s_flag c a c b)] {}
           (R a x * R b y * R c (y + x * z) *
            S
              ((if s_flag then word_msb (y + x * z) else sN),
               (if s_flag then y + x * z = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MLA_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`c`,`Rm`|->`a`,`Rs`|->`c`,`Rn`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_MLA)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MLA3' = store_thm("arm_MLA3'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MLA c_flag s_flag c a b c)] {}
           (R a x * R b y * R c (z + x * y) *
            S
              ((if s_flag then word_msb (z + x * y) else sN),
               (if s_flag then z + x * y = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MLA_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`Rn`|->`c`,`c`|->`c_flag`] (SPEC_ALL ARM_MLA)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_MLA3'' = store_thm("arm_MLA3''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (MLA c_flag s_flag c a a b)] {}
           (R a x * R b y * R c (y + x * x) *
            S
              ((if s_flag then word_msb (y + x * x) else sN),
               (if s_flag then y + x * x = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_MLA_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)` by METIS_TAC []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [`Rd`|->`c`,`Rm`|->`a`,`Rs`|->`a`,`Rn`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_MLA)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);



(* ----------------------------------------------------------------------------- *)
(* 64 bit MULTIPLICATION INSTRUCTIONS                                            *)
(* ----------------------------------------------------------------------------- *)

val arm_UMULL4 = store_thm("arm_UMULL4",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * R c' z' * S (sN,sZ,sC,sV) *
            PASS c_flag (sN,sZ,sC,sV)) [enc (UMULL c_flag s_flag c c' a b)] {}
           (R a x * R b y * R c (x * y) * R c' ((63 >< 32) (w2w x * (w2w y):word64)) *
            S
              ((if s_flag then word_msb ((w2w x * w2w y):word64) else sN),
               (if s_flag then (w2w x * w2w y):word64 = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMULL_NOP
      `a*b*c*d*st*cd*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud*cd`
      `a*b*c*d*st*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR5 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_UMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_UMULL3 = store_thm("arm_UMULL3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (UMULL c_flag s_flag c c' a c)] {}
           (R a x * R c (x * z) * R c' ((63 >< 32) ((w2w x * w2w z):word64)) *
            S
              ((if s_flag then word_msb ((w2w x * w2w z):word64) else sN),
               (if s_flag then w2w x * w2w z = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`c`,`c`|->`c_flag`] (SPEC_ALL ARM_UMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_UMULL3' = store_thm("arm_UMULL3'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (UMULL c_flag s_flag c c' a c')] {}
           (R a x * R c (x * z') * R c' ((63 >< 32) ((w2w x * w2w z'):word64)) *
            S
              ((if s_flag then word_msb ((w2w x * w2w z'):word64) else sN),
               (if s_flag then w2w x * w2w z' = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`c'`,`c`|->`c_flag`] (SPEC_ALL ARM_UMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_UMULL3'' = store_thm("arm_UMULL3''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (UMULL c_flag s_flag c c' a a)] {}
           (R a x * R c (x * x) * R c' ((63 >< 32) ((w2w x * w2w x):word64)) *
            S
              ((if s_flag then word_msb ((w2w x * w2w x):word64) else sN),
               (if s_flag then w2w x * w2w x = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)/\ ~(c = 15w)/\ ~(c' = a)/\ ~(c' = c)/\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`a`,`c`|->`c_flag`] (SPEC_ALL ARM_UMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMULL4 = store_thm("arm_SMULL4",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * R c' z' * S (sN,sZ,sC,sV) *
            PASS c_flag (sN,sZ,sC,sV)) [enc (SMULL c_flag s_flag c c' a b)] {}
           (R a x * R b y * R c ((31 >< 0) ((sw2sw x * sw2sw y):word64)) *
            R c' ((63 >< 32) ((sw2sw x * sw2sw y):word64)) *
            S
              ((if s_flag then word_msb ((sw2sw x * sw2sw y):word64) else sN),
               (if s_flag then sw2sw x * sw2sw y = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMULL_NOP
      `a*b*c*d*st*cd*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud*cd`
      `a*b*c*d*st*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR5 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_SMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMULL3 = store_thm("arm_SMULL3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SMULL c_flag s_flag c c' a c)] {}
           (R a x * R c ((31 >< 0) ((sw2sw x * sw2sw z):word64)) *
            R c' ((63 >< 32) ((sw2sw x * sw2sw z):word64)) *
            S
              ((if s_flag then word_msb ((sw2sw x * sw2sw z):word64) else sN),
               (if s_flag then sw2sw x * sw2sw z = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`c`,`c`|->`c_flag`] (SPEC_ALL ARM_SMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMULL3' = store_thm("arm_SMULL3'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SMULL c_flag s_flag c c' a c')] {}
           (R a x * R c ((31 >< 0) ((sw2sw x * sw2sw z'):word64)) *
            R c' ((63 >< 32) ((sw2sw x * sw2sw z'):word64)) *
            S
              ((if s_flag then word_msb ((sw2sw x * sw2sw z'):word64) else sN),
               (if s_flag then sw2sw x * sw2sw z' = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`c'`,`c`|->`c_flag`] (SPEC_ALL ARM_SMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMULL3'' = store_thm("arm_SMULL3''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SMULL c_flag s_flag c c' a a)] {}
           (R a x * R c ((31 >< 0) ((sw2sw x * sw2sw x):word64)) *
            R c' ((63 >< 32) ((sw2sw x * sw2sw x):word64)) *
            S
              ((if s_flag then word_msb ((sw2sw x * sw2sw x):word64) else sN),
               (if s_flag then sw2sw x * sw2sw x = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMULL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)/\ ~(c = 15w)/\ ~(c' = a)/\ ~(c' = c)/\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`a`,`c`|->`c_flag`] (SPEC_ALL ARM_SMULL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_UMLAL4 = store_thm("arm_UMLAL4",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * R c' z' * S (sN,sZ,sC,sV) *
            PASS c_flag (sN,sZ,sC,sV)) [enc (UMLAL c_flag s_flag c c' a b)] {}
           (R a x * R b y * R c ((31 >< 0) ((z' @@ z + w2w x * w2w y):word64)) * 
            R c' ((63 >< 32) (z' @@ z + w2w x * (w2w y):word64)) *
            S
              ((if s_flag then word_msb ((z' @@ z + w2w x * w2w y):word64) else sN),
               (if s_flag then (z' @@ z + w2w x * w2w y):word64 = 0w else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMLAL_NOP
      `a*b*c*d*st*cd*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud*cd`
      `a*b*c*d*st*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR5 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_UMLAL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_UMLAL3'' = store_thm("arm_UMLAL3''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (UMLAL c_flag s_flag c c' a a)] {}
           (R a x * R c ((31 >< 0) ((z' @@ z + w2w x * w2w x):word64)) * 
            R c' ((63 >< 32) ((z' @@ z + w2w x * w2w x):word64)) *
            S
              ((if s_flag then word_msb ((z' @@ z + w2w x * w2w x):word64) else sN),
               (if s_flag then z' @@ z + w2w x * w2w x = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_UMLAL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)/\ ~(c = 15w)/\ ~(c' = a)/\ ~(c' = c)/\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`a`,`c`|->`c_flag`] (SPEC_ALL ARM_UMLAL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMLAL4 = store_thm("arm_SMLAL4",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * R c' z' * S (sN,sZ,sC,sV) *
            PASS c_flag (sN,sZ,sC,sV)) [enc (SMLAL c_flag s_flag c c' a b)] {}
           (R a x * R b y * R c ((31 >< 0) (z' @@ z + (sw2sw x * sw2sw y):word64)) *
            R c' ((63 >< 32) (z' @@ z + (sw2sw x * sw2sw y):word64)) *
            S
              ((if s_flag then word_msb (z' @@ z + (sw2sw x * sw2sw y):word64) else sN),
               (if s_flag then z' @@ z + sw2sw x * sw2sw y = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMLAL_NOP
      `a*b*c*d*st*cd*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud*cd`
      `a*b*c*d*st*cmd*pc*ud` `a*b*c*d*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR5 xMm
  \\ `~(c = a) /\ ~(c = 15w) /\ ~(c' = a) /\ ~(c' = c) /\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`b`,`c`|->`c_flag`] (SPEC_ALL ARM_SMLAL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_SMLAL3'' = store_thm("arm_SMLAL3''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R c z * R c' z' * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SMLAL c_flag s_flag c c' a a)] {}
           (R a x * R c ((31 >< 0) ((z' @@ z + sw2sw x * sw2sw x):word64)) *
            R c' ((63 >< 32) ((z' @@ z + sw2sw x * sw2sw x):word64)) *
            S
              ((if s_flag then word_msb ((z' @@ z + sw2sw x * sw2sw x):word64) else sN),
               (if s_flag then z' @@ z + sw2sw x * sw2sw x = 0w:word64 else sZ),sC,sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_SMLAL_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ `~(c = a)/\ ~(c = 15w)/\ ~(c' = a)/\ ~(c' = c)/\ ~(c' = 15w)` by ASM_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      (UNDISCH_ALL (simple_clean (Q.INST [
        `RdHi`|->`c'`,`RdLo`|->`c`,`Rm`|->`a`,`Rs`|->`a`,`c`|->`c_flag`] (SPEC_ALL ARM_SMLAL)) []))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);


(* ----------------------------------------------------------------------------- *)
(* BINOP INSTRUCTIONS EXCEPT MULTIPLICATION                                      *)
(* ----------------------------------------------------------------------------- *)

val arm_ADC1 = store_thm("arm_ADC1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADC c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w)) *
            S
              (if s_flag then
                 (word_msb
                    (x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w)),
                  x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w) = 0w,
                  2**32 <=
                    w2n x + w2n (SND (ADDR_MODE1_VAL a_mode x sC)) + (if sC then 1 else 0),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x =
                    word_msb
                      (x + SND (ADDR_MODE1_VAL a_mode x sC) +
                       (if sC then 1w else 0w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADC_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADD1 = store_thm("arm_ADD1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADD c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x + SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              (if s_flag then
                 (word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC)),
                  x + SND (ADDR_MODE1_VAL a_mode x sC) = 0w,
                  2**32 <= w2n x + w2n (SND (ADDR_MODE1_VAL a_mode x sC)),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADD_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADD)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_AND1 = store_thm("arm_AND1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (AND c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x && SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x && SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x && SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_AND_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_AND)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_BIC1 = store_thm("arm_BIC1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (BIC c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x && ~SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x && ~SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x && ~SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_BIC_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_BIC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_EOR1 = store_thm("arm_EOR1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (EOR c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x ?? SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x ?? SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x = SND (ADDR_MODE1_VAL a_mode x sC) else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_EOR_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_EOR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ORR1 = store_thm("arm_ORR1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ORR c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x !! SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x !! SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x !! SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_ORR_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ORR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSB1 = store_thm("arm_RSB1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSB c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (SND (ADDR_MODE1_VAL a_mode x sC) - x) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x),
                  SND (ADDR_MODE1_VAL a_mode x sC) = x,
                  x <=+ SND (ADDR_MODE1_VAL a_mode x sC),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x)))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSB_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSC1 = store_thm("arm_RSC1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSC c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w)),
                  SND (ADDR_MODE1_VAL a_mode x sC) = (if sC then 0w else 1w) + x,
                  (if sC then x <=+ SND (ADDR_MODE1_VAL a_mode x sC) 
                         else 2**32 <= (w2n (SND (ADDR_MODE1_VAL a_mode x sC)) + w2n ~x)),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSC_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SBC1 = store_thm("arm_SBC1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SBC c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w)),
                  x = (if sC then 0w else 1w) + SND (ADDR_MODE1_VAL a_mode x sC),
                  (if sC then SND (ADDR_MODE1_VAL a_mode x sC) <=+ x  
                         else 2**32 <= (w2n x + w2n ~(SND (ADDR_MODE1_VAL a_mode x sC)))),
                  ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x =
                    word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SBC_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SBC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SUB1 = store_thm("arm_SUB1",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SUB c_flag s_flag a a (ADDR_MODE1_CMD a_mode a))] {}
           (R a (x - SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC)),
                  x = SND (ADDR_MODE1_VAL a_mode x sC),
                  SND (ADDR_MODE1_VAL a_mode x sC) <=+ x,
                   ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SUB_NOP
      `a*st*cd*cmd*pc*ud` `a*pc*cmd*st*ud*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SUB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADC2 = store_thm("arm_ADC2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADC c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x *
            R b (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)) *
            S
              (if s_flag then
                 (word_msb
                    (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w) =
                  0w,
                  2**32 <=
                    (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC)) +
                     (if sC then 1 else 0)),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb
                      (x + SND (ADDR_MODE1_VAL a_mode y sC) +
                       (if sC then 1w else 0w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADD2 = store_thm("arm_ADD2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADD c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x + SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              (if s_flag then
                 (word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) = 0w,
                  2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC))),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADD_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADD)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_AND2 = store_thm("arm_AND2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (AND c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x && SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x && SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_AND_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_AND)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_BIC2 = store_thm("arm_BIC2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (BIC c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x && ~SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x && ~SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && ~SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_BIC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_BIC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_EOR2 = store_thm("arm_EOR2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (EOR c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x ?? SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x ?? SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x = SND (ADDR_MODE1_VAL a_mode y sC) else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_EOR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_EOR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ORR2 = store_thm("arm_ORR2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ORR c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x !! SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x !! SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x !! SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_ORR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ORR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSB2 = store_thm("arm_RSB2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSB c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (SND (ADDR_MODE1_VAL a_mode y sC) - x) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x),
                  SND (ADDR_MODE1_VAL a_mode y sC) = x,
                  x <=+ SND (ADDR_MODE1_VAL a_mode y sC),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x)))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSC2 = store_thm("arm_RSC2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSC c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x *
            R b (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)),
                  SND (ADDR_MODE1_VAL a_mode y sC) = (if sC then 0w else 1w) + x,
                  (if sC then x <=+ SND (ADDR_MODE1_VAL a_mode y sC) 
                         else 2**32 <= (w2n (SND (ADDR_MODE1_VAL a_mode y sC)) + w2n ~x)),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SBC2 = store_thm("arm_SBC2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SBC c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)),
                  x = (if sC then 0w else 1w) + SND (ADDR_MODE1_VAL a_mode y sC),
                  (if sC then SND (ADDR_MODE1_VAL a_mode y sC) <=+ x  
                         else 2**32 <= (w2n x + w2n ~(SND (ADDR_MODE1_VAL a_mode y sC)))),
                  ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SBC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SBC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SUB2 = store_thm("arm_SUB2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SUB c_flag s_flag b a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b (x - SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC)),
                  x = SND (ADDR_MODE1_VAL a_mode y sC),
                  SND (ADDR_MODE1_VAL a_mode y sC) <=+ x,
                   ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SUB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SUB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADC2' = store_thm("arm_ADC2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADC c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)) *
            R b y *
            S
              (if s_flag then
                 (word_msb
                    (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w) =
                  0w,
                  2**32 <=
                    (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC)) +
                     (if sC then 1 else 0)),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb
                      (x + SND (ADDR_MODE1_VAL a_mode y sC) +
                       (if sC then 1w else 0w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADD2' = store_thm("arm_ADD2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADD c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x + SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              (if s_flag then
                 (word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) = 0w,
                  2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC))),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADD_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADD)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_AND2' = store_thm("arm_AND2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (AND c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x && SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              ((if s_flag then
                  word_msb (x && SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_AND_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_AND)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_BIC2' = store_thm("arm_BIC2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (BIC c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x && ~SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              ((if s_flag then
                  word_msb (x && ~SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && ~SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_BIC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_BIC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_EOR2' = store_thm("arm_EOR2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (EOR c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x ?? SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              ((if s_flag then
                  word_msb (x ?? SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x = SND (ADDR_MODE1_VAL a_mode y sC) else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_EOR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_EOR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ORR2' = store_thm("arm_ORR2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ORR c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x !! SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              ((if s_flag then
                  word_msb (x !! SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x !! SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_ORR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ORR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSB2' = store_thm("arm_RSB2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSB c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (SND (ADDR_MODE1_VAL a_mode y sC) - x) * R b y *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x),
                  SND (ADDR_MODE1_VAL a_mode y sC) = x,
                  x <=+ SND (ADDR_MODE1_VAL a_mode y sC),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x)))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSC2' = store_thm("arm_RSC2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSC c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)) * R b y *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)),
                  SND (ADDR_MODE1_VAL a_mode y sC) = (if sC then 0w else 1w) + x,
                  (if sC then x <=+ SND (ADDR_MODE1_VAL a_mode y sC) 
                         else 2**32 <= (w2n (SND (ADDR_MODE1_VAL a_mode y sC)) + w2n ~x)),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SBC2' = store_thm("arm_SBC2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SBC c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)) * R b y *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)),
                  x = (if sC then 0w else 1w) + SND (ADDR_MODE1_VAL a_mode y sC),
                  (if sC then SND (ADDR_MODE1_VAL a_mode y sC) <=+ x  
                         else 2**32 <= (w2n x + w2n ~(SND (ADDR_MODE1_VAL a_mode y sC)))),
                  ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SBC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SBC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SUB2' = store_thm("arm_SUB2'",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SUB c_flag s_flag a a (ADDR_MODE1_CMD a_mode b))] {}
           (R a (x - SND (ADDR_MODE1_VAL a_mode y sC)) * R b y *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC)),
                  x = SND (ADDR_MODE1_VAL a_mode y sC),
                  SND (ADDR_MODE1_VAL a_mode y sC) <=+ x,
                   ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SUB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SUB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADC2'' = store_thm("arm_ADC2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADC c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            R b (x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w)) *
            S
              (if s_flag then
                 (word_msb
                    (x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w)),
                  x + SND (ADDR_MODE1_VAL a_mode x sC) + (if sC then 1w else 0w) =
                  0w,
                  2**32 <=
                    (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode x sC)) +
                     (if sC then 1 else 0)),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x =
                    word_msb
                      (x + SND (ADDR_MODE1_VAL a_mode x sC) +
                       (if sC then 1w else 0w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADD2'' = store_thm("arm_ADD2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADD c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x + SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              (if s_flag then
                 (word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC)),
                  x + SND (ADDR_MODE1_VAL a_mode x sC) = 0w,
                  2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode x sC))),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode x sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADD_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADD)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_AND2'' = store_thm("arm_AND2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (AND c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x && SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x && SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x && SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_AND_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_AND)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_BIC2'' = store_thm("arm_BIC2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (BIC c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x && ~SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x && ~SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x && ~SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_BIC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_BIC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_EOR2'' = store_thm("arm_EOR2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (EOR c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x ?? SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x ?? SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x = SND (ADDR_MODE1_VAL a_mode x sC) else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_EOR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_EOR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ORR2'' = store_thm("arm_ORR2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ORR c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x !! SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              ((if s_flag then
                  word_msb (x !! SND (ADDR_MODE1_VAL a_mode x sC))
                else
                  sN),
               (if s_flag then x !! SND (ADDR_MODE1_VAL a_mode x sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode x sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_ORR_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ORR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSB2'' = store_thm("arm_RSB2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSB c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (SND (ADDR_MODE1_VAL a_mode x sC) - x) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x),
                  SND (ADDR_MODE1_VAL a_mode x sC) = x,
                  x <=+ SND (ADDR_MODE1_VAL a_mode x sC),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x)))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSC2'' = store_thm("arm_RSC2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSC c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x *
            R b (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w)),
                  SND (ADDR_MODE1_VAL a_mode x sC) = (if sC then 0w else 1w) + x,
                  (if sC then x <=+ SND (ADDR_MODE1_VAL a_mode x sC) 
                         else 2**32 <= (w2n (SND (ADDR_MODE1_VAL a_mode x sC)) + w2n ~x)),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode x sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode x sC) - x - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SBC2'' = store_thm("arm_SBC2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SBC c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w)),
                  x = (if sC then 0w else 1w) + SND (ADDR_MODE1_VAL a_mode x sC),
                  (if sC then SND (ADDR_MODE1_VAL a_mode x sC) <=+ x  
                         else 2**32 <= (w2n x + w2n ~(SND (ADDR_MODE1_VAL a_mode x sC)))),
                  ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x =
                    word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC) - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SBC_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SBC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SUB2'' = store_thm("arm_SUB2''",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SUB c_flag s_flag b a (ADDR_MODE1_CMD a_mode a))] {}
           (R a x * R b (x - SND (ADDR_MODE1_VAL a_mode x sC)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC)),
                  x = SND (ADDR_MODE1_VAL a_mode x sC),
                  SND (ADDR_MODE1_VAL a_mode x sC) <=+ x,
                   ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode x sC))) /\
                  ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode x sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SUB_NOP
      `a*b*st*cd*cmd*pc*ud` `a*b*pc*cmd*st*ud*cd`
      `a*b*st*cmd*pc*ud` `a*b*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR3 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`b`,`Rn`|->`a`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SUB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADC3 = store_thm("arm_ADC3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADC c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            R c (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)) *
            S
              (if s_flag then
                 (word_msb
                    (x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) + (if sC then 1w else 0w) =
                  0w,
                  2**32 <=
                    (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC)) +
                     (if sC then 1 else 0)),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb
                      (x + SND (ADDR_MODE1_VAL a_mode y sC) +
                       (if sC then 1w else 0w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADC_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ADD3 = store_thm("arm_ADD3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ADD c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x + SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              (if s_flag then
                 (word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC)),
                  x + SND (ADDR_MODE1_VAL a_mode y sC) = 0w,
                  2**32 <= (w2n x + w2n (SND (ADDR_MODE1_VAL a_mode y sC))),
                  (word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x + SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_ADD_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ADD)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_AND3 = store_thm("arm_AND3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (AND c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x && SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x && SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_AND_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_AND)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_BIC3 = store_thm("arm_BIC3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (BIC c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x && ~SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x && ~SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x && ~SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_BIC_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_BIC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_EOR3 = store_thm("arm_EOR3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (EOR c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x ?? SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x ?? SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x = SND (ADDR_MODE1_VAL a_mode y sC) else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_EOR_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_EOR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_ORR3 = store_thm("arm_ORR3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (ORR c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x !! SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              ((if s_flag then
                  word_msb (x !! SND (ADDR_MODE1_VAL a_mode y sC))
                else
                  sN),
               (if s_flag then x !! SND (ADDR_MODE1_VAL a_mode y sC) = 0w else sZ),
               (if s_flag then FST (ADDR_MODE1_VAL a_mode y sC) else sC),sV)) {}``,
  ARM_PROG2_INIT_TAC ARM_ORR_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_ORR)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSB3 = store_thm("arm_RSB3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSB c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (SND (ADDR_MODE1_VAL a_mode y sC) - x) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x),
                  SND (ADDR_MODE1_VAL a_mode y sC) = x,
                  x <=+ SND (ADDR_MODE1_VAL a_mode y sC),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x)))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSB_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);

val arm_RSC3 = store_thm("arm_RSC3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (RSC c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y *
            R c (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w)),
                  SND (ADDR_MODE1_VAL a_mode y sC) = (if sC then 0w else 1w) + x,
                  (if sC then x <=+ SND (ADDR_MODE1_VAL a_mode y sC) 
                         else 2**32 <= (w2n (SND (ADDR_MODE1_VAL a_mode y sC)) + w2n ~x)),
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) = word_msb x) /\
                  ~(word_msb (SND (ADDR_MODE1_VAL a_mode y sC)) =
                    word_msb (SND (ADDR_MODE1_VAL a_mode y sC) - x - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_RSC_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_RSC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SBC3 = store_thm("arm_SBC3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SBC c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w)),
                  x = (if sC then 0w else 1w) + SND (ADDR_MODE1_VAL a_mode y sC),
                  (if sC then SND (ADDR_MODE1_VAL a_mode y sC) <=+ x  
                         else 2**32 <= (w2n x + w2n ~(SND (ADDR_MODE1_VAL a_mode y sC)))),
                  ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x =
                    word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC) - (if sC then 0w else 1w))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SBC_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SBC)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC
  \\ ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO] \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB]);

val arm_SUB3 = store_thm("arm_SUB3",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * R b y * R c z * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV))
           [enc (SUB c_flag s_flag c a (ADDR_MODE1_CMD a_mode b))] {}
           (R a x * R b y * R c (x - SND (ADDR_MODE1_VAL a_mode y sC)) *
            S
              (if s_flag then
                 (word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC)),
                  x = SND (ADDR_MODE1_VAL a_mode y sC),
                  SND (ADDR_MODE1_VAL a_mode y sC) <=+ x,
                   ~(word_msb x = word_msb (SND (ADDR_MODE1_VAL a_mode y sC))) /\
                  ~(word_msb x = word_msb (x - SND (ADDR_MODE1_VAL a_mode y sC))))
               else
                 (sN,sZ,sC,sV))) {}``,
  ARM_PROG2_INIT_TAC ARM_SUB_NOP
      `a*b*c*st*cd*cmd*pc*ud` `a*b*c*pc*cmd*st*ud*cd`
      `a*b*c*st*cmd*pc*ud` `a*b*c*pc*cmd*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR4 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`c`,`Rn`|->`b`] (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_SUB)))
  \\ Cases_on `s_flag` \\ ARM_PROG2_HAMMER_TAC);


(* ----------------------------------------------------------------------------- *)
(* BRANCH INSTRUCTIONS                                                           *)
(* ----------------------------------------------------------------------------- *)

(* lemmas *)

val sw2sw_EQ_w2w_sw2sw = prove(
  ``sw2sw (w:word24) << 2 = (w2w ((sw2sw w):word30) << 2) :word32``,
  REWRITE_TAC [sw2sw_def,w2w_def,bitTheory.SIGN_EXTEND_def]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [LET_DEF]
  \\ Cases_on `BIT 23 (w2n w)`
  \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2n_n2w,word_lsl_n2w,n2w_11]
  \\ `0 < 1073741824` by EVAL_TAC
  \\ `!x. (x MOD 1073741824) * 4 = (4 * x) MOD (4 * 1073741824)` 
         by METIS_TAC [MULT_SYM,MOD_COMMON_FACTOR,EVAL ``0<4``]
  \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC std_ss [MOD_MOD]
  \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [MULT_SYM]))
  \\ REWRITE_TAC []
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB]
  \\ ONCE_REWRITE_TAC 
        [(RW [EVAL ``0 < 4294967296``] o GSYM o Q.SPEC `4294967296`) MOD_PLUS]
  \\ SIMP_TAC std_ss []);

val word_add_w2n = prove(
  ``!w v:'a word. w2n (w + v) = (w2n w + w2n v) MOD dimword (:'a)``,
  REWRITE_TAC [word_add_def,w2n_n2w]);

val w2w_add_lsl = prove(
  ``w2w w << 2 + w2w v << 2 = (w2w (w+v:word30) << 2) :word32``,
  SRW_TAC [] [w2w_def,word_lsl_n2w,WORD_ADD_0,word_add_n2w]
  \\ SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
  \\ REWRITE_TAC [GSYM (EVAL ``1073741824 * 4``),GSYM RIGHT_ADD_DISTRIB]
  \\ ONCE_REWRITE_TAC [MULT_SYM]  
  \\ `!x. (4 * x) MOD (4 * 1073741824) = 4 * (x MOD 1073741824)` 
         by METIS_TAC [MOD_COMMON_FACTOR,EVAL ``0<4``,EVAL ``0 < 1073741824``]
  \\ `!x y. (4 * x = 4 * y) = (x = y)` by METIS_TAC [EQ_MULT_LCANCEL,EVAL ``0=4``]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [wordsLib.SIZES_ss] [word_add_w2n]);

val PC_SIMP_LEMMA = prove(
  ``w2w (p:word30) << 2 + 8w + sw2sw (offset:word24) << 2 = 
    (w2w (p + 2w + sw2sw offset) << 2):word32``,
  REWRITE_TAC [GSYM (EVAL ``((w2w (2w:word30)):word32) << 2``)]
  \\ REWRITE_TAC [sw2sw_EQ_w2w_sw2sw]
  \\ REWRITE_TAC [w2w_add_lsl]);

val PC_SIMP = prove(
  ``addr32 p + 8w + sw2sw (offset:word24) << 2 = 
    addr32 (pcADD (sw2sw offset + 2w) p)``,
  SIMP_TAC bool_ss [pcADD_def,PC_SIMP_LEMMA,addr32_def]
  \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

(* unconditional and conditional relative branch *)

val arm_bal_expand = sep_pred_semantics (xR1,xMm,`(F,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`)

val CONDITION_PASSED2_AL = prove(
  ``!x. CONDITION_PASSED2 x AL``,
  STRIP_TAC 
  \\ `?x1 x2 x3 x4. x = (x1,x2,x3,x4)` by METIS_TAC [pairTheory.PAIR]
  \\ ASM_REWRITE_TAC []
  \\ SRW_TAC [] [CONDITION_PASSED2_def]);

val arm_B_AL = store_thm("arm_B_AL",
  ``(ARM_PROG:^(ty_antiq ARM_PROG_type)) 
      emp [enc (B AL offset)] {} SEP_F {(emp,pcADD (sw2sw offset + 2w))}``,
  ARM_PROG_INIT_TAC 
  \\ FULL_SIMP_TAC (std_ss++sep_ss) [] \\ REWRITE_TAC [SEP_F_def]
  \\ FULL_MOVE_STAR_TAC `a*b*c` `b*a*c`
  \\ FULL_SIMP_TAC bool_ss [arm_bal_expand] 
  \\ IMP_RES_TAC mem_EQ_mem_pc
  \\ FULL_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      ((UNDISCH_ALL o RW [CONDITION_PASSED2_AL] o Q.INST [`c`|->`AL`]) (simple_clean ARM_B []))
  \\ ARM_PROG2_HAMMER_TAC \\ REWRITE_TAC [GSYM PC_SIMP] \\ SRW_TAC [] []);

val arm_b_nop = let
  val th = SPEC_ALL ARM_B_NOP
  val th = Q.INST [`s:bool`|->`s_flag`] th
  val th = Q.INST [`state`|->`s`] th 
  val th = ASM_UNABBREV_ALL_RULE (UD_ALL th)
  val th = (UNDISCH_ALL o Q.INST [`c`|->`c_flag`] o 
            SIMP_RULE (bool_ss++contract_ss) [] o DISCH_ALL) th
  in SET_NO_CP th end;

val arm_B = store_thm("arm_B",
  ``(ARM_PROG:^(ty_antiq ARM_PROG_type)) 
           (S (sN,sZ,sC,sV)) [enc (B c_flag offset)] {}
           (S (sN,sZ,sC,sV) * nPASS c_flag (sN,sZ,sC,sV))
           {(S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV),pcADD (sw2sw offset + 2w))}``,
  ARM_PROG_INIT_TAC 
  \\ REWRITE_TAC [nPASS_def,GSYM STAR_OVER_DISJ]
  \\ MOVE_STAR_TAC `st*cd*m*pc*ud` `pc*m*st*ud*cd`
  \\ ASM_MOVE_STAR_TAC `st*m*pc*ud` `pc*m*st*ud`
  \\ ARM_PROG2_EXPAND_TAC xR1 xMm
  \\ Cases_on `CONDITION_PASSED2 (status s) c_flag` 
  \\ ONCE_ASM_REWRITE_TAC [] \\ REWRITE_TAC [] << [  
    ASSUME_TAC ((UNDISCH_ALL o Q.INST [`c`|->`c_flag`]) (simple_clean ARM_B []))
    \\ ARM_PROG2_HAMMER_TAC \\ REWRITE_TAC [GSYM PC_SIMP] \\ SRW_TAC [] [],
    ASSUME_TAC arm_b_nop \\ ARM_PROG2_HAMMER_TAC]);  

val arm_B2 = store_thm("arm_B2",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag 
           (S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV)) 
           [enc (B c_flag offset)] {} SEP_F        
           {(S (sN,sZ,sC,sV),pcADD (sw2sw offset + 2w))}``,
  ARM_PROG2_INIT_TAC ARM_B_NOP
      `st*cd*cmd*pc*ud` `pc*cmd*st*ud*cd`
      `st*cmd*pc*ud` `pc*cmd*st*ud`
  \\ REWRITE_TAC [SEP_F_def]
  \\ ARM_PROG2_EXPAND_TAC' xR1 xMm xR1 xMm
  \\ ASSUME_TAC ((UNDISCH_ALL o Q.INST [`c`|->`c_flag`]) (simple_clean ARM_B []))
  \\ ARM_PROG2_HAMMER_TAC \\ REWRITE_TAC [GSYM PC_SIMP] \\ SRW_TAC [] []);

(* procedure returns *)

val arm_MOV_PC_GENERAL = store_thm("arm_MOV_PC_GENERAL",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * 
            cond (SND (ADDR_MODE1_VAL a_mode x sC) && 3w = 0w))
           [enc (MOV c_flag F 15w (ADDR_MODE1_CMD a_mode a))] {} SEP_F
           {(~R a * S (sN,sZ,sC,sV),pcSET (addr30 (SND (ADDR_MODE1_VAL a_mode x sC))))}``,
  REWRITE_TAC [R30_def]
  \\ ARM_PROG2_INIT_TAC ARM_MOV_NOP
      `a*st*cd*cd'*cmd*pc*ud` `a*pc*cmd*st*ud*cd'*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ REWRITE_TAC [SEP_F_def]
  \\ ARM_PROG2_EXPAND_TAC' xR2 xMm xR2' xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`,`s_flag`|->`F`] 
          (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MOV_PC)))
  \\ ARM_PROG2_HAMMER_TAC 
  \\ ASM_SIMP_TAC std_ss [pcSET_def,SIMP_RULE (srw_ss()) [] addr32_addr30]);

val arm_MOV_PC = save_thm("arm_MOV_PC",let
  val th = Q.INST [`a_mode`|->`OneReg`,`x`|->`addr32 x`] arm_MOV_PC_GENERAL
  val th = RW [ADDR_MODE1_VAL_def,ADDR_MODE1_CMD_def,GSYM R30_def,
               addr30_addr32,emp_STAR,addr32_and_3w,SEP_cond_CLAUSES] th
  in th end);

val arm_MOV_PC_PRECISE = store_thm("arm_MOV_PC_PRECISE",
  ``(ARM_PROG2:^(ty_antiq ARM_PROG2_type)) c_flag
           (R a x * S (sN,sZ,sC,sV) * PASS c_flag (sN,sZ,sC,sV) * 
            cond (SND (ADDR_MODE1_VAL a_mode x sC) && 3w = 0w))
           [enc (MOV c_flag F 15w (ADDR_MODE1_CMD a_mode a))] {} SEP_F
           {(R a x * S (sN,sZ,sC,sV),pcSET (addr30 (SND (ADDR_MODE1_VAL a_mode x sC))))}``,
  REWRITE_TAC [R30_def]
  \\ ARM_PROG2_INIT_TAC ARM_MOV_NOP
      `a*st*cd*cd'*cmd*pc*ud` `a*pc*cmd*st*ud*cd'*cd`
      `a*st*cmd*pc*ud` `a*pc*cmd*st*ud`
  \\ REWRITE_TAC [SEP_F_def]
  \\ ARM_PROG2_EXPAND_TAC' xR2 xMm xR2 xMm
  \\ ASSUME_TAC 
       (simple_clean_AM1 [`Rd`|->`a`,`Rn`|->`a`,`s_flag`|->`F`] 
          (Q.INST [`Rm`|->`a`] (SPEC_ALL ARM_MOV_PC)))
  \\ ARM_PROG2_HAMMER_TAC
  \\ ASM_SIMP_TAC std_ss [pcSET_def,SIMP_RULE (srw_ss()) [] addr32_addr30]);

(* procedure calls *)

val arm_blal_pre = sep_pred_semantics (xR2',xMm,`(F,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`);
val arm_blal_post = sep_pred_semantics (xR2,xMm,`(F,st)`,`(T,ud)`,`(F,rt)`,`(F,g)`);

val WORD_LSL_EQ_MULT = prove(
  ``!x. x << n = x * n2w (2 ** n)``,
  Cases \\ REWRITE_TAC [word_lsl_n2w,word_mul_n2w]
  \\ Cases_on `dimindex (:'a) - 1 < n`
  \\ ASM_REWRITE_TAC [n2w_11]
  \\ `dimindex (:'a) <= n` by DECIDE_TAC
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ REWRITE_TAC [dimword_def,EXP_ADD,MULT_ASSOC]
  \\ SIMP_TAC std_ss [MOD_EQ_0]);

val arm_bl_post = sep_pred_semantics (xR2,xMm,`(T,st)`,`(T,ud)`,`(F,rt)`,`(T,g)`);

val ARM_SPEC_BL = prove(
  ``ARM_SPEC2 c (R 14w x * PASS c (sN,sZ,sC,sV) * S (sN,sZ,sC,sV),p) 
                {([enc (BL c offset)],p)} 
                (R 14w (p + 4w) * S (sN,sZ,sC,sV),p + 8w + sw2sw offset * 4w)``,
  REWRITE_TAC [ARM_SPEC2_def] \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REPEAT STRIP_TAC
  THEN1 (Q.SPEC_TAC (`p`,`p`) \\ MATCH_MP_TAC SPEC_ARM_MODEL_INTRO
         \\ REWRITE_TAC [MAKE_ARM_NOP ARM_BL_NOP])
  \\ SIMP_TAC (std_ss++sep2_ss) [SPEC_ARM_MODEL_EQ_ARM_RUN,WORD_LSL_EQ_MULT,PASS_def]
  \\ MOVE_STAR_TAC `a14*s*a15*m*u*c` `a14*a15*m*s*u*c`  
  \\ REWRITE_TAC [ARM_RUN_SEMANTICS,arm_bl_post] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `1` \\ ASM_SIMP_TAC std_ss [LET_DEF,STATE_ARM_MEM_1]
  \\ `mem (addr30 (reg 15w s)) s = enc (BL c offset)` by METIS_TAC []
  \\ `CONDITION_PASSED2 (status s) c` by METIS_TAC []
  \\ ASSUME_TAC (UNDISCH_ALL (simple_clean ARM_BL []))
  \\ ARM_PROG2_HAMMER_TAC
  \\ SIMP_TAC std_ss [WORD_MUL_LSL]
  \\ REWRITE_TAC [GSYM (SIMP_RULE (srw_ss()) [] aligned_def)]
  \\ MATCH_MP_TAC aligned_ADD
  \\ REWRITE_TAC [GSYM (EVAL ``addr32 2w``),aligned_addr32]
  \\ MATCH_MP_TAC aligned_MULT
  \\ FULL_SIMP_TAC (srw_ss()) [aligned_def]);

val arm_BL = store_thm("arm_BL",
  ``!(P:^(ty_antiq ARMel_type) set -> bool) Q C k.
      ARM_PROC P Q C ==>
      ARM_PROG (P * ~R 14w) [enc (BL AL offset)] 
               (setADD (sw2sw offset + 2w) C) (Q * ~R 14w) {}``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ARM_PROC_CALL \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [CALL_def,ARMproc_def] \\ REPEAT STRIP_TAC \\ POP_ASSUM (fn th => ALL_TAC)
  \\ REWRITE_TAC [GSYM ARMproc_def,GSYM ARM_RUN_def,ARMpc_def,STAR_ASSOC,ARM_RUN_SEMANTICS]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `1` 
  \\ FULL_SIMP_TAC (std_ss++sep_ss) [LET_DEF,STATE_ARM_MEM_1,ARMpc_def,R30_def,pcINC_def, 
       SIMP_RULE std_ss [LENGTH] (Q.SPEC `[cmd]` mpool_eq_ms),ms_def,STAR_ASSOC,
       wLENGTH_def,LENGTH,GSYM PC_SIMP]
  \\ FULL_MOVE_STAR_TAC `a*pc*ud*m` `a*pc*m*ud`  
  \\ FULL_SIMP_TAC bool_ss [arm_blal_pre,arm_blal_post]
  \\ IMP_RES_TAC mem_EQ_mem_pc
  \\ FULL_SIMP_TAC bool_ss []
  \\ ASSUME_TAC 
      ((UNDISCH_ALL o RW [CONDITION_PASSED2_AL] o Q.INST [`c`|->`AL`]) (simple_clean ARM_BL []))
  \\ ARM_PROG2_HAMMER_TAC);




val _ = export_theory();

