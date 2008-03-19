(*
  quietdec := true;
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory pairTheory;
open listTheory rich_listTheory relationTheory pairTheory fcpTheory;
open sortingTheory addressTheory;

open set_sepTheory set_sepLib progTheory arm_progTheory arm_instTheory arm_progLib;

(*
  quietdec := false;
*)


val _ = new_theory "arm_gc";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = Parse.hide "set";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* ARM_PROG_ARRAY_LOOP - a loop rule traversing the elements of an array         *)
(* ----------------------------------------------------------------------------- *)

val STAR_LIST_def = Define `
  (STAR_LIST [] = emp) /\ 
  (STAR_LIST (P::Ps) = P * STAR_LIST Ps)`;

val ARM_PROG_LOOP_DEC = prove(
  ``!P cs C Z. 
      (!v:'var word. ARM_PROG (P v * cond ~(v = 0w)) cs C Q 
                     ((P (v - 1w) * cond ~(v - 1w = 0w),I) INSERT Z)) ==>
      (!v. ARM_PROG (P v * cond ~(v = 0w)) cs C Q Z)``,
  ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\x. P x * cond ~(x:'a word = 0w)) v``]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ARM_PROG_LOOP_MEASURE
  \\ Q.EXISTS_TAC `w2n` \\ REWRITE_TAC [GSYM WORD_LO]
  \\ FULL_SIMP_TAC std_ss [ARM_PROG_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!v. b` (ASSUME_TAC o UNDISCH o RW [ARM_PROG_MOVE_COND] o Q.SPEC `v0`)
  \\ ((MATCH_MP_TAC o GEN_ALL o RW [AND_IMP_INTRO] o 
       DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL) ARM_PROG_WEAKEN_POST)
  \\ Q.EXISTS_TAC `(P (v0 - 1w) * cond ~(v0 - 1w = 0w))`
  \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_def,SEP_EXISTS_THM,GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `v0 - 1w`
  \\ FULL_SIMP_TAC std_ss [cond_STAR]
  \\ METIS_TAC [WORD_LO,WORD_PRED_THM]);

val ARM_ADDRESS_DOWN_LOOP = let
  val th1 = (*  subs a,a,#4  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`a_mode`|->`Imm 4w`] arm_SUB1))
  val th2 = (*  bne 45       *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`NE`] arm_B)
  val th = AUTO_HIDE_STATUS (FRAME_COMPOSE th1 (MATCH_INST1 [`S`] th1 th2))
  val th = RW [GSYM (EVAL ``addr32 1w``),addr32_11] (ALIGN_VARS ["x"] th)
  val th = APP_FRAME `Inv (x - 1w:word30)` th
  val th1 = (SPEC_ALL o ASSUME)
   ``!x. ARM_PROG (Inv x * R30 a x * ~S * cond ~(x = 0w)) code C 
                  (Inv (x - 1w) * R30 a x * ~S) {}``
  val th = FRAME_COMPOSE th1 th
  val th = DISCH ``sw2sw(offset:word24)+2w+1w+n2w (LENGTH (code:word32 list))=0w:word30`` th
  val th = UNDISCH (SIMP_RULE bool_ss [pcADD_0] th)
  val th = SPEC_WEAKEN1 th `Inv (0w:word30) * R30 a 0w * ~S`
  val th = SEP_IMP_RULE (SIMP_CONV (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,WORD_SUB_REFL]) th
  val th = SPEC_WEAKEN th `Inv (x - 1w) * R30 a (x - 1w) * ~S * cond ~(x = 1w)`
  val th = SEP_IMP_RULE (SIMP_CONV (bool_ss++sep2_ss) []) th  
  val th1 = (BETA_RULE o Q.ISPEC `\x. Inv x * R30 a x * ~S `) ARM_PROG_LOOP_DEC
  val th = MATCH_MP (RW [WORD_EQ_SUB_ZERO] th1) (Q.GEN `x` th)
  val th = DISCH_ALL (PAT_DISCH ``x=y:'a`` th)
  in th end;

val STAR_LIST_APPEND = prove(
  ``!xs ys. STAR_LIST (xs ++ ys) = STAR_LIST xs * STAR_LIST ys``,
  Induct \\ ASM_REWRITE_TAC [APPEND,APPEND_NIL,STAR_LIST_def,emp_STAR,STAR_ASSOC]);

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

val ALL_DISTINCT_APPEND = prove(
  ``ALL_DISTINCT (xs ++ ys) = 
    (!x. MEM x xs ==> ~MEM x ys) /\ ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
  Induct_on `xs` \\ ASM_SIMP_TAC bool_ss [APPEND_NIL,APPEND,MEM,ALL_DISTINCT,MEM_APPEND]
  \\ METIS_TAC []);

val ALL_DISTINCT_COMM = prove(
  ``!xs ys. ALL_DISTINCT (xs++ys) = ALL_DISTINCT (ys++xs)``,
  REWRITE_TAC [ALL_DISTINCT_APPEND] \\ METIS_TAC []);

val addresses_def = Define `
  (addresses a w 0 = []) /\ 
  (addresses a w (SUC n) = a :: addresses (a + w) w n)`;
  
val MEM_addresses = prove(
  ``!n x w y. MEM x (addresses y w n) = ?i. i < n /\ (x = y + w * n2w i)``,  
  Induct THEN1 REWRITE_TAC [MEM,addresses_def,DECIDE ``~(n<0)``] 
  \\ ASM_REWRITE_TAC [addresses_def,MEM] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `0` \\ ASM_REWRITE_TAC [WORD_ADD_0,WORD_MULT_CLAUSES] \\ DECIDE_TAC,
    Q.EXISTS_TAC `SUC i` \\ ASM_REWRITE_TAC [ADD1,LT_ADD_RCANCEL]
    \\ REWRITE_TAC [GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_MULT_CLAUSES],
    Cases_on `i` \\ ASM_REWRITE_TAC [WORD_ADD_0,ADD1,WORD_MULT_CLAUSES]
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `n'` 
    \\ REWRITE_TAC [GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_MULT_CLAUSES] \\ DECIDE_TAC]);

val EQ_FILTER_MOVE_CONS = prove(
  ``!xs ys x y. FILTER ($= x) (xs ++ y::ys) = FILTER ($= x) (y::xs ++ ys)``,
  Induct \\ SIMP_TAC bool_ss [APPEND_NIL,FILTER,APPEND]
  \\ ONCE_ASM_REWRITE_TAC [] \\ SIMP_TAC bool_ss [APPEND_NIL,FILTER,APPEND]
  \\ METIS_TAC []);

val APPEND_APPEND_IMP_PERM_LEMMA = prove(
  ``(!xs ys zs. P (xs++ys++zs) = P (xs++zs++ys)) ==>
    !xs ys zs. PERM xs ys ==> (P (zs ++ xs) = P (zs ++ ys))``,
  REWRITE_TAC [PERM_DEF] \\ STRIP_TAC \\ Induct \\ REWRITE_TAC [] << [
    Cases_on `ys` \\ REWRITE_TAC [FILTER] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x. [] = d` (ASSUME_TAC o Q.SPEC `h`)
    \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS],
    REPEAT STRIP_TAC \\ `MEM h ys` by ALL_TAC << [
      CCONTR_TAC \\ Q.PAT_ASSUM `!x. FILTER g xs = h` (ASSUME_TAC o Q.SPEC `h`)
      \\ FULL_SIMP_TAC std_ss [FILTER] \\ Cases_on `FILTER ($= h) ys`
      \\ FULL_SIMP_TAC bool_ss [NOT_NIL_CONS]
      \\ `MEM h' (FILTER ($= h) ys)` by METIS_TAC [MEM]
      \\ FULL_SIMP_TAC std_ss [MEM_FILTER],
      NTAC 2 (FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND])
      \\ REWRITE_TAC [APPEND_ASSOC] \\ ONCE_ASM_REWRITE_TAC []
      \\ ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND] ``[x]++xs``)]
      \\ REWRITE_TAC [APPEND_ASSOC]      
      \\ Q.PAT_ASSUM `!xs ys zs. b` (fn th => 
          CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
      \\ ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND_ASSOC] ``(xs++ys)++(zs++qs)``)]
      \\ Q.PAT_ASSUM `!ys zs. b` MATCH_MP_TAC
      \\ FULL_SIMP_TAC bool_ss [EQ_FILTER_MOVE_CONS,APPEND]
      \\ FULL_SIMP_TAC bool_ss [FILTER]
      \\ STRIP_TAC \\ Cases_on `x = h`
      \\ Q.PAT_ASSUM `!x. b` (ASSUME_TAC o Q.SPEC `x`)
      \\ METIS_TAC [CONS_11]]]);
 
val APPEND_APPEND_IMP_PERM = prove(
  ``(!xs ys zs. P (xs++ys++zs) = P (xs++zs++ys)) ==>
    !xs ys. PERM xs ys ==> (P xs = P ys)``,
  STRIP_TAC \\ IMP_RES_TAC APPEND_APPEND_IMP_PERM_LEMMA
  \\ METIS_TAC [APPEND_NIL]);

val PERM_IMP_ALL_DISTINCT = prove(
  ``!xs ys. PERM xs ys ==> (ALL_DISTINCT xs = ALL_DISTINCT ys)``,
  MATCH_MP_TAC APPEND_APPEND_IMP_PERM \\ REWRITE_TAC [GSYM APPEND_ASSOC]
  \\ ONCE_REWRITE_TAC [ALL_DISTINCT_APPEND] \\ METIS_TAC [ALL_DISTINCT_COMM,MEM_APPEND]);

val addresses_ADD = prove(
  ``!m n x. addresses x w (m + n) = addresses x w m ++ addresses (x + w * n2w m) w n``,
  Induct \\ REWRITE_TAC [ADD,addresses_def,WORD_ADD_0,APPEND,WORD_MULT_CLAUSES]
  \\ ASM_REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC,WORD_MULT_CLAUSES]);  

val PF_def = Define `PF a w i xs = FILTER (\x. MEM (FST x) (addresses (a+w) w (w2n i))) xs`;
val NF_def = Define `NF a w i xs = FILTER (\x. ~MEM (FST x) (addresses (a+w) w (w2n i))) xs`;

val PF_INV_def = Define `
  PF_INV P Q a w xs n i = 
    Q (NF a w i xs) (a + w * i) * STAR_LIST (MAP P (PF a w i xs)) *
    cond (PERM (MAP FST xs) (addresses (a + w) w (w2n n))) * cond (i <=+ n) *
    cond (ALL_DISTINCT (MAP FST xs))`;

val PF_0 = prove(
  ``!xs a w. (PF a w 0w xs = []) /\ (NF a w 0w xs = xs)``,
  SIMP_TAC bool_ss [PF_def,NF_def,w2n_n2w,ZERO_LT_dimword,LESS_MOD,addresses_def]
  \\ REWRITE_TAC [MEM] \\ Induct \\ ASM_SIMP_TAC std_ss [FILTER]);

val PF_FULL = prove(
  ``!a w xs n. 
      PERM (MAP FST xs) (addresses (a + w) w (w2n n)) ==> 
      (PF a w n xs = xs) /\ (NF a w n xs = [])``,
  REWRITE_TAC [PF_def,NF_def] \\ NTAC 4 STRIP_TAC
  \\ Q.SPEC_TAC (`addresses (a + w) w (w2n n)`,`ys`) \\ NTAC 2 STRIP_TAC
  \\ `!x. MEM x (MAP FST xs) ==> MEM x ys` by METIS_TAC [PERM_MEM_EQ]  
  \\ Q.PAT_ASSUM `PERM (MAP FST xs) ys` (fn th => ALL_TAC)
  \\ Induct_on `xs` \\ ASM_SIMP_TAC bool_ss [FILTER,MEM,MAP]);

val PF_FIX_TAIL = prove(
  ``!i a w ys.
      ~(i = 0w) /\ ~MEM (a + w * i) (MAP FST ys) ==>
      (PF a w (i - 1w) ys = PF a w i ys) /\
      (NF a w (i - 1w) ys = NF a w i ys)``,
  REWRITE_TAC [PF_def,NF_def]
  \\ Cases \\ Cases_on `n` \\ ASM_SIMP_TAC bool_ss [LESS_MOD,n2w_11,ZERO_LT_dimword]
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_SUB] 
  \\ REWRITE_TAC [word_add_n2w,GSYM ADD1] \\ `n' < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w]
  \\ REWRITE_TAC [ADD1,addresses_ADD,MEM_APPEND,GSYM word_add_n2w]
  \\ REWRITE_TAC [WORD_MULT_CLAUSES,WORD_ADD_ASSOC]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC 0``),addresses_def,MEM,DECIDE ``~(n' + SUC 0 = 0)``]
  \\ Induct_on `ys` \\ SIMP_TAC bool_ss [FILTER] \\ ASM_SIMP_TAC bool_ss [MAP,FST,MEM]);
  
val PF_UNROLL = prove(
  ``!i a w x ys.
      ~(i = 0w) /\ ~MEM (a + w * i) (MAP FST ys) ==>
      (PF a w i ((a + w * i,x)::ys) = (a + w * i,x) :: PF a w (i - 1w) ys) /\
      (NF a w i ((a + w * i,x)::ys) = NF a w i ys)``,
  SIMP_TAC bool_ss [PF_def,FILTER,NF_def] \\ REWRITE_TAC [GSYM PF_def,GSYM NF_def]
  \\ SIMP_TAC bool_ss [PF_FIX_TAIL]
  \\ Cases \\ Cases_on `n` \\ ASM_SIMP_TAC bool_ss [LESS_MOD,n2w_11,ZERO_LT_dimword]
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ REWRITE_TAC [word_add_n2w,GSYM ADD1]
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w] \\ NTAC 5 STRIP_TAC
  \\ `MEM (a + w * n2w (SUC n')) (addresses (a+w) w (SUC n'))` by ALL_TAC
  \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [MEM_addresses] \\ Q.EXISTS_TAC `n'` 
  \\ REWRITE_TAC [WORD_MULT_CLAUSES,WORD_ADD_ASSOC,ADD1,GSYM word_add_n2w] \\ DECIDE_TAC);

val PF_CONTRACT_LEMMA = prove(
  ``!i a w. ~(i = 0w) /\ ALL_DISTINCT (addresses (a+w) w (w2n i)) ==>
            ~MEM (a + w * i) (addresses (a+w) w (w2n (i - 1w)))``,
  Cases \\ Cases_on `n` \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ REWRITE_TAC [word_add_n2w,GSYM ADD1] \\ `n' < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w] \\ REWRITE_TAC [ADD1]
  \\ REWRITE_TAC [WORD_MULT_CLAUSES,WORD_ADD_ASSOC,ADD1,GSYM word_add_n2w]
  \\ REWRITE_TAC [addresses_ADD] \\ ONCE_REWRITE_TAC [ALL_DISTINCT_COMM]  
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``SUC 0``),addresses_def,APPEND,ALL_DISTINCT]);

val PF_CONTRACT = prove(
  ``!i a w x ys.
      ~(i = 0w) /\ ~MEM (a + w * i) (MAP FST ys) /\ 
      ALL_DISTINCT (addresses (a+w) w (w2n i)) ==>
      (PF a w (i - 1w) ((a + w * i,x)::ys) = PF a w (i - 1w) ys) /\
      (NF a w (i - 1w) ((a + w * i,x)::ys) = (a + w * i,x)::NF a w i ys)``,
  SIMP_TAC bool_ss [PF_def,FILTER,NF_def] \\ REWRITE_TAC [GSYM PF_def,GSYM NF_def]
  \\ SIMP_TAC bool_ss [PF_FIX_TAIL,PF_CONTRACT_LEMMA]);

val REMOVE_ORDER = prove(
  ``(!x ys. ~MEM (i:'i word) (MAP FST ys) ==> P ((i,x)::ys)) ==>
    (!xs ys zs. P (xs++ys) = P (ys++xs)) ==>
    !ys. MEM i (MAP FST ys) /\ ALL_DISTINCT (MAP FST ys) ==> P ys``,
  STRIP_TAC \\ SIMP_TAC bool_ss [MEM_MAP] \\ REPEAT STRIP_TAC
  \\ `?xs zs. ys = xs ++ y::zs` by ASM_REWRITE_TAC [GSYM MEM_EQ_APPEND]
  \\ ONCE_ASM_REWRITE_TAC [] \\ ONCE_ASM_REWRITE_TAC []
  \\ Cases_on `y` \\ Q.PAT_ASSUM `i = FST (q,r)` (ASSUME_TAC o RW [FST] o GSYM)
  \\ Q.PAT_ASSUM `!xs ys. P (xs ++ ys) = P (ys ++ xs)` (fn th => ALL_TAC)
  \\ ASM_REWRITE_TAC [APPEND] \\ Q.PAT_ASSUM `!x.b` MATCH_MP_TAC
  \\ FULL_SIMP_TAC bool_ss [MAP_APPEND,MAP,FST,MEM_APPEND,MEM]
  \\ `ALL_DISTINCT (i::MAP FST zs ++ MAP FST xs)` by METIS_TAC [ALL_DISTINCT_COMM]
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,APPEND,MEM_APPEND]);

val LE_IMP_ALL_DISTINCT_addresses = prove(
  ``!n a w m. 
      m <= n /\ ALL_DISTINCT (addresses a w n) ==> ALL_DISTINCT (addresses a w m)``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] \\ NTAC 5 STRIP_TAC
  \\ IMP_RES_TAC LESS_EQUAL_ADD \\ ASM_SIMP_TAC bool_ss [addresses_ADD,ALL_DISTINCT_APPEND]);
  
val PF_BODY_LEMMA = prove(
  ``!i:'i word a n w xs:('i word # 'd) list.
      PERM (MAP FST xs) (addresses (a + w) w (w2n n)) /\ (i <=+ n) /\
      ALL_DISTINCT (MAP FST xs) /\ ~(i = 0w) ==>
      MEM (a + w * i) (MAP FST xs) /\ ALL_DISTINCT (MAP FST xs) /\
      ALL_DISTINCT (addresses (a + w) w (w2n i)) /\ ~(i = 0w)``,
  Cases \\ Cases_on `n` \\ SIMP_TAC bool_ss [WORD_LS] \\ REPEAT STRIP_TAC
  \\ `w2n (n2w (SUC n'):'i word) = SUC n'` by ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w] << [
    IMP_RES_TAC PERM_MEM_EQ \\ ASM_REWRITE_TAC []
    \\ FULL_SIMP_TAC bool_ss [WORD_LS,MEM_addresses]
    \\ Q.EXISTS_TAC `n'`
    \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_MULT_CLAUSES,WORD_ADD_ASSOC]
    \\ DECIDE_TAC,
    `ALL_DISTINCT (addresses (a + w) w (w2n n))` by METIS_TAC [PERM_IMP_ALL_DISTINCT]
    \\ MATCH_MP_TAC LE_IMP_ALL_DISTINCT_addresses
    \\ Q.EXISTS_TAC `w2n n` \\ ASM_REWRITE_TAC []]);   
    
val PF_BODY = let
  val th = (Q.SPECL [`a + w * i`,`x`,`xs`] o ASSUME) 
    ``!i x xs. ARM_PROG (P (i:'i word,x:'d) * Q xs i * ~S) code {} 
                        ((Q ((i,x)::xs) (i - w) * ~S):'a ARMset -> bool) {}``
  val th = APP_FRAME `STAR_LIST (MAP P (PF a w (i-1w:'i word) (ys:('i word # 'd) list))) * 
              cond (~(i = 0w) /\ ~MEM (a + w * i) (MAP FST (ys:('i word # 'd) list)) /\
                    ALL_DISTINCT (addresses (a+w) w (w2n i)))` th
  val th = Q.INST [`xs`|->`NF a w i ys`] th
  val th = SPEC_STRENGTHEN th 
    `Q (NF a w (i:'i word) ((a + w * i,x:'d)::ys)) (a + w * i) * ~S * 
     STAR_LIST (MAP P (PF a w (i:'i word) ((a + w * i,x:'d)::ys))) * 
     cond ~(i = 0w) * cond (ALL_DISTINCT (addresses (a+w) w (w2n i))) *
     cond (~MEM (a + w * i) (MAP FST (ys:('i word # 'd) list)))`
  val th = SEP_IMP_RULE (SIMP_CONV (bool_ss++sep2_ss) 
             [SEP_IMP_MOVE_COND,MAP,STAR_LIST_def,PF_UNROLL]) th
  val th = SPEC_WEAKEN1 th 
    `Q (NF a w (i - 1w) ((a + w * i:'i word,x:'d)::ys)) (a + w * (i - 1w)) * ~S *
     STAR_LIST (MAP P (PF a w (i - 1w) ((a + w * i:'i word,x:'d)::ys)))`
  val th = SEP_IMP_RULE (SIMP_CONV (bool_ss++sep2_ss) 
             [SEP_IMP_MOVE_COND,MAP,STAR_LIST_def,PF_CONTRACT,
              WORD_LEFT_SUB_DISTRIB,WORD_MULT_CLAUSES,GSYM WORD_ADD_SUB_ASSOC]) th
  val th = RW1 [ARM_PROG_MOVE_COND] th
  val th = Q.GEN `x` (Q.GEN `ys` (CONV_RULE (RAND_CONV (UNBETA_CONV ``(a + w * i:'i word,x:'d)::ys``)) th))
  val th = SIMP_RULE std_ss [] (MATCH_MP REMOVE_ORDER th)
  val th = SEP_IMP_RULE (REWRITE_CONV [NF_def,PF_def,FILTER_APPEND,MAP_APPEND,STAR_LIST_APPEND]) th  
  val th = SEP_IMP_RULE (REWRITE_CONV [GSYM NF_def,GSYM PF_def]) th  
  val goal = mk_imp(``!xs:(('i word # 'd) list) ys. Q (xs ++ ys) = Q (ys ++ xs) :'i word -> 'a ARMset -> bool``,(fst o dest_imp o concl) th)
  val lemma = prove(goal,METIS_TAC [])  
  val th = Q.SPEC `xs` (MATCH_MP th (UNDISCH lemma))
  val th = RW [AND_IMP_INTRO,ARM_PROG_MOVE_COND,GSYM CONJ_ASSOC] th
  val tn = (UNDISCH o SPEC_ALL) PF_BODY_LEMMA
  val th = MATCH_MP th tn
  val th = DISCH (hd (hyp tn)) th
  val th = MATCH_MP ARM_PROG_FRAME (RW [GSYM ARM_PROG_MOVE_COND] th)
  val th = INST [``bbb:bool``|->hd (hyp tn)] (Q.SPEC `cond bbb` th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [setSTAR_CLAUSES] th
  val th = APP_PART_WEAKEN1 th 
     `cond (PERM (MAP FST (xs :('i word # 'd) list)) (addresses (a + w) w (w2n n)) /\
        (i - 1w:'i word) <=+ n /\ ALL_DISTINCT (MAP FST (xs :('i word # 'd) list)))`
     (SIMP_TAC bool_ss [SEP_IMP_cond,WORD_PRED_THM,WORD_LS]
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_IMP_LESS_OR_EQ
      \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS \\ Q.EXISTS_TAC `w2n (i:'i word)`
      \\ ASM_SIMP_TAC bool_ss [WORD_PRED_THM])
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond c``),STAR_ASSOC] th
  val th = MOVE_POST1 `S` (MOVE_PRE `S` th)
  val th = RW [GSYM PF_INV_def] th
  in th end;

val PERM_addresses = prove(
  ``!n y w.
       PERM (addresses (y + w * n + $- w) ($- w) (w2n n)) (addresses y w (w2n n))``,
  Cases \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w] 
  \\ POP_ASSUM (fn th => ALL_TAC) \\ Induct_on `n'`
  THEN1 REWRITE_TAC [addresses_def,PERM_REFL] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RAND_CONV (REWRITE_CONV [ADD1,addresses_ADD]))
  \\ ONCE_REWRITE_TAC [PERM_SYM] \\ MATCH_MP_TAC APPEND_PERM_SYM
  \\ REWRITE_TAC [GSYM (EVAL ``SUC 0``),addresses_def,APPEND]
  \\ ONCE_REWRITE_TAC [PERM_SYM] \\ REWRITE_TAC 
       [ADD1,GSYM word_add_n2w,WORD_MULT_CLAUSES,GSYM WORD_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ASM_REWRITE_TAC [WORD_ADD_ASSOC,WORD_ADD_SUB2,GSYM word_sub_def,PERM_CONS_IFF]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ ASM_REWRITE_TAC [word_sub_def,WORD_ADD_ASSOC]);

val ARM_PROG_ARRAY_LOOP = save_thm("ARM_PROG_ARRAY_LOOP",let
  val th = (APP_FRAME `R30 a i` o Q.INST [`a`|->`ax`] o INST_TYPE [``:'i``|->``:30``]) PF_BODY
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POST1 `S` (MOVE_PRE `S` th))
  val th = (Q.SPEC `n` o UNDISCH o MATCH_MP ARM_ADDRESS_DOWN_LOOP o Q.GEN `i`) th  
  val th = RW [PF_INV_def,MAP,STAR_LIST_def,emp_STAR,WORD_MULT_CLAUSES,WORD_ADD_0] th
  val th = APP_PART_WEAKEN1 (SIMP_RULE (bool_ss++sep2_ss) [] th) `emp`  
    (SIMP_TAC std_ss [SEP_IMP_def,emp_def,cond_def])
  val th = RW [emp_STAR,ARM_PROG_MOVE_COND,WORD_LOWER_EQ_REFL,PF_0,MAP,STAR_LIST_def] th
  val th = RW [GSYM ARM_PROG_MOVE_COND] (SIMP_RULE bool_ss [PF_FULL] th)  
  val th = PAT_DISCH ``x = y:'a word`` th
  val th = PAT_DISCH ``!xs ys. Q (xs ++ ys) = Q (ys ++ xs)`` th  
  val th = DISCH_ALL th
  val th = RW [WORD_SUB_RNEG] (Q.INST [`w`|->`$- w`] th)
  val lemma = prove(``!x:'a word w n. x + w * n + $- w * n = x``,
    REWRITE_TAC [GSYM WORD_ADD_ASSOC,GSYM WORD_RIGHT_ADD_DISTRIB,WORD_ADD_RINV]
    \\ REWRITE_TAC [WORD_MULT_CLAUSES,WORD_ADD_0])
  val th = RW [lemma] (Q.INST [`ax`|->`y + w * n`] th)
  val pp = METIS_PROVE [PERM_TRANS,PERM_SYM] 
            ``!xs ys zs. PERM ys zs ==> (PERM xs ys = PERM xs zs)``
  val th = RW [MATCH_MP pp (SPEC_ALL PERM_addresses)] th
  in th end);
  

(* ----------------------------------------------------------------------------- *)
(* Lemmas and helping definitions                                                *)
(* ----------------------------------------------------------------------------- *)

val STRENGTHEN_LEMMA = ARM_PROG_STRENGTHEN_PRE;
val PART_STRENGTHEN_LEMMA = ARM_PROG_PART_STRENGTHEN_PRE;

val WEAKEN1_LEMMA = ARM_PROG_WEAKEN_POST1;
val PART_WEAKEN1_LEMMA = ARM_PROG_PART_WEAKEN_POST1; 

val WEAKEN_LEMMA = ARM_PROG_WEAKEN_POST;
val PART_WEAKEN_LEMMA = ARM_PROG_PART_WEAKEN_POST;

fun SEP_IMP_SIMP ss rw = SEP_IMP_RULE (SIMP_CONV (bool_ss++ss) (SEP_IMP_REFL::rw));


(* helping definitions, move to arm_progScript? *)

val b2w_def = Define `(b2w T = 1w) /\ (b2w F = 0w)`;

val addr32f_def = Define `
  addr32f x b = addr32 x + b2w b`;

val addr32f_TEST = prove(
  ``!x b. (addr32f x b && 1w = 0w) = ~b``,
  NTAC 2 Cases \\ REWRITE_TAC [b2w_def,addr32_n2w,word_add_n2w,ADD_0,addr32f_def]
  \\ SIMP_TAC bool_ss [CART_EQ,word_and_def] \\ REPEAT STRIP_TAC << [
    Q.EXISTS_TAC `0` \\ ONCE_REWRITE_TAC [word_index_n2w]
    \\ SIMP_TAC (std_ss++SIZES_ss) [BIT_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def,FCP_BETA] 
    \\ REWRITE_TAC [DECIDE ``4 * n + 1 = (n * 2) * 2 + 1``]
    \\ SIMP_TAC std_ss [MOD_MULT],
    ONCE_REWRITE_TAC [word_index_n2w]
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [BIT_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def,FCP_BETA] 
    \\ REWRITE_TAC [DECIDE ``SUC i - i = SUC 0``,EXP]
    \\ Cases_on `i` \\ SIMP_TAC std_ss [] 
    THEN1 (REWRITE_TAC [DECIDE ``4 * n = n * 2 * 2``] \\ SIMP_TAC std_ss [MOD_EQ_0])
    \\ REWRITE_TAC [EXP]
    \\ `0 < 2 ** n'` by SIMP_TAC std_ss [ZERO_LT_EXP]  
    \\ `1 < 2 * 2 ** n' /\ 0 < 2 * 2 ** n' /\ 0 < 2` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO,LESS_MOD]]);

val addr32f_CLEAR = prove(
  ``!x. addr32f x T - 1w = addr32f x F``,
  REWRITE_TAC [addr32f_def,b2w_def,WORD_ADD_SUB,WORD_ADD_0]);

val BIT_THM = prove(
  ``!n m. BIT n m = ((m DIV 2**n) MOD 2 = 1)``,
  REWRITE_TAC [BIT_def,BITS_def,MOD_2EXP_def,DIV_2EXP_def,DECIDE ``SUC n - n = 1``,EVAL ``2**1``]);
  
val w2n_CLAUSES = prove(
  ``(w2n (0w:'a word) = 0) /\ (w2n (1w:'a word) = 1)``,
  SIMP_TAC bool_ss [w2n_n2w,dimword_def]
  \\ ASSUME_TAC (RW [GSYM (EVAL ``SUC 0``)] DIMINDEX_GE_1)
  \\ ASSUME_TAC (GEN_ALL (RW [EVAL ``0<2``] (Q.INST [`x`|->`2`] ZERO_LT_EXP)))
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS]
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD]
  \\ REWRITE_TAC [EXP_ADD,EXP,EVAL ``2*1``] \\ MATCH_MP_TAC LESS_MOD
  \\ REWRITE_TAC [LESS_EQ,EVAL ``SUC 1``]
  \\ `?k. 2**p = SUC 0 + k` by ASM_REWRITE_TAC [GSYM LESS_EQ,GSYM LESS_EQ_EXISTS]  
  \\ ASM_REWRITE_TAC [LEFT_ADD_DISTRIB,EVAL ``2 * SUC 0``] \\ DECIDE_TAC);

val addr32f_SET = prove(
  ``!x b. addr32f x b !! 1w = addr32f x T``,
  Cases
  \\ SIMP_TAC std_ss [addr32f_def,b2w_def,addr32_n2w,CART_EQ,word_or_def,FCP_BETA,word_add_def]
  \\ ONCE_REWRITE_TAC [word_index_n2w] 
  \\ SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC \\ REWRITE_TAC [BIT_THM,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ `4 * n < 4 * 1073741824` by ASM_REWRITE_TAC [LT_MULT_LCANCEL,EVAL ``0<4``]
  \\ FULL_SIMP_TAC bool_ss [EVAL ``4 * 1073741824``] \\ ASM_SIMP_TAC std_ss [LESS_MOD]
  \\ REWRITE_TAC [DECIDE ``4*n=(2*n)*2``] \\ Cases_on `i`
  \\ SIMP_TAC bool_ss [EVAL ``2**0``,DIV_1,EVAL ``1<2``,LESS_MOD,MOD_MULT]
  \\ SIMP_TAC std_ss [EXP,GSYM DIV_DIV_DIV_MULT,ZERO_DIV]
  \\ Cases_on `b` \\ REWRITE_TAC [b2w_def,w2n_CLAUSES]
  \\ SIMP_TAC std_ss [DIV_MULT]);

val addr32f_INTRO = prove(
  ``addr32 x = addr32f x F``,
  REWRITE_TAC [addr32f_def,b2w_def,WORD_ADD_0]);

(*  *)

val UNROLL_LOOP = prove(
  ``ARM_PROG Q cs C Q' Z' ==>
    ARM_PROG P cs C SEP_F {(Q,pcADD 0w)} ==>
    ARM_PROG P cs C Q' Z'``,
  REWRITE_TAC [ARM_PROG_THM,ARM_GPROG_FALSE_POST,pcADD_0]  
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (RW [UNION_EMPTY,UNION_IDEMPOT] 
        (Q.SPECL [`y`,`{}`,`x`,`c`,`c`,`{}`,`z'`] ARM_GPROG_COMPOSE)));  

val (ADDRESS_LOOP3,ADDRESS_LOOP3_RAW) = let
  (*  make_spec ["orr t, a, #1","mov a, b","mov b, c","mov c, t","tst a, #1"] *)
  val th = (*  orr t, a, #1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x1`,`y`|->`y1` ] arm_ORR2))
  val th = (*  mov a, b      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a`,`a`|->`b`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_MOV2))) `x1*x2*x3` `(x1*x3)*(x2)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  mov b, c      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`c`,`a_mode`|->`OneReg`,`x`|->`x3`,`y`|->`y3` ] arm_MOV2))) `x1*x2*x3*x4` `(x1*x3)*(x2*x4)` `x1*x2*x3` `(x2*x3)*(x1)`
  val th = (*  mov c, t      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`c`,`a`|->`t`,`a_mode`|->`OneReg`,`x`|->`x4`,`y`|->`y4` ] arm_MOV2))) `x1*x2*x3*x4*x5` `(x1*x3*x5)*(x2*x4)` `x1*x2*x3` `(x2*x3*x1)*(emp)`
  val th = (*  tst a, #1     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 1w`,`x`|->`x5` ] arm_TST1))) `x1*x2*x3*x4*x5` `(x3*x5)*(x1*x2*x4)` `x1*x2` `(x2*x1)*(emp)`
  val b =  (*  beq k         *) SIMP_RULE (bool_ss ++ armINST_ss) [] (Q.INST [`c_flag`|->`EQ`,`offset`|->`k`] arm_B) 
  val th = AUTO_HIDE_STATUS (FRAME_COMPOSE th (MATCH_INST1 [`S`] th b))
  val th = Q.INST [`x1`|->`ax`,`x2`|->`bx`,`x3`|->`cx`] th
  val th = AUTO_HIDE_POST1 [`R t`] th
  val th = AUTO_HIDE_POST [`R t`] th
  val th = AUTO_HIDE_PRE [`R t`] th
  val th = Q.INST [`ax`|->`addr32f ax F`,`bx`|->`addr32f bx bb`,`cx`|->`addr32f cx cb`] th
  val th = RW [addr32f_TEST,GSYM addr32f_INTRO,GSYM R30_def] th
  val th' = (SPEC_ALL o ASSUME) 
                ``!ax xs. ARM_PROG (R30 a ax * Inv xs * ~R t * ~S * cond (P ax)) code C 
                                   (R30 a ax * Inv (ax::xs) * ~R t * ~S) {}``
  val th' = APP_FRAME `R b (addr32f bx bb) * R c (addr32f cx cb)` th'
  val th = FRAME_COMPOSE th' th
  val th = foldl (uncurry MOVE_POST1) th [`R a`,`R b`,`R c`,`Inv`,`R t`,`S`]
  val th = foldl (uncurry MOVE_POST) th [`R a`,`R b`,`R c`,`Inv`,`R t`,`S`]
  val th = foldl (uncurry MOVE_PRE) th [`R30 a`,`R b`,`R c`,`Inv`,`R t`,`S`]
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = RW [addr32f_INTRO,R30_def] th
  val lemma = METIS_PROVE []
    ``ARM_PROG P cs C Q ((Q',pcADD k) INSERT Z) ==>
      (k = 0w) ==> ARM_PROG P cs C Q ((Q',pcADD 0w) INSERT Z)``;
  val th = UNDISCH (MATCH_MP lemma th)
  val f = SIMP_RULE (bool_ss++sep_ss) [addr32f_SET,ARM_PROG_FALSE_POST]
  val f = APP_FRAME `cond (P (bx:word30) /\ P (cx:word30) /\ P (ax:word30))` o f
  val f = SIMP_RULE (bool_ss++sep2_ss) [] o f
  val f = RW [METIS_PROVE [] ``a/\b/\c/\a = a/\b/\c:bool``] o f
  val th1 = (f o Q.INST [`bb`|->`F`,`cb`|->`F`]) th  
  val th2 = (f o Q.INST [`bb`|->`F`,`cb`|->`T`]) th  
  val th3 = (f o Q.INST [`bb`|->`T`,`cb`|->`T`]) th  
  val th = MATCH_MP (MATCH_MP UNROLL_LOOP th2) th1
  val th = MATCH_MP (MATCH_MP UNROLL_LOOP th3) th
  val th = Q.SPEC `emp` (MATCH_MP PART_WEAKEN1_LEMMA th)
  val th = RW [emp_STAR] (CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [SEP_IMP_def,emp_def,cond_def])) th)
  (* make_spec ["sub a, a, #1","sub b, b, #1","sub c, c, #1"] *)
  val th' = (*  sub a, a, #1  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a_mode`|->`Imm 1w`,`x`|->`x1` ] arm_SUB1))
  val th' = (*  sub b, b, #1  *) MOVE_COMPOSE th' (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x2` ] arm_SUB1))) `x1*x2` `(x2)*(x1)` `x1*x2` `(x2)*(x1)`
  val th' = (*  sub c, c, #1  *) MOVE_COMPOSE th' (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`c`,`a_mode`|->`Imm 1w`,`x`|->`x3` ] arm_SUB1))) `x1*x2*x3` `(x2)*(x1*x3)` `x1*x2` `(x2)*(x1)`
  val th' = AUTO_HIDE_STATUS th'
  val th' = APP_FRAME `~R t * Inv (cx:word30 ::bx::ax::xs)` th'  
  val th' = foldl (uncurry MOVE_POST1) th' [`R a`,`R b`,`R c`,`Inv`,`R t`,`S`]
  val th' = foldl (uncurry MOVE_PRE) th' [`R a`,`R b`,`R c`,`Inv`,`R t`,`S`]
  val th' = RW [addr32f_CLEAR] (MATCH_COMPOSE th th')
  val f = RW [GSYM addr32f_INTRO,GSYM R30_def] 
  val f = RW [GSYM APPEND_ASSOC,APPEND] o f  
  val f = SIMP_RULE (bool_ss++sep2_ss) [] o MOVE_POST1 `S` o MOVE_PRE `S` o f  
  val f = DISCH_ALL o PAT_DISCH ``x = 0w:word30`` o f
  in (f th',f th) end;


(* ----------------------------------------------------------------------------- *)
(* Garbage collector                                                             *)
(* ----------------------------------------------------------------------------- *)

(* basic code specs *)

(*
compose_progs'
 [("orr t, a1, #1",true),
  ("str t, [a, #4]",true)] "th" "  "
*)

val fst_init = let
  val th1 = (*  orr t, a1, #1  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`t`,`a`|->`a1`,`a_mode`|->`Imm 1w`,`x`|->`x1`,`y`|->`y1` ] arm_ORR2) 
  val th2 = (*  str t, [a, #4]  *) SIMP_RULE (bool_ss ++ armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`a`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_STR_NONALIGNED) 
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(x2 :word32)`|->`(x1 :word32) !! (1w :word32)` ] (FST_PROG2 th2))
  val th = ALIGN_VARS ["y2","x1"] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th)
  in th end;

(*
compose_progs'
 [("teq a, #0",true),
  ("beq 176",true)] "th" "  "
*)

val start_case1 = let
  val th1 = (*  teq a, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 176  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (42w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`42w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th2))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_HIDE_STATUS th
  in th end;  

(*
compose_progs'
 [("teq a, #0",true),
  ("beq 176",false),
  ("ldr a1, [a, #4]",true),
  ("ands t, a1, #1",true),
  ("bne 164",true)] "th" "  "
*)

val start_case2 = let
  val th1 = (*  teq a, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 176  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (42w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`42w` ] arm_B2)
  val th3 = (*  ldr a1, [a, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a1`,`b`|->`a`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands t, a1, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`t`,`a`|->`a1`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 164  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (39w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`39w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th5))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_HIDE_STATUS th
  val th = ALIGN_VARS ["x1"] th
  in th end;

(*
make_spec'
 [("teq a, #0",true),
  ("beq 176",false),
  ("ldr a1, [a, #4]",true),
  ("ands t, a1, #1",true),
  ("bne 164",false)]
*)

val start_case3 = let
  val th = (*  teq a, #0        *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1))
  val th = (*  beq 176          *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (42w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`42w` ] arm_B2))) `x1*x2` `(x2)*(x1)` `x1*x2` `(x1)*(x2)`
  val th = (*  ldr a1, [a, #4]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a1`,`b`|->`a`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED))) `x1*x2` `(x1*x2)*(emp)` `x1*x2*x3*x4` `(x4*x2)*(x1*x3)`
  val th = (*  ands t, a1, #1   *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`t`,`a`|->`a1`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2))) `x1*x2*x3*x4` `(x1*x4)*(x2*x3)` `x1*x2*x3` `(x1*x3)*(x2)`
  val th = (*  bne 164          *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (39w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`39w` ] arm_B2))) `x1*x2*x3*x4*x5` `(x3)*(x1*x2*x4*x5)` `x1*x2` `(x1)*(x2)`
  val th = ALIGN_VARS ["x1"] (AUTO_HIDE_STATUS th)
  in th end;

(*
compose_progs'
 [("teq a1, #0",true),
  ("beq 40",true)] "th" "  "
*)

val fst_case1 = let
  val th1 = (*  teq a1, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a1`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th2))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  in th end;  

(*
compose_progs'
 [("teq a1, #0",true),
  ("beq 40",false),
  ("ldr t, [a1, #4]",true),
  ("ands a2, t, #1",true),
  ("bne 28",true)] "th" "  "
*)

val fst_case2 = let
  val th1 = (*  teq a1, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a1`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th3 = (*  ldr t, [a1, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`a1`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands a2, t, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`a2`,`a`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th5))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["x1"] th
  in th end;

(*
compose_progs'
 [("teq a1, #0",true),
  ("beq 40",false),
  ("ldr t, [a1, #4]",true),
  ("ands a2, t, #1",true),
  ("bne 28",false),
  ("orr p ,p, #1",true),
  ("str p, [a, #4]",true),
  ("mov p, a",true),
  ("mov a, a1",true),
  ("mov a1, t",true),
  ("b -48",true)] "th" "  "
*)

val fst_case3 = let
  val th1 = (*  teq a1, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a1`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th3 = (*  ldr t, [a1, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`a1`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands a2, t, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`a2`,`a`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th6 = (*  orr p ,p, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`p`,`a_mode`|->`Imm 1w`,`x`|->`x6` ] arm_ORR1)
  val th7 = (*  str p, [a, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`p`,`b`|->`a`,`imm`|->`4w`,`x`|->`x7`,`y`|->`y7`,`z`|->`z7` ] arm_STR_NONALIGNED)
  val th8 = (*  mov p, a  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x8`,`y`|->`y8` ] arm_MOV2)
  val th9 = (*  mov a, a1  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a`,`a`|->`a1`,`a_mode`|->`OneReg`,`x`|->`x9`,`y`|->`y9` ] arm_MOV2)
  val th10 = (*  mov a1, t  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a1`,`a`|->`t`,`a_mode`|->`OneReg`,`x`|->`x10`,`y`|->`y10` ] arm_MOV2)
  val th11 = (*  b -48  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (16777202w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777202w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (SND_PROG2 th5))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th6))
  val th = FRAME_COMPOSE th (Q.INST [`(x7 :word32)`|->`(x6 :word32) !! (1w :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th7))
  val th = FRAME_COMPOSE th (Q.INST [`(y8 :word32)`|->`(x6 :word32) !! (1w :word32)`,`(x8 :word32)`|->`(y7 :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th8))
  val th = FRAME_COMPOSE th (Q.INST [`(y9 :word32)`|->`(y7 :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)`,`(x9 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th9))
  val th = FRAME_COMPOSE th (Q.INST [`(y10 :word32)`|->`(x1 :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)`,`(x10 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))` ] (FST_PROG2 th10))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th11))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["y7","x1"] th
  in th end;
    
(*
make_spec ["ldr a2, [a, #8]"]
*)

val snd = let
  val th = (*  ldr a2, [a, #8]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a2`,`b`|->`a`,`imm`|->`8w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = ALIGN_VARS ["y1"] (AUTO_HIDE_STATUS th)
  val th = Q.INST [`y1`|->`ax`,`z1`|->`a2x`] th
  in th end;

(*
compose_progs'
 [("teq a2, #0",true),
  ("beq 40",true)] "th" "  "
*)

val ret1_case1 = let
  val th1 = (*  teq a2, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a2`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th2))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  in th end;  

(*
compose_progs'
 [("teq a2, #0",true),
  ("beq 40",false),
  ("ldr t, [a2, #4]",true),
  ("ands a1, t, #1",true),
  ("bne 28",true)] "th" "  "
*)

val ret1_case2 = let
  val th1 = (*  teq a2, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a2`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th3 = (*  ldr t, [a2, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`a2`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands a1, t, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`a1`,`a`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th5))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["x1"] th
  in th end;

(*
compose_progs'
 [("teq a2, #0",true),
  ("beq 40",false),
  ("ldr t, [a2, #4]",true),
  ("ands a1, t, #1",true),
  ("bne 28",false),
  ("orr p ,p, #1",true),
  ("str p, [a, #8]",true),
  ("mov p, a",true),
  ("mov a, a2",true),
  ("mov a1, t",true),
  ("b -96",true)] "th" "  "
*)

val ret1_case3 = let
  val th1 = (*  teq a2, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`a2`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 40  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (8w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`8w` ] arm_B2)
  val th3 = (*  ldr t, [a2, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`a2`,`imm`|->`4w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands a1, t, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`a1`,`a`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th6 = (*  orr p ,p, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`p`,`a_mode`|->`Imm 1w`,`x`|->`x6` ] arm_ORR1)
  val th7 = (*  str p, [a, #8]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`p`,`b`|->`a`,`imm`|->`8w`,`x`|->`x7`,`y`|->`y7`,`z`|->`z7` ] arm_STR_NONALIGNED)
  val th8 = (*  mov p, a  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`p`,`a_mode`|->`OneReg`,`x`|->`x8`,`y`|->`y8` ] arm_MOV2)
  val th9 = (*  mov a, a2  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a`,`a`|->`a2`,`a_mode`|->`OneReg`,`x`|->`x9`,`y`|->`y9` ] arm_MOV2)
  val th10 = (*  mov a1, t  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a1`,`a`|->`t`,`a_mode`|->`OneReg`,`x`|->`x10`,`y`|->`y10` ] arm_MOV2)
  val th11 = (*  b -96  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (16777190w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777190w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (SND_PROG2 th5))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th6))
  val th = FRAME_COMPOSE th (Q.INST [`(x7 :word32)`|->`(x6 :word32) !! (1w :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th7))
  val th = FRAME_COMPOSE th (Q.INST [`(y8 :word32)`|->`(x6 :word32) !! (1w :word32)`,`(x8 :word32)`|->`(y7 :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th8))
  val th = FRAME_COMPOSE th (Q.INST [`(y9 :word32)`|->`(y7 :word32)`,`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)`,`(x9 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th9))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)`,`(x10 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2))`,`(y10 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32)` ] (FST_PROG2 th10))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (4w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th11))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["y7","x1"] th
  in th end;

(*
compose_progs'
 [("teq p, #0",true),
  ("beq 56",true)] "th" "  "
*)

val ret2_case1 = let
  val th1 = (*  teq p, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`p`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 56  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (12w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`12w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th2))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["x1"] th
  val th = SIMP_RULE (bool_ss++sep2_ss) [addr32_EQ_0] (Q.INST [`x1`|->`px`] th)
  in th end;

(*
compose_progs'
 [("teq p, #0",true),
  ("beq 56",false),
  ("ldr a2, [p, #8]",true),
  ("ands t, a2, #1",true),
  ("bne 28",true)] "th" "  "
compose_progs'
 [("str a, [p, #8]",true),
  ("mov a, p",true),
  ("sub p, a2, #1",true),
  ("b -56",true)] "th" "  "
*)

val ret2_case2 = let
  val th1 = (*  teq p, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`p`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 56  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (12w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`12w` ] arm_B2)
  val th3 = (*  ldr a2, [p, #8]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a2`,`b`|->`p`,`imm`|->`8w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands t, a2, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`t`,`a`|->`a2`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th5))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["x1"] th
  val code = 
  ``[enc (LDR AL F <|Pre := T; Up := T; Wb := F|> t p (Dt_immediate 4w));
     enc (ORR AL F a a (Dp_immediate 0w 1w));
     enc (STR AL F <|Pre := T; Up := T; Wb := F|> a p (Dt_immediate 4w));
     enc (MOV AL F a (Dp_shift_immediate (LSL p) 0w));
     enc (SUB AL F p t (Dp_immediate 0w 1w)); enc (B AL 16777193w)]``
  val th = APP_APPEND th code
  val contract = prove(``ARM_PROG P cs C SEP_F ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C Q Z``,METIS_TAC [ARM_PROG_EXTRACT_POST])
  val th = MATCH_MP contract th
  val th' = SIMP_RULE std_ss [pcINC_def,wLENGTH_def,LENGTH] th
  val th1 = (*  str a, [p, #8]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`b`|->`p`,`imm`|->`8w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_STR_NONALIGNED)
  val th2 = (*  mov a, p  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a`,`a`|->`p`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_MOV2)
  val th3 = (*  sub p, a2, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`p`,`a`|->`a2`,`a_mode`|->`Imm 1w`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2)
  val th4 = (*  b -56  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (16777200w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777200w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(y2 :word32)`|->`(x1 :word32)`,`(x2 :word32)`|->`(y1 :word32)` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(y3 :word32)`|->`(y1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [ ] (FST_PROG2 th4))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["y1"] th
  val th' = APP_FRAME `R a ax` th'
  val th = APP_FRAME `R t (z3 && 1w)` th
  val th = Q.INST [`x1`|->`ax`,`y1`|->`px`,`x3`|->`a2x`,`z3`|->`a2x`,`z1`|->`a2x`] th 
  val th' = Q.INST [`z3`|->`a2x`,`x1`|->`px`] th'
  val th = PRE_MOVE_STAR `a*p*px2*a2*s*t` `a2*t*p*px2*s*a` th
  val th = MATCH_COMPOSE th' th  
  val th = ALIGN_VARS ["px"] th
  val th = RW [addr32_EQ_0] th
  val th = Q.INST [`a2x`|->`addr32f a2x T`] th
  val th = SIMP_RULE (bool_ss++sep2_ss) [addr32f_TEST,addr32f_CLEAR] th
  val th = HIDE_POST th
  val th = HIDE_POST (POST_MOVE_STAR `a2*p*a*px2*s*t` `p*a*px2*s*t*a2` th)
  val th = RW [GSYM addr32f_INTRO,GSYM R30_def] th
  val th = HIDE_PRE (PRE_MOVE_STAR `p*a2*px2*t*s*a*c` `p*a2*px2*s*a*c*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `p*a2*px2*s*a*c*t` `p*px2*s*a*c*t*a2` th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  in th end;

(*
compose_progs'
 [("teq p, #0",true),
  ("beq 56",false),
  ("ldr a2, [p, #8]",true),
  ("ands t, a2, #1",true),
  ("bne 28",false),
  ("ldr t, [p, #4]",true),
  ("orr a, a, #1",true)] "th" "  "
compose_progs'
 [("str a, [p, #4]",true),
  ("mov a, p",true),
  ("sub p, t, #1",true),
  ("b -84",true)] "th" "  "
*)

val ret2_case3 = let
  val th1 = (*  teq p, #0  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`p`,`a_mode`|->`Imm 0w`,`x`|->`x1` ] arm_TEQ1)
  val th2 = (*  beq 56  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (12w :word24) :word30)``] (Q.INST [`c_flag`|->`EQ`,`offset`|->`12w` ] arm_B2)
  val th3 = (*  ldr a2, [p, #8]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (8w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a2`,`b`|->`p`,`imm`|->`8w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_LDR_NONALIGNED)
  val th4 = (*  ands t, a2, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`T`,`b`|->`t`,`a`|->`a2`,`a_mode`|->`Imm 1w`,`x`|->`x4`,`y`|->`y4` ] arm_AND2)
  val th5 = (*  bne 28  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (5w :word24) :word30)``] (Q.INST [`c_flag`|->`NE`,`offset`|->`5w` ] arm_B2)
  val th6 = (*  ldr t, [p, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`p`,`imm`|->`4w`,`x`|->`x6`,`y`|->`y6`,`z`|->`z6` ] arm_LDR_NONALIGNED)
  val th7 = (*  orr a, a, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a_mode`|->`Imm 1w`,`x`|->`x7` ] arm_ORR1)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (SND_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)`,`(y3 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [`(x4 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2))`,`(sN :bool)`|->`word_msb ((x1 :word32) ?? (0w :word32))`,`(sZ :bool)`|->`(x1 :word32) = (0w :word32)` ] (FST_PROG2 th4))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (SND_PROG2 th5))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) && (1w :word32) = (0w : word32)`,`(x6 :word32)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) && (1w :word32)`,`(y6 :word32)`|->`(x1 :word32)` ] (FST_PROG2 th6))
  val th = FRAME_COMPOSE th (Q.INST [`(sN :bool)`|->`word_msb   ((z3 :word32) #>>    ((8 :num) *     w2n       (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) &&    (1w :word32))`,`(sZ :bool)`|->`(z3 :word32) #>> ((8 :num) *  w2n (((1 :num) >< (0 :num)) ((x1 :word32) + (8w :word32)) :word2)) && (1w :word32) = (0w : word32)` ] (FST_PROG2 th7))
  val th = RW [WORD_XOR_CLAUSES] th
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST1_HIDE_STATUS th)
  val th' = ALIGN_VARS ["x1"] th
  val th1 = (*  str a, [p, #4]  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`b`|->`p`,`imm`|->`4w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_STR_NONALIGNED)
  val th2 = (*  mov a, p  *) SIMP_RULE (bool_ss++armINST_ss) [] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`a`,`a`|->`p`,`a_mode`|->`OneReg`,`x`|->`x2`,`y`|->`y2` ] arm_MOV2)
  val th3 = (*  sub p, t, #1  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`b`|->`p`,`a`|->`t`,`a_mode`|->`Imm 1w`,`x`|->`x3`,`y`|->`y3` ] arm_SUB2)
  val th4 = (*  b -84  *) SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(sw2sw (16777193w :word24) :word30)``] (Q.INST [`c_flag`|->`AL`,`offset`|->`16777193w` ] arm_B2)
  val th = FRAME_COMPOSE (FST_PROG2 th1) (Q.INST [`(y2 :word32)`|->`(x1 :word32)`,`(x2 :word32)`|->`(y1 :word32)` ] (FST_PROG2 th2))
  val th = FRAME_COMPOSE th (Q.INST [`(y3 :word32)`|->`(y1 :word32)` ] (FST_PROG2 th3))
  val th = FRAME_COMPOSE th (Q.INST [ ] (FST_PROG2 th4))
  val th = AUTO_PRE_HIDE_STATUS (AUTO_POST_HIDE_STATUS th)
  val th = ALIGN_VARS ["y1"] th
  val th' = POST1_MOVE_STAR `a*t*p*x1*a2*x12*s` `a*p*x1*t*s*a2*x12` th'
  val th = Q.INST [`x1`|->`x7 !! 1w`,`y1`|->`x1`,`z1`|->`z6`,`y2`|->`x7`,`x3`|->`x6`] th
  val th = RW [STAR_ASSOC] (APP_FRAME `R a2 z3 * M (x1 + 2w) z3` th)
  val th = MATCH_COMPOSE th' th
  val th = Q.INST [`x1`|->`px`,`z3`|->`addr32f a2x F`,`z6`|->`addr32f a1x T`,`x7`|->`addr32f ax F`] th
  val th = SIMP_RULE (bool_ss++sep2_ss) [addr32f_CLEAR,addr32f_SET,addr32f_TEST] th
  val th = RW [GSYM addr32f_INTRO,GSYM R30_def,addr32_EQ_0] th  
  val th = HIDE_POST (POST_MOVE_STAR `t*p*a*px1*s*a2*px2` `p*a*px1*s*a2*px2*t` th)
  val th = RW [addr32f_INTRO] th
  val th = HIDE_PRE (PRE_MOVE_STAR `p*a2*px2*t*px1*a*s*c` `p*a2*px2*px1*a*s*c*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `p*a2*px2*px1*a*s*c*t` `p*px2*px1*a*s*c*t*a2` th)
  in th end;

(* basic concepts *)

val link_block_def = Define `
  link_block (a,a1,b1,a2,b2,x,y) = 
    M (a+1w) (addr32f a1 b1) * M (a+2w) (addr32f a2 b2) * M a x * M (a+3w) y * cond ~(a = 0w)`;

val unseen1_def = Define `unseen1 (a,a1,a2,x,y) = link_block (a,a1,F,a2,F,x,y)`;
val unseen_def  = Define `unseen xs = STAR_LIST (MAP unseen1 xs)`;

val visited1_def = Define `visited1 (a,a1,a2,x,y) = link_block (a,a1,T,a2,F,x,y)`;
val visited_def  = Define `visited xs = STAR_LIST (MAP visited1 xs)`;

val stack_def = Define `
  (stack p [] = cond (p = 0w)) /\
  (stack p (((a1,n,x,y),T)::xs) = link_block (p,a1,T,n,T,x,y) * stack n xs) /\ 
  (stack p (((n,a2,x,y),F)::xs) = link_block (p,n,T,a2,F,x,y) * stack n xs)`;

val stack2list_def = Define `
  (stack2list a p [] = []) /\
  (stack2list a p (((a1,n:word30,x:word32,y:word32),T)::xs) = (p,a1,a,x,y)::stack2list p n xs) /\ 
  (stack2list a p (((n,a2,x,y),F)::xs) = (p,a,a2,x,y)::stack2list p n xs)`;

(* definitions for the spec *)

val is_path_def = Define `
  (is_path x [] y set = (x,y) IN set) /\
  (is_path x (z::zs) y set = (x,z) IN set /\ is_path z zs y set)`;

val is_reachable_def = Define `
  is_reachable set root node = (root = node) \/ ?p. is_path root p node set`;

val is_reachable'_def = Define `
  is_reachable' set roots node = ?r. MEM r roots /\ is_reachable set r node`;

val list2edges_def = Define `
  (list2edges [] = {}) /\
  (list2edges ((a,a1,a2,x,y)::xs) = (a,a1) INSERT (a,a2) INSERT list2edges xs)`;

val reachables'_def = Define `
  reachables' roots xs = 
    FILTER (\x. is_reachable' (list2edges xs) roots (FST x)) xs`;

val unreachables'_def = Define `
  unreachables' roots xs = FILTER (\x. ~MEM x (reachables' roots xs)) xs`;

val reachables_def = Define `
  reachables root xs = FILTER (\x. is_reachable (list2edges xs) root (FST x)) xs`;

val unreachables_def = Define `
  unreachables root xs = FILTER (\x. ~MEM x (reachables root xs)) xs`;

val list2domain_def = Define `
  (list2domain [] = {}) /\
  (list2domain ((a:word30,a1:word30,a2:word30,x:word32,y:word32)::xs) = a INSERT list2domain xs)`;

val list2range_def = Define `
  (list2range [] = {}) /\
  (list2range ((a:word30,a1:word30,a2:word30,x:word32,y:word32)::xs) = a1 INSERT a2 INSERT list2range xs)`;

val domain_def = Define `
  domain xs ys a p zs = list2domain xs UNION list2domain ys UNION list2domain (stack2list a p zs)`;

val range_def = Define `
  range xs ys a p zs = list2range xs UNION list2range ys UNION list2range (stack2list a p zs)`;

val connect_def = Define `
  connect xs ys a p zs = cond (range xs ys a p zs SUBSET (domain xs ys a p zs UNION {0w}))`;

val connect'_def = Define `
  connect' xs ys a p zs extra = cond (range xs ys a p zs SUBSET (domain xs ys a p zs UNION {0w} UNION extra))`;

val uvs_def = Define `
  uvs xs ys ax px zs = unseen xs * visited ys * stack px zs * connect xs ys ax px zs`;

val uvs'_def = Define `
  uvs' xs ys ax px zs bx = uvs (unreachables bx xs) (ys ++ reachables bx xs) ax px zs`;

val has_head_def = Define `
  has_head xs x = (HD xs = x) /\ ~(xs = [])`;

val GC_ASSUMPTION_def = Define `
  GC_ASSUMPTION a p a1 a2 t P C xs = 
  !ys zs px ax a1x a2x x y.
  ARM_PROG
   (uvs xs ys ax px zs * 
    R30 p px * R30 a ax * R30 a1 a1x * ~R t * ~R a2 * ~S * 
    cond (MEM (ax,a1x,a2x,x,y) xs) * P : ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) ARMset -> bool)
   [] C SEP_F {
   (uvs' xs ys ax px zs ax * R30 p px * R30 a ax * ~R a1 * ~R t * ~R a2 * ~S * cond (zs = []),pcADD 40w);   
   ((SEP_EXISTS pa1x pa2x p_x p_y. 
      uvs' xs ((px,ax,pa2x,p_x,p_y)::ys) px pa1x (TL zs) ax * 
      R30 p pa1x * R30 a px * ~R a1 * ~R t * R30 a2 pa2x * ~S * 
      cond (has_head zs ((pa1x,pa2x,p_x,p_y),F))),pcADD 14w);
   ((SEP_EXISTS pa1x pa2x p_x p_y.
      uvs' xs ((px,pa1x,ax,p_x,p_y)::ys) px pa2x (TL zs) ax * 
      R30 p pa2x * R30 a px * ~R a1 * ~R t * ~R a2 * ~S * 
      cond (has_head zs ((pa1x,pa2x,p_x,p_y),T))),pcADD 25w)
   }`;

val assumption = RW [GC_ASSUMPTION_def,emp_STAR] (ASSUME ``GC_ASSUMPTION a p a1 a2 t emp C xs``);


(* introducing the basics into the code specs *)

val fst_init' = let
  val th = HIDE_POST1 (POST1_MOVE_STAR `t*a*y21*a1*s` `a*y21*a1*s*t` fst_init)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*t*a*y21*s` `a1*a*y21*s*t` th)
  val th = Q.INST [`x1`|->`a1x`,`z2`|->`addr32f a1x F`,`y2`|->`ax`] th
  val th = RW [addr32f_INTRO,addr32f_SET] th
  val th = PRE_MOVE_STAR `a1*a*ax1*s*t` `a1*a*s*t*ax1` th
  val th = POST1_MOVE_STAR `a*ax1*a1*s*t` `a1*a*s*t*ax1` th
  val th = APP_FRAME `M (ax + 2w) (addr32f a2x F) * M ax x * M (ax + 3w) y * cond ~(ax = 0w)` th
  val th = PRE_MOVE_STAR `a1*a*s*t*ax1*(ax2*ax*ax3*c)` `a1*a*s*t*(ax1*ax2*ax*ax3*c)` th
  val th = POST1_MOVE_STAR `a1*a*s*t*ax1*(ax2*ax*ax3*c)` `a1*a*s*t*(ax1*ax2*ax*ax3*c)` th  
  val th = RW [GSYM link_block_def] th  
  in th end;

val start_case1' = let
  val th = Q.INST [`x1`|->`ax`] start_case1
  val th = RW [addr32_EQ_0] (ALIGN_VARS ["ax"] th)
  in th end;

val start_case2' = let
  val th = Q.INST [`x1`|->`ax`,`z3`|->`addr32f a1x b`] start_case2
  val th = RW [addr32_EQ_0,addr32f_TEST] (ALIGN_VARS ["ax"] th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*ca*a1*ax1*t*b*s` `a*ca*a1*ax1*b*s*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*ca*a1*ax1*b*s*t` `a*ca*ax1*b*s*t*a1` th)
  val th = HIDE_POST (POST_MOVE_STAR `a1*t*a*ax1*s` `a1*a*ax1*s*t` th)
  val th = HIDE_POST (POST_MOVE_STAR `a1*a*ax1*s*t` `a*ax1*s*t*a1` th)
  val th = APP_FRAME `M (ax + 2w) (addr32f a2x b') * M ax x * M (ax + 3w) y * cond ~(ax = 0w)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (Q.INST [`b`|->`T`] th)
  val th = SPEC_WEAKEN th `R30 a ax * ~S * ~R t * ~R a1 * link_block (ax,a1x,T,a2x,b',x,y)`
  val th = SEP_IMP_SIMP star_ss [link_block_def] th
  val th = SPEC_STRENGTHEN th `R30 a ax * ~S * ~R t * ~R a1 * link_block (ax,a1x,T,a2x,b',x,y)`
  val th = SEP_IMP_SIMP star_ss [link_block_def] th
  in th end;

val start_case3' = let
  val th = Q.INST [`x1`|->`ax`,`z3`|->`addr32f a1x b`] start_case3
  val th = RW [addr32_EQ_0,addr32f_TEST] (ALIGN_VARS ["ax"] th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*ca*a1*ax1*t*b*s` `a*ca*a1*ax1*b*s*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a*ca*a1*ax1*b*s*t` `a*ca*ax1*b*s*t*a1` th)
  val th = HIDE_POST1 (POST1_MOVE_STAR `a1*t*a*ax1*s` `a1*a*ax1*s*t` th)
  val th = APP_FRAME `M (ax + 2w) (addr32f a2x F) * M ax x * M (ax + 3w) y * cond ~(ax = 0w)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (Q.INST [`b`|->`F`] th)
  val th = SPEC_WEAKEN1 th `R30 a ax * ~S * ~R t * R a1 (addr32f a1x F) * link_block (ax,a1x,F,a2x,F,x,y)`
  val th = SEP_IMP_SIMP star_ss [link_block_def] th
  val th = SPEC_STRENGTHEN th `R30 a ax * ~S * ~R t * ~R a1 * link_block (ax,a1x,F,a2x,F,x,y)`
  val th = SEP_IMP_SIMP star_ss [link_block_def] th
  in th end;

val fst_case1' = let
  val th = Q.INST [`x1`|->`a1x`] fst_case1
  val th = RW [addr32_EQ_0] (ALIGN_VARS ["a1x"] th)
  in th end;

val ret1_case1' = let
  val th = Q.INST [`x1`|->`a2x`] ret1_case1
  val th = RW [addr32_EQ_0] (ALIGN_VARS ["a2x"] th)
  in th end;

val fst_case2' = let
  val th = Q.INST [`x1`|->`a1x`,`z3`|->`addr32f na1x b`] fst_case2
  val th = RW [addr32_EQ_0,addr32f_TEST] th
  val th = HIDE_POST (POST_MOVE_STAR `t*a2*a1*a1x1*s` `a2*a1*a1x1*s*t` th)
  val th = HIDE_POST (POST_MOVE_STAR `a2*a1*a1x1*s*t` `a1*a1x1*s*t*a2` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*t*a1x1*a2*b*s` `a1*c*a1x1*a2*b*s*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*a1x1*a2*b*s*t` `a1*c*a1x1*b*s*t*a2` th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = APP_FRAME `cond (~(a1x = 0w:word30) /\ b)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = RW [prove(``cond (b1 /\ b2) = cond b1 * cond b2``,REWRITE_TAC [SEP_cond_CLAUSES]),STAR_ASSOC] th
  val th = APP_FRAME `M (a1x + 2w) (addr32f na2x b') * M a1x x * M (a1x + 3w) y` th
  val th = POST_MOVE_STAR `a1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th
  val th = PRE_MOVE_STAR `a1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th
  val th = RW [GSYM link_block_def] th  
  in th end;  

val ret1_case2' = let
  val th = Q.INST [`x1`|->`a2x`,`z3`|->`addr32f na1x b`] ret1_case2
  val th = RW [addr32_EQ_0,addr32f_TEST] th
  val th = HIDE_POST (POST_MOVE_STAR `t*a2*a1*a1x1*s` `a2*a1*a1x1*s*t` th)
  val th = HIDE_POST (POST_MOVE_STAR `a2*a1*a1x1*s*t` `a1*a1x1*s*t*a2` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*t*a1x1*a2*b*s` `a1*c*a1x1*a2*b*s*t` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*a1x1*a2*b*s*t` `a1*c*a1x1*b*s*t*a2` th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = APP_FRAME `cond (~(a2x = 0w:word30) /\ b)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = RW [prove(``cond (b1 /\ b2) = cond b1 * cond b2``,REWRITE_TAC [SEP_cond_CLAUSES]),STAR_ASSOC] th
  val th = APP_FRAME `M (a2x + 2w) (addr32f na2x b') * M a2x x * M (a2x + 3w) y` th
  val th = POST_MOVE_STAR `a1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th
  val th = PRE_MOVE_STAR `a1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th
  val th = RW [GSYM link_block_def] th  
  in th end;  

val fst_case3' = let
  val th = Q.INST [`x1`|->`a1x`,`z3`|->`addr32f na1x b`,`y7`|->`ax`,`x6`|->`addr32f ppx g`] fst_case3
  val th = RW [addr32_EQ_0,addr32f_TEST,addr32f_SET] th
  val th = RW [GSYM addr32f_INTRO,GSYM R30_def] (Q.INST [`g`|->`F`] th)
  val th = HIDE_POST (POST_MOVE_STAR `t*a1*a*p*px1*a2*a1x1*s` `a1*a*p*px1*a2*a1x1*s*t` th)
  val th = HIDE_POST (POST_MOVE_STAR `a1*a*p*px1*a2*a1x1*s*t` `a1*a*p*px1*a1x1*s*t*a2` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*t*a1x1*a2*b*p*a*px1*s` `a1*c*a1x1*a2*b*p*a*px1*s*t` th) 
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*a1x1*a2*b*p*a*px1*s*t` `a1*c*a1x1*b*p*a*px1*s*t*a2` th) 
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = APP_FRAME `cond (~(a1x = 0w:word30) /\ ~b)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = RW [prove(``cond (b1 /\ b2) = cond b1 * cond b2``,REWRITE_TAC [SEP_cond_CLAUSES]),STAR_ASSOC] th
  val th = APP_FRAME `M (a1x + 2w) (addr32f na2x b') * M a1x x * M (a1x + 3w) y` th
  val th = PRE_MOVE_STAR `a1*a1x1*a2*p*a*px1*s*t*c*b*(ax12*ax1*ax13)` `a1*p*a*px1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th 
  val th = POST_MOVE_STAR `a1*a*p*px1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*p*a*px1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th 
  val th = RW [GSYM link_block_def] th  
  val th = APP_FRAME `M (ax + 2w) (addr32f ax2 F) * M ax p_x * M (ax + 3w) p_y * cond ~(ax = 0w)` th
  val th = Q.INST [`z7`|->`addr32f ax1 T`] th
  val th = PRE_MOVE_STAR `a1*a*ax1*s*t*a2*p*b*bl*(ax2*ax*ax3*c)` `a1*a*s*t*a2*p*b*bl*(ax1*ax2*ax*ax3*c)` th 
  val th = POST_MOVE_STAR `a1*p*a*ax1*s*t*a2*b*bl*(ax2*ax*ax3*c)` `a1*p*a*s*t*a2*b*bl*(ax1*ax2*ax*ax3*c)` th 
  val th = RW [GSYM link_block_def] th  
  val th = APP_FRAME `stack ppx qs` th
  val th = RW [STAR_ASSOC] (RW [GSYM STAR_ASSOC,GSYM stack_def] th)
  val rw = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = RW [rw] th
  in th end;

val ret1_case3' = let
  val th = Q.INST [`x1`|->`a2x`,`z3`|->`addr32f na1x b`,`y7`|->`ax`,`x6`|->`addr32f ppx g`] ret1_case3
  val th = RW [addr32_EQ_0,addr32f_TEST,addr32f_SET] th
  val th = RW [GSYM addr32f_INTRO,R30_def] (Q.INST [`g`|->`F`] th)
  val th = HIDE_POST (POST_MOVE_STAR `t*a1*a2*a*p*pax1*a1x1*s` `a1*a2*a*p*pax1*a1x1*s*t` th)
  val th = HIDE_POST (POST_MOVE_STAR `a1*a2*a*p*pax1*a1x1*s*t` `a1*a*p*pax1*a1x1*s*t*a2` th)
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*t*a1x1*a2*b*p*a*px1*s` `a1*c*a1x1*a2*b*p*a*px1*s*t` th) 
  val th = HIDE_PRE (PRE_MOVE_STAR `a1*c*a1x1*a2*b*p*a*px1*s*t` `a1*c*a1x1*b*p*a*px1*s*t*a2` th) 
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = APP_FRAME `cond (~(a2x = 0w:word30) /\ ~b)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th = RW [prove(``cond (b1 /\ b2) = cond b1 * cond b2``,REWRITE_TAC [SEP_cond_CLAUSES]),STAR_ASSOC] th
  val th = APP_FRAME `M (a2x + 2w) (addr32f na2x b') * M a2x x * M (a2x + 3w) y` th
  val th = PRE_MOVE_STAR `a1*a1x1*a2*p*a*px1*s*t*c*b*(ax12*ax1*ax13)` `a1*p*a*px1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th 
  val th = POST_MOVE_STAR `a1*a*p*px1*a1x1*s*t*a2*c*b*(ax12*ax1*ax13)` `a1*p*a*px1*s*t*a2*b*(a1x1*ax12*ax1*ax13*c)` th 
  val th = RW [GSYM link_block_def,GSYM R30_def] th  
  val th = APP_FRAME `M (ax + 1w) (addr32f ax1 T) * M ax p_x * M (ax + 3w) p_y * cond ~(ax = 0w)` th
  val th = Q.INST [`z7`|->`addr32f ax2 F`] th
  val th = PRE_MOVE_STAR `a1*a*ax1*s*t*a2*p*b*bl*(ax2*ax*ax3*c)` `a1*a*s*t*a2*p*b*bl*(ax2*ax1*ax*ax3*c)` th 
  val th = POST_MOVE_STAR `a1*p*a*ax1*s*t*a2*b*bl*(ax2*ax*ax3*c)` `a1*p*a*s*t*a2*b*bl*(ax2*ax1*ax*ax3*c)` th 
  val th = RW [GSYM link_block_def] th  
  val th = APP_FRAME `stack ppx qs` th
  val th = RW [STAR_ASSOC] (RW [GSYM STAR_ASSOC,GSYM stack_def] th)
  val rw = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = RW [rw] th
  in th end;

val snd' = let
  val th = Q.INST [`a2x`|->`addr32f a2x F`] snd
  val th = HIDE_PRE (PRE_MOVE_STAR `a2*a*ax2*s` `a*ax2*s*a2` th) 
  val th = APP_FRAME `M (ax + 1w) (addr32f a1x T) * M ax x * M (ax + 3w) y * cond ~(ax = 0w)` th
  val th = PRE_MOVE_STAR `a*ax2*s*a2*(ax1*x*y*c)` `a*s*a2*(ax1*ax2*x*y*c)` th 
  val th = POST1_MOVE_STAR `a2*a*ax2*s*(ax1*x*y*c)` `a*s*a2*(ax1*ax2*x*y*c)` th 
  val th = RW [GSYM link_block_def] th
  val th = RW [GSYM addr32f_INTRO,GSYM R30_def] th
  in th end;  

val ret2_case1' = ret2_case1;

val ret2_case2' = let
  val th = ret2_case2
  val th = Q.INST [`ax`|->`addr32f ax F`] th
  val th = PRE_CONV_RULE (REWRITE_CONV [GSYM addr32f_INTRO, GSYM R30_def]) th
  val th = APP_FRAME `M (px + 1w) (addr32f a1x T) * M px x * M (px+3w) y * cond ~(px = 0w)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = MATCH_MP STRENGTHEN_LEMMA th  
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * link_block (px,a1x,T,a2x,T,x,y) * ~S` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [link_block_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  val th = MATCH_MP WEAKEN_LEMMA th  
  val th = Q.SPEC `R30 a px * R30 p a2x * ~R a2 * ~R t * link_block (px,a1x,T,ax,F,x,y) * ~S` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [link_block_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  in th end;

val ret2_case3' = let
  val th = ret2_case3
  val th = APP_FRAME `M px x * M (px+3w) y * cond ~(px = 0w)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = MATCH_MP STRENGTHEN_LEMMA th  
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * link_block (px,a1x,T,a2x,F,x,y) * ~S` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [link_block_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  val th = MATCH_MP WEAKEN_LEMMA th  
  val th = Q.SPEC `R30 a px * R30 p a1x * R30 a2 a2x * ~R t * link_block (px,ax,T,a2x,F,x,y) * ~S` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [link_block_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  in th end;

val ARM_PROG_COMPOSE_0 = prove(
  ``ARM_PROG Q [] C SEP_F Z ==> 
    ARM_PROG P cs {} SEP_F {(Q,pcADD 0w)} ==> 
    ARM_PROG P cs C SEP_F Z``,
  REWRITE_TAC [ARM_PROG_THM,pcINC_0,pcADD_0,ARM_GPROG_FALSE_POST,ARM_GPROG_EMPTY_CODE]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION] \\ REWRITE_TAC [UNION_EMPTY]
  \\ METIS_TAC [ARM_GPROG_COMPOSE,UNION_EMPTY]);

val connect_POP = prove(
  ``connect ((a1x,na1x,na2x,x,y)::xs) ((ax,a1x,a2x,p_x,p_y)::ys) ax ppx qs =
    connect ((a1x,na1x,na2x,x,y)::xs) ys a1x ax (((ppx,a2x,p_x,p_y),F)::qs)``,
  REWRITE_TAC [connect_def,domain_def,range_def,stack2list_def,list2range_def,list2domain_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y) ``)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) /\ (z = q) ==> (f x z = f y q) ``)
  \\ STRIP_TAC \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_UNION,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []);

val connect_POP2 = prove(
  ``connect ((a1x,na1x,na2x,x,y)::xs) ((ax,a2x,a1x,p_x,p_y)::ys) ax ppx qs =
    connect ((a1x,na1x,na2x,x,y)::xs) ys a1x ax (((a2x,ppx,p_x,p_y),T)::qs)``,
  REWRITE_TAC [connect_def,domain_def,range_def,stack2list_def,list2range_def,list2domain_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y) ``)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) /\ (z = q) ==> (f x z = f y q) ``)
  \\ STRIP_TAC \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_UNION,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []);

(* prove that those elements of xs that are reachable from a1x have moved to ys *)

val STAR_LIST_APPEND = prove(
  ``!xs ys. STAR_LIST (xs ++ ys) = STAR_LIST xs * STAR_LIST ys``,
  Induct \\ ASM_REWRITE_TAC [APPEND,APPEND_NIL,STAR_LIST_def,emp_STAR,STAR_ASSOC]);

val STAR_LIST_APPEND_COMM = prove(
  ``!xs ys. STAR_LIST (xs ++ ys) = STAR_LIST (ys ++ xs)``,
  REWRITE_TAC [STAR_LIST_APPEND] \\ METIS_TAC [STAR_COMM]);

val STAR_LIST_APPEND_COMM2 = prove(
  ``!zs xs ys. STAR_LIST (zs ++ xs ++ ys) = STAR_LIST (zs ++ ys ++ xs)``,
  REWRITE_TAC [STAR_LIST_APPEND] \\ METIS_TAC [STAR_COMM,STAR_ASSOC]);

val list2range_APPEND = prove(
  ``!xs ys. list2range (xs ++ ys) = list2range xs UNION list2range ys``,
  Induct \\ ASM_REWRITE_TAC [list2range_def,APPEND_NIL,APPEND,UNION_EMPTY] 
  \\ STRIP_TAC \\ `?a a1 a2 x y. h = (a,a1,a2,x,y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2range_def,INSERT_UNION_EQ]);
  
val list2domain_APPEND = prove(
  ``!xs ys. list2domain (xs ++ ys) = list2domain xs UNION list2domain ys``,
  Induct \\ ASM_REWRITE_TAC [list2domain_def,APPEND_NIL,APPEND,UNION_EMPTY] 
  \\ STRIP_TAC \\ `?a a1 a2 x y. h = (a,a1,a2,x,y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2domain_def,INSERT_UNION_EQ]);

val connect_xs_comm = prove(
  ``!xs xs' ys ax px qs.
      connect (xs ++ xs') ys ax px qs = connect (xs' ++ xs) ys ax px qs``,
  REWRITE_TAC [connect_def,range_def,domain_def,list2domain_APPEND,list2range_APPEND]
  \\ METIS_TAC [UNION_COMM]);

val connect_ys_comm = prove(
  ``!xs ys' ys ax px qs.
      connect xs (ys ++ ys') ax px qs = connect xs (ys' ++ ys) ax px qs``,
  REWRITE_TAC [connect_def,range_def,domain_def,list2domain_APPEND,list2range_APPEND]
  \\ METIS_TAC [UNION_COMM]);

val connect_xs_comm2 = prove(
  ``!xs xs' xs'' ys ax px qs.
      connect (xs'' ++ xs ++ xs') ys ax px qs = connect (xs'' ++ xs' ++ xs) ys ax px qs``,
  REWRITE_TAC [connect_def,range_def,domain_def,list2domain_APPEND,list2range_APPEND]
  \\ METIS_TAC [UNION_COMM,UNION_ASSOC]);

val connect_ys_comm2 = prove(
  ``!xs ys ys' ys'' ax px qs.
      connect xs (ys'' ++ ys ++ ys') ax px qs = connect xs (ys'' ++ ys' ++ ys) ax px qs``,
  REWRITE_TAC [connect_def,range_def,domain_def,list2domain_APPEND,list2range_APPEND]
  \\ METIS_TAC [UNION_COMM,UNION_ASSOC]);

val uvs_xs_comm = prove(
  ``!xs xs' ys ax px qs. uvs (xs++xs') ys ax px qs = uvs (xs'++xs) ys ax px qs``,
  REWRITE_TAC [uvs_def,unseen_def,MAP_APPEND,unseen1_def]
  \\ METIS_TAC [STAR_LIST_APPEND_COMM,connect_xs_comm]);

val uvs_ys_comm = prove(
  ``!xs ys' ys ax px qs. uvs xs (ys++ys') ax px qs = uvs xs (ys'++ys) ax px qs``,
  REWRITE_TAC [uvs_def,visited_def,MAP_APPEND,visited1_def]
  \\ METIS_TAC [STAR_LIST_APPEND_COMM,connect_ys_comm]);

val uvs_xs_comm2 = prove(
  ``!xs xs' xs'' ys ax px qs. uvs (xs++xs'++xs'') ys ax px qs = uvs (xs++xs''++xs') ys ax px qs``,
  REWRITE_TAC [uvs_def,unseen_def,MAP_APPEND,unseen1_def]
  \\ METIS_TAC [STAR_LIST_APPEND_COMM2,connect_xs_comm2]);

val uvs_ys_comm2 = prove(
  ``!xs ys ys' ys'' ax px qs. uvs xs (ys++ys'++ys'') ax px qs = uvs xs (ys++ys''++ys') ax px qs``,
  REWRITE_TAC [uvs_def,visited_def,MAP_APPEND,visited1_def]
  \\ METIS_TAC [STAR_LIST_APPEND_COMM2,connect_ys_comm2]);
 
val list2edges_APPEND = prove(
  ``!xs ys. list2edges (xs++ys) = list2edges xs UNION list2edges ys``,
  Induct \\ REWRITE_TAC [APPEND_NIL,UNION_EMPTY,list2edges_def]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2edges_def,APPEND,INSERT_UNION_EQ]);  

val uvs'_xs_comm = prove(
  ``!xs xs' ys ax px qs. uvs' (xs++xs') ys ax px qs bx = uvs' (xs'++xs) ys ax px qs bx``,
  REWRITE_TAC [uvs'_def,unseen_def,MAP_APPEND,unseen1_def,unreachables_def,FILTER_APPEND,FUN_EQ_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [uvs_xs_comm]
  \\ FULL_SIMP_TAC std_ss [reachables_def,FILTER_APPEND,MEM_APPEND,list2edges_APPEND]
  \\ FULL_SIMP_TAC std_ss [MEM_FILTER] \\ ONCE_REWRITE_TAC [UNION_COMM]
  \\ FULL_SIMP_TAC bool_ss [APPEND_ASSOC] \\ ONCE_REWRITE_TAC [uvs_ys_comm2]
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ ASM_REWRITE_TAC []);

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

val uvs_0_lemma1 = prove(
  ``!x. MEM x xs ==> (uvs xs ys ax px qs) s ==> ~(FST x = 0w)``,
  REWRITE_TAC [MEM_EQ_APPEND] \\ NTAC 2 STRIP_TAC
  \\ ASM_REWRITE_TAC [] \\ ONCE_REWRITE_TAC [uvs_xs_comm]
  \\ REWRITE_TAC [APPEND] 
  \\ `?a a1 a2 x' y. x = (a,a1,a2,x',y)` by 
    (Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [uvs_def,unseen1_def,unseen_def,MAP,STAR_LIST_def,link_block_def]
  \\ SIMP_TAC (bool_ss++sep2_ss) [cond_STAR]);

val uvs_0_lemma2 = prove(
  ``uvs xs ys ax px qs s ==> ~MEM 0w (MAP FST xs)``,
  SIMP_TAC bool_ss [MEM_MAP] \\ REPEAT STRIP_TAC
  \\ Cases_on `MEM y xs` \\ ASM_REWRITE_TAC [] \\ METIS_TAC [uvs_0_lemma1]);

val uvs_0 = prove(
  ``uvs xs ys ax px qs = uvs xs ys ax px qs * cond (~MEM 0w (MAP FST xs))``,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [cond_STAR] \\ METIS_TAC [uvs_0_lemma2]);

val reachables_0_lemma1 = prove(
  ``!xs x. ~MEM x (MAP FST xs) = !z. z IN (list2edges xs) ==> ~(FST z = x)``,
  Induct \\ ASM_SIMP_TAC bool_ss [MAP,MEM,list2edges_def,NOT_IN_EMPTY]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2edges_def,IN_INSERT] \\ METIS_TAC [FST]);

val reachables_0_lemma2 = prove(
  ``!x. (!z. z IN set ==> ~(FST z = x)) ==> !y. ~is_reachable set x y \/ (x = y)``,
  SIMP_TAC bool_ss [is_reachable_def] \\ REPEAT STRIP_TAC 
  \\ Cases_on `x = y` \\ ASM_REWRITE_TAC []
  \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [is_path_def] \\ METIS_TAC [FST]);

val reachables_0_lemma3 = prove(
  ``~MEM x (MAP FST xs) ==> !y. MEM y (MAP FST xs) ==> ~is_reachable (list2edges xs) x y``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC reachables_0_lemma1 \\ IMP_RES_TAC reachables_0_lemma2 
  \\ Q.PAT_ASSUM `!y. p \/ q` (STRIP_ASSUME_TAC o SPEC_ALL)  
  \\ FULL_SIMP_TAC bool_ss []);

val reachebles_EQ_NIL = prove(
  ``~MEM x (MAP FST xs) ==> (reachables x xs = [])``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC reachables_0_lemma3
  \\ Cases_on `reachables x xs` \\ ASM_REWRITE_TAC []
  \\ `MEM h (reachables x xs)` by METIS_TAC [MEM]
  \\ FULL_SIMP_TAC bool_ss [reachables_def,MEM_FILTER]
  \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ `?ys zs. xs = ys ++ (a,a1,a2,x',y)::zs` by METIS_TAC [MEM_EQ_APPEND]
  \\ FULL_SIMP_TAC bool_ss [FST,MEM,MEM_APPEND,MAP_APPEND,MAP,FST]
  \\ METIS_TAC []);

val unreachebles_EQ_ALL = prove(
  ``~MEM x (MAP FST xs) ==> (unreachables x xs = xs)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC reachebles_EQ_NIL 
  \\ ASM_REWRITE_TAC [unreachables_def,MEM] 
  \\ POP_ASSUM (fn th => ALL_TAC) \\ POP_ASSUM (fn th => ALL_TAC)
  \\ Induct_on `xs` \\ ASM_SIMP_TAC std_ss [FILTER]);

val uvs_cond_0 = prove(
  ``SEP_IMP 
      (uvs xs ys ax px qs * cond (a1x = 0w)) 
      (uvs (unreachables a1x xs) (reachables a1x xs ++ ys) ax px qs)``,
  CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [uvs_0]))
  \\ SIMP_TAC bool_ss [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC   
  \\ IMP_RES_TAC reachebles_EQ_NIL \\ IMP_RES_TAC unreachebles_EQ_ALL 
  \\ ASM_REWRITE_TAC [APPEND_NIL,SEP_IMP_REFL]);

val NOT_IN_domain_IMP = prove(
  ``~(x IN list2domain xs) ==> !z. z IN list2edges xs ==> ~(FST z = x)``,
  Induct_on `xs` \\ REWRITE_TAC [list2domain_def,list2edges_def,NOT_IN_EMPTY]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2domain_def,list2edges_def,IN_INSERT] \\ METIS_TAC [FST])

val uvs_cond_not_in_domain = prove(
  ``SEP_IMP 
      (uvs xs ys ax px qs * cond ~(a1x IN list2domain xs)) 
      (uvs (unreachables a1x xs) (reachables a1x xs ++ ys) ax px qs)``,
  SIMP_TAC bool_ss [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC 
  \\ IMP_RES_TAC NOT_IN_domain_IMP
  \\ FULL_SIMP_TAC bool_ss [GSYM reachables_0_lemma1]
  \\ IMP_RES_TAC reachebles_EQ_NIL \\ IMP_RES_TAC unreachebles_EQ_ALL 
  \\ ASM_REWRITE_TAC [APPEND_NIL,SEP_IMP_REFL]);

val start_case1'' = let
  val th = APP_FRAME `uvs xs ys ax px qs * cond (a1x = 0w)` start_case1'
  val th' = SPEC_ALL (MATCH_MP PART_WEAKEN_LEMMA th)
  val th = MATCH_MP th' uvs_cond_0
  val th = Q.INST [`a1x`|->`ax`] th
  val th = POST_MOVE_STAR `a*s*uv` `uv*a*s` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = PRE_MOVE_STAR `a*s*uv*c` `uv*a*s*c` th
  in th end;

val fst_case1'' = let
  val th = APP_FRAME `uvs xs ys ax px qs * cond (a1x = 0w)` fst_case1'
  val th' = SPEC_ALL (MATCH_MP PART_WEAKEN_LEMMA th)
  val th = MATCH_MP th' uvs_cond_0
  val th = POST_MOVE_STAR `a1*s*uv` `uv*a1*s` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = PRE_MOVE_STAR `a1*s*uv*c` `uv*a1*s*c` th
  in th end;

val ret1_case1'' = let
  val th = APP_FRAME `uvs xs ys ax px qs * cond (a2x = 0w)` ret1_case1'
  val th' = SPEC_ALL (MATCH_MP PART_WEAKEN_LEMMA th)
  val th = MATCH_MP th' (Q.INST [`a2x`|->`a1x`] uvs_cond_0)
  val th = POST_MOVE_STAR `a1*s*uv` `uv*a1*s` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th = PRE_MOVE_STAR `a1*s*uv*c` `uv*a1*s*c` th
  in Q.INST [`a1x`|->`a2x`] th end;

val SEP_SUB_def = Define `
  SEP_SUB P Q = \s. !u v. SPLIT u (s,v) /\ Q v ==> P u`;

val SEP_EXACT_def = Define `
  SEP_EXACT P = !s t. P s /\ P t ==> (s = t)`;

val SEP_EXACT_one = prove(
  ``!x. SEP_EXACT (one x)``,
  SIMP_TAC std_ss [SEP_EXACT_def,one_def]);

val SPLIT_EMPTY = prove(
  ``!s. SPLIT s (s,{}) /\ SPLIT s ({},s)``,
  REWRITE_TAC [SPLIT_def,DISJOINT_EMPTY,UNION_EMPTY]);

val SEP_EXACT_STAR = prove(
  ``!P Q. SEP_EXACT P /\ SEP_EXACT Q ==> SEP_EXACT (P * Q)``,
  SIMP_TAC std_ss [SEP_EXACT_def,STAR_def] \\ REPEAT STRIP_TAC 
  \\ `(u = u') /\ (v = v')` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [SPLIT_def]);

val SEP_EXACT_cond = prove(
  ``!c. SEP_EXACT (cond c)``,
  SIMP_TAC std_ss [SEP_EXACT_def,cond_def]);

val SEP_EXACT_M = prove(
  ``!a x. SEP_EXACT (M a x)``,
  REWRITE_TAC [M_def,byte_def] \\
  METIS_TAC [SEP_EXACT_STAR,SEP_EXACT_cond,SPLIT_EMPTY,SEP_EXACT_one]);
  
val SEP_EXACT_link_block = prove(
  ``SEP_EXACT (link_block (a1x,na1x,b,na2x,b',x,y))``,
  REWRITE_TAC [link_block_def]
  \\ METIS_TAC [SEP_EXACT_STAR,SEP_EXACT_cond,SPLIT_EMPTY,SEP_EXACT_M]);

val SEP_SUB_STAR = prove(
  ``!P Q. SEP_EXACT Q ==> ((SEP_SUB P Q) * Q = P /\ (Q * SEP_T))``,
  SIMP_TAC std_ss [FUN_EQ_THM,SEP_CONJ_def,SEP_EXACT_def,STAR_def,SEP_SUB_def,SEP_T_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def] THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `v` \\ Q.EXISTS_TAC `u`
  \\ ONCE_REWRITE_TAC [UNION_COMM,DISJOINT_SYM] \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);

val SUB_simp = MATCH_MP SEP_SUB_STAR SEP_EXACT_link_block

val some_link_block_def = Define `
  some_link_block a b = SEP_EXISTS a1 a2 b' x y. link_block (a,a1,b,a2,b',x,y)`;

val IN_list2domain = prove(
  ``a1x IN list2domain ys = MEM a1x (MAP FST ys)``,
  Induct_on `ys` \\ REWRITE_TAC [list2domain_def,NOT_IN_EMPTY,MAP,MEM]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2domain_def,IN_INSERT]);
    
val IN_list2domain_IMP = prove(
  ``a IN list2domain xs ==> ?a1 a2 x y ys' zs'. xs = ys' ++ (a,a1,a2,x,y)::zs'``,
  Induct_on `xs` \\ SIMP_TAC bool_ss [list2domain_def,NOT_IN_EMPTY] 
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2domain_def,IN_INSERT]
  \\ Cases_on `a = a'` \\ ASM_REWRITE_TAC [] THEN1 METIS_TAC [APPEND_NIL]
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `a ==> b` IMP_RES_TAC
  \\ ASM_REWRITE_TAC [] \\ METIS_TAC [APPEND]);

val SEP_IMP_SPLIT = prove(
  ``SEP_IMP P Q /\ SEP_IMP P' Q' ==> SEP_IMP (P * P') (Q * Q')``,
  SIMP_TAC std_ss [SEP_IMP_def,STAR_def] \\ METIS_TAC []);

val T_STAR_T = prove(
  ``SEP_T = SEP_T * SEP_T``,
  SIMP_TAC bool_ss [SEP_T_def,STAR_def,FUN_EQ_THM] \\ METIS_TAC [SPLIT_EMPTY]);

val get_stack_element = prove(
  ``!ax px. 
      a1x IN list2domain (stack2list ax px qs) ==>
      SEP_IMP (stack px qs) (some_link_block a1x T * SEP_T)``,
  Induct_on `qs` \\ REWRITE_TAC [stack_def,stack2list_def,list2domain_def,NOT_IN_EMPTY]
  \\ STRIP_TAC \\ `?a1 a2 x' y b. h = ((a1,a2,x',y),b)` by
    (Cases_on `h` \\ Cases_on `q` \\ Cases_on `r'` \\ Cases_on `r` \\ Cases_on `r''`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC [list2domain_def,IN_INSERT,stack2list_def]
  \\ Cases_on `b` \\ REWRITE_TAC [stack2list_def,list2domain_def,stack_def,IN_INSERT]
  \\ REPEAT STRIP_TAC  << [
    ASM_REWRITE_TAC [some_link_block_def] \\ MATCH_MP_TAC SEP_IMP_SPLIT 
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,SEP_T_def] \\ METIS_TAC [],
    CONV_TAC (RATOR_CONV (MOVE_STAR_CONV `x*y` `y*x`)) 
    \\ ONCE_REWRITE_TAC [prove(``SEP_T = SEP_T * SEP_T``,SIMP_TAC bool_ss [SEP_T_def,STAR_def,FUN_EQ_THM] \\ METIS_TAC [SPLIT_EMPTY])]
    \\ REWRITE_TAC [STAR_ASSOC] \\ MATCH_MP_TAC SEP_IMP_SPLIT   
    \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,SEP_T_def] \\ METIS_TAC [],    
    ASM_REWRITE_TAC [some_link_block_def] \\ MATCH_MP_TAC SEP_IMP_SPLIT 
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,SEP_T_def] \\ METIS_TAC [],
    CONV_TAC (RATOR_CONV (MOVE_STAR_CONV `x*y` `y*x`)) 
    \\ ONCE_REWRITE_TAC [T_STAR_T]
    \\ REWRITE_TAC [STAR_ASSOC] \\ MATCH_MP_TAC SEP_IMP_SPLIT   
    \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,SEP_T_def] \\ METIS_TAC []]);
    
val uvs_a1x_not_in_domain = prove(
  ``SEP_IMP
      (uvs xs ys ax px qs * cond (~(a1x IN list2domain xs) /\ a1x IN domain xs ys ax px qs))
      (some_link_block a1x T * SEP_T)``,
  SIMP_TAC bool_ss [SEP_IMP_MOVE_COND,domain_def,IN_UNION]
  \\ Cases_on `a1x IN list2domain xs` \\ ASM_REWRITE_TAC []
  \\ Cases_on `a1x IN list2domain ys` \\ ASM_REWRITE_TAC [] << [  
    IMP_RES_TAC IN_list2domain_IMP \\ ASM_REWRITE_TAC []
    \\ ONCE_REWRITE_TAC [uvs_ys_comm] \\ REWRITE_TAC [APPEND]
    \\ REWRITE_TAC [uvs_def,visited_def,STAR_LIST_def,MAP,visited1_def]
    \\ MOVE_STAR_TAC `u*(lb*st)*s*c` `lb*(u*st*s*c)`
    \\ MATCH_MP_TAC SEP_IMP_SPLIT
    \\ SIMP_TAC std_ss [SEP_T_def,SEP_IMP_def,some_link_block_def,SEP_EXISTS] \\ METIS_TAC [], 
    REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [T_STAR_T] \\ REWRITE_TAC [uvs_def,STAR_ASSOC]
    \\ MOVE_STAR_TAC `u*v*s*cc` `s*(v*u*cc)` \\ MATCH_MP_TAC SEP_IMP_SPLIT
    \\ IMP_RES_TAC get_stack_element \\ ASM_REWRITE_TAC []
    \\ SIMP_TAC bool_ss [SEP_IMP_def,SEP_T_def]]);

val SEP_CONJ_ABSORB = prove(
  ``!P Q. SEP_IMP P Q ==> (P /\ Q = P)``,
  SIMP_TAC std_ss [SEP_IMP_def,FUN_EQ_THM,SEP_CONJ_def] \\ METIS_TAC []);

val start_case2'' = let
  val th = SIMP_RULE (bool_ss++sep_ss) [] (Q.INST [`b'`|->`b`] start_case2')
  val th = APP_FRAME `SEP_SUB P (link_block (ax,a1x,T,a2x,b,x,y))` th
  val th = MOVE_STAR_RULE `a1*s*t*a2*bl*sub` `a1*s*t*a2*(sub*bl)` th
  val th = RW [SUB_simp] th
  val th = APP_WEAKEN th
    `R30 a ax * ~S * ~R t * ~R a1 * (P /\ some_link_block ax T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `y` (PRE_CONV_RULE (UNBETA_CONV ``y:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `x` (PRE_CONV_RULE (UNBETA_CONV ``x:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `b` (PRE_CONV_RULE (UNBETA_CONV ``b:bool``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `a1x` (PRE_CONV_RULE (UNBETA_CONV ``a1x:word30``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `a2x` (PRE_CONV_RULE (UNBETA_CONV ``a2x:word30``) th))
  val th = SIMP_RULE std_ss [] th
  val th = APP_STRENGTHEN th
    `R30 a ax * ~S * ~R t * ~R a1 * (P /\ some_link_block ax T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th' = MATCH_MP SEP_CONJ_ABSORB uvs_a1x_not_in_domain
  val th = Q.INST [`P`|->`uvs xs ys ax px qs * cond (~(ax IN list2domain xs) /\ ax IN domain xs ys ax px qs)`] th
  val th = RW [th'] th
  val th = PRE_MOVE_STAR `a1*s*t*a2*(u*c)` `u*a1*s*t*a2*c` th
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond c``)] th
  val th = POST_MOVE_STAR `a1*s*t*a2*(u*(c*c'))` `a1*s*t*a2*(u*(c))*c'` th
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [SEP_IMP_def,emp_def,cond_def])) (Q.SPEC `emp` th)
  val th = RW [emp_STAR] (MP th TRUTH)
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = MATCH_MP th (Q.INST [`a1x`|->`ax`] uvs_cond_not_in_domain)
  val th = POST_MOVE_STAR `a1*s*t*a2*u` `u*a1*s*t*a2` (SIMP_RULE (bool_ss++sep2_ss) [] th)
  in th end;  

val fst_case2'' = let
  val th = SIMP_RULE (bool_ss++sep_ss) [] (Q.INST [`b`|->`T`,`b'`|->`b`] fst_case2')
  val th = APP_FRAME `SEP_SUB P (link_block (a1x,na1x,T,na2x,b,x,y))` th
  val th = MOVE_STAR_RULE `a1*s*t*a2*bl*sub` `a1*s*t*a2*(sub*bl)` th
  val th = RW [SUB_simp] th
  val th = APP_WEAKEN th
    `R30 a1 a1x * ~S * ~R t * ~R a2 * (P /\ some_link_block a1x T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `y` (PRE_CONV_RULE (UNBETA_CONV ``y:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `x` (PRE_CONV_RULE (UNBETA_CONV ``x:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `b` (PRE_CONV_RULE (UNBETA_CONV ``b:bool``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na1x` (PRE_CONV_RULE (UNBETA_CONV ``na1x:word30``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na2x` (PRE_CONV_RULE (UNBETA_CONV ``na2x:word30``) th))
  val th = SIMP_RULE std_ss [] th
  val th = APP_STRENGTHEN th
    `R30 a1 a1x * ~S * ~R t * ~R a2 * (P /\ some_link_block a1x T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th' = MATCH_MP SEP_CONJ_ABSORB uvs_a1x_not_in_domain
  val th = Q.INST [`P`|->`uvs xs ys ax px qs * cond (~(a1x IN list2domain xs) /\ a1x IN domain xs ys ax px qs)`] th
  val th = RW [th'] th
  val th = PRE_MOVE_STAR `a1*s*t*a2*(u*c)` `u*a1*s*t*a2*c` th
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond c``)] th
  val th = POST_MOVE_STAR `a1*s*t*a2*(u*(c*c'))` `a1*s*t*a2*(u*(c))*c'` th
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [SEP_IMP_def,emp_def,cond_def])) (Q.SPEC `emp` th)
  val th = RW [emp_STAR] (MP th TRUTH)
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = MATCH_MP th uvs_cond_not_in_domain
  val th = POST_MOVE_STAR `a1*s*t*a2*u` `u*a1*s*t*a2` (SIMP_RULE (bool_ss++sep2_ss) [] th)
  in th end;  

val ret1_case2'' = let
  val th = SIMP_RULE (bool_ss++sep_ss) [] (Q.INST [`b`|->`T`,`b'`|->`b`] ret1_case2')
  val th = APP_FRAME `SEP_SUB P (link_block (a2x,na1x,T,na2x,b,x,y))` th
  val th = MOVE_STAR_RULE `a1*s*t*a2*bl*sub` `a1*s*t*a2*(sub*bl)` th
  val th = RW [SUB_simp] th
  val th = APP_WEAKEN th
    `R30 a2 a2x * ~S * ~R t * ~R a1 * (P /\ some_link_block a2x T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `y` (PRE_CONV_RULE (UNBETA_CONV ``y:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `x` (PRE_CONV_RULE (UNBETA_CONV ``x:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `b` (PRE_CONV_RULE (UNBETA_CONV ``b:bool``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na1x` (PRE_CONV_RULE (UNBETA_CONV ``na1x:word30``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na2x` (PRE_CONV_RULE (UNBETA_CONV ``na2x:word30``) th))
  val th = SIMP_RULE std_ss [] th
  val th = APP_STRENGTHEN th
    `R30 a2 a2x * ~S * ~R t * ~R a1 * (P /\ some_link_block a2x T * SEP_T)`
    (SIMP_TAC (bool_ss++sep2_ss) [some_link_block_def] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th' = MATCH_MP SEP_CONJ_ABSORB (Q.INST [`a1x`|->`a2x`] uvs_a1x_not_in_domain)
  val th = Q.INST [`P`|->`uvs xs ys ax px qs * cond (~(a2x IN list2domain xs) /\ a2x IN domain xs ys ax px qs)`] th
  val th = RW [th'] th
  val th = PRE_MOVE_STAR `a1*s*t*a2*(u*c)` `u*a1*s*t*a2*c` th
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond c``)] th
  val th = POST_MOVE_STAR `a1*s*t*a2*(u*(c*c'))` `a1*s*t*a2*(u*(c))*c'` th
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [SEP_IMP_def,emp_def,cond_def])) (Q.SPEC `emp` th)
  val th = RW [emp_STAR] (MP th TRUTH)
  val th = MATCH_MP PART_WEAKEN_LEMMA th
  val th = MATCH_MP th (Q.INST [`a1x`|->`a2x`] uvs_cond_not_in_domain)
  val th = POST_MOVE_STAR `a1*s*t*a2*u` `u*a1*s*t*a2` (SIMP_RULE (bool_ss++sep2_ss) [] th)
  in th end;  

val fst_case3''_LEMMA = prove(
  ``!P. (!xs ys. P (xs++ys) = P (ys++xs)) ==>
        (!xs. P (z::xs)) ==> (!xs. MEM z xs ==> P xs)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND] \\ METIS_TAC [APPEND]);

val start_case3'' = let
  val th = APP_FRAME `unseen xs * visited ys * stack px zs * connect ((ax,a1x,a2x,x,y)::xs) ys ax px zs` start_case3'
  val th = SPEC_STRENGTHEN th `uvs ((ax,a1x,a2x,x,y)::xs) ys ax px zs * R30 a ax * ~R t * ~R a1 * ~S` 
  val th = SEP_IMP_SIMP star_ss [uvs_def,MAP,STAR_LIST_def,unseen_def,unseen1_def] th
  val th = SPEC_WEAKEN1 th `uvs ((ax,a1x,a2x,x,y)::xs) ys ax px zs * R30 a ax * ~R t * R30 a1 a1x  * ~S` 
  val th = SEP_IMP_SIMP star_ss [uvs_def,MAP,STAR_LIST_def,unseen_def,unseen1_def,R30_def,GSYM addr32f_INTRO] th
  in th end;
  
val fst_case3'' = let
  val th = APP_FRAME `unseen xs * visited ys` fst_case3'
  val th = APP_FRAME `connect ((a1x,na1x,na2x,x,y)::xs) ys a1x ax (((ppx,ax2,p_x,p_y),F)::qs)` th
  val th = Q.INST [`b`|->`F`,`ax1`|->`a1x`,`ax2`|->`a2x`,`b'`|->`F`] th
  val th = Q.SPEC
    `uvs ((a1x,na1x,na2x,x,y)::xs) ys a1x ax (((ppx,a2x,p_x,p_y),F)::qs) *
     R30 p ax * R30 a a1x * R30 a1 na1x * ~R t * ~R a2 * ~S` (MATCH_MP WEAKEN_LEMMA th)
  val c = SIMP_CONV (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,unseen_def,MAP,unseen1_def,STAR_LIST_def,MEM] THENC SIMP_CONV (bool_ss++star_ss) [SEP_IMP_REFL,GSYM addr32f_INTRO,GSYM R30_def,uvs_def,unseen_def,MAP,unseen1_def,STAR_LIST_def]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV c)) th
  val th = MP th TRUTH
  val th = Q.INST [`p_x`|->`x`,`p_y`|->`y`,`x`|->`nx`,`y`|->`ny`] th
  val th' = Q.SPEC
    `uvs ((a1x,na1x,na2x,nx,ny)::xs) ((ax,a1x,a2x,x,y)::ys) ax ppx qs *
     R30 p ppx * R30 a ax * R30 a1 a1x * ~R t * ~R a2 * ~S` (MATCH_MP STRENGTHEN_LEMMA th)
  val c = SIMP_CONV (bool_ss++star_ss) [uvs_def,SEP_cond_CLAUSES,emp_STAR,unseen_def,MAP,unseen1_def,STAR_LIST_def,visited_def,visited1_def,connect_POP,SEP_IMP_REFL]
  val th' = CONV_RULE (RATOR_CONV (RAND_CONV c)) th'
  val th = MP th' TRUTH
  val th' = CONV_RULE (UNBETA_CONV ``(a1x:word30,na1x:word30,na2x:word30,nx:word32,ny:word32)::xs``) th
  val P = (fst o dest_comb o concl) th'
  val th' = SIMP_RULE std_ss [] (ISPEC P fst_case3''_LEMMA)
  val th' = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV o RAND_CONV) (ONCE_REWRITE_CONV [uvs_xs_comm]) THENC REWRITE_CONV []) th'
  val th' = Q.INST [`z`|->`(a1x,na1x,na2x,nx,ny)`] th'    
  val th = SPEC_ALL (MATCH_MP th' (Q.GEN `xs` th))
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (MEM (a1x:word30,na1x:word30,na2x:word30,nx:word32,ny:word32) xs)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th' = SPEC_ALL assumption
  val th' = Q.INST [`zs`|->`((pa1x:word30,pa2x:word30,p_x:word32,p_y:word32),F)::zs`] th'
  val th' = SIMP_RULE (bool_ss++sep_ss) [NOT_CONS_NIL,has_head_def,HD,PAIR_EQ,ARM_PROG_FALSE_POST,TL] th'
  val th' = RW [ARM_PROG_FALSE_POST] (RW1 [INSERT_COMM] th')
  val th' = APP_WEAKEN th' 
    `uvs' xs ((px,ax,pa2x,p_x,p_y)::ys) px pa1x zs ax *
     R30 p pa1x * R30 a px * ~R a1 * ~R t * R30 a2 pa2x * ~S`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ METIS_TAC [])

  val th' = RW [ARM_PROG_THM,ARM_GPROG_EMPTY_CODE,ARM_GPROG_FALSE_POST] th'
  val th' = Q.SPEC `pcADD 1073741822w` (MATCH_MP ARM_GPROG_SHIFT th')
  val lemma = prove(``I:'a->'a o g = g``,SIMP_TAC std_ss [FUN_EQ_THM])
  val th' = SIMP_RULE (bool_ss++setINC_ss++pcINC_ss) [GSYM setADD_def,setADD_CLAUSES,EVAL ``12 + 1073741822``,lemma] th'
  val th = RW [ARM_PROG_THM] th
  val th = RW1 [prove(``{x;y} = {x} UNION {y}``,SIMP_TAC std_ss [INSERT_UNION_EQ,UNION_EMPTY])] th  
  val lemma = RW [UNION_EMPTY] (Q.SPECL [`y`,`{}`,`x`,`c`,`c'`,`z'`,`z`] ARM_GPROG_COMPOSE  )
  val lemma = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] lemma)
  val th' = MATCH_MP lemma th'  
  val th = MATCH_MP th' th 
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY,GSYM ARM_PROG_THM] th

  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `ny` (PRE_CONV_RULE (UNBETA_CONV ``ny:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `nx` (PRE_CONV_RULE (UNBETA_CONV ``nx:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na2x` (PRE_CONV_RULE (UNBETA_CONV ``na2x:word30``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na1x` (PRE_CONV_RULE (UNBETA_CONV ``na1x:word30``) th))
  val th = SIMP_RULE std_ss [] th
  val th = APP_STRENGTHEN th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax ppx qs * R30 p ppx * R30 a ax *
     R30 a1 a1x * ~R t * ~R a2 * ~S * cond (a1x IN list2domain xs)`
   (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `(P * Q) s` (fn th => ALL_TAC)  
    \\ Induct_on `xs` \\ REWRITE_TAC [list2domain_def,NOT_IN_EMPTY]
    \\ STRIP_TAC \\ `?a a1 a2 x y. h = (a,a1,a2,x,y)` by (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r` \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
    \\ ASM_REWRITE_TAC [list2domain_def,IN_INSERT,MEM,PAIR_EQ] \\ METIS_TAC [])
  in th end;

val ret1_case3'' = let
  val th = APP_FRAME `unseen xs * visited ys` ret1_case3'
  val th = APP_FRAME `connect ((a2x,na1x,na2x,x,y)::xs) ys a2x ax (((ax1,ppx,p_x,p_y),T)::qs)` th
  val th = Q.INST [`b`|->`F`,`ax1`|->`a1x`,`ax2`|->`a2x`,`b'`|->`F`] th
  val th = Q.SPEC
    `uvs ((a2x,na1x,na2x,x,y)::xs) ys a2x ax (((a1x,ppx,p_x,p_y),T)::qs) *
     R30 p ax * R30 a a2x * R30 a1 na1x * ~R t * ~R a2 * ~S` (MATCH_MP WEAKEN_LEMMA th)
  val c = SIMP_CONV (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND,unseen_def,MAP,unseen1_def,STAR_LIST_def,MEM] THENC SIMP_CONV (bool_ss++star_ss) [SEP_IMP_REFL,GSYM addr32f_INTRO,GSYM R30_def,uvs_def,unseen_def,MAP,unseen1_def,STAR_LIST_def]
  val th = CONV_RULE (RATOR_CONV (RAND_CONV c)) th
  val th = MP th TRUTH
  val th = Q.INST [`p_x`|->`x`,`p_y`|->`y`,`x`|->`nx`,`y`|->`ny`] th
  val th' = Q.SPEC
    `uvs ((a2x,na1x,na2x,nx,ny)::xs) ((ax,a1x,a2x,x,y)::ys) ax ppx qs *
     R30 p ppx * R30 a ax * R30 a2 a2x * ~R t * ~R a1 * ~S` (MATCH_MP STRENGTHEN_LEMMA th)
  val c = SIMP_CONV (bool_ss++star_ss) [uvs_def,SEP_cond_CLAUSES,emp_STAR,unseen_def,MAP,unseen1_def,STAR_LIST_def,visited_def,visited1_def,GSYM connect_POP2,SEP_IMP_REFL]
  val th' = CONV_RULE (RATOR_CONV (RAND_CONV c)) th'
  val th = MP th' TRUTH
  val th' = CONV_RULE (UNBETA_CONV ``(a2x:word30,na1x:word30,na2x:word30,nx:word32,ny:word32)::xs``) th
  val P = (fst o dest_comb o concl) th'
  val th' = SIMP_RULE std_ss [] (ISPEC P fst_case3''_LEMMA)
  val th' = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV o RAND_CONV) (ONCE_REWRITE_CONV [uvs_xs_comm]) THENC REWRITE_CONV []) th'
  val th' = Q.INST [`z`|->`(a2x,na1x,na2x,nx,ny)`] th'    
  val th = SPEC_ALL (MATCH_MP th' (Q.GEN `xs` th))
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (MEM (a2x:word30,na1x:word30,na2x:word30,nx:word32,ny:word32) xs)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th' = SPEC_ALL assumption
  val th' = Q.INST [`zs`|->`((pa1x:word30,pa2x:word30,p_x:word32,p_y:word32),T)::zs`] th'
  val th' = SIMP_RULE (bool_ss++sep_ss) [NOT_CONS_NIL,has_head_def,HD,PAIR_EQ,ARM_PROG_FALSE_POST,TL] th'
  val th' = RW [ARM_PROG_FALSE_POST] (RW1 [INSERT_COMM] th')
  val th' = APP_WEAKEN th' 
    `uvs' xs ((px,pa1x,ax,p_x,p_y)::ys) px pa2x zs ax *
     R30 p pa2x * R30 a px * ~R a1 * ~R t * ~R a2 * ~S`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ METIS_TAC []) 

  val th' = RW [ARM_PROG_THM,ARM_GPROG_EMPTY_CODE,ARM_GPROG_FALSE_POST] th'
  val th' = Q.SPEC `pcADD 1073741810w` (MATCH_MP ARM_GPROG_SHIFT th')
  val lemma = prove(``I:'a->'a o g = g``,SIMP_TAC std_ss [FUN_EQ_THM])
  val th' = SIMP_RULE (bool_ss++setINC_ss++pcINC_ss) [GSYM setADD_def,setADD_CLAUSES,EVAL ``11 + 1073741810``,lemma] th'
  val th = RW [ARM_PROG_THM] th
  val th = RW1 [prove(``{x;y} = {x} UNION {y}``,SIMP_TAC std_ss [INSERT_UNION_EQ,UNION_EMPTY])] th  
  val lemma = RW [UNION_EMPTY] (Q.SPECL [`y`,`{}`,`x`,`c`,`c'`,`z'`,`z`] ARM_GPROG_COMPOSE  )
  val lemma = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] lemma)
  val th' = MATCH_MP lemma th'  
  val th = MATCH_MP th' th 
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY,GSYM ARM_PROG_THM] th

  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `ny` (PRE_CONV_RULE (UNBETA_CONV ``ny:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `nx` (PRE_CONV_RULE (UNBETA_CONV ``nx:word32``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na2x` (PRE_CONV_RULE (UNBETA_CONV ``na2x:word30``) th))
  val th = RW [ARM_PROG_EXISTS_PRE] (Q.GEN `na1x` (PRE_CONV_RULE (UNBETA_CONV ``na1x:word30``) th))
  val th = SIMP_RULE std_ss [] th
  val th = APP_STRENGTHEN th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax ppx qs * R30 p ppx * R30 a ax *
     R30 a2 a2x * ~R t * ~R a1 * ~S * cond (a2x IN list2domain xs)`
   (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `(P * Q) s` (fn th => ALL_TAC)  
    \\ Induct_on `xs` \\ REWRITE_TAC [list2domain_def,NOT_IN_EMPTY]
    \\ STRIP_TAC \\ `?a a1 a2 x y. h = (a,a1,a2,x,y)` by (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r` \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
    \\ ASM_REWRITE_TAC [list2domain_def,IN_INSERT,MEM,PAIR_EQ] \\ METIS_TAC [])
  in th end;

val connect_SHIFT = prove(
  ``connect ((bx,a1x,a2x,x,y)::xs) ys ax px qs = connect xs ((bx,a1x,a2x,x,y)::ys) ax px qs``,
  REWRITE_TAC [connect_def,range_def,domain_def,list2range_def,list2domain_def]
  \\ REWRITE_TAC [SUBSET_DEF,IN_INSERT,IN_UNION,NOT_IN_EMPTY]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``!f x y. (x = y) ==> (f x = f y)``)
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\  METIS_TAC []);

val fst_init'' = let
  val th = APP_FRAME `unseen xs * visited ys * stack px qs * connect ((ax,a1x,a2x,x,y)::xs) ys ax px qs` fst_init'
  val th = Q.SPEC `uvs ((ax,a1x,a2x,x,y)::xs) ys ax px qs * R30 a1 a1x * R30 a ax * ~S * ~R t` (MATCH_MP STRENGTHEN_LEMMA th)
  val c = SIMP_CONV (bool_ss++star_ss) [uvs_def,unseen_def,MAP,STAR_LIST_def,unseen1_def,SEP_IMP_REFL]
  val th = CONV_RULE (RATOR_CONV c) th
  val th = RW [connect_SHIFT] th
  val th = Q.SPEC `uvs xs ((ax,a1x,a2x,x,y)::ys) ax px qs * R30 a1 a1x * R30 a ax * ~S * ~R t` (MATCH_MP WEAKEN1_LEMMA th)
  val c = SIMP_CONV (bool_ss++star_ss) [uvs_def,visited_def,MAP,STAR_LIST_def,visited1_def,SEP_IMP_REFL]
  val th = CONV_RULE (RATOR_CONV c) th
  val th = MP th TRUTH
  in th end;

val snd'' = let
  val th = APP_FRAME `unseen xs * visited ys * stack px qs * connect xs ((ax,a1x,a2x,x,y)::ys) ax px qs` snd'
  val th = APP_STRENGTHEN th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax px qs * R30 a ax * ~S * ~R a2`
    (SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL,uvs_def,visited_def,visited1_def,MAP,STAR_LIST_def])
  val th = APP_WEAKEN1 th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax px qs * R30 a ax * ~S * R30 a2 a2x`
    (SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL,uvs_def,visited_def,visited1_def,MAP,STAR_LIST_def])
  in th end;
  
val connect_T = prove(
  ``connect xs ys ax px (((a1x,ppx,x,y),T)::zs) =
    connect xs ((px,a1x,ax,x,y)::ys) px ppx zs``,
  REWRITE_TAC [connect_def,range_def,list2range_def,stack2list_def,domain_def,list2domain_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) /\ (a = b) ==> (g x a = g y b)``)
  \\ SIMP_TAC bool_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []);

val connect_F = prove(
  ``connect xs ys ax px (((ppx,a2x,x,y),F)::zs) =
    connect xs ((px,ax,a2x,x,y)::ys) px ppx zs``,
  REWRITE_TAC [connect_def,range_def,list2range_def,stack2list_def,domain_def,list2domain_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) /\ (a = b) ==> (g x a = g y b)``)
  \\ SIMP_TAC bool_ss [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []);

val ret2_case1'' = let
  val th = ret2_case1'
  val th = APP_FRAME `uvs xs ys ax px zs` th
  val lemma = prove(
    ``cond (px = 0w) * uvs xs ys ax px zs = uvs xs ys ax px zs * cond (zs = [])``,
    Cases_on `px = 0w` 
    \\ Cases_on `zs` \\ ASM_SIMP_TAC (bool_ss++sep_ss) [uvs_def,stack_def,NOT_NIL_CONS]
    \\ Cases_on `h` \\ Cases_on `q` \\ Cases_on `r'` \\ Cases_on `r''` \\ Cases_on `r`
    \\ ASM_SIMP_TAC (bool_ss++sep_ss) [uvs_def,stack_def,link_block_def])
  val th = RW [STAR_ASSOC] (RW [lemma] (RW [GSYM STAR_ASSOC] th))
  in th end;

val ret2_case2'' = let
  val th = APP_FRAME `stack a2x zs` ret2_case2'
  val th = MATCH_MP STRENGTHEN_LEMMA th
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * ~S * stack px (((a1x,a2x,x,y),T)::zs)` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [stack_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  val th = Q.INST [`a2x`|->`ppx`] th
  val th = APP_FRAME `unseen xs * visited ys * connect xs ((px,a1x,ax,x,y)::ys) px ppx zs` th
  val th = MATCH_MP WEAKEN_LEMMA th
  val th = Q.SPEC `R30 a px * R30 p ppx * ~R a2 * ~R t * ~S * uvs xs ((px,a1x,ax,x,y)::ys) px ppx zs` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [uvs_def,visited_def,visited1_def,MAP,STAR_LIST_def,SEP_IMP_REFL])) th  
  val th = MP th TRUTH
  val th = MATCH_MP STRENGTHEN_LEMMA th
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * ~S * uvs xs ys ax px (((a1x,ppx,x,y),T)::zs)` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [uvs_def])) th
  val th = RW [connect_T,SEP_IMP_REFL] th
  in th end;

val ret2_case3'' = let
  val th = APP_FRAME `stack a1x zs` ret2_case3'
  val th = MATCH_MP STRENGTHEN_LEMMA th
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * ~S * stack px (((a1x,a2x,x,y),F)::zs)` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [stack_def,SEP_IMP_REFL])) th
  val th = MP th TRUTH
  val th = Q.INST [`a1x`|->`ppx`] th
  val th = APP_FRAME `unseen xs * visited ys * connect xs ((px,ax,a2x,x,y)::ys) px ppx zs` th
  val th = MATCH_MP WEAKEN_LEMMA th
  val th = Q.SPEC `R30 a px * R30 p ppx * R30 a2 a2x * ~R t * ~S * uvs xs ((px,ax,a2x,x,y)::ys) px ppx zs` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [uvs_def,visited_def,visited1_def,MAP,STAR_LIST_def,SEP_IMP_REFL])) th  
  val th = MP th TRUTH
  val th = MATCH_MP STRENGTHEN_LEMMA th
  val th = Q.SPEC `R30 a ax * R30 p px * ~R a2 * ~R t * ~S * uvs xs ys ax px (((ppx,a2x,x,y),F)::zs)` th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (bool_ss++star_ss) [uvs_def])) th
  val th = RW [connect_F,SEP_IMP_REFL] th
  in th end;

(* fix together these three *)

val domain_ABSORB = prove(
  ``x IN list2domain xs \/ x IN domain xs ys ax px zs = x IN domain xs ys ax px zs``,
  REWRITE_TAC [domain_def,IN_UNION] \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []);

val fst123 = let
  val th1 = SIMP_RULE (bool_ss++sep2_ss) [] (APP_FRAME `~R t * ~R a2` fst_case1'')
  val th2 = fst_case2''
  val th = APP_MERGE th1 th2
  val th = APP_FRAME `R30 p ppx * R30 a ax` th
  val th = PRE_MOVE_STAR `u*a1*s*t*a2*cc*(p*a)` `u*p*a*a1*t*a2*s*cc` th
  val th = Q.INST [`ys`|->`((ax,a1x,a2x,x,y)::ys)`,`px`|->`ppx`] th
  val th3 = fst_case3''
  val th = APP_MERGE th th3  
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val th = RW [METIS_PROVE [] ``(b \/ (~a /\ c)) \/ a = b \/ (a \/ c):bool``] th
  val th = RW [domain_ABSORB] th
  val th = APP_STRENGTHEN th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax ppx qs * R30 p ppx * R30 a ax *
     R30 a1 a1x * ~R t * ~R a2 * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [uvs_def,connect_def]
    \\ SIMP_TAC bool_ss [SEP_IMP_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ Cases_on `a1x = 0w` 
    \\ FULL_SIMP_TAC bool_ss [domain_def,SUBSET_DEF,IN_UNION,range_def,
         list2range_def,IN_INSERT,list2domain_def,NOT_IN_EMPTY]
    \\ METIS_TAC [])
  val contract = prove(``ARM_PROG P cs C SEP_F ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C Q Z``,METIS_TAC [ARM_PROG_EXTRACT_POST])
  val th = MATCH_MP contract th
  val th = SIMP_RULE std_ss [pcINC_def,wLENGTH_def,LENGTH] th
  val th = RW [APPEND] (ONCE_REWRITE_RULE [uvs_ys_comm] th)
  val th' = Q.INST [`ys`|->`ys ++ reachables a1x xs`,`xs`|->`unreachables a1x xs`,`px`|->`ppx`] snd''
  val th' = APP_FRAME `R30 a1 a1x * ~R t * R30 p ppx` th'
  val th = ARRANGE_COMPOSE th th'
  val th = RW [uvs'_def,APPEND] th
  val th = POST1_MOVE_STAR `u*a*s*a2*(a1*t*p)` `u*p*a*t*a2*s*a1` th
  val th = RW [GSYM R30_def] (HIDE_POST1 (RW [R30_def] th))
  val th = POST1_MOVE_STAR `u*p*a*t*a2*s*a1` `u*p*a*a1*t*a2*s` th
  val contract_better = prove(``ARM_PROG P cs C Q' ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C (Q' \/ Q) Z``,METIS_TAC [ARM_PROG_EXTRACT_POST,ARM_PROG_MERGE_POST])
  val th = MATCH_MP contract_better th
  val lemma = prove(``1073741836w = 12w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = SIMP_RULE (std_ss++sep_ss) [pcINC_def,wLENGTH_def,LENGTH,lemma] th
  in th end;

val fst_init123 = let
  val th = APP_FRAME `R30 p ppx * ~R a2` (Q.INST [`px`|->`ppx`] fst_init'')
  val th = ARRANGE_COMPOSE th fst123
  val th = PRE_MOVE_STAR `u*a1*a*s*t*(p*a2)` `u*p*a*a1*a2*t*s` th    
  in th end;

val ret1_123 = let
  val th1 = SIMP_RULE (bool_ss++sep2_ss) [] (APP_FRAME `~R t * ~R a1` ret1_case1'')
  val th2 = ret1_case2''
  val th = APP_MERGE th1 th2
  val th = APP_FRAME `R30 p ppx * R30 a ax` th
  val th = PRE_MOVE_STAR `u*a1*s*t*a2*cc*(p*a)` `u*p*a*a1*t*a2*s*cc` th
  val th = Q.INST [`ys`|->`((ax,a1x,a2x,x,y)::ys)`,`px`|->`ppx`] th
  val th3 = ret1_case3''
  val th = APP_MERGE th th3  
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val th = RW [METIS_PROVE [] ``(b \/ (~a /\ c)) \/ a = b \/ (a \/ c):bool``] th
  val th = RW [domain_ABSORB] th
  val th = APP_STRENGTHEN th
    `uvs xs ((ax,a1x,a2x,x,y)::ys) ax ppx qs * R30 p ppx * R30 a ax *
     R30 a2 a2x * ~R t * ~R a1 * ~S`
   (SIMP_TAC (bool_ss++sep2_ss) [uvs_def,connect_def]
    \\ SIMP_TAC bool_ss [SEP_IMP_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ Cases_on `a1x = 0w` 
    \\ FULL_SIMP_TAC bool_ss [domain_def,SUBSET_DEF,IN_UNION,range_def,
         list2range_def,IN_INSERT,list2domain_def,NOT_IN_EMPTY]
    \\ METIS_TAC [])
  val contract = prove(``ARM_PROG P cs C SEP_F ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C Q Z``,METIS_TAC [ARM_PROG_EXTRACT_POST])
  val th = MATCH_MP contract th
  val th = SIMP_RULE std_ss [pcINC_def,wLENGTH_def,LENGTH] th
  val th = RW [APPEND] (ONCE_REWRITE_RULE [uvs_ys_comm] th)
  val th = RW [R30_def] th
  val th = HIDE_POST1 (POST1_MOVE_STAR `u*a2*s*t*a1*(p*a)` `u*p*a*a1*t*s*a2` th)
  val th = POST_MOVE_STAR `u*p*a*a1*t*a2*s` `u*p*a*a1*t*s*a2` th
  val th = RW [GSYM R30_def] th
  val th = RW [uvs'_def,APPEND] th
  val contract_better = prove(``ARM_PROG P cs C Q' ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C (Q' \/ Q) Z``,METIS_TAC [ARM_PROG_EXTRACT_POST,ARM_PROG_MERGE_POST])
  val th = MATCH_MP contract_better th
  val lemma = prove(``1073741835w = 11w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = SIMP_RULE (std_ss++sep_ss) [pcINC_def,wLENGTH_def,LENGTH,lemma] th
  in th end;    

val SUBSET_is_path = prove(
  ``!x p y set set'. set SUBSET set' /\ is_path x p y set ==> is_path x p y set'``,
  Induct_on `p` \\ FULL_SIMP_TAC bool_ss [is_path_def,SUBSET_DEF] \\ METIS_TAC []);

val list2edges_SUBSET = prove(
  ``(!x. MEM x xs ==> MEM x ys) ==> (list2edges xs SUBSET list2edges ys)``,
  Induct_on `xs` \\ REWRITE_TAC [list2edges_def,EMPTY_SUBSET]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [list2edges_def,MEM,SUBSET_DEF,IN_INSERT] \\ REPEAT STRIP_TAC    
  \\ `MEM (a,a1,a2,x',y) ys /\ !x. MEM x xs ==> MEM x ys` by METIS_TAC []
  \\ `?zs zs'. ys = zs ++ (a,a1,a2,x',y)::zs'` by ASM_REWRITE_TAC [GSYM MEM_EQ_APPEND]
  THEN1 ASM_REWRITE_TAC [list2edges_APPEND,list2edges_def,IN_UNION,IN_INSERT]
  THEN1 ASM_REWRITE_TAC [list2edges_APPEND,list2edges_def,IN_UNION,IN_INSERT]
  \\ METIS_TAC []);

val IN_list2edges = prove(
  ``!a b xs. (a,b) IN list2edges xs = ?c x y. MEM (a,b,c,x,y) xs \/ MEM (a,c,b,x,y) xs``,
  Induct_on `xs` \\ REWRITE_TAC [list2edges_def,NOT_IN_EMPTY,MEM]
  \\ STRIP_TAC \\ `?a a1 a2 x' y. h = (a,a1,a2,x',y)` by 
    (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
     \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [list2edges_def,MEM,SUBSET_DEF,IN_INSERT] \\ REPEAT STRIP_TAC    
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ METIS_TAC []);    

val is_path_APPEND = prove(
  ``!x y xs zs z set. is_path x (xs ++ y::ys) z set = is_path x xs y set /\ is_path y ys z set``,
  Induct_on `xs` \\ ASM_SIMP_TAC bool_ss [is_path_def,APPEND_NIL,APPEND,CONJ_ASSOC]);
    
val is_reachable_TRANS = prove(
  ``is_reachable set a1 a2 ==> is_reachable set a2 a3 ==> is_reachable set a1 a3``,
  REWRITE_TAC [is_reachable_def] \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p ++ a2::p'`
  \\ ASM_REWRITE_TAC [is_path_APPEND]);

val is_reachable'_unreachables = prove(
  ``~is_reachable' (list2edges xs) a z ==>
    is_reachable' (list2edges xs) b z ==>
    is_reachable' (list2edges (unreachables' a xs)) b z``,
  SIMP_TAC bool_ss [is_reachable'_def] \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r`
  \\ ASM_SIMP_TAC bool_ss [unreachables'_def,reachables'_def,MEM_FILTER,is_reachable'_def]  
  \\ ONCE_REWRITE_TAC [is_reachable_def]
  \\ `(r = z) \/ ?p. is_path r p (z) (list2edges xs)` by METIS_TAC [is_reachable_def] 
  \\ ASM_REWRITE_TAC [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `p`
  \\ Q.UNDISCH_TAC `is_reachable (list2edges xs) r z`
  \\ Q.UNDISCH_TAC `is_path r p z (list2edges xs)`
  \\ Q.SPEC_TAC (`r`,`r`) \\ Induct_on `p` << [
    REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [is_path_def,IN_list2edges,MEM_FILTER] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `c` \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `y`      
    \\ ASM_REWRITE_TAC [] \\ Cases_on `is_reachable (list2edges xs) z a` 
    \\ IMP_RES_TAC is_reachable_TRANS \\ METIS_TAC [is_reachable_TRANS],
    SIMP_TAC std_ss [is_path_def,IN_list2edges,MEM_FILTER] \\ REPEAT STRIP_TAC << [
      Q.EXISTS_TAC `c` \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `y`      
      \\ ASM_REWRITE_TAC [] \\ METIS_TAC [is_reachable_TRANS],
      FULL_SIMP_TAC bool_ss [is_path_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `!a. b` (MATCH_MP_TAC o RW [AND_IMP_INTRO] o Q.SPEC `h`)                
      \\ ASM_REWRITE_TAC [is_reachable_def] \\ METIS_TAC [],   
      Q.EXISTS_TAC `c` \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `y`      
      \\ ASM_REWRITE_TAC [] \\ METIS_TAC [is_reachable_TRANS],
      FULL_SIMP_TAC bool_ss [is_path_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `!a. b` (MATCH_MP_TAC o RW [AND_IMP_INTRO] o Q.SPEC `h`)                
      \\ ASM_REWRITE_TAC [is_reachable_def] \\ METIS_TAC []]]);

val is_reachable'_FILTER = prove(
  ``!g xs x y. 
      is_reachable' (list2edges (FILTER g xs)) x y ==> 
      is_reachable' (list2edges xs) x y``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [is_reachable'_def] 
  \\ Q.EXISTS_TAC `r` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [is_reachable_def] \\ DISJ2_TAC
  \\ Q.EXISTS_TAC `p` \\ MATCH_MP_TAC SUBSET_is_path
  \\ Q.EXISTS_TAC `list2edges (FILTER g xs)` \\ ASM_REWRITE_TAC []   
  \\ MATCH_MP_TAC list2edges_SUBSET \\ SIMP_TAC bool_ss [MEM_FILTER]);

val reachables'_SIMP = prove(
  ``MEM z (reachables' a xs ++ reachables' b (unreachables' a xs)) =
    MEM z (reachables' a xs ++ reachables' b xs)``,
  SIMP_TAC bool_ss [unreachables'_def,reachables'_def,MEM_FILTER,MEM,MEM_APPEND,GSYM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [FST]
  \\ IMP_RES_TAC is_reachable'_FILTER
  \\ Cases_on `is_reachable' (list2edges xs) a (FST z)` \\ ASM_REWRITE_TAC []
  \\ IMP_RES_TAC is_reachable'_unreachables
  \\ FULL_SIMP_TAC std_ss [unreachables'_def,reachables'_def,MEM_FILTER]);

val JOIN_reachables' = prove(
  ``MEM z (reachables' a xs ++ reachables' b xs) =
    MEM z (reachables' (a ++ b) xs)``,
  SIMP_TAC bool_ss [reachables'_def,is_reachable'_def,MEM_FILTER,MEM_APPEND]
  \\ METIS_TAC []);

val FILTER_NIL = prove(
  ``!xs g. (FILTER g xs = []) ==> !x. MEM x xs ==> ~g x``,   
  Induct \\ REWRITE_TAC [FILTER,MEM] \\ METIS_TAC [NOT_NIL_CONS]);

val FILTER_CONS = prove(
  ``!xs t g. (FILTER g xs = h::t) ==> MEM h xs /\ g h``,   
  Induct \\ REWRITE_TAC [FILTER,MEM,NOT_NIL_CONS] \\ METIS_TAC [CONS_11]);

val is_reachable'_APPEND = prove(
  ``is_reachable' set (a++b) x = is_reachable' set a x \/ is_reachable' set b x``,
  REWRITE_TAC [is_reachable'_def,MEM_APPEND] \\ METIS_TAC []);

val NOT_MEM_IMP = prove(
  ``!xs x. ~MEM x xs ==> (FILTER ($= x) xs = [])``,
  Induct \\ ASM_SIMP_TAC std_ss [MEM,FILTER]);

val IMP_APPEND_PERM = prove(
  ``(!x. ~MEM x xs \/ ~MEM x ys) /\
    (!x. MEM x zs = MEM x xs \/ MEM x ys) /\
    (!x. MEM x xs ==> (FILTER ($= x) xs = FILTER ($= x) zs)) /\
    (!x. MEM x ys ==> (FILTER ($= x) ys = FILTER ($= x) zs)) ==>
    PERM (xs ++ ys) zs``,
  REWRITE_TAC [PERM_DEF] \\ REPEAT STRIP_TAC \\ Cases_on `MEM x zs` << [
    `(MEM x xs /\ ~MEM x ys) \/ (MEM x ys /\ ~MEM x xs)` by METIS_TAC []  
    \\ IMP_RES_TAC NOT_MEM_IMP \\ NTAC 2 (Q.PAT_ASSUM `!x. a ==> b` IMP_RES_TAC)
    \\ ASM_REWRITE_TAC [APPEND_NIL,FILTER_APPEND],  
    `~MEM x xs /\ ~MEM x ys` by METIS_TAC []   
    \\ IMP_RES_TAC NOT_MEM_IMP \\ ASM_REWRITE_TAC [APPEND_NIL,FILTER_APPEND]]);    
  
val MERGE_reachables'_LEMMA1 = prove(
  ``MEM x (FILTER g xs) /\ (g x ==> h x) ==> 
    (FILTER ($= x) (FILTER g xs) = FILTER ($= x) (FILTER h xs))``,
  REWRITE_TAC [MEM_FILTER,FILTER_FILTER]
  \\ REWRITE_TAC [METIS_PROVE [] ``(x = x') /\ g x' = (x = x') /\ g x``]
  \\ SIMP_TAC bool_ss []);

val MERGE_reachables'_LEMMA2 = prove(
  ``MEM x (FILTER g (FILTER d xs)) /\ (g x ==> h x) ==> 
    (FILTER ($= x) (FILTER g (FILTER d xs)) = FILTER ($= x) (FILTER h xs))``,
  REWRITE_TAC [MEM_FILTER,FILTER_FILTER]
  \\ REWRITE_TAC [METIS_PROVE [] ``(x = x') /\ g x' = (x = x') /\ g x``]
  \\ SIMP_TAC std_ss []
  \\ REWRITE_TAC [METIS_PROVE [] ``(x = x') /\ g x' = (x = x') /\ g x``]
  \\ SIMP_TAC bool_ss []);

val MERGE_reachables' = prove(
  ``!a b xs.
      PERM (reachables' a xs ++ reachables' b (unreachables' a xs))
           (reachables' (a ++ b) xs)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC IMP_APPEND_PERM \\ REPEAT STRIP_TAC
  THEN1 (SIMP_TAC std_ss [reachables'_def,unreachables'_def,MEM_FILTER] \\ METIS_TAC [])
  THEN1 (REWRITE_TAC [GSYM reachables'_SIMP,GSYM JOIN_reachables',GSYM MEM_APPEND]) << [
    FULL_SIMP_TAC bool_ss [reachables'_def,is_reachable'_APPEND]
    \\ ONCE_REWRITE_TAC [GSYM (BETA_CONV ``(\x'. is_reachable' (list2edges xs) a (FST x')) x'``)]
    \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss []))
    \\ MATCH_MP_TAC MERGE_reachables'_LEMMA1 \\ ASM_SIMP_TAC bool_ss [],
    FULL_SIMP_TAC bool_ss [reachables'_def,is_reachable'_APPEND,unreachables'_def]
    \\ MATCH_MP_TAC MERGE_reachables'_LEMMA2 \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC is_reachable'_FILTER \\ ASM_REWRITE_TAC []]);
    
val is_reachable_THM = prove(
  ``!s r n. is_reachable s r n = is_reachable' s [r] n``,
  REWRITE_TAC [is_reachable'_def,MEM] \\ METIS_TAC []);

val reachables_THM = prove(
  ``!a xs. reachables a xs = reachables' [a] xs``,
  REWRITE_TAC [reachables'_def,reachables_def,is_reachable_THM]);

val unreachables_THM = prove(
  ``!a xs. unreachables a xs = unreachables' [a] xs``,
  REWRITE_TAC [unreachables'_def,unreachables_def,reachables_THM]);

val MEM_reachables_SIMP = prove(
  ``MEM z (reachables a1x xs ++ reachables a2x (unreachables a1x xs)) =
    MEM z (reachables a1x xs ++ reachables a2x xs)``,
  REWRITE_TAC [reachables_THM,unreachables_THM,reachables'_SIMP]);

val is_reachable_EXPAND_LEMMA = prove(
  ``(!z. z IN list2edges xs ==> ~(FST z = ax)) /\ ~(ax = z) ==>
    ~is_path ax t z ((ax,ax) INSERT list2edges xs)``,
  Induct_on `t` \\ FULL_SIMP_TAC std_ss [is_path_def,IN_INSERT,PAIR_EQ] \\ METIS_TAC [FST]);

val is_reachable_EXPAND_LEMMA1 = prove(
  ``!x. 
      (!z. z IN set ==> ~(FST z = y)) /\
      ~MEM y (x::p) /\ 
      is_path x p z ((y,y') INSERT set) ==>
      is_path x p z set``,
  Induct_on `p` \\ SIMP_TAC bool_ss [is_path_def,IN_INSERT,PAIR_EQ,MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [MEM]);
  
val is_reachable_EXPAND_LEMMA2 = prove(
  ``!t a2x. 
      (!z. z IN list2edges xs ==> ~(FST z = ax)) /\
      is_path a2x t z ((ax,a2x) INSERT list2edges xs) /\
      ~(a2x = ax) /\ ~(z = a2x) /\ ~(ax = z) ==>
      ?p. is_path a2x p z (list2edges xs)``,
  completeInduct_on `LENGTH t` \\ REPEAT STRIP_TAC \\ Cases_on `MEM ax t` << [
    FULL_SIMP_TAC std_ss [MEM_EQ_APPEND] \\ FULL_SIMP_TAC bool_ss [is_path_APPEND]
    \\ Cases_on `zs` \\ FULL_SIMP_TAC bool_ss [is_path_def,IN_INSERT,PAIR_EQ]
    THEN1 METIS_TAC [FST] 
    \\ `LENGTH t' < LENGTH ys + SUC (SUC (LENGTH t'))` by DECIDE_TAC << [
      Q.PAT_ASSUM `!m. b ==> !m'. c` 
           (ASSUME_TAC o UNDISCH o RW [LENGTH_APPEND,LENGTH] o Q.SPEC `LENGTH t'`)      
      \\ Q.PAT_ASSUM `!m. b ==> !m'. c` 
           (MATCH_MP_TAC o Q.SPEC `a2x` o RW [] o Q.SPEC `t'`)      
      \\ ASM_REWRITE_TAC [] \\ METIS_TAC [],
      METIS_TAC [FST]],
    Q.EXISTS_TAC `t` \\ MATCH_MP_TAC (GEN_ALL is_reachable_EXPAND_LEMMA1)
    \\ Q.EXISTS_TAC `a2x` \\ Q.EXISTS_TAC `ax` \\ ASM_SIMP_TAC bool_ss [MEM]]);

val is_reachable_LEMMA3 = prove(
  ``~(z = ax) ==> is_path ax p z ((ax,ax) INSERT set) ==> ?p. is_path ax p z set``,
  completeInduct_on `LENGTH p` \\ REPEAT STRIP_TAC \\ Cases_on `MEM ax p` << [  
    FULL_SIMP_TAC std_ss [MEM_EQ_APPEND] \\ FULL_SIMP_TAC bool_ss [is_path_APPEND]
    \\ Q.PAT_ASSUM `!m. b ==> !m'. c` 
       (ASSUME_TAC o RW [LENGTH_APPEND,LENGTH] o Q.SPEC `LENGTH zs`)      
    \\ `LENGTH zs < LENGTH ys + SUC (LENGTH zs)` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss []
    \\ Q.PAT_ASSUM `!m. b ==> (c ==> d)` (MATCH_MP_TAC o RW [] o Q.SPEC `zs`)
    \\ ASM_REWRITE_TAC [],
    Q.EXISTS_TAC `p` \\ Q.PAT_ASSUM `!m. m < v:num ==> b` (fn th => ALL_TAC)
    \\ Cases_on `p` \\ FULL_SIMP_TAC bool_ss [is_path_def,IN_INSERT,PAIR_EQ]
    THEN1 METIS_TAC [] THEN1 FULL_SIMP_TAC bool_ss [MEM]
    \\ Q.PAT_ASSUM `x=y` (fn th => ALL_TAC) \\ Q.PAT_ASSUM `x IN y` (fn th => ALL_TAC)
    \\ Q.UNDISCH_TAC `~(z = ax)`
    \\ Q.UNDISCH_TAC `is_path h t z ((ax,ax) INSERT set)`
    \\ Q.UNDISCH_TAC `~MEM ax (h::t)` \\ Q.SPEC_TAC (`h`,`h`)
    \\ Induct_on `t` \\ FULL_SIMP_TAC bool_ss [MEM,is_path_def,IN_INSERT,PAIR_EQ]]);

val is_reachable_LEMMA4 = prove(
  ``!h t. 
      (!z. z IN set ==> ~(FST z = ax)) /\ ~MEM ax (h::t) /\
      is_path h t z ((ax,a1x) INSERT (ax,a2x) INSERT set) ==>
      is_path h t z set``,
  Induct_on `t` \\ FULL_SIMP_TAC bool_ss [MEM,is_path_def,IN_INSERT,PAIR_EQ]
  \\ METIS_TAC []);
    
val is_reachable_EXPAND = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs)) ==>
    is_reachable (list2edges ((ax,a1x,a2x,x,y)::xs)) ax z ==>
    (ax = z) \/ 
    is_reachable (list2edges xs) a1x z \/ 
    is_reachable (list2edges xs) a2x z``,
  REWRITE_TAC [is_reachable_def] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `ax = z` \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MAP,FST]
  \\ Cases_on `z = a1x` \\ FULL_SIMP_TAC bool_ss [PAIR_EQ,reachables_0_lemma1]
  \\ Cases_on `z = a2x` \\ FULL_SIMP_TAC bool_ss [PAIR_EQ,reachables_0_lemma1]
  \\ FULL_SIMP_TAC bool_ss [is_path_def,list2edges_def,IN_INSERT,PAIR_EQ]
  \\ completeInduct_on `LENGTH p` \\ REPEAT STRIP_TAC \\ Cases_on `MEM ax p` << [  
    FULL_SIMP_TAC std_ss [MEM_EQ_APPEND] \\ FULL_SIMP_TAC bool_ss [is_path_APPEND]
    \\ Q.PAT_ASSUM `!m. b ==> !m'. c` 
       (ASSUME_TAC o RW [LENGTH_APPEND,LENGTH] o Q.SPEC `LENGTH zs`)      
    \\ `LENGTH zs < LENGTH ys + SUC (LENGTH zs)` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss []
    \\ Q.PAT_ASSUM `!m. b ==> (c ==> d)` (MATCH_MP_TAC o RW [] o Q.SPEC `zs`)
    \\ ASM_REWRITE_TAC [],
    Cases_on `p` \\ FULL_SIMP_TAC bool_ss [is_path_def,IN_INSERT,PAIR_EQ]
    \\ METIS_TAC [is_reachable_LEMMA4,FST]]);

val ALL_DISTINCT_APPEND = prove(
  ``ALL_DISTINCT (xs ++ ys) = 
    (!x. MEM x xs ==> ~MEM x ys) /\ ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
  Induct_on `xs` \\ ASM_SIMP_TAC bool_ss [APPEND_NIL,APPEND,MEM,ALL_DISTINCT,MEM_APPEND]
  \\ METIS_TAC []);

val JOIN_REACHABLES = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs++ys)) ==>
    (!z. MEM z ((ax,a1x,a2x,x,y)::
                   (ys ++ reachables a1x xs ++
                    reachables a2x (unreachables a1x xs))) =
         MEM z (reachables ax ((ax,a1x,a2x,x,y)::xs) ++ ys))``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [MAP_APPEND,ALL_DISTINCT_APPEND]
  \\ Q.PAT_ASSUM `!x.b` (fn th => ALL_TAC) 
  \\ REWRITE_TAC [MEM,GSYM APPEND_ASSOC] \\ ONCE_REWRITE_TAC [MEM_APPEND]
  \\ REWRITE_TAC [MEM_reachables_SIMP] \\ REWRITE_TAC [MEM_APPEND]
  \\ SIMP_TAC bool_ss [unreachables_def,reachables_def,MEM_FILTER,MEM,GSYM DISJ_ASSOC]
  \\ Cases_on `MEM z ys` \\ ASM_REWRITE_TAC []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [FST]
  THEN1 REWRITE_TAC [is_reachable_def] << [
    FULL_SIMP_TAC bool_ss [is_reachable_def] \\ DISJ2_TAC
    THEN1 (Q.EXISTS_TAC `[]` \\ REWRITE_TAC [is_path_def,list2edges_def,IN_INSERT])
    \\ Q.EXISTS_TAC `a1x::p` \\ REWRITE_TAC [is_path_def,list2edges_def,IN_INSERT]    
    \\ MATCH_MP_TAC SUBSET_is_path \\ Q.EXISTS_TAC `list2edges xs`
    \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT],
    FULL_SIMP_TAC bool_ss [is_reachable_def] \\ DISJ2_TAC
    THEN1 (Q.EXISTS_TAC `[]` \\ REWRITE_TAC [is_path_def,list2edges_def,IN_INSERT])
    \\ Q.EXISTS_TAC `a2x::p` \\ REWRITE_TAC [is_path_def,list2edges_def,IN_INSERT]    
    \\ MATCH_MP_TAC SUBSET_is_path \\ Q.EXISTS_TAC `list2edges xs`
    \\ ASM_SIMP_TAC bool_ss [SUBSET_DEF,IN_INSERT],
    Cases_on `(z = (ax,a1x,a2x,x,y))` \\ ASM_REWRITE_TAC []
    \\ IMP_RES_TAC is_reachable_EXPAND \\ ASM_REWRITE_TAC []
    \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND]
    \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND,MAP,FST,ALL_DISTINCT,MAP_APPEND]
    \\ METIS_TAC []]);

val ALL_DISTINCT_MAP = prove(
  ``!xs f. ALL_DISTINCT (MAP f xs) ==> ALL_DISTINCT xs``,
  Induct \\ ASM_SIMP_TAC bool_ss [ALL_DISTINCT,MAP,MEM_MAP] \\ METIS_TAC []);

val JOIN_UNREACHABLES_LEMMA1 = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs++ys)) ==>
    (!z. MEM z (unreachables a2x (unreachables a1x xs)) =
         MEM z ((ax,a1x,a2x,x,y)::xs) /\ ~MEM z ((ax,a1x,a2x,x,y)::
          (reachables a1x xs ++ reachables a2x (unreachables a1x xs))))``,
  SIMP_TAC std_ss [MEM_FILTER,unreachables_def,MEM,MEM_APPEND]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []
  \\ IMP_RES_TAC ALL_DISTINCT_MAP
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,APPEND,MEM_APPEND]);

val JOIN_UNREACHABLES_LEMMA2 = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs++ys)) ==>
    (!z. MEM z (unreachables ax ((ax,a1x,a2x,x,y)::xs)) =
         MEM z ((ax,a1x,a2x,x,y)::xs) /\ ~MEM z (reachables ax ((ax,a1x,a2x,x,y)::xs)))``,
  SIMP_TAC std_ss [MEM_FILTER,unreachables_def,MEM,MEM_APPEND]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []);

val join_unreachables'_lemma1 = prove(
  ``(!a b z. 
         MEM z (unreachables' b (unreachables' a xs)) =
         MEM z xs /\ ~MEM z 
          (reachables' a xs ++ reachables' b (unreachables' a xs)))``,
  SIMP_TAC std_ss [MEM_FILTER,unreachables'_def,MEM,MEM_APPEND]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC []);

val reachables'_COMM = prove(
  ``!set a b x. reachables' (a++b) xs = reachables' (b++a) xs``,
  REWRITE_TAC [reachables'_def,is_reachable'_def,MEM_APPEND]
  \\ REWRITE_TAC [Once DISJ_COMM]);

val JOIN_unreachables' = prove(
  ``!a b xs z. MEM z (unreachables' a (unreachables' b xs)) =
               MEM z (unreachables' (a ++ b) xs)``,
  REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [join_unreachables'_lemma1]
  \\ SIMP_TAC bool_ss [reachables'_SIMP,JOIN_reachables']
  \\ SIMP_TAC std_ss [unreachables'_def,MEM_FILTER]
  \\ REWRITE_TAC [Once reachables'_COMM]
  \\ EQ_TAC \\ SIMP_TAC bool_ss []);

val is_reachable_APPEND = prove(
  ``!set a b x. 
      is_reachable' set (a ++ b) x = is_reachable' set a x \/ is_reachable' set b x``,
  REWRITE_TAC [is_reachable'_def,MEM_APPEND] \\ METIS_TAC []);

val JOIN_unreachables' = prove(
  ``!a b xs z. (unreachables' a (unreachables' b xs)) =
               (unreachables' (a ++ b) xs)``,
  SIMP_TAC std_ss [unreachables'_def,FILTER_FILTER]
  \\ SIMP_TAC std_ss [reachables'_def,MEM_FILTER] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x t = f y t)``)
  \\ SIMP_TAC std_ss [FUN_EQ_THM,is_reachable_APPEND]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] 
  \\ Cases_on `MEM x xs` \\ ASM_REWRITE_TAC []
  \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ IMP_RES_TAC is_reachable'_FILTER
  \\ IMP_RES_TAC is_reachable'_unreachables
  \\ FULL_SIMP_TAC std_ss [unreachables'_def,reachables'_def,MEM_FILTER]);
 
val JOIN_UNREACHABLES = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs++ys)) ==>
    (!z. MEM z (unreachables a2x (unreachables a1x xs)) =
         MEM z (unreachables ax ((ax,a1x,a2x,x,y)::xs)))``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (UNDISCH JOIN_UNREACHABLES_LEMMA1)
  \\ STRIP_ASSUME_TAC (UNDISCH JOIN_UNREACHABLES_LEMMA2)
  \\ FULL_SIMP_TAC bool_ss [MAP_APPEND,ALL_DISTINCT_APPEND]
  \\ STRIP_ASSUME_TAC ((UNDISCH o RW [APPEND_NIL] o Q.INST [`ys`|->`[]`]) JOIN_REACHABLES)
  \\ ASM_REWRITE_TAC []);

val ALL_DISTINCT_REACHABLES = prove(
  ``!xs ys ax.
      ALL_DISTINCT (MAP FST (xs ++ ys)) ==> ALL_DISTINCT (reachables ax xs ++ ys)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [reachables_def]
  \\ Q.SPEC_TAC (`is_reachable (list2edges xs) ax`,`g`)
  \\ Induct_on `xs` \\ ASM_REWRITE_TAC [FILTER,APPEND_NIL,ALL_DISTINCT_MAP]
  \\ SIMP_TAC std_ss [APPEND,ALL_DISTINCT,MAP,MEM_MAP] \\ REPEAT STRIP_TAC
  \\ Cases_on `g (FST h)` \\ ASM_REWRITE_TAC [ALL_DISTINCT,APPEND] << [
    `~MEM h (xs ++ ys)` by METIS_TAC []
    \\ FULL_SIMP_TAC bool_ss [MEM_APPEND,MEM_FILTER]
    \\ METIS_TAC [],METIS_TAC []]); 

val ALL_DISTINCT_FILTER = prove(
  ``!xs g. ALL_DISTINCT xs ==> ALL_DISTINCT (FILTER g xs)``,
  Induct \\ REWRITE_TAC [FILTER,ALL_DISTINCT] \\ REPEAT STRIP_TAC
  \\ Cases_on `g h` \\ ASM_SIMP_TAC bool_ss [ALL_DISTINCT,MEM_FILTER]);

val ALL_DISTINCT_JOIN_REACHABLES = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs ++ ys)) ==>
    ALL_DISTINCT ((ax,a1x,a2x,x,y)::
       (ys ++ reachables a1x xs ++ reachables a2x (unreachables a1x xs)))``,
  REWRITE_TAC [ALL_DISTINCT,APPEND,MAP,FST] \\ REPEAT STRIP_TAC      
  THEN1 (FULL_SIMP_TAC std_ss [MEM_APPEND,MAP_APPEND,reachables_def,
      unreachables_def,MEM_FILTER,MEM_MAP] \\ METIS_TAC [FST])
  \\ FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC,MAP_APPEND]
  \\ Q.PAT_ASSUM `ALL_DISTINCT asd` (STRIP_ASSUME_TAC o RW [ALL_DISTINCT_APPEND])
  \\ ONCE_REWRITE_TAC [ALL_DISTINCT_APPEND] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,reachables_def,
       unreachables_def,MEM_MAP,MEM_FILTER] \\ METIS_TAC [FST])    
  THEN1 METIS_TAC [ALL_DISTINCT_MAP]
  \\ REWRITE_TAC [ALL_DISTINCT_APPEND] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,reachables_def,
    unreachables_def,MEM_MAP,MEM_FILTER] \\ METIS_TAC [])
  \\ REWRITE_TAC [reachables_def] \\ MATCH_MP_TAC ALL_DISTINCT_FILTER
  \\ METIS_TAC [ALL_DISTINCT_FILTER,unreachables_def,ALL_DISTINCT_MAP]);  

val ALL_DISTINCT_JOIN_UNREACHABLES = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs ++ ys)) ==>
    ALL_DISTINCT (unreachables a2x (unreachables a1x xs))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ALL_DISTINCT_MAP
  \\ REWRITE_TAC [unreachables_def]
  \\ MATCH_MP_TAC ALL_DISTINCT_FILTER
  \\ MATCH_MP_TAC ALL_DISTINCT_FILTER
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT_APPEND,ALL_DISTINCT]);

val ALL_DISTINCT_JOIN_UNREACHABLES2 = prove(
  ``ALL_DISTINCT (MAP FST ((ax,a1x,a2x,x,y)::xs ++ ys)) ==>
    ALL_DISTINCT (unreachables ax ((ax,a1x,a2x,x,y)::xs))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ALL_DISTINCT_MAP
  \\ REWRITE_TAC [unreachables_def]
  \\ MATCH_MP_TAC ALL_DISTINCT_FILTER
  \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT_APPEND,ALL_DISTINCT]);

val STAR_IMP_STAR_T = prove(
  ``!P Q s. (P * Q) s ==> (P * SEP_T) s``,
  SIMP_TAC std_ss [STAR_def,SEP_T_def] \\ METIS_TAC []);

val ALL_DISTINCT_EQ_FORALL = prove(
  ``!xs. ALL_DISTINCT xs = !x ys zs qs. ~(xs = ys ++ x::zs ++ x::qs)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [ALL_DISTINCT_APPEND,MEM,MEM_APPEND] \\ METIS_TAC [])
  \\ Induct_on `xs` \\ REWRITE_TAC [ALL_DISTINCT] \\ REPEAT STRIP_TAC << [  
    FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND] \\ FULL_SIMP_TAC bool_ss []
    \\ METIS_TAC [APPEND,APPEND_NIL],
    METIS_TAC [CONS_11,APPEND]]);

val NOT_ALL_DISTINCT_FST = prove(
  ``~ALL_DISTINCT (MAP FST xs) ==> 
    ?xs' x ys y zs. (FST x = FST y) /\ (xs = xs' ++ [x] ++ ys ++ [y] ++ zs)``,
  Induct_on `xs` \\ SIMP_TAC std_ss [ALL_DISTINCT,MAP]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [MEM_MAP,MEM_EQ_APPEND] << [  
    Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `h` \\ Q.EXISTS_TAC `ys` \\ Q.EXISTS_TAC `y`
    \\ Q.EXISTS_TAC `zs` \\ ASM_REWRITE_TAC [APPEND,GSYM APPEND_ASSOC],    
    Q.EXISTS_TAC `h::xs'` \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `ys`
    \\ Q.EXISTS_TAC `y` \\ Q.EXISTS_TAC `zs` \\ ASM_REWRITE_TAC [APPEND]]);

val ARM_PROG_uvs_ALL_DISTINCT = prove(
  ``ARM_PROG (uvs xs ys ax px qs * P) cs C Q Z =
    ALL_DISTINCT (MAP FST (xs ++ ys)) ==> 
    ARM_PROG (uvs xs ys ax px qs * P) cs C Q Z``,
  Cases_on `ALL_DISTINCT (MAP FST (xs ++ ys))` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [uvs_def,MAP_APPEND,ALL_DISTINCT_APPEND,MEM_MAP]
  \\ IMP_RES_TAC NOT_ALL_DISTINCT_FST << [
    Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
    \\ Cases_on `y'` \\ Cases_on `r` \\ Cases_on `r''` \\ Cases_on `r`
    \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND,FST,unseen_def,visited_def,MAP,
         MAP_APPEND,unseen1_def,STAR_LIST_APPEND,STAR_LIST_def,
         visited1_def,link_block_def,STAR_ASSOC]
    \\ MOVE_STAR_TAC `a1*a2*a3*a4*a5*a6*a7*a8*a9*b1*b2*b3*b4*b5*b6*b7*c1` 
                     `a9*a2*(a8*a3*a4*a5*a6*a1*a7*b1*b2*b3*b4*b5*b6*b7*c1)`
    \\ REWRITE_TAC [ARM_PROG_M_11],
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
    \\ Cases_on `y` \\ Cases_on `r` \\ Cases_on `r''` \\ Cases_on `r`
    \\ FULL_SIMP_TAC bool_ss [unseen_def,unseen1_def,MAP_APPEND,
       STAR_LIST_APPEND,MAP,STAR_LIST_def,emp_STAR,link_block_def,STAR_ASSOC,FST]
    \\ MOVE_STAR_TAC `a1*a2*a3*a4*a5*a6*a7*a8*a9*b1*b2*b3*b4*b5*b6*b7*c1` 
                     `a8*a2*(a9*a3*a4*a5*a6*a1*a7*b1*b2*b3*b4*b5*b6*b7*c1)`
    \\ REWRITE_TAC [ARM_PROG_M_11],
    Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
    \\ Cases_on `y` \\ Cases_on `r` \\ Cases_on `r''` \\ Cases_on `r`
    \\ FULL_SIMP_TAC bool_ss [visited_def,visited1_def,MAP_APPEND,
       STAR_LIST_APPEND,MAP,STAR_LIST_def,emp_STAR,link_block_def,STAR_ASSOC,FST]
    \\ MOVE_STAR_TAC `a1*a2*a3*a4*a5*a6*a7*a8*a9*b1*b2*b3*b4*b5*b6*b7*c1` 
                     `a9*a3*(a8*a2*a4*a5*a6*a1*a7*b1*b2*b3*b4*b5*b6*b7*c1)`
    \\ REWRITE_TAC [ARM_PROG_M_11]]);

val ALL_DISTINCT_COMM = prove(
  ``!xs ys. ALL_DISTINCT (xs++ys) = ALL_DISTINCT (ys++xs)``,
  REWRITE_TAC [ALL_DISTINCT_APPEND] \\ METIS_TAC []);

val MEM_AND_DISTINCT_IMP_SAME = (RW [APPEND_NIL] o Q.SPEC `[]` o prove) (
  ``!zs xs ys.
      (!x. MEM x xs = MEM x ys) ==> ALL_DISTINCT xs ==> ALL_DISTINCT ys ==>
      P (zs++xs) ==> (!xs ys zs. P (zs++xs++ys) = P (zs++ys++xs)) ==> P (zs++ys)``,
  Induct_on `xs` THEN1 (Cases_on `ys` \\ REWRITE_TAC [] \\ METIS_TAC [MEM])
  \\ REWRITE_TAC [MEM] \\ NTAC 6 STRIP_TAC
  \\ REWRITE_TAC [AND_IMP_INTRO] \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ REWRITE_TAC [GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ `?ys1 ys2. ys = ys1 ++ h::ys2` by (ASM_REWRITE_TAC [GSYM MEM_EQ_APPEND] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `!xs ys zs. b = b'` (fn th => ASM_REWRITE_TAC [] \\ ASSUME_TAC th)
  \\ ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND] ``[h] ++ xs``)]
  \\ `P (zs ++ ([h] ++ xs)) = P (([h] ++ zs) ++ xs)` by METIS_TAC [APPEND_ASSOC,APPEND_NIL]
  \\ `P (zs ++ (ys1 ++ ([h] ++ ys2))) = P (([h] ++ zs) ++ (ys1 ++ ys2))`  by METIS_TAC [APPEND_ASSOC,APPEND_NIL]
  \\ Q.PAT_ASSUM `!xs ys zs. b = b'` (fn th => ASM_REWRITE_TAC [] \\ ASSUME_TAC th)
  \\ ONCE_REWRITE_TAC [APPEND] \\ REWRITE_TAC [APPEND_NIL] \\ STRIP_TAC
  \\ Q.PAT_ASSUM `!xs ys. b ==> c` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
  \\ REPEAT STRIP_TAC << [    
    Q.PAT_ASSUM `!xs ys zs. b = b'` (fn th => ALL_TAC)
    \\ `ALL_DISTINCT (h::ys2++ys1)` by METIS_TAC [ALL_DISTINCT_COMM]
    \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM_APPEND,MEM,APPEND]
    \\ Q.PAT_ASSUM `!x. (x = h) \/ c = b'` (ASSUME_TAC o SPEC_ALL)
    \\ Cases_on `x = h` \\ FULL_SIMP_TAC bool_ss [],
    FULL_SIMP_TAC bool_ss [ALL_DISTINCT],
    `ALL_DISTINCT (h::ys2++ys1)` by METIS_TAC [ALL_DISTINCT_COMM]
    \\ FULL_SIMP_TAC bool_ss [ALL_DISTINCT,MEM_APPEND,MEM,APPEND]
    \\ ONCE_REWRITE_TAC [ALL_DISTINCT_COMM] \\ METIS_TAC [],
    METIS_TAC [],METIS_TAC []]);

val IMP_IMP_SEP_EQ = prove(
  ``!P c. (!s. P s ==> c) ==> (P = P * cond c)``,
  SIMP_TAC bool_ss [cond_STAR,FUN_EQ_THM] \\ METIS_TAC []);

val fst_ret1_123 = let
  val th1 = fst_init123
  val th2 = Q.INST [`xs`|->`unreachables a1x xs`,`ys`|->`ys ++ reachables a1x xs`] ret1_123
  val th = ARRANGE_COMPOSE th1 th2
  val th = RW [GSYM STAR_ASSOC] th
  val th = RW [STAR_ASSOC] (RW1 [ARM_PROG_uvs_ALL_DISTINCT] th)
  val th = UNDISCH th 
  val lemma = MEM_AND_DISTINCT_IMP_SAME 
  val lemma = MATCH_MP lemma (UNDISCH JOIN_REACHABLES)
  val lemma = MATCH_MP lemma (UNDISCH ALL_DISTINCT_JOIN_REACHABLES)  
  val lemm1 = Q.SPECL [`(ax,a1x,a2x,x,y)::xs`,`ys`,`ax`] ALL_DISTINCT_REACHABLES  
  val lemma = MATCH_MP lemma (UNDISCH lemm1)  
  val th = CONV_RULE (UNBETA_CONV ``(ax:word30,a1x:word30,a2x:word30,x:word32,y:word32)::(ys++reachables a1x xs++reachables a2x (unreachables a1x xs))``) th
  val tm = (fst o dest_comb o concl) th
  val lemma = SIMP_RULE std_ss [] (ISPEC tm (Q.GEN `P` lemma))
  val th = MATCH_MP lemma (BETA_RULE th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV) (RAND_CONV (ONCE_REWRITE_CONV [uvs_ys_comm2]) THENC REWRITE_CONV []) ) th  
  val th = SIMP_RULE std_ss [] th
  val lemma = MEM_AND_DISTINCT_IMP_SAME 
  val lemma = MATCH_MP lemma (UNDISCH JOIN_UNREACHABLES)
  val lemma = MATCH_MP lemma (UNDISCH ALL_DISTINCT_JOIN_UNREACHABLES)  
  val lemma = MATCH_MP lemma (UNDISCH ALL_DISTINCT_JOIN_UNREACHABLES2)  
  val th = CONV_RULE (UNBETA_CONV ``unreachables a2x (unreachables a1x xs) : (word30#word30#word30#word32#word32) list``) th
  val tm = (fst o dest_comb o concl) th
  val lemma = SIMP_RULE std_ss [] (ISPEC tm (Q.GEN `P` lemma))
  val th = MATCH_MP lemma (BETA_RULE th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV) (RAND_CONV (ONCE_REWRITE_CONV [uvs_xs_comm2]) THENC REWRITE_CONV []) ) th  
  val th = SIMP_RULE std_ss [] th
  val th = PAT_DISCH ``ALL_DISTINCT (x:'a list)`` th 
  val th = RW [STAR_ASSOC] (RW [GSYM STAR_ASSOC,GSYM ARM_PROG_uvs_ALL_DISTINCT] th)
  val th = RW1 [uvs_ys_comm] th
  in th end;  

val fst_ret1_123' = let
  val th = RW [GSYM uvs'_def] fst_ret1_123
  val th = Q.INST [`ppx`|->`px`] th
  in th end;
  
val ret2_123 = let
  val lemma = prove(
    ``(!zs. P zs (z::zs)) ==> !zs. has_head zs z ==> P (TL zs) zs``,
    REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [has_head_def] 
    \\ Cases_on `zs` \\ FULL_SIMP_TAC bool_ss [HD,TL])
  val th = CONV_RULE (UNBETA_CONV ``((a1x,ppx,x,y),T)::zs:((word30#word30#word32#word32)#bool) list``) ret2_case2''
  val th = CONV_RULE (RATOR_CONV (UNBETA_CONV ``zs:((word30#word30#word32#word32)#bool) list``)) th
  val th = SPEC_ALL (SIMP_RULE std_ss [] (MATCH_MP lemma (Q.GEN `zs` th)))
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (has_head zs ((a1x:word30,ppx:word30,x:word32,y:word32),T))` th
  val th2 = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th2 = APP_WEAKEN th2 
    `SEP_EXISTS a1x ppx x y.
       R30 a px * R30 p ppx * ~R a2 * ~R t * ~S *
       uvs xs ((px,a1x,ax,x,y)::ys) px ppx (TL zs) *
       cond (has_head zs ((a1x,ppx,x,y),T))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th = CONV_RULE (UNBETA_CONV ``((ppx,a2x,x,y),F)::zs:((word30#word30#word32#word32)#bool) list``) ret2_case3''
  val th = CONV_RULE (RATOR_CONV (UNBETA_CONV ``zs:((word30#word30#word32#word32)#bool) list``)) th
  val th = SPEC_ALL (SIMP_RULE std_ss [] (MATCH_MP lemma (Q.GEN `zs` th)))
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `cond (has_head zs ((ppx:word30,a2x:word30,x:word32,y:word32),F))` th
  val th3 = SIMP_RULE (bool_ss++sep2_ss) [] th
  val th3 = APP_WEAKEN th3 
    `SEP_EXISTS ppx a2x x y.
       R30 a px * R30 p ppx * R30 a2 a2x * ~R t * ~S *
       uvs xs ((px,ax,a2x,x,y)::ys) px ppx (TL zs) *
       cond (has_head zs ((ppx,a2x,x,y),F))`
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  val th = APP_FRAME `R30 a ax * ~R a2 * ~R t * cond (zs:((word30#word30#word32#word32)#bool) list = [])` ret2_case1''
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th  
  val th1 = MOVE_STAR_RULE `p*s*uv*a*a2*t*c` `a*p*a2*t*s*uv*c` th
  val th = APP_MERGE th3 th2
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val th = RW [ARM_PROG_MOVE_COND] th
  val th = (Q.GEN `ppx`o Q.GEN `a1x`o Q.GEN `a2x`o Q.GEN `x`o Q.GEN `y`) th
  val lemma = prove(
    ``!P. (!ppx:word30 a1x:word30 a2x:word30 x:word32 y:word32. has_head zs ((ppx,a2x,x,y),F) \/ has_head zs ((a1x,ppx,x,y),T) ==> P) ==> ~(zs = []) ==> P``,
    Cases_on `zs` \\ REWRITE_TAC [has_head_def,HD]
    \\ Cases_on `h` \\ Cases_on `r` \\ Cases_on `q` \\ Cases_on `r` \\ Cases_on `r'`
    \\ REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [NOT_NIL_CONS])
  val th = MATCH_MP lemma th
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_MERGE th1 th
  val th = SIMP_RULE (bool_ss++sep_ss) [INSERT_UNION_EQ,UNION_EMPTY] th
  in th end;
   
val ret2_123' = let
  val th = ret2_123
  val th = Q.INST [`xs`|->`unreachables bx xs`,`ys`|->`ys ++ reachables bx xs`] th
  val th = RW [APPEND_NIL] (RW1 [GSYM APPEND] th)
  val th = RW [GSYM uvs'_def] th
  in th end;

val loop_LEMMA = prove(
  ``(!xs'. LENGTH xs' < LENGTH ((ax,a1x,a2x,x,y)::xs) ==> GC_ASSUMPTION a p a1 a2 t P C xs') ==>
    GC_ASSUMPTION a p a1 a2 t P C xs /\
    GC_ASSUMPTION a p a1 a2 t P C (unreachables a1x xs)``,
  REWRITE_TAC [LENGTH,DECIDE ``n < SUC m = n <= m``] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MATCH_MP_TAC \\ REWRITE_TAC [LESS_EQ_REFL,unreachables_def]
  \\ Q.SPEC_TAC (`\x. ~MEM x (reachables a1x xs)`,`g`)
  \\ Induct_on `xs` \\ ASM_REWRITE_TAC [FILTER,LESS_EQ_REFL] \\ REPEAT STRIP_TAC
  \\ Cases_on `g h` \\ ASM_REWRITE_TAC [LENGTH,LESS_EQ_MONO] 
  \\ METIS_TAC [DECIDE ``n <= SUC n``,LESS_EQ_TRANS]);

val loop = let 
  val th1 = fst_ret1_123'
  val th2 = APP_FRAME `~R a1` ret2_123'
  val th2 = Q.INST [`xs`|->`(ax,a1x,a2x,x,y)::xs`,`bx`|->`ax`,`zs`|->`qs`] th2
  val th = ARRANGE_COMPOSE th1 th2
  val th = SIMP_RULE (arith_ss++sep2_ss) [pcINC_def,wLENGTH_def,LENGTH] th
  val th = DISCH_ALL th
  val th = RW [AND_IMP_INTRO] th  
  val lemma = METIS_PROVE [] ``GC_ASSUMPTION a p a1 a2 t P C (unreachables a1x xs) /\ GC_ASSUMPTION a p a1 a2 t P C xs = GC_ASSUMPTION a p a1 a2 t P C xs /\ GC_ASSUMPTION a p a1 a2 t P C (unreachables a1x xs)``
  val th = RW [lemma] th    
  val th = MATCH_MP th (Q.INST [`P`|->`emp`] (UNDISCH loop_LEMMA))
  val th = DISCH_ALL th
  val th = INST [``ax':word30``|->``ax:word30``,``a1x':word30``|->``a1x:word30``,``a2x':word30``|->``a2x:word30``,``x':word32``|->``x:word32``,``y':word32``|->``y:word32``] th
  val lemma = prove(
    ``(!xs. P (x::xs)) ==> (!xs ys. P (xs++ys) = P (ys++xs)) ==> !xs. MEM x xs ==> P xs``,
    REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND] \\ METIS_TAC [APPEND])
  val th = CONV_RULE (UNBETA_CONV ``(ax:word30,a1x:word30,a2x:word30,x:word32,y:word32)::xs``) th
  val th = Q.GEN `xs` th  
  val th = SIMP_RULE std_ss [] (MATCH_MP lemma th)  
  val append = METIS_PROVE [LENGTH_APPEND,ADD_COMM]  ``LENGTH (xs++ys) = LENGTH (ys++xs)``
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV) (RAND_CONV (ONCE_REWRITE_CONV [uvs_xs_comm,uvs'_xs_comm,append]) THENC REWRITE_CONV []) ) th
  val th = SPEC_ALL (RW [] th)
  val th = (UNDISCH o RW [GSYM AND_IMP_INTRO] o RW1 [CONJ_COMM] o RW [AND_IMP_INTRO]) th   
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  val th = APP_FRAME `emp` th
  val th = CONV_RULE (RAND_CONV (REWRITE_CONV [emp_STAR])) th
  val th = PRE_MOVE_STAR `uv*p*a*a1*a2*t*s*cond b` `uv*p*a*a1*t*a2*s*cond b`  th
  val th = POST_MOVE_STAR `a*p*a2*t*s*uv*a1*cond b` `uv*p*a*a1*t*a2*s*cond b` th
  val th = (Q.GEN `ys` o Q.GEN `qs` o Q.GEN `px` o Q.GEN `ax` o Q.GEN `a1x` o Q.GEN `a2x` o Q.GEN `x` o Q.GEN `y`) th
  val lemma1 = prove(``1073741849w = 25w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val lemma2 = prove(``1073741838w = 14w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val lemma3 = prove(``1073741824w = 0w:word30``,SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  val th = SIMP_RULE (bool_ss++setINC_ss) [lemma1,lemma2,lemma3,UNION_IDEMPOT] th
  val th = RW1 [ARM_PROG_EXTRACT_CODE] th
  val (_,_,c,_,_) = dest_ARM_PROG ((concl o SPEC_ALL) th)
  val goal = subst [mk_var("c",type_of c)|->c,``P:('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) ARMset -> bool``|->``emp:('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) ARMset -> bool``] 
    ``GC_ASSUMPTION a p a1 a2 t P c xs``
  val th' = REWRITE_CONV [GC_ASSUMPTION_def] goal
  val th = EQ_MP (GSYM th') th
  val th = RW1 [INSERT_SING_UNION] th
  val th' = Q.ISPEC `GC_ASSUMPTION a p a1 a2 t emp` PROC_RECURSION
  val th' = Q.SPEC `LENGTH` th'
  val th = (Q.GEN `xs` o Q.GEN `C` o DISCH_ALL) th
  val th = MATCH_MP th' th
  val th = Q.SPEC `xs` th
  in th end;

val loop' = let
  val th = (SPEC_ALL o RW [GC_ASSUMPTION_def,GSYM ARM_PROG_EXTRACT_CODE]) loop
  val th = SIMP_RULE (bool_ss++sep_ss) [has_head_def] (Q.INST [`zs`|->`[]`,`px`|->`0w`] th)
  val contract = prove(``ARM_PROG P cs C SEP_F ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C Q Z``,METIS_TAC [ARM_PROG_EXTRACT_POST])
  val th = MATCH_MP contract th
  val th = SIMP_RULE std_ss [pcINC_def,wLENGTH_def,LENGTH] th
  val th = RW [ARM_PROG_FALSE_POST] th
  in th end;

val loop'' = let 
  val th = Q.INST [`px`|->`0w`,`zs`|->`[]`] start_case3''
  val th' = Q.INST [`xs`|->`(ax,a1x,a2x,x,y)::xs`] loop'
  val th' = SIMP_RULE (bool_ss++sep_ss) [MEM] th'
  val th = APP_FRAME `R30 p 0w * ~R a2` th
  val th = ARRANGE_COMPOSE th th'
  val th = RW [STAR_ASSOC] th
  val lemma = prove(
    ``(!xs. P (x::xs)) ==> (!xs ys. P (xs++ys) = P (ys++xs)) ==> !xs. MEM x xs ==> P xs``,
    REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND] \\ METIS_TAC [APPEND])
  val th = CONV_RULE (UNBETA_CONV ``(ax:word30,a1x:word30,a2x:word30,x:word32,y:word32)::xs``) th
  val th = Q.GEN `xs` th  
  val th = SIMP_RULE std_ss [] (MATCH_MP lemma th)  
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV) (RAND_CONV (ONCE_REWRITE_CONV [uvs_xs_comm,uvs'_xs_comm]) THENC REWRITE_CONV []) ) th
  val th = SPEC_ALL (RW [] th)   
  val lemma = prove(
    ``(!a1x a2x x y. MEM (ax,a1x,a2x,x,y) xs ==> P) ==> ax IN list2domain xs ==> P``,
    Induct_on `xs` \\ REWRITE_TAC [MEM,MAP,list2domain_def,NOT_IN_EMPTY] \\ REPEAT STRIP_TAC
    \\ Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
    \\ FULL_SIMP_TAC bool_ss [FST,PAIR_EQ,list2domain_def,IN_INSERT] \\ METIS_TAC [])
  val th = MATCH_MP lemma ((Q.GEN `a1x` o Q.GEN `a2x` o Q.GEN `x` o Q.GEN `y`) th)
  val th = RW [GSYM ARM_PROG_MOVE_COND] th
  in th end;

val single_loop = let
  val th1 = RW [GSYM uvs'_def] (RW1 [uvs_ys_comm] start_case1'')
  val th2 = RW [GSYM uvs'_def] (RW1 [uvs_ys_comm] start_case2'')
  val th1 = APP_FRAME `~R t * ~R a1` th1
  val th1 = PRE_MOVE_STAR `uv*a*s*c*(t*a1)` `uv*a*a1*t*s*c` th1
  val th1 = POST_MOVE_STAR `uv*a*s*(t*a1)` `uv*a*a1*t*s` th1
  val th2 = PRE_MOVE_STAR `uv*a*s*t*a1*c` `uv*a*a1*t*s*c` th2
  val th2 = POST_MOVE_STAR `uv*a*s*t*a1` `uv*a*a1*t*s` th2
  val th = APP_MERGE th1 th2
  val th = Q.INST [`px`|->`0w`,`qs`|->`[]`] th
  val th = APP_FRAME `~R a2 * R30 p 0w` th
  val th = PRE_MOVE_STAR `uv*a*a1*t*s*c*(a2*p)` `uv*a*t*a1*s*p*a2*c` th  
  val th = POST_MOVE_STAR `uv*a*a1*t*s*(a2*p)` `uv*p*a*a1*t*a2*s` th  
  val th = APP_MERGE th loop''
  val contract_better = prove(``ARM_PROG P cs C Q' ((Q,f) INSERT Z) ==> (f = pcINC cs) ==> ARM_PROG P cs C (Q' \/ Q) Z``,METIS_TAC [ARM_PROG_EXTRACT_POST,ARM_PROG_MERGE_POST])
  val th = MATCH_MP contract_better th
  val th = SIMP_RULE std_ss [pcINC_def,wLENGTH_def,LENGTH,SEP_DISJ_CLAUSES] th
  val lemma = prove( 
    ``((ax = 0w) \/ ~(ax IN list2domain xs) /\ ax IN domain xs ys ax 0w []) \/
      ax IN list2domain xs = (ax = 0w) \/ ax IN domain xs ys ax 0w []``,
    REWRITE_TAC [domain_def,IN_UNION] \\ METIS_TAC [])
  val th = RW [lemma] th
  in th end;

val uv_def = Define `
  uv roots xs = uvs (unreachables' roots xs) (reachables' roots xs) 0w 0w []`;

val uvs_EMPTY = prove(
  ``!xs ys ax. uvs xs ys ax 0w [] = uvs xs ys 0w 0w []``,
  REWRITE_TAC [uvs_def,connect_def,range_def,domain_def,stack2list_def]);

val uv_INTRO = prove(
  ``!xs ax. uvs (unreachables' roots xs) (reachables' roots xs) ax 0w [] = uv roots xs``,
  ONCE_REWRITE_TAC [uv_def,uvs_EMPTY] \\ REWRITE_TAC []);

val EQ_FILTER_MOVE_CONS = prove(
  ``!xs ys x y. FILTER ($= x) (xs ++ y::ys) = FILTER ($= x) (y::xs ++ ys)``,
  Induct \\ SIMP_TAC bool_ss [APPEND_NIL,FILTER,APPEND]
  \\ ONCE_ASM_REWRITE_TAC [] \\ SIMP_TAC bool_ss [APPEND_NIL,FILTER,APPEND]
  \\ METIS_TAC []);

val APPEND_APPEND_IMP_PERM_LEMMA = prove(
  ``(!xs ys zs. P (xs++ys++zs) = P (xs++zs++ys)) ==>
    !xs ys zs. PERM xs ys ==> (P (zs ++ xs) = P (zs ++ ys))``,
  REWRITE_TAC [PERM_DEF] \\ STRIP_TAC \\ Induct \\ REWRITE_TAC [] << [
    Cases_on `ys` \\ REWRITE_TAC [FILTER] \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x. [] = d` (ASSUME_TAC o Q.SPEC `h`)
    \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS],
    REPEAT STRIP_TAC \\ `MEM h ys` by ALL_TAC << [
      CCONTR_TAC \\ Q.PAT_ASSUM `!x. FILTER g xs = h` (ASSUME_TAC o Q.SPEC `h`)
      \\ FULL_SIMP_TAC std_ss [FILTER] \\ Cases_on `FILTER ($= h) ys`
      \\ FULL_SIMP_TAC bool_ss [NOT_NIL_CONS]
      \\ `MEM h' (FILTER ($= h) ys)` by METIS_TAC [MEM]
      \\ FULL_SIMP_TAC std_ss [MEM_FILTER],
      NTAC 2 (FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND])
      \\ REWRITE_TAC [APPEND_ASSOC] \\ ONCE_ASM_REWRITE_TAC []
      \\ ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND] ``[x]++xs``)]
      \\ REWRITE_TAC [APPEND_ASSOC]      
      \\ Q.PAT_ASSUM `!xs ys zs. b` (fn th => 
          CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
      \\ ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND_ASSOC] ``(xs++ys)++(zs++qs)``)]
      \\ Q.PAT_ASSUM `!ys zs. b` MATCH_MP_TAC
      \\ FULL_SIMP_TAC bool_ss [EQ_FILTER_MOVE_CONS,APPEND]
      \\ FULL_SIMP_TAC bool_ss [FILTER]
      \\ STRIP_TAC \\ Cases_on `x = h`
      \\ Q.PAT_ASSUM `!x. b` (ASSUME_TAC o Q.SPEC `x`)
      \\ METIS_TAC [CONS_11]]]);
 
val APPEND_APPEND_IMP_PERM = prove(
  ``(!xs ys zs. P (xs++ys++zs) = P (xs++zs++ys)) ==>
    !xs ys. PERM xs ys ==> (P xs = P ys)``,
  STRIP_TAC \\ IMP_RES_TAC APPEND_APPEND_IMP_PERM_LEMMA
  \\ METIS_TAC [APPEND_NIL]);

val uvs_ys_PERM = (SIMP_RULE std_ss [] o prove) (
  ``!ys ys'. PERM ys ys' ==> 
      ((\ys. uvs xs ys ax px qs) ys = (\ys. uvs xs ys ax px qs) ys')``,
  MATCH_MP_TAC APPEND_APPEND_IMP_PERM \\ SIMP_TAC std_ss [uvs_ys_comm2]);

val uvs'_EQ_uv = prove(
  ``!xs ax bx. uvs' (unreachables' roots xs) (reachables' roots xs) ax 0w [] bx = uv (bx::roots) xs``,
  REWRITE_TAC [uvs'_def,reachables_THM,unreachables_THM,uv_def,JOIN_unreachables',APPEND]
  \\ ONCE_REWRITE_TAC [uvs_EMPTY] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC uvs_ys_PERM 
  \\ METIS_TAC [APPEND,reachables'_COMM,MERGE_reachables']);

val uv_address_def = Define `
  uv_address roots xs = !x. MEM x roots ==> (x = 0w) \/ x IN (list2domain xs)`;

val list2domain_MEM_EQ = prove(
  ``!xs ys. (!x. MEM x xs = MEM x ys) ==> (list2domain xs = list2domain ys)``,
  REWRITE_TAC [IN_list2domain,EXTENSION,MEM_MAP] \\ METIS_TAC []);

val list2domain_SIMP = prove(
  ``list2domain (unreachables' roots xs) UNION list2domain (reachables' roots xs) =
    list2domain xs``,
  REWRITE_TAC [unreachables'_def,GSYM list2domain_APPEND]
  \\ MATCH_MP_TAC list2domain_MEM_EQ
  \\ SIMP_TAC std_ss [reachables'_def,MEM_FILTER,MEM_APPEND] \\ METIS_TAC []);

val uv_address_SING = prove( 
  ``(ax = 0w) \/
    ax IN domain (unreachables' roots xs) (reachables' roots xs) ax 0w [] =
    uv_address [ax] xs``,
  REWRITE_TAC [uv_address_def,MEM,domain_def,stack2list_def,list2domain_def,
    UNION_EMPTY,list2domain_SIMP] \\ METIS_TAC []);

val uv_address_APPEND = prove(
  ``!a b xs. uv_address a xs /\ uv_address b xs = uv_address (a++b) xs``,
  REWRITE_TAC [uv_address_def,MEM_APPEND] \\ METIS_TAC []);

val uv_loop = let
  val th = Q.INST [`xs`|->`unreachables' roots xs`,`ys`|->`reachables' roots xs`] single_loop
  val th = RW [uvs'_EQ_uv,uv_INTRO,uv_address_SING] th  
  val th = SPEC_STRENGTHEN th `R30 a ax * (\roots. uv roots xs * R30 p 0w * ~R a1 * ~R a2) roots * ~R t * ~S * cond ((\ax. uv_address [ax] xs) ax)`   
  val th = RW [] (CONV_RULE (RATOR_CONV (SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL])) th)
  val th = SPEC_WEAKEN1 th `R30 a ax * (\roots. uv roots xs * R30 p 0w * ~R a1 * ~R a2) (ax::roots) * ~R t * ~S`   
  val th = RW [] (CONV_RULE (RATOR_CONV (SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL])) th)
  val th = ((Q.GEN `ax` o Q.GEN `roots`) th) 
  val th = MATCH_MP (Q.INST [`xs`|->`roots`] ADDRESS_LOOP3_RAW) th
  val th = SIMP_RULE std_ss [LENGTH,GSYM WORD_ADD_ASSOC,word_add_n2w,APPEND] th
  val th = Q.INST [`k`|->`0w-52w`] th
  val th = RW [] (CONV_RULE (RATOR_CONV (RAND_CONV EVAL)) th)
  val th = RW [EVAL ``0w-52w:word24``,STAR_ASSOC,uv_address_APPEND,APPEND] th
  val th = Q.INST [`roots`|->`[]`] th
  in th end;


(* ================ SWEEP STAGE =================== *)

val free_block_def = Define `
  free_block a b = M30 a b * ~M (a+1w) * ~M (a+2w) * ~M (a+3w) * cond ~(a = 0w)`;

val free_blocks_def = Define `
  (free_blocks [] = emp) /\
  (free_blocks [x] = free_block x 0w) /\
  (free_blocks (x::y::xs) = free_block x y * free_blocks (y::xs))`;

val free_list_def = Define ` 
  free_list' a xs = R30 a (if xs = [] then 0w else HD xs) * free_blocks xs`;

val fl_def = Define `
  fl' a xs = SEP_EXISTS ys. free_list' a ys * cond (PERM xs ys)`;

val fl_COMM = prove(
  ``!a xs ys. fl' a (xs ++ ys) = fl' a (ys ++ xs)``,
  SIMP_TAC bool_ss [fl_def,FUN_EQ_THM,SEP_EXISTS,cond_STAR]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `y`
  \\ IMP_RES_TAC APPEND_PERM_SYM \\ ASM_REWRITE_TAC []);

val SEP_IMP_DROP_COND = prove(
  ``!P g. SEP_IMP (P * cond g) P``,SIMP_TAC bool_ss [SEP_IMP_def,cond_STAR]);

val ARM_PROG_WEAKEN_COND = let
  val th = Q.INST [`Q'`|->`Q' * cond b`,`Q''`|->`Q'`] (SPEC_ALL ARM_PROG_WEAKEN_POST)
  in RW [SEP_IMP_DROP_COND] th end;

val ARM_PROG_WEAKEN1_COND = let
  val th = Q.INST [`Q`|->`Q * cond b`,`Q'`|->`Q`] (SPEC_ALL ARM_PROG_WEAKEN_POST1)
  in RW [SEP_IMP_DROP_COND] th end;

fun DROP_COND th = MATCH_MP ARM_PROG_WEAKEN_COND th;
fun DROP_COND1 th = MATCH_MP ARM_PROG_WEAKEN1_COND th;

val sweep1 = let
  val th = (*  ldr b, [i], #16    *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (16w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`b`,`b`|->`i`,`imm`|->`16w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  tst b, #1          *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x2` ] arm_TST1))) `x1*x2*x3*x4` `(x1*x4)*(x2*x3)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  streq a, [i,#-20]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (20w :word12) :word32)``] (Q.INST [`c_flag`|->`EQ`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`b`|->`i`,`imm`|->`20w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4` `(x2*x3)*(x1*x4)` `x1*x2*x3*x4*x5` `(x4*x2)*(x1*x3*x5)`
  val th = (*  subne b, b, #1     *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`NE`,`s_flag`|->`F`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x4` ] arm_SUB1))) `x1*x2*x3*x4*x5*x6` `(x4)*(x1*x2*x3*x5*x6)` `x1*x2` `(x1)*(x2)`
  val th = (*  subeq a, i, #20    *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (20w :word8) :word32)``] (Q.INST [`c_flag`|->`EQ`,`s_flag`|->`F`,`b`|->`a`,`a`|->`i`,`a_mode`|->`Imm 20w`,`x`|->`x5`,`y`|->`y5` ] arm_SUB2))) `x1*x2*x3*x4*x5*x6` `(x1*x2*x3)*(x4*x5*x6)` `x1*x2*x3*x4` `(x3*x2*x1)*(x4)`
  val th = (*  strne b, [i,#-16]  *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (16w :word12) :word32)``] (Q.INST [`c_flag`|->`NE`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`b`,`b`|->`i`,`imm`|->`16w`,`x`|->`x6`,`y`|->`y6`,`z`|->`z6` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4*x5*x6` `(x3)*(x1*x2*x4*x5*x6)` `x1*x2` `(x1)*(x2)`
  val th = ALIGN_VARS ["y1","x3"] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_PRE [`R b`] (AUTO_HIDE_POST1 [`R b`] th)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (Q.INST [`b'`|->`b`,`b''`|->`b`,`i'`|->`i`] th)
  val th = Q.INST [`y1`|->`ix + 1w`,`x3`|->`ax`] th
  val th = RW [GSYM WORD_ADD_ASSOC,WORD_ADD_SUB] th
  val th = RW [EVAL ``(1w + 4w) - 5w:word30``,WORD_ADD_SUB_ASSOC,WORD_ADD_0] th
  val th = RW [WORD_ADD_ASSOC] th
  val th = RW [addr32f_TEST] (Q.INST [`z1`|->`addr32f a1 b1`,`z3`|->`x`] th)
  val th = MOVE_PRE `M (ix + 1w)` (MOVE_PRE `M ix` th)
  val th = APP_FRAME `M (ix + 2w) (addr32f a2 b2) * M (ix + 3w) y * cond ~(ix = 0w)` th
  val th = MOVE_STAR_RULE `b*i*i1*(i2*i3*c)` `b*(i1*i2*i*i3*c)` th
  val th = RW [GSYM link_block_def] th
  val th = MOVE_POST1 `M ix` th
  val th = AUTO_HIDE_POST1 [`M (ix+1w)`,`M (ix+2w)`,`M (ix+3w)`] th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th 
  val th = MOVE_STAR_RULE `b*i*i1*i2*i3*c` `b*(i*i1*i2*i3*c)` th
  val th = RW [GSYM free_block_def,GSYM M30_def] th
  val th = MOVE_POST1 `R30 a` (MOVE_PRE `R30 a` th)
  val th = APP_FRAME `SEP_EXISTS ys. free_blocks ys * cond (PERM ys xs) * cond (ax = if ys = [] then 0w else HD ys)` th
  val th = RW1 [GSYM STAR_ASSOC] th
  val th = POST1_MOVE_STAR `b*f*(a*e)` `b*(f*a*e)` th
  val th = APP_PART_WEAKEN1 th `fl' a (ix::xs)`
    (SIMP_TAC (bool_ss++sep2_ss) [fl_def]
     \\ SIMP_TAC std_ss [SEP_EXISTS,cond_STAR,SEP_IMP_def] \\ REPEAT STRIP_TAC
     \\ Q.EXISTS_TAC `ix::y` \\ REWRITE_TAC [free_list_def,NOT_CONS_NIL,HD]
     \\ REWRITE_TAC [PERM_CONS_IFF] \\ ONCE_REWRITE_TAC [PERM_SYM]
     \\ ASM_REWRITE_TAC [] \\ Cases_on `y` 
     \\ FULL_SIMP_TAC (bool_ss++star_ss) [free_blocks_def,emp_STAR,NOT_CONS_NIL,HD]
     \\ METIS_TAC [])
  val th = EXISTS_PRE `ax` th
  val th = APP_STRENGTHEN th 
     `R30 i (ix + 1w) * ~S * ~R b *
      link_block (ix,a1,b1,a2,b2,x,y) * fl' a xs * cond ~b1`
    (SIMP_TAC (bool_ss++sep2_ss) [fl_def,free_list_def]
     \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR]
     \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [PERM_SYM]    
     \\ Q.EXISTS_TAC `y'` \\ ASM_REWRITE_TAC [])
  val th = APP_WEAKEN1 (APP_FRAME `cond ~b1` th)
    `(R30 i (ix + 1w + 4w) * ~S * ~R b *
     (if b1 then link_block (ix,a1,F,a2,b2,x,y) else emp) *
     fl' a (if b1 then xs else ix::xs))`
    (SIMP_TAC (bool_ss++sep2_ss) [SEP_IMP_MOVE_COND] 
     \\ SIMP_TAC (bool_ss++star_ss) [SEP_IMP_REFL])
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  in th end;

val sweep2 = let
  val th = (*  ldr b, [i], #16    *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (16w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := F; Up := T; Wb := T|>`,`a`|->`b`,`b`|->`i`,`imm`|->`16w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  tst b, #1          *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x2` ] arm_TST1))) `x1*x2*x3*x4` `(x1*x4)*(x2*x3)` `x1*x2` `(x1*x2)*(emp)`
  val th = (*  streq a, [i,#-20]  *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (20w :word12) :word32)``] (Q.INST [`c_flag`|->`EQ`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`b`|->`i`,`imm`|->`20w`,`x`|->`x3`,`y`|->`y3`,`z`|->`z3` ] arm_STR_NONALIGNED))) `x1*x2*x3*x4` `(x2)*(x1*x3*x4)` `x1*x2` `(x1)*(x2)`
  val th = (*  subne b, b, #1     *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`NE`,`s_flag`|->`F`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x4` ] arm_SUB1))) `x1*x2*x3*x4` `(x1*x2)*(x3*x4)` `x1*x2*x3` `(x2*x1)*(x3)`
  val th = (*  subeq a, i, #20    *) MOVE_COMPOSE th (SND_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (20w :word8) :word32)``] (Q.INST [`c_flag`|->`EQ`,`s_flag`|->`F`,`b`|->`a`,`a`|->`i`,`a_mode`|->`Imm 20w`,`x`|->`x5`,`y`|->`y5` ] arm_SUB2))) `x1*x2*x3*x4` `(x2)*(x1*x3*x4)` `x1*x2` `(x1)*(x2)`
  val th = ALIGN_VARS ["y1","x3"] th
  val th = Q.INST [`i'`|->`i`,`a'`|->`a`,`i''`|->`i`] th
  val tn = (*  strne b, [i,#-16]  *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (16w :word12) :word32)``] (Q.INST [`c_flag`|->`NE`,`opt`|->`<|Pre := T; Up := F; Wb := F|>`,`a`|->`b`,`b`|->`i`,`imm`|->`16w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_STR_NONALIGNED))
  val tn = Q.INST [`y1`|->`y1+4w`] (ALIGN_VARS ["y1"] tn)
  val tn = RW [WORD_ADD_SUB] tn
  val th = FRAME_COMPOSE th (MATCH_INST1 [`R b`,`S`,`M y1`] th tn)
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_PRE [`R b`] (AUTO_HIDE_POST1 [`R b`] th)
  val th = RW [WORD_ADD_SUB] (Q.INST [`y1`|->`ix + 1w`,`z1`|->`addr32f a1 b1`] th)  
  val th = RW [addr32f_TEST] th
  val th = APP_FRAME `M (ix + 2w) (addr32f a2 b2) * M ix x * M (ix + 3w) y * cond ~(ix = 0w) * cond b1` th
  val th = RW1 [GSYM STAR_ASSOC] (SIMP_RULE (bool_ss++sep2_ss) [] (MOVE_POST1 `M (ix+1w)` th))  
  val th = APP_PART_WEAKEN1 th `M (ix + 1w) (addr32f a1 F) * cond ~(ix = 0w)`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,addr32f_CLEAR,SEP_IMP_REFL])
  val th = MOVE_STAR_RULE `b*i2*i*i3*(i1*c)` `b*(i1*i2*i*i3*c)` th
  val th = RW [GSYM link_block_def] th
  val th = RW1 [GSYM STAR_ASSOC] (APP_FRAME `cond b1` th)
  val th = APP_PART_WEAKEN1 th `if b1 then link_block (ix,a1,F,a2,b2,x,y) else emp`
    (SIMP_TAC bool_ss [SEP_IMP_MOVE_COND,SEP_IMP_REFL])  
  val th = RW [STAR_ASSOC,GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond c``)] th
  val th = (MOVE_PRE `M(ix+1w)` o MOVE_PRE `M(ix+2w)` o MOVE_PRE `M(ix+3w)` o MOVE_PRE `M ix`) th
  val th = MOVE_STAR_RULE `b*c*b2*b1*i*i3*i2*i1` `b*b1*b2*(i1*i2*i*i3*c)` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] (RW [GSYM link_block_def] th)  
  val th = APP_FRAME `fl' a (if b1 then xs else ix::xs) * cond b1` th
  val th = APP_PART_STRENGTHEN th `fl' a xs * cond b1`
    (SIMP_TAC (bool_ss++sep_ss) [SEP_IMP_MOVE_COND,SEP_IMP_REFL])  
  val th = APP_PART_WEAKEN1 (RW [STAR_ASSOC] th) `emp`
    (SIMP_TAC std_ss [SEP_IMP_def,cond_def,emp_def])
  val th = SIMP_RULE (bool_ss++sep2_ss) [emp_STAR] th
  in th end;

val sweepN_def = Define `
  sweepN (ys:(word30 # bool # word30 # word30 # word32 # word32) list) = 
    (MAP FST o FILTER ($~ o FST o SND)) ys`;

val sweepP_def = Define `
  sweepP (ys:(word30 # bool # word30 # word30 # word32 # word32) list) = 
    (MAP (\(ix,b1,a1,a2,x,y). (ix,a1,a2,x,y)) o FILTER (FST o SND)) ys`;

val sweepQ_def = Define `
  sweepQ (ix,b1,a1,a2,x,y) = link_block (ix,a1,b1,a2,F,x,y)`;

val sweep3_inv_def = Define `
  sweep3_inv i b a ys ix =
    R30 i (ix + 1w) * ~R b * fl' a (sweepN ys) * unseen (sweepP ys)`;

val sweep3 = let
  val th = APP_MERGE sweep1 sweep2
  val th = SIMP_RULE (bool_ss++sep_ss) [DECIDE ``~b\/b:bool``] th
  val th = Q.INST [`b2`|->`F`] th
  val th = Q.INST [`xs`|->`sweepN ys`] th
  val th = APP_PART_WEAKEN1 th `fl' (a:word4) (sweepN ((ix,b1,a1,a2,x,y)::ys))`
    (Cases_on `b1` \\ SIMP_TAC std_ss [FILTER,MAP,sweepN_def,SEP_IMP_REFL])
  val th = APP_FRAME `unseen (sweepP ys)` th
  val th = POST1_MOVE_STAR `b*x*y*z` `b*y*(x*z)` th
  val th = APP_PART_WEAKEN1 th `unseen (sweepP ((ix,b1,a1,a2,x,y)::ys))`
    (Cases_on `b1` \\ SIMP_TAC std_ss [FILTER,MAP,sweepP_def,
      SEP_IMP_REFL,unseen_def,unseen1_def,STAR_LIST_def,emp_STAR])
  val th = RW [GSYM sweepQ_def] th
  val th = RW [GSYM sweep3_inv_def] (MOVE_PRE `sweepQ` (MOVE_PRE `S` th)) 
  val th = MOVE_PRE `S` (MOVE_PRE `sweep3_inv i b a ys` th)
  val lemma = METIS_PROVE [WORD_ADD_ASSOC,WORD_ADD_COMM] ``ix+1w+4w=(ix+4w)+1w``
  val th = RW [GSYM sweep3_inv_def] (RW1 [lemma] (MOVE_POST1 `S` th))
  val th = (PAIR_GEN "x" `(b1,a1,a2,x,y)` o Q.GEN `xs` o Q.INST [`ys`|->`xs`]) th
  val th = Q.GEN `ix` th
  in th end;

val ALL_DISTINCT_MAP_FST_EQ_FORALL = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) = !x y z ys zs qs. ~(xs = ys ++ (x,y)::zs ++ (x,z)::qs)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    FULL_SIMP_TAC bool_ss [ALL_DISTINCT_APPEND,MEM,MEM_APPEND,FST,MAP,MAP_APPEND]
    \\ METIS_TAC [],
    Induct_on `xs` \\ REWRITE_TAC [ALL_DISTINCT,MAP,FST] \\ REPEAT STRIP_TAC << [
      FULL_SIMP_TAC bool_ss [MEM_MAP]
      \\ FULL_SIMP_TAC bool_ss [MEM_EQ_APPEND] 
      \\ Cases_on `h` \\ Cases_on `y`
      \\ FULL_SIMP_TAC bool_ss [FST]
      \\ METIS_TAC [APPEND,APPEND_NIL], 
      METIS_TAC [CONS_11,APPEND]]]);

val STAR_LIST_CONTAINS_M_M = prove(
  ``!xs. 
      ~ALL_DISTINCT (MAP FST xs) ==> 
      ?i x y. SEP_CONTAINS (M i x * M i y) (STAR_LIST (MAP sweepQ xs))``,
  SIMP_TAC bool_ss [ALL_DISTINCT_MAP_FST_EQ_FORALL] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [MAP_APPEND,STAR_LIST_APPEND,MAP,STAR_LIST_def,SEP_CONTAINS_def]
  \\ Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`  
  \\ Cases_on `z` \\ Cases_on `r` \\ Cases_on `r''` \\ Cases_on `r`  
  \\ REWRITE_TAC [sweepQ_def,link_block_def]
  \\ MOVE_STAR_TAC `s*(m1*m2*m3*m4*c1*l1)*(n1*n2*n3*n4*c2*l2)` 
                   `m1*n1*(s*(m2*m3*m4*c1*l1)*(n2*n3*n4*c2*l2))`
  \\ METIS_TAC []);

val NOT_CONTAINS_M_M = prove(
  ``(~g ==> ?i x y. SEP_CONTAINS (M i x * M i y) Q) ==>
    ARM_PROG (P * Q * cond g) code C Q' Z ==> ARM_PROG (P * Q) code C Q' Z``,
  Cases_on `g` \\ SIMP_TAC (bool_ss++sep_ss) [ARM_PROG_FALSE_PRE]
  \\ REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC (RW [] ARM_PROG_CONTAINS_M_STAR_M)
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ FULL_SIMP_TAC bool_ss [SEP_CONTAINS_def,GSYM STAR_ASSOC]
  \\ Q.EXISTS_TAC `F' * P` \\ SIMP_TAC (bool_ss++star_ss) []);

val sweep4 = let
  val th = Q.INST [`a`|->`c`] ARM_PROG_ARRAY_LOOP
  val th = MATCH_MP th sweep3
  val th = RW [APPEND,LENGTH] th  
  val lemma = METIS_PROVE [APPEND_PERM_SYM] 
              ``!xs ys zs. PERM (xs ++ ys) zs = PERM (ys ++ xs) zs``
  val goal = (fst o dest_imp o concl) th
  val th1 = prove(goal,
    SIMP_TAC std_ss [sweep3_inv_def,FUN_EQ_THM,sweepP_def,FILTER_APPEND,MAP_APPEND,
                     unseen_def,STAR_LIST_APPEND,sweepN_def,fl_def]
    \\ REPEAT STRIP_TAC \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [lemma]))
    \\ SIMP_TAC (bool_ss++star_ss) [])
  val th = MATCH_MP th th1 
  val th = Q.INST [`offset`|->`0w-9w`] th
  val th = MP (CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th) TRUTH
  val th = RW [EVAL ``0w-9w:word24``] th
  val th = RW [GSYM (REWRITE_CONV [SEP_cond_CLAUSES] ``cond b * cond g``),STAR_ASSOC] th
  val th = PRE_MOVE_STAR `ss*sl*c*s*c1*c2*c3` `ss*c*s*c1*c3*sl*c2` th
  val th1 = MATCH_MP NOT_CONTAINS_M_M (SPEC_ALL STAR_LIST_CONTAINS_M_M)
  val th = MATCH_MP th1 th
  val th = PRE_MOVE_STAR `ss*c*s*c1*c3*sl` `ss*sl*c*s*c1*c3` th
  val th = SIMP_RULE (bool_ss++sep2_ss) [] th
  in th end;

val sweepP_NIL = prove(
  ``(sweepN [] = []) /\ (sweepP [] = [])``,
  SIMP_TAC std_ss [sweepP_def,sweepN_def,FILTER,MAP]);

val fl_NIL = prove(
  ``!a. fl' a [] = R30 a 0w``,
  SIMP_TAC std_ss [fl_def,FUN_EQ_THM,SEP_EXISTS_THM,cond_STAR,PERM_NIL] 
  \\ REWRITE_TAC [free_list_def,free_blocks_def,emp_STAR]);

val sweepB_def = Define `sweepB (b:bool) = 
  MAP (\x. (FST x,b,SND (x:word30 # word30 # word30 # word32 # word32)))`;

val MAP_FST_sweepB = prove(
  ``!xs ys. MAP FST (sweepB T xs ++ sweepB F ys) = MAP FST (xs ++ ys)``,
  Induct THEN1 (Induct \\ FULL_SIMP_TAC std_ss [sweepB_def,MAP,MAP_APPEND,APPEND])
  \\ FULL_SIMP_TAC std_ss [sweepB_def,MAP,MAP_APPEND,APPEND]);

val sweepB_unseen_visited = prove(
  ``!xs. (STAR_LIST (MAP sweepQ (sweepB T xs)) = visited xs) /\ 
         (STAR_LIST (MAP sweepQ (sweepB F xs)) = unseen xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [visited_def,sweepB_def,MAP,STAR_LIST_def,unseen_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ REWRITE_TAC [visited1_def,sweepQ_def,FST,SND,unseen1_def]);

val sweepN_sweepB = prove(
  ``!xs ys. (sweepN (sweepB T xs ++ sweepB F ys) = MAP FST ys) /\
            (sweepP (sweepB T xs ++ sweepB F ys) = xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [sweepN_def,sweepP_def,sweepB_def,MAP,APPEND,FILTER] 
  \\ Induct \\ FULL_SIMP_TAC std_ss [sweepN_def,sweepB_def,MAP,APPEND,FILTER]);
  
val sweep_loop = let
  val th = RW [sweep3_inv_def,sweepP_NIL,unseen_def,MAP,STAR_LIST_def,fl_NIL] sweep4
  val th = RW [GSYM R30_def] (AUTO_HIDE_POST1 [`R i`] (RW [R30_def,emp_STAR] th))
  val th = Q.INST [`xs`|->`sweepB T xs ++ sweepB F ys`] th    
  val th = RW [sweepB_unseen_visited,MAP_FST_sweepB,MAP_APPEND,STAR_LIST_APPEND] th
  val th = RW [sweepN_sweepB,GSYM unseen_def,STAR_ASSOC] th
  val th = RW [GSYM MAP_APPEND] th
  in th end;


(* ================ MARK & SWEEP JOINED =================== *)

val PERM_FILTER_NOT_FILTER = prove(
  ``!xs g. PERM (FILTER g xs ++ FILTER (\x. ~(g x)) xs) xs``,
  Induct \\ ASM_SIMP_TAC std_ss [PERM_NIL,FILTER,APPEND] \\ REPEAT STRIP_TAC
  \\ Cases_on `g h` \\ ASM_REWRITE_TAC [APPEND,PERM_CONS_IFF]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ ASM_REWRITE_TAC [APPEND,PERM_CONS_IFF]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ ASM_REWRITE_TAC []);

val FILTER_MEM = (SIMP_RULE bool_ss [] o Q.SPECL [`xs`,`xs`] o prove)(
  ``!xs ys. (!x. MEM x xs ==> MEM x ys) ==> (FILTER (\x. MEM x ys) xs = xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [FILTER,MEM]);

val FILTER_MEM_SELF = prove(
  ``!xs. FILTER (\x. MEM x (FILTER g xs)) xs = FILTER g xs``,
  REWRITE_TAC [MEM_FILTER] 
  \\ ONCE_REWRITE_TAC [GSYM (BETA_CONV ``(\x. MEM x xs) x``)]
  \\ REWRITE_TAC [GSYM FILTER_FILTER,FILTER_MEM]);

val PERM_MEM_FILTER =  
  (SIMP_RULE std_ss [FILTER_MEM_SELF] o 
   Q.SPECL [`xs`,`(\x. MEM x (FILTER g xs))`]) PERM_FILTER_NOT_FILTER;

val PERM_MAP = prove(
  ``!f xs ys. PERM xs ys ==> PERM (MAP f xs) (MAP f ys)``,
  STRIP_TAC \\ Induct \\ SIMP_TAC bool_ss [PERM_NIL,PERM_REFL,PERM_CONS_EQ_APPEND]
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [MAP_APPEND,MAP]
  \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ ASM_REWRITE_TAC [APPEND,PERM_CONS_IFF]
  \\ MATCH_MP_TAC APPEND_PERM_SYM \\ REWRITE_TAC [GSYM MAP_APPEND]
  \\ ONCE_REWRITE_TAC [PERM_SYM] \\ METIS_TAC []);

val PERM_reachables = prove(
  ``!xs. PERM (reachables' rs xs ++ unreachables' rs xs) xs``,
  REWRITE_TAC [reachables'_def,unreachables'_def,PERM_MEM_FILTER]);

val PERM_REWRITE = let 
  val th1 = MATCH_MP (Q.ISPEC `FST` PERM_MAP) (SPEC_ALL PERM_reachables)
  val th2 = METIS_PROVE [PERM_SYM,PERM_TRANS] 
            ``!xs ys. PERM xs ys ==> (PERM xs zs = PERM ys zs)``
  in MATCH_MP th2 th1 end;

val blank_def = Define `
  (blank a 0 = emp) /\
  (blank a (SUC n) = ~ M a * blank (a-1w) n)`;

val STACK_def = Define `
  STACK a xs n = R30 13w a * ms a xs * blank (a-1w) n`;

val FILTER_F = prove(
  ``!xs. (FILTER (\x.F) xs = []) /\ (FILTER (\x.T) xs = xs)``,
  Induct \\ ASM_REWRITE_TAC [FILTER]);

val reachables'_NIL = prove(
  ``!xs. (unreachables' [] xs = xs) /\ (reachables' [] xs = [])``,
  REWRITE_TAC [unreachables'_def,reachables'_def,is_reachable'_def,MEM,FILTER_F]);

val mark_and_sweep1 = let
  val th1 = SIMP_RULE (bool_ss++sep_ss) [uv_def,uvs_def,stack_def] uv_loop
  val th2 = Q.INST [`a`|->`p`,`b`|->`a2`,`c`|->`a1`,`i`|->`t`] sweep_loop
  val th2 = Q.INST [`xs`|->`reachables' [cx; bx; ax] xs`,
                   `ys`|->`unreachables' [cx; bx; ax] xs`] th2
  val th2 = RW [PERM_REWRITE] th2
  val th2 = RW [GSYM R30_def] (AUTO_HIDE_POST1 [`R a1`] (RW [R30_def] th2))
  (* make_spec ["ldr t,[sp]","ldr a1,[sp,#4]","sub a,a,#1","sub b,b,#1","sub c,c,#1","add t,t,#4"] *)
  val th = (*  ldr t,[sp]      *) FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (0w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`t`,`b`|->`13w`,`imm`|->`0w`,`x`|->`x1`,`y`|->`y1`,`z`|->`z1` ] arm_LDR_NONALIGNED))
  val th = (*  ldr a1,[sp,#4]  *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word12) :word32)``] (Q.INST [`c_flag`|->`AL`,`opt`|->`<|Pre := T; Up := T; Wb := F|>`,`a`|->`a1`,`b`|->`13w`,`imm`|->`4w`,`x`|->`x2`,`y`|->`y2`,`z`|->`z2` ] arm_LDR_NONALIGNED))) `x1*x2*x3*x4` `(x2*x4)*(x1*x3)` `x1*x2*x3*x4` `(x2*x4)*(x1*x3)`
  val th = (*  sub a,a,#1      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a_mode`|->`Imm 1w`,`x`|->`x3` ] arm_SUB1))) `x1*x2*x3*x4*x5*x6` `(x4)*(x1*x2*x3*x5*x6)` `x1*x2` `(x2)*(x1)`
  val th = (*  sub b,b,#1      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`b`,`a_mode`|->`Imm 1w`,`x`|->`x4` ] arm_SUB1))) `x1*x2*x3*x4*x5*x6*x7` `(x2)*(x1*x3*x4*x5*x6*x7)` `x1*x2` `(x2)*(x1)`
  val th = (*  sub c,c,#1      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (1w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`c`,`a_mode`|->`Imm 1w`,`x`|->`x5` ] arm_SUB1))) `x1*x2*x3*x4*x5*x6*x7*x8` `(x2)*(x1*x3*x4*x5*x6*x7*x8)` `x1*x2` `(x2)*(x1)`
  val th = (*  add t,t,#4      *) MOVE_COMPOSE th (FST_PROG2 (SIMP_RULE (bool_ss++armINST_ss) [EVAL ``(w2w (4w :word8) :word32)``] (Q.INST [`c_flag`|->`AL`,`s_flag`|->`F`,`a`|->`t`,`a_mode`|->`Imm 4w`,`x`|->`x6` ] arm_ADD1))) `x1*x2*x3*x4*x5*x6*x7*x8*x9` `(x2*x8)*(x1*x3*x4*x5*x6*x7*x9)` `x1*x2` `(x2*x1)*(emp)`
  val th = ALIGN_VARS ["y1","z1","z2"] (AUTO_HIDE_STATUS th)
  val th = AUTO_HIDE_PRE [`R t`,`R a1`] th
  val th = Q.INST [`y1`|->`sp`,`z1`|->`y`,`z2`|->`n`] th
  val th = foldl (uncurry MOVE_POST1) th [`R30 13w`,`M sp`,`M (sp+1w)`]
  val th = foldl (uncurry MOVE_PRE) th [`R30 13w`,`M sp`,`M (sp+1w)`]
  val th = MOVE_STAR_RULE `b*sp*m1*m2` `b*(sp*m1*m2)` th
  val lemma = REWRITE_CONV [STACK_def,ms_def,emp_STAR,blank_def,STAR_ASSOC] ``STACK a [x;y] 0``
  val th = RW [GSYM lemma] th  
  val th = FRAME_COMPOSE th1 (MATCH_INST1 [`R a`,`R b`,`R c`] th1 th)
  val th = RW [addr32f_CLEAR,GSYM addr32f_INTRO,GSYM R30_def] th
  val th = FRAME_COMPOSE th th2
  val th = Q.INST [`t`|->`t1`,`a1`|->`t2`,`a2`|->`t3`] th
  val th = RW [reachables'_NIL,visited_def,STAR_LIST_def,MAP,emp_STAR] th  
  in th end;

val IN_list2range_EQ_list2edges = prove( 
  ``!xs x. x IN list2range xs = ?y. (y,x) IN list2edges xs``,
  Induct \\ REWRITE_TAC [list2edges_def,list2range_def,NOT_IN_EMPTY]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ REWRITE_TAC [list2edges_def,list2range_def,NOT_IN_EMPTY,IN_INSERT]
  \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])

val IN_list2domain_EQ_list2edges = prove( 
  ``!xs x. x IN list2domain xs = ?y. (x,y) IN list2edges xs``,
  Induct \\ REWRITE_TAC [list2edges_def,list2domain_def,NOT_IN_EMPTY]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ REWRITE_TAC [list2edges_def,list2domain_def,NOT_IN_EMPTY,IN_INSERT]
  \\ ASM_REWRITE_TAC [PAIR_EQ] \\ METIS_TAC [])

val IMP_IN_list2domain = prove(
  ``!xs x y. MEM y xs /\ (FST y = x) ==> x IN list2domain xs``,
  REWRITE_TAC [IN_list2domain,MEM_MAP] \\ METIS_TAC [])
 
val IN_list2edges_EQ_MEM = prove(
  ``!xs. (x,y) IN list2edges xs = ?t u v. MEM (x,y,t,u,v) xs \/ MEM (x,t,y,u,v) xs``,
  Induct \\ REWRITE_TAC [list2edges_def,MEM,NOT_IN_EMPTY]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ ASM_REWRITE_TAC [list2edges_def,PAIR_EQ,NOT_IN_EMPTY,IN_INSERT]
  \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val IN_list2edges_reachables' = prove(
  ``!xs. (x,y) IN list2edges (reachables' roots xs) = 
         (x,y) IN list2edges xs /\ ?z. MEM z roots /\ is_reachable (list2edges xs) z x``,
  SIMP_TAC bool_ss [IN_list2edges_EQ_MEM,reachables'_def,MEM_FILTER,FST]
  \\ REWRITE_TAC [is_reachable'_def] \\ METIS_TAC []);
   
val SEP_IMP_connect_connect_lemma = prove(
  ``x IN list2range (reachables' ys xs) /\ MEM y xs /\ (FST y = x) ==>
    x IN list2domain (reachables' ys xs)``,
  REWRITE_TAC [IN_list2domain_EQ_list2edges,IN_list2range_EQ_list2edges]
  \\ REPEAT STRIP_TAC
  \\ `x IN list2domain xs` by (ASM_REWRITE_TAC [IN_list2domain,MEM_MAP] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC bool_ss [IN_list2domain_EQ_list2edges,IN_list2edges_reachables']
  \\ `is_reachable (list2edges xs) y' x` by 
    (REWRITE_TAC [is_reachable_def] \\ DISJ2_TAC
     \\ Q.EXISTS_TAC `[]` \\ ASM_REWRITE_TAC [is_path_def])
  \\ Q.EXISTS_TAC `y''` \\ ASM_REWRITE_TAC []
  \\ Q.EXISTS_TAC `z` \\ ASM_REWRITE_TAC []
  \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] is_reachable_TRANS))
  \\ Q.EXISTS_TAC `y'` \\ ASM_REWRITE_TAC [])
  
val SEP_IMP_connect_connect = prove(
  ``SEP_IMP (connect (unreachables' ys xs) (reachables' ys xs) 0w 0w []) 
            (connect [] (reachables' ys xs) 0w 0w [])``,
  REWRITE_TAC [connect_def,SEP_IMP_cond,range_def,domain_def]
  \\ REWRITE_TAC [stack2list_def,list2range_def,list2domain_def,UNION_EMPTY]
  \\ REWRITE_TAC [SUBSET_DEF,IN_UNION,IN_INSERT,NOT_IN_EMPTY] 
  \\ REPEAT STRIP_TAC
  \\ `x IN list2domain (unreachables' ys xs) \/
      x IN list2domain (reachables' ys xs) \/ (x = 0w)` by METIS_TAC []
  \\ ASM_REWRITE_TAC []
  \\ `?y. MEM y xs /\ (FST y = x) /\ ~MEM y (reachables' ys xs)` by
     (FULL_SIMP_TAC bool_ss [IN_list2domain,MEM_MAP,unreachables'_def,MEM_FILTER]      
      \\ Q.EXISTS_TAC `y` \\ ASM_REWRITE_TAC []) 
  \\ DISJ1_TAC \\ IMP_RES_TAC SEP_IMP_connect_connect_lemma);
  
val mark_and_sweep2 = let
  val th = APP_PART_WEAKEN1 mark_and_sweep1 
    `connect [] (reachables' [cx; bx; ax] xs) 0w 0w []`
    (REWRITE_TAC [SEP_IMP_connect_connect])
  in th end;

val _ = save_thm("mark_and_sweep",mark_and_sweep2);

val _ = export_theory();

