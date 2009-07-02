
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory listTheory opmonTheory combinTheory;

open x86_coretypesTheory;

val _ = new_theory "x86_seq_monad";


val _ = Hol_datatype `x86_permission = Xread | Xwrite | Xexecute`;

val _ = type_abbrev("x86_memory",``: word32 -> ((word8 # x86_permission set) option)``);

val _ = type_abbrev("x86_state",   (*  state = tuple consisting of:       *) 
  ``: (Xreg -> word32) #           (*  - general-purpose 32-bit registers *)
      (word32) #                   (*  - eip                              *)
      (Xeflags -> bool option) #   (*  - eflags                           *)
      x86_memory #                 (*  - unsegmented memory               *)
      x86_memory                   (*  - instruction cache                *) ``); 

(* functions for reading/writing state *)

val XREAD_REG_def   = Define `XREAD_REG     x ((r,p,s,m,i):x86_state) = r x `;
val XREAD_EIP_def   = Define `XREAD_EIP       ((r,p,s,m,i):x86_state) = p `;
val XREAD_EFLAG_def = Define `XREAD_EFLAG   x ((r,p,s,m,i):x86_state) = s x `;

val XREAD_MEM_def = Define `
  XREAD_MEM x ((r,p,s,m,i):x86_state) = 
    case m x of
       NONE -> NONE
    || SOME (w,perms) -> if Xread IN perms then SOME w else NONE`;

val XREAD_INSTR_def = Define `
  XREAD_INSTR x ((r,p,s,m,i):x86_state) = 
    case (i x, m x) of
       (NONE, NONE) -> NONE
    || (NONE, SOME (w,perms)) -> if {Xread;Xexecute} SUBSET perms then SOME w else NONE
    || (SOME (w,perms), _) -> if {Xread;Xexecute} SUBSET perms then SOME w else NONE`;

val X86_ICACHE_EMPTY_def = Define `X86_ICACHE_EMPTY = (\addr. NONE):x86_memory`;
 
val XCLEAR_ICACHE_def = Define `
  XCLEAR_ICACHE ((r,p,s,m,i):x86_state) = (r,p,s,m,X86_ICACHE_EMPTY):x86_state`;

val XWRITE_REG_def   = Define `XWRITE_REG   x y ((r,p,s,m,i):x86_state) = ((x =+ y) r,p,s,m,i):x86_state `;
val XWRITE_EIP_def   = Define `XWRITE_EIP     y ((r,p,s,m,i):x86_state) = (r,y,s,m,i):x86_state `;
val XWRITE_EFLAG_def = Define `XWRITE_EFLAG x y ((r,p,s,m,i):x86_state) = (r,p,(x =+ y) s,m,i):x86_state `;

val XWRITE_MEM_def   = Define `
  XWRITE_MEM x y ((r,p,s,m,i):x86_state) = 
    case m x of
       NONE -> NONE
    || SOME (w,perms) -> if Xwrite IN perms then SOME ((r,p,s,(x =+ SOME (y,perms)) m,i):x86_state) else NONE`;

val XREAD_MEM_BYTES_def = Define `
  XREAD_MEM_BYTES n a s = 
    if n = 0 then [] else XREAD_MEM a s :: XREAD_MEM_BYTES (n-1) (a+1w) s`;

val XREAD_INSTR_BYTES_def = Define `
  XREAD_INSTR_BYTES n a s = 
    if n = 0 then [] else XREAD_INSTR a s :: XREAD_INSTR_BYTES (n-1) (a+1w) s`;

val w2bits_EL = store_thm("w2bits_EL",
  ``(w2bits (w:word8) ++ ys = x1::x2::x3::x4::x5::x6::x7::x8::xs) =
    (EL 0 (w2bits (w:word8)) = x1) /\
    (EL 1 (w2bits (w:word8)) = x2) /\
    (EL 2 (w2bits (w:word8)) = x3) /\
    (EL 3 (w2bits (w:word8)) = x4) /\
    (EL 4 (w2bits (w:word8)) = x5) /\
    (EL 5 (w2bits (w:word8)) = x6) /\
    (EL 6 (w2bits (w:word8)) = x7) /\
    (EL 7 (w2bits (w:word8)) = x8) /\ (ys = xs)``,
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2bits_def]
  THEN NTAC 9 (ONCE_REWRITE_TAC [n2bits_def] THEN SIMP_TAC std_ss [CONS_11])
  THEN SIMP_TAC std_ss [APPEND,CONS_11,EL,rich_listTheory.EL_CONS,HD]); 

val expand_mem_read_bytes =
 (ONCE_REWRITE_CONV [XREAD_MEM_BYTES_def,word2bytes_def] THENC 
  ONCE_REWRITE_CONV [XREAD_MEM_BYTES_def,word2bytes_def] THENC 
  ONCE_REWRITE_CONV [XREAD_MEM_BYTES_def,word2bytes_def] THENC 
  ONCE_REWRITE_CONV [XREAD_MEM_BYTES_def,word2bytes_def] THENC 
  ONCE_REWRITE_CONV [XREAD_MEM_BYTES_def,word2bytes_def] THENC 
  SIMP_CONV std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,ASR_ADD])

val XREAD_MEM_BYTES_thm = save_thm("XREAD_MEM_BYTES_thm",
   CONJ (expand_mem_read_bytes ``XREAD_MEM_BYTES 1 a s``)
  (CONJ (expand_mem_read_bytes ``XREAD_MEM_BYTES 2 a s``)
        (expand_mem_read_bytes ``XREAD_MEM_BYTES 4 a s``)));

val word2bytes_thm = save_thm("word2bytes_thm",
   CONJ (expand_mem_read_bytes ``word2bytes 1 w``)
  (CONJ (expand_mem_read_bytes ``word2bytes 2 w``)
        (expand_mem_read_bytes ``word2bytes 4 w``)));

val EL_thm = save_thm("EL_thm",
  CONJ (EVAL ``EL 0 ((x0:'a)::xs)``)
 (CONJ (EVAL ``EL 1 ((x0:'a)::x2::xs)``) 
 (CONJ (EVAL ``EL 2 ((x0:'a)::x2::x3::xs)``) 
       (EVAL ``EL 3 ((x0:'a)::x2::x3::x4::xs)``))))


(* ---------------------------------------------------------------------------------- *>

  We define a state and monads for constructing a sequential version of the semantics.

<* ---------------------------------------------------------------------------------- *)

(* val _ = type_abbrev("Xstate",``:x86_state -> ('a # x86_state) option``); *)

val _ = type_abbrev("x86_M",``:x86_state -> ('a # x86_state) option``); 


(* sequential monads for an option state *)

val constT_seq_def = Define `
  (constT_seq: 'a -> 'a x86_M) x = \y. SOME (x,y)`;

val addT_seq_def = Define `
  (addT_seq: 'a -> 'b x86_M -> ('a # 'b) x86_M) x s = 
    \y. case s y of NONE -> NONE || SOME (z,t) -> SOME ((x,z),t)`;

val lockT_seq_def = Define `
  (lockT_seq: 'a x86_M -> 'a x86_M) s = s`;

val failureT_seq_def = Define `
  (failureT_seq: 'a x86_M) = \y. NONE`;

val seqT_seq_def = Define `
  (seqT_seq: 'a x86_M -> ('a -> 'b x86_M) -> 'b x86_M) s f = 
    \y. case s y of NONE -> NONE || SOME (z,t) -> f z t`;

val parT_seq_def = Define `
  (parT_seq: 'a x86_M -> 'b x86_M -> ('a # 'b) x86_M) s t = 
    \y. case s y of NONE -> NONE || SOME (a,z) -> 
        case t z of NONE -> NONE || SOME (b,x) -> SOME ((a,b),x)`;

val parT_unit_seq_def = Define `
  (parT_unit_seq: unit x86_M -> unit x86_M -> unit x86_M) s t = 
    \y. case s y of NONE -> NONE || SOME (a,z) -> 
        case t z of NONE -> NONE || SOME (b,x) -> SOME ((),x)`;

(* register reads/writes always succeed. *)

val write_reg_seq_def = Define `(write_reg_seq ii r x):unit x86_M = 
  \s. SOME ((),XWRITE_REG r x s)`;

val read_reg_seq_def = Define `(read_reg_seq ii r):Ximm x86_M = 
  \s. SOME (XREAD_REG r s,s)`;

(* eflags can always be written, but reading a NONE eflag causes a failure *)

val write_eflag_seq_def = Define `(write_eflag_seq ii f x):unit x86_M = 
  (\s. SOME ((),XWRITE_EFLAG f x s))`;

val read_eflag_seq_def  = Define `(read_eflag_seq ii f):bool x86_M = 
  (\s. case XREAD_EFLAG f s of NONE -> NONE || SOME b -> SOME (b,s))`;

(* eip reads/writes always succeed. *)

val write_eip_seq_def = Define `(write_eip_seq ii x):unit x86_M = 
  \s. SOME ((),XWRITE_EIP x s)`;

val read_eip_seq_def = Define `(read_eip_seq ii):Ximm x86_M = 
  \s. SOME (XREAD_EIP s,s)`;

(* memory writes are only allowed to modelled memory, i.e. locations containing SOME ... *)

val write_mem_seq_def   = Define `(write_mem_seq ii a x):unit x86_M = 
  (\s. case XWRITE_MEM a x s of NONE -> NONE || SOME s2 -> SOME ((),s2))`;

(* a memory read to an unmodelled memory location causes a failure *)

val read_mem_seq_def  = Define `(read_mem_seq ii a):word8 x86_M = 
  (\s. case XREAD_MEM a s of NONE -> NONE || SOME x -> SOME (x,s))`;

(* reading and writing 32-bit entities *)

val read_m32_seq_def = Define `(read_m32_seq ii a):Ximm x86_M =
  seqT_seq (parT_seq (read_mem_seq ii (a+0w)) (parT_seq (read_mem_seq ii (a+1w)) 
           (parT_seq (read_mem_seq ii (a+2w)) (read_mem_seq ii (a+3w)))))
       (\(x0,x1,x2,x3). constT_seq (bytes2word [x0;x1;x2;x3]))`;

val write_m32_seq_def = Define `(write_m32_seq ii a w):unit x86_M =
    (let bs = word2bytes 4 w in
       parT_unit_seq (write_mem_seq ii (a+0w) (EL 0 bs)) (parT_unit_seq (write_mem_seq ii (a+1w) (EL 1 bs)) 
      (parT_unit_seq (write_mem_seq ii (a+2w) (EL 2 bs)) (write_mem_seq ii (a+3w) (EL 3 bs)))))`;

val read_m8_seq_def = Define `(read_m8_seq ii a):word8 x86_M =
  read_mem_seq ii a`;

val write_m8_seq_def = Define `(write_m8_seq ii a w):unit x86_M =
    write_mem_seq ii a (w:word8)`;

(* clear the icache *)

val clear_icache_seq_def = Define `(clear_icache_seq ii):unit x86_M = 
  \s. SOME ((),XCLEAR_ICACHE s)`;


(* export *)

val _ = Define `(constT: 'a -> 'a x86_M)                                     = constT_seq`;
val _ = Define `(addT: 'a -> 'b x86_M -> ('a # 'b) x86_M)                    = addT_seq`;
val _ = Define `(lockT: unit x86_M -> unit x86_M)                            = lockT_seq`;
val _ = Define `(failureT: unit x86_M)                                       = failureT_seq`;
val _ = Define `(seqT: 'a x86_M -> (('a -> 'b x86_M) -> 'b x86_M))           = seqT_seq`;
val _ = Define `(parT: 'a x86_M -> 'b x86_M -> ('a # 'b) x86_M)              = parT_seq`;
val _ = Define `(parT_unit: unit x86_M -> unit x86_M -> unit x86_M)          = parT_unit_seq`;
val _ = Define `(write_reg: iiid -> Xreg -> Ximm -> unit x86_M)              = write_reg_seq`;
val _ = Define `(read_reg: iiid -> Xreg -> Ximm x86_M)                       = read_reg_seq`;
val _ = Define `(write_eip: iiid -> Ximm -> unit x86_M)                      = write_eip_seq`;
val _ = Define `(read_eip: iiid -> Ximm x86_M)                               = read_eip_seq`;
val _ = Define `(write_eflag: iiid -> Xeflags -> bool option -> unit x86_M)  = write_eflag_seq`;
val _ = Define `(read_eflag: iiid -> Xeflags -> bool x86_M)                  = read_eflag_seq`;
val _ = Define `(write_m32: iiid -> Ximm -> Ximm-> unit x86_M)               = write_m32_seq`;
val _ = Define `(read_m32: iiid -> Ximm -> Ximm x86_M)                       = read_m32_seq`;
val _ = Define `(write_m8: iiid -> Ximm -> word8 -> unit x86_M)              = write_m8_seq`;
val _ = Define `(read_m8: iiid -> Ximm -> word8 x86_M)                       = read_m8_seq`;
val _ = Define `(clear_icache: iiid -> unit x86_M)                           = clear_icache_seq`;



(* some rewriter-friendly theorems *)

val option_apply_def = Define `
  option_apply x f = if x = NONE then NONE else f (THE x)`;

val option_apply_SOME = prove(
  ``!x f. option_apply (SOME x) f = f x``,SRW_TAC [] [option_apply_def]);

val XWRITE_MEM2_def = Define `
  XWRITE_MEM2 a w ((r,e,t,m,i):x86_state) = (r,e,t,(a =+ SOME (w, SND (THE (m a)))) m,i)`;

val XREAD_MEM2_def = Define `
  XREAD_MEM2 a ((r,e,t,m,i):x86_state) = FST (THE (m a))`;

val XREAD_MEM2_WORD_def = Define `
  XREAD_MEM2_WORD a (s:x86_state) = (bytes2word
    [XREAD_MEM2 (a + 0x0w) s; XREAD_MEM2 (a + 0x1w) s; 
     XREAD_MEM2 (a + 0x2w) s; XREAD_MEM2 (a + 0x3w) s]) :word32`;  

val XWRITE_MEM2_WORD_def = Define `
  XWRITE_MEM2_WORD a (w:word32) (s:x86_state) =
    XWRITE_MEM2 (a + 3w) (EL 3 (word2bytes 4 w)) 
   (XWRITE_MEM2 (a + 2w) (EL 2 (word2bytes 4 w))
   (XWRITE_MEM2 (a + 1w) (EL 1 (word2bytes 4 w)) 
   (XWRITE_MEM2 (a + 0w) (EL 0 (word2bytes 4 w)) s)))`;

val CAN_XWRITE_MEM_def = Define `
  CAN_XWRITE_MEM a s = !w. ~(XWRITE_MEM a w s = NONE)`;

val CAN_XREAD_MEM_def = Define `
  CAN_XREAD_MEM a s = ~(XREAD_MEM a s = NONE)`;

val mem_seq_lemma = prove(
  ``(read_mem_seq ii a s = option_apply (XREAD_MEM a s) (\x. SOME (x,s))) /\ 
    (write_mem_seq ii a y s = option_apply (XWRITE_MEM a y s) (\s. SOME ((),s)))``,
  SRW_TAC [] [option_apply_def,read_mem_seq_def,write_mem_seq_def] 
  THEN Cases_on `XREAD_MEM a s` THEN FULL_SIMP_TAC std_ss [] 
  THEN Cases_on `XWRITE_MEM a y s` THEN FULL_SIMP_TAC std_ss []);

val read_eflag_seq_lemma = prove(
  ``read_eflag_seq ii f s = option_apply (XREAD_EFLAG f s) (\x. SOME (x,s))``,
  SRW_TAC [] [option_apply_def,read_eflag_seq_def] 
  THEN Cases_on `XREAD_EFLAG f s` THEN FULL_SIMP_TAC std_ss []);
  
val parT_unit_seq_lemma = prove(
  ``(parT_unit_seq s t = \y. option_apply (s y) (\z.
                             option_apply (t (SND z)) (\x. SOME ((),SND x))))``,
  SRW_TAC [] [parT_unit_seq_def,FUN_EQ_THM,option_apply_def] THEN Cases_on `s y`
  THEN SRW_TAC [] [parT_unit_seq_def,FUN_EQ_THM,option_apply_def] THEN Cases_on `x`
  THEN SRW_TAC [] [parT_unit_seq_def,FUN_EQ_THM,option_apply_def]
  THEN FULL_SIMP_TAC std_ss [] THEN Cases_on `t r`
  THEN SRW_TAC [] [parT_unit_seq_def,FUN_EQ_THM,option_apply_def] THEN Cases_on `x`  
  THEN SRW_TAC [] [parT_unit_seq_def,FUN_EQ_THM,option_apply_def]); 

val monad_simp_lemma = prove(
  ``(constT_seq x = \y. SOME (x,y)) /\ (failureT_seq = \y. NONE) /\  (lockT_seq d = d) /\
    (addT_seq q s = \y. option_apply (s y) (\t. SOME ((q,FST t),SND t))) /\
    (seqT_seq s f = \y. option_apply (s y) (\t. f (FST t) (SND t))) /\
    (parT_seq s t = \y. option_apply (s y) (\z.
                    option_apply (t (SND z)) (\x. SOME ((FST z,FST x),SND x))))``,
  SRW_TAC [] [parT_seq_def,seqT_seq_def,failureT_seq_def,lockT_seq_def,
                   addT_seq_def,constT_seq_def,FUN_EQ_THM]
  THEN Cases_on `s y` THEN POP_ASSUM MP_TAC THEN SRW_TAC [] [option_apply_def]
  THEN Cases_on `x` THEN POP_ASSUM MP_TAC THEN SRW_TAC [] [option_apply_def]
  THEN Cases_on `t r` THEN SRW_TAC [] [option_apply_def] THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `x` THEN SRW_TAC [] [option_apply_def]);

val seq_monad_thm = save_thm("seq_monad_thm",let
  val xs = option_apply_SOME :: mem_seq_lemma :: read_eflag_seq_lemma :: 
           parT_unit_seq_lemma :: (CONJUNCTS monad_simp_lemma)
  in LIST_CONJ (map GEN_ALL xs) end);

val CAN_XWRITE_MEM = store_thm("CAN_XWRITE_MEM",
  ``CAN_XWRITE_MEM a (r,e,s,m,i) = 
    ~(m a = NONE) /\ Xwrite IN SND (THE (m a))``,
  SIMP_TAC std_ss [XWRITE_MEM_def,CAN_XWRITE_MEM_def]
  THEN Cases_on `m a` THEN ASM_SIMP_TAC std_ss [] THEN SRW_TAC [] []
  THEN Cases_on `x` THEN Cases_on `Xwrite IN r'` THEN SRW_TAC [] []);

val CAN_XREAD_MEM = store_thm("CAN_XREAD_MEM",
  ``CAN_XREAD_MEM a (r,e,s,m,i) = 
    ~(m a = NONE) /\ Xread IN SND (THE (m a))``,
  SIMP_TAC std_ss [XREAD_MEM_def,CAN_XREAD_MEM_def]
  THEN Cases_on `m a` THEN ASM_SIMP_TAC std_ss [] THEN SRW_TAC [] []
  THEN Cases_on `x` THEN SRW_TAC [] []);

val CAN_XREAD_XWRITE_THM = store_thm("CAN_XREAD_XWRITE_THM",
  ``!s. (CAN_XWRITE_MEM a s ==> CAN_XWRITE_MEM a (XWRITE_REG r2 w s)) /\
        (CAN_XWRITE_MEM a s ==> CAN_XWRITE_MEM a (XWRITE_EIP e s)) /\
        (CAN_XWRITE_MEM a s ==> CAN_XWRITE_MEM a (XWRITE_EFLAG f b s)) /\
        (CAN_XWRITE_MEM a s ==> CAN_XWRITE_MEM a (XCLEAR_ICACHE s)) /\
        (CAN_XWRITE_MEM a s ==> CAN_XWRITE_MEM a (XWRITE_MEM2 c x s)) /\ 
        (CAN_XREAD_MEM a s ==> CAN_XREAD_MEM a (XWRITE_REG r2 w s)) /\
        (CAN_XREAD_MEM a s ==> CAN_XREAD_MEM a (XWRITE_EIP e s)) /\
        (CAN_XREAD_MEM a s ==> CAN_XREAD_MEM a (XWRITE_EFLAG f b s)) /\
        (CAN_XREAD_MEM a s ==> CAN_XREAD_MEM a (XCLEAR_ICACHE s)) /\
        (CAN_XREAD_MEM a s /\ CAN_XWRITE_MEM c s ==> CAN_XREAD_MEM a (XWRITE_MEM2 c x s))``,
  STRIP_TAC THEN `?r2 e2 s2 m2 i2. s = (r2,e2,s2,m2,i2)` by METIS_TAC [pairTheory.PAIR]
  THEN ASM_SIMP_TAC std_ss [XREAD_REG_def,XREAD_EIP_def,
         XREAD_EFLAG_def, XWRITE_REG_def, XWRITE_MEM2_def, XREAD_MEM2_def, 
         combinTheory.APPLY_UPDATE_THM, XWRITE_EIP_def,CAN_XREAD_MEM,
         XWRITE_EFLAG_def,XCLEAR_ICACHE_def,CAN_XWRITE_MEM]
  THEN Cases_on `c = a` THEN ASM_SIMP_TAC std_ss []);

val x86_else_none_write_mem_lemma = store_thm("x86_else_none_write_mem_lemma",
  ``!a x t f. CAN_XWRITE_MEM a t ==> 
              (option_apply (XWRITE_MEM a x t) f = f (XWRITE_MEM2 a x t))``,
  REPEAT STRIP_TAC
  THEN `?r e s m i. t = (r,e,s,m,i)` by METIS_TAC [pairTheory.PAIR]
  THEN FULL_SIMP_TAC std_ss [CAN_XWRITE_MEM,XWRITE_MEM_def,XWRITE_MEM2_def]
  THEN Cases_on `m a` THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [option_apply_def]);

val x86_else_none_read_mem_lemma = store_thm("x86_else_none_read_mem_lemma",
  ``!a x t f. CAN_XREAD_MEM a t ==> 
              (option_apply (XREAD_MEM a t) f = f (XREAD_MEM2 a t))``,
  REPEAT STRIP_TAC
  THEN `?r e s m i. t = (r,e,s,m,i)` by METIS_TAC [pairTheory.PAIR]
  THEN FULL_SIMP_TAC std_ss [CAN_XREAD_MEM,XREAD_MEM2_def,XREAD_MEM_def]
  THEN Cases_on `m a` THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [option_apply_def]);

val x86_else_none_eflag_lemma = store_thm("x86_else_none_eflag_lemma",
  ``!m a f. ~(m a = NONE) ==> 
            (option_apply ((m:x86_state->bool option) a) (f:bool->'a option) = f (THE (m a)))``,
  SIMP_TAC std_ss [option_apply_def]);

val x86_state_EXPAND = store_thm("x86_state_EXPAND",
  ``?r i f m. s:x86_state = (r,i,f,m)``,
  Cases_on `s` THEN Cases_on `r` THEN Cases_on `r'` THEN SIMP_TAC std_ss []);

val XREAD_EIP_ADD_0 = store_thm("XREAD_EIP_ADD_0",
  ``XREAD_MEM (XREAD_EIP s) s = XREAD_MEM (XREAD_EIP s + 0w) s``,
  REWRITE_TAC [WORD_ADD_0]); 

val x86_address_lemma = store_thm("x86_address_lemma",
  ``~(0w = 1w:word32) /\ ~(0w = 2w:word32) /\ ~(0w = 3w:word32) /\ 
    ~(1w = 2w:word32) /\ ~(1w = 3w:word32) /\ ~(2w = 3w:word32)``,
  EVAL_TAC);  

val _ = export_theory ();
