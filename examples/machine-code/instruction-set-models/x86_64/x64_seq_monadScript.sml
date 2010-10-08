
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory listTheory opmonTheory combinTheory;

open x64_coretypesTheory;

val _ = new_theory "x64_seq_monad";

val _ = type_abbrev("Zimm",``:word64``);

val _ = Hol_datatype `x64_permission = Zread | Zwrite | Zexecute`;

val _ = type_abbrev("x64_memory",``: word64 -> ((word8 # x64_permission set) option)``);

val _ = type_abbrev("x64_state",   (*  state = tuple consisting of:       *)
  ``: (Zreg -> word64) #           (*  - general-purpose 32-bit registers *)
      (word64) #                   (*  - rip                              *)
      (Zeflags -> bool option) #   (*  - eflags                           *)
      x64_memory #                 (*  - unsegmented memory               *)
      x64_memory                   (*  - instruction cache                *) ``);

(* functions for reading/writing state *)

val ZREAD_REG_def   = Define `ZREAD_REG     x ((r,p,s,m,i):x64_state) = r x `;
val ZREAD_RIP_def   = Define `ZREAD_RIP       ((r,p,s,m,i):x64_state) = p `;
val ZREAD_EFLAG_def = Define `ZREAD_EFLAG   x ((r,p,s,m,i):x64_state) = s x `;

val ZREAD_MEM_def = Define `
  ZREAD_MEM x ((r,p,s,m,i):x64_state) =
    case m x of
       NONE -> NONE
    || SOME (w,perms) -> if Zread IN perms then SOME w else NONE`;

val ZREAD_INSTR_def = Define `
  ZREAD_INSTR x ((r,p,s,m,i):x64_state) =
    case (i x, m x) of
       (NONE, NONE) -> NONE
    || (NONE, SOME (w,perms)) -> if {Zread;Zexecute} SUBSET perms then SOME w else NONE
    || (SOME (w,perms), _) -> if {Zread;Zexecute} SUBSET perms then SOME w else NONE`;

val Z64_ICACHE_EMPTY_def = Define `Z64_ICACHE_EMPTY = (\addr. NONE):x64_memory`;

val ZCLEAR_ICACHE_def = Define `
  ZCLEAR_ICACHE ((r,p,s,m,i):x64_state) = (r,p,s,m,Z64_ICACHE_EMPTY):x64_state`;

val ZWRITE_REG_def   = Define `ZWRITE_REG   x y ((r,p,s,m,i):x64_state) = ((x =+ y) r,p,s,m,i):x64_state `;
val ZWRITE_RIP_def   = Define `ZWRITE_RIP     y ((r,p,s,m,i):x64_state) = (r,y,s,m,i):x64_state `;
val ZWRITE_EFLAG_def = Define `ZWRITE_EFLAG x y ((r,p,s,m,i):x64_state) = (r,p,(x =+ y) s,m,i):x64_state `;

val ZWRITE_MEM_def   = Define `
  ZWRITE_MEM x y ((r,p,s,m,i):x64_state) =
    case m x of
       NONE -> NONE
    || SOME (w,perms) -> if Zwrite IN perms then SOME ((r,p,s,(x =+ SOME (y,perms)) m,i):x64_state) else NONE`;

val ZREAD_MEM_BYTES_def = Define `
  ZREAD_MEM_BYTES n a s =
    if n = 0 then [] else ZREAD_MEM a s :: ZREAD_MEM_BYTES (n-1) (a+1w) s`;

val ZREAD_INSTR_BYTES_def = Define `
  ZREAD_INSTR_BYTES n a s =
    if n = 0 then [] else ZREAD_INSTR a s :: ZREAD_INSTR_BYTES (n-1) (a+1w) s`;

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
 (ONCE_REWRITE_CONV [ZREAD_MEM_BYTES_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [ZREAD_MEM_BYTES_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [ZREAD_MEM_BYTES_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [ZREAD_MEM_BYTES_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [ZREAD_MEM_BYTES_def,word2bytes_def] THENC
  SIMP_CONV std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,ASR_ADD])

val ZREAD_MEM_BYTES_thm = save_thm("ZREAD_MEM_BYTES_thm",
   CONJ (expand_mem_read_bytes ``ZREAD_MEM_BYTES 1 a s``)
  (CONJ (expand_mem_read_bytes ``ZREAD_MEM_BYTES 2 a s``)
  (CONJ (expand_mem_read_bytes ``ZREAD_MEM_BYTES 4 a s``)
        (expand_mem_read_bytes ``ZREAD_MEM_BYTES 8 a s``))));

val word2bytes_thm = save_thm("word2bytes_thm",
   CONJ (expand_mem_read_bytes ``word2bytes 1 w``)
  (CONJ (expand_mem_read_bytes ``word2bytes 2 w``)
  (CONJ (expand_mem_read_bytes ``word2bytes 4 w``)
        (expand_mem_read_bytes ``word2bytes 8 w``))));

val EL_thm = save_thm("EL_thm",
  CONJ (EVAL ``EL 0 ((x0:'a)::xs)``)
 (CONJ (EVAL ``EL 1 ((x0:'a)::x2::xs)``)
 (CONJ (EVAL ``EL 2 ((x0:'a)::x2::x3::xs)``)
 (CONJ (EVAL ``EL 3 ((x0:'a)::x2::x3::x4::xs)``)
 (CONJ (EVAL ``EL 4 ((x0:'a)::x2::x3::x4::x5::xs)``)
 (CONJ (EVAL ``EL 5 ((x0:'a)::x2::x3::x4::x5::x6::xs)``)
 (CONJ (EVAL ``EL 6 ((x0:'a)::x2::x3::x4::x5::x6::x7::xs)``)
       (EVAL ``EL 7 ((x0:'a)::x2::x3::x4::x5::x6::x7::x8::xs)``))))))))


(* ---------------------------------------------------------------------------------- *>

  We define a state and monads for constructing a sequential version of the semantics.

<* ---------------------------------------------------------------------------------- *)

(* val _ = type_abbrev("Zstate",``:x64_state -> ('a # x64_state) option``); *)

val _ = type_abbrev("x64_M",``:x64_state -> ('a # x64_state) option``);


(* sequential monads for an option state *)

val constT_seq_def = Define `
  (constT_seq: 'a -> 'a x64_M) x = \y. SOME (x,y)`;

val addT_seq_def = Define `
  (addT_seq: 'a -> 'b x64_M -> ('a # 'b) x64_M) x s =
    \y. case s y of NONE -> NONE || SOME (z,t) -> SOME ((x,z),t)`;

val lockT_seq_def = Define `
  (lockT_seq: 'a x64_M -> 'a x64_M) s = s`;

val failureT_seq_def = Define `
  (failureT_seq: 'a x64_M) = \y. NONE`;

val seqT_seq_def = Define `
  (seqT_seq: 'a x64_M -> ('a -> 'b x64_M) -> 'b x64_M) s f =
    \y. case s y of NONE -> NONE || SOME (z,t) -> f z t`;

val parT_seq_def = Define `
  (parT_seq: 'a x64_M -> 'b x64_M -> ('a # 'b) x64_M) s t =
    \y. case s y of NONE -> NONE || SOME (a,z) ->
        case t z of NONE -> NONE || SOME (b,x) -> SOME ((a,b),x)`;

val parT_unit_seq_def = Define `
  (parT_unit_seq: unit x64_M -> unit x64_M -> unit x64_M) s t =
    \y. case s y of NONE -> NONE || SOME (a,z) ->
        case t z of NONE -> NONE || SOME (b,x) -> SOME ((),x)`;

(* register reads/writes always succeed. *)

val write_reg_seq_def = Define `(write_reg_seq ii r x):unit x64_M =
  \s. SOME ((),ZWRITE_REG r x s)`;

val read_reg_seq_def = Define `(read_reg_seq ii r):word64 x64_M =
  \s. SOME (ZREAD_REG r s,s)`;

(* eflags can always be written, but reading a NONE eflag causes a failure *)

val write_eflag_seq_def = Define `(write_eflag_seq ii f x):unit x64_M =
  (\s. SOME ((),ZWRITE_EFLAG f x s))`;

val read_eflag_seq_def  = Define `(read_eflag_seq ii f):bool x64_M =
  (\s. case ZREAD_EFLAG f s of NONE -> NONE || SOME b -> SOME (b,s))`;

(* rip reads/writes always succeed. *)

val write_rip_seq_def = Define `(write_rip_seq ii x):unit x64_M =
  \s. SOME ((),ZWRITE_RIP x s)`;

val read_rip_seq_def = Define `(read_rip_seq ii):Zimm x64_M =
  \s. SOME (ZREAD_RIP s,s)`;

(* memory writes are only allowed to modelled memory, i.e. locations containing SOME ... *)

val write_mem_seq_def   = Define `(write_mem_seq ii a x):unit x64_M =
  (\s. case ZWRITE_MEM a x s of NONE -> NONE || SOME s2 -> SOME ((),s2))`;

(* a memory read to an unmodelled memory location causes a failure *)

val read_mem_seq_def  = Define `(read_mem_seq ii a):word8 x64_M =
  (\s. case ZREAD_MEM a s of NONE -> NONE || SOME x -> SOME (x,s))`;

(* reading and writing from/to memory *)

val read_m8_seq_def = Define `(read_m8_seq ii a):word8 x64_M =
  read_mem_seq ii a`;

val read_m16_seq_def = Define `(read_m16_seq ii a):word16 x64_M =
  seqT_seq (parT_seq (read_mem_seq ii (a+0w)) (read_mem_seq ii (a+1w)))
       (\(x0,x1). constT_seq (bytes2word [x0;x1]))`; 

val read_m32_seq_def = Define `(read_m32_seq ii a):word32 x64_M =
  seqT_seq (parT_seq (read_mem_seq ii (a+0w)) 
           (parT_seq (read_mem_seq ii (a+1w))
           (parT_seq (read_mem_seq ii (a+2w)) 
                     (read_mem_seq ii (a+3w)))))
       (\(x0,x1,x2,x3). constT_seq (bytes2word [x0;x1;x2;x3]))`;

val read_m64_seq_def = Define `(read_m64_seq ii a):word64 x64_M =
  seqT_seq (parT_seq (read_mem_seq ii (a+0w)) 
           (parT_seq (read_mem_seq ii (a+1w))
           (parT_seq (read_mem_seq ii (a+2w))
           (parT_seq (read_mem_seq ii (a+3w))
           (parT_seq (read_mem_seq ii (a+4w))
           (parT_seq (read_mem_seq ii (a+5w))
           (parT_seq (read_mem_seq ii (a+6w)) 
                     (read_mem_seq ii (a+7w)))))))))
       (\(x0,x1,x2,x3,x4,x5,x6,x7). constT_seq (bytes2word [x0;x1;x2;x3;x4;x5;x6;x7]))`;


val write_m8_seq_def = Define `(write_m8_seq ii a w):unit x64_M =
    write_mem_seq ii a (w:word8)`;

val write_m16_seq_def = Define `(write_m16_seq ii a w):unit x64_M =
    (let bs = word2bytes 2 (w:word16) in
       parT_unit_seq (write_mem_seq ii (a+0w) (EL 0 bs)) 
                     (write_mem_seq ii (a+1w) (EL 1 bs)))`;

val write_m32_seq_def = Define `(write_m32_seq ii a w):unit x64_M =
    (let bs = word2bytes 4 (w:word32) in
       parT_unit_seq (write_mem_seq ii (a+0w) (EL 0 bs)) 
      (parT_unit_seq (write_mem_seq ii (a+1w) (EL 1 bs))
      (parT_unit_seq (write_mem_seq ii (a+2w) (EL 2 bs)) 
                     (write_mem_seq ii (a+3w) (EL 3 bs)))))`;

val write_m64_seq_def = Define `(write_m64_seq ii a w):unit x64_M =
    (let bs = word2bytes 8 (w:word64) in
       parT_unit_seq (write_mem_seq ii (a+0w) (EL 0 bs)) 
      (parT_unit_seq (write_mem_seq ii (a+1w) (EL 1 bs))
      (parT_unit_seq (write_mem_seq ii (a+2w) (EL 2 bs)) 
      (parT_unit_seq (write_mem_seq ii (a+3w) (EL 3 bs))
      (parT_unit_seq (write_mem_seq ii (a+4w) (EL 4 bs)) 
      (parT_unit_seq (write_mem_seq ii (a+5w) (EL 5 bs))
      (parT_unit_seq (write_mem_seq ii (a+6w) (EL 6 bs)) 
                     (write_mem_seq ii (a+7w) (EL 7 bs)))))))))`;

(* clear the icache *)

val clear_icache_seq_def = Define `(clear_icache_seq ii):unit x64_M =
  \s. SOME ((),ZCLEAR_ICACHE s)`;


(* export *)

val _ = Define `(constT: 'a -> 'a x64_M)                                     = constT_seq`;
val _ = Define `(addT: 'a -> 'b x64_M -> ('a # 'b) x64_M)                    = addT_seq`;
val _ = Define `(lockT: unit x64_M -> unit x64_M)                            = lockT_seq`;
val _ = Define `(failureT: unit x64_M)                                       = failureT_seq`;
val _ = Define `(seqT: 'a x64_M -> (('a -> 'b x64_M) -> 'b x64_M))           = seqT_seq`;
val _ = Define `(parT: 'a x64_M -> 'b x64_M -> ('a # 'b) x64_M)              = parT_seq`;
val _ = Define `(parT_unit: unit x64_M -> unit x64_M -> unit x64_M)          = parT_unit_seq`;
val _ = Define `(write_reg: iiid -> Zreg -> Zimm -> unit x64_M)              = write_reg_seq`;
val _ = Define `(read_reg: iiid -> Zreg -> Zimm x64_M)                       = read_reg_seq`;
val _ = Define `(write_rip: iiid -> Zimm -> unit x64_M)                      = write_rip_seq`;
val _ = Define `(read_rip: iiid -> Zimm x64_M)                               = read_rip_seq`;
val _ = Define `(write_eflag: iiid -> Zeflags -> bool option -> unit x64_M)  = write_eflag_seq`;
val _ = Define `(read_eflag: iiid -> Zeflags -> bool x64_M)                  = read_eflag_seq`;
val _ = Define `(write_m8: iiid -> word64 -> word8 -> unit x64_M)            = write_m8_seq`;
val _ = Define `(read_m8: iiid -> word64 -> word8 x64_M)                     = read_m8_seq`;
val _ = Define `(write_m16: iiid -> word64 -> word16 -> unit x64_M)          = write_m16_seq`;
val _ = Define `(read_m16: iiid -> word64 -> word16 x64_M)                   = read_m16_seq`;
val _ = Define `(write_m32: iiid -> word64 -> word32 -> unit x64_M)          = write_m32_seq`;
val _ = Define `(read_m32: iiid -> word64 -> word32 x64_M)                   = read_m32_seq`;
val _ = Define `(write_m64: iiid -> word64 -> word64 -> unit x64_M)          = write_m64_seq`;
val _ = Define `(read_m64: iiid -> word64 -> word64 x64_M)                   = read_m64_seq`;
val _ = Define `(clear_icache: iiid -> unit x64_M)                           = clear_icache_seq`;



(* some rewriter-friendly theorems *)

val option_apply_def = Define `
  option_apply x f = if x = NONE then NONE else f (THE x)`;

val option_apply_SOME = prove(
  ``!x f. option_apply (SOME x) f = f x``,SRW_TAC [] [option_apply_def]);

val ZWRITE_MEM2_def = Define `
  ZWRITE_MEM2 a w ((r,e,t,m,i):x64_state) = (r,e,t,(a =+ SOME (w, SND (THE (m a)))) m,i)`;

val ZREAD_MEM2_def = Define `
  ZREAD_MEM2 a ((r,e,t,m,i):x64_state) = FST (THE (m a))`;

val ZREAD_MEM2_WORD16_def = Define `
  ZREAD_MEM2_WORD16 a (s:x64_state) = (bytes2word
    [ZREAD_MEM2 (a + 0x0w) s; ZREAD_MEM2 (a + 0x1w) s]) :word16`;

val ZREAD_MEM2_WORD32_def = Define `
  ZREAD_MEM2_WORD32 a (s:x64_state) = (bytes2word
    [ZREAD_MEM2 (a + 0x0w) s; ZREAD_MEM2 (a + 0x1w) s;
     ZREAD_MEM2 (a + 0x2w) s; ZREAD_MEM2 (a + 0x3w) s]) :word32`;

val ZREAD_MEM2_WORD64_def = Define `
  ZREAD_MEM2_WORD64 a (s:x64_state) = (bytes2word
    [ZREAD_MEM2 (a + 0x0w) s; ZREAD_MEM2 (a + 0x1w) s;
     ZREAD_MEM2 (a + 0x2w) s; ZREAD_MEM2 (a + 0x3w) s;
     ZREAD_MEM2 (a + 0x4w) s; ZREAD_MEM2 (a + 0x5w) s;
     ZREAD_MEM2 (a + 0x6w) s; ZREAD_MEM2 (a + 0x7w) s]) :word64`;

val ZWRITE_MEM2_WORD16_def = Define `
  ZWRITE_MEM2_WORD16 a (w:word16) (s:x64_state) =
    ZWRITE_MEM2 (a + 1w) (EL 1 (word2bytes 2 w))
   (ZWRITE_MEM2 (a + 0w) (EL 0 (word2bytes 2 w)) s)`;

val ZWRITE_MEM2_WORD32_def = Define `
  ZWRITE_MEM2_WORD32 a (w:word32) (s:x64_state) =
    ZWRITE_MEM2 (a + 3w) (EL 3 (word2bytes 4 w))
   (ZWRITE_MEM2 (a + 2w) (EL 2 (word2bytes 4 w))
   (ZWRITE_MEM2 (a + 1w) (EL 1 (word2bytes 4 w))
   (ZWRITE_MEM2 (a + 0w) (EL 0 (word2bytes 4 w)) s)))`;

val ZWRITE_MEM2_WORD64_def = Define `
  ZWRITE_MEM2_WORD64 a (w:word64) (s:x64_state) =
    ZWRITE_MEM2 (a + 7w) (EL 7 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 6w) (EL 6 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 5w) (EL 5 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 4w) (EL 4 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 3w) (EL 3 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 2w) (EL 2 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 1w) (EL 1 (word2bytes 8 w))
   (ZWRITE_MEM2 (a + 0w) (EL 0 (word2bytes 8 w)) s)))))))`;

val CAN_ZWRITE_MEM_def = Define `
  CAN_ZWRITE_MEM a s = !w. ~(ZWRITE_MEM a w s = NONE)`;

val CAN_ZREAD_MEM_def = Define `
  CAN_ZREAD_MEM a s = ~(ZREAD_MEM a s = NONE)`;

val mem_seq_lemma = prove(
  ``(read_mem_seq ii a s = option_apply (ZREAD_MEM a s) (\x. SOME (x,s))) /\
    (write_mem_seq ii a y s = option_apply (ZWRITE_MEM a y s) (\s. SOME ((),s)))``,
  SRW_TAC [] [option_apply_def,read_mem_seq_def,write_mem_seq_def]
  THEN Cases_on `ZREAD_MEM a s` THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `ZWRITE_MEM a y s` THEN FULL_SIMP_TAC std_ss []);

val read_eflag_seq_lemma = prove(
  ``read_eflag_seq ii f s = option_apply (ZREAD_EFLAG f s) (\x. SOME (x,s))``,
  SRW_TAC [] [option_apply_def,read_eflag_seq_def]
  THEN Cases_on `ZREAD_EFLAG f s` THEN FULL_SIMP_TAC std_ss []);

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

val CAN_ZWRITE_MEM = store_thm("CAN_ZWRITE_MEM",
  ``CAN_ZWRITE_MEM a (r,e,s,m,i) =
    ~(m a = NONE) /\ Zwrite IN SND (THE (m a))``,
  SIMP_TAC std_ss [ZWRITE_MEM_def,CAN_ZWRITE_MEM_def]
  THEN Cases_on `m a` THEN ASM_SIMP_TAC std_ss [] THEN SRW_TAC [] []
  THEN Cases_on `x` THEN Cases_on `Zwrite IN r'` THEN SRW_TAC [] []);

val CAN_ZREAD_MEM = store_thm("CAN_ZREAD_MEM",
  ``CAN_ZREAD_MEM a (r,e,s,m,i) =
    ~(m a = NONE) /\ Zread IN SND (THE (m a))``,
  SIMP_TAC std_ss [ZREAD_MEM_def,CAN_ZREAD_MEM_def]
  THEN Cases_on `m a` THEN ASM_SIMP_TAC std_ss [] THEN SRW_TAC [] []
  THEN Cases_on `x` THEN SRW_TAC [] []);

val CAN_ZREAD_ZWRITE_THM = store_thm("CAN_ZREAD_ZWRITE_THM",
  ``!s. (CAN_ZWRITE_MEM a s ==> CAN_ZWRITE_MEM a (ZWRITE_REG r2 w s)) /\
        (CAN_ZWRITE_MEM a s ==> CAN_ZWRITE_MEM a (ZWRITE_RIP e s)) /\
        (CAN_ZWRITE_MEM a s ==> CAN_ZWRITE_MEM a (ZWRITE_EFLAG f b s)) /\
        (CAN_ZWRITE_MEM a s ==> CAN_ZWRITE_MEM a (ZCLEAR_ICACHE s)) /\
        (CAN_ZWRITE_MEM a s ==> CAN_ZWRITE_MEM a (ZWRITE_MEM2 c x s)) /\
        (CAN_ZREAD_MEM a s ==> CAN_ZREAD_MEM a (ZWRITE_REG r2 w s)) /\
        (CAN_ZREAD_MEM a s ==> CAN_ZREAD_MEM a (ZWRITE_RIP e s)) /\
        (CAN_ZREAD_MEM a s ==> CAN_ZREAD_MEM a (ZWRITE_EFLAG f b s)) /\
        (CAN_ZREAD_MEM a s ==> CAN_ZREAD_MEM a (ZCLEAR_ICACHE s)) /\
        (CAN_ZREAD_MEM a s /\ CAN_ZWRITE_MEM c s ==> CAN_ZREAD_MEM a (ZWRITE_MEM2 c x s))``,
  STRIP_TAC THEN `?r2 e2 s2 m2 i2. s = (r2,e2,s2,m2,i2)` by METIS_TAC [pairTheory.PAIR]
  THEN ASM_SIMP_TAC std_ss [ZREAD_REG_def,ZREAD_RIP_def,
         ZREAD_EFLAG_def, ZWRITE_REG_def, ZWRITE_MEM2_def, ZREAD_MEM2_def,
         combinTheory.APPLY_UPDATE_THM, ZWRITE_RIP_def,CAN_ZREAD_MEM,
         ZWRITE_EFLAG_def,ZCLEAR_ICACHE_def,CAN_ZWRITE_MEM]
  THEN Cases_on `c = a` THEN ASM_SIMP_TAC std_ss []);

val x64_else_none_write_mem_lemma = store_thm("x64_else_none_write_mem_lemma",
  ``!a x t f. CAN_ZWRITE_MEM a t ==>
              (option_apply (ZWRITE_MEM a x t) f = f (ZWRITE_MEM2 a x t))``,
  REPEAT STRIP_TAC
  THEN `?r e s m i. t = (r,e,s,m,i)` by METIS_TAC [pairTheory.PAIR]
  THEN FULL_SIMP_TAC std_ss [CAN_ZWRITE_MEM,ZWRITE_MEM_def,ZWRITE_MEM2_def]
  THEN Cases_on `m a` THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [option_apply_def]);

val x64_else_none_read_mem_lemma = store_thm("x64_else_none_read_mem_lemma",
  ``!a x t f. CAN_ZREAD_MEM a t ==>
              (option_apply (ZREAD_MEM a t) f = f (ZREAD_MEM2 a t))``,
  REPEAT STRIP_TAC
  THEN `?r e s m i. t = (r,e,s,m,i)` by METIS_TAC [pairTheory.PAIR]
  THEN FULL_SIMP_TAC std_ss [CAN_ZREAD_MEM,ZREAD_MEM2_def,ZREAD_MEM_def]
  THEN Cases_on `m a` THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [option_apply_def]);

val x64_else_none_eflag_lemma = store_thm("x64_else_none_eflag_lemma",
  ``!m a f. ~(m a = NONE) ==>
            (option_apply ((m:x64_state->bool option) a) (f:bool->'a option) = f (THE (m a)))``,
  SIMP_TAC std_ss [option_apply_def]);

val x64_state_EZPAND = store_thm("x64_state_EZPAND",
  ``?r i f m. s:x64_state = (r,i,f,m)``,
  Cases_on `s` THEN Cases_on `r` THEN Cases_on `r'` THEN SIMP_TAC std_ss []);

val ZREAD_RIP_ADD_0 = store_thm("ZREAD_RIP_ADD_0",
  ``ZREAD_MEM (ZREAD_RIP s) s = ZREAD_MEM (ZREAD_RIP s + 0w) s``,
  REWRITE_TAC [WORD_ADD_0]);

val x64_address_lemma = save_thm("x64_address_lemma",
  SIMP_RULE std_ss [listTheory.ALL_DISTINCT,MEM,GSYM CONJ_ASSOC] 
    (EVAL ``ALL_DISTINCT [0w;1w;2w;3w;4w;5w;6w;7w:word64]``));

val _ = export_theory ();
