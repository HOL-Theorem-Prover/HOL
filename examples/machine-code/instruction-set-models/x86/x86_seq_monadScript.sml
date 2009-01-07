
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory listTheory opmonTheory;

open x86_coretypesTheory;

val _ = new_theory "x86_seq_monad";



val _ = type_abbrev("x86_state",   (*  state = tuple consisting of:       *) 
  ``: (Xreg -> word32) #           (*  - general-purpose 32-bit registers *)
      (word32) #                   (*  - eip                              *)
      (Xeflags -> bool option) #   (*  - eflags                           *)
      (word32 -> word8 option)     (*  - unsegmented memory               *) ``); 

(* functions for reading/writing state *)

val XREAD_REG_def   = Define `XREAD_REG     i ((r,eip,f,m):x86_state) = r i `;
val XREAD_EIP_def   = Define `XREAD_EIP       ((r,eip,f,m):x86_state) = eip `;
val XREAD_EFLAG_def = Define `XREAD_EFLAG   i ((r,eip,f,m):x86_state) = f i `;
val XREAD_MEM_def   = Define `XREAD_MEM     i ((r,eip,f,m):x86_state) = m i `;

val XWRITE_REG_def   = Define `XWRITE_REG   i x ((r,eip,f,m):x86_state) = ((i =+ x) r,eip,f,m):x86_state `;
val XWRITE_EIP_def   = Define `XWRITE_EIP     x ((r,eip,f,m):x86_state) = (r,x,f,m):x86_state `;
val XWRITE_EFLAG_def = Define `XWRITE_EFLAG i x ((r,eip,f,m):x86_state) = (r,eip,(i =+ x) f,m):x86_state `;
val XWRITE_MEM_def   = Define `XWRITE_MEM   i x ((r,eip,f,m):x86_state) = (r,eip,f,(i =+ x) m):x86_state `;

val XREAD_MEM_BYTES_def = Define `
  XREAD_MEM_BYTES n a s = 
    if n = 0 then [] else XREAD_MEM a s :: XREAD_MEM_BYTES (n-1) (a+1w) s`;

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

(*
val discardT_seq_def = Define `
  (discardT_seq: 'a x86_M -> unit x86_M) s = 
    \y. case s y of NONE -> NONE || SOME (z,t) -> SOME ((),t)`;
*)

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
  (\s. case XREAD_MEM a s of NONE -> NONE || SOME y -> SOME ((),XWRITE_MEM a (SOME x) s))`;

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



(* some rewriter-friendly theorems *)

val option_apply_def = Define `
  option_apply x f = if x = NONE then NONE else f (THE x)`;

val option_apply_SOME = prove(
  ``!x f. option_apply (SOME x) f = f x``,SRW_TAC [] [option_apply_def]);

val mem_seq_lemma = prove(
  ``(read_mem_seq ii a s = option_apply (XREAD_MEM a s) (\x. SOME (x,s))) /\ 
    (write_mem_seq ii a y s = option_apply (XREAD_MEM a s) (\x. SOME ((),XWRITE_MEM a (SOME y) s)))``,
  SRW_TAC [] [option_apply_def,read_mem_seq_def,write_mem_seq_def] 
  THEN Cases_on `XREAD_MEM a s` THEN FULL_SIMP_TAC std_ss []);

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

val XREAD_CLAUSES = store_thm("XREAD_CLAUSES",
  ``!s. (XREAD_REG r (XWRITE_MEM a x s) = XREAD_REG r s) /\
        (XREAD_REG r (XWRITE_EFLAG f b s) = XREAD_REG r s) /\
        (XREAD_REG r (XWRITE_EIP e s) = XREAD_REG r s) /\
        (XREAD_MEM a (XWRITE_REG r w s) = XREAD_MEM a s) /\
        (XREAD_MEM a (XWRITE_EFLAG f b s) = XREAD_MEM a s) /\
        (XREAD_MEM a (XWRITE_EIP e s) = XREAD_MEM a s) /\
        (XREAD_EFLAG f (XWRITE_REG r w s) = XREAD_EFLAG f s) /\
        (XREAD_EFLAG f (XWRITE_MEM a x s) = XREAD_EFLAG f s) /\
        (XREAD_EFLAG f (XWRITE_EIP e s) = XREAD_EFLAG f s) /\
        (XREAD_EIP (XWRITE_REG r w s) = XREAD_EIP s) /\
        (XREAD_EIP (XWRITE_MEM a x s) = XREAD_EIP s) /\
        (XREAD_EIP (XWRITE_EFLAG f b s) = XREAD_EIP s) /\
        (XREAD_REG r (XWRITE_REG r2 w s) = if r = r2 then w else XREAD_REG r s) /\
        (XREAD_MEM a (XWRITE_MEM a2 x s) = if a = a2 then x else XREAD_MEM a s) /\
        (XREAD_EFLAG f (XWRITE_EFLAG f2 b s) = if f = f2 then b else XREAD_EFLAG f s) /\
        (XREAD_EIP (XWRITE_EIP e s) = e)``,
  Cases THEN Cases_on `r'` THEN Cases_on `r''` 
  THEN SRW_TAC [] [XREAD_REG_def,XREAD_MEM_def,XREAD_EFLAG_def, XREAD_EIP_def, 
    XWRITE_MEM_def,XWRITE_REG_def,XWRITE_EFLAG_def, XWRITE_EIP_def, combinTheory.APPLY_UPDATE_THM]);

val x86_else_none_mem_lemma = store_thm("x86_else_none_mem_lemma",
  ``!m a f. ~(m a = NONE) ==> 
            (option_apply ((m:x86_state->word8 option) a) (f:word8->'a option) = f (THE (m a)))``,
  SIMP_TAC std_ss [option_apply_def]);

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
