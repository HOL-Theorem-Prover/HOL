
Theory ppc_seq_monad
Ancestors
  words bit_list list opmon ppc_coretypes

(* state *)

val _ = type_abbrev("ppc_state",
  ``:(ppc_reg -> word32) # (ppc_bit -> bool option) # (word32 -> word8 option)``);
  (* tuple consists of registers, status bits and byte-addressed memory *)

(* functions for reading/writing state *)

Definition PREAD_R_def:   PREAD_R rd ((r,s,m):ppc_state) = r rd
End
Definition PREAD_S_def:   PREAD_S rd ((r,s,m):ppc_state) = s rd
End
Definition PREAD_M_def:   PREAD_M rd ((r,s,m):ppc_state) = m rd
End

Definition PWRITE_R_def:   PWRITE_R rd x (r,s,m) = ((rd =+ x) r,s,m):ppc_state
End
Definition PWRITE_S_def:   PWRITE_S rd x (r,s,m) = (r,(rd =+ x) s,m):ppc_state
End
Definition PWRITE_M_def:   PWRITE_M rd x (r,s,m) = (r,s,(rd =+ x) m):ppc_state
End



(* ---------------------------------------------------------------------------------- *>

  We define a state and monads for constructing a sequential version of the semantics.

<* ---------------------------------------------------------------------------------- *)

val _ = type_abbrev("ppc_M",``:ppc_state -> ('a # ppc_state) option``);


(* sequential monads for an option state *)

Definition constT_seq_def:
  (constT_seq: 'a -> 'a ppc_M) x = \y. SOME (x,y)
End

Definition addT_seq_def:
  (addT_seq: 'a -> 'b ppc_M -> ('a # 'b) ppc_M) x s =
    \y. case s y of NONE => NONE | SOME (z,t) => SOME ((x,z),t)
End

Definition lockT_seq_def:
  (lockT_seq: 'a ppc_M -> 'a ppc_M) s = s
End

Definition failureT_seq_def:
  (failureT_seq: 'a ppc_M) = \y. NONE
End

Definition seqT_seq_def:
  (seqT_seq: 'a ppc_M -> ('a -> 'b ppc_M) -> 'b ppc_M) s f =
    \y. case s y of NONE => NONE | SOME (z,t) => f z t
End

Definition parT_seq_def:
  (parT_seq: 'a ppc_M -> 'b ppc_M -> ('a # 'b) ppc_M) s t =
    \y. case s y of NONE => NONE | SOME (a,z) =>
        case t z of NONE => NONE | SOME (b,x) => SOME ((a,b),x)
End

Definition parT_unit_seq_def:
  (parT_unit_seq: unit ppc_M -> unit ppc_M -> unit ppc_M) s t =
    \y. case s y of NONE => NONE | SOME (a,z) =>
        case t z of NONE => NONE | SOME (b,x) => SOME ((),x)
End

(* register reads/writes always succeed. *)

Definition write_reg_seq_def:   (write_reg_seq ii r x):unit ppc_M =
  \s. SOME ((),PWRITE_R r x s)
End

Definition read_reg_seq_def:   (read_reg_seq ii r):word32 ppc_M =
  \s. SOME (PREAD_R r s,s)
End

(* eflags can always be written, but reading a NONE status bit causes a failure *)

Definition write_status_seq_def:   (write_status_seq ii f x):unit ppc_M =
  (\s. SOME ((),PWRITE_S f x s))
End

Definition read_status_seq_def:    (read_status_seq ii f):bool ppc_M =
  (\s. case PREAD_S f s of NONE => NONE | SOME b => SOME (b,s))
End

(* memory writes are only allowed to modelled memory, i.e. locations containing SOME ... *)

Definition write_mem_seq_def:     (write_mem_seq ii a x):unit ppc_M =
  (\s. case PREAD_M a s of NONE => NONE | SOME y => SOME ((),PWRITE_M a (SOME x) s))
End

(* a memory read to an unmodelled memory location causes a failure *)

Definition read_mem_seq_def:    (read_mem_seq ii a):word8 ppc_M =
  (\s. case PREAD_M a s of NONE => NONE | SOME x => SOME (x,s))
End


(* export *)

val _ = Define `(constT: 'a -> 'a ppc_M)                                     = constT_seq`;
val _ = Define `(addT: 'a -> 'b ppc_M -> ('a # 'b) ppc_M)                    = addT_seq`;
val _ = Define `(lockT: unit ppc_M -> unit ppc_M)                            = lockT_seq`;
val _ = Define `(failureT: unit ppc_M)                                       = failureT_seq`;
val _ = Define `(seqT: 'a ppc_M -> (('a -> 'b ppc_M) -> 'b ppc_M))           = seqT_seq`;
val _ = Define `(parT: 'a ppc_M -> 'b ppc_M -> ('a # 'b) ppc_M)              = parT_seq`;
val _ = Define `(parT_unit: unit ppc_M -> unit ppc_M -> unit ppc_M)          = parT_unit_seq`;
val _ = Define `(write_reg: iiid -> ppc_reg -> word32 -> unit ppc_M)         = write_reg_seq`;
val _ = Define `(read_reg: iiid -> ppc_reg -> word32 ppc_M)                  = read_reg_seq`;
val _ = Define `(write_status: iiid -> ppc_bit -> bool option -> unit ppc_M) = write_status_seq`;
val _ = Define `(read_status: iiid -> ppc_bit -> bool ppc_M)                 = read_status_seq`;
val _ = Define `(write_mem: iiid -> word32 -> word8 -> unit ppc_M)           = write_mem_seq`;
val _ = Define `(read_mem: iiid -> word32 -> word8 ppc_M)                    = read_mem_seq`;



(* some rewriter-friendly theorems *)

val mem_seq_lemma = prove(
  ``(read_mem_seq ii a s = option_apply (PREAD_M a s) (\x. SOME (x,s))) /\
    (write_mem_seq ii a y s = option_apply (PREAD_M a s) (\x. SOME ((),PWRITE_M a (SOME y) s)))``,
  SRW_TAC [] [option_apply_def,read_mem_seq_def,write_mem_seq_def]
  THEN Cases_on `PREAD_M a s` THEN FULL_SIMP_TAC std_ss []);

val read_status_seq_lemma = prove(
  ``read_status_seq ii f s = option_apply (PREAD_S f s) (\x. SOME (x,s))``,
  SRW_TAC [] [option_apply_def,read_status_seq_def]
  THEN Cases_on `PREAD_S f s` THEN FULL_SIMP_TAC std_ss []);

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
  val xs = option_apply_SOME :: mem_seq_lemma :: read_status_seq_lemma ::
           parT_unit_seq_lemma :: (CONJUNCTS monad_simp_lemma)
  in LIST_CONJ (map GEN_ALL xs) end);

val PREAD_CLAUSES = store_thm("PREAD_CLAUSES",
  ``!s. (PREAD_R r (PWRITE_M a x s) = PREAD_R r s) /\
        (PREAD_R r (PWRITE_S f b s) = PREAD_R r s) /\
        (PREAD_M a (PWRITE_R r w s) = PREAD_M a s) /\
        (PREAD_M a (PWRITE_S f b s) = PREAD_M a s) /\
        (PREAD_S f (PWRITE_R r w s) = PREAD_S f s) /\
        (PREAD_S f (PWRITE_M a x s) = PREAD_S f s) /\
        (PREAD_R r (PWRITE_R r2 w s) = if r = r2 then w else PREAD_R r s) /\
        (PREAD_M a (PWRITE_M a2 x s) = if a = a2 then x else PREAD_M a s) /\
        (PREAD_S f (PWRITE_S f2 b s) = if f = f2 then b else PREAD_S f s)``,
  Cases THEN Cases_on `r'` THEN SRW_TAC [] [PREAD_R_def,PREAD_M_def,PREAD_S_def,
    PWRITE_M_def,PWRITE_R_def,PWRITE_S_def, combinTheory.APPLY_UPDATE_THM]);

val ppc_else_none_mem_lemma = store_thm("ppc_else_none_mem_lemma",
  ``!m a f. ~(m a = NONE) ==>
            (option_apply ((m:ppc_state->word8 option) a) (f:word8->'a option) = f (THE (m a)))``,
  SIMP_TAC std_ss [option_apply_def]);

val ppc_else_none_status_lemma = store_thm("ppc_else_none_status_lemma",
  ``!m a f. ~(m a = NONE) ==>
            (option_apply ((m:ppc_state->bool option) a) (f:bool->'a option) = f (THE (m a)))``,
  SIMP_TAC std_ss [option_apply_def]);

