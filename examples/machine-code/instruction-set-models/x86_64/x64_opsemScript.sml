
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory;

open x64_coretypesTheory x64_astTheory x64_seq_monadTheory;

val _ = new_theory "x64_opsem";


(* ---------------------------------------------------------------------------------- *>

  We define the semantics of an instruction.

<* ---------------------------------------------------------------------------------- *)


(* assertion *)

val assertT_def = Define `
  assertT b = if b then constT () else failureT`;

val option_apply_assertT = store_thm("option_apply_assertT",
  ``!b s f. b ==> (option_apply (assertT b s) f = f ((),s))``,
  SIMP_TAC std_ss [assertT_def,constT_def,constT_seq_def,option_apply_def]);


(* calculate effective address *)

val ea_Zr_def = Define `ea_Zr s (r:Zreg) = constT (Zea_r s r)`;
val ea_Zi_def = Define `ea_Zi s (i:Zimm) = constT (Zea_i s i)`;

val ea_Zrm_base_def = Define `
  (ea_Zrm_base ii NONE = constT 0w) /\
  (ea_Zrm_base ii (SOME r) = read_reg ii r)`;

val ea_Zrm_index_def = Define `
  (ea_Zrm_index ii NONE = constT (0w:Zimm)) /\
  (ea_Zrm_index ii (SOME (s:word2,r)) =
     seqT (read_reg ii r) (\idx. constT (n2w (2 ** w2n s) * idx)))`;

val ea_Zrm_def = Define `
  (ea_Zrm ii s (Zr r) = ea_Zr s r) /\
  (ea_Zrm ii s (Zm i b d) =
     seqT
        (parT (ea_Zrm_index ii i) (ea_Zrm_base ii b))
          (\(idx,b). constT (Zea_m s (idx + b + d))))`;

val ea_Zdest_def = Define `
  (ea_Zdest ii s (Zrm_i rm i) = ea_Zrm ii s rm) /\
  (ea_Zdest ii s (Zrm_r rm r) = ea_Zrm ii s rm) /\
  (ea_Zdest ii s (Zr_rm r rm) = ea_Zr s r)`;

val ea_Zsrc_def = Define `
  (ea_Zsrc ii s (Zrm_i rm i) = ea_Zi s i) /\
  (ea_Zsrc ii s (Zrm_r rm r) = ea_Zr s r) /\
  (ea_Zsrc ii s (Zr_rm r rm) = ea_Zrm ii s rm)`;

val ea_Zimm_rm_def = Define `
  (ea_Zimm_rm ii s (Zi_rm rm) = ea_Zrm ii s rm) /\
  (ea_Zimm_rm ii s (Zi i)     = ea_Zi s i)`;


(* eval_ea calculates the value of an effective address *)

val restrict_size_def = Define `
  (restrict_size Z8  (i:word64) = constT (w2w ((w2w i):word8))) /\
  (restrict_size Z16 (i:word64) = constT (w2w ((w2w i):word16))) /\
  (restrict_size Z32 (i:word64) = constT (w2w ((w2w i):word32))) /\
  (restrict_size Z64 (i:word64) = constT i)`;

val read_ea_def = Define `
  (read_ea ii (Zea_i s i) = seqT (constT i) (restrict_size s)) /\
  (read_ea ii (Zea_r s r) = seqT (read_reg ii r) (restrict_size s)) /\
  (read_ea ii (Zea_m Z8  a) = seqT (read_m8  ii a) (\w. constT (w2w w))) /\
  (read_ea ii (Zea_m Z16 a) = seqT (read_m16 ii a) (\w. constT (w2w w))) /\
  (read_ea ii (Zea_m Z32 a) = seqT (read_m32 ii a) (\w. constT (w2w w))) /\
  (read_ea ii (Zea_m Z64 a) = seqT (read_m64 ii a) (\w. constT w))`;

val read_src_ea_def = Define `
  read_src_ea ii s ds = seqT (ea_Zsrc ii s ds) (\ea. addT ea (read_ea ii ea))`;

val read_dest_ea_def = Define `
  read_dest_ea ii s ds = seqT (ea_Zdest ii s ds) (\ea. addT ea (read_ea ii ea))`;


(* write_ea write a value to the supplied effective address *)

val write_ea_def = Define `
  (write_ea ii (Zea_i s i) x = failureT) /\  (* one cannot store into a constant *)
  (* 32-bit write clears top 32-bits, the others just update a subset of the bits *)
  (write_ea ii (Zea_r Z8 r) x = seqT (read_reg ii r)
                                 (\w. write_reg ii r (((64--8)w) !! ((7--0)x)))) /\
  (write_ea ii (Zea_r Z16 r) x = seqT (read_reg ii r)
                                  (\w. write_reg ii r (((64--16)w) !! ((15--0)x)))) /\
  (write_ea ii (Zea_r Z32 r) x = write_reg ii r (w2w ((w2w x):word32))) /\
  (write_ea ii (Zea_r Z64 r) x = write_reg ii r x) /\
  (write_ea ii (Zea_m Z8 a) x = write_m8 ii a (w2w x)) /\
  (write_ea ii (Zea_m Z16 a) x = write_m16 ii a (w2w x)) /\
  (write_ea ii (Zea_m Z32 a) x = write_m32 ii a (w2w x)) /\
  (write_ea ii (Zea_m Z64 a) x = write_m64 ii a x)`;


(* jump_to_ea updates rip according to procedure call *)

val jump_to_ea_def = Define `
  (jump_to_ea ii rip (Zea_i s i) = write_rip ii (rip + i)) /\
  (jump_to_ea ii rip (Zea_r s r) = seqT (read_reg ii r) (write_rip ii)) /\
  (jump_to_ea ii rip (Zea_m s a) = seqT (read_m64 ii a) (write_rip ii))`;


(* call_dest_from_ea finds the destination according to procedure call semantics *)

val call_dest_from_ea_def = Define `
  (call_dest_from_ea ii rip (Zea_i s i) = constT (rip + i)) /\
  (call_dest_from_ea ii rip (Zea_r s r) = read_reg ii r) /\
  (call_dest_from_ea ii rip (Zea_m s a) = read_m64 ii a)`;

val get_ea_address_def = Define `
  (get_ea_address (Zea_i s i) = 0w) /\
  (get_ea_address (Zea_r s r) = 0w) /\
  (get_ea_address (Zea_m s a) = a)`;


(* rip modifiers *)

val bump_rip_def = Define `
  bump_rip ii len rest =
    parT_unit rest (seqT (read_rip ii) (\x. write_rip ii (x + len)))`;


(* eflag updates *)

val byte_parity_def = Define `
  byte_parity = EVEN o LENGTH o FILTER I o n2bits 8 o w2n`;

val word_size_msb_def = Define `
  (word_size_msb Z8  (w:word64) = word_msb ((w2w w):word8)) /\
  (word_size_msb Z16 (w:word64) = word_msb ((w2w w):word16)) /\
  (word_size_msb Z32 (w:word64) = word_msb ((w2w w):word32)) /\
  (word_size_msb Z64 (w:word64) = word_msb w)`;

val write_PF_def = Define `write_PF ii w = write_eflag ii Z_PF (SOME (byte_parity ((w2w w):word8)))`;
val write_SF_def = Define `write_SF ii s w = write_eflag ii Z_SF (SOME (word_size_msb s w))`;
val write_ZF_def = Define `
  (write_ZF ii Z8  w = write_eflag ii Z_ZF (SOME (w2w w = 0w:word8))) /\
  (write_ZF ii Z16 w = write_eflag ii Z_ZF (SOME (w2w w = 0w:word16))) /\
  (write_ZF ii Z32 w = write_eflag ii Z_ZF (SOME (w2w w = 0w:word32))) /\
  (write_ZF ii Z64 w = write_eflag ii Z_ZF (SOME (w = 0w)))`;

val write_logical_eflags_def = Define `
  write_logical_eflags ii s w =
     parT_unit (write_PF ii w)
    (parT_unit (write_ZF ii s w)
    (parT_unit (write_SF ii s w)
    (parT_unit (write_eflag ii Z_OF (SOME F))
    (parT_unit (write_eflag ii Z_CF (SOME F))
               (write_eflag ii Z_AF NONE)))))`;  (* not modelled *)

val write_arith_eflags_except_CF_OF_def = Define `
  write_arith_eflags_except_CF_OF ii s w =
     parT_unit (write_PF ii w)
    (parT_unit (write_ZF ii s w)
    (parT_unit (write_SF ii s w)
               (write_eflag ii Z_AF NONE)))`;

val write_arith_eflags_def = Define `
  write_arith_eflags ii s (w,c,x) =
    parT_unit (write_eflag ii Z_CF (SOME c))
   (parT_unit (write_eflag ii Z_OF (SOME x))
              (write_arith_eflags_except_CF_OF ii s w))`;

val erase_eflags_def = Define `
  erase_eflags ii =
     parT_unit (write_eflag ii Z_PF NONE)
    (parT_unit (write_eflag ii Z_ZF NONE)
    (parT_unit (write_eflag ii Z_SF NONE)
    (parT_unit (write_eflag ii Z_OF NONE)
    (parT_unit (write_eflag ii Z_CF NONE)
               (write_eflag ii Z_AF NONE)))))`;

(* binops *)

val value_width_def = Define `
  (value_width Z8  = 2**8) /\
  (value_width Z16 = 2**16) /\
  (value_width Z32 = 2**32) /\
  (value_width Z64 = 2**64)`;

val bool2num_def = Define `bool2num b = if b then 1 else 0`;

val word_signed_overflow_add_def = Define `
  word_signed_overflow_add s a b =
    (word_size_msb s a = word_size_msb s b) /\ ~(word_size_msb s (a + b) = word_size_msb s a)`;

val word_signed_overflow_sub_def = Define `
  word_signed_overflow_sub s a b =
    ~(word_size_msb s a = word_size_msb s b) /\ ~(word_size_msb s (a - b) = word_size_msb s a)`;

val add_with_carry_out_def = Define `
  add_with_carry_out s (x:Zimm) y =
    (x + y, value_width s <= w2n x + w2n y, word_signed_overflow_add s x y)`;

val sub_with_borrow_out_def = Define `
  sub_with_borrow_out s (x:Zimm) y =
     (x - y, x <+ y, word_signed_overflow_sub s x y)`;

val write_arith_result_def = Define `
  write_arith_result ii s (w,c,x) ea = parT_unit (write_arith_eflags ii s (w,c,x)) (write_ea ii ea w)`;

val write_arith_result_no_CF_OF_def = Define `
  write_arith_result_no_CF_OF ii s w ea =
    (parT_unit (write_arith_eflags_except_CF_OF ii s w) (write_ea ii ea w))`;

val write_arith_result_no_write_def = Define `
  write_arith_result_no_write ii s (w,c,x) = (write_arith_eflags ii s (w,c,x))`;

val write_logical_result_def = Define `
  write_logical_result ii s w ea = (parT_unit (write_logical_eflags ii s w) (write_ea ii ea w))`;

val write_logical_result_no_write_def = Define `
  write_logical_result_no_write ii s w = (write_logical_eflags ii s w)`;

val write_result_erase_eflags_def = Define `
  write_result_erase_eflags ii w ea = (parT_unit (erase_eflags ii) (write_ea ii ea w))`;

val write_binop_def = Define `
  (write_binop ii s Zadd  x y ea = (write_arith_result ii s (add_with_carry_out s x y) ea)) /\
  (write_binop ii s Zsub  x y ea = (write_arith_result ii s (sub_with_borrow_out s x y) ea)) /\
  (write_binop ii s Zcmp  x y ea = (write_arith_result_no_write ii s (sub_with_borrow_out s x y))) /\
  (write_binop ii s Ztest x y ea = (write_logical_result_no_write ii s (x && y))) /\
  (write_binop ii s Zand  x y ea = (write_logical_result ii s (x && y) ea)) /\
  (write_binop ii s Zxor  x y ea = (write_logical_result ii s (x ?? y) ea)) /\
  (write_binop ii s Zor   x y ea = (write_logical_result ii s (x !! y) ea)) /\
  (write_binop ii s Zshl  x y ea = (write_result_erase_eflags ii (x << w2n y) ea)) /\
  (write_binop ii s Zshr  x y ea = (write_result_erase_eflags ii (x >>> w2n y) ea)) /\
  (write_binop ii s Zsar  x y ea = (write_result_erase_eflags ii (x >> w2n y) ea)) /\
  (write_binop ii s _     x y ea = failureT)`;

val write_binop_with_carry_def = Define `
  (write_binop_with_carry ii s Zadc x y cf ea =
       parT_unit (write_eflag ii Z_CF (SOME (value_width s <= w2n x + w2n y + bool2num cf)))
      (parT_unit (write_eflag ii Z_OF NONE)
                 (write_arith_result_no_CF_OF ii s (x + y + n2w (bool2num cf)) ea))) /\
  (write_binop_with_carry ii s Zsbb x y cf ea =
       parT_unit (write_eflag ii Z_CF (SOME (w2n x < w2n y + bool2num cf)))
      (parT_unit (write_eflag ii Z_OF NONE)
                 (write_arith_result_no_CF_OF ii s (x - (y + n2w (bool2num cf))) ea))) /\
  (write_binop_with_carry ii s _    x y cf ea = failureT)`;

(* monops *)

val write_monop_def = Define `
  (write_monop ii s Znot x ea = write_ea ii ea (~x)) /\
  (write_monop ii s Zdec x ea = write_arith_result_no_CF_OF ii s (x - 1w) ea) /\
  (write_monop ii s Zinc x ea = write_arith_result_no_CF_OF ii s (x + 1w) ea) /\
  (write_monop ii s Zneg x ea =
    parT_unit (write_arith_result_no_CF_OF ii s (0w - x) ea)
                (write_eflag ii Z_CF NONE))`;

(* evaluating conditions of eflags *)

val read_cond_def = Define `
  (read_cond ii Z_ALWAYS = constT T) /\
  (read_cond ii Z_E      = read_eflag ii Z_ZF) /\
  (read_cond ii Z_S      = read_eflag ii Z_SF) /\
  (read_cond ii Z_B      = read_eflag ii Z_CF) /\
  (read_cond ii Z_NE     = seqT (read_eflag ii Z_ZF) (\b. constT (~b))) /\
  (read_cond ii Z_NS     = seqT (read_eflag ii Z_SF) (\b. constT (~b))) /\
  (read_cond ii Z_NB     = seqT (read_eflag ii Z_CF) (\b. constT (~b))) /\
  (read_cond ii Z_A      = seqT
     (parT (read_eflag ii Z_CF) (read_eflag ii Z_ZF)) (\(c,z). constT (~c /\ ~z))) /\
  (read_cond ii Z_NA     = seqT
     (parT (read_eflag ii Z_CF) (read_eflag ii Z_ZF)) (\(c,z). constT (c \/ z)))`;

(* execute stack operations for non-RIP registers *)

val x64_exec_pop_def = Define `
  x64_exec_pop ii rm =
     seqT (seqT (read_reg ii RSP) (\esp. addT esp (write_reg ii RSP (esp + 4w))))
          (\(old_esp,x). seqT (parT (ea_Zrm ii Z64 rm) (read_m64 ii old_esp))
                              (\(ea,w). write_ea ii ea w))`;

val x64_exec_push_def = Define `
  x64_exec_push ii imm_rm =
     (seqT
        (parT (seqT (ea_Zimm_rm ii Z64 imm_rm) (\ea. read_ea ii ea))
              (seqT (read_reg ii RSP) (\w. constT (w - 4w))))
        (\(w,esp). parT_unit (write_m64 ii esp w) (write_reg ii RSP esp)))`;

(* execute stack operations for RIP register *)

val x64_exec_pop_rip_def = Define `
  x64_exec_pop_rip ii =
     seqT (seqT (read_reg ii RSP) (\esp. addT esp (write_reg ii RSP (esp + 8w))))
          (\(old_esp,x). seqT (read_m64 ii old_esp)
                              (\w. write_rip ii w))`;

val x64_exec_push_rip_def = Define `
  x64_exec_push_rip ii =
     (seqT
        (parT (read_rip ii)
              (seqT (read_reg ii RSP) (\w. constT (w - 8w))))
        (\(w,esp). parT_unit (write_m64 ii esp w) (write_reg ii RSP esp)))`;

(* check whether rm requires a lock, i.e. specifies a memory access *)

(* execution of one instruction *)

val x64_exec_def = Define `
  (x64_exec ii (Zbinop binop_name s ds) len = bump_rip ii len
       (if (binop_name = Zadc) \/ (binop_name = Zsbb) then
          seqT
            (parT (parT (read_src_ea ii s ds) (read_dest_ea ii s ds))
                  (read_eflag ii Z_CF))
               (\ (((ea_src,val_src),(ea_dest,val_dest)),val_cf).
                  write_binop_with_carry ii s binop_name
                    val_dest val_src val_cf ea_dest)
        else
          seqT
            (parT (read_src_ea ii s ds) (read_dest_ea ii s ds))
               (\ ((ea_src,val_src),(ea_dest,val_dest)).
                  write_binop ii s binop_name val_dest val_src ea_dest))) /\
  (x64_exec ii (Zmonop monop_name s rm) len = bump_rip ii len
     (seqT
        (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
           (\ (ea_dest,val_dest).
              write_monop ii s monop_name val_dest ea_dest))) /\
  (x64_exec ii (Zmul s rm) len = bump_rip ii len
     (seqT
        (parT (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
        (parT (read_reg ii RAX) (assertT (~(s = Z8)))))
        (\ ((ea_src,val_src),(eax,nothing)).
              parT_unit (write_reg ii RAX (eax * val_src))
             (parT_unit (write_reg ii RDX (n2w ((w2n eax * w2n val_src) DIV value_width s)))
                        (erase_eflags ii)) (* here erase_flag is an over approximation *)))) /\
  (x64_exec ii (Zdiv s rm) len = bump_rip ii len
     (seqT
        (parT (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
              (seqT (parT (read_reg ii RAX) (read_reg ii RDX))
                    (\ (eax,edx). constT (w2n edx * value_width s + w2n eax))))
        (\ ((ea_src,val_src),n).
              parT_unit (assertT (~(val_src = 0w) /\ n DIV (w2n val_src) < value_width s))
             (parT_unit (write_reg ii RAX (n2w (n DIV (w2n val_src))))
             (parT_unit (write_reg ii RDX (n2w (n MOD (w2n val_src))))
                        (erase_eflags ii)))))) /\
  (x64_exec ii (Zxadd s rm r) len = bump_rip ii len
     (seqT
        (parT (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
              (parT (constT (Zea_r s r)) (read_reg ii r)))
        (\ ((ea_dest,val_dest),(ea_src,val_src)).
           seqT (write_ea ii ea_src val_dest)
                (\x. write_binop ii s Zadd val_src val_dest ea_dest)))) /\
  (x64_exec ii (Zxchg s rm r) len =
     (if Zrm_is_memory_access rm then lockT else I)
     (bump_rip ii len
     (if rm = (Zr r) then constT () else
       (seqT
          (parT (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
                (parT (constT (Zea_r s r)) (read_reg ii r)))
          (\ ((ea_dest,val_dest),(ea_src,val_src)).
             (parT_unit (write_ea ii ea_src val_dest)
                        (write_ea ii ea_dest val_src))))))) /\
  (x64_exec ii (Zcmpxchg s rm r) len = bump_rip ii len
     (seqT
        (parT (seqT (ea_Zrm ii s rm) (\ea. addT ea (read_ea ii ea)))
              (read_reg ii RAX))
        (\ ((dest_ea,dest_val),acc).
           parT_unit (write_binop ii s Zcmp acc dest_val (Zea_r s RAX))
                     (if acc = dest_val then
                        seqT (read_reg ii r) (\src_val. write_ea ii dest_ea src_val)
                      else
                        write_reg ii RAX dest_val)))) /\
  (x64_exec ii (Zpop rm) len = bump_rip ii len (x64_exec_pop ii rm)) /\
  (x64_exec ii (Zpush imm_rm) len = bump_rip ii len (x64_exec_push ii imm_rm)) /\
  (x64_exec ii (Zcall imm_rm) len =
     seqT (parT (bump_rip ii len (constT ()))
                (ea_Zimm_rm ii Z64 imm_rm)) (\ (x,ea).
     seqT (parT (x64_exec_push_rip ii)
                (read_rip ii)) (\ (x,rip).
     jump_to_ea ii rip ea))) /\
  (x64_exec ii (Zret imm) len =
     seqT (x64_exec_pop_rip ii ) (\x.
     seqT (read_reg ii RSP) (\esp. (write_reg ii RSP (esp + imm))))) /\
  (x64_exec ii (Zlea s ds) len = bump_rip ii len
     (seqT
        ((parT (ea_Zsrc ii s ds) (ea_Zdest ii s ds)))
           (\ (ea_src,ea_dest).
               write_ea ii ea_dest (get_ea_address ea_src)))) /\
  (x64_exec ii (Zmov c s ds) len = bump_rip ii len
     (seqT
        ((parT (read_src_ea ii s ds)
                  (parT (read_cond ii c) (ea_Zdest ii s ds))))
           (\ ((ea_src,val_src),(g,ea_dest)).
               if g then write_ea ii ea_dest val_src else constT ()))) /\
  (x64_exec ii (Zmovzx s ds s2) len = bump_rip ii len
     (seqT
        (parT (read_src_ea ii s2 ds) (ea_Zdest ii s ds))
        (\ ((ea_src,val_src),ea_dest).
           write_ea ii ea_dest (w2w val_src)))) /\
  (x64_exec ii (Zjcc c imm) len = (
     seqT
       (parT (read_rip ii) (read_cond ii c))
          (\ (rip,g). write_rip ii (if g then rip + len + imm else rip + len)))) /\
  (x64_exec ii (Zjmp rm) len = (
     seqT
       (seqT (ea_Zrm ii Z64 rm) (\ea. read_ea ii ea))
       (\new_rip.
          parT_unit (write_rip ii new_rip)
                    (clear_icache ii)))) /\
  (x64_exec ii (Zloop c imm) len =
     seqT (parT (read_rip ii) (
           parT (read_cond ii c)
                (seqT (read_reg ii RCX) (\ecx. constT (ecx - 1w)))))
          (\ (rip,guard,new_ecx).
             parT_unit (write_reg ii RCX new_ecx)
                       (write_rip ii
                         (if ~(new_ecx = 0w) /\ guard
                          then rip + len + imm else rip + len))))`;

val x64_execute_def = Define `
  x64_execute ii (Zfull_inst prefixes i) len =
    if MEM Zlock prefixes then lockT (x64_exec ii i len) else x64_exec ii i len`;


val _ = export_theory ();
