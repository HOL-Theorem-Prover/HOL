
open HolKernel boolLib bossLib Parse;
open wordsTheory bit_listTheory;

open x86_coretypesTheory x86_astTheory x86_seq_monadTheory;

val _ = new_theory "x86_opsem";


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

val ea_Xr_def = Define `ea_Xr (r:Xreg) = constT (Xea_r r)`;
val ea_Xi_def = Define `ea_Xi (i:Ximm) = constT (Xea_i i)`;

val ea_Xrm_base_def = Define `
  (ea_Xrm_base ii NONE = constT 0w) /\
  (ea_Xrm_base ii (SOME r) = read_reg ii r)`;

val ea_Xrm_index_def = Define `
  (ea_Xrm_index ii NONE = constT (0w:Ximm)) /\
  (ea_Xrm_index ii (SOME (s:word2,r)) =
     seqT (read_reg ii r) (\idx. constT (n2w (2 ** w2n s) * idx)))`;

val ea_Xrm_def = Define `
  (ea_Xrm ii (Xr r) = ea_Xr r) /\
  (ea_Xrm ii (Xm i b d) =
     seqT
        (parT (ea_Xrm_index ii i) (ea_Xrm_base ii b))
          (\(idx,b). constT (Xea_m (idx + b + d))))`;

val ea_Xdest_def = Define `
  (ea_Xdest ii (Xrm_i rm i) = ea_Xrm ii rm) /\
  (ea_Xdest ii (Xrm_r rm r) = ea_Xrm ii rm) /\
  (ea_Xdest ii (Xr_rm r rm) = ea_Xr r)`;

val ea_Xsrc_def = Define `
  (ea_Xsrc ii (Xrm_i rm i) = ea_Xi i) /\
  (ea_Xsrc ii (Xrm_r rm r) = ea_Xr r) /\
  (ea_Xsrc ii (Xr_rm r rm) = ea_Xrm ii rm)`;

val ea_Ximm_rm_def = Define `
  (ea_Ximm_rm ii (Xi_rm rm) = ea_Xrm ii rm) /\
  (ea_Ximm_rm ii (Xi i)     = ea_Xi i)`;

(* eval_ea calculates the value of an effective address *)

val read_ea_def = Define `
  (read_ea ii (Xea_i i) = constT i) /\
  (read_ea ii (Xea_r r) = read_reg ii r) /\
  (read_ea ii (Xea_m a) = read_m32 ii a)`;

val read_src_ea_def = Define `
  read_src_ea ii ds = seqT (ea_Xsrc ii ds) (\ea. addT ea (read_ea ii ea))`;

val read_dest_ea_def = Define `
  read_dest_ea ii ds = seqT (ea_Xdest ii ds) (\ea. addT ea (read_ea ii ea))`;

val read_reg_byte_def = Define `
  (read_reg_byte ii EAX = seqT (read_reg ii EAX) (\w. constT ((w2w w):word8))) /\
  (read_reg_byte ii EBX = seqT (read_reg ii EBX) (\w. constT (w2w w))) /\
  (read_reg_byte ii ECX = seqT (read_reg ii ECX) (\w. constT (w2w w))) /\
  (read_reg_byte ii EDX = seqT (read_reg ii EDX) (\w. constT (w2w w))) /\
  (read_reg_byte ii EBP = seqT (read_reg ii EAX) (\w. constT (w2w (w >>> 8)))) /\
  (read_reg_byte ii ESI = seqT (read_reg ii EBX) (\w. constT (w2w (w >>> 8)))) /\
  (read_reg_byte ii EDI = seqT (read_reg ii ECX) (\w. constT (w2w (w >>> 8)))) /\
  (read_reg_byte ii ESP = seqT (read_reg ii EDX) (\w. constT (w2w (w >>> 8))))`;

val read_ea_byte_def = Define `
  (read_ea_byte ii (Xea_i i) = constT (w2w i)) /\
  (read_ea_byte ii (Xea_r r) = read_reg_byte ii r) /\
  (read_ea_byte ii (Xea_m a) = read_m8 ii a)`;

val read_src_ea_byte_def = Define `
  read_src_ea_byte ii ds = seqT (ea_Xsrc ii ds) (\ea. addT ea (read_ea_byte ii ea))`;

val read_dest_ea_byte_def = Define `
  read_dest_ea_byte ii ds = seqT (ea_Xdest ii ds) (\ea. addT ea (read_ea_byte ii ea))`;

(* write_ea write a value to the supplied effective address *)

val write_ea_def = Define `
  (write_ea ii (Xea_i i) x = failureT) /\  (* one cannot store into a constant *)
  (write_ea ii (Xea_r r) x = write_reg ii r x) /\
  (write_ea ii (Xea_m a) x = write_m32 ii a x)`;

val write_ea_byte_def = Define `
  (write_ea_byte ii (Xea_i i) x = failureT) /\  (* one cannot store into a constant *)
  (write_ea_byte ii (Xea_r r) x = failureT) /\  (* not supported yet *)
  (write_ea_byte ii (Xea_m a) x = write_m8 ii a x)`;

(* jump_to_ea updates eip according to procedure call *)

val jump_to_ea_def = Define `
  (jump_to_ea ii eip (Xea_i i) = write_eip ii (eip + i)) /\
  (jump_to_ea ii eip (Xea_r r) = seqT (read_reg ii r) (write_eip ii)) /\
  (jump_to_ea ii eip (Xea_m a) = seqT (read_m32 ii a) (write_eip ii))`;

(* call_dest_from_ea finds the destination according to procedure call semantics *)

val call_dest_from_ea_def = Define `
  (call_dest_from_ea ii eip (Xea_i i) = constT (eip + i)) /\
  (call_dest_from_ea ii eip (Xea_r r) = read_reg ii r) /\
  (call_dest_from_ea ii eip (Xea_m a) = read_m32 ii a)`;

val get_ea_address_def = Define `
  (get_ea_address (Xea_i i) = 0w) /\
  (get_ea_address (Xea_r r) = 0w) /\
  (get_ea_address (Xea_m a) = a)`;

(* eip modifiers *)

val bump_eip_def = Define `
  bump_eip ii len rest =
    parT_unit rest (seqT (read_eip ii) (\x. write_eip ii (x + len)))`;

(* eflag updates *)

val byte_parity_def = Define `
  byte_parity = EVEN o LENGTH o FILTER I o n2bits 8 o w2n`;

val write_PF_def = Define `write_PF ii w = write_eflag ii X_PF (SOME (byte_parity w))`;
val write_ZF_def = Define `write_ZF ii w = write_eflag ii X_ZF (SOME (w = 0w))`;
val write_SF_def = Define `write_SF ii w = write_eflag ii X_SF (SOME (word_msb w))`;

val write_logical_eflags_def = Define `
  write_logical_eflags ii w =
     parT_unit (write_PF ii w)
    (parT_unit (write_ZF ii w)
    (parT_unit (write_SF ii w)
    (parT_unit (write_eflag ii X_OF (SOME F))
    (parT_unit (write_eflag ii X_CF (SOME F))
               (write_eflag ii X_AF NONE)))))`;  (* not modelled *)

val write_arith_eflags_except_CF_OF_def = Define `
  write_arith_eflags_except_CF_OF ii w =
     parT_unit (write_PF ii w)
    (parT_unit (write_ZF ii w)
    (parT_unit (write_SF ii w)
               (write_eflag ii X_AF NONE)))`;

val write_arith_eflags_def = Define `
  write_arith_eflags ii (w,c,x) =
    parT_unit (write_eflag ii X_CF (SOME c))
   (parT_unit (write_eflag ii X_OF (SOME x))
              (write_arith_eflags_except_CF_OF ii w))`;

val erase_eflags_def = Define `
  erase_eflags ii =
     parT_unit (write_eflag ii X_PF NONE)
    (parT_unit (write_eflag ii X_ZF NONE)
    (parT_unit (write_eflag ii X_SF NONE)
    (parT_unit (write_eflag ii X_OF NONE)
    (parT_unit (write_eflag ii X_CF NONE)
               (write_eflag ii X_AF NONE)))))`;

(* binops *)

val bool2num_def = Define `bool2num b = if b then 1 else 0`;

val word_signed_overflow_add_def = Define `
  word_signed_overflow_add a b =
    (word_msb a = word_msb b) /\ ~(word_msb (a + b) = word_msb a)`;

val word_signed_overflow_sub_def = Define `
  word_signed_overflow_sub a b =
    ~(word_msb a = word_msb b) /\ ~(word_msb (a - b) = word_msb a)`;

val add_with_carry_out_def = Define `
  add_with_carry_out (x:Ximm) y =
    (x + y, 2**32 <= w2n x + w2n y, word_signed_overflow_add x y)`;

val sub_with_borrow_out_def = Define `
  sub_with_borrow_out (x:Ximm) y =
     (x - y, x <+ y, word_signed_overflow_sub x y)`;

val write_arith_result_def = Define `
  write_arith_result ii (w,c,x) ea = parT_unit (write_arith_eflags ii (w,c,x)) (write_ea ii ea w)`;

val write_arith_result_no_CF_OF_def = Define `
  write_arith_result_no_CF_OF ii w ea =
    (parT_unit (write_arith_eflags_except_CF_OF ii w) (write_ea ii ea w))`;

val write_arith_result_no_write_def = Define `
  write_arith_result_no_write ii (w,c,x) = (write_arith_eflags ii (w,c,x))`;

val write_logical_result_def = Define `
  write_logical_result ii w ea = (parT_unit (write_logical_eflags ii w) (write_ea ii ea w))`;

val write_logical_result_no_write_def = Define `
  write_logical_result_no_write ii w = (write_logical_eflags ii w)`;

val write_result_erase_eflags_def = Define `
  write_result_erase_eflags ii w ea = (parT_unit (erase_eflags ii) (write_ea ii ea w))`;

val write_binop_def = Define `
  (write_binop ii Xadd  x y ea = (write_arith_result ii (add_with_carry_out x y) ea)) /\
  (write_binop ii Xsub  x y ea = (write_arith_result ii (sub_with_borrow_out x y) ea)) /\
  (write_binop ii Xcmp  x y ea = (write_arith_result_no_write ii (sub_with_borrow_out x y))) /\
  (write_binop ii Xtest x y ea = (write_logical_result_no_write ii (x && y))) /\
  (write_binop ii Xand  x y ea = (write_logical_result ii (x && y) ea)) /\
  (write_binop ii Xxor  x y ea = (write_logical_result ii (x ?? y) ea)) /\
  (write_binop ii Xor   x y ea = (write_logical_result ii (x !! y) ea)) /\
  (write_binop ii Xshl  x y ea = (write_result_erase_eflags ii (x << w2n y) ea)) /\
  (write_binop ii Xshr  x y ea = (write_result_erase_eflags ii (x >>> w2n y) ea)) /\
  (write_binop ii Xsar  x y ea = (write_result_erase_eflags ii (x >> w2n y) ea)) /\
  (write_binop ii _     x y ea = failureT)`;

val write_binop_with_carry_def = Define `
  (write_binop_with_carry ii Xadc x y cf ea =
       parT_unit (write_eflag ii X_CF (SOME (2**32 <= w2n x + w2n y + bool2num cf)))
      (parT_unit (write_eflag ii X_OF NONE)
                 (write_arith_result_no_CF_OF ii (x + y + n2w (bool2num cf)) ea))) /\
  (write_binop_with_carry ii Xsbb x y cf ea =
       parT_unit (write_eflag ii X_CF (SOME (w2n x < w2n y + bool2num cf)))
      (parT_unit (write_eflag ii X_OF NONE)
                 (write_arith_result_no_CF_OF ii (x - (y + n2w (bool2num cf))) ea))) /\
  (write_binop_with_carry ii _    x y cf ea = failureT)`;

(* monops *)

val write_monop_def = Define `
  (write_monop ii Xnot x ea = write_ea ii ea (~x)) /\
  (write_monop ii Xdec x ea = write_arith_result_no_CF_OF ii (x - 1w) ea) /\
  (write_monop ii Xinc x ea = write_arith_result_no_CF_OF ii (x + 1w) ea) /\
  (write_monop ii Xneg x ea =
    parT_unit (write_arith_result_no_CF_OF ii (0w - x) ea)
                (write_eflag ii X_CF NONE))`;

(* evaluating conditions of eflags *)

val read_cond_def = Define `
  (read_cond ii X_ALWAYS = constT T) /\
  (read_cond ii X_E      = read_eflag ii X_ZF) /\
  (read_cond ii X_S      = read_eflag ii X_SF) /\
  (read_cond ii X_B      = read_eflag ii X_CF) /\
  (read_cond ii X_NE     = seqT (read_eflag ii X_ZF) (\b. constT (~b))) /\
  (read_cond ii X_NS     = seqT (read_eflag ii X_SF) (\b. constT (~b))) /\
  (read_cond ii X_NB     = seqT (read_eflag ii X_CF) (\b. constT (~b))) /\
  (read_cond ii X_A      = seqT
     (parT (read_eflag ii X_CF) (read_eflag ii X_ZF)) (\(c,z). constT (~c /\ ~z))) /\
  (read_cond ii X_NA     = seqT
     (parT (read_eflag ii X_CF) (read_eflag ii X_ZF)) (\(c,z). constT (c \/ z)))`;

(* execute stack operations for non-EIP registers *)

val x86_exec_pop_def = Define `
  x86_exec_pop ii rm =
     seqT (seqT (read_reg ii ESP) (\esp. addT esp (write_reg ii ESP (esp + 4w))))
          (\(old_esp,x). seqT (parT (ea_Xrm ii rm) (read_m32 ii old_esp))
                              (\(ea,w). write_ea ii ea w))`;

val x86_exec_push_def = Define `
  x86_exec_push ii imm_rm =
     (seqT
        (parT (seqT (ea_Ximm_rm ii imm_rm) (\ea. read_ea ii ea))
              (seqT (read_reg ii ESP) (\w. constT (w - 4w))))
        (\(w,esp). parT_unit (write_m32 ii esp w) (write_reg ii ESP esp)))`;

(* execute stack operations for EIP register *)

val x86_exec_pop_eip_def = Define `
  x86_exec_pop_eip ii =
     seqT (seqT (read_reg ii ESP) (\esp. addT esp (write_reg ii ESP (esp + 4w))))
          (\(old_esp,x). seqT (read_m32 ii old_esp)
                              (\w. write_eip ii w))`;

val x86_exec_push_eip_def = Define `
  x86_exec_push_eip ii =
     (seqT
        (parT (read_eip ii)
              (seqT (read_reg ii ESP) (\w. constT (w - 4w))))
        (\(w,esp). parT_unit (write_m32 ii esp w) (write_reg ii ESP esp)))`;

(* check whether rm requires a lock, i.e. specifies a memory access *)

(* execution of one instruction *)

val x86_exec_def = Define `
  (x86_exec ii (Xbinop binop_name ds) len = bump_eip ii len
       (if (binop_name = Xadc) \/ (binop_name = Xsbb) then
          seqT
            (parT (parT (read_src_ea ii ds) (read_dest_ea ii ds))
                  (read_eflag ii X_CF))
               (\ (((ea_src,val_src),(ea_dest,val_dest)),val_cf).
                  write_binop_with_carry ii binop_name
                    val_dest val_src val_cf ea_dest)
        else
          seqT
            (parT (read_src_ea ii ds) (read_dest_ea ii ds))
               (\ ((ea_src,val_src),(ea_dest,val_dest)).
                  write_binop ii binop_name val_dest val_src ea_dest))) /\
  (x86_exec ii (Xmonop monop_name rm) len = bump_eip ii len
     (seqT
        (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
           (\ (ea_dest,val_dest).
              write_monop ii monop_name val_dest ea_dest))) /\
  (x86_exec ii (Xmul rm) len = bump_eip ii len
     (seqT
        (parT (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
              (read_reg ii EAX))
        (\ ((ea_src,val_src),eax).
              parT_unit (write_reg ii EAX (eax * val_src))
             (parT_unit (write_reg ii EDX (n2w ((w2n eax * w2n val_src) DIV 2**32)))
                        (erase_eflags ii)) (* here erase_flag is an over approximation *)))) /\
  (x86_exec ii (Xdiv rm) len = bump_eip ii len
     (seqT
        (parT (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
              (seqT (parT (read_reg ii EAX) (read_reg ii EDX))
                    (\ (eax,edx). constT (w2n edx * 2**32 + w2n eax))))
        (\ ((ea_src,val_src),n).
              parT_unit (assertT (~(val_src = 0w) /\ n DIV (w2n val_src) < 2**32))
             (parT_unit (write_reg ii EAX (n2w (n DIV (w2n val_src))))
             (parT_unit (write_reg ii EDX (n2w (n MOD (w2n val_src))))
                        (erase_eflags ii)))))) /\
  (x86_exec ii (Xxadd rm r) len = bump_eip ii len
     (seqT
        (parT (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
              (parT (constT (Xea_r r)) (read_reg ii r)))
        (\ ((ea_dest,val_dest),(ea_src,val_src)).
           seqT (write_ea ii ea_src val_dest)
                (\x. write_binop ii Xadd val_src val_dest ea_dest)))) /\
  (x86_exec ii (Xxchg rm r) len =
     (if rm_is_memory_access rm then lockT else I)
     (bump_eip ii len
     (if rm = (Xr r) then constT () else
       (seqT
          (parT (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
                (parT (constT (Xea_r r)) (read_reg ii r)))
          (\ ((ea_dest,val_dest),(ea_src,val_src)).
             (parT_unit (write_ea ii ea_src val_dest)
                        (write_ea ii ea_dest val_src))))))) /\
  (x86_exec ii (Xcmpxchg rm r) len = bump_eip ii len
     (seqT
        (parT (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea ii ea)))
              (read_reg ii EAX))
        (\ ((dest_ea,dest_val),acc).
           parT_unit (write_binop ii Xcmp acc dest_val (Xea_r EAX))
                     (if acc = dest_val then
                        seqT (read_reg ii r) (\src_val. write_ea ii dest_ea src_val)
                      else
                        write_reg ii EAX dest_val)))) /\
  (x86_exec ii (Xpop rm) len = bump_eip ii len (x86_exec_pop ii rm)) /\
  (x86_exec ii (Xpush imm_rm) len = bump_eip ii len (x86_exec_push ii imm_rm)) /\
  (x86_exec ii (Xcall imm_rm) len =
     seqT (parT (bump_eip ii len (constT ()))
                (ea_Ximm_rm ii imm_rm)) (\ (x,ea).
     seqT (parT (x86_exec_push_eip ii)
                (read_eip ii)) (\ (x,eip).
     jump_to_ea ii eip ea))) /\
  (x86_exec ii (Xret imm) len =
     seqT (x86_exec_pop_eip ii ) (\x.
     seqT (read_reg ii ESP) (\esp. (write_reg ii ESP (esp + imm))))) /\
  (x86_exec ii (Xlea ds) len = bump_eip ii len
     (seqT
        ((parT (ea_Xsrc ii ds) (ea_Xdest ii ds)))
           (\ (ea_src,ea_dest).
               write_ea ii ea_dest (get_ea_address ea_src)))) /\
  (x86_exec ii (Xmov c ds) len = bump_eip ii len
     (seqT
        ((parT (read_src_ea ii ds)
                  (parT (read_cond ii c) (ea_Xdest ii ds))))
           (\ ((ea_src,val_src),(g,ea_dest)).
               if g then write_ea ii ea_dest val_src else constT ()))) /\
  (x86_exec ii (Xdec_byte rm) len = bump_eip ii len
     (seqT
        (seqT (ea_Xrm ii rm) (\ea. addT ea (read_ea_byte ii ea)))
        (\ (ea_src,val_src).
           parT_unit (write_ea_byte ii ea_src (val_src - 1w))
                     (erase_eflags ii)))) /\
  (x86_exec ii (Xmovzx ds) len = bump_eip ii len
     (seqT
        (parT (read_src_ea_byte ii ds) (ea_Xdest ii ds))
        (\ ((ea_src,val_src),ea_dest).
           write_ea ii ea_dest (w2w val_src)))) /\
  (x86_exec ii (Xmov_byte ds) len = bump_eip ii len
     (seqT
        (parT (read_src_ea_byte ii ds) (ea_Xdest ii ds))
        (\ ((ea_src,val_src),ea_dest).
           write_ea_byte ii ea_dest val_src))) /\
  (x86_exec ii (Xcmp_byte ds) len = bump_eip ii len
     (seqT
        (parT (read_src_ea_byte ii ds) (read_dest_ea_byte ii ds))
           (\ ((ea_src,val_src),(ea_dest,val_dest)).
              write_binop ii Xcmp (w2w val_dest) (w2w val_src) ea_dest))) /\
  (x86_exec ii (Xjcc c imm) len = (
     seqT
       (parT (read_eip ii) (read_cond ii c))
          (\ (eip,g). write_eip ii (if g then eip + len + imm else eip + len)))) /\
  (x86_exec ii (Xjmp rm) len = (
     seqT
       (seqT (ea_Xrm ii rm) (\ea. read_ea ii ea))
       (\new_eip.
          parT_unit (write_eip ii new_eip)
                    (clear_icache ii)))) /\
  (x86_exec ii (Xloop c imm) len =
     seqT (parT (read_eip ii) (
           parT (read_cond ii c)
                (seqT (read_reg ii ECX) (\ecx. constT (ecx - 1w)))))
          (\ (eip,guard,new_ecx).
             parT_unit (write_reg ii ECX new_ecx)
                       (write_eip ii
                         (if ~(new_ecx = 0w) /\ guard
                          then eip + len + imm else eip + len)))) /\
  (x86_exec ii (Xpushad) len = bump_eip ii len (
     seqT (read_reg ii ESP) (\original_esp.
     seqT (x86_exec_push ii (Xi_rm (Xr EAX))) (\x.
     seqT (x86_exec_push ii (Xi_rm (Xr ECX))) (\x.
     seqT (x86_exec_push ii (Xi_rm (Xr EDX))) (\x.
     seqT (x86_exec_push ii (Xi_rm (Xr EBX))) (\x.
     seqT (write_reg ii ESP original_esp) (\x.
     seqT (x86_exec_push ii (Xi_rm (Xr EBP))) (\x.
     seqT (x86_exec_push ii (Xi_rm (Xr ESI))) (\x.
          (x86_exec_push ii (Xi_rm (Xr EDI))))))))))))) /\
  (x86_exec ii (Xpopad)  len = bump_eip ii len (
     seqT (x86_exec_pop ii (Xr EDI)) (\x.
     seqT (x86_exec_pop ii (Xr ESI)) (\x.
     seqT (x86_exec_pop ii (Xr EBP)) (\x.
     seqT (seqT (read_reg ii ESP) (\esp. write_reg ii ESP (esp + 4w))) (\x.
     seqT (x86_exec_pop ii (Xr EBX)) (\x.
     seqT (x86_exec_pop ii (Xr EDX)) (\x.
     seqT (x86_exec_pop ii (Xr ECX)) (\x.
     seqT (x86_exec_pop ii (Xr EAX)) (\x. constT ()))))))))))`;

val x86_execute_def = Define `
  (x86_execute ii (Xprefix Xg1_none g2 i) len = x86_exec ii i len) /\
  (x86_execute ii (Xprefix Xlock g2 i) len    = lockT (x86_exec ii i len))`;


val _ = export_theory ();
