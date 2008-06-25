open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open decoderTheory combinTheory opmonTheory bit_listTheory;

val _ = new_theory "ppc";


(* =============================================================== *)
(*  PowerPC ABSTRACT SYNTAX TREE                                   *)
(* =============================================================== *)

val _ = type_abbrev("ireg",``:word5``);
val _ = type_abbrev("freg",``:word5``);
val _ = type_abbrev("constant",``:word16``);
val _ = type_abbrev("crbit",``:word2``);

(* 

  Removed:

  | Pallocframe of Z => Z     (* allocate new stack frame *)
  | Pallocblock               (* allocate new heap block *)
  | Plfi of freg => float     (* load float constant *)
  | Plabel of label           (* define a code label *)
  | Pfreeframe                (* deallocate stack frame and restore previous frame *)
  | Pmfcrbit of ireg => crbit              (* move condition bit to reg *)

  I left out the following and anything with float or freg.
 
  I changed rlwinm.

*)

val _ = Hol_datatype `
  instruction =
    Padd of ireg => ireg => ireg           (* integer addition *)
  | Paddi of ireg => ireg => constant      (* add immediate *)
  | Paddis of ireg => ireg => constant     (* add immediate high *)
  | Paddze of ireg => ireg                 (* add Carry bit *)
  | Pand_ of ireg => ireg => ireg          (* bitwise and *)
  | Pandc of ireg => ireg => ireg          (* bitwise and-complement *)
  | Pandi_ of ireg => ireg => constant     (* and immediate and set conditions *)
  | Pandis_ of ireg => ireg => constant    (* and immediate high and set conditions *)
  | Pb of word24                           (* unconditional branch *)
  | Pbctr                                  (* branch to contents of register CTR *)
  | Pbctrl                                 (* branch to contents of CTR and link *)
  | Pbf of crbit => 14 word                (* branch if false *)
  | Pbl of word24                          (* branch and link *)
  | Pbs of word24                          (* branch to symbol *)
  | Pblr                                   (* branch to contents of register LR *)
  | Pbt of crbit => 14 word                (* branch if true *)
  | Pcmplw of ireg => ireg                 (* unsigned integer comparison *)
  | Pcmplwi of ireg => constant            (* same, with immediate argument *)
  | Pcmpw of ireg => ireg                  (* signed integer comparison *)
  | Pcmpwi of ireg => constant             (* same, with immediate argument *)
  | Pcror of crbit => crbit => crbit       (* or between condition bits *)
  | Pdivw of ireg => ireg => ireg          (* signed division *)
  | Pdivwu of ireg => ireg => ireg         (* unsigned division *)
  | Peqv of ireg => ireg => ireg           (* bitwise not-xor *)
  | Pextsb of ireg => ireg                 (* 8-bit sign extension *)
  | Pextsh of ireg => ireg                 (* 16-bit sign extension *)
  | Pfabs of freg => freg                  (* float absolute value *)
  | Pfadd of freg => freg => freg          (* float addition *)
  | Pfcmpu of freg => freg                 (* float comparison *)
  | Pfcti of ireg => freg                  (* float-to-int conversion *)
  | Pfdiv of freg => freg => freg          (* float division *)
  | Pfmadd of freg => freg => freg => freg (* float multiply-add *)
  | Pfmr of freg => freg                   (* float move *)
  | Pfmsub of freg => freg => freg => freg (* float multiply-sub *)
  | Pfmul of freg => freg => freg          (* float multiply *)
  | Pfneg of freg => freg                  (* float negation *)
  | Pfrsp of freg => freg                  (* float round to single precision *)
  | Pfsub of freg => freg => freg          (* float subtraction *)
  | Pictf of freg => ireg                  (* int-to-float conversion *)
  | Piuctf of freg => ireg                 (* unsigned int-to-float conversion *)
  | Plbz of ireg => constant => ireg       (* load 8-bit unsigned word32 *)
  | Plbzx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Plfd of freg => constant => ireg       (* load 64-bit float *)
  | Plfdx of freg => ireg => ireg          (* same, with 2 index regs *)
  | Plfs of freg => constant => ireg       (* load 32-bit float *)
  | Plfsx of freg => ireg => ireg          (* same, with 2 index regs *)
  | Plha of ireg => constant => ireg       (* load 16-bit signed word32 *)
  | Plhax of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Plhz of ireg => constant => ireg       (* load 16-bit unsigned word32 *)
  | Plhzx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Plwz of ireg => constant => ireg       (* load 32-bit word32 *)
  | Plwzx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Pmfcrbit of ireg => crbit              (* move condition bit to reg *)
  | Pmflr of ireg                          (* move LR to reg *)
  | Pmr of ireg => ireg                    (* integer move *)
  | Pmtctr of ireg                         (* move ireg to CTR *)
  | Pmtlr of ireg                          (* move ireg to LR *)
  | Pmulli of ireg => ireg => constant     (* integer multiply immediate *)
  | Pmullw of ireg => ireg => ireg         (* integer multiply *)
  | Pnand of ireg => ireg => ireg          (* bitwise not-and *)
  | Pnor of ireg => ireg => ireg           (* bitwise not-or *)
  | Por of ireg => ireg => ireg            (* bitwise or *)
  | Porc of ireg => ireg => ireg           (* bitwise or-complement *)
  | Pori of ireg => ireg => constant       (* or with immediate *)
  | Poris of ireg => ireg => constant      (* or with immediate high *)
  | Prlwinm of ireg => ireg => word5 => word5 => word5 (* rotate and mask *)
  | Pslw of ireg => ireg => ireg           (* shift left *)
  | Psraw of ireg => ireg => ireg          (* shift right signed *)
  | Psrawi of ireg => ireg => word5        (* shift right signed immediate *)
  | Psrw of ireg => ireg => ireg           (* shift right unsigned *)
  | Pstb of ireg => constant => ireg       (* store 8-bit word *)
  | Pstbx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Pstfd of freg => constant => ireg      (* store 64-bit float *)
  | Pstfdx of freg => ireg => ireg         (* same, with 2 index regs *)
  | Pstfs of freg => constant => ireg      (* store 32-bit float *)
  | Pstfsx of freg => ireg => ireg         (* same, with 2 index regs *)
  | Psth of ireg => constant => ireg       (* store 16-bit word *)
  | Psthx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Pstw of ireg => constant => ireg       (* store 32-bit word*)
  | Pstwx of ireg => ireg => ireg          (* same, with 2 index regs *)
  | Psubfc of ireg => ireg => ireg         (* reversed integer subtraction *)
  | Psubfic of ireg => ireg => constant    (* integer subtraction from immediate *)
  | Pxor of ireg => ireg => ireg           (* bitwise xor *)
  | Pxori of ireg => ireg => constant      (* bitwise xor with immediate *)
  | Pxoris of ireg => ireg => constant     (* bitwise xor with immediate high *)
`;

(*
fun override_datatype name = let
  val _ = save_thm(name^"_11",TRUTH)
  val _ = save_thm(name^"_distinct",TRUTH)
  val _ = save_thm(name^"_case_cong",TRUTH)
  val _ = save_thm(name^"_nchotomy",TRUTH)
  val _ = save_thm(name^"_induction",TRUTH)
  val _ = save_thm(name^"_TY_DEF",TRUTH)
  val _ = save_thm(name^"_repfns",TRUTH)
  val _ = save_thm(name^"_case_def",TRUTH)
  in () end;

val _ = override_datatype "instruction";
*)

(* =============================================================== *)
(*  PowerPC OPERATIONAL SEMANTICS                                  *)
(* =============================================================== *)

val _ = Hol_datatype `
  ppc_bit = PPC_CARRY     (* carry bit of the status register *)
          | PPC_CR0 of word2  (* bit i of the condition register  *)`;

val _ = Hol_datatype `
  ppc_reg = PPC_IR of word5  (* integer registers *) 
          | PPC_LR           (* link register (return address) *)
          | PPC_CTR          (* count register, used for some branches *)
          | PPC_PC           (* program counter *)`;

val ppc_reg_distinct   = fetch "-" "ppc_reg_distinct";

val _ = type_abbrev("ppc_state",
  ``:(ppc_reg -> word32) # (ppc_bit -> bool option) # (word32 -> word8 option)``);

(* read/write regs, bits and memory *)

val PREAD_R_def = Define `PREAD_R rd ((r,s,m):ppc_state) = r rd`;
val PREAD_S_def = Define `PREAD_S rd ((r,s,m):ppc_state) = s rd`;
val PREAD_M_def = Define `PREAD_M rd ((r,s,m):ppc_state) = m rd`;

val PWRITE_R_def = Define `PWRITE_R rd x (r,s,m) = ((rd =+ x) r,s,m):ppc_state`;
val PWRITE_S_def = Define `PWRITE_S rd x (r,s,m) = (r,(rd =+ x) s,m):ppc_state`;
val PWRITE_M_def = Define `PWRITE_M rd x (r,s,m) = (r,s,(rd =+ x) m):ppc_state`;

val PPC_SINT_CMP_def = Define `
  PPC_SINT_CMP (a:word32) (b:word32) =
    PWRITE_S (PPC_CR0 0w) (SOME (a < b)) o 
    PWRITE_S (PPC_CR0 1w) (SOME (b < a)) o 
    PWRITE_S (PPC_CR0 2w) (SOME (a = b)) o 
    PWRITE_S (PPC_CR0 3w) NONE`;

val PPC_UINT_CMP_def = Define `
  PPC_UINT_CMP (a:word32) (b:word32) =
    PWRITE_S (PPC_CR0 0w) (SOME (a <+ b)) o 
    PWRITE_S (PPC_CR0 1w) (SOME (b <+ a)) o 
    PWRITE_S (PPC_CR0 2w) (SOME (a = b)) o 
    PWRITE_S (PPC_CR0 3w) NONE`;

val reg_write_def = Define `reg_write rd = opt_s_pop (PWRITE_R rd)`;
val read_ctr_def  = Define `read_ctr = opt_push (PREAD_R PPC_CTR)`;
val read_lr_def   = Define `read_lr  = opt_push (PREAD_R PPC_LR)`;
val read_pc_def   = Define `read_pc  = opt_push (PREAD_R PPC_PC)`;
val set_ctr_def   = Define `set_ctr = opt_s_pop (PWRITE_R PPC_CTR)`;
val set_lr_def    = Define `set_lr  = opt_s_pop (PWRITE_R PPC_LR)`;
val set_pc_def    = Define `set_pc  = opt_s_pop (PWRITE_R PPC_PC)`;

val pc_inc_def = Define `
  pc_inc = read_pc >> opt_monop (\x. x + 4w) >> set_pc`;

val pc_to_lr_def = Define `
  pc_to_lr = read_pc >> opt_monop (\x. x + 4w) >> set_lr`;

val OK_nextinstr_def = Define `OK_nextinstr f = LOCAL (f >>| pc_inc)`;

val reg_update_def = Define `
  reg_update rd f s1 s2 = 
    (s1 >>| s2) >> opt_binop f >> opt_s_pop (PWRITE_R (PPC_IR rd))`;

val uint_reg_update_def = Define `
  uint_reg_update rd f s1 s2 =
    (s1 >>| s2) >> opt_binop f >> opt_dup >>
      (opt_s_pop (PWRITE_R (PPC_IR rd)) >> opt_s_pop (\x. PPC_UINT_CMP x 0w))`;

val sint_reg_update_def = Define `
  sint_reg_update rd f s1 s2 =
    (s1 >>| s2) >> opt_binop f >> opt_dup >>
      (opt_s_pop (PWRITE_R (PPC_IR rd)) >> opt_s_pop (\x. PPC_SINT_CMP x 0w))`;

val uint_compare_def = Define `
  uint_compare s1 s2 = (s1 >>| s2) >> opt_s_pop2 PPC_UINT_CMP`;

val sint_compare_def = Define `
  sint_compare s1 s2 = (s1 >>| s2) >> opt_s_pop2 PPC_SINT_CMP`;

val bit_update_def = Define `
  bit_update bd (f:bool->bool->bool) s1 s2 = 
    (s1 >>| s2) >> opt_binop f >> opt_s_pop (PWRITE_S bd o SOME)`;

val const_low_def  = Define `const_low w = opt_push (K ((w2w:word16->word32) w))`;
val const_high_def = Define `const_high w = opt_push (K ((w2w:word16->word32) w << 16))`;

val read_bit_def = Define `
  read_bit i = opt_push (PREAD_S i) >> opt_assert (\((v,x),s). ~(v = NONE)) >> opt_monop THE`;

val read_bit_word_def = Define `
  read_bit_word i = read_bit i >> opt_monop (\x. if x then 1w else 0w:word32)`;

val read_reg_def = Define `
  read_reg i = opt_push (PREAD_R (PPC_IR i))`;

val gpr_or_zero_def = Define `gpr_or_zero d = if d = 0w then const_low 0w else read_reg d`;

val no_carry_def = Define `
  no_carry = opt_push (K NONE) >> opt_s_pop (PWRITE_S PPC_CARRY)`;

val goto_label_def = Define `
  goto_label l = read_pc >> opt_monop (\x. x + sw2sw l * 4w) >> set_pc`;

val mem_read_bytes_def = Define `
  mem_read_bytes n a s =
    if n = 0 then [] else PREAD_M a s :: mem_read_bytes (n-1) (a+1w) s`;

val mem_access_ok_def = Define `
  mem_access_ok size = opt_assert 
    (\((a,x),s). address_aligned size a /\
                 EVERY (\x. ~(x = NONE)) (mem_read_bytes size a s))`;

val push_eaddress_def = Define `
  push_eaddress size s1 s2 = (s1 >>| s2) >> opt_binop $+`;

val PWRITE_M_LIST_def = Define `
  (PWRITE_M_LIST a [] s = s) /\
  (PWRITE_M_LIST a (b::bs) s = PWRITE_M a (SOME b) (PWRITE_M_LIST (a+1w) bs s))`;

val PREAD_MDATA_def = Define `
  PREAD_MDATA size a s =
    (bytes2word o REVERSE o MAP THE o mem_read_bytes size a) s`;

val PWRITE_MDATA_def = Define `
  PWRITE_MDATA size a w s =
    PWRITE_M_LIST a (REVERSE (word2bytes size w)) s`

val read_mem_def = Define `
  read_mem size = mem_access_ok size >> opt_s_push (PREAD_MDATA size)`;

val write_mem_def = Define `
  write_mem size = 
    opt_swap >> mem_access_ok size >> opt_swap >> opt_s_pop2 (PWRITE_MDATA size)`;

val reg_store_def = Define `
  reg_store size rd s1 s2 =
    (push_eaddress size s1 s2 >>| read_reg rd) >> write_mem size`;

val reg_load_def = Define `
  reg_load size rd s1 s2 =
    push_eaddress size s1 s2 >> read_mem size >> reg_write (PPC_IR rd)`;

val ppc_exec_instr_def = Define `
  (ppc_exec_instr(Padd rd r1 r2) = 
       OK_nextinstr (reg_update rd $+ (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Paddi rd r1 cst) =
       OK_nextinstr (reg_update rd $+ (gpr_or_zero r1) (const_low cst))) /\

  (ppc_exec_instr(Paddis rd r1 cst ) = 
       OK_nextinstr (reg_update rd $+ (gpr_or_zero r1) (const_high cst))) /\

  (ppc_exec_instr(Paddze rd r1) = 
       OK_nextinstr (reg_update rd $+ (read_reg r1) (read_bit_word PPC_CARRY))) /\

  (ppc_exec_instr(Pand_ rd r1 r2) = 
       OK_nextinstr (sint_reg_update rd $&& (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pandc rd r1 r2) =
       OK_nextinstr (reg_update rd (\x y. x && ~y) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pandi_ rd r1 cst) =
       OK_nextinstr (sint_reg_update rd $&& (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pandis_ rd r1 cst) =
       OK_nextinstr (sint_reg_update rd $&& (read_reg r1) (const_high cst))) /\

  (ppc_exec_instr(Pb lbl) =
       LOCAL (goto_label lbl)) /\

  (ppc_exec_instr(Pbctr) =
       LOCAL (read_ctr >> set_pc)) /\

  (ppc_exec_instr(Pbctrl) =
       LOCAL (read_ctr >> pc_to_lr >> set_pc)) /\

  (ppc_exec_instr(Pbf bit lb1) =
       LOCAL (read_bit (PPC_CR0 bit) >> opt_cond I (goto_label lb1) pc_inc)) /\

  (ppc_exec_instr(Pbl ident) =
       LOCAL (pc_to_lr >> goto_label ident)) /\

  (ppc_exec_instr(Pbs ident) =
       LOCAL (goto_label ident)) /\

  (ppc_exec_instr(Pblr) =
       LOCAL (read_lr >> set_pc)) /\

  (ppc_exec_instr(Pbt bit lb1) =
       LOCAL (read_bit (PPC_CR0 bit) >> opt_cond I pc_inc (goto_label lb1))) /\

  (ppc_exec_instr(Pcmplw r1 r2) =
      OK_nextinstr (uint_compare (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pcmplwi r1 cst) =
      OK_nextinstr (uint_compare (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pcmpw r1 r2) =
      OK_nextinstr (sint_compare (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pcmpwi r1 cst) =
      OK_nextinstr (sint_compare (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pcror bd b1 b2) =
      OK_nextinstr (bit_update (PPC_CR0 bd) $\/ 
         (read_bit (PPC_CR0 b1)) (read_bit (PPC_CR0 b2)))) /\

  (ppc_exec_instr(Pdivw rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pdivwu rd r1 r2) = option_fail ) /\

  (ppc_exec_instr(Peqv rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. ~(x ?? y)) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pextsb rd r1) =
      OK_nextinstr (reg_update rd (\x y. sw2sw ((w2w x):word8)) 
          (read_reg r1) (read_reg r1))) /\

  (ppc_exec_instr(Pextsh rd r1) =
      OK_nextinstr (reg_update rd (\x y. sw2sw ((w2w x):word16)) 
        (read_reg r1) (read_reg r1))) /\

  (ppc_exec_instr(Pfabs rd r1) = option_fail) /\

  (ppc_exec_instr(Pfadd rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pfcmpu r1 r2) = option_fail) /\

  (ppc_exec_instr(Pfcti rd r1) = option_fail) /\

  (ppc_exec_instr(Pfdiv rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pfmadd rd r1 r2 r3) = option_fail) /\

  (ppc_exec_instr(Pfmr rd r1) = option_fail) /\

  (ppc_exec_instr(Pfmsub rd r1 r2 r3) = option_fail) /\

  (ppc_exec_instr(Pfmul rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pfneg rd r1) = option_fail) /\

  (ppc_exec_instr(Pfrsp rd r1) = option_fail) /\

  (ppc_exec_instr(Pfsub rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pictf rd r1) = option_fail) /\

  (ppc_exec_instr(Piuctf rd r1) = option_fail) /\

  (ppc_exec_instr(Plbz rd cst r1) =
      OK_nextinstr (reg_load 1 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Plbzx rd r1 r2) =
      OK_nextinstr (reg_load 1 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Plfd rd cst r1) = option_fail) /\

  (ppc_exec_instr(Plfdx rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Plfs rd cst r1) = option_fail) /\

  (ppc_exec_instr(Plfsx rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Plha rd cst r1) =
      OK_nextinstr (reg_load 2 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Plhax rd r1 r2) =
      OK_nextinstr (reg_load 2 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Plhz rd cst r1) =
      OK_nextinstr (reg_load 2 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Plhzx rd r1 r2) =
      OK_nextinstr (reg_load 2 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Plwz rd cst r1) =
      OK_nextinstr (reg_load 4 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Plwzx rd r1 r2) =
      OK_nextinstr (reg_load 4 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pmfcrbit v162 v163) = option_fail) /\

  (ppc_exec_instr(Pmflr rd) =
      OK_nextinstr (read_lr >> reg_write (PPC_IR rd))) /\

  (ppc_exec_instr(Pmr rd r1) =
      OK_nextinstr (read_reg r1 >> reg_write (PPC_IR rd))) /\

  (ppc_exec_instr(Pmtctr r1) =
      OK_nextinstr (read_reg r1 >> reg_write PPC_CTR)) /\

  (ppc_exec_instr(Pmtlr r1) =
      OK_nextinstr (read_reg r1 >> reg_write PPC_LR)) /\

  (ppc_exec_instr(Pmulli rd r1 cst) =
      OK_nextinstr (reg_update rd $* (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pmullw rd r1 r2) =
      OK_nextinstr (reg_update rd $* (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pnand rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. ~(x && y)) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pnor rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. ~(x !! y)) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Por rd r1 r2) =
      OK_nextinstr (reg_update rd $!! (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Porc rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. x !! ~y) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pori rd r1 cst) =
      OK_nextinstr (reg_update rd $!! (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Poris rd r1 cst) =
      OK_nextinstr (reg_update rd $!! (read_reg r1) (const_high cst))) /\

  (ppc_exec_instr(Prlwinm rd r1 sh mb me) = option_fail) /\

  (ppc_exec_instr(Pslw rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. x << w2n ((w2w y):word6)) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Psraw rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. x >>> w2n ((w2w y):word6)) (read_reg r1) (read_reg r2) >> no_carry)) /\

  (ppc_exec_instr(Psrawi rd r1 sh) =
      OK_nextinstr (reg_update rd (\x:word32 y:word32. x >>> w2n ((w2w y):word6)) (read_reg r1) (opt_push (K (w2w sh))) >> no_carry)) /\

  (ppc_exec_instr(Psrw rd r1 r2) =
      OK_nextinstr (reg_update rd (\x y. x >> w2n ((w2w y):word6)) (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pstb rd cst r1) =
      OK_nextinstr (reg_store 1 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pstbx rd r1 r2) =
      OK_nextinstr (reg_store 1 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pstfd rd cst r1) = option_fail) /\

  (ppc_exec_instr(Pstfdx rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Pstfs rd cst r1) = option_fail) /\

  (ppc_exec_instr(Pstfsx rd r1 r2) = option_fail) /\

  (ppc_exec_instr(Psth rd cst r1) =
      OK_nextinstr (reg_store 2 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Psthx rd r1 r2) =
      OK_nextinstr (reg_store 2 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pstw rd cst r1) =
      OK_nextinstr (reg_store 4 rd (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pstwx rd r1 r2) =
      OK_nextinstr (reg_store 4 rd (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Psubfc rd r1 r2) =
      OK_nextinstr (reg_update rd $- (read_reg r2) (read_reg r1) >> no_carry)) /\

  (ppc_exec_instr(Psubfic rd r1 cst) =
      OK_nextinstr (reg_update rd $- (const_low cst) (read_reg r1) >> no_carry)) /\

  (ppc_exec_instr(Pxor rd r1 r2) = 
      OK_nextinstr (reg_update rd $?? (read_reg r1) (read_reg r2))) /\

  (ppc_exec_instr(Pxori rd r1 cst) =
      OK_nextinstr (reg_update rd $?? (read_reg r1) (const_low cst))) /\

  (ppc_exec_instr(Pxoris rd r1 cst ) = 
      OK_nextinstr (reg_update rd $?? (read_reg r1) (const_high cst)))  `;


(* =============================================================== *)
(*  PowerPC INSTRUCTION DECODER                                    *)
(* =============================================================== *)

val ppc_match_step_def = Define `
  ppc_match_step name = 
    if name = "0" then DF else
    if name = "1" then DT else
    if MEM name ["A";"B";"C";"D";"S";"BI";"crbA";"crbB";"crbD";"SH";"MB";"ME"] then 
      assign_drop name 5 
    else if MEM name ["BD"] then 
      assign_drop name 14
    else if MEM name ["SIMM";"UIMM";"d"] then 
      assign_drop name 16
    else if MEM name ["LI"] then 
      assign_drop name 24
    else if MEM name ["AA";"Rc";"OE";"y";"z"] then 
      assign_drop name 1
    else 
      option_fail`;



val ppc_syntax = ``
  [("0 1 1 1 1 1 D A B 0 1 0 0 0 0 1 0 1 0 0",
     (\v. Padd (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 0 1 1 1 0 D A SIMM",
     (\v. Paddi (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 0 1 1 1 1 D A SIMM",
     (\v. Paddis (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 D A 0 0 0 0 0 0 0 1 1 0 0 1 0 1 0 0",
     (\v. Paddze (b2w v "D") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 0 1 1 1 0 0 1",
     (\v. Pand_ (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 1 1 1 1 0 0 0",
     (\v. Pandc (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 0 0 S A UIMM",
     (\v. Pandi_ (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 1 0 1 S A UIMM",
     (\v. Pandis_ (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 0 0 1 0 LI 0 0",
     (\v. Pb (b2w v "LI")));
   ("0 1 0 0 0 0  0 0 1 z y  BI BD 0 0",
     (\v. Pbf (b2w v "BI") (b2w v "BD")));
   ("0 1 0 0 0 0  0 1 1 z y  BI BD 0 0",
     (\v. Pbt (b2w v "BI") (b2w v "BD")));
   ("0 1 0 0 1 0 LI 0 1",
     (\v. Pbl (b2w v "LI")));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0",
     (\v. Pblr));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0",
     (\v. Pbctr));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1",
     (\v. Pbctrl));
   ("0 1 1 1 1 1 0 0 0 0 0 A B 0 0 0 0 1 0 0 0 0 0 0",
     (\v. Pcmplw (b2w v "A") (b2w v "B")));
   ("0 0 1 0 1 0 0 0 0 0 0 A UIMM",
     (\v. Pcmplwi (b2w v "A") (b2w v "UIMM")));
   ("0 1 1 1 1 1 0 0 0 0 0 A B 0 0 0 0 0 0 0 0 0 0 0",
     (\v. Pcmpw (b2w v "A") (b2w v "B")));
   ("0 0 1 0 1 1 0 0 0 0 0 A SIMM",
     (\v. Pcmpwi (b2w v "A") (b2w v "SIMM")));
   ("0 1 0 0 1 1 crbD crbA crbB 0 1 1 1 0 0 0 0 0 1 0",
     (\v. Pcror (b2w v "crbD") (b2w v "crbA") (b2w v "crbB")));
   ("0 1 1 1 1 1 D A B 0 1 1 1 1 0 1 0 1 1 0",
     (\v. Pdivw (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D A B 0 1 1 1 0 0 1 0 1 1 0",
     (\v. Pdivwu (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 0 0 0 1 1 1 0 0 0",
     (\v. Peqv (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A 0 0 0 0 0 1 1 1 0 1 1 1 0 1 0 0",
     (\v. Pextsb (b2w v "A") (b2w v "S")));
   ("0 1 1 1 1 1 S A 0 0 0 0 0 1 1 1 0 0 1 1 0 1 0 0",
     (\v. Pextsh (b2w v "A") (b2w v "S")));
   ("1 0 0 0 1 0 D A d",
     (\v. Plbz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 0 0 1 0 1 0 1 1 1 0",
     (\v. Plbzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 1 0 1 0 D A d",
     (\v. Plha (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 1 0 1 0 1 0 1 1 1 0",
     (\v. Plhax (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 1 0 0 0 D A d",
     (\v. Plhz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 1 0 0 0 1 0 1 1 1 0",
     (\v. Plhzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 0 0 0 0 D A d",
     (\v. Plwz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 0 0 0 0 1 0 1 1 1 0",
     (\v. Plwzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D 0 1 0 0 0 0 0 0 0 0 0 1 0 1 0 1 0 0 1 1 0",
     (\v. Pmflr (b2w v "D")));
   ("0 1 1 1 1 1 S A S! 0 1 1 0 1 1 1 1 0 0 0",
     (\v. Pmr (b2w v "A") (b2w v "S")));
   ("0 1 1 1 1 1 D 0 1 0 0 1 0 0 0 0 0 0 1 1 1 0 1 0 0 1 1 0",
     (\v. Pmtctr (b2w v "D")));
   ("0 1 1 1 1 1 D 0 1 0 0 0 0 0 0 0 0 0 1 1 1 0 1 0 0 1 1 0",
     (\v. Pmtlr (b2w v "D")));
   ("0 0 0 1 1 1 D A SIMM",
     (\v. Pmulli (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 D A B 0 0 1 1 1 0 1 0 1 1 0",
     (\v. Pmullw (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 1 0 1 1 1 0 0 0",
     (\v. Pnand (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 0 0 1 1 1 1 1 0 0 0",
     (\v. Pnor (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 1 1 1 1 0 0 0",
     (\v. Por (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 0 1 1 1 0 0 0",
     (\v. Porc (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 0 0 0 S A UIMM",
     (\v. Pori (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 0 0 1 S A UIMM",
     (\v. Poris (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 0 1 0 1 S A SH MB ME 0",
     (\v. Prlwinm (b2w v "A") (b2w v "S") (b2w v "SH") (b2w v "MB") (b2w v "ME")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 0 1 1 0 0 0 0",
     (\v. Pslw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 1 1 0 0 0 1 1 0 0 0 0",
     (\v. Psraw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A SH 1 1 0 0 1 1 1 0 0 0 0",
     (\v. Psrawi (b2w v "A") (b2w v "S") (b2w v "SH")));
   ("0 1 1 1 1 1 S A B 1 0 0 0 0 1 1 0 0 0 0",
     (\v. Psrw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("1 0 0 1 1 0 S A d",
     (\v. Pstb (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 1 1 0 1 0 1 1 1 0",
     (\v. Pstbx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("1 0 1 1 0 0 S A d",
     (\v. Psth (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 0 1 0 1 1 1 0",
     (\v. Psthx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("1 0 0 1 0 0 S A d",
     (\v. Pstw (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 1 0 0 1 0 1 1 1 0",
     (\v. Pstwx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D A B 0 0 0 0 0 0 1 0 0 0 0",
     (\v. Psubfc (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 0 1 0 0 0 D A SIMM",
     (\v. Psubfic (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 S A B 0 1 0 0 1 1 1 1 0 0 0",
     (\v. Pxor (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 0 1 0 S A UIMM",
     (\v. Pxori (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 0 1 1 S A UIMM",
     (\v. Pxoris (b2w v "A") (b2w v "S") (b2w v "UIMM")))]    ``;

val ppc_decode_def = Define `
  ppc_decode = match_list ppc_match_step (REVERSE o tokenise) (\k x. SOME (k (FST x))) ^ppc_syntax`;  

(* -- partially pre-evaluate ppc_decode -- *)

fun eval_term_ss tm_name tm = conv_ss 
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
val token_ss = eval_term_ss "tokenise" ``tokenise x``;
val if_ss = conv_ss { name = "if", trace = 3, 
  key = SOME ([],``if x then (y:'a) else z``), 
  conv = K (K ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) };

val ppc_decode_thm = let
  val n2bits_ss = eval_term_ss "n2bits" ``n2bits m n``;
  val th1 = REWRITE_CONV [MAP,ppc_decode_def,combinTheory.o_DEF,match_list_def] ``ppc_decode``
  val th2 = SIMP_RULE (std_ss++token_ss) [match_def,REV_DEF,REVERSE_REV] th1
  val th3 = SIMP_RULE (bool_ss++if_ss++n2bits_ss) [MAP,ppc_match_step_def] th2
  val th4 = REWRITE_RULE [option_then_assoc,drop_eq_thm,option_do_def] th3
  val th5 = REWRITE_RULE [option_try_def,GSYM option_orelse_assoc] th4
  val th6 = REWRITE_RULE [option_then_OVER_orelse] th5
  val th7 = REWRITE_RULE [option_orelse_assoc] th6
  in th7 end;

fun permanently_add_to_compset name thm = let
  val _ = save_thm(name,thm)
  val _ = computeLib.add_funs [thm]
  val _ = adjoin_to_theory {sig_ps = NONE, struct_ps = SOME (fn ppstrm => 
    let val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) in
            S ("val _ = computeLib.add_funs ["^name^"];")
    end)}
  in print ("Permanently added to compset: "^name^"\n") end;
  
val _ = permanently_add_to_compset "ppc_decode_thm" ppc_decode_thm;



(* =============================================================== *)
(*  PowerPC NEXT-STATE FUNCTION                                    *)
(* =============================================================== *)

val PPC_NEXT_def = Define `
  PPC_NEXT = 
    LOCAL (read_pc >> 
           read_mem 4 >>
           opt_monop (w2bits:word32 -> bool list) >>
           opt_try_monop ppc_decode >> 
           opt_try_s_pop ppc_exec_instr)`;


(* help to evaluate PPC_NEXT *)

val expand_mem_read_bytes =
 (ONCE_REWRITE_CONV [mem_read_bytes_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [mem_read_bytes_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [mem_read_bytes_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [mem_read_bytes_def,word2bytes_def] THENC
  ONCE_REWRITE_CONV [mem_read_bytes_def,word2bytes_def] THENC 
  SIMP_CONV std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,ASR_ADD])

val mem_read_bytes_thm = save_thm("mem_read_bytes_thm",
   CONJ (expand_mem_read_bytes ``mem_read_bytes 1 a s``)
  (CONJ (expand_mem_read_bytes ``mem_read_bytes 2 a s``)
        (expand_mem_read_bytes ``mem_read_bytes 4 a s``)));

val word2bytes_thm = save_thm("word2bytes_thm",
   CONJ (expand_mem_read_bytes ``word2bytes 1 w``)
  (CONJ (expand_mem_read_bytes ``word2bytes 2 w``)
        (expand_mem_read_bytes ``word2bytes 4 w``)));
 
val ss = rewrites [OK_nextinstr_def,LOCAL_def,reg_store_def,push_eaddress_def,
  read_reg_def,const_low_def,const_high_def,opt_thm,option_then_assoc,
  PREAD_R_def,PREAD_S_def,PREAD_M_def,write_mem_def,mem_access_ok_def,word2bytes_def,
  SIMP_RULE std_ss [LET_DEF] PWRITE_MDATA_def,mem_read_bytes_thm,read_mem_def,
  listTheory.REVERSE_REV,listTheory.REV_DEF,PWRITE_M_LIST_def,PWRITE_M_def,pc_inc_def,
  read_pc_def,read_lr_def,read_ctr_def,set_pc_def,set_lr_def,set_ctr_def,opt_s_pop_def,
  PWRITE_R_def,address_aligned_def,EVERY_DEF,option_parallel_def,
  reg_update_def,APPLY_UPDATE_THM,ppc_reg_distinct,LET_DEF,no_carry_def,PWRITE_S_def,
  PREAD_MDATA_def,MAP,listTheory.REV_DEF]

val PPC_NEXT_THM = save_thm("PPC_NEXT_THM",let
  val th = SIMP_CONV (std_ss) [PPC_NEXT_def] ``PPC_NEXT (r,s,m)``
  val th = DISCH ``
    (r PPC_PC && 3w = 0w:word32) /\ 
    (m (r PPC_PC)    = SOME (((31 >< 24) (w:word32)):word8)) /\
    (m (r PPC_PC+1w) = SOME ((23 >< 16) w)) /\
    (m (r PPC_PC+2w) = SOME ((15 ><  8) w)) /\
    (m (r PPC_PC+3w) = SOME (( 7 ><  0) w))`` th
  val th = SIMP_RULE (std_ss++ss) [bytes2word_thm] th
  val th = SIMP_RULE std_ss [option_then_def] th
  val th = DISCH ``ppc_exec_instr i ((r,s,m):ppc_state) = SOME x`` th  
  val th = DISCH ``ppc_decode (w2bits (w:word32)) = SOME i`` th
  val th = SIMP_RULE std_ss [opt_try_monop_def,opt_try_s_pop_def,LET_DEF] th
  val th = SIMP_RULE std_ss [GSYM AND_IMP_INTRO] th
  in th end);


(* ppc examples/tests:

val th = EVAL ``ppc_decode(hex2bits "7C221A14")``;  (* add 1,2,3 *)
val th = EVAL ``ppc_decode(hex2bits "7C640194")``;  (* addze 3,4 *)
val th = EVAL ``ppc_decode(hex2bits "7E6802A6")``;  (* mflr 19 *)
val th = EVAL ``ppc_decode(hex2bits "7C4903A6")``;  (* mtctr 2 *)
val th = EVAL ``ppc_decode(hex2bits "7C4803A6")``;  (* mtlr 2 *)
val th = EVAL ``ppc_decode(hex2bits "7C032040")``;  (* cmplw 3,4 *)
val th = EVAL ``ppc_decode(hex2bits "28070320")``;  (* cmplwi 7,800 *)
val th = EVAL ``ppc_decode(hex2bits "7C119000")``;  (* cmpw 17,18 *)
val th = EVAL ``ppc_decode(hex2bits "2C070258")``;  (* cmpwi 7,600 *)
val th = EVAL ``ppc_decode(hex2bits "7E7A21D6")``;  (* mullw 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7E7A2010")``;  (* subfc 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C221BD6")``;  (* divw 1,2,3 *)
val th = EVAL ``ppc_decode(hex2bits "7C858396")``;  (* divwu 4,5,16 *)
val th = EVAL ``ppc_decode(hex2bits "38221388")``;  (* addi 1,2,5000 *)
val th = EVAL ``ppc_decode(hex2bits "3C22FFCE")``;  (* addis 1,2,-50 *)
val th = EVAL ``ppc_decode(hex2bits "7C812839")``;  (* and. 1,4,5 *)
val th = EVAL ``ppc_decode(hex2bits "7C812878")``;  (* andc 1,4,5 *)
val th = EVAL ``ppc_decode(hex2bits "70E60050")``;  (* andi. 6,7,80 *)
val th = EVAL ``ppc_decode(hex2bits "76300007")``;  (* andis. 16,17,7 *)
val th = EVAL ``ppc_decode(hex2bits "4C221B82")``;  (* cror 1,2,3 *)
val th = EVAL ``ppc_decode(hex2bits "7C411A38")``;  (* eqv 1,2,3 *)
val th = EVAL ``ppc_decode(hex2bits "7E300774")``;  (* extsb 16,17 *)
val th = EVAL ``ppc_decode(hex2bits "7CA40734")``;  (* extsh 4,5 *)
val th = EVAL ``ppc_decode(hex2bits "8A7A00EA")``;  (* lbz 19, 234(26) *)
val th = EVAL ``ppc_decode(hex2bits "7E7A20AE")``;  (* lbzx 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7E7A22AE")``;  (* lhax 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7E7A222E")``;  (* lhzx 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "827A00EA")``;  (* lwz 19, 234(26) *)
val th = EVAL ``ppc_decode(hex2bits "7E7A202E")``;  (* lwzx 19, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A1378")``;  (* mr 26, 2 *)
val th = EVAL ``ppc_decode(hex2bits "1E7AFFFE")``;  (* mulli 19, 26, -2 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A23B8")``;  (* nand 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A20F8")``;  (* nor 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2378")``;  (* or 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2338")``;  (* orc 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "605A0237")``;  (* ori 26, 2, 567 *)
val th = EVAL ``ppc_decode(hex2bits "645A0237")``;  (* oris 26, 2, 567 *)
val th = EVAL ``ppc_decode(hex2bits "545A188A")``;  (* rlwinm 26, 2, 3, 2, 5 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2030")``;  (* slw 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2630")``;  (* sraw 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A1E70")``;  (* srawi 26, 2, 3 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2430")``;  (* srw 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "985A00EA")``;  (* stb 2, 234(26) *)
val th = EVAL ``ppc_decode(hex2bits "7C44D1AE")``;  (* stbx 2, 4, 26 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A232E")``;  (* sthx 2, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "905A00EA")``;  (* stw 2, 234(26) *)
val th = EVAL ``ppc_decode(hex2bits "7C5A212E")``;  (* stwx 2, 26, 4 *)
val th = EVAL ``ppc_decode(hex2bits "227AFFFE")``;  (* subfic 19, 26, -2 *)
val th = EVAL ``ppc_decode(hex2bits "7C5A2278")``;  (* xor 26, 2, 4 *)
val th = EVAL ``ppc_decode(hex2bits "685A0237")``;  (* xori 26, 2, 567 *)
val th = EVAL ``ppc_decode(hex2bits "6C5A0237")``;  (* xoris 26, 2, 567 *)
val th = EVAL ``ppc_decode(hex2bits "4BFFFFFC")``;  (* b L1 *)
val th = EVAL ``ppc_decode(hex2bits "4180FFF8")``;  (* bc 12,0,L1 *)
val th = EVAL ``ppc_decode(hex2bits "4181FFF4")``;  (* bc 12,1,L1 *)
val th = EVAL ``ppc_decode(hex2bits "4082FFF0")``;  (* bc 4,2,L1 *)
val th = EVAL ``ppc_decode(hex2bits "4083FFEC")``;  (* bc 4,3,L1 *)

*)

val _ = export_theory ();
