open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open decoderTheory bit_listTheory opmonTheory;

val _ = new_theory "ia32";


(* =============================================================== *)
(*  x86 ABSTRACT SYNTAX TREE                                       *)
(* =============================================================== *)

val _ = type_abbrev("Ximm",``:word32``);
val _ = Hol_datatype `Xreg = EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI`;

val _ = Hol_datatype `
  Xrm = Xr of Xreg                                         (* register *) 
      | Xm of (word2 # Xreg) option => Xreg option => Ximm (* mem[2^{scale} * index + base + displacement] *)`;

val _ = Hol_datatype `
  Xdest_src = Xrm_i of Xrm  => Ximm  (* mnemonic r/m32, imm32 or mnemonic r/m32, imm8 (sign-extended) *)
            | Xrm_r of Xrm  => Xreg  (* mnemonic r/m32, r32 *)
            | Xr_rm of Xreg => Xrm   (* mnemonic r32, r/m32 *)  `;

val _ = Hol_datatype `
  Ximm_rm = Xi_rm of Xrm    (* r/m32 *) 
          | Xi    of Ximm   (* imm32 or imm8 (sign-extended) *) `;

val _ = Hol_datatype `Xbinop_name = Xadd | Xand | Xcmp | Xor | Xsub | Xtest | Xxor `;
val _ = Hol_datatype `Xmonop_name = Xdec | Xinc | Xnot | Xneg `;
val _ = Hol_datatype `Xxmem_name  = Xcmpxchg | Xxadd | Xxchg `;

val _ = Hol_datatype `Xcond = X_ALWAYS | X_E | X_NE`;

val _ = Hol_datatype `
  Xinstruction = Xbinop     of Xbinop_name => Xdest_src
               | Xmonop     of Xmonop_name => Xrm
               | Xmul       of Xrm
               | Xdiv       of Xrm
               | Xxmem      of Xxmem_name => Xdest_src
               | Xpop       of Xrm
               | Xpush      of Xrm
               | Xcall      of Ximm_rm
               | Xret       of Ximm
               | Xmov       of Xcond => Xdest_src
               | Xjump      of Xcond => Ximm
               | Xloop      of Xcond => Ximm      (* Here Xcond over approximates possibilities *)
               | Xpushad      
               | Xpopad       
               | Xmfence      
               | Xsfence      
               | Xlfence    `;

val _ = Hol_datatype `Xpre_g1 = Xlock | Xg1_none `;
val _ = Hol_datatype `Xpre_g2 = Xbranch_taken | Xbranch_not_taken | Xg2_none `;

val _ = Hol_datatype `Xinst = Xprefix of Xpre_g1 => Xpre_g2 => Xinstruction`;


(* =============================================================== *)
(*  x86 OPERATIONAL SEMANTICS                                      *)
(* =============================================================== *)

val _ = Hol_datatype `
  Xeflags = X_CF | X_PF | X_AF | X_ZF | X_SF | X_OF `;

val _ = type_abbrev("x86_state",   (*  state = tuple consisting of:   *) 
  ``: (Xreg -> word32) #           (*  - general-purpose registers    *)
      (Xeflags -> bool option) #   (*  - eflags                       *)
      word32 #                     (*  - eip                          *) 
      (word32 -> word8 option)     (*  - unsegmented memory           *) ``); 

(* functions for modifying state *)

val XREAD_REG_def   = Define `XREAD_REG   i ((r,f,e,m):x86_state) = r i `;
val XREAD_EFLAG_def = Define `XREAD_EFLAG i ((r,f,e,m):x86_state) = f i `;
val XREAD_EIP_def   = Define `XREAD_EIP     ((r,f,e,m):x86_state) = e   `;
val XREAD_MEM_def   = Define `XREAD_MEM   i ((r,f,e,m):x86_state) = m i `;

val XWRITE_REG_def   = Define `XWRITE_REG   i x ((r,f,e,m):x86_state) = ((i =+ x) r,f,e,m):x86_state `;
val XWRITE_EFLAG_def = Define `XWRITE_EFLAG i x ((r,f,e,m):x86_state) = (r,(i =+ x) f,e,m):x86_state `;
val XWRITE_EIP_def   = Define `XWRITE_EIP     x ((r,f,e,m):x86_state) = (r,f,x,m)         :x86_state `;
val XWRITE_MEM_def   = Define `XWRITE_MEM   i x ((r,f,e,m):x86_state) = (r,f,e,(i =+ x) m):x86_state `;

val read_reg_def   = Define `read_reg r   = opt_push (XREAD_REG r)`;
val read_eip_def   = Define `read_eip     = opt_push (XREAD_EIP)`;
val read_eflag_def = Define `read_eflag f = opt_push (XREAD_EFLAG f)`;

val write_reg_def   = Define `write_reg r   = opt_s_pop (XWRITE_REG r)`;
val write_eip_def   = Define `write_eip     = opt_s_pop (XWRITE_EIP)`;
val write_eflag_def = Define `write_eflag f = opt_s_pop (XWRITE_EFLAG f)`;

(* setting/unsetting eflags *)

val byte_parity_def = Define `
  byte_parity = EVEN o LENGTH o FILTER I o n2bits 8 o w2n`;

val write_CF_flag_def = Define `write_CF_flag c = opt_push_const c >> write_eflag (X_CF)`;
val unset_flag_def = Define `unset_flag f = opt_push_const NONE >> write_eflag f`;
val set_flag_def = Define `set_flag f x = opt_push_const (SOME x) >> write_eflag f`;

val calc_PF_def = Define `calc_PF w = set_flag X_PF (byte_parity w)`;
val calc_ZF_def = Define `calc_ZF w = set_flag X_ZF (w = 0w)`;
val calc_SF_def = Define `calc_SF w = set_flag X_SF (word_msb w)`;

val calc_logical_op_eflags_def = Define `
  calc_logical_op_eflags = 
    opt_do_pop (\w. calc_PF w >>| calc_ZF w >>| calc_SF w >>| 
                    set_flag X_OF F >>| set_flag X_CF F >>| unset_flag X_AF)`;

val calc_arith_op_eflags_except_CF_def = Define `
  calc_arith_op_eflags_except_CF = 
    opt_do_pop (\w. calc_PF w >>| calc_ZF w >>| calc_SF w >>| 
                    unset_flag X_AF >>| unset_flag X_OF)`;

val calc_arith_op_eflags_def = Define `
  calc_arith_op_eflags = 
    opt_do_pop (\(w,c). calc_PF w >>| calc_ZF w >>| calc_SF w >>| set_flag X_CF c >>|
                        unset_flag X_AF >>| unset_flag X_OF)`;

(* memory accesses *)

val XREAD_MEM_BYTES_def = Define `
  XREAD_MEM_BYTES n a s = 
    if n = 0 then [] else XREAD_MEM a s :: XREAD_MEM_BYTES (n-1) (a+1w) s`;

val XWRITE_MEM_BYTES_def = Define `
  (XWRITE_MEM_BYTES a [] s = s) /\
  (XWRITE_MEM_BYTES a (b::bs) s = XWRITE_MEM a (SOME b) (XWRITE_MEM_BYTES (a+1w) bs s))`;

val XREAD_MDATA_def = Define `
  XREAD_MDATA number_of_bytes a s =
    (bytes2word o MAP THE o XREAD_MEM_BYTES number_of_bytes a) s`;

val XWRITE_MDATA_def = Define `
  XWRITE_MDATA number_of_bytes a w s =
    XWRITE_MEM_BYTES a (word2bytes number_of_bytes w) s`

val mem_access_ok_def = Define `
  mem_access_ok number_of_bytes = opt_assert 
    (\((a,x),s). EVERY (\x. ~(x = NONE)) (XREAD_MEM_BYTES number_of_bytes a s))`;

val read_mem_def = Define ` (* pops address to be read, pushes result *)
  read_mem size = mem_access_ok size >> opt_s_push (XREAD_MDATA size)`;

val write_mem_def = Define ` (* pops address, pops word to be stored *)
  write_mem size = 
    mem_access_ok size >> opt_swap >> opt_s_pop2 (XWRITE_MDATA size)`;

(*
   most instructions execute:
    - calc effective addresses of operands
    - load effective operands
    - perform operation
    - store to destination operand 
*)

val _ = Hol_datatype `
  Xeffective_address = 
      Xea_i of Ximm     (* constant       *)
    | Xea_r of Xreg     (* register name  *)
    | Xea_m of word32   (* memory address *) `;

(* ea_* functions calculates the effective address *)

val ea_Xr_def = Define `ea_Xr (r:Xreg) = opt_push_const (Xea_r r)`;
val ea_Xi_def = Define `ea_Xi (i:Ximm) = opt_push_const (Xea_i i)`;

val ea_Xrm_base_def = Define `
  (ea_Xrm_base NONE = opt_push_const 0w) /\
  (ea_Xrm_base (SOME r) = read_reg r)`;

val ea_Xrm_index_def = Define `
  (ea_Xrm_index NONE = opt_push_const 0w >>| opt_push_const 0w) /\
  (ea_Xrm_index (SOME (s,i)) = opt_push_const s >>| read_reg i)`;

val ea_Xrm_def = Define `
  (ea_Xrm (Xr r) = ea_Xr r) /\
  (ea_Xrm (Xm i b d) = 
     (ea_Xrm_index i >>| ea_Xrm_base b >>| opt_push_const d) >> 
     opt_quadop (\s i b d. Xea_m (n2w (2 ** w2n s) * i + b + d)))`;

val ea_Xdest_def = Define `
  (ea_Xdest (Xrm_i rm i) = ea_Xrm rm) /\
  (ea_Xdest (Xrm_r rm r) = ea_Xrm rm) /\
  (ea_Xdest (Xr_rm r rm) = ea_Xr r)`;

val ea_Xsrc_def = Define `
  (ea_Xsrc (Xrm_i rm i) = ea_Xi i) /\
  (ea_Xsrc (Xrm_r rm r) = ea_Xr r) /\
  (ea_Xsrc (Xr_rm r rm) = ea_Xrm rm)`;

val ea_Ximm_rm_def = Define `
  (ea_Ximm_rm (Xi_rm rm) = ea_Xrm rm) /\
  (ea_Ximm_rm (Xi i)     = ea_Xi i)`;

(* `load_ea` loads the value of an effective address, 
    i.e. pops something of type `Xeffective_address` and pushes the resulting word32 *)

val load_ea_aux_def = Define `
  (load_ea_aux (Xea_i i) = opt_push_const i) /\
  (load_ea_aux (Xea_r r) = read_reg r) /\
  (load_ea_aux (Xea_m i) = opt_push_const i >> read_mem 4)`; 

val load_ea_def = Define `load_ea = opt_do_pop load_ea_aux`;

(* `store_ea` stores a word to the effective address, 
    i.e. pops a word `w` and then pops effective_address `ea` and stores `w` at `ea` *)

val store_ea_aux_def = Define `
  (store_ea_aux (Xea_i i) = option_fail) /\  (* one cannot store into a constant *)
  (store_ea_aux (Xea_r r) = write_reg r) /\
  (store_ea_aux (Xea_m i) = opt_push_const i >> write_mem 4)`; 

val store_ea_def = Define `store_ea = opt_swap >> opt_do_pop store_ea_aux`;

(* eip modifiers *)

val next_eip_def = Define `
  next_eip i = read_eip >> opt_monop (\x. x + i) >> write_eip`;

val bump_eip_def = Define `
  bump_eip i f = LOCAL (f >>| next_eip i)`;

(* binops *)

val add_with_carry_out_def = Define `
  add_with_carry_out (x:'a word) y = (x + y, dimword(:'a) <= w2n x + w2n y)`;

val sub_with_borrow_out_def = Define `
  sub_with_borrow_out (x:'a word) y = (x - y, x <+ y)`;

val store_arith_op_result_def = Define `
  store_arith_op_result =
    opt_dup >> (calc_arith_op_eflags >>| (opt_monop FST >> store_ea))`;

val do_binop_def = Define `
  (do_binop Xadd  = opt_binop add_with_carry_out >> store_arith_op_result) /\ 
  (do_binop Xsub  = opt_binop sub_with_borrow_out >> store_arith_op_result) /\ 
  (do_binop Xcmp  = opt_binop sub_with_borrow_out >> calc_arith_op_eflags >> opt_pop) /\ 
  (do_binop Xtest = opt_binop $word_and >> calc_logical_op_eflags >> unset_flag X_PF >> opt_pop) /\ 
  (do_binop Xand  = opt_binop $word_and >> opt_dup >> (calc_logical_op_eflags >>| store_ea)) /\ 
  (do_binop Xxor  = opt_binop $word_xor >> opt_dup >> (calc_logical_op_eflags >>| store_ea)) /\ 
  (do_binop Xor   = opt_binop $word_or  >> opt_dup >> (calc_logical_op_eflags >>| store_ea))`;

(* monops *)

val do_monop_def = Define `
  (do_monop Xnot = opt_monop (\x. ~x) >> store_ea) /\
  (do_monop Xdec = opt_monop (\x. x - 1w) >> opt_dup >> (calc_arith_op_eflags_except_CF >>| store_ea)) /\
  (do_monop Xinc = opt_monop (\x. x + 1w) >> opt_dup >> (calc_arith_op_eflags_except_CF >>| store_ea)) /\
  (do_monop Xneg = opt_monop (\x. 0w - x) >> opt_dup >> 
     (calc_arith_op_eflags_except_CF >>| write_CF_flag NONE >>| store_ea))`;

(* evaluating conditions of eflags *)

val eval_cond_def = Define `
  (eval_cond X_ALWAYS = opt_push_const T) /\
  (eval_cond X_E  = read_eflag X_ZF >> opt_monop_the >> opt_monop (\zf.  zf)) /\
  (eval_cond X_NE = read_eflag X_ZF >> opt_monop_the >> opt_monop (\zf. ~zf))`;

(* execution of one instruction *)

val x86_exec_def = Define `
  (x86_exec (Xbinop binop_name ds) i = bump_eip i 
     ((ea_Xdest ds >> opt_dup >> load_ea) >>|      (* push ea_dest, push dest value *)
      (ea_Xsrc ds >> load_ea) >>                   (* push src value *)
       do_binop binop_name)) /\                    (* perform binop operation *)
  (x86_exec (Xmonop monop_name rm) i = bump_eip i 
     (ea_Xrm rm >> opt_dup >> load_ea >>           (* push ea_dest, push dest value *)
      do_monop monop_name)) /\                     (* perform monop operation *)
  (x86_exec (Xmul rm) i = option_fail) /\              
  (x86_exec (Xdiv rm) i = option_fail) /\              
  (x86_exec (Xxmem xmem_name ds) i = option_fail) /\              
  (x86_exec (Xpop rm) i = option_fail) /\              
  (x86_exec (Xpush rm) i = option_fail) /\              
  (x86_exec (Xcall imm_rm) i = option_fail) /\              
  (x86_exec (Xret imm) i = option_fail) /\              
  (x86_exec (Xmov c ds) i = bump_eip i
     (((ea_Xsrc ds >> load_ea) >>|                (* push value of src, regardless of condition! *)
       eval_cond c) >>                            (* push result of condition check *)
      opt_cond I                                  (* pop and branch on condition *)
       (ea_Xdest ds >> opt_swap >> store_ea)      (* cond sat, store value in dest *)
       (opt_pop))) /\                             (* cond not sat, pop src value *)              
  (x86_exec (Xjump c imm) i = LOCAL 
     ((read_eip >>| eval_cond c) >>               (* push eip, push result of condition check *)
      opt_cond I                                  (* pop and branch on condition *)
       (opt_monop (\x. x + i +imm) >> write_eip)  (* cond sat, add imm to eip *)
       (opt_monop (\x. x + i) >> write_eip))) /\  (* cond not sat, add instruction length to eip *)
  (x86_exec (Xloop c imm) i = LOCAL
     ((read_eip >>| eval_cond c >>|               (* push eip, push result of condition check *)
       (read_reg ECX >> opt_monop (\x. x - 1w) >> (* push ecx, decrement *)
        opt_dup >> write_reg ECX >>               (* store new ecx *)
        opt_monop (\x. ~(x = 0w)))) >>            (* push result of ~(ecx = 0) *)
      opt_binop $/\ >>                            (* pop, pop, push ~(ecx = 0) && c *)
      opt_cond I                                  (* pop and branch on condition *)
       (opt_monop (\x. x + i + imm) >> write_eip) (* cond sat, add imm to eip *)
       (opt_monop (\x. x + i) >> write_eip))) /\  (* cond not sat, add instruction length to eip *)
  (x86_exec (Xpushad) i = option_fail) /\              
  (x86_exec (Xpopad)  i = option_fail) /\              
  (x86_exec (Xmfence) i = option_fail) /\              
  (x86_exec (Xsfence) i = option_fail) /\              
  (x86_exec (Xlfence) i = option_fail)`;

val x86_execute_def = Define `x86_execute (Xprefix g1 g2 i) len = x86_exec i len`;


(* =============================================================== *)
(*  x86 INSTRUCTION DECODER                                        *)
(* =============================================================== *)

(* reading hex strings to bit lists *)

val STR_SPACE_AUX_def = Define `
  (STR_SPACE_AUX n "" = "") /\
  (STR_SPACE_AUX n (STRING c s) = 
     if n = 0 then STRING #" " (STRING c (STR_SPACE_AUX 1 s)) 
              else STRING c (STR_SPACE_AUX (n-1) s))`;

val bytebits_def = Define `
  bytebits = hex2bits o STR_SPACE_AUX 2`;

(* interprete the IA-32 manuals' syntax *)

val check_opcode_def = Define `
  check_opcode s = 
    let y = (n2bits 3 o char2num o HD o TL o EXPLODE) s in
      assert (\g. g "Reg/Opcode" = y)`;

val read_SIB_def = Define `
  read_SIB =
    assign_drop "Base" 3 >> assign_drop "Index" 3 >> assign_drop "Scale" 2 >>
    option_try [
      assert (\g. (g "Mod" = [F;F]) /\  (g "Base" = [T;F;T])) >> assign_drop "disp32" 32; 
      assert (\g. (g "Mod" = [F;F]) /\ ~(g "Base" = [T;F;T]));
      assert (\g. (g "Mod" = [T;F])) >> assign_drop "disp8" 8;
      assert (\g. (g "Mod" = [F;T])) >> assign_drop "disp32" 32]`;

val read_ModRM_def = Define `
  read_ModRM = 
    assign_drop "R/M" 3 >> assign_drop "Reg/Opcode" 3 >> assign_drop "Mod" 2 >>
    option_try [
      assert (\g.  (g "Mod" = [T;T]));
      assert (\g.  (g "Mod" = [F;F]) /\ ~(g "R/M" = [F;F;T]) /\ ~(g "R/M" = [T;F;T]));
      assert (\g.  (g "Mod" = [F;F]) /\  (g "R/M" = [T;F;T])) >> assign_drop "disp32" 32;
      assert (\g.  (g "Mod" = [T;F]) /\ ~(g "R/M" = [F;F;T])) >> assign_drop "disp8" 8;
      assert (\g.  (g "Mod" = [F;T]) /\ ~(g "R/M" = [F;F;T])) >> assign_drop "disp32" 32;
      assert (\g. ~(g "Mod" = [T;T]) /\  (g "R/M" = [F;F;T])) >> read_SIB]`;

val is_hex_add_def = Define `
  is_hex_add x = ((IMPLODE o DROP 2 o EXPLODE) x = "+rd")`;

val process_hex_add_def = Define `
  process_hex_add name = 
    let n = (hex2num o IMPLODE o TAKE 2 o EXPLODE) name in
      option_try [drop_eq (n2bits 8 (n+0)) >> assign "reg" (n2bits 3 0);
                  drop_eq (n2bits 8 (n+1)) >> assign "reg" (n2bits 3 1);
                  drop_eq (n2bits 8 (n+2)) >> assign "reg" (n2bits 3 2);
                  drop_eq (n2bits 8 (n+3)) >> assign "reg" (n2bits 3 3);
                  drop_eq (n2bits 8 (n+4)) >> assign "reg" (n2bits 3 4);
                  drop_eq (n2bits 8 (n+5)) >> assign "reg" (n2bits 3 5);
                  drop_eq (n2bits 8 (n+6)) >> assign "reg" (n2bits 3 6);
                  drop_eq (n2bits 8 (n+7)) >> assign "reg" (n2bits 3 7)]`;

val x86_match_step_def = Define `
  x86_match_step name = 
    if is_hex name /\ (STRLEN name = 2) then     (* opcode e.g. FE, 83 and 04 *)
      drop_eq (n2bits 8 (hex2num name))      
    else if is_hex_add name then                 (* opcode + rd, e.g. F8+rd *)
      process_hex_add name 
    else if MEM name ["ib";"cb";"rel8"] then     (* 8-bit immediate or address *) 
      assign_drop name 8  
    else if MEM name ["iw";"cw";"imm16"] then    (* 16-bit immediate or address *) 
      assign_drop name 16 
    else if MEM name ["id";"cd";"rel32"] then    (* 32-bit immediate or address *) 
      assign_drop name 32 
    else if name = "/r" then                     (* normal reg + reg/mem *) 
      read_ModRM
    else if MEM name ["/0";"/1";"/2";"/3";"/4";"/5";"/6";"/7"] then (* opcode extension in ModRM *)
      read_ModRM >> check_opcode name
    else 
      option_fail`;

(* syntax classes *)

val x86_binop_def = Define `x86_binop = 
  [("ADD",Xadd); ("AND",Xand); ("CMP",Xcmp); ("OR",Xor); ("SUB",Xsub); ("TEST",Xtest); ("XOR",Xxor)]`;

val x86_monop_def = Define `x86_monop = 
  [("DEC",Xdec); ("INC",Xinc); ("NOT",Xnot); ("NEG",Xneg)]`;

val x86_xmem_def = Define `x86_xmem = 
  [("CMPXCHG",Xcmpxchg); ("XADD",Xxadd); ("XCHG",Xxchg)]`;

(* x86 - decoder *)

val b2reg_def = Define `
  b2reg g name = (EL (bits2num (g name)) [EAX;ECX;EDX;EBX;ESP;EBP;ESI;EDI]):Xreg`;

val decode_Xr32_def = Define `  
  decode_Xr32 g name =
    if name = "EAX" then EAX else
      if g "reg" = [] then b2reg g "Reg/Opcode" else b2reg g "reg"`;

val decode_SIB_def = Define `
  decode_SIB g = 
    if (g "Base" = [T;F;T]) /\ (g "Index" = [F;F;T]) then Xm NONE NONE (b2w g "disp32") else
    if (g "Base" = [T;F;T]) /\ (g "Scale" = [F;F]) then 
      Xm (SOME (b2w g "Scale",b2reg g "Index")) NONE (b2w g "disp32") 
    else
      let disp = (if (g "Mod" = [T;F]) then sw2sw ((b2w g "disp8"):word8) else b2w g "disp32") in
      let disp = (if (g "Mod" = [F;F]) then 0w else disp) in
      let indx = (if g "Index" = [F;F;T] then NONE else SOME (b2w g "Scale", b2reg g "Index")) in 
        Xm indx (SOME (b2reg g "Base")) disp`;

val decode_Xrm32_def = Define `  (* sw2sw = sign-extension *)
  decode_Xrm32 g name =
    if name = "EAX" then Xr EAX else
      if  (g "Mod" = [F;F]) /\ (g "R/M" = [T;F;T]) then Xm NONE NONE (b2w g "disp32") else
      if ~(g "Mod" = [T;T]) /\ (g "R/M" = [F;F;T]) then decode_SIB g else
      if  (g "Mod" = [F;F]) then Xm NONE (SOME (b2reg g "R/M")) 0w else
      if  (g "Mod" = [T;F]) then Xm NONE (SOME (b2reg g "R/M")) ((sw2sw:word8->word32) (b2w g "disp8")) else
      if  (g "Mod" = [F;T]) then Xm NONE (SOME (b2reg g "R/M")) (b2w g "disp32") else
      if  (g "Mod" = [T;T]) then Xr (b2reg g "R/M") else Xr (b2reg g "reg") `;

val decode_Xconst_def = Define `
  decode_Xconst name g = 
   if name = "imm8"  then (sw2sw:word8 ->word32) (b2w g "ib") else
   if name = "rel8"  then (sw2sw:word8 ->word32) (b2w g "cb") else
   if name = "imm16" then (sw2sw:word16->word32) (b2w g "iw") else
   if name = "imm32" then b2w g "id" else
   if name = "rel32" then b2w g "cd" else 0w`;

val decode_Xdest_src_def = Define `
  decode_Xdest_src g dest src =
    if src = "r32"   then Xrm_r (decode_Xrm32 g dest) (decode_Xr32 g src)  else
    if src = "r/m32" then Xr_rm (decode_Xr32 g dest)  (decode_Xrm32 g src) else
                          Xrm_i (decode_Xrm32 g dest) (decode_Xconst src g)`;

val decode_Xconst_or_zero_def = Define `  
  decode_Xconst_or_zero ts g =
    if LENGTH ts < 2 then 0w else decode_Xconst (EL 1 ts) g`;

val decode_Xcall_def = Define `  
  decode_Xcall ts g =
    if EL 1 ts = "r/m32" then Xi_rm (decode_Xrm32 g "r/m32") else 
                              Xi (decode_Xconst (EL 1 ts) g)`;

val x86_select_op_def = Define `
  x86_select_op name list = SND (HD (FILTER (\x. FST x = name) list))`;

val x86_syntax_binop = ``
  Xbinop (x86_select_op (HD ts) x86_binop) (decode_Xdest_src g (EL 1 ts) (EL 2 ts))``;

val x86_syntax_monop = ``
  Xmonop (x86_select_op (HD ts) x86_monop) (decode_Xrm32 g (EL 1 ts))``;
 
val x86_syntax_xmem = ``
  Xxmem (x86_select_op (HD ts) x86_xmem) (decode_Xdest_src g (EL 1 ts) (EL 2 ts))``;

val X_SOME_def = Define `X_SOME f = SOME o (\(g,w). (f g,w))`;

val x86_syntax_def = Define `
  x86_syntax ts = 
    if LENGTH ts = 0 then option_fail else
    if MEM (HD ts) (MAP FST x86_binop) then X_SOME (\g. ^x86_syntax_binop) else
    if MEM (HD ts) (MAP FST x86_monop) then X_SOME (\g. ^x86_syntax_monop) else
    if MEM (HD ts) (MAP FST x86_xmem)  then X_SOME (\g. ^x86_syntax_xmem) else
    if HD ts = "MUL"  then X_SOME (\g. Xmul  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "DIV"  then X_SOME (\g. Xdiv  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "POP"  then X_SOME (\g. Xpop  (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "PUSH" then X_SOME (\g. Xpush (decode_Xrm32 g (EL 1 ts))) else
    if HD ts = "PUSHAD" then X_SOME (\g. Xpushad) else
    if HD ts = "POPAD"  then X_SOME (\g. Xpopad)  else
    if HD ts = "MFENCE" then X_SOME (\g. Xmfence) else
    if HD ts = "SFENCE" then X_SOME (\g. Xsfence) else
    if HD ts = "LFENCE" then X_SOME (\g. Xlfence) else
    if HD ts = "JMP"    then X_SOME (\g. Xjump X_ALWAYS (decode_Xconst_or_zero ts g)) else
    if HD ts = "JE"     then X_SOME (\g. Xjump X_E (decode_Xconst_or_zero ts g)) else
    if HD ts = "JNE"    then X_SOME (\g. Xjump X_NE (decode_Xconst_or_zero ts g)) else
    if HD ts = "LOOP"   then X_SOME (\g. Xloop X_ALWAYS (decode_Xconst_or_zero ts g)) else
    if HD ts = "LOOPE"  then X_SOME (\g. Xloop X_E (decode_Xconst_or_zero ts g)) else
    if HD ts = "LOOPNE" then X_SOME (\g. Xloop X_NE (decode_Xconst_or_zero ts g)) else
    if HD ts = "MOV"    then X_SOME (\g. Xmov X_ALWAYS (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVE"  then X_SOME (\g. Xmov X_E (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CMOVNE" then X_SOME (\g. Xmov X_NE (decode_Xdest_src g (EL 1 ts) (EL 2 ts))) else
    if HD ts = "CALL" then X_SOME (\g. Xcall (decode_Xcall ts g)) else
    if HD ts = "RET"  then X_SOME (\g. Xret (decode_Xconst_or_zero ts g)) else option_fail`;
  

(* a list of x86 instructions, ordered by the combination of addressing modes they support *)

val x86_syntax_list = `` [

    " 05 id     | ADD EAX, imm32    ";
    " 83 /0 ib  | ADD r/m32, imm8   ";
    " 81 /0 id  | ADD r/m32, imm32  ";
    " 01 /r     | ADD r/m32, r32    ";
    " 03 /r     | ADD r32, r/m32    ";
    " 25 id     | AND EAX, imm32    ";
    " 81 /4 id  | AND r/m32, imm32  ";
    " 83 /4 ib  | AND r/m32, imm8   ";
    " 21 /r     | AND r/m32, r32    ";
    " 23 /r     | AND r32, r/m32    "; 
    " 0F 44 /r  | CMOVE r32, r/m32  ";
    " 0F 45 /r  | CMOVNE r32, r/m32 ";
    " 3D id     | CMP EAX, imm32    ";
    " 81 /7 id  | CMP r/m32, imm32  ";
    " 83 /7 ib  | CMP r/m32, imm8   ";
    " 39 /r     | CMP r/m32, r32    ";
    " 3B /r     | CMP r32, r/m32    ";
    " 89 /r     | MOV r/m32,r32     ";
    " 8B /r     | MOV r32,r/m32     ";
    " B8+rd id  | MOV r32, imm32    ";
    " 0D id     | OR EAX, imm32     ";
    " 81 /1 id  | OR r/m32, imm32   ";
    " 83 /1 ib  | OR r/m32, imm8    ";
    " 09 /r     | OR r/m32, r32     ";
    " 0B /r     | OR r32, r/m32     ";
    " 2D id     | SUB EAX, imm32    ";
    " 83 /5 ib  | SUB r/m32, imm8   ";
    " 81 /5 id  | SUB r/m32, imm32  ";
    " 29 /r     | SUB r/m32, r32    ";
    " 2B /r     | SUB r32, r/m32    ";
    " A9 id     | TEST EAX, imm32   ";
    " F7 /0 id  | TEST r/m32, imm32 ";
    " 85 /r     | TEST r/m32, r32   ";
    " 35 id     | XOR EAX, imm32    ";
    " 81 /6 id  | XOR r/m32, imm32  ";
    " 31 /r     | XOR r/m32, r32    ";
    " 83 /6 ib  | XOR r/m32, imm8   ";
    " 33 /r     | XOR r32, r/m32    ";

    " 0F B1 /r  | CMPXCHG r/m32, r32";
    " 0F C1 /r  | XADD r/m32, r32   "; 
    " 90+rd     | XCHG EAX, r32     "; 
    " 87 /r     | XCHG r/m32, r32   "; 
    
    " FF /1     | DEC r/m32         ";
    " 48+rd     | DEC r32           ";
    " FF /0     | INC r/m32         ";
    " 40+rd     | INC r32           ";
    " F7 /3     | NEG r/m32         ";
    " F7 /2     | NOT r/m32         ";
    " F7 /4     | MUL r/m32         ";
    " F7 /6     | DIV r/m32         ";
    " 8F /0     | POP r/m32         ";
    " 58+rd     | POP r32           ";
    " FF /6     | PUSH r/m32        ";
    " 50+rd     | PUSH r32          ";

    " E8 cd     | CALL rel32        ";
    " FF /2     | CALL r/m32        ";

    " EB cb     | JMP rel8          ";
    " E9 cd     | JMP rel32         ";
    " 74 cb     | JE rel8           ";
    " 75 cb     | JNE rel8          ";
    " C3        | RET               "; (* short for "RET #0" *)
    " C2 iw     | RET imm16         ";
    " E2 cb     | LOOP rel8         ";
    " E1 cb     | LOOPE rel8        ";
    " E0 cb     | LOOPNE rel8       ";

    " 60        | PUSHAD            ";
    " 61        | POPAD             ";
    " 0F AE /5  | LFENCE            ";
    " 0F AE /6  | MFENCE            ";
    " 0F AE /7  | SFENCE            "

  ] ``;

val x86_decode_aux_def = Define `
  x86_decode_aux = (match_list x86_match_step tokenise (x86_syntax o tokenise) o 
                     MAP (\s. let x = STR_SPLIT [#"|"] s in (EL 0 x, EL 1 x))) ^x86_syntax_list`;  

val x86_decode_prefixes_def = Define `
  x86_decode_prefixes w = 
    if LENGTH w < 16 then (Xg1_none,Xg2_none,w) else 
      let bt1  = (TAKE 8 w = n2bits 8 (hex2num "2E")) in
      let bnt1 = (TAKE 8 w = n2bits 8 (hex2num "3E")) in
      let l1   = (TAKE 8 w = n2bits 8 (hex2num "F0")) in
      let bt2  = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "2E")) /\ l1 in
      let bnt2 = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "3E")) /\ l1 in
      let l2   = (TAKE 8 (DROP 8 w) = n2bits 8 (hex2num "F0")) /\ (bt1 \/ bnt1) in
      let g1   = if l1 \/ l2 then Xlock else Xg1_none in
      let g2   = if bt1 \/ bt2 then Xbranch_taken else Xg2_none in
      let g2   = if bnt1 \/ bnt2 then Xbranch_not_taken else g2 in
      let n    = if bt1 \/ bnt1 \/ l1 then (if bt2 \/ bnt2 \/ l2 then 16 else 8) else 0 in      
        (g1,g2,DROP n w)`;        

val x86_decode_def = Define `
  x86_decode w = 
    let (g1,g2,w) = x86_decode_prefixes w in 
      (x86_decode_aux >> (\(i,w). SOME (Xprefix g1 g2 i, w))) w`;

(* -- partially pre-evaluate x86_decode_aux -- *)
  
val x86_decode_aux_thm = let
  fun eval_term_ss tm_name tm = conv_ss 
    { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
  val token_ss = eval_term_ss "tokenise" ``tokenise x``;
  val if_ss = conv_ss { name = "if", trace = 3, 
    key = SOME ([],``if x then (y:'a) else z``), 
    conv = K (K ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) };
  val hex_ss = eval_term_ss "hex" ``n2bits 8 (hex2num y)``;
  val hex_add_ss = eval_term_ss "hex" ``n2bits 8 ((hex2num y) + k)``;
  val n2bits_3_ss = eval_term_ss "n2bits_3" ``n2bits 3 y``;
  val select_op_ss = eval_term_ss "select_op" ``x86_select_op x (y:('a#'b)list)``;
  val EL_LEMMA = prove(
    ``!x y z t. (EL 0 (x::t) = x) /\ (EL 1 (x::y::t) = y) /\ (EL 2 (x:'a::y::z::t) = z)``,
    REPEAT STRIP_TAC THEN EVAL_TAC);
  val SOME_LEMMA = prove(``!(f :'a -> 'b option) (g :'c) (h :'d). (SOME >> f = f)``,
    SIMP_TAC std_ss [FUN_EQ_THM,option_then_def,LET_DEF]);  
  val th1 = REWRITE_CONV [MAP,x86_decode_aux_def,combinTheory.o_DEF] ``x86_decode_aux``
  val th2 = CONV_RULE (ONCE_DEPTH_CONV (BETA_CONV) THENC (RAND_CONV (RAND_CONV EVAL))) th1
  val th3 = REWRITE_RULE [match_list_def,MAP] th2
  val th4 = SIMP_RULE (std_ss++token_ss) [match_def] th3
  val th5 = SIMP_RULE (bool_ss++if_ss) [MAP,x86_match_step_def] th4
  val th6 = SIMP_RULE (bool_ss++if_ss++select_op_ss) [x86_syntax_def,EL_LEMMA,HD] th5
  val th6a = SIMP_RULE (std_ss) [LET_DEF,process_hex_add_def] th6
  val th7 = SIMP_RULE (bool_ss++if_ss++hex_ss++hex_add_ss++n2bits_3_ss) [decode_Xdest_src_def,decode_Xconst_def] th6a
  val th8 = REWRITE_RULE [GSYM option_then_assoc,option_do_def,option_try_def,GSYM option_orelse_assoc] th7
  val th9 = SIMP_RULE std_ss [option_orelse_SOME,GSYM option_orelse_assoc,X_SOME_def] th8
  val thA = REWRITE_RULE [GSYM option_then_assoc,EL_LEMMA,drop_eq_thm,SOME_LEMMA,option_do_def] th9
  val thB = REWRITE_RULE [option_then_assoc,SOME_LEMMA] thA
  val thC = REWRITE_RULE [option_try_def,GSYM option_orelse_assoc] thB
  val thD = REWRITE_RULE [option_then_OVER_orelse] thC
  val thE = REWRITE_RULE [option_orelse_assoc] thD
  val thX = REWRITE_RULE [DT_over_DF,option_then_assoc,option_orelse_assoc,option_then_OVER_orelse] thE
  val thZ = REWRITE_RULE [DTF_THM] thX
  in thZ end;

fun permanently_add_to_compset name thm = let
  val _ = save_thm(name,thm)
  val _ = computeLib.add_funs [thm]
  val _ = adjoin_to_theory {sig_ps = NONE, struct_ps = SOME (fn ppstrm => 
    let val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) in
            S ("val _ = computeLib.add_funs ["^name^"];")
    end)}
  in print ("Permanently added to compset: "^name^"\n") end;
  
val _ = permanently_add_to_compset "x86_decode_aux_thm" x86_decode_aux_thm;


(* x86 examples/tests:

val th = EVAL ``x86_decode(bytebits "0538000000")``;      (* add eax,56 *)
val th = EVAL ``x86_decode(bytebits "810037020000")``;    (* add dword [eax],567 *)
val th = EVAL ``x86_decode(bytebits "010B")``;            (* add [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "0119")``;            (* add [ecx], ebx *)
val th = EVAL ``x86_decode(bytebits "2538000000")``;      (* and eax,56 *)
val th = EVAL ``x86_decode(bytebits "812037020000")``;    (* and dword [eax],567 *)
val th = EVAL ``x86_decode(bytebits "210B")``;            (* and [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "2319")``;            (* and ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "0F44C1")``;          (* cmove eax, ecx *)
val th = EVAL ``x86_decode(bytebits "0F454104")``;        (* cmovne eax, [ecx+4] *)
val th = EVAL ``x86_decode(bytebits "81FE38000000")``;    (* cmp esi,56 *)
val th = EVAL ``x86_decode(bytebits "813B37020000")``;    (* cmp dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "390B")``;            (* cmp [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "3B19")``;            (* cmp ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "893E")``;            (* mov [esi],edi *)
val th = EVAL ``x86_decode(bytebits "8B3E")``;            (* mov edi,[esi] *)
val th = EVAL ``x86_decode(bytebits "BC37020000")``;      (* mov esp,567 *)
val th = EVAL ``x86_decode(bytebits "81CE38000000")``;    (* or  esi,56 *)
val th = EVAL ``x86_decode(bytebits "810B37020000")``;    (* or  dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "090B")``;            (* or  [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "0B19")``;            (* or  ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "81EE38000000")``;    (* sub esi,56 *)
val th = EVAL ``x86_decode(bytebits "812B37020000")``;    (* sub dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "290B")``;            (* sub [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "2B19")``;            (* sub ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "F7C638000000")``;    (* test esi,56 *)
val th = EVAL ``x86_decode(bytebits "F70337020000")``;    (* test dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "850B")``;            (* test [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "81F638000000")``;    (* xor esi,56 *)
val th = EVAL ``x86_decode(bytebits "813337020000")``;    (* xor dword [ebx],567 *)
val th = EVAL ``x86_decode(bytebits "310B")``;            (* xor [ebx], ecx *)
val th = EVAL ``x86_decode(bytebits "3319")``;            (* xor ebx, [ecx] *)
val th = EVAL ``x86_decode(bytebits "0FB110")``;          (* cmpxchg [eax],edx *)
val th = EVAL ``x86_decode(bytebits "0FC11E")``;          (* xadd [esi],ebx *)
val th = EVAL ``x86_decode(bytebits "FF4E3C")``;          (* dec dword [esi+60] *)
val th = EVAL ``x86_decode(bytebits "4C")``;              (* dec esp *)
val th = EVAL ``x86_decode(bytebits "FF80401F0000")``;    (* inc dword [eax+8000] *)
val th = EVAL ``x86_decode(bytebits "40")``;              (* inc eax *)
val th = EVAL ``x86_decode(bytebits "F750C8")``;          (* not dword [eax-56] *)
val th = EVAL ``x86_decode(bytebits "F720")``;            (* mul dword [eax] *)
val th = EVAL ``x86_decode(bytebits "F7F6")``;            (* div esi *)
val th = EVAL ``x86_decode(bytebits "8F0590010000")``;    (* pop dword [400] *)
val th = EVAL ``x86_decode(bytebits "59")``;              (* pop ecx *)
val th = EVAL ``x86_decode(bytebits "FFB498C8010000")``;  (* push dword [eax + 4*ebx + 456] *)
val th = EVAL ``x86_decode(bytebits "FF749801")``;        (* push dword [eax + 4*ebx + 1] *)
val th = EVAL ``x86_decode(bytebits "FF74AD02")``;        (* push dword [ebp + 4*ebp + 2] *)
val th = EVAL ``x86_decode(bytebits "FF746D2D")``;        (* push dword [ebp + 2*ebp + 45] *)
val th = EVAL ``x86_decode(bytebits "FFB42DEA000000")``;  (* push dword [ebp + ebp + 234] *)
val th = EVAL ``x86_decode(bytebits "FFB4B6EE711202")``;  (* push dword [esi + 4*esi + 34763246] *)
val th = EVAL ``x86_decode(bytebits "50")``;              (* push eax *)
val th = EVAL ``x86_decode(bytebits "E8BDFFFFFF")``;      (* call l1 *)
val th = EVAL ``x86_decode(bytebits "FFD0")``;            (* call eax *)
val th = EVAL ``x86_decode(bytebits "EBB9")``;            (* jmp l1 *)
val th = EVAL ``x86_decode(bytebits "74B7")``;            (* je l1 *)
val th = EVAL ``x86_decode(bytebits "75B5")``;            (* jne l1 *)
val th = EVAL ``x86_decode(bytebits "C3")``;              (* ret *)
val th = EVAL ``x86_decode(bytebits "C20500")``;          (* ret 5 *)
val th = EVAL ``x86_decode(bytebits "E2AF")``;            (* loop l1 *)
val th = EVAL ``x86_decode(bytebits "E1AD")``;            (* loope l1 *)
val th = EVAL ``x86_decode(bytebits "E0AB")``;            (* loopne l1 *)
val th = EVAL ``x86_decode(bytebits "60")``;              (* pushad *)
val th = EVAL ``x86_decode(bytebits "61")``;              (* popad *)
val th = EVAL ``x86_decode(bytebits "0FAEF0")``;          (* mfence *)
val th = EVAL ``x86_decode(bytebits "0FAEF8")``;          (* sfence *)
val th = EVAL ``x86_decode(bytebits "0FAEE8")``;          (* lfence *)
val th = EVAL ``x86_decode(bytebits "93")``;              (* xchg eax, ebx *)
val th = EVAL ``x86_decode(bytebits "8731")``;            (* xchg [ecx], esi *)
val th = EVAL ``x86_decode(bytebits "F7583C")``;          (* neg dword [eax+60] *)

*)


(* =============================================================== *)
(*  x86 NEXT-STATE FUNCTION                                        *)
(* =============================================================== *)

val x86_decode_bytes_def = Define `
  x86_decode_bytes b = x86_decode (FOLDR APPEND [] (MAP w2bits b))`;

val X86_NEXT_def = Define `
  X86_NEXT s = 
    let e = XREAD_EIP s in                                   (* read eip *)
    let xs = MAP THE (XREAD_MEM_BYTES 20 e s) in             (* read next 20 bytes *)
    let m = x86_decode_bytes xs in                           (* attempt to decode *)
      if m = NONE then NONE else                             (* if decoded fail, return NONE *)
        let (i,w) = THE m in                                 (* otherwise extract content *)
        let n = 20 - (LENGTH w DIV 8) in                     (* calc length of instruction *)
          if EVERY (\x. ~(x = NONE)) (XREAD_MEM_BYTES n e s) (* check that memory is there *)
          then x86_execute i (n2w n) s else NONE`;           (* execute the instruction *) 


(* help to evaluate X86_NEXT *)

val X86_NEXT_THM = store_thm("X86_NEXT_THM",
  ``(x86_decode xs = SOME (i,w)) ==>
    (FOLDR APPEND [] (MAP w2bits (MAP THE (XREAD_MEM_BYTES 20 e (r,f,e,m)))) = xs) ==>
    (EVERY (\x. ~(x = NONE)) (XREAD_MEM_BYTES (20 - (LENGTH w DIV 8)) e (r,f,e,m))) ==>
    (x86_execute i (n2w (20 - (LENGTH w DIV 8))) (r,f,e,m) = SOME s') ==>
    (X86_NEXT (r,f,e,m) = SOME s')``,
  SIMP_TAC std_ss [X86_NEXT_def,LET_DEF,XREAD_EIP_def,x86_decode_bytes_def]);  

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


val _ = export_theory ();
