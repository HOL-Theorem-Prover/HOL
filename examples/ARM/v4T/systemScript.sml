(* ========================================================================= *)
(* FILE          : systemScript.sml                                          *)
(* DESCRIPTION   : Model of a basic ARM system, with upto 16 coprocessors    *)
(*                 plus main memory.                                         *)
(* AUTHOR        : Anthony Fox (with some contributions by Juliano Iyoda)    *)
(*                 University of Cambridge                                   *)
(* DATE          : 2005 - 2006                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "armTheory", "instructionTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q wordsTheory rich_listTheory updateTheory;
open armTheory instructionTheory;

val _ = new_theory "system";

val _ = wordsLib.guess_lengths();

(* -------------------------------------------------------------------------- *)
(* In what follows, the term "cp" stands for "coprocessor".                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Circuit specification for the complete ARM system (core, cp, memory, pipe) *)
(* -------------------------------------------------------------------------- *)

val ARM_IO_def = Define`
  ARM_IO (next,out1,out2) state (inp1,inp2,outp1,outp2) =
    !t. (state(t+1) = next (state t, inp2 t)) /\
        (outp1 t = out1 (state t)) /\
        (outp2 t = out2 (state t, inp1 t))`;

val MEM_IO_def = Define`
  MEM_IO (next,out1,out2) state (inp1,inp2,outp1,outp2) =
    !t. (state(t+1) = next (state t, inp2 t)) /\
        (outp1 t = out1 (state t, inp1 t)) /\
        (outp2 t = out2 (state t, inp2 t))`;

val CP_IO_def = Define`
  CP_IO (next,out) state (inp1,inp2,outp) =
    !t. (state(t+1) = next (state t, inp2 t)) /\
        (outp t = out (state t, inp1 t))`;

val MUX_2in_1out_def = Define`
  MUX_2in_1out f (inp1,inp2,outp) =
    !t. outp t = f (inp1 t, inp2 t)`;

val MUX_3in_1out_def = Define`
  MUX_3in_1out f (inp1,inp2,inp3,outp) =
    !t. outp t = f (inp1 t, inp2 t, inp3 t)`;

val MUX_6in_1out_def = Define`
  MUX_6in_1out f (inp1,inp2,inp3,inp4,inp5,inp6,outp) =
    !t. outp t = f (inp1 t, inp2 t, inp3 t, inp4 t, inp5 t, inp6 t)`;

val SYSTEM_def = Define`
  SYSTEM (next_arm, out_arm1, out_arm2, inp_arm1, inp_arm2,
          next_cp,  out_cp,  inp_cp1, inp_cp2,
          next_mem, out_mem1, out_mem2, inp_mem)
         (state_arm,state_cp,state_mem) (resets,fiqs,irqs) =
  ?arm_in1 arm_in2 cp_in1 cp_in2 mem_in arm_out1 arm_out2 cp_out
   mem_out1 mem_out2.
    MUX_2in_1out inp_arm1 (mem_out1,resets,arm_in1) /\
    MUX_6in_1out inp_arm2 (cp_out,mem_out1,mem_out2,resets,fiqs,irqs,arm_in2) /\
    MUX_2in_1out inp_cp1 (arm_out2,mem_out1,cp_in1) /\
    MUX_3in_1out inp_cp2 (arm_out2,mem_out1,mem_out2,cp_in2) /\
    MUX_2in_1out inp_mem (arm_out2,cp_out,mem_in) /\
    ARM_IO (next_arm,out_arm1,out_arm2) state_arm
       (arm_in1,arm_in2,arm_out1,arm_out2) /\
    CP_IO (next_cp,out_cp) state_cp (cp_in1,cp_in2,cp_out) /\
    MEM_IO (next_mem,out_mem1,out_mem2) state_mem
       (arm_out1,mem_in,mem_out1,mem_out2)`;

(* The circuit above is implemented with the following next state function *)

val NEXT_SYSTEM_def = Define`
  NEXT_SYSTEM
      (next_arm, out_arm1, out_arm2, inp_arm1, inp_arm2,
       next_cp,  out_cp,  inp_cp1, inp_cp2,
       next_mem, out_mem1, out_mem2, inp_mem) ((a,c,m), (r,f,i)) =
    let arm_out1 = out_arm1 a in
    let mem_out1 = out_mem1 (m, arm_out1) in
    let arm_in1  = inp_arm1 (mem_out1, r) in
    let arm_out2 = out_arm2 (a, arm_in1) in
    let cp_in1   = inp_cp1  (arm_out2, mem_out1) in
    let cp_out   = out_cp   (c, cp_in1) in
    let mem_in   = inp_mem  (arm_out2, cp_out) in
    let mem_out2 = out_mem2 (m, mem_in) in
    let arm_in2  = inp_arm2 (cp_out,mem_out1,mem_out2,r,f,i) in
    let cp_in2   = inp_cp2  (arm_out2,mem_out1,mem_out2) in
       (next_arm(a, arm_in2), next_cp(c, cp_in2), next_mem(m, mem_in))`;

(* -------------------------------------------------------------------------- *)
(* The coprocessor model is paramaterised by a collection of operations       *)
(* i.e. cdp, mrc, mcr, stc and ldc functions:                                 *)
(*                                                                            *)
(* absent: is_usr ireg => bool            ... which instructions are accepted *)
(*                                                                            *)
(* f_cdp : state is_usr ireg => state     ... operation for CDP instruction   *)
(*                                                                            *)
(* f_mrc : state is_usr ireg => word32    ... output for MRC instruction      *)
(*                                                                            *)
(* f_mcr : state is_usr ireg data => state                                    *)
(*                                        ... operation for MCR instruction   *)
(*                                                                            *)
(* f_stc : state is_usr ireg => word32 list                                   *)
(*                                        ... output for STC instruction      *)
(*                                                                            *)
(* f_ldc : state is_usr ireg data => state                                    *)
(*                                        ... operation for LDC instruction   *)
(*                                                                            *)
(* n_ldc : state is_usr ireg => num       ... number of words to load         *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype `coproc =
  <| absent : bool -> word32 -> bool;
     f_cdp  : 'a -> bool -> word32 -> 'a;
     f_mrc  : 'a -> bool -> word32 -> word32;
     f_mcr  : 'a -> bool -> word32 -> word32 -> 'a;
     f_stc  : 'a -> bool -> word32 -> word32 list;
     f_ldc  : 'a -> bool -> word32 -> word32 list -> 'a;
     n_ldc  : 'a -> bool -> word32 -> num
  |>`;

(* -------------------------------------------------------------------------- *)
(* ADD_COPROC                                                                 *)
(* Add a new coprocessor (cp1) to an existing specification (cp2)             *)
(* -------------------------------------------------------------------------- *)

val ADD_COPROC = Define`
  ADD_COPROC (cp1:'a coproc) (cp2:'b coproc) =
    <| absent := \is_usr ireg. cp1.absent is_usr ireg /\ cp2.absent is_usr ireg;
       f_cdp := \state is_usr ireg.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_cdp (FST state) is_usr ireg,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_cdp (SND state) is_usr ireg);
       f_mrc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.f_mrc (SND state) is_usr ireg
                   else
                     cp1.f_mrc (FST state) is_usr ireg;
       f_mcr := \state is_usr ireg data.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_mcr (FST state) is_usr ireg data,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_mcr (SND state) is_usr ireg data);
       f_stc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.f_stc (SND state) is_usr ireg
                   else
                     cp1.f_stc (FST state) is_usr ireg;
       f_ldc := \state is_usr ireg data.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_ldc (FST state) is_usr ireg data,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_ldc (SND state) is_usr ireg data);
       n_ldc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.n_ldc (SND state) is_usr ireg
                   else
                     cp1.n_ldc (FST state) is_usr ireg |>`;

(* -------------------------------------------------------------------------- *)
(* CP input and output                                                        *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype`
  cp_input = <| is_usr : bool; cpi : bool; ireg : word32 |>`;

val _ = Hol_datatype`
  cp_output = <| n_ldc : num; data : word32 list; absent : bool |>`;

(* -------------------------------------------------------------------------- *)
(* CPN                                                                        *)
(* Returns the coprocessor number from the instruction                        *)
(* -------------------------------------------------------------------------- *)

val DECODE_CPN_def = Define `DECODE_CPN (w:word32) = (11 >< 8) w`;

(* -------------------------------------------------------------------------- *)
(* DECODE_CDP                                                                 *)
(* -------------------------------------------------------------------------- *)

val DECODE_CDP_def = Define`
  DECODE_CDP (w:word32) =
    ((23 >< 20) w, (* Cop1 *)
     (19 >< 16) w, (* CRn  *)
     (15 >< 12) w, (* CRd  *)
     (11 >< 8) w,  (* CPN  *)
     (7 >< 5) w,   (* Cop2 *)
     (3 >< 0) w)`; (* CRm  *)

(* -------------------------------------------------------------------------- *)
(* DECODE_MRC_MCR                                                             *)
(* -------------------------------------------------------------------------- *)

val DECODE_MRC_MCR_def = Define`
  DECODE_MRC_MCR (w:word32) =
    ((23 >< 21) w, (* Cop1 *)
     (19 >< 16) w, (* CRn  *)
     (15 >< 12) w, (* Rd   *)
     (11 >< 8) w,  (* CPN  *)
     (7 >< 5) w,   (* Cop2 *)
     (3 >< 0) w)`; (* CRm  *)

(* -------------------------------------------------------------------------- *)
(* DECODE_CP                                                                  *)
(* Determines the instruction class ** for a coprocessor instruction **       *)
(* -------------------------------------------------------------------------- *)

val DECODE_CP_def = Define`
  DECODE_CP (w:word32) =
    if w ' 25 then
      if w ' 4 /\ w ' 27 then
        if w ' 20 then
          mrc
        else
          mcr
      else
        cdp_und
    else
      ldc_stc`;

(* -------------------------------------------------------------------------- *)
(* NEXT_CP                                                                    *)
(* Takes a CP state and the input (word32 list) and returns the next state    *)
(* -------------------------------------------------------------------------- *)

val NEXT_CP_def = Define`
  NEXT_CP cp (state, (cp_in, data)) =
    let ireg = cp_in.ireg and is_usr = cp_in.is_usr in
      if cp_in.cpi /\ ~cp.absent is_usr ireg then
        let ic = DECODE_CP ireg in
          if ic = mcr then
            cp.f_mcr state is_usr ireg (HD data)
          else if (ic = ldc_stc) /\ ireg ' 20 then
            cp.f_ldc state is_usr ireg data
          else if ic = cdp_und then
            cp.f_cdp state is_usr ireg
          else
            state
      else
        state`;

(* -------------------------------------------------------------------------- *)
(* OUT_CP                                                                     *)
(* It is assumed that only one coprocessor (i.e. "CP ireg") can accept the    *)
(* instruction but in general this need not be the case                       *)
(* -------------------------------------------------------------------------- *)

val OUT_CP_def = Define`
  OUT_CP cp (state, cp_in:cp_input) =
    let ireg = cp_in.ireg and is_usr = cp_in.is_usr in
      if cp_in.cpi /\ ~cp.absent is_usr ireg then
        let ic = DECODE_CP ireg in
          <| n_ldc :=
               if (ic = ldc_stc) /\ ireg ' 20 then
                 cp.n_ldc state is_usr ireg
               else
                 0;
             data :=
               if ic = mrc then
                 [cp.f_mrc state is_usr ireg]
               else if (ic = ldc_stc) /\ ~(ireg ' 20) then
                 cp.f_stc state is_usr ireg
               else
                 [];
           absent := F |>
      else
        <| n_ldc := 0; data := []; absent := T |>`;

(* -------------------------------------------------------------------------- *)
(* An Idealistic Memory Model (little-endian)                                 *)
(* -------------------------------------------------------------------------- *)

val _ = type_abbrev("mem", ``:word30->word32``);

val ADDR30_def = Define `ADDR30 (addr:word32) = (31 >< 2) addr`;

val SET_BYTE_def = Define`
  SET_BYTE (oareg:word2) (b:word8) (w:word32) =
    word_modify (\i x.
                  (i < 8) /\ (if oareg = 0w then b ' i else x) \/
       (8 <= i /\ i < 16) /\ (if oareg = 1w then b ' (i - 8) else x) \/
      (16 <= i /\ i < 24) /\ (if oareg = 2w then b ' (i - 16) else x) \/
      (24 <= i /\ i < 32) /\ (if oareg = 3w then b ' (i - 24) else x)) w`;

val SET_HALF_def = Define`
  SET_HALF (oareg:bool) (hw:word16) (w:word32) =
    word_modify (\i x.
                 (i < 16) /\ (if ~oareg then hw ' i else x) \/
      (16 <= i /\ i < 32) /\ (if oareg then hw ' (i - 16) else x)) w`;

val MEM_WRITE_BYTE_def = Define`
  MEM_WRITE_BYTE (mem:mem) addr (word:word8) =
    let addr30 = ADDR30 addr in
      (addr30 =+ SET_BYTE ((1 >< 0) addr) word (mem addr30)) mem`;

val MEM_WRITE_HALF_def = Define`
  MEM_WRITE_HALF (mem:mem) addr (word:word16) =
    let addr30 = ADDR30 addr in
      (addr30 =+ SET_HALF (addr ' 1) word (mem addr30)) mem`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD (mem:mem) addr word = (ADDR30 addr =+ word) mem`;

val MEM_WRITE_def = Define`
  MEM_WRITE mem addr d =
    case d of
       Byte b  -> MEM_WRITE_BYTE mem addr b
    || Half hw -> MEM_WRITE_HALF mem addr hw
    || Word w  -> MEM_WRITE_WORD mem addr w`;

val MEM_READ_def = Define `MEM_READ mem addr = mem (ADDR30 addr)`;

(* -------------------------------------------------------------------------- *)
(* NEXT_MEM                                                                   *)
(* Takes read and write functions, the memory state state and the input       *)
(* (memop list) and returns the next state                                    *)
(* -------------------------------------------------------------------------- *)

val WRITE_MEM_def = Define`
  (WRITE_MEM write read s [] = s) /\
  (WRITE_MEM write read s (memop::memops) =
     case memop of
        MemRead a ->
         (case read s a of
             SOME (x:word32) -> WRITE_MEM write read s memops
          || NONE   -> s)
     || MemWrite a d ->
         (case write s a d of
             SOME s' -> WRITE_MEM write read s' memops
          || NONE    -> s))`;

val NEXT_MEM_def = Define`
  NEXT_MEM write read (state, memops) = WRITE_MEM write read state memops`;

(* -------------------------------------------------------------------------- *)
(* OUT_MEM                                                                    *)
(* -------------------------------------------------------------------------- *)

val READ_MEM_def = Define`
  (READ_MEM write read (s:'a) [] dout = <| data := dout; abort := F |>) /\
  (READ_MEM write read s (memop::memops) dout =
     case memop of
        MemRead a ->
         (case read s a of
             SOME d -> READ_MEM write read s memops (dout ++ [d])
          || NONE   -> <| data := dout; abort := T |>)
     || MemWrite a x ->
         (case write s a x of
             SOME s' -> READ_MEM write read s' memops dout
          || NONE    -> <| data := dout; abort := T |>))`;

val OUT_MEM_def = Define`
  OUT_MEM write read (state, memops) = READ_MEM write read state memops []`;

(* -------------------------------------------------------------------------- *)
(* 1-stage (i.e. not pipelined)                                               *)
(* -------------------------------------------------------------------------- *)

val GET_IREG_def = Define`
  GET_IREG t (fpc1:bool) (w:word32) =
    if t then
      THUMB_TO_ARM (if fpc1 then (31 >< 16) w else (15 >< 0) w)
    else
      w`;

val NEXT_ARM_1STAGE_def = Define`
  NEXT_ARM_1STAGE (state,mem_out1,inp2) =
    let ireg = if mem_out1.abort then
                 enc (UND AL)
               else let r = state.regs in
                 GET_IREG ((CPSR_READ r.psr) ' 5) ((FETCH_PC r.reg) ' 1)
                   (HD mem_out1.data)
    in
      NEXT_ARM (state,ireg,inp2)`;

val OUT_ARM1_def = Define`
  OUT_ARM1 s = [MemRead (FETCH_PC s.regs.reg)]`;

val OUT_ARM2_def = Define`
  OUT_ARM2 (state,mem_out1,rst) =
    let ireg = if mem_out1.abort then
                 enc (UND AL)
               else let r = state.regs in
                 GET_IREG ((CPSR_READ r.psr) ' 5) ((FETCH_PC r.reg) ' 1)
                   (HD mem_out1.data)
    in
      OUT_ARM (state,ireg,rst)`;

(* -------------------------------------------------------------------------- *)
(* Input functions.                                                           *)
(* -------------------------------------------------------------------------- *)

val INP_ARM1_def = Define`
  INP_ARM1 (mem_out1:mem_output, RESET) = (mem_out1, IS_SOME RESET)`;

val INP_ARM2_def = Define`
  INP_ARM2 (cp_out, mem_out1, mem_out2, RESET, FIQ, IRQ) =
    (mem_out1,
     <| data := (mem_out2.data ++ cp_out.data);
        interrupts :=
          <| Reset := RESET;
             Prefetch := mem_out1.abort;
             Dabort := if mem_out2.abort then
                         SOME (LENGTH mem_out2.data)
                       else
                         NONE;
             Fiq := FIQ;
             Irq := IRQ |>;
        absent := cp_out.absent |>)`;

val INP_MEM_def = Define`
  INP_MEM (arm_out2:arm_output, cp_out:cp_output) =
    case arm_out2.transfers of
       MemAccess f -> f cp_out.n_ldc cp_out.data
    || _ -> []`;

val INP_CP1_def = Define`
  INP_CP1 (arm_out2:arm_output, mem_out1:mem_output) =
    <| is_usr := arm_out2.user; cpi := arm_out2.cpi;
       ireg := HD mem_out1.data |>`;

val INP_CP2_def = Define`
  INP_CP2 (arm_out2, mem_out1, mem_out2:mem_output) =
    (INP_CP1 (arm_out2, mem_out1),
     case arm_out2.transfers of
        CPWrite d -> [d]
     || _ ->  mem_out2.data)`;

(* -------------------------------------------------------------------------- *)
(* Parametrized next state and state function.                                *)
(* -------------------------------------------------------------------------- *)

val NEXT_1STAGE_def = Define`
  NEXT_1STAGE cp write read =
  NEXT_SYSTEM
     (NEXT_ARM_1STAGE, OUT_ARM1, OUT_ARM2, INP_ARM1, INP_ARM2,
      NEXT_CP cp, OUT_CP cp, INP_CP1, INP_CP2,
      NEXT_MEM write read, OUT_MEM write read, OUT_MEM write read, INP_MEM)`;

val STATE_1STAGE_def = Define`
  (STATE_1STAGE cp write read (s,i) 0 = s) /\
  (STATE_1STAGE cp write read (s,i) (SUC t) =
     NEXT_1STAGE cp write read (STATE_1STAGE cp write read (s,i) t, i t))`;

(* -------------------------------------------------------------------------- *)
(* 3-stage                                                                    *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype`
  arm_state3 = <| state : arm_state; flush : bool;
                  ir1 : word32; ir2 : word32 |>`;

val UPDATES_PC_def = Define`
  UPDATES_PC (state,ireg) =
    ~(state.exception = software) \/
    let (nzcv,i,f,t,m) = DECODE_PSR (CPSR_READ state.regs.psr) in
      CONDITION_PASSED nzcv ireg /\
     (case DECODE_ARM ireg of
         data_proc ->
           (let (I,opcode,S,Rn,Rd,opnd2) = DECODE_DATAP ireg in
              ~TEST_OR_COMP opcode /\ (Rd = 15w))
      || mla_mul   ->
           (let (L,Sgn,A,S,Rd,Rn,Rs,Rm) = DECODE_MLA_MUL ireg in
              L /\ (Rn = 15w) \/ (Rd = 15w))
      || swi_ex    -> T
      || br        -> T
      || bx        -> T
      || msr       -> F
      || mrs       -> ((15 >< 12) ireg = 15w:word4)
      || swp       -> ((15 >< 12) ireg = 15w:word4)
      || ldm_stm   ->
           (let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
              L /\ list ' 15)
      || ldr_str   ->
           (let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
              (P ==> W) /\ (Rn = 15w) \/ L /\ (Rd = 15w))
      || ldrh_strh ->
           (let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
              (P ==> W) /\ (Rn = 15w) \/ L /\ (Rd = 15w))
      || _         -> F)`;

val NEXT_ARM_3STAGE_def = Define`
  NEXT_ARM_3STAGE (state3,mem_out1,inp2) =
    if ~(state3.state.exception = software) then
      let s = NEXT_ARM (state3.state,state3.ir2,inp2) in
        <| state := s; flush := (s.exception = software);
           ir1 := state3.ir1; ir2 := state3.ir2 |>
    else
      if state3.flush /\ mem_out1.abort /\ NULL mem_out1.data then
        <| state := NEXT_ARM (state3.state with exception := pabort,
                              enc (UND AL),inp2);
           flush := F; ir1 := state3.ir1; ir2 := state3.ir2 |>
      else
        let r = state3.state.regs in
        let t = (CPSR_READ r.psr) ' 5
        and fpc1 = (FETCH_PC r.reg) ' 1
        and l = mem_out1.data in
        let ireg = GET_IREG t fpc1 (if state3.flush then HD l else state3.ir2)
        and fetch = (t ==> fpc1) in
        let s = NEXT_ARM (state3.state,ireg,inp2)
        and ir1 = if state3.flush then
                    if fetch then HD (TL (TL l)) else HD (TL l)
                  else
                    if fetch then HD l else state3.ir1
        and ir2 = if state3.flush then
                    if fetch then HD (TL l) else HD l
                  else
                    if fetch then state3.ir1 else state3.ir2
        in
          <| state := s;
             flush := (UPDATES_PC (state3.state,ireg) /\
                       (s.exception = software));
             ir1 := ir1; ir2 := ir2 |>`;

val OUT_ARM1_3STAGE_def = Define`
  OUT_ARM1_3STAGE state3 =
    if ~(state3.state.exception = software) then
      []
    else
      let r = state3.state.regs in
      let pc = FETCH_PC r.reg in
      let fpc = (31 <> 2) pc in
      let fetch = ((CPSR_READ r.psr) ' 5) ==> (pc ' 1) in
        if state3.flush then
          if fetch then
            [MemRead fpc; MemRead (fpc + 4w); MemRead (fpc + 8w)]
          else
            [MemRead fpc; MemRead (fpc + 4w)]
        else
          if fetch then
            [MemRead (fpc + 8w)]
          else
            []`;

val OUT_ARM2_3STAGE_def = Define`
  OUT_ARM2_3STAGE (state3,mem_out1,rst) =
    if ~(state3.state.exception = software) then
      OUT_ARM (state3.state,state3.ir2,rst)
    else
      if state3.flush /\ mem_out1.abort /\ NULL mem_out1.data then
        OUT_ARM (state3.state with exception := pabort,enc (UND AL),rst)
      else
        let r = state3.state.regs in
        let ireg = GET_IREG ((CPSR_READ r.psr) ' 5) ((FETCH_PC r.reg) ' 1)
                     (if state3.flush then HD mem_out1.data else state3.ir2)
        in
          OUT_ARM (state3.state,ireg,rst)`;

val NEXT_3STAGE_def = Define`
  NEXT_3STAGE cp write read =
  NEXT_SYSTEM
     (NEXT_ARM_3STAGE, OUT_ARM1_3STAGE, OUT_ARM2_3STAGE, INP_ARM1, INP_ARM2,
      NEXT_CP cp, OUT_CP cp, INP_CP1, INP_CP2,
      NEXT_MEM write read, OUT_MEM write read, OUT_MEM write read, INP_MEM)`;

val STATE_3STAGE_def = Define`
  (STATE_3STAGE cp write read (s,i) 0 = s) /\
  (STATE_3STAGE cp write read (s,i) (SUC t) =
     NEXT_3STAGE cp write read (STATE_3STAGE cp write read (s,i) t, i t))`;

(* -------------------------------------------------------------------------- *)

val STATE_1STAGE_NUM = save_thm("STATE_1STAGE_NUM",
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
    (GEN_ALL (CONJUNCT2 STATE_1STAGE_def)));

val _ = computeLib.add_persistent_funs [("STATE_1STAGE_NUM", STATE_1STAGE_NUM)];

val STATE_3STAGE_NUM = save_thm("STATE_3STAGE_NUM",
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
    (GEN_ALL (CONJUNCT2 STATE_3STAGE_def)));

val _ = computeLib.add_persistent_funs [("STATE_3STAGE_NUM", STATE_3STAGE_NUM)];

(* -------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val t =
let val c = concl (SPEC_ALL SYSTEM_def)
    val l = lhs c
    val r = snd (strip_exists (rhs c))
    val rr = ``?arm_out1 mem_out1 arm_in1 arm_out2 cp_in1 cp_out
                mem_in mem_out2 arm_in2 cp_in2. ^r``
in
  mk_eq(l,rr)
end;

val SYSTEM = GEN_ALL (Tactical.prove(t,
  EQ_TAC \\ SRW_TAC [] [SYSTEM_def] \\ METIS_TAC []));

fun EXISTS_MATCH_STREAM_TAC q (g as (asl, w)) =
let
  val fv_set = FVL (w::asl) empty_tmset
  val ctxt = HOLset.listItems fv_set
  val r = Parse.parse_in_context ctxt q
  fun matchr t = raw_match [] fv_set r t ([],[])
  fun finder t = not (is_var t orelse is_const t) andalso can matchr t
in
  case Lib.total (find_term finder) w of
    NONE => raise HOL_ERR {origin_function = "MATCH_TERM_TAC",
                           origin_structure = "systemTheory",
                           message = "No matching term found"}
  | SOME t => Tactic.EXISTS_TAC (mk_abs(``t:num``,t)) g
end;

val SYSTEM_THM = store_thm("SYSTEM_THM",
  `SYSTEM (next_arm, out_arm1, out_arm2, inp_arm1, inp_arm2,
           next_cp,  out_cp, inp_cp1, inp_cp2,
           next_mem, out_mem1, out_mem2, inp_mem)
         (state_arm,state_cp,state_mem) (resets,fiqs,irqs) =
   !t. (state_arm(t+1), state_cp(t+1), state_mem(t+1)) =
       NEXT_SYSTEM
         (next_arm, out_arm1, out_arm2, inp_arm1, inp_arm2,
           next_cp,  out_cp, inp_cp1, inp_cp2,
           next_mem, out_mem1, out_mem2, inp_mem)
         ((state_arm t, state_cp t, state_mem t),
          (resets t, fiqs t, irqs t))`,
  EQ_TAC << [
    SRW_TAC [] [SYSTEM, MUX_6in_1out_def, MUX_3in_1out_def, MUX_2in_1out_def,
                ARM_IO_def, MEM_IO_def, CP_IO_def]
      \\ Induct_on `t`
      \\ SRW_TAC [boolSimps.LET_ss] [NEXT_SYSTEM_def],
    SRW_TAC [boolSimps.LET_ss]
            [NEXT_SYSTEM_def, SYSTEM, MUX_6in_1out_def, MUX_3in_1out_def,
             MUX_2in_1out_def, ARM_IO_def, MEM_IO_def, CP_IO_def,
             GSYM FORALL_AND_THM]
      \\ MAP_EVERY EXISTS_MATCH_STREAM_TAC
           [`out_arm1 X`, `out_mem1 X`, `inp_arm1 X`, `out_arm2 X`, `inp_cp1 X`,
            `out_cp X`, `inp_mem X`, `out_mem2 X`, `inp_arm2 X`, `inp_cp2 X`]
      \\ SRW_TAC [] []]);

(* ------------------------------------------------------------------------- *)
(* Export ML versions of functions                                           *)
(*---------------------------------------------------------------------------*)

val BASIC_WRITE_def = Define `BASIC_WRITE m a x = SOME (MEM_WRITE m a x)`;
val BASIC_READ_def  = Define `BASIC_READ (m:mem) a = SOME (MEM_READ m a)`;
val NO_CP_def       = Define `NO_CP = <| absent := \u i. T |> : 'a coproc`;
val NO_IRPTS_def    = Define `NO_IRPTS (t:num) = (NONE:regs option, F, F)`;

val mem_read_def        = Define`mem_read (m: mem, a) = m a`;
val mem_write_def       = Define`mem_write (m:mem) a d = (a =+ d) m`;
val mem_write_block_def = Define`mem_write_block (m:mem) a cr = (a |: cr) m`;
val empty_memory_def    = Define`empty_memory = (\a. enc (UND AL)):mem`;
val empty_registers_def = Define`empty_registers = (\n. 0w):registers`;
val empty_psrs_def      = Define`empty_psrs = (\x. SET_IFTM F F F usr 0w):psrs`;

(* ------------------------------------------------------------------------- *)

open arithmeticTheory numeralTheory bitTheory;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val word_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++
  rewrites [n2w_def,word_extract_def,word_bits_n2w,w2w,
    BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
    DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def]

val MOD_DIMINDEX_32 = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
   Thm.INST_TYPE [alpha |-> ``:32``]) MOD_DIMINDEX;

val DECODE_TAC = SIMP_TAC std_ss [DECODE_PSR_def,DECODE_BRANCH_def,
      DECODE_DATAP_def,DECODE_MRS_def,DECODE_MSR_def,DECODE_LDR_STR_def,
      DECODE_LDRH_STRH_def,DECODE_MLA_MUL_def,DECODE_LDM_STM_def,
      DECODE_SWP_def,DECODE_LDC_STC_def,DECODE_CDP_def,DECODE_MRC_MCR_def,
      SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,
      CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV rich_listTheory.GENLIST,
      NZCV_def,REGISTER_LIST_def,rich_listTheory.SNOC,word_extract_def]
 \\ SIMP_TAC word_ss [];

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,t) = DIVMOD_2EXP 1 q0 in
     let (q2,i) = DIVMOD_2EXP 1 q1 in
     let (q3,f) = DIVMOD_2EXP 1 q2 in
     let (q4,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q3) in
     let (q5,C) = DIVMOD_2EXP 1 q4 in
     let (q6,Z) = DIVMOD_2EXP 1 q5 in
       ((ODD q6,Z=1,C=1,V=1),f = 1,i = 1,t = 1,n2w m)`, DECODE_TAC);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH (n2w n) =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,n2w offset)`, DECODE_TAC);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP (n2w n) =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,n2w opcode,S = 1,n2w Rn,n2w Rd,n2w opnd2)`, DECODE_TAC);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS (n2w n) =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),n2w Rd)`, DECODE_TAC);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR (n2w n) =
     let (q0,opnd) = DIVMOD_2EXP 12 n in
     let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
     let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
     let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
       (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,
        n2w (MOD_2EXP 4 opnd),n2w opnd)`,
  DECODE_TAC \\ `4096 = 16 * 256` by numLib.ARITH_TAC
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC arith_ss [MOD_MULT_MOD]);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 12 n in
    let (q1,Rd) = DIVMOD_2EXP 4 q0 in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,L) = DIVMOD_2EXP 1 q2 in
    let (q4,W) = DIVMOD_2EXP 1 q3 in
    let (q5,B) = DIVMOD_2EXP 1 q4 in
    let (q6,U) = DIVMOD_2EXP 1 q5 in
    let (q7,P) = DIVMOD_2EXP 1 q6 in
      (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,n2w Rn,n2w Rd,n2w offset)`,
   DECODE_TAC);

val DECODE_LDRH_STRH_THM = store_thm("DECODE_LDRH_STRH_THM",
  `!n. DECODE_LDRH_STRH (n2w n) =
    let (q0,offsetL) = DIVMOD_2EXP 4 n in
    let (q1,H) = DIVMOD_2EXP 1 (DIV2 q0) in
    let (q2,S) = DIVMOD_2EXP 1 q1 in
    let (q3,offsetH) = DIVMOD_2EXP 4 (DIV2 q2) in
    let (q4,Rd) = DIVMOD_2EXP 4 q3 in
    let (q5,Rn) = DIVMOD_2EXP 4 q4 in
    let (q6,L) = DIVMOD_2EXP 1 q5 in
    let (q7,W) = DIVMOD_2EXP 1 q6 in
    let (q8,I) = DIVMOD_2EXP 1 q7 in
    let (q9,U) = DIVMOD_2EXP 1 q8 in
      (ODD q9,U = 1,I = 1,W = 1,L = 1,n2w Rn,n2w Rd,
       n2w offsetH,S = 1,H = 1,n2w offsetL)`,
   DECODE_TAC);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,Rd) = DIVMOD_2EXP 4 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,A) = DIVMOD_2EXP 1 q4 in
    let (q6,Sgn) = DIVMOD_2EXP 1 q5 in
      (ODD q6,Sgn = 1,A = 1,S = 1,n2w Rd,n2w Rn,n2w Rs,n2w Rm)`, DECODE_TAC);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM (n2w n) =
    let (q0,list) = DIVMOD_2EXP 16 n in
    let (q1,Rn) = DIVMOD_2EXP 4 q0 in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,U) = DIVMOD_2EXP 1 q4 in
      (ODD q5, U = 1, S = 1, W = 1, L = 1,n2w Rn,n2w list)`, DECODE_TAC);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),n2w Rn,n2w Rd,n2w Rm)`, DECODE_TAC);

val DECODE_LDC_STC_THM = store_thm("DECODE_LDC_STC_THM",
  `!n. DECODE_LDC_STC (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 8 n in
    let (q1,CPN) = DIVMOD_2EXP 4 q0 in
    let (q2,CRd) = DIVMOD_2EXP 4 q1 in
    let (q3,Rn) = DIVMOD_2EXP 4 q2 in
    let (q4,L) = DIVMOD_2EXP 1 q3 in
    let (q5,W) = DIVMOD_2EXP 1 q4 in
    let (q6,N) = DIVMOD_2EXP 1 q5 in
    let (q7,U) = DIVMOD_2EXP 1 q6 in
      (ODD q7,U = 1,N = 1,W = 1,L = 1,n2w Rn,n2w CRd,n2w CPN,n2w offset)`,
  DECODE_TAC);

val DECODE_CDP_THM = store_thm("DECODE_CDP_THM",
  `!n. DECODE_CDP (n2w n) =
    let (q0,CRm) = DIVMOD_2EXP 4 n in
    let (q1,Cop2) = DIVMOD_2EXP 3 (DIV2 q0) in
    let (q2,CPN) = DIVMOD_2EXP 4 q1 in
    let (q3,CRd) = DIVMOD_2EXP 4 q2 in
    let (q4,CRn) = DIVMOD_2EXP 4 q3 in
      (n2w (MOD_2EXP 4 q4),n2w CRn,n2w CRd,n2w CPN,n2w Cop2,n2w CRm)`,
  DECODE_TAC);

val DECODE_MRC_MCR_THM = store_thm("DECODE_MRC_MCR_THM",
  `!n. DECODE_MRC_MCR (n2w n) =
    let (q0,CRm) = DIVMOD_2EXP 4 n in
    let (q1,Cop2) = DIVMOD_2EXP 3 (DIV2 q0) in
    let (q2,CPN) = DIVMOD_2EXP 4 q1 in
    let (q3,CRd) = DIVMOD_2EXP 4 q2 in
    let (q4,CRn) = DIVMOD_2EXP 4 q3 in
      (n2w (MOD_2EXP 3 (DIV2 q4)),n2w CRn,n2w CRd,n2w CPN,n2w Cop2,n2w CRm)`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

fun w2w_n2w_sizes a b = (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
  Thm.INST_TYPE [alpha |-> a, beta |-> b]) w2w_n2w;

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!reg t mode C opnd2.
     SHIFT_IMMEDIATE reg t mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let shift = MOD_2EXP 5 q1 in
       let rm = REG_READ t reg mode (n2w Rm) in
         SHIFT_IMMEDIATE2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:12``) [``:8``, ``:4``, ``:2``])
    \\ DECODE_TAC);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg t mode C opnd2.
     SHIFT_REGISTER reg t mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ t reg mode (n2w Rs)))
       and rm = REG_READ t (INC_PC t reg) mode (n2w Rm) in
         SHIFT_REGISTER2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC [w2w_n2w_sizes ``:32`` ``:8``]
    \\ ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:12``) [``:8``, ``:4``, ``:2``])
    \\ SIMP_TAC std_ss [SHIFT_REGISTER_def,word_extract_def,
         (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [n2w_w2n,BITS_THM,DIV_1,
            (GSYM o SIMP_RULE std_ss [] o SPEC `8`) MOD_2EXP_def] o
          SPECL [`7`,`0`,`w2n (a:word32)`] o
          Thm.INST_TYPE [alpha |-> ``:32``]) word_bits_n2w]
    \\ SIMP_TAC word_ss []);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST (n2w n) =
       let (q0,b0) = DIVMOD_2EXP 1 n in
       let (q1,b1) = DIVMOD_2EXP 1 q0 in
       let (q2,b2) = DIVMOD_2EXP 1 q1 in
       let (q3,b3) = DIVMOD_2EXP 1 q2 in
       let (q4,b4) = DIVMOD_2EXP 1 q3 in
       let (q5,b5) = DIVMOD_2EXP 1 q4 in
       let (q6,b6) = DIVMOD_2EXP 1 q5 in
       let (q7,b7) = DIVMOD_2EXP 1 q6 in
       let (q8,b8) = DIVMOD_2EXP 1 q7 in
       let (q9,b9) = DIVMOD_2EXP 1 q8 in
       let (q10,b10) = DIVMOD_2EXP 1 q9 in
       let (q11,b11) = DIVMOD_2EXP 1 q10 in
       let (q12,b12) = DIVMOD_2EXP 1 q11 in
       let (q13,b13) = DIVMOD_2EXP 1 q12 in
       let (q14,b14) = DIVMOD_2EXP 1 q13 in
       MAP SND (FILTER FST
         [(b0 = 1,0w); (b1 = 1,1w); (b2 = 1,2w); (b3 = 1,3w);
          (b4 = 1,4w); (b5 = 1,5w); (b6 = 1,6w); (b7 = 1,7w);
          (b8 = 1,8w); (b9 = 1,9w); (b10 = 1,10w); (b11 = 1,11w);
          (b12 = 1,12w); (b13 = 1,13w); (b14 = 1,14w); (ODD q14,15w)])`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val DECODE_ARM_THM = store_thm("DECODE_ARM_THM",
  `!ireg. DECODE_ARM (ireg : word32) =
    let b n = ireg ' n in
      if b 27 then
        if b 26 then
          if b 25 then
            if b 24 then (* (T,T,T,T,...) *)
              swi_ex
            else (* (T,T,T,F,...) *)
              if b 4 then
                if b 20 then mrc else mcr
              else
                cdp_und
          else (* (T,T,F,...) *)
            ldc_stc
        else (* (T,F,...) *)
          if b 25 then br else ldm_stm
      else
         if b 26 then (* (F,T,...) *)
           if b 25 then
             if b 4 then cdp_und else ldr_str
           else
             ldr_str
         else
           if b 25 then (* (F,F,T,...) *)
             if b 24 /\ ~b 23 /\ ~b 20 then
               if b 21 then
                 msr
               else
                 cdp_und
             else
               data_proc
           else
             if b 24 then (* (F,F,F,T,...) *)
               if b 7 then
                 if b 4 then
                   if b 20 then
                     if b 6 then
                       ldrh_strh
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 6 then
                       cdp_und
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         if ~b 23 /\ ~b 21 then
                           swp
                         else
                           cdp_und
                 else
                   data_proc
               else
                 if b 4 then
                   if ~b 23 /\ ~b 22 /\ b 21 /\ ~b 20 /\ ~b 6 /\ ~b 5 then
                     bx
                   else
                     data_proc
                 else
                   if ~b 23 /\ ~b 20 /\ ~b 6 /\ ~b 5 then
                     if b 21 then msr else mrs
                   else
                     data_proc
             else (* (F,F,F,F,...) *)
               if b 7 then
                 if b 4 then
                   if b 6 \/ b 5 then
                     if b 20 /\ b 6 then
                       ldrh_strh
                     else
                       if ~b 6 /\ b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 23 \/ ~b 22 then mla_mul else cdp_und
                 else
                   data_proc
               else
                 if b 4 then data_proc else data_proc`,
  SRW_TAC [boolSimps.LET_ss] [DECODE_ARM_def]
    \\ FULL_SIMP_TAC (srw_ss()) [bool_case_ID]);

(*---------------------------------------------------------------------------*)

val num2register = prove(
  `!n. num2register n =
         if n = 0 then r0 else
         if n = 1 then r1 else
         if n = 2 then r2 else
         if n = 3 then r3 else
         if n = 4 then r4 else
         if n = 5 then r5 else
         if n = 6 then r6 else
         if n = 7 then r7 else
         if n = 8 then r8 else
         if n = 9 then r9 else
         if n = 10 then r10 else
         if n = 11 then r11 else
         if n = 12 then r12 else
         if n = 13 then r13 else
         if n = 14 then r14 else
         if n = 15 then r15 else
         if n = 16 then r8_fiq else
         if n = 17 then r9_fiq else
         if n = 18 then r10_fiq else
         if n = 19 then r11_fiq else
         if n = 20 then r12_fiq else
         if n = 21 then r13_fiq else
         if n = 22 then r14_fiq else
         if n = 23 then r13_irq else
         if n = 24 then r14_irq else
         if n = 25 then r13_svc else
         if n = 26 then r14_svc else
         if n = 27 then r13_abt else
         if n = 28 then r14_abt else
         if n = 29 then r13_und else
         if n = 30 then r14_und else
           FAIL num2register ^(mk_var("30 < n",bool)) n`,
  SRW_TAC [] [num2register_thm, combinTheory.FAIL_THM]);

val num2condition = prove(
  `!n. num2condition n =
         if n = 0 then EQ else
         if n = 1 then CS else
         if n = 2 then MI else
         if n = 3 then VS else
         if n = 4 then HI else
         if n = 5 then GE else
         if n = 6 then GT else
         if n = 7 then AL else
         if n = 8 then NE else
         if n = 9 then CC else
         if n = 10 then PL else
         if n = 11 then VC else
         if n = 12 then LS else
         if n = 13 then LT else
         if n = 14 then LE else
         if n = 15 then NV else
           FAIL num2condition ^(mk_var("15 < n",bool)) n`,
  SRW_TAC [] [num2condition_thm, combinTheory.FAIL_THM]);

(*---------------------------------------------------------------------------*)

val _ = type_pp.pp_num_types := false;
val _ = type_pp.pp_array_types := false;

val _ =
 let open EmitML
     fun f x = [QUOTE (EmitTeX.datatype_thm_to_string x)]
     val g = GEN_ALL o SIMP_RULE bool_ss [wordsTheory.n2w_w2n]
     val word12_rule = g o INST [`opnd2` |-> `w2n (w:word12)`] o SPEC_ALL
     val word16_rule = g o Q.SPEC `w2n (w:word16)`
     val word32_rule = g o Q.SPEC `w2n (w:word32)`
     val mem_rule = REWRITE_RULE [GSYM mem_read_def, GSYM mem_write_def]
     val und_rule = REWRITE_RULE [EVAL ``enc (UND AL)``]
     fun mk_word n = let val s = Int.toString n in
                       EmitML.MLSIG ("type word" ^ s ^ " = wordsML.word" ^ s)
                     end
 in
   emitML (!Globals.emitMLDir) ("arm",
    OPEN ["num", "option", "set", "fcp", "list", "rich_list", "bit", "words"]
    :: MLSIG "type 'a itself = 'a fcpML.itself"
    :: MLSIG "type 'a word = 'a wordsML.word"
    :: MLSIG "type ('a,'b) cart = ('a,'b) fcpML.cart"
    :: MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum"
    :: MLSIG "type 'a bit0 = 'a fcpML.bit0"
    :: MLSIG "type 'a bit1 = 'a fcpML.bit1"
    :: MLSIG "type num = numML.num"
    :: map mk_word [2,3,4,5,8,12,16,24,30,32]
     @ map (DATATYPE o f) [datatype_register, datatype_psr]
     @ EQDATATYPE ([], f datatype_iclass)
    :: MLSTRUCT "type registers = register->word32"
    :: MLSTRUCT "type psrs = psr->word32"
    :: MLSTRUCT "type mem = word30->word32"
    :: MLSIG "type registers = register->word32"
    :: MLSIG "type psrs = psr->word32"
    :: MLSIG "type mem = word30->word32"
    :: map (DATATYPE o f)
         [datatype_mode, datatype_condition, datatype_exceptions,
          datatype_regs, datatype_arm_state, datatype_formats,
          datatype_data, datatype_memop, datatype_transfers,
          datatype_arm_output, datatype_interrupts, datatype_arm_input,
          datatype_mem_output, theorem "datatype_cp_input",
          theorem "datatype_cp_output", theorem "datatype_coproc"]
    @ map (DEFN o wordsLib.WORDS_EMIT_RULE) (map word32_rule
         [DECODE_PSR_THM, DECODE_BRANCH_THM, DECODE_DATAP_THM,
          DECODE_MRS_THM, DECODE_MSR_THM, DECODE_LDR_STR_THM,
           DECODE_MLA_MUL_THM, DECODE_LDM_STM_THM, DECODE_SWP_THM,
           DECODE_LDC_STC_THM, DECODE_LDRH_STRH_THM, DECODE_CDP_THM,
           DECODE_MRC_MCR_THM]
       @ [LUPDATE_def, mem_read_def, mem_write_def, mem_write_block_def,
          und_rule empty_memory_def, ADDR30_def, GET_HALF_def,
          GET_BYTE_def, FORMAT_def, SET_BYTE_def, SET_HALF_def,
          mem_rule MEM_WRITE_BYTE_def, mem_rule MEM_WRITE_HALF_def,
          mem_rule MEM_WRITE_WORD_def, MEM_WRITE_def, MEM_READ_def,
          BASIC_READ_def, BASIC_WRITE_def, NO_IRPTS_def,
          DECODE_CPN_def, DECODE_CP_def, USER_def, mode_reg2num_def,
          DECODE_ARM_def, mode_num_def, exceptions2num_thm, register2num_thm,
          num2register, num2condition, SET_IFTM_def, SET_THUMB_def,
          REG_READ_def, REG_WRITE_def, INC_PC_def, FETCH_PC_def,
          SET_NZCV_def, SET_NZC_def, SET_NZ_def, DECODE_MODE_def,
          NZCV_def, CARRY_def, mode2psr_def, SPSR_READ_def, CPSR_READ_def,
          CPSR_WRITE_def, SPSR_WRITE_def, exception2mode_def,
          SPECL [`r`,`t`,`e`] EXCEPTION_def, BRANCH_def, BRANCH_EXCHANGE_def,
          LSL_def, LSR_def, ASR_def, ROR_def,
          IMMEDIATE_def, SHIFT_IMMEDIATE2_def,
          SHIFT_REGISTER2_def, word12_rule SHIFT_IMMEDIATE_THM,
          word12_rule SHIFT_REGISTER_THM, ADDR_MODE1_def,
          SPEC `f` ALU_arith_def, ALU_logic_def,
          ADD_def, SUB_def, AND_def, EOR_def, ORR_def,
          ALU_def, ARITHMETIC_def, TEST_OR_COMP_def, DATA_PROCESSING_def,
          MRS_def, MSR_def, ALU_multiply_def, MLA_MUL_def,
          UP_DOWN_def, ADDR_MODE2_def, IMP_DISJ_THM, LDR_STR_def,
          ADDR_MODE3_def, LDRH_STRH_def, word16_rule REGISTER_LIST_THM,
          ADDRESS_LIST_def, WB_ADDRESS_def, FIRST_ADDRESS_def,
          ADDR_MODE4_def, LDM_LIST_def, STM_LIST_def, STM_DATA_def, LDM_STM_def,
          SWP_def, MRC_def, MCR_def, ADDR_MODE5_def, LDC_STC_def,
          CONDITION_PASSED2_def, CONDITION_PASSED_def, THUMB_TO_ARM_def,
          GET_IREG_def, RUN_ARM_def, interrupt2exception_def,
          WRITE_MEM_def, READ_MEM_def, NoTransfers_def,
          NEXT_ARM_def, und_rule NEXT_ARM_1STAGE_def, OUT_ARM1_def, OUT_ARM_def,
          und_rule OUT_ARM2_def, INP_ARM1_def, INP_ARM2_def,
          NEXT_CP_def, OUT_CP_def, und_rule INP_CP1_def, INP_CP2_def,
          NEXT_MEM_def, OUT_MEM_def, INP_MEM_def,
          NEXT_SYSTEM_def, NEXT_1STAGE_def, empty_registers_def]))
 end;

(* -------------------------------------------------------------------------- *)

val _ = export_theory();
