(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Defines ARM state-space and a sequential state-transforming Monad    *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_astTheory", "wordsLib"];
  val _ = HOL_Interactive.toggle_quietdec();
*)

open HolKernel boolLib bossLib Parse;
open wordsLib;

open arm_astTheory;

val _ = new_theory "arm_seq_monad";

(* ------------------------------------------------------------------------ *)

(* ---------------------------- *)
(* Monad for exclusive monitors *)
(* ---------------------------- *)

val _ = type_abbrev("exclusive_triple", ``: FullAddress # iiid # num``);

val _ = type_abbrev("exclusive_state",
  ``: (proc -> FullAddress set) # (FullAddress # proc) set``);

val _ = type_abbrev("ExclusiveM",
  ``: exclusive_state -> ('a # exclusive_state)``);

val constE_def = Define`
  (constE: 'a -> 'a ExclusiveM) x = \y. (x,y)`;

val seqE_def = Define`
  (seqE: 'a ExclusiveM -> ('a -> 'b ExclusiveM) -> 'b ExclusiveM) s f =
  \y. let (v,x) = s y in f v x`;

val _ = Hol_datatype `ExclusiveMonitors =
  <| state                   : exclusive_state;
     MarkExclusiveGlobal     : exclusive_triple -> unit ExclusiveM;
     MarkExclusiveLocal      : exclusive_triple -> unit ExclusiveM;
     IsExclusiveGlobal       : exclusive_triple -> bool ExclusiveM;
     IsExclusiveLocal        : exclusive_triple -> bool ExclusiveM;
     ClearExclusiveByAddress : exclusive_triple -> unit ExclusiveM;
     ClearExclusiveLocal     : proc -> unit ExclusiveM
  |>`;

(* ---------------------- *)
(* Monad for Coprocessors *)
(* ---------------------- *)

val _ = type_abbrev("cp_state",``:CP15reg``);

val _ = type_abbrev("CoprocessorM", ``:cp_state -> ('a # cp_state)``);

val constC_def = Define`
  (constC: 'a -> 'a CoprocessorM) x = \y. (x,y)`;

val seqC_def = Define`
  (seqC: 'a CoprocessorM -> ('a -> 'b CoprocessorM) -> 'b CoprocessorM) s f =
  \y. let (v,x) = s y in f v x`;

val _ = Hol_datatype `Coprocessors =
  <| state        : cp_state;
     accept       : CPinstruction -> bool CoprocessorM;
     internal_op  : CPinstruction -> unit CoprocessorM;
     load_count   : CPinstruction -> num CoprocessorM;
     load         : CPinstruction -> word32 list -> unit CoprocessorM;
     store        : CPinstruction -> word32 list CoprocessorM;
     send_one     : CPinstruction -> word32 -> unit CoprocessorM;
     get_one      : CPinstruction -> word32 CoprocessorM;
     send_two     : CPinstruction -> word32 # word32 -> unit CoprocessorM;
     get_two      : CPinstruction -> (word32 # word32) CoprocessorM
  |>`;

(* ------------- *)
(* Monad for ARM *)
(* ------------- *)

val _ = Hol_datatype `arm_state =
  <| registers      : proc # RName -> word32;    (* general-purpose *)
     psrs           : proc # PSRName -> ARMpsr; (* program-status  *)
     event_register : proc -> bool;
     interrupt_wait : proc -> bool;
     memory         : FullAddress -> word8;
     accesses       : memory_access list;
     information    : ARMinfo;
     coprocessors   : Coprocessors;
     monitors       : ExclusiveMonitors (* synchronization & semaphores *)
  |>`;

(* ------------------------------------------------------------------------ *)

val _ = Hol_datatype `error_option = ValueState of 'a => 'b | Error of string`;

val _ = type_abbrev("M",``:arm_state -> ('a, arm_state) error_option``);

val constT_def = Define`
  (constT: 'a -> 'a M) x = \y. ValueState x y`;

val errorT_def = Define`
  (errorT : string -> 'a M) e = K (Error e)`;

val seqT_def = Define`
  (seqT: 'a M -> ('a -> 'b M) -> 'b M) s f =
   \y. case s y of Error e -> Error e
                || ValueState z t -> f z t`;

val parT_def = Define`
  (parT: 'a M -> 'b M -> ('a # 'b) M) s t =
    seqT s (\x. seqT t (\y. constT (x,y)))`;

val lockT_def = Define`
  (lockT: 'a M -> 'a M) s = s`;

val condT_def = Define`
  (condT: bool -> unit M -> unit M) =
    \b s. if b then s else constT ()`;

val forT_def = tDefine "forT"
 `forT (l : num) (h : num) (f : num -> 'a M) : ('a list) M =
    if l <= h then
      seqT (f l)
      (\r. seqT (forT (l + 1) h f) (\l. constT (r::l)))
    else
      constT []`
 (WF_REL_TAC `measure (\(l,h,f). h + 1 - l)`);

val readT_def  = Define `(readT f  : 'a M)   = \y. ValueState (f y) y`;
val writeT_def = Define `(writeT f : unit M) = \y. ValueState () (f y)`;

(* ARM specific operations *)

val read_info_def = Define`
  read_info (ii:iiid) = readT arm_state_information`;

val read_arch_def = Define`
  read_arch (ii:iiid) = readT (ARMinfo_arch o arm_state_information)`;

val read_extensions_def = Define`
  read_extensions (ii:iiid) =
    readT (ARMinfo_extensions o arm_state_information)`;

val read__reg_def = Define`
  read__reg (ii:iiid) rname = readT (\s. s.registers (ii.proc,rname))`;

val write__reg_def = Define`
  write__reg (ii:iiid) rname value =
    writeT (arm_state_registers_fupd ((ii.proc,rname) =+ value))`;

val read__psr_def = Define`
  read__psr (ii:iiid) i = readT (\s. s.psrs (ii.proc,i))`;

val write__psr_def = Define`
  (write__psr (ii:iiid) psrname value):unit M =
    writeT (arm_state_psrs_fupd ((ii.proc,psrname) =+ value))`;

val read_scr_def = Define`
  read_scr (ii:iiid) = readT (\s. s.coprocessors.state.SCR)`;

val write_scr_def = Define`
  write_scr (ii:iiid) value =
    writeT (arm_state_coprocessors_fupd (Coprocessors_state_fupd
           (\state. state with <| SCR := value |>)))`;

val read_nsacr_def = Define`
  read_nsacr (ii:iiid) = readT (\s. s.coprocessors.state.NSACR)`;

val read_sctlr_def = Define`
  read_sctlr (ii:iiid) = readT (\s. s.coprocessors.state.SCTLR)`;

val read_cpsr_def  = Define `read_cpsr ii = read__psr ii CPSR`;

val write_cpsr_def = Define`
  write_cpsr ii value = write__psr ii CPSR value`;

val read_isetstate_def = Define`
  read_isetstate (ii:iiid) =
    seqT (read_cpsr ii)
    (\cpsr.
       constT ((FCP i. (i = 1) /\ cpsr.J \/ (i = 0) /\ cpsr.T):word2))`;

val write_isetstate_def = Define`
  write_isetstate ii (isetstate:word2) =
    seqT (read_cpsr ii)
    (\cpsr.
       write_cpsr ii
         (cpsr with <| J := isetstate ' 1; T := isetstate ' 0 |>))`;

val have_security_ext_def = Define`
  have_security_ext (ii:iiid) =
    seqT (read_extensions ii)
    (\ext. constT (Extension_Security IN ext))`;

val bad_mode_def = Define`
  bad_mode (ii:iiid) (mode:word5) =
    if mode = 0b10110w then
      seqT (have_security_ext ii)
      (\have_security_ext. constT (~have_security_ext))
    else
      constT (mode NOTIN {0b10000w;
                          0b10001w;
                          0b10010w;
                          0b10011w;
                          0b10111w;
                          0b11011w;
                          0b11111w})`;

val read_spsr_def = Define`
  read_spsr (ii:iiid) =
    seqT (read_cpsr ii)
    (\cpsr.
       seqT (bad_mode ii cpsr.M)
       (\bad_mode.
         if bad_mode then
           errorT "read_spsr: unpredictable"
         else
           case cpsr.M
           of 0b10001w -> read__psr ii SPSR_fiq  (* FIQ mode *)
           || 0b10010w -> read__psr ii SPSR_irq  (* IRQ mode *)
           || 0b10011w -> read__psr ii SPSR_svc  (* Supervisor mode *)
           || 0b10110w -> read__psr ii SPSR_mon  (* Monitor mode *)
           || 0b10111w -> read__psr ii SPSR_abt  (* Abort mode *)
           || 0b11011w -> read__psr ii SPSR_und  (* Undefined mode *)
           || _ -> errorT "read_spsr: unpredictable"))`;

val write_spsr_def = Define`
  write_spsr (ii:iiid) value =
    seqT (read_cpsr ii)
    (\cpsr.
       seqT (bad_mode ii cpsr.M)
       (\bad_mode.
         if bad_mode then
           errorT "write_spsr: unpredictable"
         else
           case cpsr.M
           of 0b10001w -> write__psr ii SPSR_fiq value (* FIQ mode *)
           || 0b10010w -> write__psr ii SPSR_irq value (* IRQ mode *)
           || 0b10011w -> write__psr ii SPSR_svc value (* Supervisor mode *)
           || 0b10110w -> write__psr ii SPSR_mon value (* Monitor mode *)
           || 0b10111w -> write__psr ii SPSR_abt value (* Abort mode *)
           || 0b11011w -> write__psr ii SPSR_und value (* Undefined mode *)
           || _ -> errorT "write_spsr: unpredictable"))`;

val current_mode_is_priviledged_def = Define`
  current_mode_is_priviledged (ii:iiid) =
    seqT (read_cpsr ii)
    (\cpsr.
      seqT (bad_mode ii cpsr.M)
      (\bad_mode.
         if bad_mode then
           errorT "current_mode_is_priviledged: unpredictable"
         else
           constT (cpsr.M <> 0b10000w)))`;

val current_mode_is_user_or_system_def = Define`
  current_mode_is_user_or_system (ii:iiid) =
    seqT (read_cpsr ii)
    (\cpsr.
      seqT (bad_mode ii cpsr.M)
      (\bad_mode.
         if bad_mode then
           errorT "current_mode_is_user_or_system: unpredictable"
         else
           constT (cpsr.M IN {0b10000w; 0b11111w})))`;

val is_secure_def = Define`
  is_secure (ii:iiid) =
    seqT
      (parT (have_security_ext ii)
         (parT (read_scr ii) (read_cpsr ii)))
      (\(have_security_ext,scr,cpsr).
         constT (~have_security_ext \/ ~scr.NS \/ (cpsr.M = 0b10110w)))`;

val read_vbar_def = Define`
  read_vbar ii =
    seqT (is_secure ii)
    (\is_secure.
       if is_secure then
         readT (\s. s.coprocessors.state.VBAR.secure)
       else
         readT (\s. s.coprocessors.state.VBAR.non_secure))`;

val read_mvbar_def = Define`
  read_mvbar (ii:iiid) = readT (\s. s.coprocessors.state.MVBAR)`;

val current_instr_set_def = Define`
  current_instr_set ii =
    seqT (read_isetstate ii)
    (\isetstate.
      constT
       (case isetstate
        of 0b00w -> InstrSet_ARM
        || 0b01w -> InstrSet_Thumb
        || 0b10w -> InstrSet_Jazelle
        || 0b11w -> InstrSet_ThumbEE))`;

val select_instr_set_def = Define`
  select_instr_set ii (iset:InstrSet) =
    case iset
    of InstrSet_ARM ->
         seqT (current_instr_set ii)
           (\current_instr_set.
              if current_instr_set = InstrSet_ThumbEE then
                errorT "select_instr_set: unpredictable"
              else
                write_isetstate ii 0b00w)
    || InstrSet_Thumb ->
         write_isetstate ii 0b01w
    || InstrSet_Jazelle ->
         write_isetstate ii 0b10w
    || InstrSet_ThumbEE ->
         write_isetstate ii 0b11w`;

val RBankSelect_def = Define`
  RBankSelect (ii:iiid) (mode, usr, fiq, irq, svc, abt, und, mon) : RName M =
    seqT (bad_mode ii mode)
    (\bad_mode.
       if bad_mode then
         errorT "RBankSelect: unpredictable"
       else
         constT
           ((case mode
             of 0b10000w -> usr  (* User mode *)
             || 0b10001w -> fiq  (* FIQ mode *)
             || 0b10010w -> irq  (* IRQ mode *)
             || 0b10011w -> svc  (* Supervisor mode *)
             || 0b10110w -> mon  (* Monitor mode *)
             || 0b10111w -> abt  (* Abort mode *)
             || 0b11011w -> und  (* Undefined mode *)
             || 0b11111w -> usr  (* System mode uses User mode registers *))))`;

val RfiqBankSelect_def = Define`
  RfiqBankSelect ii (mode, usr, fiq) =
    RBankSelect ii (mode, usr, fiq, usr, usr, usr, usr, usr)`;

val LookUpRName_def = Define`
  LookUpRName (ii:iiid) (n:word4, mode) =
     case n
     of 0w  -> constT RName_0usr
     || 1w  -> constT RName_1usr
     || 2w  -> constT RName_2usr
     || 3w  -> constT RName_3usr
     || 4w  -> constT RName_4usr
     || 5w  -> constT RName_5usr
     || 6w  -> constT RName_6usr
     || 7w  -> constT RName_7usr
     || 8w  -> RfiqBankSelect ii (mode, RName_8usr, RName_8fiq)
     || 9w  -> RfiqBankSelect ii (mode, RName_9usr, RName_9fiq)
     || 10w -> RfiqBankSelect ii (mode, RName_10usr, RName_10fiq)
     || 11w -> RfiqBankSelect ii (mode, RName_11usr, RName_11fiq)
     || 12w -> RfiqBankSelect ii (mode, RName_12usr, RName_12fiq)
     || 13w -> RBankSelect ii
                 (mode, RName_SPusr, RName_SPfiq, RName_SPirq,
                  RName_SPsvc, RName_SPabt, RName_SPund, RName_SPmon)
     || 14w -> RBankSelect ii
                 (mode, RName_LRusr, RName_LRfiq, RName_LRirq,
                  RName_LRsvc, RName_LRabt, RName_LRund, RName_LRmon)
     || _ -> errorT "LookUpRName: n = 15w"`;

val read_reg_mode_def = Define`
  read_reg_mode ii (n, mode) =
    seqT (parT (is_secure ii) (read_nsacr ii))
    (\(is_secure,nsacr).
        if (n = 15w) \/ ~is_secure /\
             ((mode = 0b10110w) \/ (mode = 0b10001w) /\ nsacr.RFR)
        then
          errorT "read_reg_mode: unpredictable"
        else
          seqT
            (LookUpRName ii (n, mode))
            (\rname. read__reg ii rname))`;

val write_reg_mode_def = Define`
  write_reg_mode ii (n, mode) value =
    seqT (parT (is_secure ii)
             (parT (read_nsacr ii)
                       (current_instr_set ii)))
    (\(is_secure,nsacr,current_instr_set).
        if (n = 15w) \/
           ~is_secure /\
             ((mode = 0b10110w) \/
              (mode = 0b10001w) /\ nsacr.RFR) \/
           (n = 13w) /\ ~aligned(value,4) /\ (current_instr_set <> InstrSet_ARM)
        then
          errorT "write_reg_mode: unpredictable"
        else
          seqT (LookUpRName ii (n, mode))
          (\rname. write__reg ii rname value))`;

val read_pc_def = Define `read_pc ii = read__reg ii RName_PC`;

val pc_store_value_def = Define`
  pc_store_value ii =
    seqT (read_pc ii)
    (\pc. constT (pc + 8w))`;

val read_reg_def = Define`
  read_reg (ii:iiid) n =
    if n = 15w then
      seqT (parT (read_pc ii) (current_instr_set ii))
      (\(pc,current_instr_set).
         constT
           (if current_instr_set = InstrSet_ARM then
              pc + 8w
            else
              pc + 4w))
     else
       seqT (read_cpsr ii)
       (\cpsr. read_reg_mode ii (n,cpsr.M))`;

val write_reg_def = Define`
  write_reg (ii:iiid) n value =
    if n = 15w then
      errorT "write_reg: assert"
    else
      seqT (read_cpsr ii)
       (\cpsr. write_reg_mode ii (n,cpsr.M) value)`;

val branch_to_def = Define`
  branch_to ii (address:word32) =
    write__reg ii RName_PC address`;

val increment_pc_def = Define`
  increment_pc ii enc =
    seqT (read_pc ii)
    (\pc. branch_to ii (pc + if enc = Encoding_Thumb then 2w else 4w))`;

val big_endian_def = Define`
  big_endian (ii:iiid) =
    seqT (read_cpsr ii) (\cpsr. constT (cpsr.E))`;

(* A basic memory address translation *)

val translate_address_def = Define`
  translate_address
     (address : word32, ispriv : bool, iswrite : bool) : AddressDescriptor M =
    constT
      (<| memattrs := <|
           type           := MemType_Normal;
           innerattrs     := 0w; (* Non-cacheable *)
           outerattrs     := 0w; (* Non-cacheable *)
           shareable      := T;
           outershareable := T |>;
          paddress := address |>)`;

val read_monitor_def = Define`
  read_monitor (ii:iiid) = readT arm_state_monitors`;

val write_monitor_def = Define`
  write_monitor (ii:iiid) d = writeT (\s. s with monitors := d)`;

val read_mem1_def = Define`
  read_mem1 (ii:iiid) (address:FullAddress) : word8 M =
    seqT (writeT (arm_state_accesses_fupd (CONS (MEM_READ address))))
         (\u:unit. readT (\s. s.memory address))`;

val write_mem1_def = Define`
  write_mem1 (ii:iiid) (address:FullAddress) (byte:word8) =
    seqT (writeT (arm_state_accesses_fupd (CONS (MEM_WRITE address byte))))
         (\u:unit. writeT (arm_state_memory_fupd (address =+ byte)))`;

(* aligned, atomic, little-endian memory access - read *)

val read_mem_def = Define`
  read_mem (ii:iiid)
    (memaddrdesc:AddressDescriptor, size:num) : (word8 list) M =
   if size NOTIN {1; 2; 4; 8} then
     errorT "read_mem: size is not 1, 2, 4 or 8"
   else let address = memaddrdesc.paddress in
     forT 0 (size - 1)
       (\i. read_mem1 ii (address + n2w i))`;

(* aligned, atomic, little-endian memory access - write *)

val write_mem_def = Define`
  write_mem (ii:iiid)
    (memaddrdesc:AddressDescriptor, size:num) (value:word8 list) : unit M =
   if  size NOTIN {1; 2; 4; 8} then
     errorT "write_mem: size is not 1, 2, 4 or 8"
   else if LENGTH value <> size then
     errorT "write_mem: value has wrong size"
   else let address = memaddrdesc.paddress in
     seqT
       (forT 0 (size - 1)
          (\i. write_mem1 ii (address + n2w i) (EL i value)))
       (\l. constT ())`;

val read_memA_with_priv_def = Define`
  read_memA_with_priv (ii:iiid) (address:word32, size:num, priveledged:bool) =
    seqT
      (if aligned(address,size) then
         constT address
       else
         seqT (read_sctlr ii)
         (\sctlr.
            if sctlr.A \/ sctlr.U then
              errorT "read_memA_with_priv: DAbort_Alignment"
            else
              constT (align(address,size))))
      (\VA.
        seqT (translate_address(VA, priveledged, F))
        (\memaddrdesc.
          seqT (read_mem ii (memaddrdesc, size))
          (\value.
             seqT
                (big_endian ii)
                (\E. constT (if E then REVERSE value else value)))))`;

val write_memA_with_priv_def = Define`
  write_memA_with_priv (ii:iiid)
     (address:word32, size:num, priveledged:bool) (value:word8 list) =
    seqT
      (if aligned(address,size) then
         constT address
       else
         seqT (read_sctlr ii)
         (\sctlr.
            if sctlr.A \/ sctlr.U then
              errorT "write_memA_with_priv: DAbort_Alignment"
            else
              constT (align(address,size))))
      (\VA.
        seqT (translate_address(VA, priveledged, T))
        (\memaddrdesc.
           seqT
           (if memaddrdesc.memattrs.shareable then
              seqT
                (read_monitor ii)
                (\monitor.
                   write_monitor ii
                     (monitor with
                      state := SND (monitor.ClearExclusiveByAddress
                                (memaddrdesc.paddress,ii,size) monitor.state)))
            else
              constT ())
           (\u.
             seqT
               (seqT (big_endian ii)
                  (\E. constT (if E then REVERSE value else value)))
               (\value. write_mem ii (memaddrdesc,size) value))))`;

val read_memU_with_priv_def = Define`
  read_memU_with_priv (ii:iiid) (address:word32, size:num, priveledged:bool) =
    seqT (read_sctlr ii)
    (\sctlr.
       seqT
         (if ~sctlr.A /\ ~sctlr.U then
            constT (align(address,size))
          else
            constT (address))
       (\address.
          if aligned(address,size) then
            read_memA_with_priv ii (address,size,priveledged)
          else if sctlr.A then
            errorT "read_memU_with_priv: DAbort_Alignment"
          else
            seqT
              (forT 0 (size - 1)
                 (\i. read_memA_with_priv ii (address + n2w i,1,priveledged)))
              (\values. let value = FLAT values in
                seqT
                  (big_endian ii)
                  (\E. constT (if E then REVERSE value else value)))))`;

val write_memU_with_priv_def = Define`
  write_memU_with_priv (ii:iiid)
    (address:word32, size:num, priveledged:bool) (value:word8 list) =
    seqT (read_sctlr ii)
    (\sctlr.
       seqT
         (if ~sctlr.A /\ ~sctlr.U then
            constT (align(address,size))
          else
            constT (address))
       (\address.
          if aligned(address,size) then
            write_memA_with_priv ii (address,size,priveledged) value
          else if sctlr.A then
            errorT "write_memU_with_priv: DAbort_Alignment"
          else
            seqT
              (seqT (big_endian ii)
                 (\E. constT (if E then REVERSE value else value)))
              (\value.
                 seqT
                   (forT 0 (size - 1)
                      (\i. write_memA_with_priv ii
                             (address + n2w i,1,priveledged) [EL i value]))
                   (\u. constT ()))))`;

val read_memA_def = Define`
  read_memA ii (address:word32, size:num) =
    seqT (current_mode_is_priviledged ii)
      (\priviledged. read_memA_with_priv ii (address,size,priviledged))`;

val write_memA_def = Define`
  write_memA ii (address:word32, size:num) (value:word8 list) =
    seqT (current_mode_is_priviledged ii)
      (\priviledged. write_memA_with_priv ii (address,size,priviledged) value)`;

val read_memA_unpriv_def = Define`
  read_memA_unpriv ii (address:word32, size:num) =
    read_memA_with_priv ii (address,size,F)`;

val write_memA_unpriv_def = Define`
  write_memA_unpriv ii (address:word32, size:num) (value:word8 list) =
    write_memA_with_priv ii (address,size,F) value`;

val read_memU_def = Define`
  read_memU ii (address:word32, size:num) =
    seqT (current_mode_is_priviledged ii)
      (\priviledged. read_memU_with_priv ii (address,size,priviledged))`;

val write_memU_def = Define`
  write_memU ii (address:word32, size:num) (value:word8 list) =
    seqT (current_mode_is_priviledged ii)
      (\priviledged. write_memU_with_priv ii (address,size,priviledged) value)`;

val read_memU_unpriv_def = Define`
  read_memU_unpriv ii (address:word32, size:num) =
    read_memU_with_priv ii (address,size,F)`;

val write_memU_unpriv_def = Define`
  write_memU_unpriv ii (address:word32, size:num) (value:word8 list) =
    write_memU_with_priv ii (address,size,F) value`;

(* hints and event operations *)

val data_memory_barrier_def = Define`
  (data_memory_barrier : iiid -> MBReqDomain # MBReqTypes -> unit M) ii x =
    constT ()`;

val data_synchronization_barrier_def = Define`
  (data_synchronization_barrier :
      iiid -> MBReqDomain # MBReqTypes -> unit M) ii x =
    constT ()`;

val instruction_synchronization_barrier_def = Define`
  (instruction_synchronization_barrier : iiid -> unit M) ii =
    constT ()`;

val hint_yield_def = Define`
  (hint_yield : iiid -> unit M) ii = constT ()`;

val hint_preload_data_for_write_def = Define`
  (hint_preload_data_for_write : iiid -> FullAddress -> unit M) ii x =
    constT ()`;

val hint_preload_data_def = Define`
  (hint_preload_data : iiid -> FullAddress -> unit M) ii x =
    constT ()`;

val hint_preload_instr_def = Define`
  (hint_preload_instr : iiid -> FullAddress -> unit M) ii x =
    constT ()`;

val hint_debug_def = Define`
  (hint_debug : iiid -> word4 -> unit M) ii option = constT ()`;

val clear_event_register_def = Define`
  (clear_event_register : iiid -> unit M) ii =
    writeT (arm_state_event_register_fupd (ii.proc =+ F))`;

val event_registered_def = Define`
  (event_registered : iiid -> bool M) ii =
    readT (\s. s.event_register ii.proc)`;

val send_event_def = Define`
  (send_event : iiid -> unit M) ii =
    writeT (\s. s with event_register := K T)`;

val wait_for_event_def = Define`
  (wait_for_event : iiid -> unit M) ii = constT ()`;

val waiting_for_interrupt_def = Define`
  (waiting_for_interrupt : iiid -> bool M) ii =
    readT (\s. s.interrupt_wait ii.proc)`;

val clear_wait_for_interrupt_def = Define`
  (clear_wait_for_interrupt : iiid -> unit M) ii =
    writeT (arm_state_interrupt_wait_fupd (ii.proc =+ F))`;

val wait_for_interrupt_def = Define`
  (wait_for_interrupt : iiid -> unit M) ii =
    writeT (arm_state_interrupt_wait_fupd (ii.proc =+ T))`;

(* exclusive monitor operations. *)

val set_exclusive_monitors_def = Define`
  (set_exclusive_monitors ii (address:word32,size:num)) : unit M =
  seqT
    (parT (read_cpsr ii) (read_monitor ii))
    (\(cpsr,monitor).
       seqT (translate_address(address, cpsr.M <> 0b10000w, F))
       (\memaddrdesc. let triple = (memaddrdesc.paddress,ii,size) in
         write_monitor ii
           (monitor with
            state :=
              SND ((if memaddrdesc.memattrs.shareable then
                     seqE
                       (monitor.MarkExclusiveGlobal triple)
                       (\u. monitor.MarkExclusiveLocal triple)
                    else
                      monitor.MarkExclusiveLocal triple)
                   monitor.state))))`;

val exclusive_monitors_pass_def = Define`
  (exclusive_monitors_pass ii (address:word32,size:num)) : bool M =
  seqT
    (parT (read_cpsr ii) (read_monitor ii))
    (\(cpsr,monitor).
       if ~aligned(address,size) then
         errorT "exclusive_monitors_pass: alignment fault"
       else
         seqT (translate_address(address, cpsr.M <> 0b10000w, F))
         (\memaddrdesc.
            let triple = (memaddrdesc.paddress,ii,size) in
            let (passed,state') =
              seqE (monitor.IsExclusiveLocal triple)
              (\local_passed.
                seqE
                  (if memaddrdesc.memattrs.shareable then
                     seqE (monitor.IsExclusiveGlobal triple)
                     (\global_passed.
                        constE (local_passed /\ global_passed))
                   else
                     constE local_passed)
                  (\passed.
                      if passed then
                        seqE (monitor.ClearExclusiveLocal ii.proc)
                        (\u. constE passed)
                      else
                        constE passed)) monitor.state
            in
              seqT
                (write_monitor ii (monitor with state := state'))
                (\u. constT passed)))`;

val clear_exclusive_local_def = Define`
  (clear_exclusive_local (ii:iiid)) : unit M =
     seqT (read_monitor ii)
     (\monitor.
        let state' = SND (monitor.ClearExclusiveLocal ii.proc monitor.state)
        in
          write_monitor ii (monitor with state := state'))`;

(* coprocessor operations. *)

val read_coprocessors_def = Define`
  read_coprocessors (ii:iiid) = readT arm_state_coprocessors`;

val write_coprocessors_def = Define`
  write_coprocessors (ii:iiid) d = writeT (\s. s with coprocessors := d)`;

val coproc_accepted_def = Define`
  coproc_accepted (ii:iiid) (inst:CPinstruction) : bool M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let accept = FST (coprocessors.accept inst coprocessors.state) in
         constT accept)`;

val coproc_internal_operation_def = Define`
  coproc_internal_operation (ii:iiid) (inst:CPinstruction) : unit M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let cp_state = SND (coprocessors.internal_op inst coprocessors.state) in
         write_coprocessors ii (coprocessors with state := cp_state))`;

val coproc_send_loaded_words_def = Define`
  coproc_send_loaded_words (ii:iiid)
      (readm:num->word32 M, inst:CPinstruction) : unit M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let count = FST (coprocessors.load_count inst coprocessors.state)
       in
         seqT
           (forT 0 (count - 1) readm)
           (\data.
             let cp_state = SND (coprocessors.load inst data coprocessors.state)
             in
               write_coprocessors ii
                 (coprocessors with state := cp_state)))`;

val coproc_get_words_to_store_def = Define`
  coproc_get_words_to_store (ii:iiid)
      (inst:CPinstruction) : (word32 list) M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let data = FST (coprocessors.store inst coprocessors.state) in
          constT data)`;

val coproc_send_one_word_def = Define`
  coproc_send_one_word (ii:iiid)
      (data:word32, inst:CPinstruction) : unit M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let cp_state = SND (coprocessors.send_one inst data coprocessors.state)
       in
         write_coprocessors ii (coprocessors with state := cp_state))`;

val coproc_get_one_word_def = Define`
  coproc_get_one_word (ii:iiid) (inst:CPinstruction) : word32 M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let data = FST (coprocessors.get_one inst coprocessors.state) in
         constT data)`;

val coproc_send_two_words_def = Define`
  coproc_send_two_words (ii:iiid)
      (data:word32 # word32, inst:CPinstruction) : unit M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let cp_state = SND (coprocessors.send_two inst data coprocessors.state)
       in
         write_coprocessors ii (coprocessors with state := cp_state))`;

val coproc_get_two_words_def = Define`
  coproc_get_two_words (ii:iiid) (inst:CPinstruction) : (word32#word32) M =
    seqT (read_coprocessors ii)
    (\coprocessors.
       let data = FST (coprocessors.get_two inst coprocessors.state) in
         constT data)`;

val _ = export_theory ();
