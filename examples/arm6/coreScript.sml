(* app load ["onestepTheory","word32Theory","armTheory"]; *)
open HolKernel boolLib Q bossLib Parse arithmeticTheory
     onestepTheory word32Theory armTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "core";

(* -------------------------------------------------------- *)

val _ = Hol_datatype `iseq = t3 | t4 | t5 | t6`;
val _ = Hol_datatype `dp = DP of reg=>psr=>word32=>word32=>word32=>word32`;
(* reg,psr,areg,din,alua,alub *)
val _ = Hol_datatype
  `ctrl = CTRL of word32=>bool=>word32=>bool=>word32=>bool=>word32=>word32=>bool=>bool=>bool=>
                  iclass=>iseq=>num=>bool=>bool=>word32=>word32=>num`;
(* pipea,pipeaval,pipeb,pipebval,ireg,iregval,apipea,apipeb,ointstart,onewinst,opipebll,
   nxtic,nxtis,aregn,nbw,nrw,sctrlreg,psrfb,oareg *)
val _ = Hol_datatype `state_ARM6 = ARM6 of mem=>dp=>ctrl`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)
(* Pipeline Control *)

(* True if new instruction to be executed on next cycle *)

val NEWINST_def = Define`
  NEWINST ic is intstart = intstart \/ (ic = data_proc) \/ (ic = mrs_msr) \/ 
                           (ic = unexec) \/ (((ic = str) \/ (ic = reg_shift)) /\ (is = t4)) \/
                           (((ic = ldr) \/ (ic = br) \/ (ic = swi_ex)) /\ (is = t5)) \/
                           ((ic = swp) /\ (is = t6))`;

(* undefined instruction, or software interrupt *)

val AREGN1_def = Define`
  AREGN1 intstart = if intstart then 1 else 2`;

(* --------------- *)

val NXTIC_def = Define`
  NXTIC intstart newinst ic ireg =
    if intstart then swi_ex else
      if ~newinst then
         ic
      else
         DECODE_INST (w2n ireg)`;

val NXTIS_def = Define`
  NXTIS ic is newinst =
    if newinst then
       t3
    else if (is = t3) /\ ((ic = reg_shift) \/ (ic = ldr) \/ (ic = str) \/
                          (ic = br) \/ (ic = swi_ex) \/ (ic = swp)) then
       t4
    else if (is = t4) /\ ((ic = ldr) \/ (ic = br) \/ (ic = swi_ex) \/ (ic = swp)) then
       t5
    else if (is = t5) /\ (ic = swp) then
       t6
    else ARB`;

val IC_def = Define`
  IC abortinst nxtic =
    if abortinst then unexec else nxtic`;

val IS_def = Define`
  IS abortinst nxtis =
    if abortinst then t3 else nxtis`;

(* --------------- *)

val INTSEQ_def = Define`
  INTSEQ ic is = (ic = undef) /\ (is = t3)`;

val ABORTINST_def = Define`
  ABORTINST iregval onewinst ointstart ireg n z c v =
    ~iregval \/ (onewinst /\ ~ointstart /\ ~CONDITION_PASSED n z c v (w2n ireg))`;

(* --------------- *)

val PIPEALL_def = Define`
   PIPEALL opipebll = opipebll`;

val PIPEBLL_def = Define`
   PIPEBLL newinst ic =
      newinst \/ (ic = br) \/ (ic = swi_ex)`;

(* --------------- *)

val PIPEAWRITE_def = Define`
   PIPEAWRITE pipeall = pipeall`;

val PIPEBWRITE_def = Define`
   PIPEBWRITE pipebll = pipebll`;

val PIPECWRITE_def = Define`
   PIPECWRITE newinst = newinst`;

(* --------------- *)

val PIPEAVAL_def = Define`
   PIPEAVAL pcchange = ~pcchange`;

val IREGVAL_def = Define`
   IREGVAL pipecval pcchange = pipecval /\ ~pcchange`;

(* --------------- *)

val PIPESTATAWRITE_def = Define`
   PIPESTATAWRITE pipeall pcchange = pipeall \/ pcchange`;

val PIPESTATBWRITE_def = Define`
   PIPESTATBWRITE pipebll pcchange = pipebll \/ pcchange`;

val PIPESTATIREGWRITE_def = Define`
   PIPESTATIREGWRITE newinst pcchange = newinst \/ pcchange`;

(* --------------- *)

val PCCHANGE_def = Define`
  PCCHANGE rwa = let (w,a) = rwa in w /\ (a = 15)`;

val ALIGN_EQ_def = Define`
  ALIGN_EQ a b = (WORD_ALIGN a = WORD_ALIGN b)`;

val PIPECHANGE_def = Define`
  PIPECHANGE areg apipea apipeb =
    (ALIGN_EQ areg apipea) \/ (ALIGN_EQ areg apipeb)`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

(* Memory access on next cycle: Byte (F) or word (T) *)

val NBW_def = Define`
  NBW ic is ireg = ~(WORD_BIT 22 ireg /\
                     ((is = t3) /\ ((ic = ldr) \/ (ic = str) \/ (ic = swp)) \/
                      (is = t4) /\ (ic = swp)))`;

(* Memory access on next cycle: Write (T) or other (F) *)

val NRW_def = Define`
  NRW ic is = (is = t3) /\ (ic = str) \/ (is = t4) /\ (ic = swp)`;

val SCTRLREGWRITE_def = Define`
  SCTRLREGWRITE ic is = (is = t3) /\ (ic = reg_shift)`;

val PSRFBWRITE_def = Define`
  PSRFBWRITE ic is = ~((is = t4) /\ (ic = swi_ex))`;

val ALUAWRITE_def = Define`
  ALUAWRITE ic is = ~((is = t4) /\ ((ic = ldr) \/ (ic = str) \/ (ic = br) \/ (ic = swi_ex)))`;

val ALUBWRITE_def = Define`
  ALUBWRITE ic is = ~((is = t4) /\ ((ic = ldr) \/ (ic = str) \/ (ic = swp)))`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

(* Gives din *)

val DIN_def = Define`
  DIN ic is ireg data =
    if ((ic = ldr) \/ (ic = swp)) /\ (is = t4) then
      data
    else 
      ireg`;

val DINWIRTE_def = Define`
  DINWRITE ic is = ~((ic = swp) /\ (is = t5))`;

(* oareg = WORD_BIT 1 0 areg i.e. alignment bits of previous areg *)
(* Gives din' *)

val FIELD_def = Define`
  FIELD ic is ireg oareg din =
    if is = t3 then
      if ic = br then
         SIGN_EX_OFFSET (WORD_BITS 23 0 din)
      else if (ic = ldr) \/ (ic = str) then
         w32 (WORD_BITS 11 0 din)
      else if (ic = mrs_msr) \/ (ic = data_proc) then
         w32 (WORD_BITS 7 0 din)
      else
         ARB
    else if (is = t5) /\ (ic = ldr) \/ (is = t6) /\ (ic = swp) then
      if ~WORD_BIT 22 ireg then
         din
      else let a = 8 * oareg in
         w32 (WORD_SLICE (a + 7) a din)
    else
       ARB`;

(* sctrlreg = reg[ireg[11:8]] *)
(* Gives alub *)

val SHIFTER_def = Define`
  SHIFTER ic is ireg oareg sctrlreg busb c =
    let bit25 = WORD_BIT 25 ireg
    and bits117 = WORD_BITS 11 7 ireg
    and bits65 = WORD_BITS 6 5 ireg in
    let bits118 = bits117 DIV 2 in
      if is = t3 then
        if bit25 /\ ((ic = data_proc) \/ (ic = mrs_msr)) then
          ROR busb (2 * bits118) c
        else if (ic = swp) \/ ~bit25 /\ ((ic = ldr) \/ (ic = str) \/ (ic = mrs_msr)) then
          LSL busb 0 c
        else if (~bit25 /\ (ic = data_proc)) \/ (bit25 /\ ((ic = ldr) \/ (ic = str))) then
          SHIFT_IMMEDIATE2 bits117 bits65 busb c
        else if ic = br then
          LSL busb 2 c
        else
          ARB
      else if (is = t4) /\ (ic = reg_shift) then
        SHIFT_REGISTER2 (WORD_BITS 7 0 sctrlreg) bits65 busb c
      else if (is = t5) /\ (ic = ldr) \/ (is = t6) /\ (ic = swp) then
        ROR busb (8 * oareg) c
      else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
        LSL busb 0 c
      else
        ARB`;
       
(* -------------------------------------------------------- *)

(* Register bus B address *)

val RBA_def = Define`
  RBA ic is ireg =
    if (is = t3) /\ ((ic = data_proc) \/ (ic = mrs_msr) \/ (ic = ldr) \/ (ic = str)) \/
       (is = t4) /\ (ic = reg_shift) \/
       (is = t5) /\ (ic = swp) then
       WORD_BITS 3 0 ireg
    else if (is = t3) /\ (ic = swp) then
       WORD_BITS 19 16 ireg
    else if (is = t4) /\ (ic = str) then
       WORD_BITS 15 12 ireg
    else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
       14
    else ARB`;

(* Register bus A address *)

val RAA_def = Define`
  RAA ic is ireg =
    if is = t3 then
       if (ic = data_proc) \/ (ic = ldr) \/ (ic = str) then
         WORD_BITS 19 16 ireg
       else if ic = reg_shift then
         WORD_BITS 11 8 ireg
       else if (ic = br) \/ (ic = swi_ex) then
         15
       else ARB
    else if (is = t4) /\ (ic = reg_shift) then
       WORD_BITS 19 16 ireg
    else ARB`;
      

(* Register write address *)

val RWA_def = Define`
  RWA ic is ireg =
    let bit21 = WORD_BIT 21 ireg
    and bit23 = WORD_BIT 23 ireg
    and bit24 = WORD_BIT 24 ireg in
      if ((is = t3) /\ (ic = data_proc) \/
          (is = t4) /\ (ic = reg_shift)) /\ (~bit24 \/ bit23) \/
         (is = t3) /\ (ic = mrs_msr) /\ ~bit21 \/
         (is = t5) /\ (ic = ldr) \/
         (is = t6) /\ (ic = swp) then
         (T,WORD_BITS 15 12 ireg)
      else if (is = t4) /\ ((ic = ldr) \/ (ic = str)) /\ (~bit24 \/ bit21) then
         (T,WORD_BITS 19 16 ireg)
      else if ((is = t4) \/ (is = t5)) /\ (((ic = br) /\ bit24) \/ (ic = swi_ex)) then
         (T,14)
      else (F,ARB)`;

(* True if pc is to be updated by incrementor *)

val PCWA_def = Define`
  PCWA ic is ireg =
    let bits2423 = WORD_BITS 24 23 ireg
    and bit21    = WORD_BIT 21 ireg
    and bits1512 = WORD_BITS 15 12 ireg in
      ((is = t3) /\ ~(((ic = data_proc) /\ ~(bits2423 = 2) /\ (bits1512 = 15)) \/
            ((ic = mrs_msr) /\ ~bit21 /\ (bits1512 = 15)) \/ (ic = undef))) \/
      (ic = br) \/ (ic = swi_ex)`;

(* PSR read address *)

val PSRA_def = Define`
  PSRA ic is ireg =
    let bit22 = WORD_BIT 22 ireg
    and bit20 = WORD_BIT 20 ireg in
      ((is = t3) /\ ((ic = swi_ex) \/ (~bit22 /\ ((ic = mrs_msr) \/ ((ic = data_proc) /\ ~bit20))))) \/
      ((is = t4) /\ ~bit22 /\ (ic = reg_shift) /\ ~bit20)`;

(* PSR write address *)
val PSRWA_def = Define`
  PSRWA ic is ireg nbs =
    let bit22 = WORD_BIT 22 ireg
    and bit21 = WORD_BIT 21 ireg
    and bit20 = WORD_BIT 20 ireg
    and bit19 = WORD_BIT 19 ireg
    and bit16 = WORD_BIT 16 ireg in
      if bit20 /\ (((is = t3) /\ (ic = data_proc)) \/ ((is = t4) /\ (ic = reg_shift))) \/
         (is = t3) /\ (ic = swi_ex) then
         (T,T)
      else if (is = t3) /\ (ic = mrs_msr) then
         if ~bit21 \/ (~bit19 /\ ~bit16) \/
            (USER nbs /\ (bit22 \/ (~bit19 /\ bit16))) then
            (F,ARB)
         else
            (T,~bit22)
      else if (is = t4) /\ (ic = swi_ex) then
         (T,F)
      else
         (F,ARB)`;
            
val ALUOUT_def = Define`
  ALUOUT (n,z,c,v,res) = res`;

val NZCV_def = Define`
  NZCV (n,z,c,v,res) = (n,z,c,v)`;

(* sctlc = shcout = FST (SHIFTER ...) *)
(* PSR write bus *)
val PSRDAT_def = Define`
  PSRDAT ic is ireg nbs aregn cpsrl psrfb alu sctlc =
    let bit24 = WORD_BIT 24 ireg
    and bit23 = WORD_BIT 23 ireg
    and bit22 = WORD_BIT 22 ireg
    and bit21 = WORD_BIT 21 ireg
    and bit20 = WORD_BIT 20 ireg
    and bit19 = WORD_BIT 19 ireg
    and bit16 = WORD_BIT 16 ireg
    and bits1512 = WORD_BITS 15 12 ireg
    in
      if bit20 /\ (((is = t3) /\ (ic = data_proc)) \/ ((is = t4) /\ (ic = reg_shift))) then
         if bits1512 = 15 then
            if USER nbs then
               cpsrl
            else
               psrfb
         else let (n,z,c,v) = NZCV alu in
            if (~bit23 /\ ~bit22) \/ (bit24 /\ bit23) then
               SET_NZC n z sctlc cpsrl
            else
               SET_NZCV n z c v cpsrl
      else if (is = t3) /\ (ic = mrs_msr) then
        let aluout = ALUOUT alu in
         if USER nbs then
            if ~bit22 /\ bit19 then
               w32 (WORD_SLICE 31 28 aluout + WORD_BITS 27 0 psrfb)
            else
               ARB
         else
            if bit19 then
               if bit16 then
                  w32 (WORD_SLICE 31 28 aluout + WORD_SLICE 27 8 psrfb + WORD_BITS 7 0 aluout)
               else
                  w32 (WORD_SLICE 31 28 aluout + WORD_BITS 27 0 psrfb)
            else
               if bit16 then
                  w32 (WORD_SLICE 31 8 psrfb + WORD_BITS 7 0 aluout)
               else
                  ARB
      else if (is = t3) /\ (ic = swi_ex) then
         SET_IFMODE T (if (aregn = 0) \/ (aregn = 7) then T else WORD_BIT 6 cpsrl)
                    (exception2mode (num2exception aregn)) cpsrl
      else if (is = t4) /\ (ic = swi_ex) then
         psrfb
      else
         ARB`;

val BUSA_def = Define`
  BUSA ic is psrrd ra =
    if is = t3 then
      if ic = mrs_msr then
        psrrd
      else
        if (ic = data_proc) \/ (ic = ldr) \/ (ic = str) \/ (ic = br) \/ (ic = swi_ex) then
          ra
        else
          ARB
    else if (is = t4) /\ (ic = reg_shift) then
       ra
    else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
       w32 3
    else
       ARB`;

val BUSB_def = Define`
  BUSB ic is ireg din' rb =
    let bit25 = WORD_BIT 25 ireg in
      if (is = t3) /\
         ((ic = br) \/ (bit25 /\ ((ic = data_proc) \/ (ic = mrs_msr))) \/
                      (~bit25 /\ ((ic = ldr) \/ (ic = str)))) \/
         (is = t5) /\ (ic = ldr) \/ (is = t6) /\ (ic = swp) then
         din'
      else
         rb`;

(* -------------------------------------------------------- *)

(* aregn is vector address for exception/interrupt *)

val AREG_def = Define`
  AREG ic is ireg aregn inc reg15 aluout =
    let bits1916 = WORD_BITS 19 16 ireg
    and bits1512 = WORD_BITS 15 12 ireg
    and bit21 = WORD_BIT 21 ireg
    and bit23 = WORD_BIT 23 ireg
    and bit24 = WORD_BIT 24 ireg
    in
    if (is = t4) /\ (ic = reg_shift)  then
      if (~bit24 \/ bit23) /\ (bits1512 = 15) then
        aluout
      else
        reg15
    else if (is = t4) /\ ((ic = ldr) \/ (ic = str)) then
      if (~bit24 \/ bit21) /\ (bits1916 = 15) then
        aluout
      else
        reg15
    else if (is = t5) /\ (ic = ldr) \/
            (is = t6) /\ (ic = swp) then
      if bits1512 = 15 then
        aluout
      else
        reg15
    else if (is = t3) /\ ((ic = data_proc) /\ (~bit24 \/ bit23) /\ (bits1512 = 15) \/
                          (ic = mrs_msr) /\ ~bit21 /\ (bits1512 = 15) \/
                          (ic = ldr) \/ (ic = str) \/ (ic = br)) \/ (ic = swp) then
        aluout
    else if (is = t3) /\ (ic = swi_ex) then
      w32 (aregn * 4)
    else
      inc`;

(* -------------------------------------------------------- *)

val ALU6_def = Define`
 ALU6 ic is ireg alua alub c =
  let opc = WORD_BITS 24 21 ireg in
   if ((ic = data_proc) /\ (is = t3)) \/
      ((ic = reg_shift) /\ (is = t4)) then
     ALU opc alua alub c
   else if (ic = mrs_msr) /\ (is = t3) then
     ALU_logic (if BIT 0 opc then alub else alua)
   else if (ic = ldr) \/ (ic = str) then
     let P = BIT 3 opc and U = BIT 2 opc in
       if (is = t3) /\ ~P then
         ALU_logic alua
       else if (is = t3) \/ (is = t4) then
         if U then ADD alua alub F else SUB alua alub T
       else if (is = t5) /\ (ic = ldr) then
         ALU_logic alub
       else
         ARB
   else if (is = t3) /\ (ic = br) then
     ADD alua alub F
   else if (ic = br) \/ (ic = swi_ex) then
     if is = t4 then ALU_logic alua         else
     if is = t5 then ADD (NOT alua) alub F  else ARB
   else if ic = swp then
     ALU_logic alub
   else ARB`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val REG_READ6_def = Define`
  REG_READ6 reg mode n =
    if n = 15 then
      FETCH_PC reg
    else REG_READ reg mode n`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val NEXT_ARM6_def = Define`
   NEXT_ARM6 (ARM6 mem (DP reg psr areg din alua alub)
          (CTRL pipea pipeaval pipeb pipebval ireg iregval apipea apipeb
                ointstart onewinst opipebll nxtic nxtis aregn nbw nrw sctrlreg psrfb oareg)) =
     let cpsr = CPSR_READ psr
     in
     let (n,z,c,v,nbs) = DECODE_PSR cpsr
     in
     let abortinst = ABORTINST iregval onewinst ointstart ireg n z c v
     in
     let ic = IC abortinst nxtic
     and is = IS abortinst nxtis
     in
     let pcwa = PCWA ic is ireg     (* PC write *)
     and rwa = RWA ic is ireg       (* Register write address *)
     in
     let intseq = INTSEQ ic is
     and pcchange = PCCHANGE rwa
     in
     let newinst = NEWINST ic is intseq
     in
     let pipeall = PIPEALL opipebll
     and pipebll = PIPEBLL newinst ic
     and pipec = if PIPECWRITE newinst then pipeb else ireg
     and pipecval = pipebval
     in
     let psrrd = if PSRA ic is ireg then cpsr else SPSR_READ psr nbs
     in
     let psrfb' = if PSRFBWRITE ic is then psrrd else psrfb
     in
     let raa = RAA ic is ireg
     and rba = RBA ic is ireg
     in
     let ra = REG_READ6 reg nbs raa
     and rb = REG_READ6 reg nbs rba
     and din' = FIELD ic is ireg oareg din
     in
     let busa = BUSA ic is psrrd ra
     and busb = BUSB ic is ireg din' rb
     and sctrlreg' = if SCTRLREGWRITE ic is then ra else sctrlreg
     in
     let shifter = SHIFTER ic is ireg oareg sctrlreg busb c
     in
     let shcout = FST shifter
     and shout = SND shifter
     in
     let alua' = if ALUAWRITE ic is then busa else alua
     and alub' = if ALUBWRITE ic is then shout else alub
     in
     let alu = ALU6 ic is ireg alua' alub' c
     in
     let aluout = ALUOUT alu
     and inc = areg + w32 4
     and pcbus = REG_READ6 reg usr 15
     and psrwa = PSRWA ic is ireg nbs
     in
     let psrdat = PSRDAT ic is ireg nbs aregn cpsr psrfb' alu shcout
     and data = if nrw then ARB else MEMREAD mem areg
     in
     let mem' = if nrw /\ (pcchange \/ ~PIPECHANGE areg apipea apipeb)
                   then MEM_WRITE (~nbw) mem busb areg else mem
     and reg' = if pcwa then REG_WRITE reg nbs 15 inc else reg
     and psr' = if FST psrwa then
                   if SND psrwa then CPSR_WRITE psr psrdat else SPSR_WRITE psr nbs psrdat
                else psr
     in
     let reg'' = if FST rwa then REG_WRITE reg' nbs (SND rwa) aluout else reg'
     in
     let oareg' = WORD_BITS 1 0 areg
     and areg' = AREG ic is ireg aregn inc pcbus aluout
     and pipea' = if PIPEAWRITE pipeall then data else pipea
     and apipea' = if PIPEAWRITE pipeall then areg else apipea
     in
     let pipeb' = if PIPEBWRITE pipebll then pipea' else pipeb
     and apipeb' = if PIPEBWRITE pipebll then apipea' else apipeb
     and pipeaval' = if PIPESTATAWRITE pipeall pcchange then PIPEAVAL pcchange else pipeaval
     in
     let pipebval' = if PIPESTATBWRITE pipebll pcchange then pipeaval' else pipebval
     and iregval' = if PIPESTATIREGWRITE newinst pcchange then IREGVAL pipecval pcchange
                                                          else iregval
     in
     let nxtic' = NXTIC intseq newinst ic pipec
     and nxtis' = NXTIS ic is newinst
     and nxtdin = if DINWRITE ic is then DIN ic is pipec data else din
     in
     let aregn' = AREGN1 intseq
     and nbw'  = NBW ic is ireg      (* Word access on next cycle *)
     and nrw'  = NRW ic is           (* Mem write on next cycle *)
     in
   ARM6 mem' (DP reg'' psr' areg' nxtdin alua' alub')
        (CTRL pipea' pipeaval' pipeb' pipebval' pipec iregval' apipea' apipeb'
              intseq newinst pipebll nxtic' nxtis' aregn' nbw' nrw' sctrlreg' psrfb' oareg')`;

(* --------------- *)

val INIT_ARM6_def = Define`
   INIT_ARM6 (ARM6 mem (DP reg psr areg din alua alub)
          (CTRL pipea pipeaval pipeb pipebval ireg iregval apipea apipeb
                 ointstart onewinst opipebll nxtic nxtis aregn nbw nrw sctrlreg psrfb oareg)) =
    let pc = REG_READ6 reg usr 15
    in
    let apipeb' = pc - w32 4
    in
    let pipeb' = MEMREAD mem apipeb'
    and ireg'  = MEMREAD mem (pc - w32 8)
    in
  ARM6 mem (DP reg psr pc ireg' alua alub)
       (CTRL pipeb' T pipeb' T ireg' T apipeb' apipeb' F T T
         (NXTIC F T nxtic ireg') t3 (AREGN1 F) nbw F sctrlreg psrfb oareg)`;

(* --------------- *)

val STATE_ARM6_def = Define`
  (STATE_ARM6 0 a = INIT_ARM6 a) /\
  (STATE_ARM6 (SUC t) a = NEXT_ARM6 (STATE_ARM6 t a))`;
 
(* -------------------------------------------------------- *)

val SUB8_PC_def = Define `SUB8_PC reg = SUBST reg (r15,reg r15 - w32 8)`;
val ADD8_PC_def = Define `ADD8_PC reg = SUBST reg (r15,reg r15 + w32 8)`;

val ABS_ARM6_def = Define`
   ABS_ARM6 (ARM6 mem (DP reg psr areg din alua alub) ctrl) = ARM mem (SUB8_PC reg) psr`;

val DUR_ARM6_def = Define`
   DUR_ARM6 (ARM6 mem (DP reg psr areg din alua alub)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval apipea apipeb
               ointstart onewinst opipebll nxtic nxtis aregn nbw nrw sctrlreg psrfb oareg)) =
     let (n,z,c,v,nbs) = DECODE_PSR (CPSR_READ psr) in
     let abortinst = ABORTINST iregval onewinst ointstart ireg n z c v in
     let ic = IC abortinst nxtic in
     let pcchange = PCCHANGE (RWA ic t3 ireg)
     in
     if ic = undef then
       4
     else
       if (ic = mrs_msr) \/ (ic = data_proc) then
         if pcchange then 3 else 1
       else
         if ic = reg_shift then
            if (WORD_BITS 15 12 ireg = 15) /\ (~(WORD_BIT 24 ireg) \/ WORD_BIT 23 ireg) then 4 else 2
         else
            if ic = ldr then
               if (WORD_BITS 15 12 ireg = 15) \/
                  (WORD_BITS 19 16 ireg = 15) /\ (~(WORD_BIT 24 ireg) \/ WORD_BIT 21 ireg) then 5 else 3
            else
               if ic = str then
                  if (WORD_BITS 19 16 ireg = 15) /\ (~(WORD_BIT 24 ireg) \/ WORD_BIT 21 ireg) then 4 else 2
               else
                  if (ic = br) \/ (ic = swi_ex) then
                     3
                   else 
                      if ic = swp then
                        if WORD_BITS 15 12 ireg = 15 then 6 else 4
                      else (* unexec *)
                        1`;

val IMM_ARM6_def = Define`
  (IMM_ARM6 a 0 = 0) /\
  (IMM_ARM6 a (SUC t) = DUR_ARM6 (STATE_ARM6 (IMM_ARM6 a t) a) + IMM_ARM6 a t)`;

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val STATE_ARM6_THM = store_thm("STATE_ARM6_THM",
  `IMAP STATE_ARM6 INIT_ARM6 NEXT_ARM6`,
  PROVE_TAC [STATE_ARM6_def,IMAP_def]
);

val STATE_ARM6_IMAP = store_thm("STATE_ARM6_IMAP",
  `IS_IMAP STATE_ARM6`,
  PROVE_TAC [STATE_ARM6_THM,IS_IMAP_def]
);

fun T_MINUS_ONE th =
  REPEAT STRIP_TAC
    THEN Cases_on `t = 0`
    THEN ASM_SIMP_TAC std_ss [th]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN IMP_RES_TAC LESS_ADD_1
    THEN `t = SUC p` by RW_TAC arith_ss []
    THEN ASM_SIMP_TAC arith_ss [th];

val STATE_ARM6_COR = store_thm("STATE_ARM6_COR",
  `!t a. STATE_ARM6 t a = FUNPOW NEXT_ARM6 t (INIT_ARM6 a)`,
  RW_TAC std_ss [STATE_ARM6_THM,STATE_FUNPOW_LEMMA]
);

val IMM_ARM6_COR = store_thm("IMM_ARM6_COR",
  `IMM_ARM6 a t = if t = 0 then 0 else
                  let tm1 = IMM_ARM6 a (t-1) in
                     DUR_ARM6 (STATE_ARM6 tm1 a) + tm1`,
  SIMP_TAC std_ss []
    THEN T_MINUS_ONE IMM_ARM6_def
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val _ = export_theory();
