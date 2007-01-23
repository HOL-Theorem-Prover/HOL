(* ========================================================================= *)
(* FILE          : coreScript.sml                                            *)
(* DESCRIPTION   : Model of the ARM6 micro-architecture                      *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["armTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q io_onestepTheory armTheory;

val _ = new_theory "core";

(* ------------------------------------------------------------------------- *)
(* The State Space --------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `iseq = t3 | t4 | t5 | t6 | tn | tm`;

val _ = Hol_datatype
  `dp = DP of reg=>psr=>word32=>word32=>word32=>word32=>word32`;

val _ = Hol_datatype
  `ctrl = CTRL of word32=>bool=>word32=>bool=>word32=>bool=>bool=>bool=>
                  bool=>bool=>bool=>iclass=>iseq=>bool=>bool=>bool=>bool=>
                  bool=>bool=>bool=>bool=>bool=>bool=>bool=>word3=>bool=>
                  bool=>bool=>word32=>word32=>word2=>word16=>word4=>word4=>
                  word2=>word32=>bool=>word5`;

val _ = Hol_datatype `state_arm6 = ARM6 of dp=>ctrl`;

val arm6state = ``ARM6 (DP reg psr areg din alua alub dout)
  (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst
        obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq ooonfq
        oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2 nbw nrw
        sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift)``;

(* ......................................................................... *)

val Rg = inst [alpha |-> ``:32``, beta |-> ``:4``] ``$><``;

val CLEARBIT_def = Define `CLEARBIT x = word_modify (\i b. ~(i = x) /\ b)`;
val LEASTBIT_def = Define `LEASTBIT n = LEAST b. n %% b`;

val REG_READ6_def = Define`
  REG_READ6 reg mode n =
    if n = 15w then
      FETCH_PC reg
    else
      REG_READ reg mode n`;

(* ------------------------------------------------------------------------- *)
(* Data Path Control: Instruction Fetch Phase 1 ---------------------------- *)
(* ------------------------------------------------------------------------- *)

val NMREQ_def = Define`
  NMREQ ic is pencz mulx cpb =
    (is = t3) /\ ((ic = reg_shift) \/ (ic = mla_mul) \/ (ic = mcr) \/
                 ((ic = cdp_und) \/ (ic = ldc) \/ (ic = stc)) /\ cpb) \/
    (is = t4) /\ (ic = ldr) \/
    (is = t5) /\ (ic = swp) \/
    (is = tn) /\ (ic = mla_mul) /\ ~mulx \/
    ~(is = t3) /\ ~(is = tm) /\ (ic = ldm) /\ pencz \/
    ~(is = t5) /\ (ic = mrc)`;

(* True if pc is to be updated by incrementor *)

val PCWA_def = Define`
  PCWA ic is ireg cpb =
    let bit24 = ireg %% 24
    and bit23 = ireg %% 23
    and bit21 = ireg %% 21
    and bits1512 = ^Rg 15 12 ireg in
      (is = t3) /\
        ~((ic = data_proc) /\ (~bit24 \/ bit23) /\ (bits1512 = 15w) \/
          (ic = mrs_msr) /\ ~bit21 /\ (bits1512 = 15w) \/
          (((ic = cdp_und) \/ (ic = mcr) \/ (ic = mrc) \/
          (ic = ldc) \/ (ic = stc)) /\ cpb)) \/
      (ic = br) \/ (ic = swi_ex)`;

(* ------------------------------------------------------------------------- *)
(* Data Path Control: Instruction Fetch Phase 2 ---------------------------- *)
(* ------------------------------------------------------------------------- *)

(* Memory access on next cycle: Byte (F) or word (T) *)

val NBW_def = Define`
  NBW ic is (ireg:word32) =
    ~(ireg %% 22 /\
      ((is = t3) /\ ((ic = ldr) \/ (ic = str) \/ (ic = swp)) \/
      (is = t4) /\ (ic = swp)))`;

val NOPC_def = Define`
  NOPC ic is pencz cpb =
    ((ic = ldr) \/ (ic = str) \/ (ic = swp)) /\ (is = t3) \/
    ((ic = ldc) \/ (ic = stc)) /\ ~cpb \/
    (ic = swp) /\ (is = t4) \/
    (ic = ldm) /\ ~(is  = tm) /\ ~pencz \/
    (ic = stm) /\ ~pencz`;

(* Memory access on next cycle: Write (T) or other (F) *)

val NRW_def = Define`
  NRW ic is pencz cpb =
    (is = t3) /\ ((ic = str) \/ (ic = mcr) /\ ~cpb) \/
    (is = t4) /\ (ic = swp) \/
    (ic = stc) /\ ~cpb \/
    (ic = stm) /\ ~pencz`;

val AREG_def = Define`
  AREG ic is ireg (aregn:word3) (inc:word32) reg15 aluout (list:word16)
       pencz (oorp:word4) cpb dataabt =
    let bits1916 = ^Rg 19 16 ireg
    and bits1512 = ^Rg 15 12 ireg
    and bit21 = ireg %% 21
    and bit23 = ireg %% 23
    and bit24 = ireg %% 24
    in
    if (is = t4) /\ (ic = reg_shift)  then
      if (~bit24 \/ bit23) /\ (bits1512 = 15w) then
        aluout
      else
        reg15
    else if (is = t4) /\ ((ic = ldr) \/ (ic = str)) then
      if (~bit24 \/ bit21) /\ (bits1916 = 15w) then
        aluout
      else
        reg15
    else if (is = t5) /\ (ic = ldr) \/
            (is = t6) /\ (ic = swp) then
      if (bits1512 = 15w) /\ ~dataabt then
        aluout
      else
        reg15
    else if (is = tm) /\ (ic = ldm) then
      if (oorp = 15w) /\ ~(list = 0w) then
        aluout
      else
        reg15
    else if (ic = ldc) \/ (ic = stc) then
      if cpb then
        reg15
      else if is = t3 then
        aluout
      else
        inc
    else if (is = t3) /\
           ((ic = data_proc) /\ (~bit24 \/ bit23) /\ (bits1512 = 15w) \/
            (ic = mrs_msr) /\ ~bit21 /\ (bits1512 = 15w) \/
            (ic = ldr) \/ (ic = str) \/ (ic = ldm) \/ (ic = stm) \/
            (ic = br)) \/ (ic = swp) then
        aluout
    else if (is = t3) /\ (ic = swi_ex) then
      4w * w2w aregn
    else if ((ic = ldm) \/ (ic = stm)) /\ pencz \/
            (is = tn) /\ (ic = mla_mul) \/
            (is = t3) /\ (ic = cdp_und) /\ cpb \/
            (~(is = t3) \/ cpb) /\ ((ic = mcr) \/ (ic = mrc)) then
      reg15
    else
      inc`;

(* ------------------------------------------------------------------------- *)
(* Data Path Control: Instruction Decode Phase 2 --------------------------- *)
(* ------------------------------------------------------------------------- *)

val DIN_def = Define`
  DIN ic is (ireg:word32) data =
    if ((ic = ldr) \/ (ic = ldm) \/ (ic = swp) \/ (ic = mrc)) /\ (is = t4) \/
        (ic = ldm) /\ (is = tn) then
      data
    else
      ireg`;

val DINWRITE_def = Define`
  DINWRITE ic is = ~((ic = swp) /\ (is = t5))`;

val MASK_def = Define`
  MASK nxtic nxtis (mask:word16) (rp:word4) =
    if (nxtic = ldm) \/ (nxtic = stm) then
      if nxtis = t3 then
        Tw
      else
        CLEARBIT (w2n rp) mask
    else ARB`;

(* ------------------------------------------------------------------------- *)
(* Data Path Control: Instruction Execute Phase 1 -------------------------- *)
(* ------------------------------------------------------------------------- *)

val NBS_def = Define`
  NBS ic is (ireg:word32) m =
    let bit22 = ireg %% 22
    and bit15 = ireg %% 15 in
      if bit22 /\ (((is = tn) \/ (is = tm)) /\ (ic = ldm) /\ ~bit15 \/
                   ((is = t4) \/ (is = tn)) /\ (ic = stm)) then
        usr
      else
        DECODE_MODE m`;

val RP_def = Define`
  RP ic (list:word16) mask =
    if (ic = ldm) \/ (ic = stm) then
      n2w (LEASTBIT (list && mask)):word4
    else ARB`;

val PENCZ_def = Define`
  PENCZ ic (list:word16) mask =
    if (ic = ldm) \/ (ic = stm) then
      (list && mask) = 0w
    else ARB`;

val OFFSET_def = Define`
  OFFSET ic is (ireg:word32) (list:word16) =
    let bit24 = ireg %% 24
    and bit23 = ireg %% 23
    and w = 4w * n2w (SUM 16 (BITV (w2n list))) - 4w:word32 in
      if (is = t3) /\ ((ic = ldm) \/ (ic = stm)) then
        if bit23 then
          3w
        else if bit24 then
          w + 3w
        else
          w
      else if (is = t4) /\ ((ic = ldm) \/ (ic = stm)) then
        w + 3w
      else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
        3w
      else
        ARB`;

val FIELD_def = Define`
  FIELD ic is (ireg:word32) (oareg:word2) (din:word32) =
    if is = t3 then
      if ic = br then
        sw2sw (((23 >< 0) din):word24):word32
      else if (ic = ldr) \/ (ic = str) then
        (11 -- 0) din
      else if (ic = mrs_msr) \/ (ic = data_proc) \/
              (ic = ldc) \/ (ic = stc) then
        (7 -- 0) din
      else
        ARB
    else if (is = t5) /\ (ic = ldr) \/ (is = t6) /\ (ic = swp) then
      if ~(ireg %% 22) then
        din
      else let a = 8 * w2n oareg in
        ((a + 7) <> a) din
    else if (ic = ldm) /\ ((is = tn) \/ (is = tm)) \/
            (ic = mrc) /\ (is = t5) then
      din
    else
      ARB`;

val RBA_def = Define`
  RBA ic is ireg orp =
    if (is = t3) /\ ((ic = data_proc) \/ (ic = mrs_msr) \/
                     (ic = ldr) \/ (ic = str)) \/
       (is = t4) /\ (ic = reg_shift) \/
       (is = t5) /\ (ic = swp) \/
       (is = tn) /\ (ic = mla_mul) then
       ^Rg 3 0 ireg
    else if (is = t3) /\ ((ic = swp) \/ (ic = ldm) \/ (ic = stm)) then
       ^Rg 19 16 ireg
    else if (is = t3) /\ (ic = mla_mul) \/ (is = t4) /\ (ic = str)  \/
            (is = t4) /\ (ic = mcr) then
       ^Rg 15 12 ireg
    else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
       14w
    else if ((is = t4) \/ (is = tn)) /\ (ic = stm) then
       orp
    else
       ARB`;

val RAA_def = Define`
  RAA ic is ireg =
    if is = t3 then
       if (ic = data_proc) \/ (ic = ldr) \/ (ic = str) \/
          (ic = ldc) \/ (ic = stc) then
         ^Rg 19 16 ireg
       else if (ic = reg_shift) \/ (ic = mla_mul) then
         ^Rg 11 8 ireg
       else if (ic = br) \/ (ic = swi_ex) then
         15w
       else ARB
    else if (is = t4) /\ (ic = reg_shift) \/
            ((is = tn) \/ (is = tm)) /\ (ic = ldm) \/
            (is = tn) /\ (ic = mla_mul) then
       ^Rg 19 16 ireg
    else ARB`;

val PSRA_def = Define`
  PSRA ic is (ireg:word32) =
    let bit22 = ireg %% 22
    and bit20 = ireg %% 20 in
      (is = t3) /\ ((ic = swi_ex) \/ ~bit22 /\ ((ic = mrs_msr) \/
                    (ic = data_proc) /\ ~bit20)) \/
      (is = t4) /\ ~bit22 /\ (ic = reg_shift) /\ ~bit20 \/
      (is = tm) /\ ~bit22 /\ (ic = ldm)`;

val BUSB_def = Define`
  BUSB ic is (ireg:word32) (din':word32) rb =
    let bit25 = ireg %% 25 in
      if (is = t3) /\
         ((ic = br) \/
          (bit25 /\ ((ic = data_proc) \/ (ic = mrs_msr))) \/
          (~bit25 /\ ((ic = ldr) \/ (ic = str))) \/
          (ic = ldc) \/ (ic = stc)) \/
         (is = t5) /\ ((ic = ldr) \/ (ic = mrc)) \/
          (is = t6) /\ (ic = swp) \/
         ((is = tn) \/ (is = tm)) /\ (ic = ldm) then
         din'
      else
         rb`;

val BUSA_def = Define`
  BUSA ic is (psrrd:word32) ra offset =
    if ((is = t3) \/ (is = t4)) /\ ((ic = ldm) \/ (ic = stm)) \/
        (is = t5) /\ ((ic = br) \/ (ic = swi_ex)) then
      offset
    else if is = t3 then
      if ic = mrs_msr then
        psrrd
      else if (ic = data_proc) \/ (ic = ldr) \/ (ic = str) \/
              (ic = br) \/ (ic = swi_ex) \/ (ic = ldc) \/ (ic = stc) then
        ra
      else
        ARB
    else if (is = t4) /\ (ic = reg_shift) \/
            (is = tn) /\ (ic = mla_mul) \/
            ((is = tn) \/ (is = tm)) /\ (ic = ldm) then
       ra
    else
       ARB`;

(* Incorporates SCTLC *)

val SHIFTER_def = Define`
  SHIFTER ic is (ireg:word32) (oareg:word2) (mshift:word5)
          (sctrlreg:word32) busb c =
    let bit25 = ireg %% 25
    and bits118 = (11 >< 8) ireg
    and bits117 = (11 >< 7) ireg
    and bits65 = (6 >< 5) ireg in
      if is = t3 then
        if bit25 /\ ((ic = data_proc) \/ (ic = mrs_msr)) then
          ROR busb (2w * bits118) c
        else if (ic = ldm) \/ (ic = stm) \/ (ic = swp) \/ (ic = mla_mul) \/
                ~bit25 /\ ((ic = ldr) \/ (ic = str) \/ (ic = mrs_msr)) then
          LSL busb 0w c
        else if (~bit25 /\ (ic = data_proc)) \/
                 (bit25 /\ ((ic = ldr) \/ (ic = str))) then
          SHIFT_IMMEDIATE2 bits117 bits65 busb c
        else if (ic = br) \/ (ic = ldc) \/ (ic = stc) then
          LSL busb 2w c
        else
          ARB
      else if (is = t4) /\ (ic = reg_shift) then
        SHIFT_REGISTER2 ((7 >< 0) sctrlreg) bits65 busb c
      else if (is = t5) /\ (ic = ldr) \/ (is = t6) /\ (ic = swp) then
        ROR busb (8w * w2w oareg) c
      else if (is = t5) /\ ((ic = br) \/ (ic = swi_ex) \/ (ic = mrc)) \/
             ~(is = t4) /\ (ic = ldm) then
        LSL busb 0w c
      else if ic = mla_mul then (* is = tn *)
        LSL busb (w2w mshift) c
      else
        ARB`;

val BORROW_def = Define`
  BORROW ic is (mul:word2) =
    if ic = mla_mul then
       ~(is = t3) /\ mul %% 1
    else
       ARB`;

val COUNT1_def = Define`
  COUNT1 ic is (mshift:word5) =
    if ic = mla_mul then
       if is = t3 then (0w:word4) else (4 >< 1) mshift + 1w
    else
       ARB`;

val MUL1_def = Define`
  MUL1 ic is ra (mul2:word32) =
    if ic = mla_mul then
       if is = t3 then ra else (29 -- 0) mul2
    else
       ARB`;

val MULZ_def = Define`
  MULZ ic is mul2 =
   if (is = tn) /\ (ic = mla_mul) then
     (29 -- 0) mul2 = 0w
   else
     ARB`;

val MULX_def = Define`
  MULX ic is mulz borrow (mshift:word5) =
    if (is = tn) /\ (ic = mla_mul) then
      mulz /\ ~borrow \/ ((4 -- 1) mshift = 15w)
    else
      ARB`;

val PSRFBWRITE_def = Define`
  PSRFBWRITE ic is = ~((ic = mla_mul) \/ (is = t4) /\ (ic = swi_ex))`;

val SCTRLREGWRITE_def = Define`
  SCTRLREGWRITE ic is = (is = t3) /\ (ic = reg_shift)`;

val ALUAWRITE_def = Define`
  ALUAWRITE ic is obaselatch =
    (is = t3) /\ ((ic = data_proc) \/ (ic = mrs_msr) \/
      (ic = ldr) \/ (ic = str) \/ (ic = ldm) \/
      (ic = ldc) \/ (ic = stc)) \/
    (is = t4) /\ ((ic = reg_shift) \/ (ic = ldm)) \/
    (is = tn) /\ (ic = mla_mul) \/
    ~(is = tn) /\ (ic = stm) \/
    ~(is = t4) /\ ((ic = br) \/ (ic = swi_ex)) \/
    (ic = ldm) /\ obaselatch`;

val ALUBWRITE_def = Define`
  ALUBWRITE ic is =
    ~((ic = stm) /\ ~(is = t3) \/
      (is = t4) /\ ((ic = ldr) \/ (ic = str) \/ (ic = swp) \/ (ic = ldm)) \/
      (is = tn) /\ ((ic = ldc) \/ (ic = stc)))`;

val BASELATCH_def = Define`
  BASELATCH ic is = (ic = ldm) /\ (is = t4)`;

val NCPI_def = Define`
  NCPI ic = ~((ic = cdp_und) \/ (ic = mcr) \/ (ic = mrc) \/
              (ic = ldc) \/ (ic = stc))`;

val RWA_def = Define`
  RWA ic is ireg (list:word16) oorp dataabt =
    let bits1916 = ^Rg 19 16 ireg
    and bits1512 = ^Rg 15 12 ireg
    and bit21 = ireg %% 21
    and bit23 = ireg %% 23
    and bit24 = ireg %% 24 in
      if ((is = t3) /\ (ic = data_proc) \/
          (is = t4) /\ (ic = reg_shift)) /\ (~bit24 \/ bit23) \/
         (is = t3) /\ (ic = mrs_msr) /\ ~bit21 \/
         ((is = t5) /\ ((ic = ldr) \/ (ic = mrc) /\ ~(bits1512 = 15w)) \/
          (is = t6) /\ (ic = swp)) /\ ~dataabt then
        (T,bits1512)
      else if (ic = ldm) /\ (list = 0w) /\ ~dataabt /\ (is = tm) \/
              (ic = mla_mul) /\
                ((bits1916 = 15w) \/ (bits1916 = ^Rg 3 0 ireg)) then
        (F,ARB)
      else if (is = t4) /\
                (((ic = ldr) \/ (ic = str)) /\ (~bit24 \/ bit21) \/
                 ((ic = ldm) \/ (ic = stm)) /\ bit21 /\ ~(bits1916 = 15w)) \/
              (is = tm) /\ (ic = ldm) /\ dataabt /\ ~(bits1916 = 15w) \/
              (is = tn) /\
                ((ic = ldc) \/ (ic = stc)) /\ bit21 /\ ~(bits1916 = 15w) \/
              (ic = mla_mul) then
        (T,bits1916)
      else if ((is = t4) \/ (is = t5)) /\
                (((ic = br) /\ bit24) \/ (ic = swi_ex)) then
        (T,14w)
      else if (ic = ldm) /\ ((is = tn) \/ (is = tm)) /\ ~dataabt then
        (T,oorp)
      else (F,ARB)`;

(* ------------------------------------------------------------------------- *)
(* Data Path Control: Instruction Execute Phase 2 -------------------------- *)
(* ------------------------------------------------------------------------- *)

val ALU6_def = Define`
 ALU6 ic is ireg borrow2 (mul:word2) dataabt alua alub c =
  let opc = ^Rg 24 21 ireg in
   if ((ic = data_proc) /\ (is = t3)) \/
      ((ic = reg_shift) /\ (is = t4)) then
     ALU opc alua alub c
   else if (ic = mrs_msr) /\ (is = t3) then
     ALU_logic (if ireg %% 21 then alub else alua)
   else if ic = mla_mul then
     if is = t3 then
       if ireg %% 21 then ALU_logic alub else ALU_logic 0w
     else
       if ~borrow2 /\ (mul = 0w) \/ borrow2 /\ (mul = 3w) then
          ALU_logic alua
       else if borrow2 /\ (mul = 0w) \/ (mul = 1w) then
          ADD alua alub F
       else
          SUB alua alub T
   else if (ic = ldr) \/ (ic = str) \/ (ic = ldc) \/ (ic = stc) then
     if (is = t3) /\ ~(ireg %% 24) then
       ALU_logic alua
     else if (is = t3) \/
            ((is = t4) /\ (ic = ldr) \/ (ic = str)) \/
            ((is = tn) /\ (ic = ldc) \/ (ic = stc)) then
       if ireg %% 23 then ADD alua alub F else SUB alua alub T
     else if (is = t5) /\ (ic = ldr) then
       ALU_logic alub
     else
       ARB
   else if (ic = ldm) \/ (ic = stm) then
    (let bit24 = ireg %% 24
     and bit23 = ireg %% 23 in
     if is = t3 then
       if bit24 then
         if bit23 then
           ADD alua alub T
         else
           ADD (~alua) alub F
       else
         if bit23 then
           ALU_logic alub
         else
           ADD (~alua) alub T
     else if is = t4 then
       if (15 >< 0) ireg = 0w:word16 then
         ALU_logic alub
       else if bit23 then
         ADD alua alub T
       else
         ADD (~alua) alub F
     else if (ic = ldm) /\ (is = tm) /\ dataabt then
       ALU_logic alua
     else if (ic = ldm) /\ ((is = tn) \/ (is = tm)) then
       ALU_logic alub
     else ARB)
   else if (is = t3) /\ (ic = br) then
     ADD alua alub F
   else if (ic = br) \/ (ic = swi_ex) then
     if is = t4 then ALU_logic alua         else
     if is = t5 then ADD (~alua) alub F  else ARB
   else if (ic = swp) \/ (is = t5) /\ (ic = mrc) then
     ALU_logic alub
   else ARB`;

val MSHIFT_def = Define`
  MSHIFT ic borrow mul count1 =
    if ic = mla_mul then
      MSHIFT2 borrow mul count1
    else
      ARB`;

val PSRWA_def = Define`
  PSRWA ic is ireg nbs =
    let bits1916 = ^Rg 19 16 ireg
    and bit22 = ireg %% 22
    and bit21 = ireg %% 21
    and bit20 = ireg %% 20
    and bit19 = ireg %% 19
    and bit16 = ireg %% 16 in
      if bit20 /\
           (((is = t3) /\ (ic = data_proc)) \/
            ((is = t4) /\ (ic = reg_shift)) \/
            ((is = tn) /\ (ic = mla_mul)) /\
            ~((bits1916 = 15w) \/ (bits1916 = ^Rg 3 0 ireg))) \/
         (is = t5) /\ (ic = mrc) \/
         (is = t3) /\ (ic = swi_ex) \/
         (is = tm) /\ (ic = ldm) /\ ~USER nbs /\ bit22 then
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

val PSRDAT_def = Define`
  PSRDAT ic is ireg nbs (oorp:word4) dataabt (aregn:word3)
         cpsrl psrfb alu sctlc =
    let bit24 = ireg %% 24
    and bit23 = ireg %% 23
    and bit22 = ireg %% 22
    and bit21 = ireg %% 21
    and bit20 = ireg %% 20
    and bit19 = ireg %% 19
    and bit16 = ireg %% 16
    and bits1512 = ^Rg 15 12 ireg
    in
      if bit20 /\ (((is = t3) /\ (ic = data_proc)) \/
                   ((is = t4) /\ (ic = reg_shift))) then
        let (n,z,c,v) = FST alu in
        if bit24 /\ ~bit23 then
          if ~bit22 then
            SET_NZC (n,z,sctlc) cpsrl
           else
            SET_NZCV (n,z,c,v) cpsrl
        else if bits1512 = 15w then
          if USER nbs then
            cpsrl
          else
            psrfb
        else if (~bit23 /\ ~bit22) \/ (bit24 /\ bit23) then
          SET_NZC (n,z,sctlc) cpsrl
        else
          SET_NZCV (n,z,c,v) cpsrl
      else if bit20 /\ (is = tn) /\ (ic = mla_mul) then
        let (n,z,c,v) = FST alu in SET_NZC (n,z,sctlc) cpsrl
      else if (is = t5) /\ (ic = mrc) then
        if bits1512 = 15w then
          SET_NZCV (NZCV (SND alu)) cpsrl
        else
          cpsrl
      else if (is = t3) /\ (ic = mrs_msr) then
        let aluout = SND alu in
        if USER nbs then
          if ~bit22 /\ bit19 then
            word_modify (\i b. 28 <= i /\ aluout %% i \/ i < 28 /\ b) psrfb
          else
            ARB
        else
          word_modify (\i b. 28 <= i /\ (if bit19 then aluout %% i else b) \/
                             8 <= i /\ i <= 27 /\ b \/
                             i <= 7 /\ (if bit16 then aluout %% i else b)) psrfb
      else if (is = t3) /\ (ic = swi_ex) then
        SET_IFMODE T (if (aregn = 0w) \/ (aregn = 7w) then T else cpsrl %% 6)
                   (exception2mode (num2exception (w2n aregn))) cpsrl
      else if (is = t4) /\ (ic = swi_ex) then
        psrfb
      else if (is = tm) /\ (ic = ldm) then
        if (oorp = 15w) /\ ~dataabt then psrfb else cpsrl
      else
        ARB`;

(* ------------------------------------------------------------------------- *)
(* Pipeline Control: phase 1 ----------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val ABORTINST_def = Define`
  ABORTINST iregval onewinst ointstart ireg flags =
    ~iregval \/ (onewinst /\ ~ointstart /\ ~CONDITION_PASSED flags ireg)`;

val DATAABT_def = Define`
  DATAABT dataabt2 endinst = dataabt2 /\ ~endinst`;

val IC_def = Define`
  IC abortinst nxtic =
    if abortinst then unexec else nxtic`;

val IS_def = Define`
  IS abortinst nxtis =
    if abortinst then t3 else nxtis`;

val COPROC1_def = Define`
  COPROC1 cpa ncpi = cpa /\ ~ncpi`;

val DATAABT1_def = Define`
  DATAABT1 dataabt2 endinst mrq2 nopc1 abort =
    dataabt2 /\ ~endinst \/ mrq2 /\ nopc1 /\ abort`;

val FIQACT_def = Define`
  FIQACT cpsrf ooonfq = ~cpsrf /\ ~ooonfq`;

val IRQACT_def = Define`
  IRQACT cpsri oooniq = ~cpsri /\ ~oooniq`;

val PCCHANGE_def = Define`
  PCCHANGE rwa = let (rw,a:word4) = rwa in rw /\ (a = 15w)`;

val RESETLATCH_def = Define`
  RESETLATCH ph1 oorst resetstart resetlatch =
    if ph1 then
      oorst \/ resetlatch
    else (* ph2 *)
      if oorst \/ resetstart then oorst else resetlatch`;

val RESETSTART_def = Define`
  RESETSTART resetlatch oorst = resetlatch /\ ~oorst`;

val INTSEQ_def = Define`
  INTSEQ mrq2 nopc1 abort dataabt2 endinst ncpi cpa cpb
         fiqact iregabt1 irqact resetlatch oorst =
     mrq2 /\ nopc1 /\ abort \/
     dataabt2 /\ ~endinst \/
     ~ncpi /\ cpa /\ cpb \/
     fiqact \/ iregabt1 \/ irqact \/
     resetlatch /\ ~oorst`;

val NEWINST_def = Define`
  NEWINST ic is cpb intseq pencz mulx =
     (ic = data_proc) \/ (ic = mrs_msr) \/ (ic = unexec) \/
     (ic = cdp_und) /\ ~cpb \/
     ((ic = cdp_und) \/ (ic = mcr) \/ (ic = mrc) \/
      (ic = ldc) \/ (ic = stc)) /\ ((is = t3) /\ cpb /\ intseq) \/
     (ic = mcr) /\ (is = t4) \/
     (ic = mrc) /\ (is = t5) \/
     ((ic = ldc) \/ (ic = stc)) /\ (is = tn) /\ cpb \/
     (((ic = str) \/ (ic = reg_shift)) /\ (is = t4)) \/
     (((ic = ldr) \/ (ic = br) \/ (ic = swi_ex)) /\ (is = t5)) \/
     (ic = ldm) /\ (is = tm) \/
     ((ic = swp) /\ (is = t6)) \/
     (ic = mla_mul) /\ (is = tn) /\ mulx \/
     (ic = stm) /\ pencz /\ ((is = t4) \/ (is = tn))`;

val PIPEALL_def = Define`
   PIPEALL opipebll = opipebll`;

val PIPEBLL_def = Define`
   PIPEBLL ic newinst =
      newinst \/ (ic = br) \/ (ic = swi_ex)`;

val PIPECWRITE_def = Define`
   PIPECWRITE newinst = newinst`;

(* ------------------------------------------------------------------------- *)
(* Pipeline Control: phase 2 ----------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val NXTIC_def = Define`
  NXTIC intstart newinst ic ireg =
    if ~newinst then
      ic
    else if intstart then
      swi_ex
    else
      DECODE_INST ireg`;

val INC_IS_def = Define`INC_IS is = num2iseq (iseq2num is + 1)`;

val NXTIS_def = Define`
  NXTIS ic is newinst cpb pencz =
    if newinst \/
       ((ic = cdp_und) \/ (ic = mcr) \/ (ic = mrc) \/
        (ic = ldc) \/ (ic = stc)) /\ (is = t3) /\ cpb then
       t3
    else if ((is = t4) \/ (is = tn)) /\ (ic = ldm) then
       if pencz then tm else tn
    else if ((is = t4) \/ (is = tn)) /\ (ic = stm) \/ (ic = mla_mul) \/
            ((ic = ldc) \/ (ic = stc)) /\ ~cpb then
       tn
    else
       INC_IS is`;

val PIPEAWRITE_def = Define`
   PIPEAWRITE pipeall = pipeall`;

val PIPEBWRITE_def = Define`
   PIPEBWRITE pipebll = pipebll`;

val PIPESTATAWRITE_def = Define`
   PIPESTATAWRITE pipeall pcchange = pipeall \/ pcchange`;

val PIPESTATBWRITE_def = Define`
   PIPESTATBWRITE pipebll pcchange = pipebll \/ pcchange`;

val PIPESTATIREGWRITE_def = Define`
   PIPESTATIREGWRITE pipeall newinst srst =
      pipeall \/ newinst \/ srst`;

val PIPEAVAL_def = Define`
   PIPEAVAL srst pcchange = srst \/ ~pcchange`;

val IREGVAL_def = Define`
   IREGVAL pipecval srst pcchange = pipecval /\ ~srst /\ ~pcchange`;

val PIPEAABT_def = Define`
  PIPEAABT abortlatch srst pcchange = abortlatch /\ (srst \/ ~pcchange)`;

val IREGABT2_def = Define`
  IREGABT2 iregabt1 srst pcchange = iregabt1 /\ ~srst /\ ~pcchange`;

val AREGN1_def = Define`
  AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2 =
    if resetstart then 0w else
    if dataabt1   then 4w else
    if fiqactl    then 7w else
    if irqactl    then 6w else
    if coproc1    then 1w else
    if iregabt2   then 3w else 2w:word3`;

val ENDINST_def = Define`
  ENDINST resetstart iregval newinst =
    resetstart \/ iregval /\ newinst`;

(* ------------------------------------------------------------------------- *)
(* The State Function ------------------------------------------------------ *)
(* ------------------------------------------------------------------------- *)

val NEXT_ARM6_def = Define`
   NEXT_ARM6 (^arm6state) (NRESET,ABORT,NFQ,NIQ,DATA,CPA,CPB) =
     let cpsr = CPSR_READ psr
     in
     let (nzcv,cpsri,cpsrf,m) = DECODE_PSR cpsr
     and list = (15 >< 0) ireg
     in
     let abortinst = ABORTINST iregval onewinst ointstart ireg nzcv             (* PIPELINE CONTROL: PHASE 1 *)
     and dataabt = DATAABT dataabt2 endinst
     in
     let ic = IC abortinst nxtic
     and is = IS abortinst nxtis
     in
     let nbs    = NBS ic is ireg m                                              (* DATAPATH CONTROL: EXECUTE PHASE 1 *)
     and rp     = RP ic list mask
     and pencz  = PENCZ ic list mask
     and offset = OFFSET ic is ireg list
     and din'   = FIELD ic is ireg oareg din
     and rba    = RBA ic is ireg orp
     and raa    = RAA ic is ireg
     in
     let psrrd  = if PSRA ic is ireg then cpsr else SPSR_READ psr nbs
     and rb = REG_READ6 reg nbs rba
     and ra = REG_READ6 reg nbs raa
     in
     let busb = BUSB ic is ireg din' rb
     and busa = BUSA ic is psrrd ra offset
     in
     let shifter = SHIFTER ic is ireg oareg mshift sctrlreg busb (CARRY nzcv)
     and borrow  = BORROW ic is mul
     and count1  = COUNT1 ic is mshift
     and mul1    = MUL1 ic is ra mul2
     and mulz    = MULZ ic is mul2
     in
     let mulx      = MULX ic is mulz borrow mshift
     and psrfb'    = if PSRFBWRITE ic is then psrrd else psrfb
     and sctrlreg' = if SCTRLREGWRITE ic is then ra else sctrlreg
     and shcout    = FST shifter
     and alua'     = if ALUAWRITE ic is obaselatch then busa else alua
     and alub'     = if ALUBWRITE ic is then (SND shifter) else alub
     and baselatch = BASELATCH ic is
     and ncpi      = NCPI ic
     and rwa       = RWA ic is ireg list oorp dataabt
     in
     let nmreq = NMREQ ic is pencz mulx CPB                                     (* DATAPATH CONTROL: INSTRUCTION FETCH PHASE 1 *)
     and pcwa  = PCWA ic is ireg CPB
     in
     let orst  = ~NRESET                                                        (* PIPELINE CONTROL: PHASE 1 *)
     and srst  = oorst
     and oonfq = onfq
     and ooniq = oniq
     and iregabt1    = pipebabt
     and coproc1     = COPROC1 CPA ncpi
     and dataabt1    = DATAABT1 dataabt2 endinst mrq2 nopc1 ABORT
     and fiqactl     = FIQACT cpsrf ooonfq
     and irqactl     = IRQACT cpsri oooniq
     and pcchange    = PCCHANGE rwa
     and abortlatch  = ABORT
     and resetlatch' = RESETLATCH T oorst ARB resetlatch
     and aregn       = aregn2
     in
     let resetstart = RESETSTART resetlatch' oorst
     and intstart   = INTSEQ mrq2 nopc1 ABORT dataabt2 endinst ncpi CPA CPB
                        fiqactl iregabt1 irqactl resetlatch' oorst
     in
     let newinst = NEWINST ic is CPB intstart pencz mulx
     in
     let pipeall  = PIPEALL opipebll
     and pipebll  = PIPEBLL ic newinst
     and pipec    = if PIPECWRITE newinst then pipeb else ireg
     and pipecval = pipebval
     in
     let mul'  = (1 >< 0) mul1                                                  (* DATAPATH CONTROL: PIPELINE PHASE 2 *)
     and mul2' = (31 -- 2) mul1
     in
     let alu     = ALU6 ic is ireg borrow2 mul dataabt alua' alub' (CARRY nzcv) (* DATAPATH CONTROL: EXECUTE PHASE 2 *)
     and mshift' = MSHIFT ic borrow mul' count1
     and psrwa   = PSRWA ic is ireg nbs
     in
     let aluout = SND alu
     and psrdat = PSRDAT ic is ireg nbs oorp dataabt aregn cpsr
                         psrfb' alu shcout
     and inc    = areg + 4w
     and pcbus  = REG_READ6 reg usr 15w
     in
     let reg'  = if pcwa then REG_WRITE reg nbs 15w inc else reg
     in
     let reg'' = if FST rwa then REG_WRITE reg' nbs (SND rwa) aluout else reg'
     and psr'  = if FST psrwa then
                    if SND psrwa then CPSR_WRITE psr psrdat
                                 else SPSR_WRITE psr nbs psrdat
                 else psr
     in
     let nxtic' = NXTIC intstart newinst ic pipec                               (* PIPELINE CONTROL: PHASE 2 *)
     and nxtis' = NXTIS ic is newinst CPB pencz
     and oorst' = orst
     and pipea' = if PIPEAWRITE pipeall then DATA else pipea
     in
     let pipeb' = if PIPEBWRITE pipebll then pipea' else pipeb
     and (pipeaval',pipeaabt') =
           if PIPESTATAWRITE pipeall pcchange then
             (PIPEAVAL srst pcchange, PIPEAABT abortlatch srst pcchange)
           else (pipeaval, pipeaabt)
     in
     let (pipebval',pipebabt') =
           if PIPESTATBWRITE pipebll pcchange then
             (pipeaval', pipeaabt')
           else (pipebval, pipebabt)
     and (iregval',iregabt2') =
           if PIPESTATIREGWRITE pipeall newinst srst then
             (IREGVAL pipecval srst pcchange, IREGABT2 iregabt1 srst pcchange)
           else (iregval, iregabt2)
     in
     let aregn1   = AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2'
     and endinst' = ENDINST resetstart iregval' newinst
     and resetlatch'' = RESETLATCH F oorst' resetstart resetlatch'
     in
     let nxtdin   = if DINWRITE ic is then DIN ic is pipec DATA else din        (* DATAPATH CONTROL: DECODE PHASE 2 *)
     and mask'    = MASK nxtic' nxtis' mask rp
     in
     let nbw'   = NBW ic is ireg                                                (* DATAPATH CONTROL: FETCH PHASE 2 *)
     and nopc   = NOPC ic is pencz CPB
     and nrw'   = NRW ic is pencz CPB
     and oareg' = (1 >< 0) areg
     and areg'  = AREG ic is ireg aregn inc pcbus aluout list
                       pencz oorp CPB dataabt
     in
   ARM6 (DP reg'' psr' areg' nxtdin alua' alub' busb)
     (CTRL pipea' pipeaval' pipeb' pipebval' pipec iregval' intstart newinst
           endinst' baselatch pipebll nxtic' nxtis' nopc oorst' resetlatch''
           NFQ oonfq NIQ ooniq pipeaabt' pipebabt' iregabt2' dataabt1 aregn1
           (~nmreq) nbw' nrw' sctrlreg' psrfb' oareg' mask' rp orp mul' mul2'
           borrow mshift')`;

val OUT_ARM6_def = Define`
  OUT_ARM6 (^arm6state) = (dout,~mrq2,nopc1,nrw,nbw,areg)`;

val INIT_ARM6_def = Define`
  INIT_ARM6 (^arm6state) =
    let ointstart1 = ~(aregn2 = 2w) in
    let nxtic1 = if ointstart1 then swi_ex else NXTIC F T nxtic ireg in
      ARM6 (DP reg psr (if ointstart1 then areg else REG_READ6 reg usr 15w)
                       (if ointstart1 then din else ireg) alua alub dout)
        (CTRL pipea T pipeb T ireg T
              ointstart1 T T obaselatch T nxtic1 t3 F F F
              onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
              aregn2 mrq2 nbw F sctrlreg psrfb oareg
              (MASK nxtic1 t3 mask ARB) orp oorp mul mul2 borrow2 mshift)`;

val STATE_ARM6_def = Define`
  (STATE_ARM6 0 x = INIT_ARM6 x.state) /\
  (STATE_ARM6 (SUC t) x = NEXT_ARM6 (STATE_ARM6 t x) (x.inp t))`;

val ARM6_SPEC_def = Define`
  ARM6_SPEC t x = let s = STATE_ARM6 t x in
     <| state := s; out := OUT_ARM6 s |>`;

(* ------------------------------------------------------------------------- *)
(* Projections ------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val arm6inp =
 ``(NRESET:bool,ABORT:bool,NFIQ:bool,NIRQ:bool,DATA:word32,CPA:bool,CPB:bool)``;

val PROJ_NRESET_def = Define `PROJ_NRESET (^arm6inp) = NRESET`;
val PROJ_ABORT_def  = Define `PROJ_ABORT  (^arm6inp) = ABORT`;
val PROJ_NFIQ_def   = Define `PROJ_NFIQ   (^arm6inp) = NFIQ`;
val PROJ_NIRQ_def   = Define `PROJ_NIRQ   (^arm6inp) = NIRQ`;
val PROJ_DATA_def   = Define `PROJ_DATA   (^arm6inp) = DATA`;
val PROJ_CPA_def    = Define `PROJ_CPA    (^arm6inp) = CPA`;
val PROJ_CPB_def    = Define `PROJ_CPB    (^arm6inp) = CPB`;

val IS_RESET_def  = Define `IS_RESET  i (t:num) = ~PROJ_NRESET (i t)`;
val IS_ABORT_def  = Define `IS_ABORT  i (t:num) =  PROJ_ABORT  (i t)`;
val IS_FIQ_def    = Define `IS_FIQ    i (t:num) = ~PROJ_NFIQ   (i t)`;
val IS_IRQ_def    = Define `IS_IRQ    i (t:num) = ~PROJ_NIRQ   (i t)`;
val IS_ABSENT_def = Define `IS_ABSENT i (t:num) =  PROJ_CPA    (i t)`;
val IS_BUSY_def   = Define `IS_BUSY   i (t:num) =  PROJ_CPB    (i t)`;

val arm6out =
  ``(dout:word32, mrq2:bool, nopc1:bool, nrw:bool, nbw:bool, areg:word32)``;

val IS_MEMOP_def = Define `IS_MEMOP (^arm6out) = nopc1`;

(* ------------------------------------------------------------------------- *)
(* The Uniform Immersion --------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val CP_INTERRUPT_def = Define`
  CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt) i n =
    IS_ABSENT i n \/
    ~cpsrf /\ (if n = 0 then ~ooonfq else
               if n = 1 then ~onfq else IS_FIQ i (n - 2)) \/
    ~cpsri /\ (if n = 0 then ~oooniq else
               if n = 1 then ~oniq else IS_IRQ i (n - 2)) \/
    pipebabt`; (* abort on fetch *)

val BUSY_WAIT_DONE_def = Define`
  BUSY_WAIT_DONE iflags i n = IS_BUSY i n ==> CP_INTERRUPT iflags i n`;

val BUSY_WAIT_def = Define`
  BUSY_WAIT x i = LEAST n. BUSY_WAIT_DONE x i n`;

val DUR_IC_def = Define`
  DUR_IC ic ireg rs iflags inp =
    if (ic = br) \/ (ic = swi_ex) then
      3
    else if (ic = mrs_msr) \/ (ic = data_proc) then
      if PCCHANGE (RWA ic t3 ireg ARB ARB ARB) then 3 else 1
    else if ic = reg_shift then
      if PCCHANGE (RWA ic t4 ireg ARB ARB ARB) then 4 else 2
    else if ic = ldr then
      if PCCHANGE (RWA ic t4 ireg ARB ARB ARB) \/
         PCCHANGE (RWA ic t5 ireg ARB ARB (IS_ABORT inp 1)) then 5 else 3
    else if ic = str then
      if PCCHANGE (RWA ic t4 ireg ARB ARB ARB) then 4 else 2
    else if ic = swp then
      if PCCHANGE (RWA ic t6 ireg ARB ARB
           (IS_ABORT inp 1 \/ IS_ABORT inp 2)) then 6 else 4
    else if ic = mla_mul then
      1 + MLA_MUL_DUR rs
    else let l = LENGTH (REGISTER_LIST ((15 >< 0) ireg)) in
    if ic = ldm then
      2 + (l - 1) + 1 +
     (if ireg %% 15 /\ ~(?s. s < l /\ IS_ABORT inp (s + 1)) then 2 else 0)
    else if ic = stm then
      2 + (l - 1)
    else let b = BUSY_WAIT iflags inp in
    if (ic = cdp_und) \/
        ic IN {mcr; mrc; ldc; stc} /\ IS_BUSY inp b /\
        CP_INTERRUPT iflags inp b then
      1 + b
    else if ic = mcr then
      1 + b + 1
    else if ic = mrc then
      1 + b + 2
    else if (ic = ldc) \/ (ic = stc) then
      1 + b + (LEAST n. IS_BUSY (ADVANCE b inp) n)
    else (* unexec *)
      1`;

val IFLAGS_def = Define`
  IFLAGS x = case x of (^arm6state) ->
      let (flags,cpsri,cpsrf,m) = DECODE_PSR (CPSR_READ psr) in
        (onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt)`;

val DUR_X_def = Define`
  DUR_X x = case x.state of (^arm6state) ->
    let (flags,cpsri,cpsrf,m) = DECODE_PSR (CPSR_READ psr) in
    let abortinst = ABORTINST iregval onewinst ointstart ireg flags in
    let ic = IC abortinst nxtic
    and rs = REG_READ6 reg (DECODE_MODE m) (^Rg 11 8 ireg) in
    let d = DUR_IC ic ireg rs (IFLAGS x.state) x.inp
    in
      if ?t. t < d /\ IS_RESET x.inp t then (* oorst = F *)
        (T,(LEAST t. IS_RESET x.inp t /\
              ~IS_RESET x.inp (t + 1) /\ ~IS_RESET x.inp (t + 2)) + 3)
      else
        (F,d)`;

val DUR_ARM6_def = Define`DUR_ARM6 x = SND (DUR_X x)`;

val IMM_ARM6_def = Define`
  (IMM_ARM6 x 0 = 0) /\
  (IMM_ARM6 x (SUC t) =
     DUR_ARM6 <|state := STATE_ARM6 (IMM_ARM6 x t) x;
       inp := ADVANCE (IMM_ARM6 x t) x.inp|> + IMM_ARM6 x t)`;

(* ------------------------------------------------------------------------- *)
(* The Data Abstraction ---------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val SUB8_PC_def = Define `SUB8_PC (reg:reg) = (r15 :- reg r15 - 8w) reg`;
val ADD8_PC_def = Define `ADD8_PC (reg:reg) = (r15 :- reg r15 + 8w) reg`;

val ABS_ARM6_def = Define`
  ABS_ARM6 (^arm6state) =
    ARM_EX (ARM (SUB8_PC reg) psr) ireg (num2exception (w2n aregn2))`;

(* ------------------------------------------------------------------------- *)
(* Stream Domain and Abstraction ------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val STRM_ARM6_def = Define`
  STRM_ARM6 i =
    (!t. IS_RESET i t ==>
           ~(t = 0) /\ IS_RESET i (t - 1) \/
           (IS_RESET i (t + 1) /\ IS_RESET i (t + 2) /\ IS_RESET i (t + 3))) /\
    (!t. IS_ABSENT i t ==> IS_BUSY i t) /\
    (!t. ?t2. t < t2 /\ ~IS_RESET i t2 /\ ~IS_RESET i (t2 + 1)) /\
    (!t. ?t2. t < t2 /\ (IS_BUSY i t2 ==> IS_ABSENT i t2)) /\
    (!t. ~IS_BUSY i t ==> ?t2. t < t2 /\ IS_BUSY i t2)`;

val exc2exception_def = Define`
  exc2exception exc a n =
   case exc of
      reset     -> SOME (Reset a)
   || dabort    -> SOME (Dabort n)
   || fast      -> SOME Fiq
   || interrupt -> SOME Irq
   || pabort    -> SOME Prefetch
   || undefined -> SOME Undef
   || _         -> NONE`;

val SMPL_EXC_ARM6_def = Define`
  SMPL_EXC_ARM6 x t =
    case ABS_ARM6 (STATE_ARM6 (IMM_ARM6 x (t + 1)) x) of
      ARM_EX state ireg exc ->
        (exc2exception exc state
           (LEAST s. IS_ABORT x.inp (IMM_ARM6 x t + (s + 1))),
         let s = IMM_ARM6 x t in
         let b = BUSY_WAIT (IFLAGS (STATE_ARM6 s x)) (ADVANCE s x.inp) in
           IS_BUSY x.inp (s + b),
         ireg)`;

val SMPL_DATA_ARM6_def = Define`
  SMPL_DATA_ARM6 x =
    MAP_STRM TL (PACK (IMM_ARM6 x) (MAP_STRM PROJ_DATA x.inp))`;

val SMPL_ARM6_def = Define`
  SMPL_ARM6 x =
    COMBINE (\(a,b,c) d. (a,b,c,d)) (SMPL_EXC_ARM6 x) (SMPL_DATA_ARM6 x)`;

val MOVE_DOUT_def = Define`
  MOVE_DOUT x l =
    if NULL l then [] else ZIP (SNOC x (TL (MAP FST l)),MAP SND l)`;

val MEMOP_def = Define`
  MEMOP (^arm6out) =
    if nrw then
      MemWrite (~nbw) areg dout
    else
      MemRead areg`;

val PROJ_IREG_def = Define `PROJ_IREG (^arm6state) = ireg`;

val OSMPL_ARM6_def = Define`
  OSMPL_ARM6 x l =
    let x0 = SINIT INIT_ARM6 x in
    let ireg = PROJ_IREG x0.state in
    let ic = DECODE_INST ireg in
      if FST (DUR_X x0) \/
         (ic = mcr) \/ (ic = ldc) \/ (ic = stc)
         (* in future should add "sanity checks" for coproc. cases e.g.
            if executed and no interrupt then:
                "l" contains correct sequential memory requsets,
             or "l" finishes with DOUT set for write to coproc. *)
      then
        OUT_ARM (ABS_ARM6 x.state)
      else
        (MAP MEMOP o FILTER IS_MEMOP o
         MOVE_DOUT (FST (OUT_ARM6 (STATE_ARM6 (IMM_ARM6 x 1) x)))) l`;

(* ------------------------------------------------------------------------- *)
(* Basic Theorems ---------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val STATE_ARM6_THM = store_thm("STATE_ARM6_THM",
  `IMAP ARM6_SPEC INIT_ARM6 NEXT_ARM6 OUT_ARM6`,
  RW_TAC (std_ss++boolSimps.LET_ss) [ARM6_SPEC_def,STATE_ARM6_def,IMAP_def]);

val STATE_ARM6_IMAP_INIT = store_thm("STATE_ARM6_IMAP_INIT",
  `IS_IMAP_INIT ARM6_SPEC INIT_ARM6`,
  PROVE_TAC [STATE_ARM6_THM,IS_IMAP_INIT_def]);

val STATE_ARM6_IMAP = store_thm("STATE_ARM6_IMAP",
  `IS_IMAP ARM6_SPEC`, PROVE_TAC [STATE_ARM6_THM,IS_IMAP_def]);

val ARM6_SPEC_STATE = save_thm("ARM6_SPEC_STATE",
  (SIMP_CONV (srw_ss()++boolSimps.LET_ss) [ARM6_SPEC_def])
  ``(ARM6_SPEC t x).state``);

val STATE_ARM6_COR = save_thm("STATE_ARM6_COR",
  REWRITE_RULE [ARM6_SPEC_STATE] (MATCH_MP STATE_FUNPOW_INIT4 STATE_ARM6_THM));

val ARM6_SPEC_OUT = save_thm("ARM6_SPEC_OUT",
  REWRITE_RULE [ARM6_SPEC_STATE] (MATCH_MP OUTPUT_THM STATE_ARM6_THM));

val MSHIFT = save_thm("MSHIFT",REWRITE_RULE [MSHIFT2_def] MSHIFT_def);

val INC_IS = save_thm("INC_IS",
  LIST_CONJ (map (fn is => (GEN_ALL o RIGHT_CONV_RULE (SIMP_CONV arith_ss
     [theorem "iseq2num_thm",theorem "num2iseq_thm"]) o SPEC is) INC_IS_def)
     [`t3`,`t4`,`t5`]));

val DUR_X = save_thm("DUR_X",
  (SIMP_RULE (srw_ss()++boolSimps.LET_ss) [DECODE_PSR_def,GSYM IMP_DISJ_THM] o
   ONCE_REWRITE_RULE [PROVE []
     ``!a b c. (if a then c else b) = (if ~a then b else c)``] o
     SPEC `<|state := (^arm6state); inp := i|>`) DUR_X_def);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
