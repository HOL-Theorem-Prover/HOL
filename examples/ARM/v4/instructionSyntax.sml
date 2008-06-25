(* ========================================================================= *)
(* FILE          : instructionSyntax.sml                                     *)
(* DESCRIPTION   : Support for working with ARM instructions                 *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["Nonstdio","wordsSyntax", "instructionTheory",
            "assemblerML", "Data"];
*)

structure instructionSyntax :> instructionSyntax = struct

open HolKernel boolLib Parse bossLib;
open Q wordsSyntax instructionTheory Data assemblerML;

(* ------------------------------------------------------------------------- *)

fun mk_bool b = if b then T else F;

fun mk_word t n = mk_n2w(numLib.mk_numeral n, t);

val mk_word3 = mk_word ``:3``;
val mk_word4 = mk_word ``:4``;
val mk_word5 = mk_word ``:5``;
val mk_word8 = mk_word ``:8``;
val mk_word12 = mk_word ``:12``;
val mk_word16 = mk_word ``:16``;
val mk_word24 = mk_word ``:24``;
val mk_word32 = mk_word ``:32``;

fun mk_register (NReg n) = (mk_word4 o Arbnum.fromInt o register2int) n
  | mk_register (VReg x) = mk_var (x, ``:word4``);

fun mk_condition cond =
  case cond of
    EQ => ``EQ`` | NE => ``NE`` | CS => ``CS`` | CC => ``CC``
  | MI => ``MI`` | PL => ``PL`` | VS => ``VS`` | VC => ``VC``
  | HI => ``HI`` | LS => ``LS`` | GE => ``GE`` | LT => ``LT``
  | GT => ``GT`` | LE => ``LE`` | AL => ``AL`` | NV => ``NV``;

fun mk_opcode opc =
  case opc of
    AND => ``instruction$AND`` | EOR => ``instruction$EOR``
  | SUB => ``instruction$SUB`` | RSB => ``instruction$RSB``
  | ADD => ``instruction$ADD`` | ADC => ``instruction$ADC``
  | SBC => ``instruction$SBC`` | RSC => ``instruction$RSC``
  | TST => ``instruction$TST`` | TEQ => ``instruction$TEQ``
  | CMP => ``instruction$CMP`` | CMN => ``instruction$CMN``
  | ORR => ``instruction$ORR`` | MOV => ``instruction$MOV``
  | BIC => ``instruction$BIC`` | MVN => ``instruction$MVN``;

fun mk_br (Instruction (x,c)) =
 (case x of
    Br y =>
      subst [``c:condition``   |-> mk_condition c,
             ``offset:word24`` |-> mk_word24 (Arbnum.fromInt (#offset y))]
        (if #L y then ``instruction$BL c offset``
                 else ``instruction$B c offset``)
  | _ => raise ERR "mk_br" "not a branch instruction")
 | mk_br _ = raise ERR "mk_br" "not a branch instruction";

fun mk_swi_ex c = subst [``c:condition`` |-> mk_condition c] ``SWI c``;

local
  fun num2imm(x,n) =
  let val x8 = Arbnum.mod(x,Arbnum.fromInt 256) in
    if x8 = x then
      (Arbnum.fromInt n, x8)
    else
      if n < 15 then
        num2imm(rol32 x 2, n + 1)
      else
        raise ERR "num2immediate" "number cannot be represented as an immediate"
  end
in
  fun num2immediate n = num2imm(n, 0)
end;

fun mk_shift r s =
  subst [``r:word4`` |-> mk_register r]
  (case s of
     LSL => ``instruction$LSL r``
   | LSR => ``instruction$LSR r``
   | ASR => ``instruction$ASR r``
   | ROR => ``instruction$ROR r``);

local
  fun mk_dp_immediate x =
  let val (n,m) = num2immediate x in
    subst [``n:word4`` |-> mk_word4 n,
           ``m:word8`` |-> mk_word8 m] ``Dp_immediate n m``
  end

  fun mk_addr_mode1 x =
    case x of
      DpImmediate n => mk_dp_immediate n
    | DpShiftImmediate i =>
         subst [``sh:shift``  |-> mk_shift (#Rm i) (#Sh i),
                ``imm:word5`` |-> mk_word5 (Arbnum.fromInt (#Imm i))]
           ``Dp_shift_immediate sh imm``
    | DpShiftRegister r =>
         subst [``sh:shift`` |-> mk_shift (#Rm r) (#Sh r),
                ``rs:word4`` |-> mk_register (#Rs r)]
           ``Dp_shift_register sh rs``
  val err = ERR "mk_data_proc" "not a data processing instruction"
in
  fun mk_data_proc (Instruction (x,c)) =
   (case x of
      Data_proc y => let val opc = #opc y in
        if mem opc [TST,TEQ,CMP,CMN] then
          subst [``f:condition -> word4 -> addr_mode1 -> arm_instruction`` |->
                 mk_opcode opc, ``c:condition`` |-> mk_condition c,
                 ``rn:word4`` |-> mk_register (#Rn y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (rn:word4)
                 (op2:addr_mode1)):arm_instruction``
        else if opc = MOV orelse opc = MVN then
          subst [``f:condition -> bool -> word4 -> addr_mode1 ->
                     arm_instruction`` |-> mk_opcode opc,
                 ``c:condition`` |-> mk_condition c,
                 ``s:bool`` |-> mk_bool (#S y),
                 ``rd:word4`` |-> mk_register (#Rd y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (s:bool) (rd:word4)
                 (op2:addr_mode1)):arm_instruction``
        else
          subst [``f:condition -> bool -> word4 -> word4 -> addr_mode1 ->
                     arm_instruction`` |-> mk_opcode opc,
                 ``c:condition`` |-> mk_condition c,
                 ``s:bool``   |-> mk_bool (#S y),
                 ``rd:word4`` |-> mk_register (#Rd y),
                 ``rn:word4`` |-> mk_register (#Rn y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (s:bool) (rd:word4) (rn:word4)
                 (op2:addr_mode1)):arm_instruction``
      end
    | _ => raise err)
   | mk_data_proc _ = raise err
end;

fun mk_mla_mul (Instruction (x,c)) =
 (case x of
    Mla_mul y =>
      subst [``c:condition`` |-> mk_condition c,
             ``s:bool`` |-> mk_bool (#S y),
             ``rd:word4`` |-> mk_register (#Rd y),
             ``rm:word4`` |-> mk_register (#Rm y),
             ``rs:word4`` |-> mk_register (#Rs y),
             ``rn:word4`` |-> mk_register (#Rn y)]
      (case (#L y, #Signed y, #A y) of
         (false,_,false)    => ``MUL c s rd rm rs``
       | (false,_,true)     => ``MLA c s rd rm rs rn``
       | (true,false,false) => ``UMULL c s rn rd rm rs``
       | (true,false,true)  => ``UMLAL c s rn rd rm rs``
       | (true,true,false)  => ``SMULL c s rn rd rm rs``
       | (true,true,true)   => ``SMLAL c s rn rd rm rs``)
  | _ => raise ERR "mk_mla_mul" "not a multiply instruction")
 | mk_mla_mul _ = raise ERR "mk_mla_mul" "not a multiply instruction";

local
  fun mk_addr_mode2 x =
    case x of
      DtImmediate n =>
        subst [``i:word12`` |-> mk_word12 (Arbnum.fromInt n)] ``Dt_immediate i``
    | DtShiftImmediate i =>
        subst [``sh:shift`` |-> mk_shift (#Rm i) (#Sh i),
                ``imm:word5`` |-> mk_word5 (Arbnum.fromInt (#Imm i))]
        ``Dt_shift_immediate sh imm``

  fun mk_options (Ldr_str y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldr_str" "not a load/store instruction"
  val err = ERR "mk_ldr_str" "not a load/store instruction"
in
  fun mk_ldr_str (Instruction(x,c)) =
   (case x of
      Ldr_str y =>
        subst [``c:condition`` |-> mk_condition c,
               ``b:bool`` |-> mk_bool (#B y),
               ``opt:transfer_options`` |-> mk_options x,
               ``rd:word4`` |-> mk_register (#Rd y),
               ``rn:word4`` |-> mk_register (#Rn y),
               ``offset:addr_mode2`` |-> mk_addr_mode2 (#offset y)]
        (if #L y then
           ``instruction$LDR c b opt rd rn offset``
         else
           ``instruction$STR c b opt rd rn offset``)
    | _ => raise err)
   | mk_ldr_str _ = raise err
end;

local
  fun mk_addr_mode3 x =
    case x of
      DthImmediate n =>
        subst [``i:word8`` |-> mk_word8 (Arbnum.fromInt n)] ``Dth_immediate i``
    | DthRegister r =>
        subst [``rm:word4`` |-> mk_register r] ``Dth_register rm``

  fun mk_options (Ldrh_strh y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldrh_strh"
                               "not a load/store (half) instruction"
  val err = ERR "mk_ldrh_strh" "not a load/store (half) instruction"
in
  fun mk_ldrh_strh (Instruction(x,c)) =
   (case x of
      Ldrh_strh y =>
        subst [``c:condition`` |-> mk_condition c,
               ``s:bool`` |-> mk_bool (#S y),
               ``h:bool`` |-> mk_bool (#H y),
               ``opt:transfer_options`` |-> mk_options x,
               ``rd:word4`` |-> mk_register (#Rd y),
               ``rn:word4`` |-> mk_register (#Rn y),
               ``offset:addr_mode3`` |-> mk_addr_mode3 (#offset y)]
        (if #L y then
           subst [``s:bool`` |-> mk_bool (#S y)]
              ``instruction$LDRH c s h opt rd rn offset``
         else
           ``instruction$STRH c opt rd rn offset``)
    | _ => raise err)
   | mk_ldrh_strh _ = raise err
end;

local
  fun mk_options (Ldm_stm y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldm_stm" "not a block transfer instruction"
  val err = ERR "mk_ldm_stm" "not a block transfer instruction"
in
  fun mk_ldm_stm (Instruction(x,c)) =
   (case x of
      Ldm_stm y =>
        subst [``c:condition`` |-> mk_condition c,
               ``s:bool``      |-> mk_bool (#S y),
               ``opt:transfer_options`` |-> mk_options x,
               ``rn:word4``    |-> mk_register (#Rn y),
               ``list:word16`` |-> mk_word16 (Arbnum.fromInt (#list y))]
        (if #L y then
           ``instruction$LDM c s opt rn list``
         else
           ``instruction$STM c s opt rn list``)
    | _ => raise err)
   | mk_ldm_stm _ = raise err
end;

fun mk_swp (Instruction(x,c)) =
 (case x of
    Swp y =>
       subst [``c:condition`` |-> mk_condition c,
              ``b:bool``   |-> mk_bool (#B y),
              ``rd:word4`` |-> mk_register (#Rd y),
              ``rm:word4`` |-> mk_register (#Rm y),
              ``rn:word4`` |-> mk_register (#Rn y)]
      ``instruction$SWP c b rd rm rn``
  | _ => raise ERR "mk_swp" "not a swap instruction")
 | mk_swp _ = raise ERR "mk_swp" "not a swap instruction";

fun mk_mrs (Instruction(x,c)) =
 (case x of
    Mrs y =>
      subst [``c:condition`` |-> mk_condition c,
             ``r:bool``   |-> mk_bool (#R y),
             ``rd:word4`` |-> mk_register (#Rd y)]
        ``instruction$MRS c r rd``
  | _ => raise ERR "mk_mrs" "not an mrs instruction")
 | mk_mrs _ = raise ERR "mk_mrs" "not an mrs instruction";

local
  fun mk_msr_psr (Msr y) =
       (case (#R y,#bit19 y,#bit16 y) of
          (_,false,false) =>
             raise ERR "mk_msr" "either bit19 or bit16 must be set"
        | (false,false,true) => ``CPSR_c``
        | (false,true,false) => ``CPSR_f``
        | (false,true,true)  => ``CPSR_a``
        | (true,false,true)  => ``SPSR_c``
        | (true,true,false)  => ``SPSR_f``
        | (true,true,true)   => ``SPSR_a``)
    | mk_msr_psr _ = raise ERR "mk_msr" "not an msr instruction"

  fun mk_msr_immediate x =
  let val (n,m) = num2immediate x in
    subst [``n:word4`` |-> mk_word4 n,
           ``m:word8`` |-> mk_word8 m] ``Msr_immediate n m``
  end

  fun mk_msr_mode x =
        case x of
          MsrImmediate n => mk_msr_immediate n
        | MsrRegister r => subst [``r:word4`` |-> mk_register r]
            ``Msr_register r``

  val err = ERR "mk_msr" "not an msr instruction"
in
  fun mk_msr (Instruction(x,c)) =
   (case x of
      Msr y =>
        subst [``c:condition``  |-> mk_condition c,
               ``psrd:msr_psr`` |-> mk_msr_psr x,
               ``op:msr_mode``  |-> mk_msr_mode (#Op y)]
        ``instruction$MSR c psrd op``
    | _ => raise err)
   | mk_msr _ = raise err
end;

fun mk_cdp (Instruction(x,c)) =
 (case x of
    Cdp y =>
      subst [``c:condition`` |-> mk_condition c,
             ``cpn:word4``  |-> mk_word4 (Arbnum.fromInt (#CP y)),
             ``cop1:word4`` |-> mk_word4 (Arbnum.fromInt (#Cop1 y)),
             ``crd:word4``  |-> mk_register (#CRd y),
             ``crn:word4``  |-> mk_register (#CRn y),
             ``crm:word4``  |-> mk_register (#CRm y),
             ``cop2:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop2 y))]
      ``instruction$CDP c cpn cop1 crd crn crm cop2``
  | _ => raise ERR "mk_cdp" "not a cdp instruction")
 | mk_cdp _ = raise ERR "mk_cdp" "not a cdp instruction";

fun mk_mcr_mrc (Instruction(x,c)) =
 (case x of
    Mcr_mrc y =>
      subst [``c:condition`` |-> mk_condition c,
             ``cpn:word4``  |-> mk_word4 (Arbnum.fromInt (#CP y)),
             ``cop1:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop1 y)),
             ``rd:word4``   |-> mk_register (#Rd y),
             ``crn:word4``  |-> mk_register (#CRn y),
             ``crm:word4``  |-> mk_register (#CRm y),
             ``cop2:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop2 y))]
      (if #L y then
         ``instruction$MRC c cpn cop1 rd crn crm cop2``
       else
         ``instruction$MCR c cpn cop1 rd crn crm cop2``)
  | _ => raise ERR "mk_mcr_mrc" "not an mcr or mrc instruction")
 | mk_mcr_mrc _ = raise ERR "mk_mcr_mrc" "not an mcr or mrc instruction";

local
  fun mk_options (Ldc_stc y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldc_stc" "not an ldc or stc instruction"
  val err = ERR "mk_ldc_stc" "not an ldc or stc instruction"
in
  fun mk_ldc_stc (Instruction(x,c)) =
   (case x of
      Ldc_stc y =>
        subst [``c:condition`` |-> mk_condition c,
               ``n:bool`` |-> mk_bool (#N y),
               ``opt:transfer_options`` |-> mk_options x,
               ``cpn:word4``   |-> mk_word4 (Arbnum.fromInt (#CP y)),
               ``crd:word4``   |-> mk_register (#CRd y),
               ``rn:word4``    |-> mk_register (#Rn y),
               ``offset:word8`` |-> mk_word8 (Arbnum.fromInt (#offset y))]
        (if #L y then
           ``instruction$LDC c n opt cpn crd rn offset``
         else
           ``instruction$STC c n opt cpn crd rn offset``)
    | _ => raise err)
  | mk_ldc_stc _ = raise err
end;

fun mk_undef c = subst [``c:condition`` |-> mk_condition c] ``UND c``;

(* ------------------------------------------------------------------------- *)

fun arm_to_term (i as Instruction (x,c)) =
 (case x of
    Br y        => mk_br i
  | Swi_ex      => mk_swi_ex c
  | Data_proc y => mk_data_proc i
  | Mla_mul y   => mk_mla_mul i
  | Ldr_str y   => mk_ldr_str i
  | Ldrh_strh y => mk_ldrh_strh i
  | Ldm_stm y   => mk_ldm_stm i
  | Swp y       => mk_swp i
  | Mrs y       => mk_mrs i
  | Msr y       => mk_msr i
  | Cdp y       => mk_cdp i
  | Mcr_mrc y   => mk_mcr_mrc i
  | Ldc_stc y   => mk_ldc_stc i
  | Undef       => mk_undef c)
 | arm_to_term (Data n) = mk_word32 n;

(* ------------------------------------------------------------------------- *)

fun index_size t = let open Arbnum in
   if t = ``:3`` then fromInt 8 else
   if t = ``:4`` then fromInt 16 else
   if t = ``:5`` then fromInt 32 else
   if t = ``:8`` then fromInt 256 else
   if t = ``:12`` then fromInt 4096 else
   if t = ``:16`` then fromInt 65536 else
   if t = ``:24`` then fromInt 16777216 else
   if t = ``:32`` then fromString "4294967296" else
    raise ERR "index_mod_size" "unknown word size"
end;

fun dest_word t = let val (n,typ) = dest_n2w t in
  Arbnum.mod(numLib.dest_numeral n,index_size typ) end;

val dest_wordi  = Arbnum.toInt o dest_word;

fun dest_register t = NReg (int2register (dest_wordi t))
  handle HOL_ERR e =>
    let val (x, t) = dest_var t in
      if t = ``:word4`` then VReg x else Raise (HOL_ERR e)
    end;

fun dest_bool t =
  if term_eq t T then true else
  if term_eq t F then false else
    raise ERR "dest_bool" "neither T nor F";

fun dest_condition t = let val eqt = term_eq t
in
  if eqt ``EQ`` then EQ else
  if eqt ``NE`` then NE else
  if eqt ``CS`` then CS else
  if eqt ``CC`` then CC else
  if eqt ``MI`` then MI else
  if eqt ``PL`` then PL else
  if eqt ``VS`` then VS else
  if eqt ``VC`` then VC else
  if eqt ``HI`` then HI else
  if eqt ``LS`` then LS else
  if eqt ``GE`` then GE else
  if eqt ``LT`` then LT else
  if eqt ``GT`` then GT else
  if eqt ``LE`` then LE else
  if eqt ``AL`` then AL else
  if eqt ``NV`` then NV else
    raise ERR "dest_condition" "not an instance of :condition"
end;

local
  val err = ERR "dest_br" "not a variable-free branch instruction"
in
  fun dest_br t =
   (case strip_comb t of
      (i, [c, offset]) => let val l = term_eq i ``instruction$BL`` in
          if l orelse term_eq i ``instruction$B`` then
            Instruction(Br {L = l,offset = dest_wordi offset},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_swi_ex" "not a valid swi_ex instruction"
in
  fun dest_swi_ex t =
  let val (i,c) = dest_comb t in
     if term_eq i ``instruction$SWI`` then
       Instruction(Swi_ex, dest_condition c)
     else
       raise err
  end handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_undef" "not a valid undefined instruction"
in
  fun dest_undef t =
  let val (i,c) = dest_comb t in
     if term_eq i ``instruction$UND`` then
       Instruction(Undef, dest_condition c)
     else
       raise err
  end handle HOL_ERR _ => raise err
end;

fun dest_opc1 t = let val eqt = term_eq t
in
  if eqt ``instruction$AND`` then AND else
  if eqt ``instruction$EOR`` then EOR else
  if eqt ``instruction$SUB`` then SUB else
  if eqt ``instruction$RSB`` then RSB else
  if eqt ``instruction$ADD`` then ADD else
  if eqt ``instruction$ADC`` then ADC else
  if eqt ``instruction$SBC`` then SBC else
  if eqt ``instruction$RSC`` then RSC else
  if eqt ``instruction$ORR`` then ORR else
  if eqt ``instruction$BIC`` then BIC else raise ERR "dest_opc1"
     "term is not: AND, EOR, SUB, RSB, ADD, ADC, SBC, RSC, ORR or BIC"
end;

fun dest_opc2 t = let val eqt = term_eq t
in
  if eqt ``instruction$TST`` then TST else
  if eqt ``instruction$TEQ`` then TEQ else
  if eqt ``instruction$CMP`` then CMP else
  if eqt ``instruction$CMN`` then CMN else
    raise ERR "dest_opc2" "term is not: TST, TEQ, CMP or CMN"
end;

fun dest_opc3 t =
  if term_eq t ``instruction$MOV`` then MOV else
  if term_eq t ``instruction$MVN`` then MVN else
    raise ERR "dest_opc3" "term is not: MOV or MVN";

fun dest_shift t =
let val (s,r) = dest_comb t in
  if term_eq s ``instruction$LSL`` then (LSL, dest_register r) else
  if term_eq s ``instruction$LSR`` then (LSR, dest_register r) else
  if term_eq s ``instruction$ASR`` then (ASR, dest_register r) else
  if term_eq s ``instruction$ROR`` then (ROR, dest_register r) else
    raise ERR "dest_shift" "not a valid term of type :shift"
end;

local
  val err = ERR "dest_addr_mode1" "not a valid instance of :addr_mode1"
in
  fun dest_addr_mode1 t =
    case strip_comb t of
      (m, [x, y]) =>
        if term_eq m ``Dp_immediate`` then
          DpImmediate (mk_immediate (dest_wordi x) (dest_word y))
        else let val (s,rm) = dest_shift x in
          if term_eq m ``Dp_shift_immediate`` then
            DpShiftImmediate {Imm = dest_wordi y, Sh = s, Rm = rm}
          else if term_eq m ``Dp_shift_register`` then
            DpShiftRegister {Rs = dest_register y, Sh = s, Rm = rm}
          else raise err
        end
    | _ => raise err
end;

local
  val err = ERR "dest_data_proc" "not a variable-free data_proc instruction"
in
  fun dest_data_proc t =
   (case strip_comb t of
      (opc, [c,s,rd,rn,op2]) =>
         Instruction(Data_proc {opc = dest_opc1 opc, S = dest_bool s,
           Rd = dest_register rd, Rn = dest_register rn,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | (opc, [c,rn,op2]) =>
         Instruction(Data_proc {opc = dest_opc2 opc, S = true,
           Rd = NReg R0, Rn = dest_register rn,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | (opc, [c,s,rd,op2]) =>
         Instruction(Data_proc {opc = dest_opc3 opc, S = dest_bool s,
           Rd = dest_register rd, Rn = NReg R0,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mla_mul" "not a variable-free multiply instruction"
in
  fun dest_mla_mul t =
   (case strip_comb t of
      (i, [c,s,rd,rm,rs]) =>
         if term_eq i ``instruction$MUL`` then
           Instruction(Mla_mul {L = false, Signed = false,
             A = false, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rm,
             Rs = dest_register rs, Rn = NReg R0},dest_condition c)
         else
           raise err
    | (i, [c,s,rd,rm,rs,rn]) =>
         if term_eq i ``instruction$MLA`` then
           Instruction(Mla_mul {L = false, Signed = false,
             A = true, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rm,
             Rs = dest_register rs, Rn = dest_register rn},dest_condition c)
         else if term_eq i ``instruction$UMULL`` then
           Instruction(Mla_mul {L = true, Signed = false,
             A = false, S = dest_bool s,
             Rd = dest_register rm, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rd},dest_condition c)
         else if term_eq i ``instruction$UMLAL`` then
           Instruction(Mla_mul {L = true, Signed = false,
             A = true, S = dest_bool s,
             Rd = dest_register rm, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rd},dest_condition c)
         else if term_eq i ``instruction$SMULL`` then
           Instruction(Mla_mul {L = true, Signed = true,
             A = false, S = dest_bool s,
             Rd = dest_register rm, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rd},dest_condition c)
         else if term_eq i ``instruction$SMLAL`` then
           Instruction(Mla_mul {L = true, Signed = true,
             A = true, S = dest_bool s,
             Rd = dest_register rm, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rd},dest_condition c)
         else
           raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

fun dest_options t =
  case snd (TypeBase.dest_record t) of
    [("Pre", p), ("Up", u), ("Wb", w)] =>
       (dest_bool p, dest_bool u, dest_bool w)
  | _ => raise ERR "dest_options" "not an instance of type :transfer_options";

local
  val err = ERR "dest_addr_mode2" "not a valid instance of :addr_mode2"
in
  fun dest_addr_mode2 t =
   (case strip_comb t of
      (m, [n]) =>
        if term_eq m ``Dt_immediate`` then
          DtImmediate (dest_wordi n)
        else
          raise err
    | (m, [sh, i]) =>
        if term_eq m ``Dt_shift_immediate`` then
          let val (s,rm) = dest_shift sh in
            DtShiftImmediate {Imm = dest_wordi i, Sh = s, Rm = rm}
          end
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldr_str" "not a variable-free load/store instruction"
in
  fun dest_ldr_str t =
   (case strip_comb t of
      (i, [c,b,opt,rd,rn,offset]) =>
        let val l = term_eq i ``instruction$LDR``
            val (p,u,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STR`` then
            Instruction(Ldr_str {L = l,offset = dest_addr_mode2 offset,
              Rd = dest_register rd, Rn = dest_register rn,
              P = p, U = u, B = dest_bool b, W = w},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_addr_mode3" "not a valid instance of :addr_mode3"
in
  fun dest_addr_mode3 t =
   (case strip_comb t of
      (m, [n]) =>
        if term_eq m ``Dth_immediate`` then
          DthImmediate (dest_wordi n)
        else if term_eq m ``Dth_register`` then
          DthRegister (dest_register n)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldr_str" "not a variable-free load/store instruction"
in
  fun dest_ldrh_strh t =
   (case strip_comb t of
      (i, [c,s,h,opt,rd,rn,offset]) =>
        let val (p,u,w) = dest_options opt in
          if term_eq i ``instruction$LDRH`` then
            Instruction(Ldrh_strh {L = true,offset = dest_addr_mode3 offset,
              Rd = dest_register rd, Rn = dest_register rn, P = p, U = u,
              W = w, S = dest_bool s, H = dest_bool h},dest_condition c)
          else
            raise err
        end
    | (i, [c,opt,rd,rn,offset]) =>
        let val (p,u,w) = dest_options opt in
          if term_eq i ``instruction$STRH`` then
            Instruction(Ldrh_strh {L = false,offset = dest_addr_mode3 offset,
              Rd = dest_register rd, Rn = dest_register rn,
              P = p, U = u, W = w, S = false, H = true},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldm_stm" "not a variable-free block transfer instruction"
in
  fun dest_ldm_stm t =
   (case strip_comb t of
      (i, [c,s,opt,rn,list]) =>
        let val l = term_eq i ``instruction$LDM``
            val (p,u,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STM`` then
            Instruction(Ldm_stm {L = l,list = dest_wordi list,
              Rn = dest_register rn, P = p, U = u, S = dest_bool s, W = w},
              dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_swp" "not a variable-free swap instruction"
in
  fun dest_swp t =
   (case strip_comb t of
      (i, [c,b,rd,rm,rn]) =>
        if term_eq i ``instruction$SWP`` then
          Instruction(Swp {B = dest_bool b,Rd = dest_register rd,
            Rm = dest_register rm, Rn = dest_register rn},dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mrs" "not a variable-free mrs instruction"
in
  fun dest_mrs t =
   (case strip_comb t of
      (i, [c,r,rd]) =>
        if term_eq i ``instruction$MRS`` then
          Instruction(Mrs {R = dest_bool r,Rd = dest_register rd},
            dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

fun dest_msr_psr t = let val eqt = term_eq t
in
  if eqt ``CPSR_c`` then (false,false,true) else
  if eqt ``CPSR_f`` then (false,true,false) else
  if eqt ``CPSR_a`` then (false,true,true) else
  if eqt ``SPSR_c`` then (true,false,true) else
  if eqt ``SPSR_f`` then (true,true,false) else
  if eqt ``SPSR_a`` then (true,true,true) else
    raise ERR "dest_msr_psr" "not a valid instance of :msr_psr"
end;

local
  val err = ERR "dest_addr_mode1" "not a valid instance of :msr_mode"
in
  fun dest_msr_mode t =
   (case strip_comb t of
      (m, [x, y]) =>
        if term_eq m ``Msr_immediate`` then
          MsrImmediate (mk_immediate (dest_wordi x) (dest_word y))
        else
          raise err
    | (m, [x]) =>
        if term_eq m ``Msr_register`` then
          MsrRegister (dest_register x)
        else
          raise err
    | _ => raise err) handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_msr" "not a variable-free mrs instruction"
in
  fun dest_msr t =
   (case strip_comb t of
      (i, [c,psrd,opnd]) =>
        if term_eq i ``instruction$MSR`` then
          let val (r,b19,b16) = dest_msr_psr psrd in
            Instruction(Msr {R = r, bit19 = b19, bit16 = b16,
              Op = dest_msr_mode opnd},dest_condition c)
          end
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_cdp" "not a variable-free cdp instruction"
in
  fun dest_cdp t =
   (case strip_comb t of
      (i, [c,cpn,cop1,crd,crn,crm,cop2]) =>
        if term_eq i ``instruction$CDP`` then
          Instruction(Cdp {CP = dest_wordi cpn, CRd = dest_register crd,
            CRn = dest_register crn, CRm = dest_register crm,
            Cop1 = dest_wordi cop1, Cop2 = dest_wordi cop2},dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldc_stc" "not a variable-free ldc/stc instruction"
in
  fun dest_ldc_stc t =
   (case strip_comb t of
      (i, [c,n,opt,cpn,crd,rn,offset]) =>
        let val l = term_eq i ``instruction$LDC``
            val (p,u,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STC`` then
            Instruction(Ldc_stc {CP = dest_wordi cpn, CRd = dest_register crd,
              L = l, P = p, U = u, N = dest_bool n, W = w,
              Rn = dest_register rn, offset = dest_wordi offset},
             dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mcr_mrc" "not a variable-free mcr/mrc instruction"
in
  fun dest_mcr_mrc t =
   (case strip_comb t of
      (i, [c,cpn,cop1,rd,crn,crm,cop2]) =>
        let val l = term_eq i ``instruction$MCR`` in
          if l orelse term_eq i ``instruction$MRC`` then
            Instruction(Mcr_mrc {CP = dest_wordi cpn, L = l,
              CRn = dest_register crn, CRm = dest_register crm,
              Rd = dest_register rd, Cop1 = dest_wordi cop1,
              Cop2 = dest_wordi cop2},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

(* ------------------------------------------------------------------------- *)

fun term_to_arm t =
  if type_of t = ``:word32`` then
    Data (dest_word t)
  else let val opc = fst (strip_comb t)
           val eqt = term_eq opc
  in
    if eqt ``instruction$SWI`` then
      dest_swi_ex t
    else if eqt ``instruction$B`` orelse eqt ``instruction$BL`` then
      dest_br t
    else if eqt ``instruction$MUL`` orelse eqt ``instruction$MLA`` orelse
            eqt ``instruction$UMULL`` orelse eqt ``instruction$UMLAL`` orelse
            eqt ``instruction$SMULL`` orelse eqt ``instruction$SMLAL`` then
      dest_mla_mul t
    else if eqt ``instruction$LDRH`` orelse eqt ``instruction$STRH`` then
      dest_ldrh_strh t
    else if eqt ``instruction$LDR`` orelse eqt ``instruction$STR`` then
      dest_ldr_str t
    else if eqt ``instruction$LDM`` orelse eqt ``instruction$STM`` then
      dest_ldm_stm t
    else if eqt ``instruction$SWP`` then
      dest_swp t
    else if eqt ``instruction$MRS`` then
      dest_mrs t
    else if eqt ``instruction$MSR`` then
      dest_msr t
    else if eqt ``instruction$CDP`` then
      dest_cdp t
    else if eqt ``instruction$LDC`` orelse eqt ``instruction$STC`` then
      dest_ldc_stc t
    else if eqt ``instruction$MCR`` orelse eqt ``instruction$MRC`` then
      dest_mcr_mrc t
    else if eqt ``instruction$UND`` then
      dest_undef t
    else
      dest_data_proc t
  end
handle HOL_ERR _ =>
  raise ERR "term_to_arm" "not a variable-free ARM instruction";

(* ------------------------------------------------------------------------- *)

val encode_instruction = arm_to_num o term_to_arm;
val decode_instruction = arm_to_term o num_to_arm;
val decode_instruction_dec = decode_instruction o Arbnum.fromString;
val decode_instruction_hex = decode_instruction o Arbnum.fromHexString;

val mk_instruction = arm_to_term o string_to_arm;
fun dest_instruction i t = arm_to_string i false (term_to_arm t);

(* ------------------------------------------------------------------------- *)
end;
