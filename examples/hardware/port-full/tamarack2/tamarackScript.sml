(* ===================================================================== *)
(* April 2018 - Updated to HOL 4, Ramana Kumar, Thomas Tuerk             *)

(* ===================================================================== *)
(* 14 June 1989 - modified for HOL88                                     *)
(*                                                                       *)
(* ===================================================================== *)
(* Jeff Joyce, University of Cambridge, 1 November 1988                  *)
(*                                                                       *)
(* Specify register-transfer level implementation and functional         *)
(* behaviour of a very simple microprocessor.                            *)

open HolKernel boolLib bossLib Parse

open arithmeticTheory stringTheory

val _ = new_theory "tamarack";

val _ = loose_equality()

(* ----------------------------- *)
(* - Definitions               - *)
(* ----------------------------- *)

Type time = “:num”
Type wire = “:time->bool”
Type bus = “:time->num”
Type mem = “:time->num->num”

Definition INCn_def: INCn n a = (a + 1) MOD (2 EXP n)
End
Definition SUBn_def: SUBn n (a,b) = (a + b) MOD (2 EXP n)
End
Definition ADDn_def: ADDn n (a,b) = (a + b) MOD (2 EXP n)
End

Definition Bits_def: Bits (n,m) w = (w DIV (2 EXP n)) MOD (2 EXP m)
End

Definition Update_def: Update (s:'a->'b,x,y) = (x =+ y) s
End

Definition PWR_def: PWR (w:wire) = !t. w t = T
End

Definition GND_def: GND (w:wire) = !t. w t = F
End

Definition AND_def: AND (a:wire,b:wire,out:wire) = !t. out t = a t /\ b t
End

Definition OR_def: OR (a:wire,b:wire,out:wire) = !t. out t = a t \/ b t
End

Definition MUX_def:
  MUX (cntl:wire,a:bus,b:bus,out:bus) =
  !t. out t = (if cntl t then b t else a t)
End

Definition BITS_def:
  BITS (n,m) (inp:bus,out:bus) = !t. out t = Bits (n,m) (inp t)
End

Definition TNZ_def: TNZ (inp:bus,flag:wire) = !t. flag t <=> inp t <> 0
End

Definition HWC_def: HWC c (b:bus) = !t. b t = c
End

Definition ADDER_def:
  ADDER n (a:bus,b:bus,out:bus) = !t. out t = ADDn n (a t,b t)
End

Definition ALU_def:
  ALU n (f0:wire,f1:wire,a:bus,b:bus,out:bus) =
  !t.
    ?w.
      out t =
      if ((f0 t,f1 t) = (T,T)) then w
      else if ((f0 t,f1 t) = (F,T)) then INCn n (b t)
      else if ((f0 t,f1 t) = (F,F)) then ADDn n (a t,b t)
      else SUBn n (a t,b t)
End

Definition DEL_def: DEL (inp:bus,out:bus) = !t. out (t+1) = inp t
End

Definition REG_def:
  REG ((w:wire,r:wire,inp:bus,bus:bus,out:bus),P) =
  !t.
    (out (t+1) = (if w t then inp t else out t)) /\
    (P t ==> r t ==> (bus t = out t))
End

Definition MEM_def:
  MEM n ((w:wire,r:wire,addr:bus,bus:bus),(P,mem:mem)) =
  !t.
    (mem (t+1) = (if w t then Update (mem t,addr t,bus t) else mem t)) /\
    (P t ==> r t ==> (bus t = mem t (addr t)))
End

Definition CheckCntls_def:
  CheckCntls (rmem,rpc,racc,rir,rbuf,P) =
  !t.
    P t =
    if rmem t then ~(rpc t \/ racc t \/ rir t \/ rbuf t)
    else if rpc t  then ~(racc t \/ rir t \/ rbuf t)
    else if racc t then ~(rir t \/ rbuf t)
    else if rir t  then ~rbuf t
    else T
End

Definition DataPath_def:
  DataPath n
  ((wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
    zeroflag,opcode),
   (mem,mar,pc,acc,ir,arg,buf)) <=>
  ?P bus addr alu pwr gnd.
    CheckCntls (rmem,rpc,racc,rir,rbuf,P) /\
    MEM n ((wmem,rmem,addr,bus),(P,mem)) /\
    REG ((wmar,gnd,bus,bus,mar),P) /\
    BITS (0,n) (mar,addr) /\
    REG ((wpc,rpc,bus,bus,pc),P) /\
    REG ((wacc,racc,bus,bus,acc),P) /\
    TNZ (acc,zeroflag) /\
    REG ((wir,rir,bus,bus,ir),P) /\
    BITS (n,3) (ir,opcode) /\
    REG ((warg,gnd,bus,bus,arg),P) /\
    ALU (n+3) (alu0,alu1,arg,bus,alu) /\
    REG ((pwr,rbuf,alu,bus,buf),P) /\
    PWR pwr /\
    GND gnd
End

Definition Cntls_def:
  Cntls (tok1,tok2) =
  (tok2 = "wmem", tok1 = "rmem", tok2 = "wmar", tok2 = "wpc", tok1 = "rpc",
   tok2 = "wacc", tok1 = "racc", tok2 = "wir", tok1 = "rir", tok2 = "warg",
   tok2 = "sub", tok2 = "inc", tok1 = "rbuf")
End

Definition NextMpc_def:
  NextMpc (tok,addr:num) =
  if tok = "jop" then ((T,F),addr)
  else if tok = "jnz" then ((F,T),addr)
  else if tok = "jmp" then ((T,T),addr)
  else ((F,F),addr)
End

Definition Microcode_def:
  (Microcode 0  = (Cntls ("rpc","wmar"),  NextMpc ("inc",0)) ) /\
  (Microcode 1  = (Cntls ("rmem","wir"),  NextMpc ("inc",0)) ) /\
  (Microcode 2  = (Cntls ("rir","wmar"),  NextMpc ("jop",0)) ) /\
  (Microcode 3  = (Cntls ("none","none"), NextMpc ("jnz",10))) /\ (* JZR *)
  (Microcode 4  = (Cntls ("rir","wpc"),   NextMpc ("jmp",0)) ) /\ (* JMP *)
  (Microcode 5  = (Cntls ("racc","warg"), NextMpc ("jmp",12))) /\ (* ADD *)
  (Microcode 6  = (Cntls ("racc","warg"), NextMpc ("jmp",13))) /\ (* SUB *)
  (Microcode 7  = (Cntls ("rmem","wacc"), NextMpc ("jmp",10))) /\ (* LD  *)
  (Microcode 8  = (Cntls ("racc","wmem"), NextMpc ("jmp",10))) /\ (* ST  *)
  (Microcode 9  = (Cntls ("none","none"), NextMpc ("inc",0)) ) /\ (* NOP *)
  (Microcode 10 = (Cntls ("rpc","inc"),   NextMpc ("inc",0)) ) /\ (* NOP *)
  (Microcode 11 = (Cntls ("rbuf","wpc"),  NextMpc ("jmp",0)) ) /\
  (Microcode 12 = (Cntls ("rmem","add"),  NextMpc ("jmp",14))) /\
  (Microcode 13 = (Cntls ("rmem","sub"),  NextMpc ("inc",0)) ) /\
  (Microcode 14 = (Cntls ("rbuf","wacc"), NextMpc ("jmp",10))) /\
  (Microcode _  = (Cntls ("none","none"), NextMpc ("jmp",0)))
End


val miw_ty = ty_antiq (hd (tl (snd (dest_type (type_of “Microcode”)))));

val ROM_def = Define ‘
        ROM contents (addr:bus,data:time->^miw_ty) =
          !t. data t = contents (addr t)’;

val Decoder_def = Define
         ‘Decoder (
          miw:time->^miw_ty,test0,test1,addr,
          wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) =
          !t.
            ((wmem t,rmem t,wmar t,wpc t,rpc t,wacc t,
              racc t,wir t,rir t,warg t,alu0 t,alu1 t,rbuf t),
             ((test0 t,test1 t),addr t)) =
            miw t’;

val MpcUnit_def = Define
         ‘MpcUnit (test0,test1,zeroflag,opcode,addr,mpc) =
          ?w1 w2 const0 const1 const3 b1 b2 b3 b4 b5.
            AND (test1,zeroflag,w1) /\
            OR (test0,w1,w2) /\
            MUX (test1,opcode,addr,b1) /\
            MUX (w2,mpc,b1,b2) /\
            HWC 0 const0 /\
            HWC 3 const3 /\
            MUX (test1,const3,const0,b3) /\
            HWC 1 const1 /\
            MUX (w2,const1,b3,b4) /\
            ADDER 4 (b2,b4,b5) /\
            DEL (b5,mpc)’;

val CntlUnit_def = Define
         ‘CntlUnit (
          (zeroflag,opcode,
           wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
          mpc) =
          ?miw test0 test1 addr.
            ROM Microcode (mpc,miw) /\
            Decoder (
              miw,test0,test1,addr,
              wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) /\
            MpcUnit (test0,test1,zeroflag,opcode,addr,mpc)’;

val Tamarack_def = Define
         ‘Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) =
          ?zeroflag opcode
           wmem rmem wmar wpc rpc wacc racc wir rir warg alu0 alu1 rbuf.
            CntlUnit (
              (zeroflag,opcode,
               wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
              (mpc)) /\
            DataPath n (
              (wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
               zeroflag,opcode),
              (mem,mar,pc,acc,ir,arg,buf))’;

val Inst_def = Define ‘Inst n (mem:num->num,pc) = mem (pc MOD (2 EXP n))’;

val Opc_def = Define ‘Opc n inst = ((inst DIV (2 EXP n)) MOD (2 EXP 3))’;

val Addr_def = Define ‘Addr n inst = (inst MOD (2 EXP n))’;

val NextState_def = Define ‘
          NextState n (mem,pc,acc) =
          let inst = Inst n (mem,pc) in
          let opc = Opc n inst in
          let addr = Addr n inst in
          (if (opc = 0) then (mem,(if (acc = 0) then inst else (INCn (n+3) pc)),acc) else
           if (opc = 1) then (mem,inst,acc) else
           if (opc = 2) then (mem,(INCn (n+3) pc),(ADDn (n+3) (acc,mem addr))) else
           if (opc = 3) then (mem,(INCn (n+3) pc),(SUBn (n+3) (acc,mem addr))) else
           if (opc = 4) then (mem,(INCn (n+3) pc),mem addr) else
           if (opc = 5) then (Update (mem,addr,acc),(INCn (n+3) pc),acc) else
                             (mem,(INCn (n+3) pc),acc))’;

val Behaviour_def = Define
        ‘Behaviour n (mem,pc,acc) =
          !t.
            (mem (t+1),pc (t+1),acc (t+1)) =
              NextState n (mem t,pc t,acc t)’;

val MicroCycles_def = Define
         ‘MicroCycles n (mem,pc,acc) =
          let opc = Opc n (Inst n (mem,pc)) in
          (if (opc = 0) then (if (acc = 0) then 5 else 6) else
           if (opc = 1) then 4 else
           if (opc = 2) then 8 else
           if (opc = 3) then 8 else
           if (opc = 4) then 6 else
           if (opc = 5) then 6 else
           if (opc = 6) then 6 else
                             5)’;

val REV_TimeOfCycle_def = Define ‘
  (REV_TimeOfCycle 0 n mem pc acc = 0) /\
  (REV_TimeOfCycle (SUC t) n mem pc acc =
     let prev = (REV_TimeOfCycle t n mem pc acc) in
     (prev + (MicroCycles n (mem prev,pc prev,acc prev))))’;

val TimeOfCycle_def = Define ‘
  TimeOfCycle n (mem,pc,acc) t = REV_TimeOfCycle t n mem pc acc’;



(* --------------------------- *)
(* - Proofs 1                - *)
(* --------------------------- *)

(* Evaluation theorem.
   One can first evaluate via e.g.

   LIST_CONJ (map (CONV_RULE (RHS_CONV EVAL)) (BODY_CONJUNCTS Microcode_def))

   and then copy the result, massage it a bit and finally state it
   explicitly. That way one can increase robustness. *)
Theorem Microcode_EVALS:
  (Microcode 0 = ((F,F,T,F,T,F,F,F,F,F,F,F,F),(F,F),0)) /\
  (Microcode 1 = ((F,T,F,F,F,F,F,T,F,F,F,F,F),(F,F),0)) /\
  (Microcode 2 = ((F,F,T,F,F,F,F,F,T,F,F,F,F),(T,F),0)) /\
  (Microcode 3 = ((F,F,F,F,F,F,F,F,F,F,F,F,F),(F,T),10)) /\
  (Microcode 4 = ((F,F,F,T,F,F,F,F,T,F,F,F,F),(T,T),0)) /\
  (Microcode 5 = ((F,F,F,F,F,F,T,F,F,T,F,F,F),(T,T),12)) /\
  (Microcode 6 = ((F,F,F,F,F,F,T,F,F,T,F,F,F),(T,T),13)) /\
  (Microcode 7 = ((F,T,F,F,F,T,F,F,F,F,F,F,F),(T,T),10)) /\
  (Microcode 8 = ((T,F,F,F,F,F,T,F,F,F,F,F,F),(T,T),10)) /\
  (Microcode 9 = ((F,F,F,F,F,F,F,F,F,F,F,F,F),(F,F),0)) /\
  (Microcode 10 = ((F,F,F,F,T,F,F,F,F,F,F,T,F),(F,F),0)) /\
  (Microcode 11 = ((F,F,F,T,F,F,F,F,F,F,F,F,T),(T,T),0)) /\
  (Microcode 12 = ((F,T,F,F,F,F,F,F,F,F,F,F,F),(T,T),14)) /\
  (Microcode 13 = ((F,T,F,F,F,F,F,F,F,F,T,F,F),(F,F),0)) /\
  (Microcode 14 = ((F,F,F,F,F,T,F,F,F,F,F,F,T),(T,T),10)) /\
  (Microcode 15 = ((F,F,F,F,F,F,F,F,F,F,F,F,F),(T,T),0)) /\
  !v. v <> 0 /\ v <> 1 /\ v <> 2 /\ v <> 3 /\ v <> 4 /\ v <> 5 /\ v <> 6 /\
      v <> 7 /\ v <> 8 /\ v <> 9 /\ v <> 10 /\ v <> 11 /\ v <> 12 /\
      v <> 13 /\ v <> 14 ==>
      (Microcode v = ((F,F,F,F,F,F,F,F,F,F,F,F,F),(T,T),0))
Proof
  EVAL_TAC >> SIMP_TAC std_ss []
QED


(* The following tactics correspond to the sequence of steps which take
   place when a microinstruction is executed:

   tac1 - produce microcode ROM output;
   tac2 - generate next mpc state;
   tac3 - generate next data path state.
 *)

val tac1 : tactic =
  PURE_REWRITE_TAC [Tamarack_def, CntlUnit_def, ROM_def] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_THEN (MP_TAC o (SPEC “t:time”)) (fst (EQ_IMP_RULE (SPEC_ALL Decoder_def))) THEN
  ASM_REWRITE_TAC [Microcode_EVALS, pairTheory.PAIR_EQ] THEN
  STRIP_TAC

val tac2 : tactic =
  IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE (SPEC_ALL MpcUnit_def))) THEN
  PURE_ONCE_REWRITE_TAC [AND_def,OR_def,MUX_def,HWC_def,ADDER_def,DEL_def] THEN
  DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) (fn thm => REWRITE_TAC [thm])) THEN
  ASM_REWRITE_TAC [];

val tac3 : tactic =
  IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE (SPEC_ALL DataPath_def))) THEN
  PURE_ONCE_REWRITE_TAC [CheckCntls_def,MEM_def,REG_def,BITS_def,TNZ_def,ALU_def,PWR_def,GND_def] THEN
  DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) MP_TAC) THEN
  DISCH_THEN (MP_TAC o LIST_CONJ o (map (SPEC “t:time”)) o CONJUNCTS) THEN
  ASM_REWRITE_TAC [pairTheory.PAIR_EQ] THEN
  DISCH_THEN (fn thm => MP_TAC (REWRITE_RULE [CONJUNCT1 thm] (CONJUNCT2 thm))) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [];

(* Combined Tactic *)
val MPC_n_TAC =
  tac1 >> tac2 >> tac3 >>
  SIMP_TAC arith_ss [ADDn_def]

val MPC_0_THM = store_thm ("MPC_0_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1)) =
     (1,mem t,pc t,pc t,acc t))”,

  MPC_n_TAC
);


val MPC_1_THM = store_thm ("MPC_1_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 1) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     (2,mem t,pc t,acc t,mem t (Bits (0,n) (mar t))))”,

  MPC_n_TAC
);


val MPC_2_THM = store_thm ("MPC_2_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 2) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     ((Bits (n,3) (ir t)) + 3,mem t,ir t,pc t,acc t,ir t))”,

  MPC_n_TAC >>
  ‘Bits (n,3) (ir t) < 8’ by SIMP_TAC arith_ss [Bits_def] >>
  DECIDE_TAC
);



val MPC_3_THM = store_thm ("MPC_3_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 3) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     (((if ((acc t) = 0) then 4 else 10),mem t,pc t,acc t,ir t)))”,
  MPC_n_TAC
);


val MPC_4_THM = store_thm ("MPC_4_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 4) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,ir t,acc t))”,

  MPC_n_TAC
);


val MPC_5_THM = store_thm ("MPC_5_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 5) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
     (12,mem t,mar t,pc t,acc t,acc t))”,

  MPC_n_TAC
);


val MPC_6_THM = store_thm ("MPC_6_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 6) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
     (13,mem t,mar t,pc t,acc t,acc t))”,

  MPC_n_TAC
);


val MPC_7_THM = store_thm ("MPC_7_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 7) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,mem t (Bits (0,n) (mar t))))”,

  MPC_n_TAC
);


val MPC_8_THM = store_thm ("MPC_8_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 8) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,Update (mem t,Bits (0,n) (mar t),acc t),pc t,acc t))”,

  MPC_n_TAC
);


val MPC_9_THM = store_thm ("MPC_9_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 9) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,acc t))”,

  MPC_n_TAC
);



val MPC_10_THM = store_thm ("MPC_10_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 10) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (11,mem t,pc t,acc t,INCn (n+3) (pc t)))”,

  MPC_n_TAC
);


val MPC_11_THM = store_thm ("MPC_11_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 11) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,buf t,acc t))”,

  MPC_n_TAC
);


val MPC_12_THM = store_thm ("MPC_12_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 12) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (14,mem t,pc t,acc t,
      ADDn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))”,

  MPC_n_TAC
);


val MPC_13_THM = store_thm ("MPC_13_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 13) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (14,mem t,pc t,acc t,
      SUBn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))”,

  MPC_n_TAC);


val MPC_14_THM = store_thm ("MPC_14_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 14) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,buf t))”,

  MPC_n_TAC);


val MPC_15_THM = store_thm ("MPC_15_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 15) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,pc t,acc t))”,

  MPC_n_TAC);


(* Nowadays, we have much more computational power at our hands. We
   can therefore prove a stronger version of theorems MPC_0_THM - MPC_15_THM
   via brute force. The main idea is using Skolemization in reverse.
   Apart from that, it is unfolding and a little bit of simple reordering. *)

val Tamarack_EVAL_THM = store_thm ("Tamarack_EVAL_THM",
   “!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) <=>
          !t.
              if mpc t = 0 then
                (mpc (t + 1) = 1) /\ (mem (t + 1) = mem t) /\
                (pc (t + 1) = pc t) /\ (mar (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,mar (t + 1)))
              else if mpc t = 1 then
                (mpc (t + 1) = 2) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\
                (ir (t + 1) = mem t (Bits (0,n) (mar t))) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) =
                 ADDn (n + 3) (arg t,mem t (Bits (0,n) (mar t))))
              else if mpc t = 2 then
                (mpc (t + 1) = (Bits (n,3) (ir t) + 3)) /\
                (mem (t + 1) = mem t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (mar (t + 1) = ir t) /\ (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,mar (t + 1)))
              else if mpc t = 3 then
                (mpc (t + 1) = if acc t = 0 then 4 else 10) /\
                (mem (t + 1) = mem t) /\ (mar (t + 1) = mar t) /\
                (pc (t + 1) = pc t) /\ (acc (t + 1) = acc t) /\
                (ir (t + 1) = ir t) /\ (arg (t + 1) = arg t) /\
                ?bus. buf (t + 1) = ADDn (n + 3) (arg t,bus)
              else if mpc t = 4 then
                (mpc (t + 1) = 0) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (acc (t + 1) = acc t) /\
                (ir (t + 1) = ir t) /\ (pc (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,pc (t + 1)))
              else if mpc t = 5 then
                (mpc (t + 1) = 12) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = acc t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,acc t))
              else if mpc t = 6 then
                (mpc (t + 1) = 13) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = acc t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,acc t))
              else if mpc t = 7 then
                (mpc (t + 1) = 10) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = mem t (Bits (0,n) (mar t))) /\
                (ir (t + 1) = ir t) /\ (arg (t + 1) = arg t) /\
                (buf (t + 1) =
                 ADDn (n + 3) (arg t,mem t (Bits (0,n) (mar t))))
              else if mpc t = 8 then
                (mpc (t + 1) = 10) /\
                (mem (t + 1) = (Bits (0,n) (mar t) =+ acc t) (mem t)) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,acc t))
              else if mpc t = 9 then
                (mpc (t + 1) = 10) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                ?bus. buf (t + 1) = ADDn (n + 3) (arg t, bus)
              else if mpc t = 10 then
                (mpc (t + 1) = 11) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\ (buf (t + 1) = INCn (n + 3) (pc t))
              else if mpc t = 11 then
                (mpc (t + 1) = 0) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (acc (t + 1) = acc t) /\
                (ir (t + 1) = ir t) /\ (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,pc (t + 1))) /\
                (pc (t + 1) = buf t)
              else if mpc t = 12 then
                (mpc (t + 1) = 14) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) =
                 ADDn (n + 3) (arg t,mem t (Bits (0,n) (mar t))))
              else if mpc t = 13 then
                (mpc (t + 1) = 14) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                (buf (t + 1) =
                 SUBn (n + 3) (arg t,mem t (Bits (0,n) (mar t))))
              else if mpc t = 14 then
                (mpc (t + 1) = 10) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (ir (t + 1) = ir t) /\ (arg (t + 1) = arg t) /\
                (buf (t + 1) = ADDn (n + 3) (arg t,acc (t + 1))) /\
                (acc (t + 1) = buf t)
              else
                (mpc (t + 1) = 0) /\ (mem (t + 1) = mem t) /\
                (mar (t + 1) = mar t) /\ (pc (t + 1) = pc t) /\
                (acc (t + 1) = acc t) /\ (ir (t + 1) = ir t) /\
                (arg (t + 1) = arg t) /\
                ?bus. buf (t + 1) = ADDn (n + 3) (arg t,bus)”,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [Tamarack_def, CntlUnit_def,
  ROM_def, Decoder_def, MpcUnit_def, DataPath_def,
  AND_def, OR_def, MUX_def, HWC_def, MEM_def, ALU_def, REG_def,
  BITS_def, DEL_def, CheckCntls_def,
  ADDER_def, PWR_def, GND_def, TNZ_def,
  GSYM FORALL_AND_THM, PULL_EXISTS] >>
SIMP_TAC std_ss [GSYM SKOLEM_THM] >>
ConseqConv.CONSEQ_CONV_TAC (K ConseqConv.FORALL_EQ___CONSEQ_CONV) >>
SIMP_TAC pure_ss [prove (“(X:'a = if c then x1 else x2) <=> (if c then (X = x1) else (X = x2))”,
                   Cases_on ‘c’ >> REWRITE_TAC[])] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [Microcode_EVALS, ADDn_def,
  Update_def, GSYM PULL_EXISTS] >>
‘!n m. (Bits (n,3) m + 3) < 16’ by (
  REPEAT GEN_TAC >>
  ‘Bits (n, 3) m < 8’ by SIMP_TAC arith_ss [Bits_def] >>
  DECIDE_TAC
) >>
ASM_SIMP_TAC (arith_ss++boolSimps.LIFT_COND_ss) []);



(* --------------------------- *)
(* - Proofs 2                - *)
(* --------------------------- *)

fun EXEC_MPC_TAC tm =
  Q.PAT_ASSUM ‘Tamarack _ _’ (fn thm => let
    val thm0 = CONV_RULE (REWR_CONV Tamarack_EVAL_THM) thm
    val thm1 = SPEC tm thm0
  in MP_TAC thm1 end) >>
  SUBST1_TAC (SIMP_CONV arith_ss [] “^tm + 1”) >>
  ASM_SIMP_TAC std_ss [ADDn_def, Bits_def] >>
  STRIP_TAC

fun EXEC_MPC_TACn n = let
  fun mk_tm n = let val m = numLib.term_of_int n in “(t:time) + ^m” end
  val ns = Lib.for 0 (n-1) mk_tm
in
  EVERY (map EXEC_MPC_TAC ns)
end

fun EXEC_INST_FETCH_TAC n =
   SIMP_TAC arith_ss [Opc_def,Inst_def] >>
   REPEAT (FIRST [GEN_TAC,DISCH_THEN STRIP_ASSUME_TAC]) >>
   EXEC_MPC_TACn n


val JZR_T_INST_THM = store_thm ("JZR_T_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 0) /\
    (acc t = 0)
    ==>
    (mpc (t+5) = 0) /\
    ((mem (t+5),pc (t+5),acc (t+5)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 5 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def]);


val JZR_F_INST_THM = store_thm ("JZR_F_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 0) /\
    ~(acc t = 0)
    ==>
    (mpc (t+6) = 0) /\
    ((mem (t+6),pc (t+6),acc (t+6)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 6 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def]);


val JMP_INST_THM = store_thm ("JMP_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 1)
    ==>
    (mpc (t+4) = 0) /\
    ((mem (t+4),pc (t+4),acc (t+4)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 4 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def]);


val ADD_INST_THM = store_thm ("ADD_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 2)
    ==>
    (mpc (t+8) = 0) /\
    ((mem (t+8),pc (t+8),acc (t+8)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 8 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Addr_def]);


val SUB_INST_THM = store_thm ("SUB_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 3)
    ==>
    (mpc (t+8) = 0) /\
    ((mem (t+8),pc (t+8),acc (t+8)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 8 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Addr_def]);


val LD_INST_THM = store_thm ("LD_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 4)
    ==>
    (mpc (t+6) = 0) /\
    ((mem (t+6),pc (t+6),acc (t+6)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 6 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Update_def, Addr_def]);


val ST_INST_THM = store_thm ("ST_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 5)
    ==>
    (mpc (t+6) = 0) /\
    ((mem (t+6),pc (t+6),acc (t+6)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 6 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Update_def, Addr_def]);


val NOP1_INST_THM = store_thm ("NOP1_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 6)
    ==>
    (mpc (t+6) = 0) /\
    ((mem (t+6),pc (t+6),acc (t+6)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 6 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Update_def, Addr_def]);


val NOP2_INST_THM = store_thm ("NOP2_INST_THM",
“!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) /\
    (Opc n (Inst n (mem t,pc t)) = 7)
    ==>
    (mpc (t+5) = 0) /\
    ((mem (t+5),pc (t+5),acc (t+5)) =
      NextState n (mem t,pc t,acc t))”,

EXEC_INST_FETCH_TAC 5 >>
ASM_SIMP_TAC std_ss [NextState_def, LET_DEF, Inst_def, Opc_def,
  ADDn_def, Update_def, Addr_def]);


(* --------------------------- *)
(* - Proofs 3                - *)
(* --------------------------- *)

Definition MicroCycles_def[allow_rebind]:
  MicroCycles n (mem,pc,acc) =
  let opc = Opc n (Inst n (mem,pc)) in
  (if (opc = 0) then (if (acc = 0) then 5 else 6) else
   if (opc = 1) then 4 else
   if (opc = 2) then 8 else
   if (opc = 3) then 8 else
   if (opc = 4) then 6 else
   if (opc = 5) then 6 else
   if (opc = 6) then 6 else
                     5)
End

Definition TimeOfCycle_def[allow_rebind]:
  (TimeOfCycle n (mem,pc,acc) 0 = 0) /\
  (TimeOfCycle n (mem,pc,acc) (SUC t) =
     let prev = TimeOfCycle n (mem, pc, acc) t in
     (prev + (MicroCycles n (mem prev,pc prev,acc prev))))
End


Theorem EVERY_INST_THM:
  !n mpc mem mar pc acc ir arg buf.
    Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
    ==>
    !t.
      (mpc t = 0)
      ==>
      let m = MicroCycles n (mem t,pc t,acc t)
      in
        (mpc (t+m) = 0) /\
        ((mem (t+m),pc (t+m),acc (t+m)) = NextState n (mem t,pc t,acc t))
Proof
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC ‘opc = Opc n (Inst n (mem t,pc t))’ >>
  ASM_SIMP_TAC std_ss [MicroCycles_def, LET_DEF] >>
  ‘(opc = 0) \/ (opc = 1) \/ (opc = 2) \/ (opc = 3) \/
   (opc = 4) \/ (opc = 5) \/ (opc = 6) \/ (opc = 7)’
    by (‘opc < 8’ suffices_by DECIDE_TAC >>
        Q.UNABBREV_TAC ‘opc’ >>
        SIMP_TAC arith_ss [Opc_def]) >>
  ASM_SIMP_TAC std_ss [] >>
  metis_tac[JZR_T_INST_THM, JZR_F_INST_THM, JMP_INST_THM, ADD_INST_THM,
            SUB_INST_THM, LD_INST_THM, ST_INST_THM, NOP1_INST_THM,
            NOP2_INST_THM]
QED

Theorem ALWAYS_MPC_0_THM:
  !n mpc mem mar pc acc ir arg buf.
    Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
    (mpc 0 = 0)
    ==>
    !t. mpc (TimeOfCycle n (mem,pc,acc) t) = 0
Proof
  rpt strip_tac >> Induct_on ‘t’ >>
  metis_tac [EVERY_INST_THM, TimeOfCycle_def]
QED

Theorem CORRECTNESS_THM:
  !n mpc mem mar pc acc ir arg buf.
    Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
    (mpc 0 = 0)
    ==>
    let f = TimeOfCycle n (mem,pc,acc) in
      Behaviour n (mem o f,pc o f,acc o f)
Proof
  SIMP_TAC std_ss [Behaviour_def, LET_DEF, TimeOfCycle_def, GSYM ADD1] >>
  METIS_TAC[ALWAYS_MPC_0_THM, EVERY_INST_THM]
QED


val _ = export_theory ();
