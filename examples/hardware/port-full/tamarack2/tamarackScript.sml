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

val _ = type_abbrev ("time",``:num``);
val _ = type_abbrev ("wire",``:time->bool``);
val _ = type_abbrev ("bus",``:time->num``);
val _ = type_abbrev ("mem",``:time->num->num``);

val INCn_def = Define `INCn n a = (a + 1) MOD (2 EXP n)`;
val SUBn_def = Define `SUBn n (a,b) = (a + b) MOD (2 EXP n)`;
val ADDn_def = Define `ADDn n (a,b) = (a + b) MOD (2 EXP n)`;

val Bits_def = Define `Bits (n,m) w = ((w DIV (2 EXP n)) MOD (2 EXP m))`;

val Update_def = Define `Update (s:'a->'b,x,y) = (x =+ y) s`;

val PWR_def = Define `PWR (w:wire) = !t. w t = T`;

val GND_def = Define `GND (w:wire) = !t. w t = F`;

val AND_def = Define `AND (a:wire,b:wire,out:wire) = !t. out t = a t /\ b t`;

val OR_def = Define `OR (a:wire,b:wire,out:wire) = !t. out t = a t \/ b t`;

val MUX_def = Define `MUX (cntl:wire,a:bus,b:bus,out:bus) =
          !t. out t = (if cntl t then b t else a t)`;

val BITS_def = Define `BITS (n,m) (inp:bus,out:bus) = !t. out t = Bits (n,m) (inp t)`;

val TNZ_def = Define `TNZ (inp:bus,flag:wire) = !t. flag t = ~(inp t = 0)`;

val HWC_def = Define `HWC c (b:bus) = !t. b t = c`;

val ADDER_def = Define `ADDER n (a:bus,b:bus,out:bus) = !t. out t = ADDn n (a t,b t)`;

val ALU_def = Define `ALU n (f0:wire,f1:wire,a:bus,b:bus,out:bus) =
          !t.
            ?w.
              out t =
                (if ((f0 t,f1 t) = (T,T)) then w else
                 if ((f0 t,f1 t) = (F,T)) then INCn n (b t) else
                 if ((f0 t,f1 t) = (F,F)) then ADDn n (a t,b t) else
                                               SUBn n (a t,b t))`;

val DEL_def = Define `DEL (inp:bus,out:bus) = !t. out (t+1) = inp t`;

val REG_def = Define `REG ((w:wire,r:wire,inp:bus,bus:bus,out:bus),P) =
          !t.
            ((out (t+1) = (if w t then inp t else out t)) /\
             (P t ==> r t ==> (bus t = out t)))`;

val MEM_def = Define `MEM n ((w:wire,r:wire,addr:bus,bus:bus),(P,mem:mem)) =
          !t.
            (mem (t+1) = (if w t then Update (mem t,addr t,bus t) else mem t)) /\
            (P t ==> r t ==> (bus t = mem t (addr t)))`;

val CheckCntls_def = Define `CheckCntls (rmem,rpc,racc,rir,rbuf,P) =
          !t.
            P t =
              (if (rmem t) then (~(rpc t \/ racc t \/ rir t \/ rbuf t)) else
              (if (rpc t)  then (~(racc t \/ rir t \/ rbuf t)) else
              (if (racc t) then (~(rir t \/ rbuf t)) else
              (if (rir t)  then (~(rbuf t)) else T))))`;

val DataPath_def = Define `DataPath n (
          (wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
           zeroflag,opcode),
          (mem,mar,pc,acc,ir,arg,buf)) =
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
            GND gnd`;

val Cntls_def = Define `
        Cntls (tok1,tok2) =
          ((tok2 = "wmem"),
           (tok1 = "rmem"),
           (tok2 = "wmar"),
           (tok2 = "wpc"),
           (tok1 = "rpc"),
           (tok2 = "wacc"),
           (tok1 = "racc"),
           (tok2 = "wir"),
           (tok1 = "rir"),
           (tok2 = "warg"),
           (tok2 = "sub"),
           (tok2 = "inc"),
           (tok1 = "rbuf"))`;

val NextMpc_def = Define `NextMpc (tok,addr:num) =
          if (tok = "jop") then ((T,F),addr) else
          if (tok = "jnz") then ((F,T),addr) else
          if (tok = "jmp") then ((T,T),addr) else
                                ((F,F),addr)`;

val Microcode_def = Define `
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
          (Microcode 15 = (Cntls ("none","none"), NextMpc ("jmp",0)))`;

val miw_ty = ty_antiq (hd (tl (snd (dest_type (type_of ``Microcode``)))));

val ROM_def = Define `
        ROM contents (addr:bus,data:time->^miw_ty) =
          !t. data t = contents (addr t)`;

val Decoder_def = Define
         `Decoder (
          miw:time->^miw_ty,test0,test1,addr,
          wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) =
          !t.
            ((wmem t,rmem t,wmar t,wpc t,rpc t,wacc t,
              racc t,wir t,rir t,warg t,alu0 t,alu1 t,rbuf t),
             ((test0 t,test1 t),addr t)) =
            miw t`;

val MpcUnit_def = Define
         `MpcUnit (test0,test1,zeroflag,opcode,addr,mpc) =
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
            DEL (b5,mpc)`;

val CntlUnit_def = Define
         `CntlUnit (
          (zeroflag,opcode,
           wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
          mpc) =
          ?miw test0 test1 addr.
            ROM Microcode (mpc,miw) /\
            Decoder (
              miw,test0,test1,addr,
              wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) /\
            MpcUnit (test0,test1,zeroflag,opcode,addr,mpc)`;

val Tamarack_def = Define
         `Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) =
          ?zeroflag opcode
           wmem rmem wmar wpc rpc wacc racc wir rir warg alu0 alu1 rbuf.
            CntlUnit (
              (zeroflag,opcode,
               wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
              (mpc)) /\
            DataPath n (
              (wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
               zeroflag,opcode),
              (mem,mar,pc,acc,ir,arg,buf))`;

val Inst_def = Define `Inst n (mem:num->num,pc) = mem (pc MOD (2 EXP n))`;

val Opc_def = Define `Opc n inst = ((inst DIV (2 EXP n)) MOD (2 EXP 3))`;

val Addr_def = Define `Addr n inst = (inst MOD (2 EXP n))`;

val NextState_def = Define `
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
                             (mem,(INCn (n+3) pc),acc))`;

val Behaviour_def = Define
        `Behaviour n (mem,pc,acc) =
          !t.
            (mem (t+1),pc (t+1),acc (t+1)) =
              NextState n (mem t,pc t,acc t)`;


val _ = export_theory ();
