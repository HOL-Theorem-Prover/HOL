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

val INCn = new_definition ("INCn",``INCn n a = (a + 1) MOD (2 EXP n)``);
val SUBn = new_definition ("SUBn",``SUBn n (a,b) = (a + b) MOD (2 EXP n)``);
val ADDn = new_definition ("ADDn",``ADDn n (a,b) = (a + b) MOD (2 EXP n)``);

val Bits = new_definition (
        "Bits",
        ``Bits (n,m) w = ((w DIV (2 EXP n)) MOD (2 EXP m))``);

val Update = new_definition (
        "Update",
        ``Update (s:'a->'b,x,y) = \x'. if (x = x') then y else (s x')``);

val PWR = new_definition ("PWR",``PWR (w:wire) = !t. w t = T``);

val GND = new_definition ("GND",``GND (w:wire) = !t. w t = F``);

val AND = new_definition (
        "AND",
        ``AND (a:wire,b:wire,out:wire) = !t. out t = a t /\ b t``);

val OR = new_definition (
        "OR",
        ``OR (a:wire,b:wire,out:wire) = !t. out t = a t \/ b t``);

val MUX = new_definition (
        "MUX",
        ``MUX (cntl:wire,a:bus,b:bus,out:bus) =
          !t. out t = (if cntl t then b t else a t)``);

val BITS = new_definition (
        "BITS",
        ``BITS (n,m) (inp:bus,out:bus) = !t. out t = Bits (n,m) (inp t)``);

val TNZ = new_definition (
        "TNZ",
        ``TNZ (inp:bus,flag:wire) = !t. flag t = ~(inp t = 0)``);

val HWC = new_definition ("HWC",``HWC c (b:bus) = !t. b t = c``);

val ADDER = new_definition (
        "ADDER",
        ``ADDER n (a:bus,b:bus,out:bus) = !t. out t = ADDn n (a t,b t)``);

val ALU = new_definition (
        "ALU",
        ``ALU n (f0:wire,f1:wire,a:bus,b:bus,out:bus) =
          !t.
            ?w.
              out t =
                (if ((f0 t,f1 t) = (T,T)) then w else
                 if ((f0 t,f1 t) = (F,T)) then INCn n (b t) else
                 if ((f0 t,f1 t) = (F,F)) then ADDn n (a t,b t) else
                                               SUBn n (a t,b t))``);

val DEL = new_definition (
        "DEL",
        ``DEL (inp:bus,out:bus) = !t. out (t+1) = inp t``);

val REG = new_definition (
        "REG",
        ``REG ((w:wire,r:wire,inp:bus,bus:bus,out:bus),P) =
          !t.
            ((out (t+1) = (if w t then inp t else out t)) /\
             (P t ==> r t ==> (bus t = out t)))``);

val _ = Parse.hide "MEM"; (* prevent MEM from list-theory causing type-errors below *)
val MEM = new_definition (
        "MEM",
        ``MEM n ((w:wire,r:wire,addr:bus,bus:bus),(P,mem:mem)) =
          !t.
            (mem (t+1) = (if w t then Update (mem t,addr t,bus t) else mem t)) /\
            (P t ==> r t ==> (bus t = mem t (addr t)))``);

val CheckCntls = new_definition (
        "CheckCntls",
        ``CheckCntls (rmem,rpc,racc,rir,rbuf,P) =
          !t.
            P t =
              (if (rmem t) then (~(rpc t \/ racc t \/ rir t \/ rbuf t)) else
              (if (rpc t)  then (~(racc t \/ rir t \/ rbuf t)) else
              (if (racc t) then (~(rir t \/ rbuf t)) else
              (if (rir t)  then (~(rbuf t)) else T))))``);

val DataPath = new_definition (
        "DataPath",
        ``DataPath n (
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
            GND gnd``);

val Cntls = new_definition (
        "Cntls",
        ``Cntls (tok1,tok2) =
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
           (tok1 = "rbuf"))``);

val NextMpc = new_definition (
        "NextMpc",
        ``NextMpc (tok,addr:num) =
          if (tok = "jop") then ((T,F),addr) else
          if (tok = "jnz") then ((F,T),addr) else
          if (tok = "jmp") then ((T,T),addr) else
                                ((F,F),addr)``);

val Microcode = new_definition (
        "Microcode",
        ``Microcode n =
          if (n = 0)  then (Cntls ("rpc","wmar"),  NextMpc ("inc",0))  else
          if (n = 1)  then (Cntls ("rmem","wir"),  NextMpc ("inc",0))  else
          if (n = 2)  then (Cntls ("rir","wmar"),  NextMpc ("jop",0))  else
          if (n = 3)  then (Cntls ("none","none"), NextMpc ("jnz",10)) else (*% JZR %*)
          if (n = 4)  then (Cntls ("rir","wpc"),   NextMpc ("jmp",0))  else (*% JMP %*)
          if (n = 5)  then (Cntls ("racc","warg"), NextMpc ("jmp",12)) else (*% ADD %*)
          if (n = 6)  then (Cntls ("racc","warg"), NextMpc ("jmp",13)) else (*% SUB %*)
          if (n = 7)  then (Cntls ("rmem","wacc"), NextMpc ("jmp",10)) else (*% LD %*)
          if (n = 8)  then (Cntls ("racc","wmem"), NextMpc ("jmp",10)) else (*% ST %*)
          if (n = 9)  then (Cntls ("none","none"), NextMpc ("inc",0))  else (*% NOP %*)
          if (n = 10) then (Cntls ("rpc","inc"),   NextMpc ("inc",0))  else (*% NOP %*)
          if (n = 11) then (Cntls ("rbuf","wpc"),  NextMpc ("jmp",0))  else
          if (n = 12) then (Cntls ("rmem","add"),  NextMpc ("jmp",14)) else
          if (n = 13) then (Cntls ("rmem","sub"),  NextMpc ("inc",0))  else
          if (n = 14) then (Cntls ("rbuf","wacc"), NextMpc ("jmp",10)) else
                           (Cntls ("none","none"), NextMpc ("jmp",0))``);

val miw_ty = ty_antiq (hd (tl (snd (dest_type (type_of ``Microcode``)))));

val ROM = new_definition (
        "ROM",
        ``ROM contents (addr:bus,data:time->^miw_ty) =
          !t. data t = contents (addr t)``);

val Decoder = new_definition (
        "Decoder",
        ``Decoder (
          miw:time->^miw_ty,test0,test1,addr,
          wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) =
          !t.
            ((wmem t,rmem t,wmar t,wpc t,rpc t,wacc t,
              racc t,wir t,rir t,warg t,alu0 t,alu1 t,rbuf t),
             ((test0 t,test1 t),addr t)) =
            miw t``);

val MpcUnit = new_definition (
        "MpcUnit",
        ``MpcUnit (test0,test1,zeroflag,opcode,addr,mpc) =
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
            DEL (b5,mpc)``);

val CntlUnit = new_definition (
        "CntlUnit",
        ``CntlUnit (
          (zeroflag,opcode,
           wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
          mpc) =
          ?miw test0 test1 addr.
            ROM Microcode (mpc,miw) /\
            Decoder (
              miw,test0,test1,addr,
              wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) /\
            MpcUnit (test0,test1,zeroflag,opcode,addr,mpc)``);

val Tamarack = new_definition (
        "Tamarack",
        ``Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) =
          ?zeroflag opcode
           wmem rmem wmar wpc rpc wacc racc wir rir warg alu0 alu1 rbuf.
            CntlUnit (
              (zeroflag,opcode,
               wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
              (mpc)) /\
            DataPath n (
              (wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
               zeroflag,opcode),
              (mem,mar,pc,acc,ir,arg,buf))``);

val Inst = new_definition (
        "Inst",
        ``Inst n (mem:num->num,pc) = mem (pc MOD (2 EXP n))``);

val Opc = new_definition (
        "Opc",
        ``Opc n inst = ((inst DIV (2 EXP n)) MOD (2 EXP 3))``);

val Addr = new_definition (
        "Addr",
        ``Addr n inst = (inst MOD (2 EXP n))``);

val NextState = new_definition (
        "NextState",
        ``NextState n (mem,pc,acc) =
          let inst = Inst n (mem,pc) in
          let opc = Opc n inst in
          let addr = Addr n inst in
          (if (opc = 0) then (mem,(if (acc = 0) then inst else (INCn (n+3) pc)),acc) else
           if (opc = 1) then (mem,inst,acc) else
           if (opc = 2) then (mem,(INCn (n+3) pc),(ADDn (n+3) (acc,mem addr))) else
           if (opc = 3) then (mem,(INCn (n+3) pc),(SUBn (n+3) (acc,mem addr))) else
           if (opc = 4) then (mem,(INCn (n+3) pc),mem addr) else
           if (opc = 5) then (Update (mem,addr,acc),(INCn (n+3) pc),acc) else
                             (mem,(INCn (n+3) pc),acc))``);

val Behaviour = new_definition (
        "Behaviour",
        ``Behaviour n (mem,pc,acc) =
          !t.
            (mem (t+1),pc (t+1),acc (t+1)) =
              NextState n (mem t,pc t,acc t)``);


val _ = export_theory ();
