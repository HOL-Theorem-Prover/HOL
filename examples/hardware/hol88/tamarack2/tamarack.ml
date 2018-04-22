% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;
load_library `string`;;
let EXP = (LIST_CONJ o (map SPEC_ALL) o CONJUNCTS) EXP;;
let new_definition = SPEC_ALL o new_definition;;
let new_prim_rec_definition  =
	LIST_CONJ o (map SPEC_ALL) o CONJUNCTS o new_prim_rec_definition;;

% ===================================================================== %
% Jeff Joyce, University of Cambridge, 1 November 1988			%
%									%
% Specify register-transfer level implementation and functional		%
% behaviour of a very simple microprocessor.				%

new_theory `tamarack`;;

new_parent `mod`;;
new_parent `div`;;

new_type_abbrev (`time`,":num");;
new_type_abbrev (`wire`,":time->bool");;
new_type_abbrev (`bus`,":time->num");;
new_type_abbrev (`mem`,":time->num->num");;

let INCn = new_definition (`INCn`,"INCn n a = (a + 1) MOD (2 EXP n)");;
let SUBn = new_definition (`SUBn`,"SUBn n (a,b) = (a + b) MOD (2 EXP n)");;
let ADDn = new_definition (`ADDn`,"ADDn n (a,b) = (a + b) MOD (2 EXP n)");;

let Bits = new_definition (
	`Bits`,
	"Bits (n,m) w = ((w Div (2 EXP n)) MOD (2 EXP m))");;

let Update = new_definition (
	`Update`,
	"Update (s:*->**,x,y) = \x'. (x = x') => y | (s x')");;

let PWR = new_definition (`PWR`,"PWR (w:wire) = !t. w t = T");;

let GND = new_definition (`GND`,"GND (w:wire) = !t. w t = F");;

let AND = new_definition (
	`AND`,
	"AND (a:wire,b:wire,out:wire) = !t. out t = a t /\ b t");;

let OR = new_definition (
	`OR`,
	"OR (a:wire,b:wire,out:wire) = !t. out t = a t \/ b t");;

let MUX = new_definition (
	`MUX`,
	"MUX (cntl:wire,a:bus,b:bus,out:bus) =
	  !t. out t = (cntl t => b t | a t)");;

let BITS = new_definition (
	`BITS`,
	"BITS (n,m) (in:bus,out:bus) = !t. out t = Bits (n,m) (in t)");;

let TNZ = new_definition (
	`TNZ`,
	"TNZ (in:bus,flag:wire) = !t. flag t = ~(in t = 0)");;

let HWC = new_definition (`HWC`,"HWC c (b:bus) = !t. b t = c");;

let ADDER = new_definition (
	`ADDER`,
	"ADDER n (a:bus,b:bus,out:bus) = !t. out t = ADDn n (a t,b t)");;

let ALU = new_definition (
	`ALU`,
	"ALU n (f0:wire,f1:wire,a:bus,b:bus,out:bus) =
	  !t.
	    ?w.
	      out t =
	        (((f0 t,f1 t) = (T,T)) => w |
	         ((f0 t,f1 t) = (F,T)) => INCn n (b t) |
	         ((f0 t,f1 t) = (F,F)) => ADDn n (a t,b t) |
	                                  SUBn n (a t,b t))");;

let DEL = new_definition (
	`DEL`,
	"DEL (in:bus,out:bus) = !t. out (t+1) = in t");;

let REG = new_definition (
	`REG`,
	"REG ((w:wire,r:wire,in:bus,bus:bus,out:bus),P) =
	  !t.
	    ((out (t+1) = (w t => in t | out t)) /\
	     (P t ==> r t ==> (bus t = out t)))");;

let MEM = new_definition (
	`MEM`,
	"MEM n ((w:wire,r:wire,addr:bus,bus:bus),(P,mem:mem)) =
	  !t.
	    (mem (t+1) = (w t => Update (mem t,addr t,bus t) | mem t)) /\
	    (P t ==> r t ==> (bus t = mem t (addr t)))");;

let CheckCntls = new_definition (
	`CheckCntls`,
	"CheckCntls (rmem,rpc,racc,rir,rbuf,P) =
	  !t.
	    P t =
	      ((rmem t)	=> (~(rpc t \/ racc t \/ rir t \/ rbuf t)) |
	      ((rpc t)	=> (~(racc t \/ rir t \/ rbuf t)) |
	      ((racc t)	=> (~(rir t \/ rbuf t)) |
	      ((rir t)	=> (~(rbuf t)) | T))))");;

let DataPath = new_definition (
	`DataPath`,
	"DataPath n (
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
	    GND gnd");;

let Cntls = new_definition (
	`Cntls`,
	"Cntls (tok1,tok2) =
	  ((tok2 = `wmem`),
	   (tok1 = `rmem`),
	   (tok2 = `wmar`),
	   (tok2 = `wpc`),
	   (tok1 = `rpc`),
	   (tok2 = `wacc`),
	   (tok1 = `racc`),
	   (tok2 = `wir`),
	   (tok1 = `rir`),
	   (tok2 = `warg`),
	   (tok2 = `sub`),
	   (tok2 = `inc`),
	   (tok1 = `rbuf`))");;

let NextMpc = new_definition (
	`NextMpc`,
	"NextMpc (tok,addr:num) =
	  (tok = `jop`) => ((T,F),addr) |
	  (tok = `jnz`) => ((F,T),addr) |
	  (tok = `jmp`) => ((T,T),addr) |
			   ((F,F),addr)");;

let Microcode = new_definition (
	`Microcode`,
	"Microcode n =
	  ((n = 0)  => (Cntls (`rpc`,`wmar`),  NextMpc (`inc`,0))  |
	   (n = 1)  => (Cntls (`rmem`,`wir`),  NextMpc (`inc`,0))  |
	   (n = 2)  => (Cntls (`rir`,`wmar`),  NextMpc (`jop`,0))  |
	   (n = 3)  => (Cntls (`none`,`none`), NextMpc (`jnz`,10)) | % JZR %
	   (n = 4)  => (Cntls (`rir`,`wpc`),   NextMpc (`jmp`,0))  | % JMP %
	   (n = 5)  => (Cntls (`racc`,`warg`), NextMpc (`jmp`,12)) | % ADD %
	   (n = 6)  => (Cntls (`racc`,`warg`), NextMpc (`jmp`,13)) | % SUB %
	   (n = 7)  => (Cntls (`rmem`,`wacc`), NextMpc (`jmp`,10)) | % LD %
	   (n = 8)  => (Cntls (`racc`,`wmem`), NextMpc (`jmp`,10)) | % ST %
	   (n = 9)  => (Cntls (`none`,`none`), NextMpc (`inc`,0))  | % NOP %
	   (n = 10) => (Cntls (`rpc`,`inc`),   NextMpc (`inc`,0))  | % NOP %
	   (n = 11) => (Cntls (`rbuf`,`wpc`),  NextMpc (`jmp`,0))  |
	   (n = 12) => (Cntls (`rmem`,`add`),  NextMpc (`jmp`,14)) |
	   (n = 13) => (Cntls (`rmem`,`sub`),  NextMpc (`inc`,0))  |
	   (n = 14) => (Cntls (`rbuf`,`wacc`), NextMpc (`jmp`,10)) |
	               (Cntls (`none`,`none`), NextMpc (`jmp`,0)))");;

let miw_ty = hd (tl (snd (dest_type (type_of "Microcode"))));;

let ROM = new_definition (
	`ROM`,
	"ROM contents (addr:bus,data:time->^miw_ty) =
	  !t. data t = contents (addr t)");;

let Decoder = new_definition (
	`Decoder`,
	"Decoder (
	  miw:time->^miw_ty,test0,test1,addr,
	  wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) =
	  !t.
	    ((wmem t,rmem t,wmar t,wpc t,rpc t,wacc t,
	      racc t,wir t,rir t,warg t,alu0 t,alu1 t,rbuf t),
	     ((test0 t,test1 t),addr t)) =
	    miw t");;

let MpcUnit = new_definition (
	`MpcUnit`,
	"MpcUnit (test0,test1,zeroflag,opcode,addr,mpc) =
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
	    DEL (b5,mpc)");;

let CntlUnit = new_definition (
	`CntlUnit`,
	"CntlUnit (
	  (zeroflag,opcode,
	   wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
	  mpc) =
	  ?miw test0 test1 addr.
	    ROM Microcode (mpc,miw) /\
	    Decoder (
	      miw,test0,test1,addr,
	      wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf) /\
	    MpcUnit (test0,test1,zeroflag,opcode,addr,mpc)");;

let Tamarack = new_definition (
	`Tamarack`,
	"Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) =
	  ?zeroflag opcode
	   wmem rmem wmar wpc rpc wacc racc wir rir warg alu0 alu1 rbuf.
	    CntlUnit (
	      (zeroflag,opcode,
	       wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf),
	      (mpc)) /\
	    DataPath n (
	      (wmem,rmem,wmar,wpc,rpc,wacc,racc,wir,rir,warg,alu0,alu1,rbuf,
	       zeroflag,opcode),
	      (mem,mar,pc,acc,ir,arg,buf))");;

let Inst = new_definition (
	`Inst`,
	"Inst n (mem:num->num,pc) = mem (pc MOD (2 EXP n))");;

let Opc = new_definition (
	`Opc`,
	"Opc n inst = ((inst Div (2 EXP n)) MOD (2 EXP 3))");;

let Addr = new_definition (
	`Addr`,
	"Addr n inst = (inst MOD (2 EXP n))");;

let NextState = new_definition (
	`NextState`,
	"NextState n (mem,pc,acc) =
	  let inst = Inst n (mem,pc) in
	  let opc = Opc n inst in
	  let addr = Addr n inst in
	  ((opc = 0) => (mem,((acc = 0) => inst | (INCn (n+3) pc)),acc) |
	   (opc = 1) => (mem,inst,acc) |
	   (opc = 2) => (mem,(INCn (n+3) pc),(ADDn (n+3) (acc,mem addr))) |
	   (opc = 3) => (mem,(INCn (n+3) pc),(SUBn (n+3) (acc,mem addr))) |
	   (opc = 4) => (mem,(INCn (n+3) pc),mem addr) |
	   (opc = 5) => (Update (mem,addr,acc),(INCn (n+3) pc),acc) |
 	                (mem,(INCn (n+3) pc),acc))");;

let Behaviour = new_definition (
	`Behaviour`,
	"Behaviour n (mem,pc,acc) =
	  !t.
	    (mem (t+1),pc (t+1),acc (t+1)) =
	      NextState n (mem t,pc t,acc t)");;

close_theory ();;
