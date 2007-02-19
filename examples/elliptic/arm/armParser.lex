structure Tokens = Tokens
type pos = int

type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b)Tokens.token
type lexresult = (svalue,pos) token

val pos = ref 1
fun eof () = Tokens.EOF(!pos, !pos)

open Data;

fun int2register n =
   case n of
     0  => R0  | 1  => R1  | 2  => R2  | 3 => R3
   | 4  => R4  | 5  => R5  | 6  => R6  | 7 => R7
   | 8  => R8  | 9  => R9  | 10 => R10 | 11 => R11
   | 12 => R12 | 13 => R13 | 14 => R14 | 15 => R15
   | _ =>  raise Parse "not a register list";

fun str2cond skp s =
   (case String.map Char.toLower (String.extract(s,skp,SOME 2)) of
     "eq" => EQ | "ne" => NE | "cs" => CS | "cc" => CC
   | "mi" => MI | "pl" => PL | "vs" => VS | "vc" => VC
   | "hi" => HI | "ls" => LS | "ge" => GE | "lt" => LT
   | "gt" => GT | "le" => LE | "nv" => NV | _ => AL)
   handle Subscript => AL;

fun opc1 s =
   case String.map Char.toLower (String.extract(s,0,SOME 3)) of
     "and" => AND | "eor" => EOR | "sub" => SUB | "rsb" => RSB
   | "add" => ADD | "adc" => ADC | "sbc" => SBC | "rsc" => RSC
   | "tst" => TST | "teq" => TEQ | "cmp" => CMP | "cmn" => CMN
   | "orr" => ORR | "mov" => MOV | "bic" => BIC | "mvn" => MVN
   | _ => raise Parse "not an opcode";

fun strSkip n s = String.extract(s,n,NONE);

val str2int = valOf o Int.fromString o strSkip 1;
val reg1 = int2register o str2int

val hexnum = Arbnum.fromHexString;
val octnum = Arbnum.fromOctString;
val decnum = Arbnum.fromString;

fun binnum s =
     if String.sub(s,0) = #"+" then
       Arbnum.fromBinString (strSkip 3 s)
     else
       Arbnum.fromBinString (strSkip 2 s);

val cond1 = str2cond 1;
val cond2 = str2cond 2;
val cond3 = str2cond 3;

%%
%header (functor armLexFun(structure Tokens : arm_TOKENS));

A = [aA]; B = [bB]; C = [cC]; D = [dD];
E = [eE]; F = [fF]; G = [gG]; H = [hH];
I = [iI]; L = [lL];
M = [mM]; N = [nN]; O = [oO]; P = [pP];
Q = [qQ]; R = [rR]; S = [sS]; T = [tT];
U = [uU]; V = [vV]; W = [wW]; X = [xX];
cond = ({E}{Q} | {N}{E} | {C}{S} | {H}{S}
      | {C}{C} | {L}{O} | {M}{I} | {P}{L}
      | {V}{S} | {V}{C} | {H}{I} | {L}{S}
      | {G}{E} | {L}{T} | {G}{T} | {L}{E}
      | {A}{L} | {N}{V})?;
opcode1 = {T}{S}{T} | {T}{E}{Q} | {C}{M}{P} | {C}{M}{N};
opcode2 = {A}{N}{D} | {E}{O}{R} | {S}{U}{B} | {R}{S}{B} | {A}{D}{D}
        | {A}{D}{C} | {S}{B}{C} | {R}{S}{C} | {O}{R}{R} | {B}{I}{C};
opcode3 = {M}{O}{V} | {M}{V}{N};

%%

[\ \t]+                 => ( continue() );
\n                      => ( pos := !pos + 1; continue() );
"+"?"0x"[0-9a-fA-F]+    => ( Tokens.NUMBER (hexnum yytext, !pos, !pos) );
"+"?"0b"[0-1]+          => ( Tokens.NUMBER (binnum yytext, !pos, !pos) );
"+"?0[0-7]+             => ( Tokens.NUMBER (octnum yytext, !pos, !pos) );
"+"?[1-9][0-9]*         => ( Tokens.NUMBER (decnum yytext, !pos, !pos) );
"+"?0                   => ( Tokens.NUMBER (Arbnum.zero, !pos, !pos) );
{R}[0-9]                => ( Tokens.REG (reg1 yytext, !pos, !pos) );
{R}1[0-5]               => ( Tokens.REG (reg1 yytext, !pos, !pos) );
{C}[0-9]                => ( Tokens.COREG (reg1 yytext, !pos, !pos) );
{C}1[0-5]               => ( Tokens.COREG (reg1 yytext, !pos, !pos) );
{P}[0-9]                => ( Tokens.COPROC (str2int yytext, !pos, !pos) );
{P}1[0-5]               => ( Tokens.COPROC (str2int yytext, !pos, !pos) );
{S}{L}                  => ( Tokens.REG (R10, !pos, !pos) );
{F}{P}                  => ( Tokens.REG (R11, !pos, !pos) );
{I}{P}                  => ( Tokens.REG (R12, !pos, !pos) );
{S}{P}                  => ( Tokens.REG (R13, !pos, !pos) );
{L}{R}                  => ( Tokens.REG (R14, !pos, !pos) );
{P}{C}                  => ( Tokens.REG (R15, !pos, !pos) );
{A}{S}{L}               => ( Tokens.SHIFT (LSL, !pos, !pos) );
{L}{S}{L}               => ( Tokens.SHIFT (LSL, !pos, !pos) );
{L}{S}{R}               => ( Tokens.SHIFT (LSR, !pos, !pos) );
{A}{S}{R}               => ( Tokens.SHIFT (ASR, !pos, !pos) );
{R}{O}{R}               => ( Tokens.SHIFT (ROR, !pos, !pos) );
{R}{R}{X}               => ( Tokens.RRX (!pos, !pos) );
{C}{P}{S}{R}            => ( Tokens.PSR (false, !pos, !pos) );
{S}{P}{S}{R}            => ( Tokens.PSR (true, !pos, !pos) );
{C}{P}{S}{R}"_c"("tl")? => ( Tokens.PSRF ((false,false,true), !pos, !pos) );
{C}{P}{S}{R}"_f"("lg")? => ( Tokens.PSRF ((false,true,false), !pos, !pos) );
{C}{P}{S}{R}"_a"("ll")? => ( Tokens.PSRF ((false,true,true), !pos, !pos) );
{S}{P}{S}{R}"_c"("tl")? => ( Tokens.PSRF ((true,false,true), !pos, !pos) );
{S}{P}{S}{R}"_f"("lg")? => ( Tokens.PSRF ((true,true,false), !pos, !pos) );
{S}{P}{S}{R}"_a"("ll")? => ( Tokens.PSRF ((true,true,true), !pos, !pos) );
{B}{cond}          => ( Tokens.BRANCH ((cond1 yytext,false), !pos, !pos) );
{B}{L}{cond}       => ( Tokens.BRANCH ((cond2 yytext,true), !pos, !pos) );
{S}{W}{I}{cond}    => ( Tokens.SWI_EX (cond3 yytext, !pos, !pos) );
{opcode1}{cond} =>
   ( Tokens.DPROC1 ((opc1 yytext, cond3 yytext, true), !pos, !pos) );
{opcode2}{cond} =>
   ( Tokens.DPROC2 ((opc1 yytext, cond3 yytext, false), !pos, !pos) );
{opcode2}{cond}{S} =>
   ( Tokens.DPROC2 ((opc1 yytext, cond3 yytext, true), !pos, !pos) );
{opcode3}{cond} =>
   ( Tokens.DPROC1 ((opc1 yytext, cond3 yytext, false), !pos, !pos) );
{opcode3}{cond}{S} =>
   ( Tokens.DPROC1 ((opc1 yytext, cond3 yytext, true), !pos, !pos) );
{M}{U}{L}{cond}    => ( Tokens.MULT3 ((cond3 yytext, false), !pos, !pos) );
{M}{U}{L}{cond}{S} => ( Tokens.MULT3 ((cond3 yytext, true), !pos, !pos) );
{M}{L}{A}{cond} =>
   ( Tokens.MULT4 ((cond3 yytext, false, false, true, false), !pos, !pos) );
{M}{L}{A}{cond}{S} =>
   ( Tokens.MULT4 ((cond3 yytext, false, false, true, true), !pos, !pos) );
{U}{M}{U}{L}{L}{cond} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, false, false), !pos, !pos) );
{U}{M}{U}{L}{L}{cond}{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, false, true), !pos, !pos) );
{U}{M}{L}{A}{L}{cond} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, true, false), !pos, !pos) );
{U}{M}{L}{A}{L}{cond}{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, true, true), !pos, !pos) );
{S}{M}{U}{L}{L}{cond} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, false, false), !pos, !pos) );
{S}{M}{U}{L}{L}{cond}{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, false, true), !pos, !pos) );
{S}{M}{L}{A}{L}{cond} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, true, false), !pos, !pos) );
{S}{M}{L}{A}{L}{cond}{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, true, true), !pos, !pos) );
{L}{D}{R}{cond}{S}{B} =>
   ( Tokens.STRANSH ((true, cond3 yytext, true, false), !pos, !pos) );
{L}{D}{R}{cond}{S}{H} =>
   ( Tokens.STRANSH ((true, cond3 yytext, true, true), !pos, !pos) );
{L}{D}{R}{cond}{H} =>
   ( Tokens.STRANSH ((true, cond3 yytext, false, true), !pos, !pos) );
{S}{T}{R}{cond}{S}?{H} =>
   ( Tokens.STRANSH ((false, cond3 yytext, false, true), !pos, !pos) );
{L}{D}{R}{cond} =>
   ( Tokens.STRANS ((true, cond3 yytext, false), !pos, !pos) );
{L}{D}{R}{cond}{B} =>
   ( Tokens.STRANS ((true, cond3 yytext, true), !pos, !pos) );
{S}{T}{R}{cond} =>
   ( Tokens.STRANS ((false,cond3 yytext, false), !pos, !pos) );
{S}{T}{R}{cond}{S}?{B} =>
   ( Tokens.STRANS ((false,cond3 yytext, true), !pos, !pos) );
{L}{D}{M}{cond}({E}{D} | {I}{B}) => ( Tokens.BTRANS ((true, cond3 yytext, true, true), !pos, !pos) );
{L}{D}{M}{cond}({F}{D} | {I}{A}) => ( Tokens.BTRANS ((true, cond3 yytext, false,true), !pos, !pos) );
{L}{D}{M}{cond}({E}{A} | {D}{B}) => ( Tokens.BTRANS ((true, cond3 yytext, true, false), !pos, !pos) );
{L}{D}{M}{cond}({F}{A} | {D}{A}) => ( Tokens.BTRANS ((true, cond3 yytext, false,false), !pos, !pos) );
{S}{T}{M}{cond}({F}{A} | {I}{B}) => ( Tokens.BTRANS ((false,cond3 yytext, true, true), !pos, !pos) );
{S}{T}{M}{cond}({E}{A} | {I}{A}) => ( Tokens.BTRANS ((false,cond3 yytext, false,true), !pos, !pos) );
{S}{T}{M}{cond}({F}{D} | {D}{B}) => ( Tokens.BTRANS ((false,cond3 yytext, true, false), !pos, !pos) );
{S}{T}{M}{cond}({E}{D} | {D}{A}) => ( Tokens.BTRANS ((false,cond3 yytext, false,false), !pos, !pos) );
{S}{W}{P}{cond}    => ( Tokens.SWAP ((cond3 yytext, false), !pos, !pos) );
{S}{W}{P}{cond}{B} => ( Tokens.SWAP ((cond3 yytext, true), !pos, !pos) );
{M}{R}{S}{cond}    => ( Tokens.MRS  (cond3 yytext, !pos, !pos) );
{M}{S}{R}{cond}    => ( Tokens.MSR  (cond3 yytext, !pos, !pos) );
{C}{D}{P}{cond}    => ( Tokens.CDP  (cond3 yytext, !pos, !pos) );
{M}{C}{R}{cond}    => ( Tokens.MCR_MRC ((cond3 yytext, false), !pos, !pos) );
{M}{R}{C}{cond}    => ( Tokens.MCR_MRC ((cond3 yytext, true), !pos, !pos) );
{L}{D}{C}{cond}    => ( Tokens.LDC_STC ((true, cond3 yytext, false), !pos, !pos) );
{L}{D}{C}{cond}{L} => ( Tokens.LDC_STC ((true, cond3 yytext, true), !pos, !pos) );
{S}{T}{C}{cond}    => ( Tokens.LDC_STC ((false,cond3 yytext, false), !pos, !pos) );
{S}{T}{C}{cond}{L} => ( Tokens.LDC_STC ((false,cond3 yytext, true), !pos, !pos) );
"{"                => ( Tokens.LBRACE (!pos, !pos) );
"}"                => ( Tokens.RBRACE (!pos, !pos) );
"["                => ( Tokens.LSQUARE(!pos, !pos)  );
"]"                => ( Tokens.RSQUARE(!pos, !pos)  );
"#"                => ( Tokens.HASH (!pos, !pos) );
"-"                => ( Tokens.MINUS (!pos, !pos) );
"+"                => ( Tokens.PLUS (!pos, !pos) );
"!"                => ( Tokens.EXCLAIM (!pos, !pos) );
":"                => ( Tokens.COLON (!pos, !pos) );
","                => ( Tokens.COMMA (!pos, !pos) );
"^"                => ( Tokens.HAT (!pos, !pos) );
"|"                => ( Tokens.BAR (!pos, !pos) );
[".""_"a-zA-Z0-9]+ => ( Tokens.LABEL (yytext, !pos, !pos) );
[";""@"][^"\n"]*   => ( continue() );
