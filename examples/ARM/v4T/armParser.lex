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
   | _ =>  raise Parse "not a register";

fun int2register_ n =
   case n of
     0  => R0_  | 1  => R1_  | 2  => R2_  | 3 => R3_
   | 4  => R4_  | 5  => R5_  | 6  => R6_  | 7 => R7_
   | _ =>  raise Parse "not a lower register";

fun str2cond skp s =
   (case String.map Char.toLower (String.extract(s,skp,SOME 2)) of
     "eq" => EQ | "ne" => NE | "cs" => CS | "hs" => CS
   | "cc" => CC | "lo" => CC | "mi" => MI | "pl" => PL
   | "vs" => VS | "vc" => VC | "hi" => HI | "ls" => LS
   | "ge" => GE | "lt" => LT | "gt" => GT | "le" => LE
   | "nv" => NV | _ => AL)
   handle Subscript => AL;

fun strSkip n s = String.extract(s,n,NONE);

val str2int = valOf o Int.fromString o strSkip 1;
val reg1 = int2register o str2int
val reg1_ = int2register_ o str2int

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
cond = {E}{Q} | {N}{E} | {C}{S} | {H}{S}
     | {C}{C} | {L}{O} | {M}{I} | {P}{L}
     | {V}{S} | {V}{C} | {H}{I} | {L}{S}
     | {G}{E} | {L}{T} | {G}{T} | {L}{E}
     | {A}{L} | {N}{V};

%%

[\ \t]+                 => ( continue() );
\n                      => ( pos := !pos + 1; continue() );
"+"?"0x"[0-9a-fA-F]+    => ( Tokens.NUMBER (hexnum yytext, !pos, !pos) );
"+"?"0b"[0-1]+          => ( Tokens.NUMBER (binnum yytext, !pos, !pos) );
"+"?0[0-7]+             => ( Tokens.NUMBER (octnum yytext, !pos, !pos) );
"+"?[1-9][0-9]*         => ( Tokens.NUMBER (decnum yytext, !pos, !pos) );
"+"?0                   => ( Tokens.NUMBER (Arbnum.zero, !pos, !pos) );
{R}[0-7]                => ( Tokens.LREG (reg1_ yytext, !pos, !pos) );
{R}[8-9]                => ( Tokens.REG (reg1 yytext, !pos, !pos) );
{R}1[0-2]               => ( Tokens.REG (reg1 yytext, !pos, !pos) );
{R}13                   => ( Tokens.SP_ (!pos, !pos) );
{R}14                   => ( Tokens.LR_ (!pos, !pos) );
{R}15                   => ( Tokens.PC_ (!pos, !pos) );
{C}[0-9]                => ( Tokens.COREG (reg1 yytext, !pos, !pos) );
{C}1[0-5]               => ( Tokens.COREG (reg1 yytext, !pos, !pos) );
{P}[0-9]                => ( Tokens.COPROC (str2int yytext, !pos, !pos) );
{P}1[0-5]               => ( Tokens.COPROC (str2int yytext, !pos, !pos) );
{S}{L}                  => ( Tokens.REG (R10, !pos, !pos) );
{F}{P}                  => ( Tokens.REG (R11, !pos, !pos) );
{I}{P}                  => ( Tokens.REG (R12, !pos, !pos) );
{S}{P}                  => ( Tokens.SP_ (!pos, !pos) );
{L}{R}                  => ( Tokens.LR_ (!pos, !pos) );
{P}{C}                  => ( Tokens.PC_ (!pos, !pos) );
{A}{S}{L}               => ( Tokens.SHIFT (LSL, !pos, !pos) );
{L}{S}{L}               => ( Tokens.SHIFT (LSL, !pos, !pos) );
{L}{S}{R}               => ( Tokens.SHIFT (LSR, !pos, !pos) );
{A}{S}{R}               => ( Tokens.SHIFT (ASR, !pos, !pos) );
{R}{O}{R}               => ( Tokens.ROR (!pos, !pos) );
{R}{R}{X}               => ( Tokens.RRX (!pos, !pos) );
{C}{P}{S}{R}            => ( Tokens.PSR (false, !pos, !pos) );
{S}{P}{S}{R}            => ( Tokens.PSR (true, !pos, !pos) );
{C}{P}{S}{R}"_c"("tl")? => ( Tokens.PSRF ((false,false,true), !pos, !pos) );
{C}{P}{S}{R}"_f"("lg")? => ( Tokens.PSRF ((false,true,false), !pos, !pos) );
{C}{P}{S}{R}"_a"("ll")? => ( Tokens.PSRF ((false,true,true), !pos, !pos) );
{S}{P}{S}{R}"_c"("tl")? => ( Tokens.PSRF ((true,false,true), !pos, !pos) );
{S}{P}{S}{R}"_f"("lg")? => ( Tokens.PSRF ((true,true,false), !pos, !pos) );
{S}{P}{S}{R}"_a"("ll")? => ( Tokens.PSRF ((true,true,true), !pos, !pos) );
{C}{O}{D}{E}16          => ( Tokens.CODE16 (!pos, !pos) );
{C}{O}{D}{E}32          => ( Tokens.CODE32 (!pos, !pos) );

{B}{L}             => ( Tokens.BL_ (!pos, !pos) );
{B}{L}1            => ( Tokens.BL1 (!pos, !pos) );
{B}{L}2            => ( Tokens.BL2 (!pos, !pos) );
{B}{X}             => ( Tokens.BX_ (!pos, !pos) );
{S}{W}{I}          => ( Tokens.SWI_ (!pos, !pos) );
{B}{cond}?         => ( Tokens.BRANCH (cond1 yytext, !pos, !pos) );
{B}{L}{cond}       => ( Tokens.BRANCH_LINK (cond2 yytext, !pos, !pos) );
{B}{X}{cond}       => ( Tokens.BX (cond3 yytext, !pos, !pos) );
{S}{W}{I}{cond}    => ( Tokens.SWI_EX (cond3 yytext, !pos, !pos) );

{N}{E}{G}          => ( Tokens.NEG (!pos, !pos) );
{P}{U}{S}{H}       => ( Tokens.PUSH (!pos, !pos) );
{P}{O}{P}          => ( Tokens.POP (!pos, !pos) );
{B}{L}{1}          => ( Tokens.BL1 (!pos, !pos) );
{B}{L}{2}          => ( Tokens.BL2 (!pos, !pos) );

{A}{N}{D}          => ( Tokens.AND_ (!pos, !pos) );
{E}{O}{R}          => ( Tokens.EOR_ (!pos, !pos) );
{S}{U}{B}          => ( Tokens.SUB_ (!pos, !pos) );
{A}{D}{D}          => ( Tokens.ADD_ (!pos, !pos) );
{A}{D}{C}          => ( Tokens.ADC_ (!pos, !pos) );
{S}{B}{C}          => ( Tokens.SBC_ (!pos, !pos) );
{T}{S}{T}          => ( Tokens.TST_ (!pos, !pos) );
{C}{M}{P}          => ( Tokens.CMP_ (!pos, !pos) );
{C}{M}{N}          => ( Tokens.CMN_ (!pos, !pos) );
{O}{R}{R}          => ( Tokens.ORR_ (!pos, !pos) );
{M}{O}{V}          => ( Tokens.MOV_ (!pos, !pos) );
{B}{I}{C}          => ( Tokens.BIC_ (!pos, !pos) );
{M}{V}{N}          => ( Tokens.MVN_ (!pos, !pos) );
{M}{U}{L}          => ( Tokens.MUL_ (!pos, !pos) );

{A}{N}{D}{cond}    => ( Tokens.AND ((cond3 yytext, false), !pos, !pos) );
{E}{O}{R}{cond}    => ( Tokens.EOR ((cond3 yytext, false), !pos, !pos) );
{S}{U}{B}{cond}    => ( Tokens.SUB ((cond3 yytext, false), !pos, !pos) );
{R}{S}{B}{cond}?   => ( Tokens.RSB ((cond3 yytext, false), !pos, !pos) );
{A}{D}{D}{cond}    => ( Tokens.ADD ((cond3 yytext, false), !pos, !pos) );
{A}{D}{C}{cond}    => ( Tokens.ADC ((cond3 yytext, false), !pos, !pos) );
{S}{B}{C}{cond}    => ( Tokens.SBC ((cond3 yytext, false), !pos, !pos) );
{R}{S}{C}{cond}?   => ( Tokens.RSC ((cond3 yytext, false), !pos, !pos) );
{T}{S}{T}{cond}    => ( Tokens.TST (cond3 yytext, !pos, !pos) );
{T}{E}{Q}{cond}?   => ( Tokens.TEQ (cond3 yytext, !pos, !pos) );
{C}{M}{P}{cond}    => ( Tokens.CMP (cond3 yytext, !pos, !pos) );
{C}{M}{N}{cond}    => ( Tokens.CMN (cond3 yytext, !pos, !pos) );
{O}{R}{R}{cond}    => ( Tokens.ORR ((cond3 yytext, false), !pos, !pos) );
{M}{O}{V}{cond}    => ( Tokens.MOV ((cond3 yytext, false), !pos, !pos) );
{B}{I}{C}{cond}    => ( Tokens.BIC ((cond3 yytext, false), !pos, !pos) );
{M}{V}{N}{cond}    => ( Tokens.MVN ((cond3 yytext, false), !pos, !pos) );
{M}{U}{L}{cond}    => ( Tokens.MUL ((cond3 yytext, false), !pos, !pos) );

{A}{N}{D}{cond}?{S} => ( Tokens.AND ((cond3 yytext, true), !pos, !pos) );
{E}{O}{R}{cond}?{S} => ( Tokens.EOR ((cond3 yytext, true), !pos, !pos) );
{S}{U}{B}{cond}?{S} => ( Tokens.SUB ((cond3 yytext, true), !pos, !pos) );
{R}{S}{B}{cond}?{S} => ( Tokens.RSB ((cond3 yytext, true), !pos, !pos) );
{A}{D}{D}{cond}?{S} => ( Tokens.ADD ((cond3 yytext, true), !pos, !pos) );
{A}{D}{C}{cond}?{S} => ( Tokens.ADC ((cond3 yytext, true), !pos, !pos) );
{S}{B}{C}{cond}?{S} => ( Tokens.SBC ((cond3 yytext, true), !pos, !pos) );
{R}{S}{C}{cond}?{S} => ( Tokens.RSC ((cond3 yytext, true), !pos, !pos) );
{O}{R}{R}{cond}?{S} => ( Tokens.ORR ((cond3 yytext, true), !pos, !pos) );
{M}{O}{V}{cond}?{S} => ( Tokens.MOV ((cond3 yytext, true), !pos, !pos) );
{B}{I}{C}{cond}?{S} => ( Tokens.BIC ((cond3 yytext, true), !pos, !pos) );
{M}{V}{N}{cond}?{S} => ( Tokens.MVN ((cond3 yytext, true), !pos, !pos) );
{M}{U}{L}{cond}?{S} => ( Tokens.MUL ((cond3 yytext, true), !pos, !pos) );

{M}{L}{A}{cond}? =>
   ( Tokens.MULT4 ((cond3 yytext, false, false, true, false), !pos, !pos) );
{M}{L}{A}{cond}?{S} =>
   ( Tokens.MULT4 ((cond3 yytext, false, false, true, true), !pos, !pos) );
{U}{M}{U}{L}{L}{cond}? =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, false, false), !pos, !pos) );
{U}{M}{U}{L}{L}{cond}?{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, false, true), !pos, !pos) );
{U}{M}{L}{A}{L}{cond}? =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, true, false), !pos, !pos) );
{U}{M}{L}{A}{L}{cond}?{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, false, true, true), !pos, !pos) );
{S}{M}{U}{L}{L}{cond}? =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, false, false), !pos, !pos) );
{S}{M}{U}{L}{L}{cond}?{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, false, true), !pos, !pos) );
{S}{M}{L}{A}{L}{cond}? =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, true, false), !pos, !pos) );
{S}{M}{L}{A}{L}{cond}?{S} =>
   ( Tokens.MULT4 ((cond3 yytext, true, true, true, true), !pos, !pos) );

{L}{D}{R}{S}{B}  => ( Tokens.LDRSB_ (!pos, !pos) );
{L}{D}{R}{S}{H}  => ( Tokens.LDRSH_ (!pos, !pos) );
{L}{D}{R}{H}     => ( Tokens.LDRH_ (!pos, !pos) );
{S}{T}{R}{S}?{H} => ( Tokens.STRH_ (!pos, !pos) );
{L}{D}{R}        => ( Tokens.LDR_ (!pos, !pos) );
{L}{D}{R}{B}     => ( Tokens.LDRB_ (!pos, !pos) );
{S}{T}{R}        => ( Tokens.STR_ (!pos, !pos) );
{S}{T}{R}{S}?{B} => ( Tokens.STRB_ (!pos, !pos) );

{L}{D}{R}{cond}{S}{B} =>
   ( Tokens.TRANSH ((true, cond3 yytext, true, false), !pos, !pos) );
{L}{D}{R}{cond}{S}{H} =>
   ( Tokens.TRANSH ((true, cond3 yytext, true, true), !pos, !pos) );
{L}{D}{R}{cond}{H} =>
   ( Tokens.TRANSH ((true, cond3 yytext, false, true), !pos, !pos) );
{S}{T}{R}{cond}{S}?{H} =>
   ( Tokens.TRANSH ((false, cond3 yytext, false, true), !pos, !pos) );
{L}{D}{R}{cond} =>
   ( Tokens.TRANS ((true, cond3 yytext, false), !pos, !pos) );
{L}{D}{R}{cond}{B} =>
   ( Tokens.TRANS ((true, cond3 yytext, true), !pos, !pos) );
{S}{T}{R}{cond} =>
   ( Tokens.TRANS ((false,cond3 yytext, false), !pos, !pos) );
{S}{T}{R}{cond}{S}?{B} =>
   ( Tokens.TRANS ((false,cond3 yytext, true), !pos, !pos) );

{L}{D}{M}({F}{D} | {I}{A}) => ( Tokens.LDMIA_ (!pos, !pos) );
{S}{T}{M}({E}{A} | {I}{A}) => ( Tokens.STMIA_ (!pos, !pos) );

{L}{D}{M}{cond}?({E}{D} | {I}{B}) => ( Tokens.BTRANS ((true, cond3 yytext, true, true), !pos, !pos) );
{L}{D}{M}{cond}({F}{D} | {I}{A}) => ( Tokens.BTRANS ((true, cond3 yytext, false,true), !pos, !pos) );
{L}{D}{M}{cond}?({E}{A} | {D}{B}) => ( Tokens.BTRANS ((true, cond3 yytext, true, false), !pos, !pos) );
{L}{D}{M}{cond}?({F}{A} | {D}{A}) => ( Tokens.BTRANS ((true, cond3 yytext, false,false), !pos, !pos) );
{S}{T}{M}{cond}?({F}{A} | {I}{B}) => ( Tokens.BTRANS ((false,cond3 yytext, true, true), !pos, !pos) );
{S}{T}{M}{cond}({E}{A} | {I}{A}) => ( Tokens.BTRANS ((false,cond3 yytext, false,true), !pos, !pos) );
{S}{T}{M}{cond}?({F}{D} | {D}{B}) => ( Tokens.BTRANS ((false,cond3 yytext, true, false), !pos, !pos) );
{S}{T}{M}{cond}?({E}{D} | {D}{A}) => ( Tokens.BTRANS ((false,cond3 yytext, false,false), !pos, !pos) );

{S}{W}{P}{cond}?    => ( Tokens.SWAP ((cond3 yytext, false), !pos, !pos) );
{S}{W}{P}{cond}?{B} => ( Tokens.SWAP ((cond3 yytext, true), !pos, !pos) );
{M}{R}{S}{cond}?    => ( Tokens.MRS  (cond3 yytext, !pos, !pos) );
{M}{S}{R}{cond}?    => ( Tokens.MSR  (cond3 yytext, !pos, !pos) );
{C}{D}{P}{cond}?    => ( Tokens.CDP  (cond3 yytext, !pos, !pos) );
{M}{C}{R}{cond}?    => ( Tokens.MCR_MRC ((cond3 yytext, false), !pos, !pos) );
{M}{R}{C}{cond}?    => ( Tokens.MCR_MRC ((cond3 yytext, true), !pos, !pos) );
{L}{D}{C}{cond}?    => ( Tokens.LDC_STC ((true, cond3 yytext, false), !pos, !pos) );
{L}{D}{C}{cond}?{L} => ( Tokens.LDC_STC ((true, cond3 yytext, true), !pos, !pos) );
{S}{T}{C}{cond}?    => ( Tokens.LDC_STC ((false,cond3 yytext, false), !pos, !pos) );
{S}{T}{C}{cond}?{L} => ( Tokens.LDC_STC ((false,cond3 yytext, true), !pos, !pos) );
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
