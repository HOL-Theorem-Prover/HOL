{
 open Lexing Parser Data;

 exception LexicalError of string * int * int (* (message, loc1, loc2) *)

 fun lexerError lexbuf s =
     raise LexicalError (s, getLexemeStart lexbuf, getLexemeEnd lexbuf);

 fun int2register n =
   case n of
     0  => R0  | 1  => R1  | 2  => R2  | 3 => R3
   | 4  => R4  | 5  => R5  | 6  => R6  | 7 => R7
   | 8  => R8  | 9  => R9  | 10 => R10 | 11 => R11
   | 12 => R12 | 13 => R13 | 14 => R14 | 15 => R15
   | _ =>  raise ERR "int2register" "not a register list";

 fun str2cond skp s =
   (case String.map Char.toLower (String.extract(s,skp,SOME 2)) of
     "eq" => EQ | "ne" => NE | "cs" => CS | "cc" => CC
   | "mi" => MI | "pl" => PL | "vs" => VS | "vc" => VC
   | "hi" => HI | "ls" => LS | "ge" => GE | "lt" => LT
   | "gt" => GT | "le" => LE | "nv" => NV | _ => AL)
   handle Subscript => AL;

 fun str2opc s =
   case String.map Char.toLower (String.extract(s,0,SOME 3)) of
     "and" => AND | "eor" => EOR | "sub" => SUB | "rsb" => RSB
   | "add" => ADD | "adc" => ADC | "sbc" => SBC | "rsc" => RSC
   | "tst" => TST | "teq" => TEQ | "cmp" => CMP | "cmn" => CMN
   | "orr" => ORR | "mov" => MOV | "bic" => BIC | "mvn" => MVN
   | _ => raise ERR "str2opc" "not an opcode";

 fun strSkip n s = String.extract(s,n,NONE);

 val str2int = valOf o Int.fromString o strSkip 1;
 val str2reg = int2register o str2int;

 val hexnum = Arbnum.fromHexString o getLexeme;
 val octnum = Arbnum.fromOctString o getLexeme;
 val decnum = Arbnum.fromString o getLexeme;

 fun binnum lexbuf =
   let val s = getLexeme lexbuf in
     if String.sub(s,0) = #"+" then
       Arbnum.fromBinString (strSkip 3 s)
     else
       Arbnum.fromBinString (strSkip 2 s)
   end;

 val cond1 = str2cond 1 o getLexeme;
 val cond2 = str2cond 2 o getLexeme;
 val cond3 = str2cond 3 o getLexeme;

 val opc1 = str2opc o getLexeme
 val reg1 = str2reg o getLexeme
 }

let A = [`a``A`] let B = [`b``B`] let C = [`c``C`] let D = [`d``D`]
let E = [`e``E`] let F = [`f``F`] let G = [`g``G`] let H = [`h``H`]
let I = [`i``I`] let L = [`l``L`]
let M = [`m``M`] let N = [`n``N`] let O = [`o``O`] let P = [`p``P`]
let Q = [`q``Q`] let R = [`r``R`] let S = [`s``S`] let T = [`t``T`]
let U = [`u``U`] let V = [`v``V`] let W = [`w``W`] let X = [`x``X`]
let cond = (E Q | N E | C S | H S | C C | L O | M I | P L | V S
          | V C | H I | L S | G E | L T | G T | L E | A L | N V)?
let opcode1 = T S T | T E Q | C M P | C M N
let opcode2 = A N D | E O R | S U B | R S B | A D D
            | A D C | S B C | R S C | O R R | B I C
let opcode3 = M O V | M V N
rule Token = parse
    [` ``\t``\n``\r`]+               { Token lexbuf }
  | `+`?"0x"[`0`-`9``a`-`f``A`-`F`]+ { NUMBER (hexnum lexbuf) }
  | `+`?"0b"[`0`-`1`]+               { NUMBER (binnum lexbuf) }
  | `+`?`0`[`0`-`7`]+                { NUMBER (octnum lexbuf) }
  | `+`?[`1`-`9`][`0`-`9`]*          { NUMBER (decnum lexbuf) }
  | `+`?`0`                          { NUMBER Arbnum.zero }
  | R [`0`-`9`]             { REG (reg1 lexbuf) }
  | R `1`[`0`-`5`]          { REG (reg1 lexbuf) }
  | C [`0`-`9`]             { COREG (reg1 lexbuf) }
  | C `1`[`0`-`5`]          { COREG (reg1 lexbuf) }
  | P [`0`-`9`]             { COPROC (str2int (getLexeme lexbuf)) }
  | P `1`[`0`-`5`]          { COPROC (str2int (getLexeme lexbuf)) }
  | S P                     { REG R13 }
  | L R                     { REG R14 }
  | P C                     { REG R15 }
  | A S L                   { SHIFT LSL }
  | L S L                   { SHIFT LSL }
  | L S R                   { SHIFT LSR }
  | A S R                   { SHIFT ASR }
  | R O R                   { SHIFT ROR }
  | R R X                   { RRX }
  | C P S R                 { PSR false }
  | S P S R                 { PSR true }
  | C P S R `_``c`(`t``l`)? { PSRF (false,false,true) }
  | C P S R `_``f`(`l``g`)? { PSRF (false,true,false) }
  | C P S R `_``a`(`l``l`)? { PSRF (false,true,true) }
  | S P S R `_``c`(`t``l`)? { PSRF (true,false,true) }
  | S P S R `_``f`(`l``g`)? { PSRF (true,true,false) }
  | S P S R `_``a`(`l``l`)? { PSRF (true,true,true) }
  | B cond                  { BRANCH (cond1 lexbuf,false) }
  | B L cond                { BRANCH (cond2 lexbuf,true) }
  | S W I cond              { SWI_EX (cond3 lexbuf) }
  | opcode1 cond            { DPROC1 (opc1 lexbuf, cond3 lexbuf, true) }
  | opcode2 cond            { DPROC2 (opc1 lexbuf, cond3 lexbuf, false) }
  | opcode2 cond S          { DPROC2 (opc1 lexbuf, cond3 lexbuf, true) }
  | opcode3 cond            { DPROC1 (opc1 lexbuf, cond3 lexbuf, false) }
  | opcode3 cond S          { DPROC1 (opc1 lexbuf, cond3 lexbuf, true) }
  | M U L cond              { MULT   (cond3 lexbuf, false) }
  | M U L cond S            { MULT   (cond3 lexbuf, true) }
  | M L A cond              { MULTA  (cond3 lexbuf, false) }
  | M L A cond S            { MULTA  (cond3 lexbuf, true) }
  | L D R cond              { STRANS (true, cond3 lexbuf, false) }
  | L D R cond B            { STRANS (true, cond3 lexbuf, true) }
  | S T R cond              { STRANS (false,cond3 lexbuf, false) }
  | S T R cond B            { STRANS (false,cond3 lexbuf, true) }
  | L D M cond (E D | I B)  { BTRANS (true, cond3 lexbuf, true, true) }
  | L D M cond (F D | I A)  { BTRANS (true, cond3 lexbuf, false,true) }
  | L D M cond (E A | D B)  { BTRANS (true, cond3 lexbuf, true, false) }
  | L D M cond (F A | D A)  { BTRANS (true, cond3 lexbuf, false,false) }
  | S T M cond (F A | I B)  { BTRANS (false,cond3 lexbuf, true, true) }
  | S T M cond (E A | I A)  { BTRANS (false,cond3 lexbuf, false,true) }
  | S T M cond (F D | D B)  { BTRANS (false,cond3 lexbuf, true, false) }
  | S T M cond (E D | D A)  { BTRANS (false,cond3 lexbuf, false,false) }
  | S W P cond              { SWAP   (cond3 lexbuf, false) }
  | S W P cond B            { SWAP   (cond3 lexbuf, true) }
  | M R S cond              { MRS    (cond3 lexbuf) }
  | M S R cond              { MSR    (cond3 lexbuf) }
  | C D P cond              { CDP    (cond3 lexbuf) }
  | M C R cond              { MCR_MRC (cond3 lexbuf, true) }
  | M R C cond              { MCR_MRC (cond3 lexbuf, false) }
  | L D C cond              { LDC_STC (true, cond3 lexbuf, false) }
  | L D C cond L            { LDC_STC (true, cond3 lexbuf, true) }
  | S T C cond              { LDC_STC (false,cond3 lexbuf, false) }
  | S T C cond L            { LDC_STC (false,cond3 lexbuf, true) }
  | `{`                     { LBRACE }
  | `}`                     { RBRACE }
  | `[`                     { LSQUARE }
  | `]`                     { RSQUARE }
  | `#`                     { HASH }
  | `-`                     { MINUS }
  | `+`                     { PLUS }
  | `!`                     { EXCLAIM }
  | `,`                     { COMMA }
  | `^`                     { HAT }
  | eof                     { EOF }
  | _                       { lexerError lexbuf "Illegal symbol in input" }
;
