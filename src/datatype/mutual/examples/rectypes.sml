(* ========================================================================= *)
(* Some (mutually, nested) recursive types from various sources, collected   *)
(* by jrh.                                                                   *)
(* ========================================================================= *)

app load ["mutualLib", "optionTheory"]; open mutualLib;

fun basic_define_type n l q = 
 Define_type.define_type{name=n,type_spec=q,fixities = l};

val _ = time (define_type []) 
         `Term = Var of 'A => 'B 
               | App of bool => Termlist;
      Termlist = Emp 
               | Consp of Term => Termlist`;

val _ = time (basic_define_type "List" [Prefix,Prefix])
      `List = Nil 
            | Cons of 'A => List`;;

val _ = time (basic_define_type "Btree" [Prefix,Prefix])
    `Btree = Lf of 'A 
           | Nd of 'B => Btree => Btree`;;

val _ = time (define_type [])
    `Command = Assign of ind => Express
             | If of Express => Command
             | Ite of Express => Command => Command
             | While of Express => Command
             | Do of Command => Express;

     Express = Constant of num
             | Variable of ind
             | Summ of Express => Express
             | Product of Express => Express`;

val _ = time (define_type []) 
    `testa = empty_testa 
           | cons_testa of testa => testb;
     testb = contentb of 'L => testc;
     testc = connection of 'M => testa`;;

val _ = time (define_type [])
    `atexp = Varb of ind 
           | Let of dec => exp;

       exp = Exp1 of atexp 
           | Exp2 of exp => atexp 
           | Exp3 of match;

     match = Match1 of rule 
           | Matches of rule => match;

     rule  = Rule of pat => exp;
       dec = Val of valbind 
           | Local of dec => dec 
           | Decs of dec => dec;

   valbind = Single of pat => exp 
           | Multi of pat => exp => valbind 
           | Rec of valbind;

       pat = Wild 
           | Varpat of ind`;;

val _ = time (basic_define_type "tri" [Prefix,Prefix,Prefix])
     `tri = ONE | TWO | THREE`;

(* ------------------------------------------------------------------------- *)
(* A couple from Steve Brackin's work.                                       *)
(* ------------------------------------------------------------------------- *)

val _ = time (basic_define_type "Steve1" 
  [Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
   Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
   Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
   Prefix,Prefix,Prefix,Prefix])
      `Steve0 = X1  | X2  | X3  | X4  | X5  | X6  | X7  | X8  | X9  | X10 |
                X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 |
                X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | 
                X31 | X32 | X33 | X34`;;

val _ = time (define_type [])
    `TY1 = NoF__ 
         | Fk__ of 'A => TY2;

     TY2 = Ta__   of bool 
         | Td__   of bool 
         | Tf__   of TY1 
         | Tk__   of bool 
         | Tp__   of bool
         | App__  of 'A => TY1 => TY2 => TY3 
         | Pair__ of TY2 => TY2;

     TY3 = NoS__ 
         | Fresh__        of TY2 
         | Trustworthy__  of 'A
         | PrivateKey__   of 'A => 'B => 'C 
         | PublicKey__    of 'A => 'B => 'C
         | Conveyed__     of 'A => TY2 
         | Possesses__    of 'A => TY2 
         | Received__     of 'A => TY2 
         | Recognizes__   of 'A => TY2 
         | Sends__        of 'A => TY2 => 'B 
         | SharedSecret__ of 'A => TY2 => 'B
         | Believes__     of 'A => TY3 
         | And__          of TY3 => TY3
         | NeverMalFromSelf__ of 'A => 'B => TY2`;;

(* ------------------------------------------------------------------------- *)
(* Some with nesting of various kinds, plus required auxiliaries.            *)
(* ------------------------------------------------------------------------- *)

val _ = time (define_type [listTheory.list_Axiom])
   `term = Vari of ind     (* ind was int *)
         | Fni of ind => term list`;

val _ = time (define_type [pairTheory.pair_Axiom])
  `bintree = Leafb 
           | Branchb of bintree # bintree`;

val _  = time (define_type [sumTheory.sum_Axiom])
  `etree = Terminal 
         | Nonterminal of num + etree`;

val _ = time (define_type [optionTheory.option_Axiom])
  `ptree = Only of ptree option`;;

val def5 = time (define_type [])
  `mutual = Mutual of 'A => mutual => 'D => otherone 
          | Friend of 'D => otherone;
 otherone = Great of 'C 
          | Expectations of mutual => otherone`;;

(* Need to prove rec'n thm for mutual first *)
val def6 = time (define_type [#New_Ty_Existence_Thm def5])
  `groof = Wu of bool
         | Wibble of ('A,groof,'L)mutual
         | Wobble of groof => groof`;

val _ = time (define_type [listTheory.list_Axiom, sumTheory.sum_Axiom])
  `biterm = Variab of ind
          | Fnapp of biterm list + biterm list`;

val _ = time (define_type [listTheory.list_Axiom, sumTheory.sum_Axiom])
  `triterm = Var0 of ind
           | Fun2 of triterm list + triterm list
           | Fun1 of triterm list`;;

val _ = time (define_type [listTheory.list_Axiom])
    `xtree = Leafx of 'A
           | Branchx of xtree list`;;

(* Need to prove rec'n thm for xtree first *)
val def10 = time (define_type [xtree_Axiom])
  `simper = Leaves of 'A => 'B
          | Bough of simper xtree`;;

val def11 = time (basic_define_type "array" [Prefix])
  `array = Array of num => 'A list`;

(* Need to prove rec'n thms for xtree and array first *)
val def12 = time (define_type [listTheory.list_Axiom, xtree_Axiom, def11])
  `value = Integer of num
         | Boolean of bool
         | List of value list
         | Tree of value xtree
         | Array of value array`;;

val _ = time (define_type [listTheory.list_Axiom,pairTheory.pair_Axiom])
  `command 
       = Assignment of num list # expression list
       | Sequence   of command list
   ;
   expression 
       = Numeral of num
       | Plus    of expression # expression
       | Valof   of command`;;

(* Need recursion theorem for mutual_Axiom *)
val def14 = time (define_type[mutual_Axiom,listTheory.list_Axiom,
                              pairTheory.pair_Axiom])
  `zonk = Stonk of ((zonk,pink,'A)mutual)list # expression
        | Tonk of zonk => pink list
        | Honk of num;
   pink = Floyd of zonk # pink
        | Purple of num
        | Rain of 'A # pink`;;

(* ------------------------------------------------------------------------- *)
(* Example from Konrad: 68000 instruction set.                               *)
(* ------------------------------------------------------------------------- *)

time (basic_define_type "SZ" [Prefix,Prefix,Prefix])
      `Size = Byte | Word | Long`;;

time (basic_define_type "DataRegister" 
  [Prefix,Prefix,Prefix,Prefix, Prefix,Prefix,Prefix,Prefix])
  `DataRegister 
       = RegD0
       | RegD1
       | RegD2
       | RegD3
       | RegD4
       | RegD5
       | RegD6
       | RegD7`;

time (basic_define_type "AddressRegister" 
 [Prefix,Prefix,Prefix,Prefix, Prefix,Prefix,Prefix,Prefix])
  `AddressRegister 
          = RegA0
          | RegA1
          | RegA2
          | RegA3
          | RegA4
          | RegA5
          | RegA6
          | RegA7`;;

time (basic_define_type "DataOrAddressRegister" [Prefix,Prefix])
 `DataOrAddressRegister
               = data of DataRegister
               | address of AddressRegister`;

time (basic_define_type "Condition" 
[Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix])
    `Condition 
         = Hi
         | Ls
         | Cc
         | Cs
         | Ne
         | Eq
         | Vc
         | Vs
         | Pl
         | Mi
         | Ge
         | Lt
         | Gt
         | Le`;;

time (basic_define_type "AddressingMode" 
[Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix])
 `AddressingMode 
        = immediate of  num
        | direct of DataOrAddressRegister
        | indirect of AddressRegister
        | postinc of AddressRegister
        | predec of AddressRegister
        | indirectdisp of num => AddressRegister
        | indirectindex of num => AddressRegister => 
                           DataOrAddressRegister => Size
        | absolute of num
        | pcdisp of num
        | pcindex of num => DataOrAddressRegister => Size`;;

(* 60 Meg. 
    runtime: 819.080s,    gctime: 101.500s,     systime: 0.780s.
*)
time (basic_define_type "M68kInstruction"
[Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,
 Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix])
`M68kInstruction
    = ABCD of AddressingMode => AddressingMode
    | ADD of Size => AddressingMode => AddressingMode
    | ADDA of Size => AddressingMode => AddressRegister
    | ADDI of Size => num => AddressingMode
    | ADDQ of Size => num => AddressingMode
    | ADDX of Size => AddressingMode => AddressingMode
    | AND of Size => AddressingMode => AddressingMode
    | ANDI of Size => num => AddressingMode
    | ANDItoCCR of num
    | ANDItoSR of num
    | ASL of Size => AddressingMode => DataRegister
    | ASLW of AddressingMode
    | ASR of Size => AddressingMode => DataRegister
    | ASRW of AddressingMode
    | Bcc of Condition => Size => num
    | BTST of Size => AddressingMode => AddressingMode
    | BCHG of Size => AddressingMode => AddressingMode
    | BCLR of Size => AddressingMode => AddressingMode
    | BSET of Size => AddressingMode => AddressingMode
    | BRA of Size => num
    | BSR of Size => num
    | CHK of AddressingMode => DataRegister
    | CLR of Size => AddressingMode
    | CMP of Size => AddressingMode => DataRegister
    | CMPA of Size => AddressingMode => AddressRegister
    | CMPI of Size => num => AddressingMode
    | CMPM of Size => AddressRegister => AddressRegister
    | DBT of DataRegister => num
    | DBF of DataRegister => num
    | DBcc of Condition => DataRegister => num
    | DIVS of AddressingMode => DataRegister
    | DIVU of AddressingMode => DataRegister
    | EOR of Size => DataRegister => AddressingMode
    | EORI of Size => num => AddressingMode
    | EORItoCCR of num
    | EORItoSR of num
    | EXG of DataOrAddressRegister => DataOrAddressRegister
    | EXT of Size => DataRegister
    | ILLEGAL
    | JMP of AddressingMode
    | JSR of AddressingMode
    | LEA of AddressingMode => AddressRegister
    | LINK of AddressRegister => num
    | LSL of Size => AddressingMode => DataRegister
    | LSLW of AddressingMode
    | LSR of Size => AddressingMode => DataRegister
    | LSRW of AddressingMode
    | MOVE of Size => AddressingMode => AddressingMode
    | MOVEtoCCR of AddressingMode
    | MOVEtoSR of AddressingMode
    | MOVEfromSR of AddressingMode
    | MOVEtoUSP of AddressingMode
    | MOVEfromUSP of AddressingMode
    | MOVEA of Size => AddressingMode => AddressRegister
    | MOVEMto of Size => AddressingMode => DataOrAddressRegister list
    | MOVEMfrom of Size => DataOrAddressRegister list => AddressingMode
    | MOVEP of Size => AddressingMode => AddressingMode
    | MOVEQ of num => DataRegister
    | MULS of AddressingMode => DataRegister
    | MULU of AddressingMode => DataRegister
    | NBCD of AddressingMode
    | NEG of Size => AddressingMode
    | NEGX of Size => AddressingMode
    | NOP
    | NOT of Size => AddressingMode
    | OR of Size => AddressingMode => AddressingMode
    | ORI of Size => num => AddressingMode
    | ORItoCCR of num
    | ORItoSR of num
    | PEA of AddressingMode
    | RESET
    | ROL of Size => AddressingMode => DataRegister
    | ROLW of AddressingMode
    | ROR of Size => AddressingMode => DataRegister
    | RORW of AddressingMode
    | ROXL of Size => AddressingMode => DataRegister
    | ROXLW of AddressingMode
    | ROXR of Size => AddressingMode => DataRegister
    | ROXRW of AddressingMode
    | RTE
    | RTR
    | RTS
    | SBCD of AddressingMode => AddressingMode
    | ST of AddressingMode
    | SF of AddressingMode
    | Scc of Condition => AddressingMode
    | STOP of num
    | SUB of Size => AddressingMode => AddressingMode
    | SUBA of Size => AddressingMode => AddressingMode
    | SUBI of Size => num => AddressingMode
    | SUBQ of Size => num => AddressingMode
    | SUBX of Size => AddressingMode => AddressingMode
    | SWAP of DataRegister
    | TAS of AddressingMode
    | TRAP of num
    | TRAPV
    | TST of Size => AddressingMode
    | UNLK of AddressRegister`;;


(* ------------------------------------------------------------------------- *)
(* Example from Myra: part of the syntax of SML.                             *)
(* ------------------------------------------------------------------------- *)

val str_ax = time (basic_define_type "string" [Prefix,Prefix])
  `string = EMPTY_STRING 
          | CONS_STRING of num => string`;

val _ = time (define_type [])
  `strid = STRID of string;
   var = VAR of string;
   con = CON of string;
   scon = SCINT of num  (* was int *)
        | SCSTR of string;
   excon = EXCON of string;
   label = LABEL of string`;;

val nel_ax = time (basic_define_type "nonemptylist" [Prefix])
  `nonemptylist = Head_and_tail of 'A => 'A list`;;

val long_ax = time (basic_define_type "long" [Prefix,Prefix])
  `long = BASE of 'A | QUALIFIED of strid => long`;;


(* runtime on sole: 1251.940s,    gctime: 176.740s,     systime: 1.080s. *)

val _ = time (define_type [long_ax, optionTheory.option_Axiom,nel_ax])
  `atpat_e = WILDCARDatpat_e
           | SCONatpat_e   of scon
           | VARatpat_e    of var
           | CONatpat_e    of con long
           | EXCONatpat_e  of excon long
           | RECORDatpat_e of patrow_e option
           | PARatpat_e    of pat_e;

   patrow_e = DOTDOTDOT_e
            | PATROW_e of label => pat_e => patrow_e option;

   pat_e = ATPATpat_e   of atpat_e
         | CONpat_e     of con long => atpat_e
         | EXCONpat_e   of excon long => atpat_e
         | LAYEREDpat_e of var => pat_e;

   conbind_e = CONBIND_e of con => conbind_e option;

   datbind_e = DATBIND_e of conbind_e => datbind_e option;

   exbind_e = EXBIND1_e of excon => exbind_e option
            | EXBIND2_e of excon => excon long => exbind_e option;

   atexp_e = SCONatexp_e   of scon
           | VARatexp_e    of var long
           | CONatexp_e    of con long
           | EXCONatexp_e  of excon long
           | RECORDatexp_e of exprow_e option
           | LETatexp_e    of dec_e => exp_e
           | PARatexp_e    of exp_e;

   exprow_e = EXPROW_e of label => exp_e => exprow_e option;

   exp_e = ATEXPexp_e  of atexp_e
         | APPexp_e    of exp_e => atexp_e
         | HANDLEexp_e of exp_e => match_e
         | RAISEexp_e  of exp_e
         | FNexp_e     of match_e;

   match_e = MATCH_e of mrule_e => match_e option;

   mrule_e = MRULE_e of pat_e => exp_e;

   dec_e = VALdec_e      of valbind_e
         | DATATYPEdec_e of datbind_e
         | ABSTYPEdec_e  of datbind_e => dec_e
         | EXCEPTdec_e   of exbind_e
         | LOCALdec_e    of dec_e => dec_e
         | OPENdec_e     of (strid long) nonemptylist
         | EMPTYdec_e
         | SEQdec_e      of dec_e => dec_e;

   valbind_e = PLAINvalbind_e of pat_e => exp_e => valbind_e option
             | RECvalbind_e   of valbind_e`;;

(* ------------------------------------------------------------------------- *)
(* Example from Daryl: a Verilog grammar.                                    *)
(* ------------------------------------------------------------------------- *)

val _ = time (define_type [listTheory.list_Axiom, optionTheory.option_Axiom])
  `Source_text
     = module of string => string list => Module_item list
     | Source_textMeta of string;
  Module_item
     = declaration of Declaration
     | initial of Statement
     | always of Statement
     | assign of Lvalue => Expression
     | Module_itemMeta of string;
  Declaration
     = reg_declaration of Range option => string list
     | net_declaration of Range option => string list
     | input_declaration of Range option => string list
     | output_declaration of Range option => string list
     | DeclarationMeta of string;
  Range = range of Expression => Expression 
        | RangeMeta of string;
  Statement
     = clock_statement of Clock => Statement_or_null
     | blocking_assignment of Lvalue => Expression
     | non_blocking_assignment of Lvalue => Expression
     | conditional_statement of Expression => Statement_or_null 
                                => Statement_or_null option
     | case_statement of Expression => Case_item list
     | while_loop of Expression => Statement
     | repeat_loop of Expression => Statement
     | for_loop of Lvalue => Expression => Expression 
                   => Lvalue => Expression => Statement
     | forever_loop of Statement
     | disable of string
     | seq_block of string option => Statement list
     | StatementMeta of string;
  Statement_or_null = statement of Statement 
                    | null_statement 
                    | Statement_or_nullMeta of string;
  Clock
     = posedge of string
     | negedge of string
     | clock of string
     | ClockMeta of string;
  Case_item
     = case_item of Expression list => Statement_or_null
     | default_case_item of Statement_or_null
     | Case_itemMeta of string;
  Expression
     = plus    of Expression => Expression
     | minus   of Expression => Expression
     | lshift  of Expression => Expression
     | rshift  of Expression => Expression
     | lt      of Expression => Expression
     | leq     of Expression => Expression
     | gt      of Expression => Expression
     | geq     of Expression => Expression
     | logeq   of Expression => Expression
     | logneq  of Expression => Expression
     | caseeq  of Expression => Expression
     | caseneq of Expression => Expression
     | bitand  of Expression => Expression
     | bitxor  of Expression => Expression
     | bitor   of Expression => Expression
     | logand  of Expression => Expression
     | logor   of Expression => Expression
     | conditional of Expression => Expression => Expression
     | positive  of Primary
     | negative  of Primary
     | lognot    of Primary
     | bitnot    of Primary
     | reducand  of Primary
     | reducxor  of Primary
     | reducor   of Primary
     | reducnand of Primary
     | reducxnor of Primary
     | reducnor  of Primary
     | primary   of Primary
     | ExpressionMeta of string;
  Primary
     = primary_number of Number
     | primary_IDENTIFIER of string
     | primary_bit_select of string => Expression
     | primary_part_select of string => Expression => Expression
     | primary_gen_bit_select of Expression => Expression
     | primary_gen_part_select of Expression => Expression => Expression
     | primary_concatenation of Concatenation
     | primary_multiple_concatenation of Multiple_concatenation
     | brackets of Expression
     | PrimaryMeta of string;
  Lvalue
     = lvalue of string
     | lvalue_bit_select of string => Expression
     | lvalue_part_select of string => Expression => Expression
     | lvalue_concatenation of Concatenation
     | LvalueMeta of string;
  Number
     = decimal of string
     | based of string option => string
     | NumberMeta of string;
  Concatenation
     = concatenation of Expression list
     | ConcatenationMeta of string;
  Multiple_concatenation
     = multiple_concatenation of Expression => Expression list
     | Multiple_concatenationMeta of string;
  meta
     = Meta_Source_text of Source_text
     | Meta_Module_item of Module_item
     | Meta_Declaration of Declaration
     | Meta_Range of Range
     | Meta_Statement of Statement
     | Meta_Statement_or_null of Statement_or_null
     | Meta_Clock of Clock
     | Meta_Case_item of Case_item
     | Meta_Expression of Expression
     | Meta_Primary of Primary
     | Meta_Lvalue of Lvalue
     | Meta_Number of Number
     | Meta_Concatenation of Concatenation
     | Meta_Multiple_concatenation of Multiple_concatenation`;;
