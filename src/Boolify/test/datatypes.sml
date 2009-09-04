(* ========================================================================= *)
(* Some (mutually, nested) recursive types from various sources, collected   *)
(* by jrh.                                                                   *)
(* Additions by Joe Hurd, June 2002.                                         *)
(* ========================================================================= *)

val () =
  loadPath :=
  ["../../../../ptr/hol/src/datatype/", "../../../../ptr/hol/src/list/src",
   "../../../../ptr/hol/src/tfl/src", "../../../../ptr/hol/src/Boolify/src"] @
  !loadPath;

app load ["Datatype", "listTheory", "PreListBoolify"];

fun first_token (QUOTE s :: _) = hd (String.tokens Char.isSpace (Lib.deinitcomment s));
val size_of = Lib.total TypeBase.size_of;
val boolify_of = Lib.total TypeBase.boolify_of;

val Hol_datatype =
  fn q =>
  let
    val () = Lib.try (Count.apply Datatype.Hol_datatype) q
    val tyname = first_token q
  in
    (tyname, size_of tyname, boolify_of tyname)
  end;

(* ------------------------------------------------------------------------- *)
(* Very small examples to test basic functionality of datatype package.      *)
(* ------------------------------------------------------------------------- *)

Hol_datatype `NumBool = Num of num | Bool of bool`;

Hol_datatype
  `NumBoolNums = Num of num | Bool of bool | Nums of num list`;

Hol_datatype `NTree = Tree of NTree list`;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous examples.                                                   *)
(* ------------------------------------------------------------------------- *)

Hol_datatype
         `Term = Var of 'A => 'B
               | App of bool => Termlist;
      Termlist = Emp
               | Consp of Term => Termlist`;

Hol_datatype
      `List = Nil
            | Cons of 'A => List`;

Hol_datatype
    `Btree = Lf of 'A
           | Nd of 'B => Btree => Btree`;

Hol_datatype
    `Command = Assign of ind => Express
             | If of Express => Command
             | Ite of Express => Command => Command
             | While of Express => Command
             | Do of Command => Express;

     Express = Constant of num
             | Variable of ind
             | Summ of Express => Express
             | Product of Express => Express`;

Hol_datatype
    `testa = empty_testa
           | cons_testa of testa => testb;
     testb = contentb of 'L => testc;
     testc = connection of 'M => testa`;

Hol_datatype
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
           | Varpat of ind`;

Hol_datatype
     `tri = ONE | TWO | THREE`;

(* ------------------------------------------------------------------------- *)
(* A couple from Steve Brackin's work.                                       *)
(* ------------------------------------------------------------------------- *)

Hol_datatype
      `Steve0 = X1  | X2  | X3  | X4  | X5  | X6  | X7  | X8  | X9  | X10 |
                X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 |
                X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 |
                X31 | X32 | X33 | X34`;

Hol_datatype
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
         | NeverMalFromSelf__ of 'A => 'B => TY2`;

(* ------------------------------------------------------------------------- *)
(* Some with nesting of various kinds, plus required auxiliaries.            *)
(* ------------------------------------------------------------------------- *)

Hol_datatype `fot = aVar of 'a
                  | bApp of 'b => fot list`;

Hol_datatype
   `term = Vari of ind
         | Fni of ind => term list`;

Hol_datatype
  `bintree = Leafb
           | Branchb of bintree # bintree`;

Hol_datatype
  `etree = Terminal
         | Nonterminal of num + etree`;

Hol_datatype
  `ptree = Only of ptree option`;

Hol_datatype
  `biterm = Variab of ind
          | Fnapp of biterm list + biterm list`;

Hol_datatype
  `triterm = Var0 of ind
           | Fun2 of triterm list + triterm list
           | Fun1 of triterm list`;

Hol_datatype
    `xtree = Leafx of 'A
           | Branchx of xtree list`;

Hol_datatype
  `array = Arry of num => 'A list`;

Lib.try Hol_datatype
  `value = Integer of num
         | Boolean of bool
         | List of value list
         | Tree of value xtree
         | Array of value array`;

Hol_datatype
  `simper = Leaves of 'a => 'b
          | Bough of simper xtree`;

Lib.try Hol_datatype  (* used to fail *)
  `simper = Leaves of 'A => 'B
          | Bough of simper xtree`;

Hol_datatype
  `command
       = Assignment of num list # expression list
       | Sequence   of command list
   ;
   expression
       = Numeral of num
       | Plus    of expression # expression
       | Valof   of command`;


Hol_datatype
  `mutual = Mutual of 'A => mutual => 'D => otherone
          | Friend of 'D => otherone;
 otherone = Great of 'C
          | Expectations of mutual => otherone`;

(* loops? *)
Hol_datatype
  `groof = Wu of bool
         | Wibble of ('A,groof,'L)mutual
         | Wobble of groof => groof`;

(* loops? *)
Hol_datatype
  `zonk = Stonk of ((zonk,pink,'A)mutual)list # expression
        | Tonk of zonk => pink list
        | Honk of num;
   pink = Floyd of zonk # pink
        | Purple of num
        | Rain of 'A # pink`;

Hol_datatype `T1 = CONSTR1 of 'a`;

Lib.try
Hol_datatype `T2 = CONSTR2 of T3 list => 'a T1
                 ;
              T3 = CONSTR31 of 'a T1
                 | CONSTR32 of T2
                 | CONSTR33 of 'b`;

Hol_datatype `T4 = CONSTR4 of ('a,'b)T2 set`;

Hol_datatype `ty1 = C1 of 'a
                  | C2 of ty2 option
               ;
              ty2 = C3 of 'b
                  | C4 of ty1 list option`;

delete_type "exp"; scrub();
Hol_datatype
        `exp = VAR of 'a
             | IF  of bexp => exp => exp
             | APP of 'b => exp list
          ;
        bexp = EQ  of exp => exp
             | LEQ of exp => exp
             | AND of bexp => bexp
             | OR  of bexp => bexp
             | NOT of bexp`;

(*---------------------------------------------------------------------------
   Example from Peter Homeier (tweaked)
 ---------------------------------------------------------------------------*)


Hol_datatype

       (* obj ::= x | [li=mi] i in 1..n |  a.l | a.l:=m *)

        `obj  = OVAR of 'a
              | OBJ of (string # method) list
              | INVOKE of obj => string
              | UPDATE of obj => string => method ;

        (* method ::= sigma x. o *)

          method = SIGMA of 'a => obj` ;

val REM_ALL_def =
 Define
  `(REM_ALL x [] = []) /\
   (REM_ALL x (h::t) = if x=h then REM_ALL x t else h::REM_ALL x t)`;

val LDIFF_def =
 xDefine "LDIFF"
  `(LDIFF L [] = L) /\
   (LDIFF L (h::t) = LDIFF (REM_ALL h L) t)`;

set_fixity "LDIFF" (Infixl 500);

val FV_object =
 xDefine "FV_object"
     `(FV_obj (OVAR x)        = [x])
 /\   (FV_obj (OBJ d)         = FV_dict d)
 /\   (FV_obj (INVOKE o1 l)   = FV_obj o1)
 /\   (FV_obj (UPDATE o1 l m) = APPEND (FV_obj o1) (FV_method m))
 /\   (FV_dict (e::es)        = APPEND (FV_entry e) (FV_dict es))
 /\   (FV_dict  []            = [])
 /\   (FV_entry (l, m)        = FV_method m)
 /\   (FV_method (SIGMA x o1) = (FV_obj o1) LDIFF [x])`;


(*---------------------------------------------------------------------------
   Another example from Peter Homeier.
 ---------------------------------------------------------------------------*)

Hol_datatype
        `(* vexp ::= n | x | SUC v | v+v | v-v | v*v | f (v1,...,vn)  *)

          vexp = ANUM of num
               | AVAR of string
               | ASUC of vexp
               | APLUS of vexp => vexp
               | AMINUS of vexp => vexp
               | AMULT of vexp => vexp
               | ACONDV of aexp => vexp => vexp
               | ACALL of string => vexp list ;

       (* aexp ::= true | false | v=v | v<v | vs<<vs |
                   a/\a | a\/a | ~a | a==>a | a=b |
                   (a=>a|a) | !x.a | ?x.a                  *)

          aexp = ATRUE
               | AFALSE
               | AEQ of vexp => vexp
               | ALESS of vexp => vexp
               | ALLESS of vexp list => vexp list
               | AAND of aexp => aexp
               | AOR of aexp => aexp
               | ANOT of aexp
               | AIMP of aexp => aexp
               | AEQB of aexp => aexp
               | ACOND of aexp => aexp => aexp
               | AFORALL of string => aexp
               | AEXISTS of string => aexp`;

(* ------------------------------------------------------------------------- *)
(* 68000 instruction set.                                                    *)
(* ------------------------------------------------------------------------- *)

Hol_datatype `Size = Byte | Word | Long`;

Hol_datatype
  `DataRegister
       = RegD0
       | RegD1
       | RegD2
       | RegD3
       | RegD4
       | RegD5
       | RegD6
       | RegD7`;

Hol_datatype
  `AddressRegister
          = RegA0
          | RegA1
          | RegA2
          | RegA3
          | RegA4
          | RegA5
          | RegA6
          | RegA7`;

Hol_datatype
 `DataOrAddressRegister
               = data of DataRegister
               | address of AddressRegister`;

Hol_datatype
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
         | Le`;

Hol_datatype
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
        | pcindex of num => DataOrAddressRegister => Size`;

(* Elsa et al. package:
    60 Meg.     runtime: 819.080s,    gctime: 101.500s,     systime: 0.780s.

   JRH package: runtime: 3680.900s,    gctime: 1113.220s,     systime: 5.040s.
*)
Hol_datatype
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
    | UNLK of AddressRegister`;


(* ------------------------------------------------------------------------- *)
(* Example from Myra: part of the syntax of SML.                             *)
(* ------------------------------------------------------------------------- *)

Hol_datatype
  `string = EMPTY_STRING
          | CONS_STRING of num => string`;

Hol_datatype
  `strid = STRID of string;
   var = VAR of string;
   con = CON of string;
   scon = SCINT of num  (* was int *)
        | SCSTR of string;
   excon = EXCON of string;
   label = LABEL of string`;

Hol_datatype
  `nonemptylist = Head_and_tail of 'A => 'A list`;

Hol_datatype
  `long = BASE of 'A | QUALIFIED of strid => long`;


(* runtime on sole: 1251.940s,    gctime: 176.740s,     systime: 1.080s. *)

Hol_datatype
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
             | RECvalbind_e   of valbind_e`;

(* ------------------------------------------------------------------------- *)
(* Example from Daryl: a Verilog grammar.                                    *)
(* ------------------------------------------------------------------------- *)

Hol_datatype
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
     | Meta_Multiple_concatenation of Multiple_concatenation`;

(* ------------------------------------------------------------------------- *)
(* Various sizes of enumerated type.                                         *)
(* ------------------------------------------------------------------------- *)

Hol_datatype `Enum1 = one`;

Hol_datatype `Enum2 = one | two`;

Hol_datatype `Enum3 = one | two | three`;

Hol_datatype `Enum4 = one | two | three | four`;

Hol_datatype `Enum5 = one | two | three | four | five`;

Hol_datatype `Enum6 = one | two | three | four | five | six`;

Hol_datatype `Enum7 = one | two | three | four | five | six | seven`;

Hol_datatype
`Enum30 =
  one | two | three | four | five | six | seven | eight | nine | ten
| eleven | twelve | thirteen | fourteen | fifteen | sixteen | seventeen
| eighteen | nineteen | twenty | twentyone | twentytwo | twentythree
| twentyfour | twentyfive | twentysix | twentyseven | twentyeight
| twentynine | thirty`;

Hol_datatype
`Enum31 =
  one | two | three | four | five | six | seven | eight | nine | ten
| eleven | twelve | thirteen | fourteen | fifteen | sixteen | seventeen
| eighteen | nineteen | twenty | twentyone | twentytwo | twentythree
| twentyfour | twentyfive | twentysix | twentyseven | twentyeight
| twentynine | thirty | thirtyone`;

Hol_datatype
`Enum32 =
  one | two | three | four | five | six | seven | eight | nine | ten
| eleven | twelve | thirteen | fourteen | fifteen | sixteen | seventeen
| eighteen | nineteen | twenty | twentyone | twentytwo | twentythree
| twentyfour | twentyfive | twentysix | twentyseven | twentyeight
| twentynine | thirty | thirtyone | thirtytwo`;

Hol_datatype
`Enum33 =
  one | two | three | four | five | six | seven | eight | nine | ten
| eleven | twelve | thirteen | fourteen | fifteen | sixteen | seventeen
| eighteen | nineteen | twenty | twentyone | twentytwo | twentythree
| twentyfour | twentyfive | twentysix | twentyseven | twentyeight
| twentynine | thirty | thirtyone | thirtytwo | thirtythree`;

Hol_datatype
`Enum34 =
  one | two | three | four | five | six | seven | eight | nine | ten
| eleven | twelve | thirteen | fourteen | fifteen | sixteen | seventeen
| eighteen | nineteen | twenty | twentyone | twentytwo | twentythree
| twentyfour | twentyfive | twentysix | twentyseven | twentyeight
| twentynine | thirty | thirtyone | thirtytwo | thirtythree | thirtyfour`;
