(* ========================================================================= *)
(* Some (mutually, nested) recursive types from various sources.             *)
(* ========================================================================= *)

time define_type "Term = Var A B | App bool Termlist;
              Termlist = Empty | Consp Term Termlist";;

time define_type "List = Nil | Cons A List";;

time define_type "Btree = Leaf A | Node B Btree Btree";;

time define_type "Command = Assign ind Express
                    | If Express Command
                    | Ite Express Command Command
                    | While Express Command
                    | Do Command Express;
            Express = Constant num
                       | Variable ind
                       | Summ Express Express
                       | Product Express Express";;


time define_type "testa = empty_testa | cons_testa testa testb;
            testb = contentb L testc;
            testc = connection M testa";;

time define_type "atexp = Varb ind | Let dec exp;
            exp   = Exp1 atexp | Exp2 exp atexp | Exp3 match;
            match = Match1 rule | Matches rule match;
            rule  = Rule pat exp;
            dec   = Val valbind | Local dec dec | Decs dec dec;
            valbind = Single pat exp | Multi pat exp valbind | Rec valbind;
            pat = Wild | Varpat ind";;

time define_type "tri = ONE | TWO | THREE";;

(* ------------------------------------------------------------------------- *)
(* A couple from Steve Brackin's work.                                       *)
(* ------------------------------------------------------------------------- *)

time define_type "T = X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 |
                X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 |
                X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31 |
                X32 | X33 | X34";;

time define_type "TY1 = NoF__ | Fk__ A TY2;
            TY2 = Ta__ bool | Td__ bool | Tf__ TY1 | Tk__ bool | Tp__ bool
                | App__ A TY1 TY2 TY3 | Pair__ TY2 TY2;
            TY3 = NoS__ | Fresh__ TY2 | Trustworthy__ A
                | PrivateKey__ A B C | PublicKey__ A B C
                | Conveyed__ A TY2 | Possesses__ A TY2 | Received__ A TY2
                | Recognizes__ A TY2 | NeverMalFromSelf__ A B TY2
                | Sends__ A TY2 B | SharedSecret__ A TY2 B
                | Believes__ A TY3 | And__ TY3 TY3";;

(* ------------------------------------------------------------------------- *)
(* Some with nesting of various kinds, plus required auxiliaries.            *)
(* ------------------------------------------------------------------------- *)

let term_INDUCTION,term_RECURSION = time define_type
  "term = Vari int | Fni int (term list)";;

let bintree_INDUCTION,bintree_RECURSION = time define_type
  "bintree = Leafb | Branchb (bintree # bintree)";;

let etree_INDUCTION,etree_RECURSION = time define_type
  "etree = Terminal | Nonterminal (num + etree)";;

let ptree_INDUCTION,ptree_RECURSION = time define_type
  "ptree = Only (ptree option)";;

let mut_INDUCTION,mut_RECURSION = time define_type
  "mutual = Mutual A mutual D otherone | Friend D otherone;
   otherone = Great C | Expectations mutual otherone";;

let groof_INDUCTION,groof_RECURSION = time define_type
  "groof = Wu bool
         | Wibble (A,groof,L)mutual
         | Wobble groof groof";;

let biterm_INDUCTION,biterm_RECURSION = time define_type
  "biterm = Variab int
          | Fnapp (biterm list + biterm list)";;

let triterm_INDUCTION,triterm_RECURSION = time define_type
  "triterm = Var0 int
          | Fun2 (triterm list + triterm list)
          | Fun1 (triterm list)";;

let xtree_INDUCTION,xtree_RECURSION = time define_type
    "xtree = Leafx A
           | Branchx (xtree list)";;

let simper_INDUCTION,simper_RECURSION = time define_type
  "simper = Leaves A B
          | Bough (simper xtree)";;

let array_INDUCTION,array_RECURSION = time define_type
  "array = Array num (A list)";;

let value_INDUCTION,value_RECURSION = time define_type
  "value = Integer num
         | Boolean bool
         | List_of (value list)
         | Tree_of (value xtree)
         | Array_of (value array)";;

let example_INDUCTION,example_RECURSION = time define_type
  "command = Assignment (num list # expression list)
           | Sequence (command list);
   expression = Numeral num
              | Plus (expression # expression)
              | Valof command";;

let zonk_INDUCTION,zonk_RECURSION = time define_type
  "zonk = Stonk ((zonk,pink,A)mutual)list # expression
        | Tonk zonk (pink list)
        | Honk num;
   pink = Floyd (zonk # pink)
        | Purple num
        | Rain (A # pink)";;

(* ------------------------------------------------------------------------- *)
(* Example from Konrad: 68000 instruction set.                               *)
(* ------------------------------------------------------------------------- *)

time define_type "Size = Byte | Word | Long";;

time define_type "DataRegister
              = RegD0
              | RegD1
              | RegD2
              | RegD3
              | RegD4
              | RegD5
              | RegD6
              | RegD7";;

time define_type "AddressRegister
              = RegA0
              | RegA1
              | RegA2
              | RegA3
              | RegA4
              | RegA5
              | RegA6
              | RegA7";;

time define_type "DataOrAddressRegister
              = data DataRegister
              | address AddressRegister";;

time define_type "Condition
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
              | Le";;

time define_type "AddressingMode
        = immediate num
        | direct DataOrAddressRegister
        | indirect AddressRegister
        | postinc AddressRegister
        | predec AddressRegister
        | indirectdisp num AddressRegister
        | indirectindex num AddressRegister DataOrAddressRegister Size
        | absolute num
        | pcdisp num
        | pcindex num DataOrAddressRegister Size";;

time define_type "M68kInstruction
    = ABCD AddressingMode AddressingMode
    | ADD Size AddressingMode AddressingMode
    | ADDA Size AddressingMode AddressRegister
    | ADDI Size num AddressingMode
    | ADDQ Size num AddressingMode
    | ADDX Size AddressingMode AddressingMode
    | AND Size AddressingMode AddressingMode
    | ANDI Size num AddressingMode
    | ANDItoCCR num
    | ANDItoSR num
    | ASL Size AddressingMode DataRegister
    | ASLW AddressingMode
    | ASR Size AddressingMode DataRegister
    | ASRW AddressingMode
    | Bcc Condition Size num
    | BTST Size AddressingMode AddressingMode
    | BCHG Size AddressingMode AddressingMode
    | BCLR Size AddressingMode AddressingMode
    | BSET Size AddressingMode AddressingMode
    | BRA Size num
    | BSR Size num
    | CHK AddressingMode DataRegister
    | CLR Size AddressingMode
    | CMP Size AddressingMode DataRegister
    | CMPA Size AddressingMode AddressRegister
    | CMPI Size num AddressingMode
    | CMPM Size AddressRegister AddressRegister
    | DBT DataRegister num
    | DBF DataRegister num
    | DBcc Condition DataRegister num
    | DIVS AddressingMode DataRegister
    | DIVU AddressingMode DataRegister
    | EOR Size DataRegister AddressingMode
    | EORI Size num AddressingMode
    | EORItoCCR num
    | EORItoSR num
    | EXG DataOrAddressRegister DataOrAddressRegister
    | EXT Size DataRegister
    | ILLEGAL
    | JMP AddressingMode
    | JSR AddressingMode
    | LEA AddressingMode AddressRegister
    | LINK AddressRegister num
    | LSL Size AddressingMode DataRegister
    | LSLW AddressingMode
    | LSR Size AddressingMode DataRegister
    | LSRW AddressingMode
    | MOVE Size AddressingMode AddressingMode
    | MOVEtoCCR AddressingMode
    | MOVEtoSR AddressingMode
    | MOVEfromSR AddressingMode
    | MOVEtoUSP AddressingMode
    | MOVEfromUSP AddressingMode
    | MOVEA Size AddressingMode AddressRegister
    | MOVEMto Size AddressingMode DataOrAddressRegister list
    | MOVEMfrom Size DataOrAddressRegister list AddressingMode
    | MOVEP Size AddressingMode AddressingMode
    | MOVEQ num DataRegister
    | MULS AddressingMode DataRegister
    | MULU AddressingMode DataRegister
    | NBCD AddressingMode
    | NEG Size AddressingMode
    | NEGX Size AddressingMode
    | NOP
    | NOT Size AddressingMode
    | OR Size AddressingMode AddressingMode
    | ORI Size num AddressingMode
    | ORItoCCR num
    | ORItoSR num
    | PEA AddressingMode
    | RESET
    | ROL Size AddressingMode DataRegister
    | ROLW AddressingMode
    | ROR Size AddressingMode DataRegister
    | RORW AddressingMode
    | ROXL Size AddressingMode DataRegister
    | ROXLW AddressingMode
    | ROXR Size AddressingMode DataRegister
    | ROXRW AddressingMode
    | RTE
    | RTR
    | RTS
    | SBCD AddressingMode AddressingMode
    | ST AddressingMode
    | SF AddressingMode
    | Scc Condition AddressingMode
    | STOP num
    | SUB Size AddressingMode AddressingMode
    | SUBA Size AddressingMode AddressingMode
    | SUBI Size num AddressingMode
    | SUBQ Size num AddressingMode
    | SUBX Size AddressingMode AddressingMode
    | SWAP DataRegister
    | TAS AddressingMode
    | TRAP num
    | TRAPV
    | TST Size AddressingMode
    | UNLK AddressRegister";;

(* ------------------------------------------------------------------------- *)
(* Example from Myra: part of the syntax of SML.                             *)
(* ------------------------------------------------------------------------- *)

let string_INDUCTION,string_RECURSION = time define_type
  "string = EMPTY_STRING | CONS_STRING num string";;

let strid_INDUCTION,strid_RECURSION = time define_type
  "strid = STRID string;
   var = VAR string;
   con = CON string;
   scon = SCINT int | SCSTR string;
   excon = EXCON string;
   label = LABEL string";;

let nonemptylist_INDUCTION,nonemptylist_RECURSION = time define_type
  "nonemptylist = Head_and_tail A (A list)";;

let long_INDUCTION,long_RECURSION = time define_type
  "long = BASE A | QUALIFIED strid long";;

let myra_INDUCTION,myra_RECURSION = time define_type
  "atpat_e = WILDCARDatpat_e
           | SCONatpat_e scon
           | VARatpat_e var
           | CONatpat_e (con long)
           | EXCONatpat_e (excon long)
           | RECORDatpat_e (patrow_e option)
           | PARatpat_e pat_e;

   patrow_e = DOTDOTDOT_e
            | PATROW_e label pat_e (patrow_e option);

   pat_e = ATPATpat_e atpat_e
         | CONpat_e (con long) atpat_e
         | EXCONpat_e (excon long) atpat_e
         | LAYEREDpat_e var pat_e;

   conbind_e = CONBIND_e con (conbind_e option);

   datbind_e = DATBIND_e conbind_e (datbind_e option);

   exbind_e = EXBIND1_e excon (exbind_e option)
            | EXBIND2_e excon (excon long) (exbind_e option);

   atexp_e = SCONatexp_e scon
           | VARatexp_e (var long)
           | CONatexp_e (con long)
           | EXCONatexp_e (excon long)
           | RECORDatexp_e (exprow_e option)
           | LETatexp_e dec_e exp_e
           | PARatexp_e exp_e;

   exprow_e = EXPROW_e label exp_e (exprow_e option);

   exp_e = ATEXPexp_e atexp_e
         | APPexp_e exp_e atexp_e
         | HANDLEexp_e exp_e match_e
         | RAISEexp_e exp_e
         | FNexp_e match_e;

   match_e = MATCH_e mrule_e (match_e option);

   mrule_e = MRULE_e pat_e exp_e;

   dec_e = VALdec_e valbind_e
         | DATATYPEdec_e datbind_e
         | ABSTYPEdec_e datbind_e dec_e
         | EXCEPTdec_e exbind_e
         | LOCALdec_e dec_e dec_e
         | OPENdec_e ((strid long) nonemptylist)
         | EMPTYdec_e
         | SEQdec_e dec_e dec_e;

   valbind_e = PLAINvalbind_e pat_e exp_e (valbind_e option)
             | RECvalbind_e valbind_e";;

(* ------------------------------------------------------------------------- *)
(* Example from Daryl: a Verilog grammar.                                    *)
(* ------------------------------------------------------------------------- *)

let daryl_INDUCTION,daryl_RECURSION = time define_type
  "Source_text
     = module string (string list) (Module_item list)
     | Source_textMeta string;
  Module_item
     = declaration Declaration
     | initial Statement
     | always Statement
     | assign Lvalue Expression
     | Module_itemMeta string;
  Declaration
     = reg_declaration (Range option) (string list)
     | net_declaration (Range option) (string list)
     | input_declaration (Range option) (string list)
     | output_declaration (Range option) (string list)
     | DeclarationMeta string;
  Range = range Expression Expression | RangeMeta string;
  Statement
     = clock_statement Clock Statement_or_null
     | blocking_assignment Lvalue Expression
     | non_blocking_assignment Lvalue Expression
     | conditional_statement
          Expression Statement_or_null (Statement_or_null option)
     | case_statement Expression (Case_item list)
     | while_loop Expression Statement
     | repeat_loop Expression Statement
     | for_loop
          Lvalue Expression Expression Lvalue Expression Statement
     | forever_loop Statement
     | disable string
     | seq_block (string option) (Statement list)
     | StatementMeta string;
  Statement_or_null
     = statement Statement | null_statement | Statement_or_nullMeta string;
  Clock
     = posedge string
     | negedge string
     | clock string
     | ClockMeta string;
  Case_item
     = case_item (Expression list) Statement_or_null
     | default_case_item Statement_or_null
     | Case_itemMeta string;
  Expression
     = plus Expression Expression
     | minus Expression Expression
     | lshift Expression Expression
     | rshift Expression Expression
     | lt Expression Expression
     | leq Expression Expression
     | gt Expression Expression
     | geq Expression Expression
     | logeq Expression Expression
     | logneq Expression Expression
     | caseeq Expression Expression
     | caseneq Expression Expression
     | bitand Expression Expression
     | bitxor Expression Expression
     | bitor Expression Expression
     | logand Expression Expression
     | logor Expression Expression
     | conditional Expression Expression Expression
     | positive Primary
     | negative Primary
     | lognot Primary
     | bitnot Primary
     | reducand Primary
     | reducxor Primary
     | reducor Primary
     | reducnand Primary
     | reducxnor Primary
     | reducnor Primary
     | primary Primary
     | ExpressionMeta string;
  Primary
     = primary_number Number
     | primary_IDENTIFIER string
     | primary_bit_select string Expression
     | primary_part_select string Expression Expression
     | primary_gen_bit_select Expression Expression
     | primary_gen_part_select Expression Expression Expression
     | primary_concatenation Concatenation
     | primary_multiple_concatenation Multiple_concatenation
     | brackets Expression
     | PrimaryMeta string;
  Lvalue
     = lvalue string
     | lvalue_bit_select string Expression
     | lvalue_part_select string Expression Expression
     | lvalue_concatenation Concatenation
     | LvalueMeta string;
  Number
     = decimal string
     | based string option string
     | NumberMeta string;
  Concatenation
     = concatenation (Expression list) | ConcatenationMeta string;
  Multiple_concatenation
     = multiple_concatenation Expression (Expression list)
     | Multiple_concatenationMeta string;
  meta
     = Meta_Source_text Source_text
     | Meta_Module_item Module_item
     | Meta_Declaration Declaration
     | Meta_Range Range
     | Meta_Statement Statement
     | Meta_Statement_or_null Statement_or_null
     | Meta_Clock Clock
     | Meta_Case_item Case_item
     | Meta_Expression Expression
     | Meta_Primary Primary
     | Meta_Lvalue Lvalue
     | Meta_Number Number
     | Meta_Concatenation Concatenation
     | Meta_Multiple_concatenation Multiple_concatenation";;
