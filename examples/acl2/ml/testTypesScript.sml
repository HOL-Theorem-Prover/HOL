open Theory Datatype Drule Thm Term Lib listTheory ratTheory;

val types = ref ([] : hol_type list);

fun DataType t def = 
let	val _ = (Parse.Type t ; ()) handle _ => Hol_datatype def
in
	(types := Parse.Type t :: (!types))
end;

fun AddType t = (types := Parse.Type t :: (!types));

val _ = new_theory "testTypes";

(*****************************************************************************)
(* Simple Types                                                              *)
(*****************************************************************************)

val _ = DataType `:'a List` `List = LNil | LCons of 'a => List`;
val _ = DataType `:'a Tree` `Tree = TLeaf of 'a | TBranch of Tree => Tree`;
val _ = DataType `:'a Tre` `Tre = TNil | TNode of 'a => Tre => Tre`;
val _ = DataType `:Label` `Label = L0 | L1 | L2 | L3 | L4`;
val _ = DataType `:'a + 'b` `'a + 'b = Left of 'a | Right of 'b`;
val _ = DataType `:unit` `unit = ()`;
val _ = DataType `:'a BList` `BList = BL of unit + 'a # BList`;
val _ = DataType `:'a CList` `CList = CLL of 'a # CList + unit`;
val _ = DataType `:'a BTree` `BTree = BT of 'a + BTree # BTree`;

(*****************************************************************************)
(* Types using recursive functions for their nested recursion                *)
(*****************************************************************************)

val _ = DataType `:'a RoseTree` `RoseTree = RTBranch of ('a # RoseTree) List`;
val _ = DataType `:'a BRoseTree` 
      		 `BRoseTree = BRTBranch of ('a # BRoseTree) BList`;
val _ = DataType `:RoseBush` `RoseBush = RBush of RoseBush RoseTree`;
val _ = DataType `:BRoseBush` `BRoseBush = BBush of BRoseBush BRoseTree`;
val _ = DataType `:Thicket` `Thicket = TStalk of Thicket Tre`;

(*****************************************************************************)
(* Connected single constructors                                             *)
(*****************************************************************************)

val _ = DataType `:'a CS4` 
		`	CS1 = CS1C of 'a CS2 => 'a CS4 ; 
			CS2 = CS2C of 'a CS3 => 'a CS4 ; 
			CS3 = CS3C of 'a CS4 ;
			CS4 = CS4C of 'a`;
val _ = AddType `:'a CS1`;
val _ = AddType `:'a CS2`;
val _ = AddType `:'a CS3`;

val _ = DataType `:'a DListL` 
      	`DListL = DLR of DListR ; DListR = DLRNil | DLRCons of 'a => DListL`;
(* val _ = DataType `:'a DLTree` 
       	   `DLTree = DLBranch of ('a # DLTree DListR)` --> Fails!! *)
val _ = DataType `:'a CSList` `CSList = CSNil | CSCons of 'a => CSList CS1`;

(*****************************************************************************)
(* Types with products as sub-types, since products are used heavily         *)
(*****************************************************************************)

val _ = DataType `:NumProdList`
		`NumProdList = NPLNull | NPLCons of num # num => NumProdList`;

val _ = DataType `:UncurriedNPL`
		 `UncurriedNPL = UNPLNull | 
		 	       	 UNPLCons of num # num # UncurriedNPL`;

(*****************************************************************************)
(* Previous types from earlier incarnations                                  *)
(*****************************************************************************)

val _ = DataType `:('a,'b) test1` `test1 = Pair of 'a # 'b`;
val _ = DataType `:('a,'b)test2`  `test2 = Curry of 'a => 'b`;
val _ = DataType `:('a,'b,'c) test2b`  `test2b = Curry3 of 'a => 'b => 'c`;
val _ = DataType `:('a,'b,'c) test2c`  `test2c = Curry2 of 'a => 'b # 'c`;
val _ = DataType `:('a,'b) test3`  `test3 = Sum1 of 'a | Sum2 of 'b`;
val _ = DataType `:test4`  `test4 = Recursive of test4 | End`;
val _ = DataType `:test5`  `test5 = RecursiveList of test5 list | EndList`;
val _ = DataType `:test6` 
      		 `test6 = DoubleList of test6 list => test6 list | EndD`;
val _ = DataType `:'a test7`  `test7 = Node of test7 # test7 | Leaf of 'a`;
val _ = DataType `:test8`  `test8 = Double of test8 test7 # test8 list | End8`;
val _ = DataType `:test9l`
      		 `test9l = R9 of test9r | EndL ; test9r = L9 of test9l | EndR`;
val _ = DataType `:testA`
      		 `testA = <| Reg1 : num; Reg2 : num; Waiting : bool |>`;
val _ = DataType `:testBa`  
      		 `testBa = Aa of num | Ba of testBb | Ca of testBc ; 
		  testBb = Bb of int | Ab of testBa | Cb of testBc ;
		  testBc = Cc of rat | Bc of testBb | Ac of testBa`;
val _ = DataType `:('a,'b) testCR`
      		 `testCR = CR of ('a # testCL) list ; 
		  testCL = CL of ('b # testCR) list`;
val _ = DataType `:testDX` 
      		 `testDX = dL of testDZ => testDY | DeL ; 
		  testDY = dR of testDX ; testDZ = dRec of testDX`;
val _ = DataType `:testEX`  
      		 `testEX = eL of testEZ => testEY | EeL ; 
		  testEY = eR of testEZ => testEX | EeR ; 
		  testEZ = twoRec of testEX => testEY`;
val _ = DataType `:('a,'b) testFX`  
      		 `testFX = fL of testFZ => testFY | FeL ; 
		  testFY = fR of testFZ => testFX | FeR ; 
		  testFZ = fRec of testFX => 'a => 'b => testFY`;
val _ = DataType `:('a,'b) state_out` 
      		 `state_out = <| state : 'a; out : 'b |>`;
val _ = DataType `:register`
`register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;
val _ = DataType `:psr`
  `psr = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und`;
val _ = DataType `:exceptions`
  `exceptions = reset | undefined | software | pabort |
                dabort | address |interrupt | fast`;
val _ = DataType `:('a,'b,'c) sumpair` `sumpair = Lsp of 'a | Rsp of 'b => 'c`;
val _ = DataType `:'a my_tree` 
      		 `my_tree = Branch of ('a,my_tree,my_tree) sumpair`;

(*****************************************************************************)
(* Red-Black trees                                                           *)
(*****************************************************************************)

val _ = DataType `colour = R | B`;
val _ = DataType `tree = LEAF | NODE of colour => num => tree => tree`; 

(*****************************************************************************)
(* Some examples from src/datatype/jrh.test                                  *)
(*****************************************************************************)

val _ = DataType  `:One` `One = Single_contructor`;

val _ = DataType 
        `:('A,'B) Term` 
	`Term = Var of 'A => 'B 
               | App of bool => Termlist;
      Termlist = Emp 
               | Consp of Term => Termlist`;

val _ = DataType 
	`:('A,'B) Btree`
    	`Btree = Lf of 'A 
           | Nd of 'B => Btree => Btree`;;

val _ = DataType 
    `:Express`
    `Command = Assign of num => Express
             | If of Express => Command
             | Ite of Express => Command => Command
             | While of Express => Command
             | Do of Command => Express;

     Express = Constant of num
             | Variable of num
             | Summ of Express => Express
             | Product of Express => Express`;

val _ = AddType `:Command`;

val _ = DataType 
    `:pat`
    `atexp = Varb of num 
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
           | Varpat of num`;

val _ = AddType `:atexp`;

val _ = DataType
     `:tri`
     `tri = ONE | TWO | THREE`;

val _ = DataType
      `:Steve0`
      `Steve0 = X1  | X2  | X3  | X4  | X5  | X6  | X7  | X8  | X9  | X10 |
                X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 |
                X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | 
                X31 | X32 | X33 | X34`;;

val _ = DataType
    `:('A,'B,'C) TY1`
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

(*****************************************************************************)
(* Example from Myra: part of the syntax of SML.                             *)
(*****************************************************************************)

val _ = DataType
  `:String`
  `String = EMPTY_STRING 
          | CONS_STRING of num => String`;

val _ = DataType
  `:strid`
  `strid = STRID of String;
   var = VAR of String;
   con = CON of String;
   scon = SCINT of num  (* was int *)
        | SCSTR of String;
   excon = EXCON of String;
   label = LABEL of String`;;

val _ = AddType `:var`;
val _ = AddType `:con`;
val _ = AddType `:scon`;
val _ = AddType `:excon`;

val _ = DataType
  `:'A nonemptylist`
  `nonemptylist = Head_and_tail of 'A => 'A list`;;

val _ = DataType
  `:'A long`
  `long = BASE of 'A | QUALIFIED of strid => long`;;

val _ = DataType
  `:'a option`
  `option = SOME of 'a | NONE`;

val _ = DataType
  `:atpat_e`
  `atpat_e = WILDCARDatpat_e
           | SCONatpat_e   of scon
           | VARatpat_e    of var
           | CONatpat_e    of con long
           | EXCONatpat_e  of excon long
           | RECORDatpat_e of patrow_e option
           | PARatpat_e    of pat_e;

   patrow_e = DOTDOTDOT_e
            | PATROW_e of num => pat_e => patrow_e option;

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

   exprow_e = EXPROW_e of num => exp_e => exprow_e option;

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

val _ = save_thm("LIST",LIST_CONJ (map (REFL o curry mk_var "a")
      				  (rev (!types))));

val _ = export_theory();
