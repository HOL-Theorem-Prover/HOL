(*****************************************************************************)
(* File: testEncode.sml                                                      *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Runs some simple tests of encodeLib                                       *)
(*****************************************************************************)

quietdec := true;

val _ = loadPath := "../ml/" :: !loadPath;

load "encodeLib";
open encodeLib arithmeticTheory listTheory;

quietdec := false;

(*****************************************************************************)
(* Some simple tests of different data types                                 *)
(*****************************************************************************)

val _ = Hol_datatype `test1 = Pair of 'a # 'b`;
val _ = Hol_datatype `test2 = Curry of 'a => 'b`;
val _ = Hol_datatype `test2b = Curry3 of 'a => 'b => 'c`;
val _ = Hol_datatype `test2c = Curry2 of 'a => 'b # 'c`;
val _ = Hol_datatype `test3 = Sum1 of 'a | Sum2 of 'b`;
val _ = Hol_datatype `test4 = Recursive of test4 | End`;
val _ = Hol_datatype `test5 = RecursiveList of test5 list | EndList`;
val _ = Hol_datatype `test6 = DoubleList of test6 list => test6 list | EndD`;
val _ = Hol_datatype `test7 = Node of test7 # test7 | Leaf of 'a`;
val _ = Hol_datatype `test8 = Double of test8 test7 # test8 list | End8`;
val _ = Hol_datatype `test9l = R9 of test9r | EndL ; test9r = L9 of test9l | EndR`;
val _ = Hol_datatype `testA = <| Reg1 : num; Reg2 : num; Waiting : bool |>`;
val _ = Hol_datatype `	testBa = Aa of num | Ba of testBb | Ca of testBc ; 
			testBb = Bb of int | Ab of testBa | Cb of testBc ;
			testBc = Cc of rat | Bc of testBb | Ac of testBa`;
val _ = Hol_datatype `labels = l1 | l2 | l3 | l4 | l5`;
val _ = Hol_datatype `noalpha = CurryNA of num => num => num # num`;
val _ = Hol_datatype `threecons = ConsNone | CurryTC of 'a => 'b => 'c | CurryNTC of num => num => num # num`;
val _ = Hol_datatype `rose_tree = Branch of ('a # rose_tree) list`; 
val _ = Hol_datatype `mlistL = Left of 'a => mlistR | endL ; mlistR = Right of 'b => mlistL | endR`;


(*****************************************************************************)
(* Black - Red trees                                                         *)
(*****************************************************************************)

val _ = Hol_datatype `colour = R | B`;
val _ = Hol_datatype `tree = LEAF | NODE of colour => num => tree => tree`; 

(*****************************************************************************)
(* Some examples from src/datatype/jrh.test                                  *)
(*****************************************************************************)

val _ = Hol_datatype  `One = Single_contructor`;

val _ = Hol_datatype 
         `Term = Var of 'A => 'B 
               | App of bool => Termlist;
      Termlist = Emp 
               | Consp of Term => Termlist`;

val _ = Hol_datatype 
      `List = Nil 
            | Cons of 'A => List`;;

val _ = Hol_datatype 
    `Btree = Lf of 'A 
           | Nd of 'B => Btree => Btree`;;

val _ = Hol_datatype 
    `Command = Assign of num => Express
             | If of Express => Command
             | Ite of Express => Command => Command
             | While of Express => Command
             | Do of Command => Express;

     Express = Constant of num
             | Variable of num
             | Summ of Express => Express
             | Product of Express => Express`;

val _ = Hol_datatype 
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

val _ = Hol_datatype
     `tri = ONE | TWO | THREE`;

Hol_datatype
      `Steve0 = X1  | X2  | X3  | X4  | X5  | X6  | X7  | X8  | X9  | X10 |
                X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 |
                X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | 
                X31 | X32 | X33 | X34`;;

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
         | NeverMalFromSelf__ of 'A => 'B => TY2`;;

(*****************************************************************************)
(* Example from Myra: part of the syntax of SML.                             *)
(*****************************************************************************)

Hol_datatype
  `String = EMPTY_STRING 
          | CONS_STRING of num => String`;

Hol_datatype
  `strid = STRID of String;
   var = VAR of String;
   con = CON of String;
   scon = SCINT of num  (* was int *)
        | SCSTR of String;
   excon = EXCON of String;
   label = LABEL of String`;;

Hol_datatype
  `nonemptylist = Head_and_tail of 'A => 'A list`;;

Hol_datatype
  `long = BASE of 'A | QUALIFIED of strid => long`;;


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

set_trace "EncodeLib.TypeEncoding" 1;

val types = [	``:('a,'b) test1``,``:('a,'b) test2``,``:('a,'b,'c) test2b``,``:('a,'b,'c) test2c``,``:('a,'b) test3``,``:labels``,``:noalpha``,``:('a,'b,'c) threecons``,
		``:test4``,``:test5``,``:test6``,``:test8``,``:'a test7``,``:test9l``,``:test9r``,``:'a rose_tree``,``:testBa``,``:('a,'b) mlistL``,``:tree``,
		``:One``,``:('a,'b) Term``,``:'a List``,``:('a,'b) Btree``,``:Command``,``:tri``,``:exp``,``:Steve0``,``:('a,'b,'c) TY1``,``:atpat_e``];

fun test_types types = 
let	fun timeit t = 
	let 	val _ = print "Encoding Type: "
		val _ = print_type t
		val _ = print "\n"
		val start = Time.now()
		val res = encode_type t
	in 
		(print ("Time taken: " ^ (Time.toString (Time.- (Time.now(),start)) handle e => "0.000") ^ "s\n\n") ; res)
	end;	
	val (passed,failed) = partition (can timeit) types
	fun concat f [] = ""
	  | concat f [x] = f x
	  | concat f (x::xs) = (f x) ^ "," ^ (concat f xs)
	val _ = print ("Passed: [" ^ (concat type_to_string passed) ^ "]\n")
	val _ = print ("Failed: [" ^ (concat type_to_string failed) ^ "]\n")
in
	(print "\nTheorems:\n" ; 
	app (fn x => (	print_thm (get_encode_decode_thm x) ; print "\n" ; 
			print_thm (get_decode_encode_thm x) ; print "\n" ; 
			print_thm (get_detect_encode_thm x) ; print "\n\n")) passed)
end;

time test_types types;


(*****************************************************************************)
(* Example, originating from Matt Kaufmann, showing the flow                 *)
(* from HOL to HOL/SEXP and then to ACL2.                                    *)
(*****************************************************************************)

(*****************************************************************************)
(* The example is a machine that processes read and write instructions       *)
(* N.B. Maybe write should be curried -- will change if necessary?           *)
(*****************************************************************************)

val _ = Hol_datatype `instruction = Read of num | Write of num # num`;

(*****************************************************************************)
(* read_step addr [(a1,v1);...;(an,vn)] returns vi where addr=ai,            *)
(* scanning from left (i.e. from i=1)                                        *)
(*****************************************************************************)
val read_step_def =
 Define
  `(read_step (addr:num) [] = 0n)
   /\
   (read_step addr ((addr',v)::alist) = 
     if addr = addr' then v else read_step addr alist)`;

(*****************************************************************************)
(* write_step addr v [(a1,v1);...;(ai,vi);...;(an,vn)] =                     *)
(*   [(a1,v1);...;(ai,v);...;(an,vn)]                                        *)
(*                                                                           *)
(* where addr=ai, scanning from left (i.e. from i=1)                         *)
(*****************************************************************************)
val write_step_def =
 Define
  `(write_step (addr:num) (v:num) [] = [(addr,v)])
   /\
   (write_step addr v ((addr',v')::alist) =
     if addr = addr' 
      then (addr,v)::alist 
      else (addr',v')::(write_step addr v alist))`;

(*****************************************************************************)
(* run [ins1;...;insn] [(a1,v1);...;(ai,vi);...;(an,vn)] [v1;...;vp] =       *)
(*  [v1;...;vp;vq...;vr]                                                     *)
(*                                                                           *)
(* where [vq;...;vr] is the reversed list of values Read (by a Read          *)
(* instruction) when executing [ins1;...;insn] (in that order)               *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*     |- run                                                                *)
(*          [Write (92,1); Read 38; Write (79,3); Read 21; Write (66,5);     *)
(*           Read 4; Write (53,7); Read 87; Write (40,9); Read 70;           *)
(*           Write (27,11); Read 53; Write (14,13); Read 36; Write (1,15);   *)
(*           Read 19; Write (88,17); Read 2; Write (75,19); Read 85;         *)
(*           Write (62,21); Read 68; Write (49,23); Read 51; Write (36,25);  *)
(*           Read 34; Write (23,27); Read 17; Write (10,29); Read 0] [] []   *)
(*        [0; 0; 0; 0; 0; 0; 0; 0; 0; 7; 0; 0; 0; 0; 0] : thm                *)
(*****************************************************************************)
val run_def =
 Define
  `(run [] alist reversed_values_read = reversed_values_read)
   /\
   (run (Write (addr,v)::instrs) alist reversed_values_read =
     run instrs (write_step addr v alist) reversed_values_read)
   /\
   (run (Read (addr)::instrs) alist reversed_values_read =
     run instrs alist (read_step addr alist::reversed_values_read))`;

(*****************************************************************************)
(* The function make_instrs generates a program to run. For example:         *)
(*                                                                           *)
(*     |- make_instrs 0 10 F 10 [] =                                         *)
(*        [Write (62,1); Read 68; Write (49,3); Read 51;                     *)
(*         Write (36,5); Read 34; Write (23,7); Read 17;                     *)
(*         Write (10,9); Read 0]                                             *)
(*                                                                           *)
(* This was generated by EVAL ``make_instrs 0 10 F 10 []``.                  *)
(*                                                                           *)
(* Note that as an accumulator is used, the list returned is the list of     *)
(* instructions in the reverse order to which they were created.             *)
(*****************************************************************************)
val write_increment_def = 
 Define `write_increment = 13n`;

val read_increment_def = 
 Define `read_increment = 17n`;

val max_addr_def = 
 Define `max_addr = 100n`;

val fix_address_def = Define  `fix_address a b = if a >= b /\ ~(b = 0) then fix_address (a - b) b else a:num`;

val make_instrs_def =
 Define
  `(make_instrs read_start write_start flag 0 acc = acc)
   /\
   (make_instrs read_start write_start flag (SUC n) acc = 
     if flag
      then make_instrs read_start
                       (fix_address (write_start + write_increment) max_addr)
                       (~flag)
                       n
                       (Write(write_start,SUC n) :: acc)
      else make_instrs (fix_address (read_start + read_increment) max_addr)
                       write_start
                       (~flag)
                       n
                       (Read read_start :: acc))`;

(*****************************************************************************)
(* Version using a conditional rather than pattern matching on ``0`` and     *)
(* ``SUC n`` (needed to amke computeLib.EVAL happy)                          *)
(*****************************************************************************)
val make_instrs_def =
 prove
  (``make_instrs read_start write_start flag n acc =
      if n=0
       then acc 
       else if flag
             then make_instrs read_start
                              (fix_address (write_start + write_increment) max_addr)
                              (~flag)
                              (n - 1)
                              (Write(write_start,n) :: acc)
             else make_instrs (fix_address (read_start + read_increment) max_addr)
                              write_start
                              (~flag)
                              (n - 1)
                              (Read read_start :: acc)``,
   Cases_on `n`
    THEN RW_TAC arith_ss [make_instrs_def]);

val _ = computeLib.add_funs[make_instrs_def];


(**** Examples ***************************************************************

val basic_result = time EVAL ``run (make_instrs 0 10 F 100 []) [] []``;
runtime: 2.405s,    gctime: 0.224s,     systime: 0.000s.
> val basic_result =
    |- run (make_instrs 0 10 F 100 []) [] [] =
       [39; 21; 3; 0; 0; 0; 0; 0; 0; 77; 59; 41; 23; 5; 0; 0; 0; 0; 0; 0; 0;
        0; 43; 25; 7; 0; 0; 0; 0; 0; 0; 0; 0; 0; 27; 9; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0] : thm

Example that is too big (segmentation fault on trout).

val medium_instr_list  = time EVAL ``make_instrs 0 10 F 1000 []``;

val medium_instr_list_def =
 Define
  `medium_instr_list = ^(rhs(concl(time EVAL ``make_instrs 0 10 F 1000 []``)))`;

val medium_result = time EVAL ``run medium_instr_list [] []``;

val medium_result = time EVAL ``run (make_instrs 0 10 F 1000 []) [] []``;

val big_instr_list  = time EVAL ``make_instrs 0 10 F 1000000 []``;

val big_instr_list_def =
 Define
  `big_instr_list = ^(rhs(concl(time EVAL ``make_instrs 0 10 F 1000000 []``)))`;

val basic_result = time EVAL ``run big_instr_list [] []``;

******************************************************************************)

set_trace "EncodeLib.FunctionEncoding" 1;

(*****************************************************************************)
(* Some simple arithmetic functions:                                         *)
(*****************************************************************************)

val (divsub_def,divsub_ind) = 
	(RIGHT_CONV_RULE (ONCE_DEPTH_CONV (HO_REWR_CONV 
		(prove(``	(let c = a * b:num in let d = a + b in e c d) = 
				(let c = a * b and d = a + b in e c d)``,
			REWRITE_TAC [LET_THM] THEN BETA_TAC THEN REFL_TAC)))) ## I)
	(Defn.tprove 
		(Hol_defn "divsub" `divsub a b = 
			if 0 < a \/ 0 < b then let c = a * b in let d = a + b in 1 + divsub (c DIV d) (c - d) else 0n`,
	WF_REL_TAC `measure (\ (a,b). if 0 < a then a else b)` THEN
	RW_TAC arith_ss [DIV_LT_X,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,X_LT_DIV]));

val acl2_exp_def = 		convert_definition EXP;
val acl2_fact_def =             convert_definition FACT;
val acl2_findq_def = 		convert_definition findq_thm;
val acl2_divmod_def = 		convert_definition DIVMOD_THM;
val acl2_divsub_def = 		convert_definition divsub_def;


(*****************************************************************************)
(* Encoding of Matt's example given earlier:                                 *)
(*****************************************************************************)

val acl2_read_step_def = 	convert_definition read_step_def;
val acl2_write_step_def = 	convert_definition write_step_def;
val acl2_run_def = 		convert_definition run_def;
val acl2_write_increment_def = 	convert_definition write_increment_def;
val acl2_read_increment_def = 	convert_definition read_increment_def;
val acl2_max_addr_def = 	convert_definition max_addr_def;
val acl2_fix_address_def = 	convert_definition fix_address_def;
val acl2_make_instrs_def = 	convert_definition make_instrs_def;

(*****************************************************************************)
(* Encoding of rose_tree and red-black tree functions...                     *)
(*****************************************************************************)


val count_def = 		Define `	(count (Branch []) = 0n) /\ 
						(count (Branch ((x,hd)::tl)) = 1 + count (hd:num rose_tree) + count (Branch tl))`;
val acl2_count_def = 		convert_definition count_def;

val member_def = 		Define `	(member key LEAF = F) /\ 
						(member key (NODE col k left right) = if key < k then member key left else if k < key then member key right else T)`;
val acl2_member_def = 		convert_definition member_def;

(*****************************************************************************)
(* Restricting the input domain of a function:                               *)
(*****************************************************************************)

val modpow_def = 		Define `(modpow a 0 n = 1) /\ (modpow a (SUC b) n = a * (modpow a b n) MOD n)`;
val acl2_modpow_def = 		convert_definition_restricted ``\a b c. ~(c = 0n)`` modpow_def;

(*****************************************************************************)
(* Addition of a termination helper theorem:                                 *)
(*****************************************************************************)

val (log2_def,log2_ind) = 	Defn.tprove(Hol_defn "log2" `(log2 0 = 0) /\ (log2 a = SUC (log2 (a DIV 2)))`,WF_REL_TAC `measure (\a.a)` THEN RW_TAC arith_ss [DIV_LT_X]);
val acl2_log2_def = 		convert_definition_full NONE (SOME (prove(``!a. 0 < a ==> a DIV 2 < a``,RW_TAC arith_ss [DIV_LT_X]))) log2_def;

(*****************************************************************************)
(* Theorem encoding...                                                       *)
(*****************************************************************************)

val acl2_division = convert_theorem DIVISION;
val acl2_divmod_calc = convert_theorem DIVMOD_CALC;

(*****************************************************************************)
(* HO function encoding...                                                   *)                   
(*****************************************************************************)

val (acl2_filter_correct,acl2_filter_def) = convert_definition (INST_TYPE [``:'a`` |-> ``:num``] FILTER);

val filter_zero_def = Define `filter_zero x = FILTER (\x. ~(x = 0n)) x`;

val (acl2_filter_zero_correct,acl2_filter_zero_def) = convert_definition filter_zero_def;

val (filter0_rewrite,filter0_def) = flatten_HO_definition "filter0" acl2_filter_def ``(acl2_FILTER (\x. ite (natp x) (not (equal x (nat 0))) (not (equal (nat 0) (nat 0)))) X)``;

val acl2_filter_zero_def' = REWRITE_RULE [filter0_rewrite] acl2_filter_zero_def;
