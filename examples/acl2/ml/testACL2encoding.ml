load "acl2encodeLib";
load "testTypesTheory";
load "testFunctionsTheory";
load "intLib";

open Parse
open polytypicLib encodeLib functionEncodeLib
open acl2encodeLib testTypesTheory testFunctionsTheory; 
open listTheory rich_listTheory optionTheory combinTheory;

(*****************************************************************************)
(* Testing ...                                                               *)
(*****************************************************************************)

fun mappartition f [] = ([],[])
  | mappartition f (x::xs) = 
    (cons (f x) ## I) (mappartition f xs)
    handle e => (print (exn_to_string e) ; (I ## cons x) (mappartition f xs));

val type_tests = (ref 0,ref ([]:(string * hol_type list) list));

fun Test s f t = 
let val (count,results) = type_tests
    val (passed,failed) = mappartition f t
in
    (count := (!count) + 1 ;
     results := ("Test " ^ s ^ " : " ^ 
     	     	int_to_string (!count),failed) :: (!results))
end

val types = ref (rev (map (type_of o lhs) (strip_conj (concl LIST))));

(* Initialisation *)

val num = ``:num``;
val int = ``:int``;
val rat = ``:rat``;
val com = ``:complex_rational``;
val bool = ``:bool``;
val char = ``:char``;
val string = ``:string``;
val pair = ``:'a # 'b``;
val list = ``:'a list``;
val sexp = ``:sexp``;

local 
in
fun generate_functions target = 
let val _ = Test "" (map (add_translation target o fst) o 
    	    	    	 split_nested_recursive_set) (rev (!types));
    val _ = Test "map" (generate_source_function "map" o base_type)
    	    	       (rev (!types));
    val _ = Test "all" (generate_source_function "all" o base_type)
    	    	       (rev (!types));
    val _ = Test "encode" (generate_coding_function target "encode" o base_type)
    	    	 	  (rev (!types));
    val _ = Test "detect" (generate_coding_function target "detect" o base_type)
    	    	 	  (rev (!types));
    val _ = Test "decode" (generate_coding_function target "decode" o base_type)
    	    	 	  (rev (!types));
    val _ = Test "fix" (generate_coding_function target "fix" o base_type)
    	    	       (rev (!types));
in
	()
end
end

fun generate_theorems target = 
let val every_type = 
    filter (fn x => not (can (match_type x) pair) andalso 
    	       	    not (can (match_type x) list) andalso 
		    not (x = num) andalso not (x = bool) andalso 
		    not (x = rat) andalso not (x = int))
    (mk_set (flatten (map (fn t => 
    	    t::map snd (reachable_graph uncurried_subtypes t)) (rev (!types)))))

    fun cremove_all string = 
    	mapfilter (fn t => remove_coding_theorem_precise sexp t string) 
		  every_type
    fun sremove_all string = 
	mapfilter (fn t => remove_source_theorem_precise t string) 
		  every_type

    val remove_all = cremove_all "encode_detect_all";
    val remove_all = sremove_all "map_compose";
    val remove_all = cremove_all "encode_decode_map";
    val remove_all = cremove_all "encode_map_encode";
    val remove_all = cremove_all "general_detect";
    val remove_all = cremove_all "general_detect";
    val remove_all = cremove_all "decode_encode_fix";
    val remove_all = cremove_all "fix_id";
		
    val _ = time (Test "encode_detect_all" 
               	       (generate_coding_theorem sexp "encode_detect_all"))
	         (rev (!types));
    val _ = time (Test "all_id" 
    	    	       (generate_source_theorem "all_id")) 
                 (rev (!types));
    val _ = time (Test "map_id" 
              	   (generate_source_theorem "map_id"))
                 (rev (!types));
    val _ = time (Test "map_compose" 
              	       (generate_source_theorem "map_compose"))
                 (rev (!types));
    val _ = time (Test "encode_decode_map"
              	       (generate_coding_theorem sexp "encode_decode_map"))
                 (rev (!types));
    val _ = time (Test "encode_map_encode" 
              	       (generate_coding_theorem sexp "encode_map_encode"))
         	 (rev (!types));
    val _ = time (Test "general_detect"
    	    	       (generate_coding_theorem sexp "general_detect"))
		 (rev (!types));
    val _ = time (Test "decode_encode_fix" 
    	    	       (generate_coding_theorem sexp "decode_encode_fix"))
		 (rev (!types));
    val _ = time (Test "fix_id" 
    	    	       (generate_coding_theorem sexp "fix_id"))
		 (rev (!types));
in
()
end


(*****************************************************************************)
(* Function testing:                                                         *)
(*    add_test adds a test as a string, function, data pair                  *)
(*                                                                           *)
(*****************************************************************************)

val tests = ref ([] : (string * (thm -> unit) * thm) list);
fun add_test (name,func,arg) = 
    tests := !tests @ [(name,(fn y => (func y ; ())),arg)];
fun run_test (s,func,thm) = 
    (print ("Test: " ^ s ^ "\n") ; 
    (func thm) before (print "passed!\n"))
    handle e => Raise e;
val last_test = ref (NONE : (string * (thm -> unit) * thm) option);
fun run_function_tests () = 
    case (total (first (not o can run_test)) (!tests))
    of NONE => print "Success!!!!!!\n"
    |  SOME last => (last_test := SOME last ; print "Failed.\n");
fun run_last_function_test () = run_test (Option.valOf (!last_test))

(*****************************************************************************)
(* Initialisation:                                                           *)
(*     Add theorems for natural numbers and the conditional                  *)
(*     Add theorems for booleans and polymorphic equality                    *)
(*     Add simple theorems for lists                                         *)
(*     Add simple pair theorems                                              *)
(*                                                                           *)
(*****************************************************************************)

fun initialise_function_tests () =
let val _ = add_standard_coding_rewrites ``:sexp`` ``:'a option``
      	handle e => Raise e;
    val _ = add_standard_coding_rewrites ``:sexp`` ``:'a Tree``
      	handle e => Raise e;
in
   ()
end;

(*****************************************************************************)
(* Flattening: 'a list, 'a + num, (num + 'a) list, ('a + num) list           *)
(*****************************************************************************)

val _ = add_test ("flatten list",
            flatten_recognizers (mk_fullname ``:sexp``) o
	    type_of o lhs o concl,
            (REFL o curry mk_var "a") ``:'a list``);

val _ = add_test ("flatten sum",
            flatten_recognizers (mk_fullname ``:sexp``) o
	    type_of o lhs o concl,
            (REFL o curry mk_var "a") ``:'a + num``);

val _ = add_test ("flatten sum list A",
            flatten_recognizers (mk_fullname ``:sexp``) o
	    type_of o lhs o concl,
            (REFL o curry mk_var "a") ``:(num + 'a) list``);

val _ = add_test ("flatten sum list B",
            flatten_recognizers (mk_fullname ``:sexp``) o
	    type_of o lhs o concl,
            (REFL o curry mk_var "a") ``:('a + num) list``);

(*****************************************************************************)
(* Simple functions:                                                         *)
(*    EXP                  : Clause form & natural number case               *)
(*    LENGTH (num)         : Clause form & list case                         *) 
(*    APPEND (num)         : Clause form & list case                         *)
(*    REVERSE (num)        : Clause form & list case                         *)
(*    FLAT (num)           : Clause form & list case (hard)                  *)
(*    LAST (num)           : Missing cases                                   *)
(*    SEG (num)            : Missing cases (hard)                            *)
(*    SPLIT (num)          : Mutually Recursive Definition                   *)
(*    EVEN_EXTEND          : Extended case on SUC                            *)
(*    ODD_EVEN             : Mutually Recursive Definition                   *)
(*    ECASE (num)          : Extended case (num) & Missing case (hard)       *)
(*    LCASE (num)          : Extended case (list) & Missing case (hard)      *)
(*                                                                           *)
(* Datatype functions:                                                       *)
(*    OPTION_JOIN (num)    : Simple option case                              *)
(*    OLIST (num)          : Option cases in a list                          *)
(*    FLATTEN_TREE (num)   : Flatten a binary tree using append              *)
(*    FT_FAST (num)        : Flatten a binary tree using an accumulator      *)
(*                                                                           *)
(* Functions from the thesis:                                                *)
(*    merge                : Combintation                                    *)
(*    merge_sort           : LET construct                                   *)
(*                                                                           *)
(*****************************************************************************)

open testFunctionsTheory;

val _ = add_test ("EXP",
            translate_simple_function [(``($**):num -> num -> num``,"exp")],
	    arithmeticTheory.EXP);
val _ = add_test ("LENGTH (num)",
            translate_simple_function [(``LENGTH``,"length")],
	    INST_TYPE [alpha |-> num] LENGTH);
val _ = add_test ("APPEND (num)",
            translate_simple_function [(``$++``,"append")],
	    INST_TYPE [alpha |-> num] APPEND);
val _ = add_test ("REVERSE (num)",
            translate_simple_function [(``REVERSE``,"reverse")],
	    INST_TYPE [alpha |-> num] REVERSE_DEF);
val _ = add_test ("FLAT (num)",
            translate_simple_function [(``testFunctions$FLAT``,"flat")],
	    INST_TYPE [alpha |-> num] FLAT_def);
val _ = add_test ("LAST (num)",
            translate_simple_function [(``LAST``,"last")],
	    INST_TYPE [alpha |-> num] LAST_DEF);

val limit_correct = 
    prove(``a + b <= LENGTH c ==> ~((?n. a = SUC n) /\ (c = []))``,
    	  Cases_on `c` THEN RW_TAC arith_ss [listTheory.LENGTH]);
val limit_recursive1 = 
    prove(``(?d. a = SUC d) /\ (b = 0) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    	       PRE a + 0 <= LENGTH (TL c)``,
          Cases_on `c` THEN RW_TAC arith_ss [LENGTH,TL,NULL]);
val limit_recursive2 = 
    prove(``(?d. a = SUC d) /\ (?d. b = SUC d) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    		SUC (PRE a) + PRE b <= LENGTH (TL c)``,
	  Cases_on `c` THEN RW_TAC arith_ss [LENGTH,TL,NULL]);

val _ = add_test ("SEG (num)",
            translate_limit_function
                 [(``SEG``,"seg")]
	         [(``SEG``,[``\a b c. a + b <= LENGTH c``])]
	         [limit_correct,limit_recursive1,limit_recursive2],		
	    INST_TYPE [alpha |-> num] SEG);

val _ = add_test ("SPLIT (num)",
            translate_simple_function
	    [(``split1``,"splitn1"),(``split2``,"splitn2")],
	    INST_TYPE [alpha |-> num] SPLIT_def);
val _ = add_test ("EVEN_EXTEND",
            translate_simple_function [(``EVEN``,"even_extend")],
	    EVEN_EXTEND_def);
val _ = add_test ("ODD_EVEN",
            translate_simple_function [(``ODD``,"odd"),(``EVEN``,"even")],
	    ODD_EVEN_def);
val _ = add_test ("ECASE (num)",
            translate_simple_function [(``ECASE``,"ecase")],
	    INST_TYPE [alpha |-> num] ECASE_def);
val _ = add_test ("LCASE (num)",
      	    translate_simple_function [(``LCASE``,"lcase")],
	    INST_TYPE [alpha |-> num] LCASE_def);

val _ = add_test ("OPTION_JOIN (num)",
            translate_simple_function [(``OPTION_JOIN``,"option_join")],
	    INST_TYPE [alpha |-> num] OPTION_JOIN_DEF);
val _ = add_test ("OLIST (num)",
            translate_simple_function [(``OLIST``,"olist")],
	    INST_TYPE [alpha |-> num] OLIST_def);

val _ = add_test ("merge",
            translate_simple_function [(``merge``,"mergen")],
            merge_def);
val _ = add_test ("merge_sort",
            translate_simple_function [(``merge_sort``,"merge_sortn")],
            merge_sort_def);

val _ = add_test ("FLATTEN_TREE (num)",
            translate_simple_function [(``FLATTEN_TREE``,"flatten_tree")],
	    INST_TYPE [alpha |-> num] FLATTEN_TREE_def);

val _ = add_test ("FT_FAST (num)",
            translate_simple_function [(``FT_FAST``,"ft_fast")],
	    INST_TYPE [alpha |-> num] FT_FAST_def);

val LENGTH_MAP = prove(``!x f. LENGTH (MAP f x) = LENGTH x``,
    Induct THEN 
    FULL_SIMP_TAC std_ss [LENGTH,MAP,o_THM]);

val _ = add_test ("LENGTH (polymorphic)",
            translate_simple_polymorphic_function
                      [(``LENGTH``,"length_poly")]
                      [(``LENGTH``,LENGTH_MAP)],
	    LENGTH);

val APPEND_MAP = prove(``!x y f. MAP f x ++ MAP f y = MAP f (x ++ y)``,
    Induct THEN RW_TAC std_ss [MAP,APPEND]);

val _ = add_test ("APPEND (polymorphic)",
            translate_simple_polymorphic_function 
                      [(``$++``,"append")]
                      [(``$++``,APPEND_MAP)],
	    APPEND);

val REVERSE_APP_MAP = prove(
    ``!x y f. REVERSE (MAP f x) ++ MAP f y = MAP f (REVERSE x ++ y)``,
    Induct THEN RW_TAC std_ss [MAP,REVERSE_DEF,APPEND,GSYM APPEND_ASSOC] THEN 
    RW_TAC std_ss [GSYM MAP]);

val REVERSE_MAP = REWRITE_RULE [APPEND_NIL,MAP] 
    (Q.SPECL [`x`,`[]`] REVERSE_APP_MAP);

val _ = add_test ("REVERSE (polymorphic)",
            translate_simple_polymorphic_function
                      [(``REVERSE``,"reverse")]
		      [(``REVERSE``,REVERSE_MAP)],
	    REVERSE_DEF);

val FLAT_MAP = prove(``!x. FLAT (MAP (MAP f) x) = MAP f (FLAT x)``,
    Induct THEN TRY Induct THEN RW_TAC std_ss [FLAT_def,MAP] THEN
    ASM_REWRITE_TAC [GSYM MAP]);

val _ = add_test ("FLAT (polymorphic)",
            translate_simple_polymorphic_function
                      [(``testFunctions$FLAT``,"flat")]
                      [(``testFunctions$FLAT``,FLAT_MAP)],
	    FLAT_def);

val LAST_MAP = prove(
    ``!x. (?a b. x = a :: b) ==> (LAST (MAP f x) = f (LAST x))``,
    Induct THEN TRY (Cases_on `x`) THEN RW_TAC std_ss [MAP,LAST_DEF] THEN 
    FULL_SIMP_TAC std_ss [MAP] THEN METIS_TAC []);

val MAP_CONS = prove(
    ``!x. (?a b. x = a :: b) ==> (?a b. MAP f x = a :: b)``,
    Induct THEN RW_TAC std_ss [MAP]);

val last_limit = prove(``!a. (?x y. a = x :: y) ==> ~(a = [])``,
    Cases THEN RW_TAC std_ss []);

val _ = add_test ("LAST (polymorphic)",
            translate_limit_polymorphic_function
	              [(``LAST``,"last")]
		      [(``LAST``,LAST_MAP)]
                      [(``LAST``,[``\a. (?x y. a = x :: y)``])]
                      [MAP_CONS,SPEC_ALL last_limit],
	    LAST_DEF);

val limit_correct = 
    prove(``a + b <= LENGTH c ==> ~((?n. a = SUC n) /\ (c = []))``,
    	  Cases_on `c` THEN RW_TAC arith_ss [listTheory.LENGTH]);
val limit_recursive1 = 
    prove(``(?d. a = SUC d) /\ (b = 0) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    	       PRE a + 0 <= LENGTH (TL c)``,
          Cases_on `c` THEN RW_TAC arith_ss [LENGTH,TL,NULL]);
val limit_recursive2 = 
    prove(``(?d. a = SUC d) /\ (?d. b = SUC d) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    		SUC (PRE a) + PRE b <= LENGTH (TL c)``,
	  Cases_on `c` THEN RW_TAC arith_ss [LENGTH,TL,NULL]);

val SEG_MAP = prove(
    ``!c a b. a + b <= LENGTH c ==> (SEG a b (MAP f c) = MAP f (SEG a b c))``,
    Induct THEN1 RW_TAC std_ss [LENGTH,MAP,SEG] THEN
    Induct_on `a` THEN Induct_on `b` THEN RW_TAC std_ss [SEG,LENGTH,MAP] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN DECIDE_TAC);

val LIMIT_MAP = prove(
    ``!c a b f. a + b <= LENGTH c ==> a + b <= LENGTH (MAP f c)``,
     Induct THEN RW_TAC std_ss [LENGTH,MAP,LENGTH_MAP]);

val _ = add_test ("SEG (polymorphic)",
            translate_limit_polymorphic_function
                 [(``SEG``,"seg")]
                 [(``SEG``,SEG_MAP)]
	         [(``SEG``,[``\a b c. a + b <= LENGTH c``])]
	         [LIMIT_MAP,limit_correct,limit_recursive1,limit_recursive2],
	    SEG);

(*****************************************************************************)
(* Word and FCP testing:                                                     *)
(*     i2n                 : Convert integers to natural numbers (mod p)     *)
(*     extend              : Convert a signed int to a signed int (mod p)    *)
(*                                                                           *)
(*****************************************************************************)

local
open intLib integerTheory
val i2n_lemma = prove(``0 <= (i + 1) rem 2 ** l - 1 + 2 ** l``,
    REWRITE_TAC [ARITH_PROVE ``0i <= a - 1 + b = ~a < b``] THEN
    MATCH_MP_TAC (ARITH_PROVE ``!a b c. a <= b /\ b < c ==> a < c:int``) THEN
    Q.EXISTS_TAC `ABS ((i + 1) rem 2 ** l)` THEN
    METIS_TAC [INT_REMQUOT,INT_ABS_NUM,INT_EXP,INT_EXP_EQ0,
        ARITH_PROVE ``~(2 = 0i)``,INT_ABS,INT_NOT_LT,INT_NEGNEG,INT_LE_REFL,
	INT_LE_NEGL]);
in
val thms = [INT_EXP_EQ0,ARITH_PROVE ``~(2 = 0i)``,
            REWRITE_CONV [integerTheory.INT_POS,integerTheory.INT_EXP] 
                 ``0 <= 2 ** a``,
            prove(``~(b = 0) /\ 0i <= b ==> 0 <= a % b``,
		     METIS_TAC [INT_MOD_BOUNDS,INT_NOT_LT]),i2n_lemma]
end;

val _ = add_test("i2n",
	    translate_conditional_function [(``i2n``,"I2N")] thms,
	    signedintTheory.i2n_def);

val _ = add_test("extend",
	    translate_simple_function [(``extend``,"EXTEND")],
	    signedintTheory.extend_def);

val _ = add_test("word_div",
	    translate_limit_fcp_function
	    "WORDDIV"
	    [``\a b. ~(b = 0w)``] [wordsTheory.w2n_eq_0],
	    wordsTheory.word_div_def);

(*****************************************************************************)
(* Functions with limits and recursion proofs (ie. LOG)                      *)
(*****************************************************************************)

val log_compute = prove(``1 < a /\ 1 <= x ==> 
	     (LOG a x = if x < a then 0 else 1 + LOG a (x DIV a))``,
    RW_TAC std_ss [] THEN 
    FULL_SIMP_TAC std_ss [arithmeticTheory.NOT_LESS,logrootTheory.LOG_DIV] THEN
    MATCH_MP_TAC logrootTheory.LOG_UNIQUE THEN 
    RW_TAC arith_ss [arithmeticTheory.EXP]);

val log_rec = prove(``1 < a /\ 1 <= x ==> x DIV a < x``,
    REPEAT (Induct_on `a` THEN 
    RW_TAC arith_ss [arithmeticTheory.DIV_LT_X,arithmeticTheory.ADD1,
           arithmeticTheory.LEFT_ADD_DISTRIB]));

val log_rec_ok = prove(``~(a = 0) /\ ~(x < a) ==> (1 <= x DIV a)``,
       RW_TAC arith_ss [arithmeticTheory.NOT_LESS,arithmeticTheory.X_LE_DIV]);

val _ = add_test("LOG",
	     translate_limit_function 
	     [(``LOG``,"log")]
	     [(``LOG``,[``\a b. 1n < a /\ 1n <= b ``,
	      ``\a b. 1 < a /\ 1 <= b ==> b DIV a < b``])]
             [GEN_ALL log_rec,DECIDE ``1 < a ==> ~(a = 0n)``,log_rec_ok],
             log_compute);

(*****************************************************************************)
(* Testing HO functions                                                      *)
(*****************************************************************************)

val _ = add_test("EVERY",
		 translate_simple_function
		 [(``EVERY``,"everyless")],
                 (CONJ (ISPEC ``\a. 0n < a`` (CONJUNCT1 EVERY_DEF))
		       (ISPEC ``\a. 0n < a`` (CONJUNCT2 EVERY_DEF))));

val _ = add_test("ADDLIST",
		 translate_simple_function
		 [(``ADDLIST``,"addlist")],
		 ADDLIST_def);

val _ = add_test("SNOC",
		 translate_simple_function
		 [(``SNOC``,"snoc")],
		 (INST_TYPE [alpha |-> num] rich_listTheory.SNOC));

val _ = add_test("GENLIST",
                translate_simple_function
                [(``GENLIST``,"genlist")],
		   (REWRITE_RULE [combinTheory.I_THM] 
		      ((LIST_CONJ (map (ISPEC ``I:num -> num``)
		   	      (CONJUNCTS rich_listTheory.GENLIST))))));

val _ = add_test("GENL",translate_simple_function 
                [(``GENL``,"genl")],GENL_def);		   

val _ = add_test("ADDN",translate_simple_function 
               [(``ADDN``,"addn")],ADDN_def);

(*****************************************************************************)
(* Perform the testing...                                                    *)
(*****************************************************************************)

(*
val _ = Hol_datatype `wordlist = WNil | WCons of 'a word => wordlist`;

val _ = types := ``:'a wordlist``::(!types);
*)

val _ = generate_functions ``:sexp``; 
val _ = generate_theorems ``:sexp``;

val _ = print "Testing flattening....";
val _ = set_trace "functionEncodeLib.Trace" 1;
val (passed,failed) = 
    mappartition (flatten_recognizers (mk_fullname ``:sexp``))
                 (!types);
val _ = if length failed > 1 then raise Empty else ();


val _ = print "Testing abstract flattening...";

val gen = Random.newgen();

fun mk_word t = type_subst [alpha |-> t] ``:'a word``;

fun tsubst t = 
let val tvs = type_vars t
    val tvs' = map (fn x => 
        if (Random.range(0,2) gen = 1) then mk_word x else x) tvs
    val r = type_subst (map2 (curry op|->) tvs tvs') t
in
    (print_type r ; print "\n" ; r)
end;

val _ = set_trace "functionEncodeLib.Trace" 1;
val f = can (match_term ``dimindex (:'a)``);
val target = ``:sexp``;
val word_gen = flatten_abstract_recognizers (K "wordp") 
               f ``:sexp`` ``:'a word``;
val cstypes = mapfilter Type [`:'a CS3`, `:'a CS2`, `:'a CS1`, `:'a CS4`];
val sane_types = filter (fn x => not (exists (can (C match_type x)) cstypes)) 
                        (!types)
val (passed,failed) = 
    mappartition (flatten_abstract_recognizers (mk_fullname ``:sexp``) 
                  f ``:sexp`` o tsubst) sane_types;
val _ = if length failed > 1 then raise Empty else ();

val _ = print "Testing rewrite-initialisation...";
val (passed,failed) = 
    mappartition (add_standard_coding_rewrites ``:sexp``) 
    (filter (not o C mem [``:register``,``:Steve0``]) (!types));
val _ = if length failed > 1 then raise Empty else ();

val _ = print "Testing predicate equivalence...";
val (passed,failed) = 
    mappartition (predicate_equivalence ``:sexp``) 
    (filter (not o C mem [``:register``,``:Steve0``]) (!types));
val _ = if length failed > 1 then raise Empty else ();

val _ = initialise_function_tests ();
val _ = set_trace "functionEncodeLib.Trace" 4;

(*****************************************************************************)
(* Polymorphic tests for datatypes...                                        *)
(*****************************************************************************)

val OPTION_JOIN_MAP = prove(
    ``!x. OPTION_JOIN (map (map f) x) = map f (OPTION_JOIN x)``,
    Cases THEN RW_TAC std_ss [get_source_function_def ``:'a option`` "map"]);

val _ = add_test ("OPTION_JOIN (polymorphic)",
            translate_simple_polymorphic_function 
	              [(``OPTION_JOIN``,"option_join")]
		      [(``OPTION_JOIN``,OPTION_JOIN_MAP)],
	    OPTION_JOIN_DEF);

val FLATTEN_TREE_MAP = prove(
    ``!x. FLATTEN_TREE (map f x) = MAP f (FLATTEN_TREE x)``,
    Induct THEN 
    RW_TAC std_ss [FLATTEN_TREE_def,get_source_function_def ``:'a Tree`` "map",
                   MAP,MAP_APPEND]);

val _ = add_test ("FLATTEN_TREE (polymorphic)",
            translate_simple_polymorphic_function 
                      [(``FLATTEN_TREE``,"flatten_tree")]
		      [(``FLATTEN_TREE``,FLATTEN_TREE_MAP)],
	    FLATTEN_TREE_def);

val FT_FAST_MAP = prove(
    ``!x y f. FT_FAST (map f x) (MAP f y) = MAP f (FT_FAST x y)``,
    Induct THEN 
    RW_TAC std_ss [FT_FAST_def,get_source_function_def ``:'a Tree`` "map",MAP]);

val _ = add_test ("FT_FAST (polymorphic)",
            translate_simple_polymorphic_function 
	              [(``FT_FAST``,"ft_fast")]
		      [(``FT_FAST``,FT_FAST_MAP)],
	    FT_FAST_def);

val _ = run_function_tests();

