(* File: e1.sml *)
(*
   t0 is an example of a simple nesting
   t1 is an example of nesting within nesting of the same type constructor
   t2 is an example of nesting within nesting of the different type
      constructors.
   t3 is an example using the prod type constuctor.  Here you have to
      create your own recursion theorem.
   e0 is an example of a fairly typical nesting, with multiple cases.
      It has irrelevant recursor theorems, num_Axiom and sum_Axiom.
   e1 is the same as e0, but without the irrelevant theorem.
   e2 is an example without any actual nesting at all.
   e3 is an example with polymorphism
*)


(*---------------------------------------------------------------------------
  SRC=/home/kxs/hol.ken/src
  THEORIES=/home/kxs/hol.ken/theories
  LIBRARY=/home/kxs/hol.ken/library
  mosml -I ${SRC} -I ${SRC}/portableML -I ${SRC}/0 -I ${SRC}/1 -I ${SRC}/2 \
        -I ${SRC}/3 -I ${THEORIES} \
        -I ${LIBRARY}/num/src \
        -I ${LIBRARY}/utils/src \
        -I ${LIBRARY}/mutrec/src 
 *---------------------------------------------------------------------------*)
load"nested_recLib";
quotation := true;
open DefTypeInfo;
open Parse;
fun print_thm th = (Thm.print_thm th; Portable.output(Portable.std_out, "\n"));

(* An example of a simple nesting *)

val {Cases_Thm = t0_cases, 
     Constructors_Distinct_Thm = t0_distinct,
     Constructors_One_One_Thm = t0_one_one, 
     New_Ty_Existence_Thm = t0_existence,
     New_Ty_Induct_Thm = t0_induct, 
     New_Ty_Uniqueness_Thm = t0_unique} 
  = 
  nested_recLib.define_type
     [{type_name = "Alist",
       constructors = [{name = "mkA",
	                arg_info = [type_op{Tyop = "list",
                                            Args = [being_defined "Alist"]}]}]}]
     [listTheory.list_Axiom];



(* An example of nesting within nesting *)

val {Cases_Thm = t1_cases, 
     Constructors_Distinct_Thm = t1_distinct,
     Constructors_One_One_Thm = t1_one_one, 
     New_Ty_Existence_Thm = t1_existence,
     New_Ty_Induct_Thm = t1_induct, 
     New_Ty_Uniqueness_Thm = t1_unique} 
  = 
  nested_recLib.define_type
     [{type_name = "Blist",
       constructors = [{name = "mkB", arg_info = 
         [type_op {Tyop = "list", Args =
		      [type_op {Tyop = "list",
				Args = [being_defined "Blist"]}]}]}]}]
     [listTheory.list_Axiom];


(* An example of nesting within nesting of the different type constructors. *)
val {Cases_Thm = t2_cases, 
     Constructors_Distinct_Thm = t2_distinct,
     Constructors_One_One_Thm = t2_one_one, 
     New_Ty_Existence_Thm = t2_existence,
     New_Ty_Induct_Thm = t2_induct, 
     New_Ty_Uniqueness_Thm = t2_unique} 
  = 
  nested_recLib.define_type  (* sAlist := smk of (sAlist list) + (sAlist list) *)
    [{type_name = "sAlist",
      constructors =
       [{name = "smk", arg_info =
	    [type_op {Tyop = "sum",
		      Args = [type_op {Tyop = "list",
				       Args = [being_defined "sAlist"]},
			      type_op {Tyop = "list",
				       Args = [being_defined "sAlist"]}]}]}]}]
		
     [listTheory.list_Axiom, sumTheory.sum_Axiom];


(* An example with prod *)

val {Cases_Thm = t3_cases, 
     Constructors_Distinct_Thm = t3_distinct,
     Constructors_One_One_Thm = t3_one_one, 
     New_Ty_Existence_Thm = t3_existence,
     New_Ty_Induct_Thm = t3_induct, 
     New_Ty_Uniqueness_Thm = t3_unique} 
  = 
  nested_recLib.define_type     (* Aprod := End | pmk of (Aprod # Aprod) *)
    [{type_name = "Aprod",
      constructors = 
        [{name = "End", arg_info = []},
         {name = "pmk", arg_info =
		    [type_op {Tyop = "prod",
			      Args = [being_defined "Aprod",
				      being_defined "Aprod"]}]}]}]
	 [pairTheory.pair_Axiom];


(* FAILS *)
val {Cases_Thm = t4_cases, 
     Constructors_Distinct_Thm = t4_distinct,
     Constructors_One_One_Thm = t4_one_one, 
     New_Ty_Existence_Thm = t4_existence,
     New_Ty_Induct_Thm = t4_induct, 
     New_Ty_Uniqueness_Thm = t4_unique} 
  = 
  nested_recLib.define_type    		
            (*
             state = State of (num # value) list
             env = Env of (num # value) list | AltEnv of (num # value) list
             value = Base of 'a | Ind of num env | Ref of (state # value)
             *)
      [{type_name = "state",
        constructors =
          [{name = "State",
            arg_info = [type_op {Tyop = "list", Args =
                         [type_op {Tyop = "prod", Args =
                            [existing (==`:num`==),being_defined "value"]}]}]}]},
       {type_name = "env",
        constructors =
          [{name = "Env1",
            arg_info = [type_op {Tyop = "list", Args =
                          [type_op {Tyop = "prod", Args =
                             [existing (==`:num`==), being_defined "value"]}]}]},
           {name = "Env2",
            arg_info = [type_op {Tyop = "list", Args =
                        [type_op {Tyop = "prod", Args =
                          [existing (==`:num`==), being_defined "value"]}]}]}]},
       {type_name = "value",
        constructors =
          [{name = "Base", arg_info = [existing (==`:'a`==)]},
           {name = "Ind",  arg_info = being_defined "env"]},
           {name = "Ref", arg_info =
                    [type_op {Tyop = "prod",
                              Args = [being_defined "state",
                                     being_defined "value"]}]}]}]
      [listTheory.list_Axiom,pairTheory.pair_Axiom];



(* An example of irrelevant recursor theorems  -- fails *)

val {Cases_Thm = e0_cases, 
     Constructors_Distinct_Thm = e0_distinct,
     Constructors_One_One_Thm = e0_one_one, 
     New_Ty_Existence_Thm = e0_existence,
     New_Ty_Induct_Thm = e0_induct, 
     New_Ty_Uniqueness_Thm = e0_unique} 
  = 
  nested_recLib.define_type   (* "BBlist = mkBB of BBlist list | mkBB1 of num" *)
   [{type_name = "BBlist",
     constructors = [{name = "mkBB1", arg_info = [existing (==`:num`==)]}]}]
   [listTheory.list_Axiom, prim_recTheory.num_Axiom, sumTheory.sum_Axiom];

val {Cases_Thm = e1_cases, 
     Constructors_Distinct_Thm = e1_distinct,
     Constructors_One_One_Thm = e1_one_one, 
     New_Ty_Existence_Thm = e1_existence,
     New_Ty_Induct_Thm = e1_induct, 
     New_Ty_Uniqueness_Thm = e1_unique} 
  = 
  nested_recLib.define_type   (* "BBlist = mkBB of BBlist list | mkBB1 of num" *)
   [{type_name = "BBlist",
     constructors = [{name = "mkBB1", arg_info = [existing (==`:num`==)]}]}]
   [listTheory.list_Axiom];


(* An example with no actual nesting *)

val {Cases_Thm = e2_cases, 
     Constructors_Distinct_Thm = e2_distinct,
     Constructors_One_One_Thm = e2_one_one, 
     New_Ty_Existence_Thm = e2_existence,
     New_Ty_Induct_Thm = e2_induct, 
     New_Ty_Uniqueness_Thm = e2_unique} 
  = 
  nested_recLib.define_type   	    (* "AB = mkAB1 of num" *)
    [{type_name = "AB", 
      constructors = [{name = "mkAB1", arg_info = [existing (==`:num`==)]}]}]
    [];


(* An example with polymorphism  - FAILS *)
    
val {Cases_Thm = e3_cases, 
     Constructors_Distinct_Thm = e3_distinct,
     Constructors_One_One_Thm = e3_one_one, 
     New_Ty_Existence_Thm = e3_existence,
     New_Ty_Induct_Thm = e3_induct, 
     New_Ty_Uniqueness_Thm = e3_unique} 
  = 
  nested_recLib.define_type    (* "CClist = mkCC of CClist list | mkCC1 of 'a" *)
   [{type_name = "CClist",
     constructors =
        [{name = "mkCC", arg_info = [type_op {Tyop = "list",
                                              Args = [being_defined "CClist"]}]},
         {name = "mkCC1", arg_info = [existing (==`:'a`==)]}]}]
   [listTheory.list_Axiom];
