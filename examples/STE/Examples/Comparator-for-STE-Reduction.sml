(* Two bit comparator *)
val _ = load "combinTheory";
val _ = load "stringLib";
val _ = load "pairTheory";
val _ = load "arithmeticTheory";
val _ = load " listTheory";
open combinTheory stringLib pairTheory arithmeticTheory listTheory;

fun SUC_ELIM n = 
    let val thm =
	RIGHT_CONV_RULE(TOP_DEPTH_CONV numLib.num_CONV)(numLib.num_CONV n)
	in thm end;


(* Basic circuit functions defined on a domain of lattice values *)
val Or_def = Define `Or (a, b) (c, d) = (a\/c, b/\d)`;; 

val Not_def = Define `Not (a:bool, b:bool) = (b, a)`;;

val And_def = Define `And (a, b) (c, d) = (a/\c, b\/d)`;; 

val Xnor_def = Define `Xnor a b = Or (And a b)(And (Not a)(Not b))`;

(* Unit delay two bit comparator circuit for equality testing - lattice model*)
val Comparison_def = Define `(Comparison s node =
    if (node = "a0") then X
    else if (node = "a1") then X
	 else if (node = "b0") then X
	      else if (node = "b1") then X
		  else if (node = "i0") 
			   then 
			       Xnor (s "a0")(s "b0")
		       else if (node = "i1") 
				then 
				    Xnor (s "a1")(s "b1")
			    else if (node = "out") 
				     then
					 And 
					 (Xnor (s "a0")(s "b0"))
					 (Xnor (s "a1")(s "b1"))
				 else X)`;

val And_lattice_def = Define `(And_lattice s node = 
			    if (node = "i0")
				then X
			    else if (node = "i1") then 
				X
				 else if (node = "out") 
					  then 
					      And (s "i0")(s "i1")
				      else
					  X)`;

val Bitwise_comparison_def = Define `(Bitwise_comparison s node =
    if (node = "a0") then X
    else if (node = "a1") then X
	 else if (node = "b0") then X
	      else if (node = "b1") then X
		  else if (node = "i0") then Xnor (s "a0")(s "b0")
		       else if (node = "i1") then Xnor (s "a1")(s "b1")
			   else X)`;


val Comparator_lattice_def = Define `(Comparator_lattice  = 
				      And_lattice o Bitwise_comparison)`;

val xnor_def = Define `xnor a b = (a /\ b) \/ (~a /\ ~b)`;    
val comp_list = [Comparison_def, Bitwise_comparison_def, 
		 Comparator_lattice_def,
		 Xnor_def, xnor_def, Or_def, o_DEF,
		 And_def, And_lattice_def, Not_def, FST, SND];



val MEM_CONV = SIMP_CONV list_ss [DISJ_IMP_THM, MAP, MEM, LESS_OR_EQ, LESS_EQ,
				FORALL_AND_THM, UNWIND_FORALL_THM1, 
				LENGTH, HD, TL, FOLDR, MAP2];

(*********************** E X A M P L E S *******************************)

(* Example I *)

val a0 = (T, "a0", ``a0:bool``, 0, 1);
val a1 = (T, "a1", ``a1:bool``, 0, 1);
val b0 = (T, "b0", ``b0:bool``, 0, 1);
val b1 = (T, "b1", ``b1:bool``, 0, 1);
val out = (T, "out", ``xnor a0 b0 /\ xnor a1 b1``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	      
val COMPARATOR_STE_IMPL1 = STE A C ``Comparator_lattice`` comp_list true;

(******* using symmetry  ****************************************************)
(*
The detailed solution
----------------------

Equality
--------

The goal is to show that 

Comp |= ("a0" is a0) and ("b0" is b0) and
        ("a1" is a1) and ("b1" is b1) 
         ==>> ("out" is 1) when (xnor a0 b0 /\ xnor a1 b1)

A1 = ("a0" is a0) and ("b0" is b0) from 0 to 1
A2 = ("a1" is a1) and ("b1" is b1) from 0 to 1
B1 = ("i0" is 1)  from 1 to 2
B2 = ("i1" is 1) from 1 to 2
G1 = (a0=b0) 
G2 = (a1=b1)
C = "out" is 1 from 2 to 3
*)

val A1 = TF [(T, "a0", ``a0:bool``, 0, 1), (T, "b0", ``b0:bool``, 0, 1)];
val G1 = ``xnor a0 b0``;
val B1 = (T, "i0", T, 1, 2);

(* B1 when G1*)
val NewB1 = TF [(G1, "i0", T, 1, 2)];

(* Comp |= A1 ==>> B1 when G1  (STE run) *)

STE A1 NewB1 ``Bitwise_comparison`` comp_list true;

(*
From symmetry we conclude

Comp |= A2 ==>> B2 when G2  (Symmetry)

By Constr Impl1 we get

G1 ==> (Comp |= A1 ==>> B1)

G2 ==> (Comp |= A2 ==>> B2)

From GUARD CONJUNCTION we get

(G1 /\ G2) ==> (Comp|= (A1 and A2) ==>> (B1 and B2))

*)

(* Comp |= (B1 and B2) ==>> C (STE run) *)

val B1 = (T, "i0", T, 0, 1);
val B2 = (T, "i1", T, 0, 1);
val C = (T, "out", T, 1, 2);

STE (TF [B1, B2]) (TF [C]) ``And_lattice`` comp_list true;

By time shift lemma it will be true that for the following formulas

val B1 = (T, "i0", T, 1, 2);
val B2 = (T, "i1", T, 1, 2);
val C = (T, "out", T, 2, 3);

 the following lemma will hold

|- STE (TF [B1, B2]) (TF [C]) ``And_lattice`` comp_list true;


By SPECIALISED CUT 1  we get

(G1 /\ G2) ==> (Comp |= A1 and A2 ==>> C)

By Constr Impl 2 we get

Comp |= (A1 and A2) ==>> (C when (G1 /\ G2))

Replacing the values of A1, A2, C, G1 and G2 we get

Comp |= ("a0" is a0) and ("b0" is b0) and
        ("a1" is a1) and ("b1" is b1) 
         ==>> ("out" is 1) when ((a0=b0) /\ (a1=b1))

Similarly we can do the Inequality case by following the flow in this file
../../TypeSystem/Examples/Comparator.sml
