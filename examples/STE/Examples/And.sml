
(* And Delay *)

val And_def = Define  `And (a, b) (c, d) = (a/\c, b\/d)`;;

val And_bool_def =  Define `And_bool s_b s_b' =
    !node. ((node = "out") ==>
	    (s_b' node = ((s_b "i0") /\ (s_b "i1"))))`;

val And_lattice_def = Define `(And_lattice s node =
			    if (node = "i0")
				then X
			    else if (node = "i1") then X
			    else if (node = "out")
				     then
					 And (s "i0")(s "i1")
				 else
				     X)`;

val comp_list = [And_lattice_def, And_bool_def];

val a1 = (T, "i0", ``v1:bool``, 0, 1);
val a2 = (T, "i1", ``v2:bool``, 0, 1);
val c  =  (T, "out", ``(v1/\v2):bool``, 1, 2) ;
val A  =  TF [a1, a2];
val C  =  TF [c];

(* Running the STE Simulator *)
val AND_STE_IMPL1 = STE A C ``And_lattice`` comp_list true;

(* when you expect a low output at the AND gate *)

 (* under specification works okay *)
val a1 = (T, "i0", ``v1:bool``, 0, 1);
val c  =  (T, "out", ``F:bool``, 1, 2) ;
val A  =  TF [a1];
val C  =  TF [c];

(* Running the STE Simulator *)
val AND_STE_IMPL1 = STE A C ``And_lattice`` comp_list true;


(* when you expect a high output at the AND gate *)
val a1 = (T, "i0", ``v1:bool``, 0, 1);
val a2 = (T, "i1", ``v2:bool``, 0, 1);
val c  = (T, "out", ``T:bool``, 1, 2) ;
val A  =  TF [a1,a2];
val C  =  TF [c];

(* Running the STE Simulator *)
val AND_STE_IMPL1 = STE A C ``And_lattice`` comp_list true;
val residue = rhs(concl AND_STE_IMPL1);

set_goal([], ``v1/\v2 ==> ^residue``);

