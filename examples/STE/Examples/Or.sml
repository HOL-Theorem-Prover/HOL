(* Or Delay *)

val Or_def = Define  `Or (a, b) (c, d) = (a\/c, b/\d)`;;

val Or_bool_def =  Define `Or_bool s_b s_b' = 
    !node. ((node = "out") ==> 
	    (s_b' node = ((s_b "i0") \/ (s_b "i1"))))`;

val Or_lattice_def = Define `(Or_lattice s node = 
			    if (node = "i0")
				then X 
			    else if (node = "i1") then X
			    else if (node = "out") 
				     then 
					 Or (s "i0")(s "i1")
				 else
				     X)`;

val comp_list = [Or_lattice_def, Or_bool_def, Or_lattice_def];

val a1 = (T, "i0", ``v1:bool``, 0, 1);
val a2 = (T, "i1", ``v2:bool``, 0, 1);
val c  =  (T, "out", ``(v1\/v2):bool``, 1, 2) ;
val A  =  TF [a1, a2];
val C  =  TF [c];

(* Running the STE Simulator *)	      
val OR_STE_IMPL1 = STE A C ``Or_lattice`` comp_list true;


val comp_list = [Or_lattice_def, Or_bool_def, Or_lattice_def];

(* under specified assertion *)
val a1 = (T, "i0", ``v1:bool``, 0, 1);
val c  =  (``v1:bool``, "out", ``T:bool``, 1, 2) ;
val A  =  TF [a1];
val C  =  TF [c];

(* Running the STE Simulator *)	      
val OR_STE_IMPL1 = STE A C ``Or_lattice`` comp_list true;
val residue = rhs(concl OR_STE_IMPL1);

set_goal([], ``v1 ==> ^residue``);

(* for the case when the output of the or gate is low *)

val a1 = (T, "i0", ``v1:bool``, 0, 1);
val a2 = (T, "i1", ``v2:bool``, 0, 1);
val c  = (T, "out", ``F:bool``, 1, 2) ;
val A  =  TF [a1,a2];
val C  =  TF [c];

(* Running the STE Simulator *)	      
val OR_STE_IMPL1 = STE A C ``Or_lattice`` comp_list true;
