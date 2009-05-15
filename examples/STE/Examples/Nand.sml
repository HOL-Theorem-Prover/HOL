(* Nand Delay *)
val Not_def = Define `Not (a:bool, b:bool) = (b, a)`;;

val And_def = Define `And (a, b) (c, d) = (a/\c, b\/d)`;; 

val Nand_def = Define `Nand a b = Not(And a b)`;
			       
val Nand_bool_def =  Define `Nand_bool s_b s_b' = 
    !node. ((node = "out") ==> 
	    (s_b' node = ~((s_b "in") /\ (s_b node))))`;

val Nand_lattice_def = Define `(Nand_lattice s node = 
			    if (node = "in")
				then X 
			    else if (node = "out") 
				     then 
					 Nand (s "in")(s node)
				 else
				     X)`;

val comp_list = [Nand_lattice_def, Nand_def, And_def, Not_def];

(* Its okay to relate Nand_lattice and Nand_bool *)
val NAND_OK = 
    store_thm ("NAND_OK", 
	       ``Okay (Nand_lattice, Nand_bool)``,
	       FULL_SIMP_TAC std_ss [Okay_def, 
				     Nand_lattice_def, Nand_def,
				     Nand_bool_def, And_def, Not_def,
				     extended_drop_state_def, 
				     leq_state_def] 
	       THEN REPEAT STRIP_TAC 
	       THEN REPEAT COND_CASES_TAC 
	       THEN fs [lattice_X1_lemma, leq_def] 
	       THENL [PROVE_TAC [lattice_X1_lemma],
		      Cases_on `s_b "in"` THEN fs [drop_def, 
						   One_def,
						   Zero_def, 
						   X_def,
						   Top_def,
						   lub_def, 
						   Nand_def, 
						   And_def,
						   Not_def],
		      PROVE_TAC [lattice_X1_lemma]]
	       THEN Cases_on `s_b "out"` THEN fs [drop_def, 
						  One_def,
						  Zero_def, 
						  X_def,
						  Top_def,
						  lub_def, 
						  Nand_def,
						  And_def,
						  Not_def]);
    

(* Nand lattice is monotonic *)
val NAND_MONOTONIC = 
    store_thm("NAND_MONOTONIC", 
	      ``Monotonic Nand_lattice``,
	      FULL_SIMP_TAC std_ss [Monotonic_def, 
				    Nand_lattice_def,
				    Nand_def,
				    Nand_bool_def, And_def, Not_def,
				    extended_drop_state_def, 
				    leq_state_def] 
	      THEN REPEAT STRIP_TAC 
	      THEN REPEAT COND_CASES_TAC 
	      THEN fs [leq_def, lub_def, X_def]
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"in"``)
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"out"``)
	      THEN Cases_on `s "in"` THEN Cases_on `s' "in"`
	      THEN Cases_on `s "out"` THEN Cases_on `s' "out"`
	      THEN fs [Not_def, And_def, lub_def] 
	      THEN Cases_on `q` 
	      THEN Cases_on `r` 
	      THEN Cases_on `q'` 
	      THEN Cases_on `r'` THEN PROVE_TAC []);

(* Example *)    
	
(* STE assertions *)

val a1 = (T, "in", ``v1:bool``, 0, 1);
val a2 = (T, "out", ``v2:bool``, 0, 1);
val c  =  (T, "out", ``~(v1/\v2):bool``, 1, 2) ;
val A  =  TF [a1, a2];
val C  =  TF [c];

(* Running the STE Simulator *)	      
val NAND_STE_IMPL1 = STE A C ``Nand_lattice`` comp_list true;

(* STE TO BOOL *)
val NAND_STE_BOOL1 = STE_TO_BOOL A C ``Nand_lattice`` ``Nand_bool`` 
    NAND_OK NAND_MONOTONIC NAND_STE_IMPL1;



