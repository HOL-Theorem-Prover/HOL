(* Two bit comparator *)

val fs = FULL_SIMP_TAC std_ss;

(* Basic circuit functions defined on a domain of lattice values *)
val Or_def = Define `Or (a, b) (c, d) = (a\/c, b/\d)`;; 

val Not_def = Define `Not (a:bool, b:bool) = (b, a)`;;

val And_def = Define `And (a, b) (c, d) = (a/\c, b\/d)`;; 

val Xnor_def = Define `Xnor a b = Or (And a b)(And (Not a)(Not b))`;

(* Unit delay two bit comparator circuit for equality testing - lattice model*)
val Comparator_lattice_def = Define `(Comparator_lattice s node = 
			      if (node = "a0") then X
				  else if (node = "a1") then X
				      else if (node = "b0") then X
					  else if (node = "b1") then X
					      else if (node = "out") then
						  And (Xnor (s "a0")(s "b0"))
						  (Xnor (s "a1")(s "b1"))
						      else X)`;
    

(* Unit delay two bit comparator circuit for equality testing - Boolean model*)
val Comparator_bool_def = Define `Comparator_bool (s_b:string->bool) s_b' =
    !node. (node = "out") ==> 
    (s_b' node = (s_b "a0" = s_b "b0") /\ (s_b "a1" = s_b "b1"))`;


val comp_list = [Comparator_lattice_def, Xnor_def, Or_def, 
		 And_def, Not_def];

(* prove that it is okay to relate the two models for comparator *)    
val COMPARATOR_OK = 
    store_thm ("COMPARATOR_OK",
	       ``Okay (Comparator_lattice, Comparator_bool)``,
	       FULL_SIMP_TAC std_ss [Okay_def, 
				     Comparator_lattice_def, Xnor_def, Or_def,
				     Comparator_bool_def, And_def, Not_def,
				     extended_drop_state_def, 
				     leq_state_def]
	       THEN REPEAT STRIP_TAC 
	       THEN REPEAT COND_CASES_TAC 
	       THEN fs [lattice_X1_lemma, leq_def] 
	       THENL [PROVE_TAC [lattice_X1_lemma],
		      PROVE_TAC [lattice_X1_lemma],
		      PROVE_TAC [lattice_X1_lemma],
		      PROVE_TAC [lattice_X1_lemma],
		      Cases_on `s_b "a0"`
		      THEN Cases_on `s_b "b0"` 
		      THEN Cases_on `s_b "a1"` 
		      THEN Cases_on `s_b "b1"`
		      THEN fs [drop_def, 
			       One_def,
			       Zero_def, 
			       X_def,
			       Top_def,
			       lub_def, 
			       Or_def,
			       And_def,
			       Not_def],
		      PROVE_TAC [lattice_X1_lemma]]);

(* prove that the comparator circuit is monotonic *)    
val COMPARATOR_MONOTONIC = 
    store_thm("COMPARATOR_MONOTONIC",
	      ``Monotonic Comparator_lattice``,
	      FULL_SIMP_TAC std_ss [Monotonic_def, 
		      Comparator_lattice_def,
		      Xnor_def, Or_def,
		      And_def, Not_def,
		      extended_drop_state_def, 
		      leq_state_def] 
	      THEN REPEAT STRIP_TAC 
	      THEN REPEAT COND_CASES_TAC 
	      THEN fs [leq_def, lub_def, X_def]
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"a0"``)
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"a1"``)
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"b0"``)
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"b1"``)
	      THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"out"``)
	      THEN Cases_on `s "a0"` THEN Cases_on `s' "a0"`
	      THEN Cases_on `s "b0"` THEN Cases_on `s' "b0"`
	      THEN Cases_on `s "a1"` THEN Cases_on `s' "a1"`
	      THEN Cases_on `s "b1"` THEN Cases_on `s' "b1"`
	      THEN Cases_on `s "out"` THEN Cases_on `s' "out"`
	      THEN fs [Not_def, And_def, Or_def, lub_def] 
	      THEN RW_TAC std_ss [] 
	      THENL [EQ_TAC THEN REPEAT STRIP_TAC THEN fs [],
		     EQ_TAC THEN REPEAT STRIP_TAC THEN fs []]);



(*********************** E X A M P L E S *******************************)

(* Example I *)

val a0 = (T, "a0", ``a0:bool``, 0, 1);
val a1 = (T, "a1", ``a1:bool``, 0, 1);
val b0 = (T, "b0", ``b0:bool``, 0, 1);
val b1 = (T, "b1", ``b1:bool``, 0, 1);
val out = (T, "out", ``(a0:bool=b0)/\(a1=b1)``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	      
val COMPARATOR_STE_IMPL1 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL1 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL1;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL1;

(* Example II *)

val a0 = (T, "a0", ``T:bool``, 0, 1);
val a1 = (T, "a1", ``T:bool``, 0, 1);
val b0 = (T, "b0", ``T:bool``, 0, 1);
val b1 = (T, "b1", ``T:bool``, 0, 1);
val out = (T, "out", ``T``, 1, 2);
val A  =  TF [a0, a1, b0, b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	      
val COMPARATOR_STE_IMPL2 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL2 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL2;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL2;

(* Example III *)

val a0 = (T, "a0", ``a0:bool``, 0, 1);
val a1 = (T, "a1", ``a1:bool``, 0, 1);
val b0 = (T, "b0", ``b0:bool``, 0, 1);
val b1 = (T, "b1", ``b1:bool``, 0, 1);
val out = (T, "out", ``(a0:bool=b0)/\(a1=b1)``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	      
val COMPARATOR_STE_IMPL3 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL3 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL3;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL3;

(* Example IV *)

val a0 = (T, "a0", ``v0:bool``, 0, 1);
val a1 = (T, "a1", ``v1:bool``, 0, 1);
val b0 = (T, "b0", ``v0:bool``, 0, 1);
val b1 = (T, "b1", ``v1:bool``, 0, 1);
val out = (T, "out", ``T``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	      
val COMPARATOR_STE_IMPL4 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL4 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL4;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL4;

(* Example V *)

val a0 = (T, "a0", ``T:bool``, 0, 1);
val a1 = (T, "a1", ``T:bool``, 0, 1);
val b0 = (T, "b0", ``T:bool``, 0, 1);
val b1 = (T, "b1", ``T:bool``, 0, 1);
val out = (T, "out", ``T``, 1, 2);
val A  =  TF [a0, a1, b0, b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	
val COMPARATOR_STE_IMPL5 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL5 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL5;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL5;

(* Example VI *)

val a0 = (T, "a0", ``T:bool``, 0, 1);
val a1 = (T, "a1", ``F:bool``, 0, 1);
val b0 = (T, "b0", ``T:bool``, 0, 1);
val b1 = (T, "b1", ``F:bool``, 0, 1);
val out = (T, "out", ``T``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out];

(* Running the STE Simulator *)	
val COMPARATOR_STE_IMPL6 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL6 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL6;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL6;

(* Example VII *)

val a0 = (T, "a0", ``T:bool``, 0, 1);
val a1 = (T, "a1", ``F:bool``, 0, 1);
val b0 = (T, "b0", ``T:bool``, 0, 1);
val b1 = (T, "b1", ``T:bool``, 0, 1);
val out = (T, "out", ``T``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)	
val COMPARATOR_STE_IMPL7 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL7 = 
STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL7;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL7;

(* Example VIII *)

val a0 = (T, "a0", ``T:bool``, 0, 1);
val a1 = (T, "a1", ``F:bool``, 0, 1);
val b0 = (T, "b0", ``T:bool``, 0, 1);
val b1 = (T, "b1", ``T:bool``, 0, 1);
val out = (T, "out", ``F``, 1, 2);
val A  =  TF [a0,a1,b0,b1] ;
val C  =  TF [out] ;

(* Running the STE Simulator *)
val COMPARATOR_STE_IMPL8 = STE A C ``Comparator_lattice`` comp_list true;

(* STE TO BOOL *)
val COMPARATOR_STE_BOOL8 = 
    STE_TO_BOOL A C ``Comparator_lattice`` ``Comparator_bool`` 
    COMPARATOR_OK COMPARATOR_MONOTONIC COMPARATOR_STE_IMPL8;

CONV_RULE(EVAL) COMPARATOR_STE_BOOL8;
