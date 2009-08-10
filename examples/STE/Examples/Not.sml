(* Unit delay inverter -- lattice model *)

val fs = FULL_SIMP_TAC std_ss;
val Not_def = Define `Not (a:bool, b:bool) = (b, a)`;;

val Not_lattice_def = Define `Not_lattice s node =
    if (node = "in") then X
    else if (node = "out") then Not (s "in")
	 else X`;

(* Unit delay inverter -- Boolean model *)

val Not_bool_def =  Define `Not_bool s_b s_b' =
    !node. ((node = "out") ==> (s_b' node = ~(s_b "in")))`;


val comp_list = [Not_lattice_def, Not_def, Not_def];


val NOT_OK = store_thm("NOT_OK", ``Okay (Not_lattice, Not_bool)``,
		       FULL_SIMP_TAC std_ss [Okay_def,
					     Not_lattice_def,
					     Not_bool_def, Not_def,
					     extended_drop_state_def,
					     leq_state_def]
		       THEN REPEAT STRIP_TAC
		       THEN REPEAT COND_CASES_TAC
		       THEN fs [lattice_X1_lemma, leq_def]
		       THENL [PROVE_TAC [lattice_X1_lemma],
			      Cases_on `s_b "in"`
			      THEN Cases_on `s_b' "out"`
			      THEN fs [drop_def, One_def, Zero_def,
				       X_def, Top_def, lub_def,
				       Not_def,
				       Not_bool_def],
			      PROVE_TAC [lattice_X1_lemma]]);



val NOT_MONOTONIC =
    store_thm ("NOT_MONOTONIC",
	       ``Monotonic Not_lattice``,
	       FULL_SIMP_TAC std_ss [Monotonic_def,
				     Not_lattice_def,
				     Not_def,
				     extended_drop_state_def,
				     leq_state_def]
	       THEN REPEAT STRIP_TAC
	       THEN REPEAT COND_CASES_TAC
	       THEN fs [leq_def, lub_def, X_def]
	       THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"in"``)
	       THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"out"``)
	       THEN Cases_on `s "in"`
	       THEN Cases_on `s' "in"`
	       THEN Cases_on `q`
	       THEN Cases_on `r`
	       THEN Cases_on `q'`
	       THEN Cases_on `r'`
	       THEN PROVE_TAC [Not_def, lub_def]);

(* Example I *)

val a =  (T, "in", ``v1:bool``, 0, 1);
val c  =  (T, "out", ``~v1:bool``, 1, 2) ;
val A  =  TF [a] ;
val C  =  TF [c] ;

(* Running the STE simulator *)
val NOT_STE_IMPL1 = STE A C ``Not_lattice`` comp_list true;

(* STE TO BOOL *)
val NOT_STE_BOOL1 =
    STE_TO_BOOL A C ``Not_lattice`` ``Not_bool``
    NOT_OK NOT_MONOTONIC NOT_STE_IMPL1;

CONV_RULE (EVAL) NOT_STE_BOOL1;


(* Example II *)

val a = (T, "in", ``v1:bool``, 0, 1);
val c  =  (T, "out", ``v1:bool``, 1, 2) ;
val A  =  TF [a] ;
val C  =  TF [c] ;

(* Running the STE simulator *)
val NOT_STE_IMPL2 = STE A C ``Not_lattice`` comp_list true;

(* STE TO BOOL *)
val NOT_STE_BOOL2 =
    STE_TO_BOOL A C ``Not_lattice`` ``Not_bool``
    NOT_OK NOT_MONOTONIC NOT_STE_IMPL2;

CONV_RULE(EVAL) NOT_STE_BOOL2;;


