(* Unit delay 2-to-1 two bit MUX *)

val fs = FULL_SIMP_TAC std_ss;
val fl = FULL_SIMP_TAC list_ss;
val fw = FULL_SIMP_TAC (srw_ss());

(* Basic circuit functions defined on a domain of lattice values *)
val Or_def = Define `Or (a, b) (c, d) = (a\/c, b/\d)`;;

val Not_def = Define `Not (a:bool, b:bool) = (b, a)`;;

val And_def = Define `And (a, b) (c, d) = (a/\c, b\/d)`;;

(* Unit delay 2-to-1 two bit MUX ---  lattice model *)
val Mux_lattice_def =
    Define `(Mux_lattice s node =
	     if (node = "a0") then X
	     else if (node = "a1") then X
		  else if (node = "b0") then X
		       else if (node = "b1") then X
			    else if (node = "ctrl") then X
				 else
				     if (node = "out0")
					 then
					     Or
					     (And (s "a0")(s "ctrl"))
					     (And (s "b0")(Not(s "ctrl")))
				     else
					 if (node = "out1")
					     then
						 Or
						 (And (s "a1")(s "ctrl"))
						 (And (s "b1")(Not(s "ctrl")))
					 else X)`;

(* Unit delay 2-to-1 MUX Boolean model *)
val Mux_bool_def = Define `Mux_bool s_b s_b' =
    !node.
    (if (node = "out0") then
	 if (s_b "ctrl") then
	     (s_b' "out0" = s_b "a0")
	 else (s_b' "out0" = s_b "b0")
     else if (node = "out1") then
	 if (s_b "ctrl") then
	     (s_b' "out1" = s_b "a1")
	 else (s_b' "out1" = s_b "b1")
	  else T)`;


val comp_list = [Mux_lattice_def, Or_def, And_def, Not_def];

(* prove that it is okay to relate the two models for MUX *)
val MUX_OK =
    store_thm("MUX_OK",
	      ``Okay (Mux_lattice, Mux_bool)``,
	      FULL_SIMP_TAC std_ss [Okay_def, Mux_lattice_def, Or_def,
				    Mux_bool_def, And_def, Not_def,
				    extended_drop_state_def, leq_def,
				    leq_state_def]
	      THEN REPEAT STRIP_TAC
	      THEN REPEAT COND_CASES_TAC
	      THENL [PROVE_TAC [lattice_X1_lemma],
		     PROVE_TAC [lattice_X1_lemma],
		     PROVE_TAC [lattice_X1_lemma],
		     PROVE_TAC [lattice_X1_lemma],
		     PROVE_TAC [lattice_X1_lemma],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"out0"``)
		         THEN fw []
                         THEN POP_ASSUM MP_TAC
			    THEN COND_CASES_TAC
			    THENL [fl [] THEN Cases_on `s_b "a0"`
				   THEN Cases_on `s_b "b0"`
				   THEN Cases_on `s_b' "out0"`
				   THEN fs [drop_def, One_def, Zero_def,
					    X_def, Top_def, lub_def,
					    Or_def, And_def, Not_def],
				   Cases_on `s_b "a0"`
				   THEN Cases_on `s_b "b0"`
				   THEN Cases_on `s_b' "out0"`
				   THEN fs [drop_def, One_def, Zero_def,
					    X_def, Top_def, lub_def,
					    Or_def, And_def, Not_def]],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"out1"``)
                     THEN fw []
		     THEN POP_ASSUM MP_TAC THEN (REPEAT COND_CASES_TAC)
		     THENL [fl [] THEN Cases_on `s_b "a1"`
			    THEN Cases_on `s_b "b1"`
			    THEN Cases_on `s_b' "out1"`
			    THEN fs [drop_def, One_def, Zero_def,
				     X_def, Top_def, lub_def,
				     Or_def, And_def, Not_def],
			    fl [] THEN Cases_on `s_b "a1"`
			    THEN Cases_on `s_b "b1"`
			    THEN Cases_on `s_b' "out1"`
			    THEN fs [drop_def, One_def, Zero_def,
				     X_def, Top_def, lub_def,
				     Or_def, And_def, Not_def]],
		     PROVE_TAC [lattice_X1_lemma]]);

(* prove that the MUX circuit is monotonic *)
val MUX_MONOTONIC =
    store_thm("MUX_MONOTONIC", ``Monotonic Mux_lattice``,
	      FULL_SIMP_TAC std_ss [Monotonic_def,
				    Mux_lattice_def,
				    Or_def,
				    And_def, Not_def,
				    extended_drop_state_def,
				    leq_state_def]
	      THEN REPEAT STRIP_TAC
	      THEN REPEAT COND_CASES_TAC
	      THEN fs [leq_def, lub_def, X_def]
	      THENL [REPEAT (POP_ASSUM MP_TAC)
		     THEN CONV_TAC(TOP_DEPTH_CONV(stringLib.string_EQ_CONV))
		     THEN RW_TAC std_ss [],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"a0"``)
		     THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"ctrl"``)
		     THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"b0"``)
		     THEN Cases_on `s "a0"` THEN Cases_on `s' "a0"`
		     THEN Cases_on `s "b0"` THEN Cases_on `s' "b0"`
		     THEN Cases_on `s "ctrl"` THEN Cases_on `s' "ctrl"`
		     THEN fs [Not_def, And_def, Or_def, lub_def]
		     THEN RW_TAC std_ss [] THEN
		     EQ_TAC THEN REPEAT STRIP_TAC THEN fs [],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"a1"``)
		     THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"ctrl"``)
		     THEN FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``"b1"``)
		     THEN Cases_on `s "a1"` THEN Cases_on `s' "a1"`
		     THEN Cases_on `s "b1"` THEN Cases_on `s' "b1"`
		     THEN Cases_on `s "ctrl"` THEN Cases_on `s' "ctrl"`
		     THEN fs [Not_def, And_def, Or_def, lub_def]
		     THEN RW_TAC std_ss [] THEN
		     EQ_TAC THEN REPEAT STRIP_TAC THEN fs []]);



(*********************** E X A M P L E S *******************************)


(* Example I *)
val a0 = (T, "a0", T, 0, 1);
val a1 = (T, "a1", T, 0, 1);
val b0 = (T, "b0", F, 0, 1);
val b1 = (T, "b1", F, 0, 1);

val ctrl = (T, "ctrl", T, 0, 1);

val out0 = (T, "out0", T, 1, 2);
val out1 = (T, "out1", T, 1, 2);

val A  =  TF [ctrl, a0, a1, b0, b1];
val C  =  TF [out0, out1] ;

(* Running the STE simulator *)
val MUX_STE_IMPL1 = STE A C ``Mux_lattice`` comp_list true;

(* STE TO BOOL *)
val MUX_STE_BOOL1 =
    STE_TO_BOOL A C ``Mux_lattice`` ``Mux_bool``
    MUX_OK MUX_MONOTONIC MUX_STE_IMPL1;

CONV_RULE(EVAL) MUX_STE_BOOL1;

(* Example II *)

val a0 = (T, "a0", ``va0:bool``, 0, 1);
val a1 = (T, "a1", ``va1:bool``, 0, 1);
val b0 = (T, "b0", ``vb0:bool``, 0, 1);
val b1 = (T, "b1", ``vb1:bool``, 0, 1);
val ctrl = (T, "ctrl", T, 0, 1);
val out0 = (T, "out0", ``va0:bool``, 1, 2);
val out1 = (T, "out1", ``va1:bool``, 1, 2);
val A  =  TF [ctrl,a0,a1,b0,b1];
val C  =  TF [out0, out1] ;

(* Running the STE simulator *)
val MUX_STE_IMPL2 = STE A C ``Mux_lattice`` comp_list true;

(* STE TO BOOL *)
val MUX_STE_BOOL2 =
    STE_TO_BOOL A C ``Mux_lattice`` ``Mux_bool``
    MUX_OK MUX_MONOTONIC MUX_STE_IMPL2;

CONV_RULE(EVAL) MUX_STE_BOOL2;


(* Example III *)

val a0 = (T, "a0", ``va0:bool``, 0, 1);
val a1 = (T, "a1", ``va1:bool``, 0, 1);
val b0 = (T, "b0", ``vb0:bool``, 0, 1);
val b1 = (T, "b1", ``vb1:bool``, 0, 1);
val ctrl = (T, "ctrl", ``ctrl:bool``, 0, 1);

val out0 = (T, "out0", ``(va0 /\ ctrl) \/ (vb0 /\ (~ctrl))``, 1, 2);
val out1 = (T, "out1", ``(va1 /\ ctrl) \/ (vb1 /\ (~ctrl))``, 1, 2);
val A  =  TF [ctrl,a0,a1,b0,b1] ;
val C  =  TF [out0, out1];
val A  =  TF [ctrl,a0,a1,b0,b1];
val C  =  TF [out0, out1] ;

(* Running the STE simulator *)
val MUX_STE_IMPL3 = STE A C ``Mux_lattice`` comp_list true;

(* STE TO BOOL *)
val MUX_STE_BOOL3 =
    STE_TO_BOOL A C ``Mux_lattice`` ``Mux_bool``
    MUX_OK MUX_MONOTONIC MUX_STE_IMPL3;

CONV_RULE(EVAL) MUX_STE_BOOL3;
