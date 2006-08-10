(* ========================================================================= *)
(* Aaron R. Coble							     *)
(* aaron.coble@gmail.com						     *)
(*									     *)
(* Create "simpledcScript"                   		    	             *)
(* A proof of the simple ring-based dining cryptographers problem            *)
(* generalized for n cryptographers					     *)
(*									     *)
(* !!!!!!!!!!!!!!!!!!!!!!!! Proof still in progress !!!!!!!!!!!!!!!!!!!!!!!! *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib", "wpTheory", "valueTheory", "arithmeticTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory wpTheory valueTheory arithmeticTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "simpledc"                                         *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "simpledc";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = I prove;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions                                                       *)
(* ------------------------------------------------------------------------- *)

(* ---------------- Creates a list of the Ints 0 through n ----------------- *)

val zero_to_n_Int_list = Define
   `(zero_to_n_Int_list 0 = []) /\
    (zero_to_n_Int_list (SUC n) = SNOC (Int (&n)) (zero_to_n_Int_list n))`;

(* ------------------- Computes the xor of a value list ------------------- *)

val xor_def = Define
  `(xor [] = Int 0) /\
   (xor ((Int i)::l) = if i=0 then xor l else Int(1 - (int_of_value(xor l))))`;

(* ----------------- Computes the xor values in an array ------------------ *)

val Xor_def = Define
  `Xor (Array a) = xor a`;

(* ------------------------------------------------------------------------- *)
(* Defining heads and tails and yes and no                                   *)
(* ------------------------------------------------------------------------- *)

val Heads_def = Define `Heads = Int 1`;

val Tails_def = Define `Tails = Int 0`;

val Yes_def = Define `Yes = Int 1`;

val No_def = Define `No = Int 0`;

(* ------------------------------------------------------------------------- *)
(* Protocol Definition                                                       *)
(* ------------------------------------------------------------------------- *)

val initialize_var_N_def = Define
   `initialize_var_N n = Assign "N" (\s. Int (&n))`;

val set_payer_def = Define
  `set_payer n =
	Demonchoice "payer" (zero_to_n_Int_list (SUC n))`;

val initialize_def = Define
  `initialize n = Program [initialize_var_N n; set_payer n]`;

val flip_coins_def = Define
   `flip_coins =
	Program
	[
	  New_Array "Coins" "N";
	  For_0_to_n "i" "N"
	   [
	   	Probchoice "coinflip" [Heads; Tails];
	   	Assign_Array_i "Coins" "i" (\s. s "coinflip")
	   ]
	]`;

val set_announcements_def = Define
   `set_announcements =
	Program
	[
	   New_Array "Announces" "N";
	   For_0_to_n "i" "N"
	   [
		Assign "currentcoin" (\s. get_Array_i (s "Coins") (num_of_value (s "i")));
		If (\s. (num_of_value (s "i")) = 0) 
		   (Assign "previouscoin" (\s. get_Array_i (s "Coins") (num_of_value(s "N")-1)))
		   (Assign "previouscoin" (\s. get_Array_i (s "Coins") ((num_of_value (s "i"))-1)));
		If (\s. s "i" = s "payer")
		   (Assign "pays" (\s. Yes))
		   (Assign "pays" (\s. No));
		Assign_Array_i "Announces" "i" (\s. xor [s "previouscoin"; s "currentcoin"; s "pays"])
	     ]
	]`;

val compute_result_def = Define
   `compute_result = Assign "result" (\s. Xor (s "Announces"))`;

val dcprog_def = Define
   `dcprog_def n =
	Program
	[
	   initialize n;
	   flip_coins;
	   set_announcements;
	   compute_result
	]`;

(* ------------------------------------------------------------------------- *)
(* Proofs                                                                    *)
(* ------------------------------------------------------------------------- *)

val zero_to_n_Int_list_length = store_thm
  ("zero_to_n_Int_list_length",
   ``!n. LENGTH (zero_to_n_Int_list n) = n``,
   Induct_on `n`
   ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH, LENGTH_SNOC]
);

val zero_to_n_Int_list_result = store_thm
  ("zero_to_n_Int_list_result",
   ``!n i. (n>0) /\ (i<n) ==> ((EL i (zero_to_n_Int_list n)) = (Int (&i)))``,
   Induct_on `n`
   >> RW_TAC arith_ss []
   ++ Cases_on `n`
   >> (Cases_on `i`
       ++ FULL_SIMP_TAC arith_ss [zero_to_n_Int_list, EL, SNOC, HD, TL])
   ++ REPEAT STRIP_TAC
   ++ FULL_SIMP_TAC arith_ss []
   ++ Q.ABBREV_TAC `x=SUC n'`
   ++ RW_TAC arith_ss [zero_to_n_Int_list]
   ++ Cases_on `i < x`
   >> RW_TAC arith_ss [zero_to_n_Int_list_length, EL_SNOC]
   ++ `i = x` by RW_TAC arith_ss []
   ++ `LENGTH (zero_to_n_Int_list x) = i` 
	   by RW_TAC arith_ss [zero_to_n_Int_list_length]
   ++ RW_TAC arith_ss [EL_LENGTH_SNOC]);

val zero_to_n_Int_list_contains_lem1 = store_thm
   ("zero_to_n_Int_list_contains_lem1",
    ``!x n.
        (x < n) ==> MEM (Int (&x)) (zero_to_n_Int_list n)``,
    REPEAT STRIP_TAC
    ++ Induct_on `n`
    ++ RW_TAC arith_ss [zero_to_n_Int_list, IS_EL_SNOC, INT_INJ]
    ++ Cases_on `x = n`
    ++ RW_TAC arith_ss []);

val zero_to_n_Int_list_contains_lem2 = store_thm
   ("zero_to_n_Int_list_contains_lem2",
    ``!x n.
        (MEM (Int (&x)) (zero_to_n_Int_list n)) ==> (x < n)``,
    REPEAT STRIP_TAC
    ++ RW_TAC arith_ss []
    ++ Induct_on `n`
    ++ RW_TAC std_ss [zero_to_n_Int_list, MEM]
    ++ RW_TAC std_ss []
    ++ Cases_on `MEM (Int (& x)) (zero_to_n_Int_list n)`
    ++ FULL_SIMP_TAC arith_ss [zero_to_n_Int_list, IS_EL_SNOC, INT_INJ]
    ++ `x = n` by RW_TAC arith_ss [INT_INJ]
    ++ RW_TAC arith_ss []);

val zero_to_n_Int_list_contains = store_thm
   ("zero_to_n_Int_list_contains",
    ``!x n. (MEM (Int (&x)) (zero_to_n_Int_list n)) = (x < n)``,
    PROVE_TAC [EQ_IMP_THM, zero_to_n_Int_list_contains_lem1, zero_to_n_Int_list_contains_lem2]);

val MEM_zero_to_n_Int_list_implies_Int = store_thm
  ("MEM_zero_to_n_Int_list_implies_Int",
   ``!x n. (MEM x (zero_to_n_Int_list n)) ==> (?i. x = (Int i))``,
   Induct_on `n`
   ++ RW_TAC std_ss [zero_to_n_Int_list, MEM, IS_EL_SNOC]
   ++ FULL_SIMP_TAC std_ss []);

val MEM_zero_to_n_Int_list_implies_ge_zero = store_thm
  ("MEM_zero_to_n_Int_list_implies_zero",
   ``!i n. MEM (Int i) (zero_to_n_Int_list n) ==> (0 <= i)``,
   REPEAT STRIP_TAC
   ++ Induct_on `n`
   ++ RW_TAC std_ss [MEM, zero_to_n_Int_list]
   ++ Cases_on `MEM (Int i) (zero_to_n_Int_list n)`
   >> RW_TAC std_ss []
   ++ FULL_SIMP_TAC arith_ss [IS_EL_SNOC, INT_OF_NUM, int_of_value_def]
   ++ Cases_on `n`
   ++ RW_TAC arith_ss []
   ++ RW_TAC arith_ss [INT_LE_REFL, INT_LE]);

val zero_to_n_Int_list_contains_Int = store_thm
  ("zero_to_n_Int_list_contains_Int",
   ``!x n. MEM x (zero_to_n_Int_list n) ==> (num_of_value x < n)``,
   REPEAT GEN_TAC
   ++ `(MEM (Int (& (num_of_value x))) (zero_to_n_Int_list n)) ==> 
	((num_of_value x) < n)` 
   by METIS_TAC [zero_to_n_Int_list_contains_lem2]
   ++ `MEM x (zero_to_n_Int_list n) ==> MEM (Int (& (num_of_value x))) (zero_to_n_Int_list n)` by
	(`((MEM x (zero_to_n_Int_list n)) /\ 
          (x = (Int (& (num_of_value x))))) ==> 
		(MEM (Int (& (num_of_value x))) (zero_to_n_Int_list n))` 
	 by METIS_TAC []
	 ++ `(MEM x (zero_to_n_Int_list n) /\ ?i. x = Int i) ==> 
		((MEM x (zero_to_n_Int_list n)) /\ 
		(x = (Int (& (num_of_value x)))))` 
	     by (REPEAT STRIP_TAC
    	     ++ RW_TAC arith_ss [num_of_value_def, INT_OF_NUM, int_of_value_def]
    	     ++ METIS_TAC [MEM_zero_to_n_Int_list_implies_ge_zero])
	 ++ `(MEM x (zero_to_n_Int_list n)) ==> 
		((MEM x (zero_to_n_Int_list n)) /\ 
		(?i. x = Int i))` 
	 by METIS_TAC [MEM_zero_to_n_Int_list_implies_Int]
	 ++ METIS_TAC [])
   ++ METIS_TAC []);

val initialize_var_N_term = store_thm
  ("initialize_var_N_term",
   ``!n. (wp (initialize_var_N n) One) = One``,
    RW_TAC std_ss [initialize_var_N_def, wp_def, One_def]);

val initialize_var_N_result = store_thm
  ("initialize_var_N_result",
   ``!n. (wp (initialize_var_N n) (\s. if ((num_of_value(s"N")) = n) then 1 else 0)) = One``,
   RW_TAC std_ss [initialize_var_N_def, wp_def, assign_def, One_def, num_of_value_def, int_of_value_def, NUM_OF_INT]);

val initialize_var_N_result2 = store_thm
  ("initialize_var_N_result2",
   ``!n. (wp (initialize_var_N n) (\s. if (s"N" = Int(&n)) then 1 else 0)) = One``,
   RW_TAC std_ss [initialize_var_N_def, wp_def, assign_def, One_def]);

val seq_term = store_thm
  ("seq_term",
  ``!a b. ((wp a One) = One) /\ ((wp b One) = One) ==> ((wp (Seq a b) One) = One)``,
  RW_TAC std_ss [wp_def]);

val demon_term = store_thm
  ("demon_term",
   ``!a b. ((wp a One) = One) /\ ((wp b One) = One) ==> ((wp (Demon a b) One) = One)``,
   RW_TAC posreal_ss [wp_def, Min_def, One_def]);

val Demonchoice_term = store_thm
  ("Demonchoice_term",
   ``!v l. ((LENGTH l) > 0) ==> ((wp (Demonchoice v l) One) = One)``,
   RW_TAC std_ss [Demonchoice_def]
   ++ Induct_on `l`
   ++ RW_TAC arith_ss [LENGTH]
   ++ Cases_on `l`
   >> RW_TAC posreal_ss [MAP, Demons_def, wp_def, One_def, Min_def, min_def]
   ++ FULL_SIMP_TAC arith_ss [LENGTH]
   ++ Cases_on `t`
   ++ FULL_SIMP_TAC arith_ss [LENGTH, MAP, Demons_def]
   ++ MATCH_MP_TAC demon_term
   ++ RW_TAC posreal_ss [wp_def, One_def]);

val set_payer_term = store_thm
  ("set_payer_term",
   ``!n. (n > 0) ==> ((wp (set_payer n) One) = One)``,
   RW_TAC std_ss [set_payer_def]
   ++ MATCH_MP_TAC Demonchoice_term
   ++ RW_TAC arith_ss [zero_to_n_Int_list_length]);

val wp_1bounded_exp_is_1bounded = store_thm
  ("wp_1bounded_exp_is_1bounded",
   ``!prog e. (Leq e One) ==> (Leq (wp prog e) One)``,
   REPEAT STRIP_TAC
++ FULL_SIMP_TAC posreal_ss [Leq_def, One_def]
++ MATCH_MP_TAC healthy_bounded
++ RW_TAC posreal_ss [wp_healthy]);

val min_leq = store_thm
  ("min_leq",
   ``!e f g. Leq f e /\ Leq g e ==> Leq (Min f g) e``,
   RW_TAC real_ss [Leq_def, Min_def, preal_min_def]
   ++ Cases_on `f s <= g s`
   ++ RW_TAC posreal_ss []);

val strip_nested_min = store_thm
  ("strip_nested_min",
   ``!x y. min x (min x y) = min x y``,
   Cases_on `x <= y`
   ++ REPEAT STRIP_TAC
   ++ RW_TAC posreal_ss [preal_min_def]
   ++ FULL_SIMP_TAC posreal_ss []);

val Demonchoice_result = store_thm
  ("Demonchoice_result",
   ``!v l k. ((LENGTH l) > 0) ==>
	((wp (Demonchoice v l) (\s. if (MEM (s v) l) then 1 else 0)) = One) /\
	((?x y. (MEM x l) /\ (MEM y l) /\ (~(x=y))) ==>
	 	((wp (Demonchoice v l) (\s. if ((s v) = k) then 1 else 0)) = Zero))``,
   RW_TAC std_ss [Demonchoice_def]
   << [Induct_on `l`
   	++ RW_TAC arith_ss [LENGTH]
    	++ Cases_on `l`
    	>> RW_TAC posreal_ss [MAP, Demons_def, wp_def, assign_eta, One_def, MEM]
    	++ FULL_SIMP_TAC arith_ss [LENGTH, MAP, Demons_def, MEM]
    	++ RW_TAC posreal_ss [wp_def, assign_eta]
    	++ Q.ABBREV_TAC `prog = (Demons (Assign v (\s. h')::MAP (\x. Assign v (\s. x)) t))`
   	++ `Leq (wp prog (\s. (if (s v = h') \/ MEM (s v) t then 1 else 0)))
     		(wp prog (\s. (if (s v = h) \/ (s v = h') \/ MEM (s v) t then 1 else 0)))` by
		(MATCH_MP_TAC wp_mono
		++ RW_TAC posreal_ss [Leq_def]
		++ Cases_on `(s v = h') \/ MEM (s v) t`
		++ RW_TAC bool_ss []
		++ RW_TAC posreal_ss [leq_refl])
   	++ `Leq (wp prog (\s. (if (s v = h) \/ (s v = h') \/ MEM (s v) t then 1 else 0))) One` by
		(MATCH_MP_TAC wp_1bounded_exp_is_1bounded
		++ RW_TAC posreal_ss [Leq_def, One_def]
		++ Cases_on `(s v = h) \/ (s v = h') \/ MEM (s v) t`
		++ RW_TAC bool_ss []
		++ RW_TAC posreal_ss [leq_refl])
   	++ `Leq One (wp prog (\s. (if (s v = h) \/ (s v = h') \/ MEM (s v) t then 1 else 0)))` by
		METIS_TAC [leq_refl, leq_trans]
   	++ `(wp prog (\s. (if (s v = h) \/ (s v = h') \/ MEM (s v) t then 1 else 0))) = One` by 		METIS_TAC [leq_antisym]
   	++ RW_TAC posreal_ss [Min_def, One_def],
	Induct_on `l`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ Cases_on `l`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ Cases_on `t`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ FULL_SIMP_TAC posreal_ss [MAP, Demons_def, wp_def, assign_eta, Min_def, Zero_def]
	++ REPEAT STRIP_TAC 
	++ RW_TAC posreal_ss [strip_nested_min]
	++ FULL_SIMP_TAC posreal_ss []]);

val Demonchoice_do_nothing = store_thm
  ("Demonchoice_do_nothing",
   ``!v l e. (LENGTH l > 0) ==>
	        ((!a s. e s = e (assign v a s)) ==>
		   ((wp (Demonchoice v l) e) = e))``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss [Demonchoice_def]
   ++ Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   ++ Cases_on `l`
   << [RW_TAC std_ss [LENGTH, MAP, Demons_def, wp_def]
       ++ METIS_TAC [],
       FULL_SIMP_TAC posreal_ss [LENGTH, MAP, Demons_def, wp_def, Min_def]
       ++ METIS_TAC [min_refl]]);

val LESS_EQ_EQ_LESS_SUC = store_thm
  ("LESS_EQ_EQ_LESS_SUC",
   ``!n m. (n <= m) = (n < SUC m)``,
   RW_TAC arith_ss []);

val set_payer_result = store_thm
  ("set_payer_result",
   ``!n k. 
	(n>0) ==>
		(((wp (set_payer n) (\s.if ((num_of_value(s"payer")) <= n) then 1 else 0)) = One) /\
  		 ((wp (set_payer n) (\s.if (s"payer"=k) then 1 else 0)) = Zero))``,
   STRIP_TAC
   ++ STRIP_TAC
   ++ `((LENGTH (zero_to_n_Int_list (SUC n))) > 0) ==>
	((wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n))) 
             (\s. if (MEM (s "payer") (zero_to_n_Int_list (SUC n))) then 1 else 0)) = One) /\
	((?x y. (MEM x (zero_to_n_Int_list (SUC n))) /\ 
                (MEM y (zero_to_n_Int_list (SUC n))) /\ 
                (~(x=y))) ==>
	 	((wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n))) 
                     (\s. if ((s "payer") = k) then 1 else 0)) = Zero))` 
      by METIS_TAC [Demonchoice_result]
   ++ FULL_SIMP_TAC std_ss [zero_to_n_Int_list_length]
   ++ RW_TAC std_ss [set_payer_def]
   << [`(wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
            (\s. (if num_of_value (s "payer") <= n then 1 else 0))) =
        (wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
            (\s. (if num_of_value (s "payer") < SUC n then 1 else 0)))` 
       by RW_TAC arith_ss [LESS_EQ_EQ_LESS_SUC]
       ++ `Leq (\s. (if MEM (s "payer") (zero_to_n_Int_list (SUC n)) then 1 else 0))
               (\s. (if num_of_value (s "payer") < SUC n then 1 else 0))`
       by (RW_TAC posreal_ss [Leq_def]
           ++ Cases_on `MEM (s "payer") (zero_to_n_Int_list (SUC n))`
           ++ RW_TAC posreal_ss [zero_to_n_Int_list_contains_Int])
       ++ `Leq  (wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
                    (\s. (if MEM (s "payer") (zero_to_n_Int_list (SUC n)) then 1 else 0)))
                (wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
                    (\s. (if num_of_value (s "payer") < SUC n then 1 else 0)))` 
          by METIS_TAC [wp_mono]
       ++ `Leq One 
               (wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
                   (\s. (if num_of_value (s "payer") <= n then 1 else 0)))` 
          by METIS_TAC []
       ++ `Leq (\s. (if num_of_value (s "payer") <= n then 1 else 0)) One`
          by (RW_TAC posreal_ss [Leq_def, One_def]
              ++ Cases_on `num_of_value (s "payer") <= n`
              ++ RW_TAC posreal_ss [])
       ++ `Leq (wp (Demonchoice "payer" (zero_to_n_Int_list (SUC n)))
                   (\s. (if num_of_value (s "payer") <= n then 1 else 0)))
               One` 
          by METIS_TAC [wp_1bounded_exp_is_1bounded]
       ++ METIS_TAC [leq_antisym],
       `(?x y. MEM x (zero_to_n_Int_list (SUC n)) /\
               MEM y (zero_to_n_Int_list (SUC n)) /\ 
               ~(x = y))`
       by (`MEM (Int (&0)) (zero_to_n_Int_list (SUC n))` 
           by RW_TAC arith_ss [zero_to_n_Int_list_contains]
           ++ `MEM (Int (&1)) (zero_to_n_Int_list (SUC n))` 
           by RW_TAC arith_ss [zero_to_n_Int_list_contains]
           ++  `~((Int 0) = (Int 1))` 
           by RW_TAC int_ss []
           ++ METIS_TAC [])
       ++ METIS_TAC []]);

val initialize_term = store_thm
  ("initialize_term",
   ``!n. (n > 0) ==> ((wp (initialize n) One) = One)``,
   RW_TAC std_ss [initialize_def, Program_def]
   ++ METIS_TAC [seq_term, initialize_var_N_term, set_payer_term]);

(*
val initialize_result = store_thm
  ("initialize_result",
   ``!n k. (n > 0) ==> 
	((wp (initialize n) 
	     (\s.if ((num_of_value(s"N")) = n) then 1 else 0)) = One) /\
	((wp (initialize n) 
             (\s.if ((0<=(num_of_value(s"payer")))/\((num_of_value(s"payer"))<=n)) then 1 else 0)) = One) /\
	((wp (initialize n) 
 	     (\s.if ((num_of_value(s"payer"))=k) then 1 else 0)) = Zero)``,
   ????);

val set_announcements_term = store_thm
  ("set_announcements_term",
   ``((wp set_announcements One) (\s. if ((s"N" = 0) \/ (s"N" > 0)) then 1 else 0)) = 1``,
   ????);

val set_announcements_result = store_thm
  ("set_announcements_result",
   ``!k. ((k>0) \/ (k=0)) ==>
	((((wp set_announcements (\s. if (((get_Array_i (s"Coins") k) = Heads) \/   
					  ((get_Array_i (s"Coins") k) = Heads)) then 1 else 0))
	  (\s. if ((k<s"N")\/(k=s"N")) then 1 else 0)) = 1) /\
	(((wp set_announcements (\s. if ((get_Array_i (s"Coins") k) = Heads) then 1 else 0))
	  (\s. if ((k<s"N")\/(k=s"N")) then 1 else 0)) = 0.5) /\
	(((wp set_announcements (\s. if ((get_Array_i (s"Coins") k) = Tails) then 1 else 0))
	  (\s. if ((k<s"N")\/(k=s"N")) then 1 else 0)) = 0.5))``,
   ????);
*)

val _ = export_theory();