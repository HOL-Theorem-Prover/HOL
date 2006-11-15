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
   "metisLib","posrealLib","expectationTheory","intLib", "wpTheory", "valueTheory", "arithmeticTheory",
   "stringLib", "looprulesTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib stringLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory wpTheory valueTheory arithmeticTheory looprulesTheory;

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

val initialize_var_NSApays_def = Define
   `initialize_var_NSApays nsapays = 
	if nsapays then Assign "NSApays" (\s. Yes)
	           else Assign "NSApays" (\s. No)`;

val set_payer_def = Define
  `set_payer n nsapays =
	if nsapays then Assign "payer" (\s. Int (&n))
		   else NondetAssign "payer" (zero_to_n_Int_list n)`;

val initialize_def = Define
  `initialize n nsapays = Program [initialize_var_N n; 
                                   initialize_var_NSApays nsapays; 
                                   set_payer n nsapays]`;

val flip_coins_def = Define
   `flip_coins =
	Program
	[
	  New_Array "Coins" "N";
	  For_0_to_n "i" "N"
	   [
	   	ProbAssign "coinflip" [Heads; Tails];
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
   `dcprog n nsapays =
	Program
	[
	   initialize n nsapays;
	   flip_coins;
	   set_announcements;
	   compute_result
	]`;

(* ------------------------------------------------------------------------- *)
(* Proofs                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ----------------- zero_to_n_Int_list proofs ----------------------------- *)

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

(* ------------------- initialize_var_N proofs ----------------------------- *)

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

(* ------------------- initialize_var_NSApays proofs ----------------------- *)

val initialize_var_NSApays_term = store_thm
  ("initialize_var_NSApays_term",
   ``!nsapays. (wp (initialize_var_NSApays nsapays) One) = One``,
    RW_TAC std_ss [initialize_var_NSApays_def, wp_def, One_def]);

val initialize_var_NSApays_result = store_thm
  ("initialize_var_NSApays_result",
   ``!nsapays. (wp (initialize_var_NSApays nsapays) 
		   (\s. if nsapays then
				(if (s "NSApays") = Yes then 1 else 0)
			else
				(if (s "NSApays") = No then 1 else 0))) = One``,
   RW_TAC std_ss [initialize_var_NSApays_def, wp_def, assign_def, 
                  Yes_def, No_def, One_def, num_of_value_def, 
		  int_of_value_def, NUM_OF_INT]);

(* ------------------------- general arithmetic proof ---------------------- *)

val LESS_EQ_EQ_LESS_SUC = store_thm
  ("LESS_EQ_EQ_LESS_SUC",
   ``!n m. (n <= m) = (n < SUC m)``,
   RW_TAC arith_ss []);

val posreal_of_SUC = store_thm
  ("posreal_of_SUC",
   ``(&(SUC n)) = (& n) + (1:posreal)``,
   RW_TAC posreal_ss [posreal_of_num_inj]);

val subr1_inv_eq_zero = store_thm
  ("subr1_inv_eq_zero",
   ``!x. (1 - inv x = 0) = (x < 1 \/ (x = 1))``,
   `!x. ((x < 1) \/ (inv x = 1)) ==> (1 - inv x = 0)`
	by (RW_TAC posreal_ss []
	    >> (SPOSE_NOT_THEN STRIP_ASSUME_TAC
	    	++ `~(1 - inv x <= 0)` by RW_TAC posreal_ss [le_zero]
	    	++ `~(1=infty)` by RW_TAC posreal_ss []
	    	++ `~(1 <= 0 + inv x)` by METIS_TAC [sub_le_eq]
	    	++  FULL_SIMP_TAC std_ss [add_lzero, inv_one_le]
	   	 ++ METIS_TAC [le_total, preal_lt_def])
	    ++ RW_TAC posreal_ss [])
   ++ `!x. (1 - inv x = 0) ==> ((x < 1) \/ (inv x = 1))`
	by (RW_TAC posreal_ss []
	    ++ `1 - inv x <= 0` by RW_TAC posreal_ss [le_zero]
	    ++ `~(1=infty)` by RW_TAC posreal_ss []
	    ++ `1 <= 0 + inv x` by METIS_TAC [sub_le_eq]
	    ++  FULL_SIMP_TAC std_ss [add_lzero, inv_one_le]
	    ++ METIS_TAC [preal_lt_def, le_total, le_antisym])
   ++ FULL_SIMP_TAC posreal_ss []
   ++ METIS_TAC []);

val bound1_eq_lemma = store_thm
  ("bound1_eq_lemma",
   ``!x y. (~(y=infty)) ==> ((bound1 x) * y + (1 - bound1 x) * y = y)``,
   RW_TAC posreal_ss [bound1_def, sub_rdistrib, sub_add2]
   ++ `1 < infty` by RW_TAC posreal_ss [preal_lt_def]
   ++ `~(x = infty)` by METIS_TAC [let_trans, infty_le, preal_lt_def]
   ++ `~(x*y = infty)` by METIS_TAC [mul_eq_infty]
   ++ METIS_TAC [sub_add2, le_refl, operand_le_one_imp_mul_le_one]);

(* -------------------------- general wp proofs ---------------------------- *)

val seq_term = store_thm
  ("seq_term",
  ``!a b. ((wp a One) = One) /\ ((wp b One) = One) ==> ((wp (Seq a b) One) = One)``,
  RW_TAC std_ss [wp_def]);

val Nondet_term = store_thm
  ("Nondet_term",
   ``!a b. ((wp a One) = One) /\ ((wp b One) = One) ==> ((wp (Nondet a b) One) = One)``,
   RW_TAC posreal_ss [wp_def, Min_def, One_def]);

val wp_1bounded_exp_is_1bounded = store_thm
  ("wp_1bounded_exp_is_1bounded",
   ``!prog e. (Leq e One) ==> (Leq (wp prog e) One)``,
   REPEAT STRIP_TAC
++ FULL_SIMP_TAC posreal_ss [Leq_def, One_def]
++ MATCH_MP_TAC healthy_bounded
++ RW_TAC posreal_ss [wp_healthy]);

val strip_nested_min = store_thm
  ("strip_nested_min",
   ``!x y. min x (min x y) = min x y``,
   Cases_on `x <= y`
   ++ REPEAT STRIP_TAC
   ++ RW_TAC posreal_ss [preal_min_def]
   ++ FULL_SIMP_TAC posreal_ss []);

val NondetAssign_term = store_thm
  ("NondetAssign_term",
   ``!v l. ((LENGTH l) > 0) ==> ((wp (NondetAssign v l) One) = One)``,
   RW_TAC std_ss [NondetAssign_def]
   ++ Induct_on `l`
   ++ RW_TAC arith_ss [LENGTH]
   ++ Cases_on `l`
   >> RW_TAC posreal_ss [MAP, Nondets_def, wp_def, One_def, Min_def, min_def]
   ++ FULL_SIMP_TAC arith_ss [LENGTH]
   ++ Cases_on `t`
   ++ FULL_SIMP_TAC arith_ss [LENGTH, MAP, Nondets_def]
   ++ MATCH_MP_TAC Nondet_term
   ++ RW_TAC posreal_ss [wp_def, One_def]);

val NondetAssign_repeat_list = store_thm
  ("NondetAssign_repeat_list",
``!v (l:'a list) (x:'a). (!x'. (MEM x' l) ==> (x' = x)) /\
	 (LENGTH l > 0) ==>
	 (wp (NondetAssign v l) = wp (NondetAssign v [x]))``,
   REPEAT STRIP_TAC
   ++ Induct_on `l`
   ++ RW_TAC std_ss [LENGTH]
   ++ Cases_on `l`
   >> (`h=x` by METIS_TAC [MEM]
       ++ ASM_REWRITE_TAC [])
   ++ FULL_SIMP_TAC std_ss [LENGTH]
   ++ `!x'. (MEM x' (h'::t)) ==> (x' = x)`
	by METIS_TAC [MEM]
   ++ FULL_SIMP_TAC std_ss [NondetAssign_def, MAP, Nondets_def]
   ++ SIMP_TAC std_ss [wp_def]
   ++ `h = x` by METIS_TAC [MEM]
   ++ ASM_REWRITE_TAC []
   ++ SIMP_TAC std_ss [wp_def, FUN_EQ_THM, refl_min]);

val NondetAssign_of_singleton_Leq = store_thm
  ("NondetAssign_of_singleton_Leq",
   ``!v k (l:'a list) (x:'a). (MEM x l) ==>
	Leq (wp (NondetAssign v l) (\s. if ~(s v = k) then 1 else 0))
	    (wp (NondetAssign v [x])(\s. if ~(s v = k) then 1 else 0))``,
   REPEAT STRIP_TAC
   ++ Induct_on `l`
   >> RW_TAC std_ss [MEM]
   ++ RW_TAC std_ss [MEM]
   >> (Cases_on `l`
       >> SIMP_TAC std_ss [leq_refl]
       ++ FULL_SIMP_TAC std_ss [NondetAssign_def, MAP, Nondets_def, wp_def, Leq_def]
       ++ RW_TAC posreal_ss [Min_def, preal_min_def]
       ++ `expect1 (\(s:string->'a). (if ~(s v = k) then (1:posreal) else 0))` 
   	by (RW_TAC posreal_ss [expect1_def]
   	    ++ RW_TAC posreal_ss [zero_le, le_refl])
       ++ `expect1 (wp (Nondets (Assign v (\s. h')::MAP (\x. Assign v (\s. x)) t))
      		       (\s. (if ~(s v = k) then 1 else 0)))`
	by METIS_TAC [expect1_postE_imp_expect1_wp_postE]
       ++ FULL_SIMP_TAC std_ss [expect1_def])
   ++ Cases_on `l`
   >> FULL_SIMP_TAC std_ss [MEM]
   ++ FULL_SIMP_TAC std_ss [NondetAssign_def, MAP, Nondets_def, wp_def, Leq_def]
   ++ RW_TAC posreal_ss [Min_def, preal_min_def]
   << [FULL_SIMP_TAC std_ss [assign_eta]
       ++ `~((1:posreal) <= 0)` by RW_TAC posreal_ss []
       ++ METIS_TAC [le_trans],
       `expect1 (\(s:string->'a). (if ~(s v = k) then (1:posreal) else 0))` 
		by (RW_TAC posreal_ss [expect1_def]
		    ++ RW_TAC posreal_ss [zero_le, le_refl])
       ++ `expect1 (wp (Nondets (Assign v (\s. h')::MAP (\x. Assign v (\s. x)) t))
      		       (\s. (if ~(s v = k) then 1 else 0)))`
		by METIS_TAC [expect1_postE_imp_expect1_wp_postE]
       ++ FULL_SIMP_TAC std_ss [expect1_def],
       FULL_SIMP_TAC std_ss [assign_eta, le_zero]]);

val NondetAssign_partial_result = store_thm
  ("NondetAssign_partial_result",
   ``!v l k. ((LENGTH l) > 0) ==>
	((wp (NondetAssign v l) (\s. if (MEM (s v) l) then 1 else 0)) = One) /\
	((?x y. (MEM x l) /\ (MEM y l) /\ (~(x=y))) ==>
	 	((wp (NondetAssign v l) (\s. if ((s v) = k) then 1 else 0)) = Zero))``,
   RW_TAC std_ss [NondetAssign_def]
   << [Induct_on `l`
   	++ RW_TAC arith_ss [LENGTH]
    	++ Cases_on `l`
    	>> RW_TAC posreal_ss [MAP, Nondets_def, wp_def, assign_eta, One_def, MEM]
    	++ FULL_SIMP_TAC arith_ss [LENGTH, MAP, Nondets_def, MEM]
    	++ RW_TAC posreal_ss [wp_def, assign_eta]
    	++ Q.ABBREV_TAC `prog = (Nondets (Assign v (\s. h')::MAP (\x. Assign v (\s. x)) t))`
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
	++ FULL_SIMP_TAC posreal_ss [MAP, Nondets_def, wp_def, assign_eta, Min_def, Zero_def]
	++ REPEAT STRIP_TAC 
	++ RW_TAC posreal_ss [strip_nested_min]
	++ FULL_SIMP_TAC posreal_ss []]);

val NondetAssign_result = store_thm
  ("NondetAssign_result",
   ``!v l k. ((LENGTH l) > 0) ==>
	((wp (NondetAssign v l) (\s. if (MEM (s v) l) then 1 else 0)) = One) /\
	((?x y. (MEM x l) /\ (MEM y l) /\ (~(x=y))) ==>
	 	((wp (NondetAssign v l) (\s. if ((s v) = k) then 1 else 0)) = Zero) /\
                ((MEM k l) ==> ((wp (NondetAssign v l) (\s. if ~((s v) = k) then 1 else 0)) = Zero)))``,
   RW_TAC std_ss []
   << [RW_TAC std_ss [NondetAssign_def]
	++ Induct_on `l`
   	++ RW_TAC arith_ss [LENGTH]
    	++ Cases_on `l`
    	>> RW_TAC posreal_ss [MAP, Nondets_def, wp_def, assign_eta, One_def, MEM]
    	++ FULL_SIMP_TAC arith_ss [LENGTH, MAP, Nondets_def, MEM]
    	++ RW_TAC posreal_ss [wp_def, assign_eta]
    	++ Q.ABBREV_TAC `prog = (Nondets (Assign v (\s. h')::MAP (\x. Assign v (\s. x)) t))`
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
   	++ `(wp prog (\s. (if (s v = h) \/ (s v = h') \/ MEM (s v) t then 1 else 0))) = One` by 		
	 	METIS_TAC [leq_antisym]
   	++ RW_TAC posreal_ss [Min_def, One_def],
	RW_TAC std_ss [NondetAssign_def]
	++ Induct_on `l`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ Cases_on `l`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ Cases_on `t`
	++ FULL_SIMP_TAC arith_ss [LENGTH, MEM]
	++ FULL_SIMP_TAC posreal_ss [MAP, Nondets_def, wp_def, assign_eta, Min_def, Zero_def]
	++ REPEAT STRIP_TAC 
	++ RW_TAC posreal_ss [strip_nested_min]
	++ FULL_SIMP_TAC posreal_ss [],
	Suff `Leq (wp (NondetAssign v l) (\s. (if ~(s v = k) then 1 else 0)))
		   Zero`
	>> METIS_TAC [leq_zero]
	++ `Leq (wp (NondetAssign v l) (\s. if ~(s v = k) then 1 else 0))
	    	(wp (NondetAssign v [k])(\s. if ~(s v = k) then 1 else 0))`
		by METIS_TAC [NondetAssign_of_singleton_Leq]
	++ FULL_SIMP_TAC std_ss [NondetAssign_def, MAP, wp_def, assign_eta, Nondets_def, Zero_def]
	++ RW_TAC posreal_ss []]);

val NondetAssign_do_nothing = store_thm
  ("NondetAssign_do_nothing",
   ``!v l e. (LENGTH l > 0) ==>
	        ((!a s. e s = e (assign v a s)) ==>
		   ((wp (NondetAssign v l) e) = e))``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss [NondetAssign_def]
   ++ Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   ++ Cases_on `l`
   << [RW_TAC std_ss [LENGTH, MAP, Nondets_def, wp_def]
       ++ METIS_TAC [],
       FULL_SIMP_TAC posreal_ss [LENGTH, MAP, Nondets_def, wp_def, Min_def]
       ++ METIS_TAC [min_refl]]);

val NondetAssign_do_nothing_val = store_thm
  ("NondetAssign_do_nothing_val",
   ``!v (l:value list) (e:(string->value)->posreal). (LENGTH l > 0) ==>
	        ((!a s. e s = e (assign v a s)) ==>
		   ((wp (NondetAssign v l) e) = e))``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss [NondetAssign_def]
   ++ Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   ++ Cases_on `l`
   << [RW_TAC std_ss [LENGTH, MAP, Nondets_def, wp_def]
       ++ METIS_TAC [],
       FULL_SIMP_TAC posreal_ss [LENGTH, MAP, Nondets_def, wp_def, Min_def]
       ++ METIS_TAC [min_refl]]);

val ProbAssign_do_nothing = store_thm
  ("ProbAssign_do_nothing",
   ``!v l e. (LENGTH l > 0) ==>
	        ((!a s. e s = e (assign v a s)) ==>
		   ((wp (ProbAssign v l) e) = e))``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss []
   ++ Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   ++ FULL_SIMP_TAC posreal_ss [LENGTH, MAP, ProbAssign_def, Probs_def, wp_def, lin_eta, FUN_EQ_THM, preal_div_def]
       ++ Cases_on `LENGTH l > 0`
       >> (FULL_SIMP_TAC std_ss [LENGTH]
	   ++ RW_TAC list_ss [MAP_MAP_o]
	   ++ RW_TAC posreal_ss [preal_div_def]
	   ++ `inv (& (SUC (LENGTH l))) *
               inv (1 - inv (& (SUC (LENGTH l)))) =
	       inv ((& (SUC (LENGTH l))) * (1 - inv (& (SUC (LENGTH l)))))`
		by (`~((& (SUC (LENGTH l)) * (1 - inv (& (SUC (LENGTH l))))) = (0:posreal))`
			by RW_TAC posreal_ss [entire, posreal_of_num_inj, 
					      subr1_inv_eq_zero, DE_MORGAN_THM]
		    ++ METIS_TAC [inv_mul])
	   ++ RW_TAC std_ss []
	   ++ POP_ASSUM (K ALL_TAC)
	   ++ `~ (& (SUC (LENGTH l)) = (0:posreal))`
		by RW_TAC arith_ss [posreal_of_num_inj]
	   ++ RW_TAC posreal_ss [sub_ldistrib, mul_rinv]
	   ++ `e (assign v (\s. h) x) = e x` by METIS_TAC []
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `x'`
	   ++ Cases_on `e x = infty`
	   >> (`~(bound1 (inv (& (SUC (LENGTH l)))) = 0)` by RW_TAC posreal_ss [bound1_def]
	       ++ RW_TAC posreal_ss [mul_rinfty, add_rinfty])
	   ++ METIS_TAC [bound1_eq_lemma])
	++ Cases_on `l`
	>> (RW_TAC posreal_ss [MAP, Probs_def, wp_def, Zero_def, mul_rzero, add_rzero]
	    ++ Q.UNABBREV_TAC `x'`
	    ++ RW_TAC posreal_ss [LENGTH])
	++ FULL_SIMP_TAC arith_ss [LENGTH]);

val ProbAssign_do_nothing_val = store_thm
  ("ProbAssign_do_nothing_val",
   ``!v l e. (LENGTH l > 0) ==>
	        ((!a (s:string->value). e s = e (assign v a s)) ==>
		   ((wp (ProbAssign v l) e) = e))``,
   REPEAT STRIP_TAC
   ++ RW_TAC std_ss []
   ++ Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   ++ FULL_SIMP_TAC posreal_ss [LENGTH, MAP, ProbAssign_def, Probs_def, wp_def, lin_eta, FUN_EQ_THM, preal_div_def]
       ++ Cases_on `LENGTH l > 0`
       >> (FULL_SIMP_TAC std_ss [LENGTH]
	   ++ RW_TAC list_ss [MAP_MAP_o]
	   ++ RW_TAC posreal_ss [preal_div_def]
	   ++ `inv (& (SUC (LENGTH l))) *
               inv (1 - inv (& (SUC (LENGTH l)))) =
	       inv ((& (SUC (LENGTH l))) * (1 - inv (& (SUC (LENGTH l)))))`
		by (`~((& (SUC (LENGTH l)) * (1 - inv (& (SUC (LENGTH l))))) = (0:posreal))`
			by RW_TAC posreal_ss [entire, posreal_of_num_inj, 
					      subr1_inv_eq_zero, DE_MORGAN_THM]
		    ++ METIS_TAC [inv_mul])
	   ++ RW_TAC std_ss []
	   ++ POP_ASSUM (K ALL_TAC)
	   ++ `~ (& (SUC (LENGTH l)) = (0:posreal))`
		by RW_TAC arith_ss [posreal_of_num_inj]
	   ++ RW_TAC posreal_ss [sub_ldistrib, mul_rinv]
	   ++ `e (assign v (\s. h) x) = e x` by METIS_TAC []
	   ++ RW_TAC std_ss []
	   ++ Q.UNABBREV_TAC `x'`
	   ++ Cases_on `e x = infty`
	   >> (`~(bound1 (inv (& (SUC (LENGTH l)))) = 0)` by RW_TAC posreal_ss [bound1_def]
	       ++ RW_TAC posreal_ss [mul_rinfty, add_rinfty])
	   ++ METIS_TAC [bound1_eq_lemma])
	++ Cases_on `l`
	>> (RW_TAC posreal_ss [MAP, Probs_def, wp_def, Zero_def, mul_rzero, add_rzero]
	    ++ Q.UNABBREV_TAC `x'`
	    ++ RW_TAC posreal_ss [LENGTH])
	++ FULL_SIMP_TAC arith_ss [LENGTH]);
	   
(* -------------------------- set_payer proofs ----------------------------- *)

val set_payer_term = store_thm
  ("set_payer_term",
   ``!n nsapays. (n > 0) ==> ((wp (set_payer n nsapays) One) = One)``,
   RW_TAC std_ss [set_payer_def]
   >> RW_TAC posreal_ss [wp_def, One_def]
   ++ MATCH_MP_TAC NondetAssign_term
   ++ RW_TAC arith_ss [zero_to_n_Int_list_length]);

(* -------------------------- initialize proofs ---------------------------- *)

val initialize_term = store_thm
  ("initialize_term",
   ``!n. (n > 0) ==> ((wp (initialize n nsapays) One) = One)``,
   RW_TAC std_ss [initialize_def, Program_def]
   ++ METIS_TAC [seq_term, initialize_var_N_term, initialize_var_NSApays_term, set_payer_term]);

val initialize_result = store_thm
  ("initialize_result",
   ``!n nsapays k. (n > 0) ==>
	((wp (initialize n nsapays) (\s. if ((num_of_value (s "N")) = n) then 1 else 0) = One) /\
	 (wp (initialize n nsapays) (\s. if nsapays 
					 then (if ((s "NSApays") = Yes) then 1 else 0)								 else (if ((s "NSApays") = No) then 1 else 0)) = One) /\
	 (if nsapays
	  then (wp (initialize n nsapays) (\s. if ((s "payer") = (s "N")) then 1 else 0) = One)
	  else 
	  ((wp (initialize n nsapays) 
	       (\s. if ((num_of_value (s "payer")) < 
		        (num_of_value (s "N"))) then 1 else 0) = One)
	    /\ ((n > 1) ==> ((wp (initialize n nsapays)
			         (\s. if (s "payer") = Int (& k) then 1 else 0) = Zero)
	    		     /\ ( (k < n) ==>
				(wp (initialize n nsapays)
				    (\s. if ~ ((s "payer") = Int (& k)) 
					 then 1 else 0) = Zero)))))))``,
   REPEAT STRIP_TAC
   << [RW_TAC std_ss [initialize_def, Program_def, wp_def, set_payer_def, 
		   initialize_var_NSApays_def, assign_eta]
    >> RW_TAC posreal_ss [initialize_var_N_result]
    ++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
	   (\s. (if num_of_value (s "N") = n then 1 else 0)) =
	   (\s. (if num_of_value (s "N") = n then 1 else 0))`
	by (`LENGTH (zero_to_n_Int_list n) > 0`
		by (Cases_on `n`
	    	    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
	    ++ `!(n:num). (n > 0) ==>
		(?(l:value list). l = zero_to_n_Int_list n)`
		by (Induct_on `n`
	    	    ++ RW_TAC arith_ss [])
	    ++ `?l. zero_to_n_Int_list n = l` by METIS_TAC []
	    ++ `LENGTH l > 0` by RW_TAC arith_ss []
	    ++ ASM_REWRITE_TAC []
	    ++ `!a s. (\s. (if num_of_value (s "N") = n then (1:posreal) else 0)) s =
		      (\s. (if num_of_value (s "N") = n then 1 else 0))
		      (assign "payer" a s)` 
		by RW_TAC std_ss [assign_eta]
	    ++ `!(v :string) (l :value list) (e :(string -> value) -> posreal).
         	 LENGTH l > (0 :num) ==>
         	 (!(a :(string -> value) -> value) (s :string -> value).
          	 e s = e (assign v a s)) ==>
         	(wp (NondetAssign v l) e = e)` 
		by METIS_TAC [NondetAssign_do_nothing_val]
	    ++ FULL_SIMP_TAC std_ss [])
    ++ RW_TAC std_ss [initialize_var_N_result],
    RW_TAC std_ss [initialize_def, Program_def, wp_def, set_payer_def, assign_eta]
    >> (`wp (initialize_var_NSApays T)
              		(\s. (if T then
                    		(if s "NSApays" = Yes then 1 else 0)
                  	      else
                    		(if s "NSApays" = No then 1 else 0))) = One`
			by METIS_TAC [Q.SPECL [`T`] initialize_var_NSApays_result]
	++ FULL_SIMP_TAC std_ss [initialize_var_N_term])
    ++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
	   (\s. (if s "NSApays" = No then 1 else 0)) =
	   (\s. (if s "NSApays" = No then 1 else 0))`
	by (`LENGTH (zero_to_n_Int_list n) > 0`
		by (Cases_on `n`
	    	    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
	    ++ `!(n:num). (n > 0) ==>
		(?(l:value list). l = zero_to_n_Int_list n)`
		by (Induct_on `n`
	    	    ++ RW_TAC arith_ss [])
	    ++ `?l. zero_to_n_Int_list n = l` by METIS_TAC []
	    ++ `LENGTH l > 0` by RW_TAC arith_ss []
	    ++ ASM_REWRITE_TAC []
	    ++ `!a s. (\s. (if s "NSApays" = No then (1:posreal) else 0)) s =
		      (\s. (if s "NSApays" = No then 1 else 0))
		      (assign "payer" a s)` 
		by RW_TAC std_ss [assign_eta]
	    ++ `!(v :string) (l :value list) (e :(string -> value) -> posreal).
         	 LENGTH l > (0 :num) ==>
         	 (!(a :(string -> value) -> value) (s :string -> value).
          	 e s = e (assign v a s)) ==>
         	(wp (NondetAssign v l) e = e)` 
		by METIS_TAC [NondetAssign_do_nothing_val]
	    ++ FULL_SIMP_TAC std_ss [])
    ++ ASM_REWRITE_TAC []
    ++ POP_ASSUM (K ALL_TAC)
    ++ `wp (initialize_var_NSApays F)
           (\s. (if F then
                    (if s "NSApays" = Yes then 1 else 0)
                 else
                    (if s "NSApays" = No then 1 else 0))) = One`
	by METIS_TAC [Q.SPECL [`F`] initialize_var_NSApays_result]
    ++ FULL_SIMP_TAC std_ss [initialize_var_N_term],
    RW_TAC std_ss []
    << [RW_TAC posreal_ss [initialize_def, Program_def, wp_def, set_payer_def, assign_eta,
			   initialize_var_NSApays_def, initialize_var_N_def, One_def],
 	RW_TAC posreal_ss [initialize_def, Program_def, wp_def, set_payer_def, assign_eta, 
			   initialize_var_NSApays_def, initialize_var_N_def]
	++ `Leq (\s. (if n = num_of_value (s "N") then 1 else 0))
		(wp (NondetAssign "payer" (zero_to_n_Int_list n))
	    	    (\s. (if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0)))`
		by (`Leq (wp (NondetAssign "payer" (zero_to_n_Int_list n))
	    		     (\s. (if n = num_of_value (s "N") then 1 else 0)))
			 (wp (NondetAssign "payer" (zero_to_n_Int_list n))
	    		     (\s. (if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0)))`
			by (`Leq (Conj (wp (NondetAssign "payer" (zero_to_n_Int_list n)) 
		  			   (\s. if (n = num_of_value (s "N")) then 1 else 0))
	      			       (wp (NondetAssign "payer" (zero_to_n_Int_list n))
		  			   (\s. if MEM (s "payer") (zero_to_n_Int_list n) then 1 else 0)))
				 (wp (NondetAssign "payer" (zero_to_n_Int_list n))
	    			     (\s. if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0))`
				by (`Leq (Conj (wp (NondetAssign "payer" (zero_to_n_Int_list n))
			   			   (\s. (if n = num_of_value (s "N") then 1 else 0)))
		       			       (wp (NondetAssign "payer" (zero_to_n_Int_list n))
			   			   (\s. (if MEM (s "payer") (zero_to_n_Int_list n) 
						         then 1 else 0))))
		 			 (wp (NondetAssign "payer" (zero_to_n_Int_list n))
		     			     (Conj (\s. if (n = num_of_value (s "N")) then 1 else 0)
	      		   			   (\s. if MEM (s "payer") (zero_to_n_Int_list n) 
							then (1:posreal) else 0)))`
					by METIS_TAC [wp_conj]
	    			    ++ Suff `Leq (wp (NondetAssign "payer" (zero_to_n_Int_list n))
		     	     			     (Conj (\s. if (n = num_of_value (s "N")) then 1 else 0)
	      		   	   			   (\s. if MEM (s "payer") (zero_to_n_Int_list n) 
								then (1:posreal) else 0)))
	    		 			 (wp (NondetAssign "payer" (zero_to_n_Int_list n))
	    		     			     (\s. if num_of_value (s "payer") < num_of_value (s "N") 
							  then 1 else 0))`
	    			    >> PROVE_TAC [leq_trans]
	    			    ++ POP_ASSUM (K ALL_TAC)
	    			    ++ MATCH_MP_TAC wp_mono
	    			    ++ `Leq (\s. if MEM (s "payer") 
						        (zero_to_n_Int_list (num_of_value (s "N"))) 
						 then 1 else 0)
        	    			    (\s. if num_of_value (s "payer") < num_of_value (s "N") 
						 then (1:posreal) else 0)`
					by (RW_TAC posreal_ss [Leq_def]
	    				    ++ RW_TAC posreal_ss [zero_le, le_refl]
	  			  	    ++ METIS_TAC [zero_to_n_Int_list_contains_Int])
	    			    ++ `Leq (\s. if MEM (s "payer") (zero_to_n_Int_list n) /\ 
			 			    (n = num_of_value (s "N")) then 1 else 0)
		    			    (\s. if MEM (s "payer") 
						    (zero_to_n_Int_list (num_of_value (s "N"))) 
						 then 1 else 0)`
					by (RW_TAC posreal_ss [Leq_def]
	     			            ++ RW_TAC posreal_ss [zero_le, le_refl]
	       			            ++ METIS_TAC [])
				    ++ `Leq (Conj (\s. if (n = num_of_value (s "N")) then 1 else 0)
	 			     		  (\s. if MEM (s "payer") (zero_to_n_Int_list n) 
						       then (1:posreal) else 0))
					    (\s. if MEM (s "payer") (zero_to_n_Int_list n) /\ 
						    (n = num_of_value (s "N")) then 1 else 0)`
					by (RW_TAC posreal_ss [Leq_def, Conj_def]
					    ++ RW_TAC posreal_ss []
					    ++ METIS_TAC [])
				    ++ PROVE_TAC [leq_trans])
			    ++ `LENGTH (zero_to_n_Int_list n) > 0`
				by (Cases_on `n`
				    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
		  	    ++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
	       			   (\s. (if MEM (s "payer") (zero_to_n_Int_list n) then 1 else 0)) = One`
				by METIS_TAC [NondetAssign_partial_result]
			    ++ FULL_SIMP_TAC posreal_ss [Conj_def, One_def, add_sub]
			    ++ METIS_TAC [])
		    ++ `(wp (NondetAssign "payer" (zero_to_n_Int_list n))
       		            (\s. (if n = num_of_value (s "N") then 1 else 0))) =
	       		    (\s. (if n = num_of_value (s "N") then 1 else 0))`
			by (`LENGTH (zero_to_n_Int_list n) > 0`
				by (Cases_on `n`
		    		    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
		    	    ++ `!a s. (\s. (if n = num_of_value (s "N") then (1:posreal) else 0)) s =
			              (\s. (if n = num_of_value (s "N") then 1 else 0)) 
			      	      (assign "payer" a s)`
				by RW_TAC posreal_ss [assign_eta]
		    	    ++ `!v (l:value list) (e:(string->value)->posreal). (LENGTH l > 0) ==>
	        		   ((!a s. e s = e (assign v a s)) ==>
		  	 	   ((wp (NondetAssign v l) e) = e))`
				by METIS_TAC [NondetAssign_do_nothing_val]
		    	    ++ FULL_SIMP_TAC std_ss [])
		    ++ FULL_SIMP_TAC std_ss [])
	++ RW_TAC posreal_ss [FUN_EQ_THM, One_def]
	++ MATCH_MP_TAC le_antisym
	++ `expect1 (\s. (if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0))`
		by (RW_TAC posreal_ss [expect1_def]
		    ++ RW_TAC posreal_ss [le_refl, zero_le])
	++ `expect1 (wp (NondetAssign "payer" (zero_to_n_Int_list n))
			(\s. (if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0)))`
		by METIS_TAC [expect1_postE_imp_expect1_wp_postE]
	++ FULL_SIMP_TAC posreal_ss [expect1_def, Leq_def]
	++ POP_ASSUM (K ALL_TAC)
	++ POP_ASSUM (K ALL_TAC)
	++ Q.ABBREV_TAC `state = (\w. (if w = "NSApays" then No else (if w = "N" then Int (& n) else s w)))`
	++ `(if n = num_of_value (state "N") then (1:posreal) else 0) <=
	    wp (NondetAssign "payer" (zero_to_n_Int_list n))
	       (\s. (if num_of_value (s "payer") < num_of_value (s "N") then 1 else 0)) state`
		by PROVE_TAC []
	++ Suff `(1:posreal) <= (if n = num_of_value (state "N") then (1:posreal) else 0)`
	>> METIS_TAC [le_trans]
	++ Q.UNABBREV_TAC `state`
	++ RW_TAC posreal_ss [num_of_value_def, int_of_value_def, NUM_OF_INT],
	RW_TAC posreal_ss [initialize_def, Program_def, wp_def, set_payer_def, assign_eta, 
			   initialize_var_NSApays_def, initialize_var_N_def]
	++ RW_TAC posreal_ss [FUN_EQ_THM, Zero_def]
	++ `LENGTH (zero_to_n_Int_list n) > 0`
		by (Cases_on `n`
		    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
	++ `?x y. (MEM x (zero_to_n_Int_list n)) /\ (MEM y (zero_to_n_Int_list n)) /\ (~(x=y))`
		by (Q.EXISTS_TAC `Int 0`
		    ++ Q.EXISTS_TAC `Int 1`
		    ++ RW_TAC int_ss [zero_to_n_Int_list_contains])
	++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
               (\s. (if s "payer" = Int(& k) then 1 else 0)) = Zero`
		by METIS_TAC [NondetAssign_partial_result]
	++ RW_TAC posreal_ss [Zero_def],
	RW_TAC posreal_ss [initialize_def, Program_def, wp_def, set_payer_def, assign_eta, 
			   initialize_var_NSApays_def, initialize_var_N_def]
	++ RW_TAC posreal_ss [FUN_EQ_THM, Zero_def]
	++ `LENGTH (zero_to_n_Int_list n) > 0`
		by (Cases_on `n`
		    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
	++ `?x y. (MEM x (zero_to_n_Int_list n)) /\ (MEM y (zero_to_n_Int_list n)) /\ (~(x=y))`
		by (Q.EXISTS_TAC `Int 0`
		    ++ Q.EXISTS_TAC `Int 1`
		    ++ RW_TAC int_ss [zero_to_n_Int_list_contains])
	++ `MEM (Int (& k)) (zero_to_n_Int_list n)`
		by METIS_TAC [zero_to_n_Int_list_contains]
	++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
	       (\s. (if ~(s "payer" = Int (& k)) then 1 else 0)) = Zero`
		by METIS_TAC [NondetAssign_result]
	++ RW_TAC posreal_ss [Zero_def]]]);

val initialize_result2 = store_thm
  ("initialize_result2",
   ``!n nsapays k. (n > 0) ==>
	((wp (initialize n nsapays) (\s. if ((num_of_value (s "N")) = n) then 1 else 0) = One) /\
	 (wp (initialize n nsapays) (\s. if (s"N" = Int(&n)) then 1 else 0) = One) /\
	 (wp (initialize n nsapays) (\s. if nsapays 
					 then (if ((s "NSApays") = Yes) then 1 else 0)								 else (if ((s "NSApays") = No) then 1 else 0)) = One) /\
	 (if nsapays
	  then (wp (initialize n nsapays) (\s. if ((s "payer") = (s "N")) then 1 else 0) = One)
	  else 
	  ((wp (initialize n nsapays) 
	       (\s. if ((num_of_value (s "payer")) < 
		        (num_of_value (s "N"))) then 1 else 0) = One)
	    /\ ((n > 1) ==> ((wp (initialize n nsapays)
			         (\s. if (s "payer") = Int (& k) then 1 else 0) = Zero)
	    		     /\ ( (k < n) ==>
				(wp (initialize n nsapays)
				    (\s. if ~ ((s "payer") = Int (& k)) 
					 then 1 else 0) = Zero)))))))``,
    RW_TAC bool_ss [FORALL_AND_THM, initialize_result]
    ++ RW_TAC std_ss [initialize_def, Program_def, wp_def, set_payer_def, 
		   initialize_var_NSApays_def, assign_eta]
    >> RW_TAC posreal_ss [initialize_var_N_result2]
    ++ `wp (NondetAssign "payer" (zero_to_n_Int_list n))
	   (\s. (if s "N" = Int (& n) then 1 else 0)) =
	   (\s. (if s "N" = Int (& n) then 1 else 0))`
	by (`LENGTH (zero_to_n_Int_list n) > 0`
		by (Cases_on `n`
	    	    ++ RW_TAC arith_ss [zero_to_n_Int_list, LENGTH_SNOC])
	    ++ `!(n:num). (n > 0) ==>
		(?(l:value list). l = zero_to_n_Int_list n)`
		by (Induct_on `n`
	    	    ++ RW_TAC arith_ss [])
	    ++ `?l. zero_to_n_Int_list n = l` by METIS_TAC []
	    ++ `LENGTH l > 0` by RW_TAC arith_ss []
	    ++ ASM_REWRITE_TAC []
	    ++ `!a s. (\s. (if s "N" = Int (& n) then (1:posreal) else 0)) s =
		      (\s. (if s "N" = Int (& n) then 1 else 0))
		      (assign "payer" a s)` 
		by RW_TAC std_ss [assign_eta]
	    ++ `!(v :string) (l :value list) (e :(string -> value) -> posreal).
         	 LENGTH l > (0 :num) ==>
         	 (!(a :(string -> value) -> value) (s :string -> value).
          	 e s = e (assign v a s)) ==>
         	(wp (NondetAssign v l) e = e)` 
		by METIS_TAC [NondetAssign_do_nothing_val]
	    ++ FULL_SIMP_TAC std_ss [])
    ++ RW_TAC std_ss [initialize_var_N_result2]);

(* -------------------------- flip_coins proofs ---------------------------- *)

val flip_coins_term = store_thm
  ("flip_coins_term",
   ``!n nsapays k. (n > 0) ==>
	(wp (Seq (initialize n nsapays) (flip_coins)) One = One)``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC seq_term
   ++ RW_TAC std_ss [initialize_term, flip_coins_def, Program_def, wp_def]
   ++ `wp (For_0_to_n "i" "N"
		      [ProbAssign "coinflip" [Heads; Tails];
		       Assign_Array_i "Coins" "i" (\s. s "coinflip")]) One = One`
	by (`~("N" = "i")` by SRW_TAC [] []
	    ++ `Leq (\s. if (\s. (0 <= int_of_value (s "i"))) s then 1 else 0)
		    (wp (Program
			 [ProbAssign "coinflip" [Heads; Tails];
			  Assign_Array_i "Coins" "i" (\s. s "coinflip")])
			(\s. if (\s. (0 <= int_of_value (s "i"))) s then 1 else 0))`
		by (SRW_TAC [] [Program_def, wp_def, Assign_Array_i_def, assign_eta]
		    ++ Suff `wp (ProbAssign "coinflip" [Heads; Tails])
		                (\s. (if 0 <= int_of_value (s "i") then (1:posreal) else 0)) = 
			        (\s. (if 0 <= int_of_value (s "i") then (1:posreal) else 0))`
		    >> (RW_TAC std_ss [] ++ METIS_TAC [leq_refl])
		    ++ `!v l e. (LENGTH l > 0) ==>
	        ((!a (s:string->value). e s = e (assign v a s)) ==>
		   ((wp (ProbAssign v l) e) = e))` by METIS_TAC [ProbAssign_do_nothing_val]
		    ++ `!a s. (\s. (if 0 <= int_of_value (s "i") then (1:posreal) else 0)) s =
			      (\s. (if 0 <= int_of_value (s "i") then 1 else 0))
			      (assign "coinflip" a s)` 
			by SRW_TAC [] [assign_eta]
		    ++ `LENGTH [Heads;Tails] > 0` by RW_TAC arith_ss [LENGTH]
		    ++ FULL_SIMP_TAC std_ss [])
	    ++ `!N. Leq (\s. if (\s.((int_of_value (s "i")) < (int_of_value (s "N")))) s /\
			        (\s.(0 <= (int_of_value(s "i")))) s /\
			        ((\s.((int_of_value (s "N")) - (int_of_value (s "i")))) s = N)
			     then 1 else 0)
			(wp (Program
			     [ProbAssign "coinflip" [Heads; Tails];
			      Assign_Array_i "Coins" "i" (\s. s "coinflip")])
			    (\s. if ((\s.((int_of_value (s "N")) - (int_of_value (s "i")))) s <= N) 
			         then 1 else 0))`
		by (SRW_TAC [] [Program_def, wp_def, Assign_Array_i_def, assign_eta]
		    ++ `Leq (\s. (if int_of_value (s "i") < int_of_value (s "N") /\
				     0 <= int_of_value (s "i") /\
				     (int_of_value (s "N") - int_of_value (s "i") = N)
				  then 1 else 0))
			    (\s. (if int_of_value (s "N") - int_of_value (s "i") <= N 
				  then 1 else 0))`
			by (RW_TAC posreal_ss [Leq_def]
			    ++ RW_TAC posreal_ss []
			    ++ METIS_TAC [INT_LE_REFL])
		    ++ Suff `(wp (ProbAssign "coinflip" [Heads; Tails])
				 (\s. (if int_of_value (s "N") - int_of_value (s "i") <= N 
				       then 1 else 0))) =
			     (\s. (if int_of_value (s "N") - int_of_value (s "i") <= N 
				  then 1 else 0))`
		    >> (RW_TAC std_ss [] ++ METIS_TAC [leq_trans])
		    ++ `!v l e. (LENGTH l > 0) ==>
	        ((!a (s:string->value). e s = e (assign v a s)) ==>
		   ((wp (ProbAssign v l) e) = e))` by METIS_TAC [ProbAssign_do_nothing_val]
		    ++ `!a s. (\s. (if int_of_value (s "N") - 
				       int_of_value (s "i") <= N then (1:posreal) else 0)) s =
			      (\s. (if int_of_value (s "N") - 
				       int_of_value (s "i") <= N then 1 else 0))
			      (assign "coinflip" a s)` 
			by SRW_TAC [] [assign_eta]
		    ++ `LENGTH [Heads;Tails] > 0` by RW_TAC arith_ss [LENGTH]
		    ++ FULL_SIMP_TAC std_ss [])
	    ++ METIS_TAC [For_i_0_to_n_variant_rule])
	++ RW_TAC std_ss [New_Array_def, wp_def, assign_eta, One_def]);

val flip_coins_result_part1 = store_thm
  ("flip_coins_result_part1",
   ``!(n :num) (nsapays :bool) (i :num).
      n > (0 :num) /\ i < n ==>
      (wp (Seq (initialize n nsapays) flip_coins)
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") i = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))) =
       (One :value state expect))``,
   RW_TAC std_ss [wp_def]
   ++ MATCH_MP_TAC leq_antisym
       ++ `Leq
      (wp (initialize (n :num) (nsapays :bool))
         (wp flip_coins
            (\(s :value state).
               (if
                  (get_Array_i (s "Coins") (i :num) = Heads) \/
                  (get_Array_i (s "Coins") i = Tails)
                then
                  (1 :
                posreal)
                else
                  (0 :
                posreal))))) (One :value state expect)`
	by (`Leq
      (wp flip_coins
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") (i :num) = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal)))) (One :value state expect)`
		by (`expect1
      (\(s :value state).
         (if
            (get_Array_i (s "Coins") (i :num) = Heads) \/
            (get_Array_i (s "Coins") i = Tails)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))`
			by (RW_TAC posreal_ss [expect1_def]
		    	    ++ RW_TAC posreal_ss [le_refl, zero_le])
       		    ++ `expect1
      (wp flip_coins
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") (i :num) = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
			by METIS_TAC [expect1_postE_imp_expect1_wp_postE]
       		    ++ FULL_SIMP_TAC posreal_ss [expect1_def, Leq_def, One_def]
		    ++ RW_TAC std_ss [])
	    ++ `expect1
      (wp flip_coins
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") (i :num) = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
		by FULL_SIMP_TAC posreal_ss [expect1_def, Leq_def, One_def]
	    ++ `expect1
      (wp (initialize (n :num) (nsapays :bool))
         (wp flip_coins
            (\(s :value state).
               (if
                  (get_Array_i (s "Coins") (i :num) = Heads) \/
                  (get_Array_i (s "Coins") i = Tails)
                then
                  (1 :
                posreal)
                else
                  (0 :
                posreal)))))`
		by METIS_TAC [expect1_postE_imp_expect1_wp_postE]
	    ++ FULL_SIMP_TAC posreal_ss [expect1_def, Leq_def, One_def])
        ++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ RW_TAC posreal_ss [flip_coins_def, For_0_to_n_def, wp_def, Program_def]
	++ RW_TAC std_ss [For_def]
	++ `wp
      (Seq (Assign "i" (\(s :value state). Int (0 :int)))
         (While
            (\(s :value state). int_of_value (s "i") < int_of_value (s "N"))
            (Seq
               (Program
                  [ProbAssign "coinflip" [Heads; Tails];
                   Assign_Array_i "Coins" "i"
                     (\(s :value state). s "coinflip")])
               (Assign "i"
                  (\(s :value state).
                     Int (int_of_value (s "i") + (1 :int)))))))
      (\(s :value state).
         (if
            (get_Array_i (s "Coins") (i :num) = Heads) \/
            (get_Array_i (s "Coins") i = Tails)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal))) =
    wp (Assign "i" (\(s :value state). Int (0 :int)))
      (wp
         (While
            (\(s :value state). int_of_value (s "i") < int_of_value (s "N"))
            (Seq
               (Program
                  [ProbAssign "coinflip" [Heads; Tails];
                   Assign_Array_i "Coins" "i"
                     (\(s :value state). s "coinflip")])
               (Assign "i"
                  (\(s :value state).
                     Int (int_of_value (s "i") + (1 :int))))))
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") i = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
		by METIS_TAC [wp_def]
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ Q.ABBREV_TAC `Inv = (\(v :num) (s :value state).
                (v = num_of_value (s "N") - num_of_value (s "i")) /\
                (0 :int) <= int_of_value (s "i") /\
                v <= num_of_value (s "N") /\
                int_of_value (s "i") <= int_of_value (s "N") /\
                (!(j :num).
                   j < num_of_value (s "i") ==>
                   (get_Array_i (s "Coins") j = Heads) \/
                   (get_Array_i (s "Coins") j = Tails)) /\
                (?(l :value list). s "Coins" = Array l) /\
                (Array_length (s "Coins") = num_of_value (s "N")) /\
                (num_of_value (s "N") = (n :num)) /\
                (s "N" = Int (& n :int)))`
	++ Q.ABBREV_TAC `body = Seq
               (Program
                  [ProbAssign "coinflip" [Heads; Tails];
                   Assign_Array_i "Coins" "i"
                     (\(s :value state). s "coinflip")])
               (Assign "i"
                  (\(s :value state).
                     Int (int_of_value (s "i") + (1 :int))))`
	++ Q.ABBREV_TAC `g = (\(s :value state).
                int_of_value (s "i") < int_of_value (s "N"))`
	++ `!v:num. Leq (bool_exp (Inv v))
			(wp (While g body)
			    (bool_exp (\s. ?v'. Inv v' s /\ (~(g s)))))`
		by (MATCH_MP_TAC bool_Inv_rule
		    ++ GEN_TAC
		    ++ RW_TAC posreal_ss [bool_exp_def, Leq_def]
		    ++ RW_TAC posreal_ss [zero_le]
		    ++ Q.UNABBREV_TAC `body`
		    ++ RW_TAC posreal_ss [Program_def, wp_def, assign_eta, Assign_Array_i_def, 
					  ProbAssign_def, MAP, Probs_def, LENGTH]
		    ++ Q.UNABBREV_TAC `Inv`
		    ++ Q.UNABBREV_TAC `g`
		    ++ `(\(v :value state).
       (1 :posreal) / (2 :posreal) /
       ((1 :posreal) - (1 :posreal) / (2 :posreal))) =
    (\(v :value state). (1 :posreal))`
			by (RW_TAC posreal_ss [FUN_EQ_THM, sub_ratr, div_rat, preal_div_def]
			    ++ MATCH_MP_TAC mul_linv
			    ++ RW_TAC posreal_ss [])
		    ++ ASM_REWRITE_TAC []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ FULL_SIMP_TAC posreal_ss [lin_eta, bound1_def, mul_lone, Zero_def, mul_rzero, 
						 int_of_value_def, let_lemma, let_lin_lemma]
		    ++ `(0 :int) <= int_of_value ((s :value state) "i") + (1 :int)`
			by RW_TAC int_ss []
		    ++ `~("Coins" = "i")` by SRW_TAC [] []
		    ++ `~("N" = "i")` by SRW_TAC [] []
		    ++ `~("N" = "Coins")` by SRW_TAC [] []
		    ++ `~("N" = "coinflip")` by SRW_TAC [] []
		    ++ FULL_SIMP_TAC std_ss [num_of_value_def, int_of_value_def]
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `(0 :int) <= (& (n :num) :int)`
			 by (MATCH_MP_TAC INT_LT_IMP_LE 
			     ++ METIS_TAC [INT_LET_TRANS])
   		    ++ `?(n' :num). int_of_value ((s :value state) "N") = (& n' :int)`
			by METIS_TAC [int_of_value_def]
		    ++ `?(i' :num). int_of_value ((s :value state) "i") = (& i' :int)`
			by METIS_TAC [NUM_POSINT_EXISTS]
		    ++ `(& (i' :num) :int) + (1 :int) = (& (SUC i') :int)` by METIS_TAC [INT]
		    ++ FULL_SIMP_TAC int_ss [NUM_OF_INT]
		    ++ Suff `((!(j :num).
        j < SUC (i' :num) ==>
        (get_Array_i (update_Array_i (Array (l :value list)) i' Heads) j =
         Heads) \/
        (get_Array_i (update_Array_i (Array l) i' Heads) j = Tails)) /\
     (?(l' :value list). update_Array_i (Array l) i' Heads = Array l') /\
     (Array_length (update_Array_i (Array l) i' Heads) = (n :num))) /\
    (!(j :num).
       j < SUC i' ==>
       (get_Array_i (update_Array_i (Array l) i' Tails) j = Heads) \/
       (get_Array_i (update_Array_i (Array l) i' Tails) j = Tails)) /\
    (?(l' :value list). update_Array_i (Array l) i' Tails = Array l') /\
    (Array_length (update_Array_i (Array l) i' Tails) = n)`
		    >> (RW_TAC posreal_ss [sub_ratr, add_rat]
			++ RW_TAC posreal_ss [preal_div_def]
			++ Suff `(4 :posreal) * inv (4 :posreal) = (1 :posreal)`
			>> METIS_TAC [le_refl]
			++ MATCH_MP_TAC mul_rinv
		        ++ RW_TAC posreal_ss [])
		    ++ `(0 :num) < (n :num) - (i' :num)`
			by (`!(a :num) (b :num). a < b ==> (0 :num) < b - a` by RW_TAC arith_ss []
		    	    ++ METIS_TAC [])
		    ++ `Array_length (update_Array_i (Array (l :value list)) (i' :num) Tails) =
    Array_length ((s :value state) "Coins")`
			by (`?(l' :value list).
      update_Array_i (Array (l :value list)) (i' :num) Tails = Array l'`
				by RW_TAC std_ss [update_Array_i_def]
		    	    ++ METIS_TAC [update_Array_i_length])
		    ++ `Array_length (update_Array_i (Array (l :value list)) (i' :num) Heads) =
    Array_length ((s :value state) "Coins")`
			by (`?(l' :value list).
      update_Array_i (Array (l :value list)) (i' :num) Heads = Array l'`
				by RW_TAC std_ss [update_Array_i_def]
		    	    ++ METIS_TAC [update_Array_i_length])
		    ++ `(!(j :num).
       j < SUC (i' :num) ==>
       (get_Array_i (update_Array_i (Array (l :value list)) i' Heads) j =
        Heads) \/
       (get_Array_i (update_Array_i (Array l) i' Heads) j = Tails)) /\
    (?(l' :value list). update_Array_i (Array l) i' Heads = Array l') =
    !(j :num).
      j < SUC i' ==>
      (get_Array_i (update_Array_i (Array l) i' Heads) j = Heads) \/
      (get_Array_i (update_Array_i (Array l) i' Heads) j = Tails)`
			by RW_TAC std_ss [update_Array_i_def]
		    ++ `(!(j :num).
       j < SUC (i' :num) ==>
       (get_Array_i (update_Array_i (Array (l :value list)) i' Tails) j =
        Heads) \/
       (get_Array_i (update_Array_i (Array l) i' Tails) j = Tails)) /\
    (?(l' :value list). update_Array_i (Array l) i' Tails = Array l') =
    !(j :num).
      j < SUC i' ==>
      (get_Array_i (update_Array_i (Array l) i' Tails) j = Heads) \/
      (get_Array_i (update_Array_i (Array l) i' Tails) j = Tails)`
			by RW_TAC std_ss [update_Array_i_def]
		    ++ FULL_SIMP_TAC std_ss []
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ POP_ASSUM (K ALL_TAC)
		    ++ `!(j :num).
      j < SUC (i' :num) ==>
      (get_Array_i (update_Array_i (Array (l :value list)) i' Heads) j =
       Heads) \/ (get_Array_i (update_Array_i (Array l) i' Heads) j = Tails)`
			by (REPEAT STRIP_TAC
		    	    ++ `(j :num) <= (i' :num)` by RW_TAC int_ss []
		    	    ++ `(j :num) < Array_length ((s :value state) "Coins")`
				by METIS_TAC [LESS_EQ_LESS_TRANS]
		    	    ++ `get_Array_i (update_Array_i (Array (l :value list)) (i' :num) Heads)
      (j :num) =
    (if j = i' then Heads else get_Array_i (Array l) j)`
				by METIS_TAC [update_Array_i_el]
		    	    ++ ASM_REWRITE_TAC []
		    	    ++ Cases_on `j = i'`
		    	    >> RW_TAC std_ss []
		    	    ++ `(j :num) < (i' :num)` by RW_TAC int_ss []
		    	    ++ METIS_TAC [])
		    ++ `!(j :num).
      j < SUC (i' :num) ==>
      (get_Array_i (update_Array_i (Array (l :value list)) i' Tails) j =
       Heads) \/ (get_Array_i (update_Array_i (Array l) i' Tails) j = Tails)`
			by (REPEAT STRIP_TAC
		    	    ++ `(j :num) <= (i' :num)` by RW_TAC int_ss []
		    	    ++ `(j :num) < Array_length ((s :value state) "Coins")`
				by METIS_TAC [LESS_EQ_LESS_TRANS]
		    	    ++ `get_Array_i (update_Array_i (Array (l :value list)) (i' :num) Tails)
      (j :num) =
    (if j = i' then Tails else get_Array_i (Array l) j)`
				by METIS_TAC [update_Array_i_el]
		    	    ++ ASM_REWRITE_TAC []
		    	    ++ Cases_on `j = i'`
		    	    >> RW_TAC std_ss []
		    	    ++ `(j :num) < (i' :num)` by RW_TAC int_ss []
		    	    ++ METIS_TAC [])
		    ++ RW_TAC std_ss [])
	++ `Leq (bool_exp ((Inv :num -> value state -> bool) (n :num)))
      (wp (While (g :value state -> bool) (body :value command))
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") (i :num) = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
		by (`Leq
      (wp (While (g :value state -> bool) (body :value command))
         (bool_exp
            (\(s :value state).
               ?(v' :num). (Inv :num -> value state -> bool) v' s /\ ~g s)))
      (wp (While g body)
         (\(s :value state).
            (if
               (get_Array_i (s "Coins") (i :num) = Heads) \/
               (get_Array_i (s "Coins") i = Tails)
             then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
			by (`Leq
      (bool_exp
         (\(s :value state).
            ?(v' :num).
              (Inv :num -> value state -> bool) v' s /\
              ~(g :value state -> bool) s))
      (\(s :value state).
         (if
            (get_Array_i (s "Coins") (i :num) = Heads) \/
            (get_Array_i (s "Coins") i = Tails)
          then
            (1 :
          posreal)
          else
            (0 :
          posreal)))`
				by (POP_ASSUM (K ALL_TAC)
				    ++ RW_TAC posreal_ss [Leq_def, bool_exp_def]
				    ++ Suff `(?(v' :num).
       (Inv :num -> value state -> bool) v' (s :value state) /\
       ~(g :value state -> bool) s) ==>
    (get_Array_i (s "Coins") (i :num) = Heads) \/
    (get_Array_i (s "Coins") i = Tails)`
			    	    >> RW_TAC posreal_ss [zero_le, le_refl]
			  	    ++ Q.UNABBREV_TAC `Inv`
				    ++ Q.UNABBREV_TAC `g`
				    ++ RW_TAC std_ss []
				    ++ `int_of_value ((s :value state) "i") = int_of_value (s "N")`
					by (FULL_SIMP_TAC int_ss [INT_NOT_LT]
					    ++ METIS_TAC [INT_LE_ANTISYM])
		  		    ++ FULL_SIMP_TAC std_ss [num_of_value_def])
		 	   ++ METIS_TAC [wp_mono])
		    ++ METIS_TAC [leq_trans])
	++ Suff `Leq (One :value state expect)
      (wp (initialize (n :num) (nsapays :bool))
         (wp (New_Array "Coins" "N")
            (wp (Assign "i" (\(s :value state). Int (0 :int)))
               (bool_exp ((Inv :num -> value state -> bool) n)))))`
	>> PROVE_TAC [wp_mono, leq_trans]
	++ POP_ASSUM (K ALL_TAC)
	++ POP_ASSUM (K ALL_TAC)
	++ Q.UNABBREV_TAC `body`
	++ Q.UNABBREV_TAC `g`
	++ Q.UNABBREV_TAC `Inv`
	++ SRW_TAC [] [bool_exp_def, wp_def, assign_eta, New_Array_def, 
		       num_of_value_def, int_of_value_def, Array_length_def]
	++ `(\(s :value state).
       (if
          ((n :num) = Num (int_of_value (s "N"))) /\
          n <= Num (int_of_value (s "N")) /\
          (0 :int) <= int_of_value (s "N") /\
          (LENGTH (n_list (Num (int_of_value (s "N"))) Null) =
           Num (int_of_value (s "N"))) /\
          (Num (int_of_value (s "N")) = n) /\ (s "N" = Int (& n :int))
        then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    (\(s :value state).
       (if (s "N" = Int (& n :int)) /\ (Num (int_of_value (s "N")) = n) then
          (1 :
        posreal)
        else
          (0 :
        posreal)))`
		by (RW_TAC std_ss [FUN_EQ_THM]
		    ++ RW_TAC posreal_ss []
		    >> (FULL_SIMP_TAC arith_ss [int_of_value_def]
			++ `~((0 :int) <= (& (Num (int_of_value ((s :value state) "N"))) :int))` by METIS_TAC [int_of_value_def]
			++ FULL_SIMP_TAC int_ss [INT_LE_REDUCE])
		    ++ FULL_SIMP_TAC arith_ss [int_of_value_def, length_of_n_list])
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ `(\(s :value state).
       (if
          (s "N" = Int (& (n :num) :int)) /\
          (Num (int_of_value (s "N")) = n)
        then
          (1 :
        posreal)
        else
          (0 :
        posreal))) =
    Conj
      (\(s :value state).
         (if s "N" = Int (& n :int) then (1 :posreal) else (0 :posreal)))
      (\(s :value state).
         (if Num (int_of_value (s "N")) = n then
            (1 :
          posreal)
          else
            (0 :
          posreal)))`
		by (RW_TAC posreal_ss [Conj_def, FUN_EQ_THM]
		    ++ RW_TAC posreal_ss [])
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ Suff `(One :value state expect) =
    Conj
      (wp (initialize (n :num) (nsapays :bool))
         (\(s :value state).
            (if s "N" = Int (& n :int) then
               (1 :
             posreal)
             else
               (0 :
             posreal))))
      (wp (initialize n nsapays)
         (\(s :value state).
            (if Num (int_of_value (s "N")) = n then
               (1 :
             posreal)
             else
               (0 :
             posreal))))`
	>> PROVE_TAC [leq_trans, leq_refl, wp_conj]
	++ `wp (initialize (n :num) (nsapays :bool))
      (\(s :value state).
         (if s "N" = Int (& n :int) then (1 :posreal) else (0 :posreal))) =
    (One :value state expect)`
		by METIS_TAC [initialize_result2]
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ `wp (initialize (n :num) (nsapays :bool))
      (\(s :value state).
         (if num_of_value (s "N") = n then
            (1 :
          posreal)
          else
            (0 :
          posreal))) =
    (One :value state expect)`
		by METIS_TAC [initialize_result2, num_of_value_def]
	++ FULL_SIMP_TAC std_ss [num_of_value_def]
	++ POP_ASSUM (K ALL_TAC)
	++ RW_TAC posreal_ss [Conj_def, One_def]);

(* ???????????????????????????????????????????????

val flip_coins_result = store_thm
  ("flip_coins_result",
   ``!n nsapays i. (n > 0) /\
	(i < n) ==>
	(wp (Seq (initialize n nsapays) (flip_coins))
	   (\s. if ((get_Array_i (s "Coins") i) = Heads) \/
		   ((get_Array_i (s "Coins") i) = Tails)
		then 1 else 0) = 
	 One) /\
	(wp (Seq (initialize n nsapays) (flip_coins))
	    (\s. if ((get_Array_i (s "Coins") i) = Heads)
		 then 1 else 0) =
	 (\s. 1/2)) /\
	(wp (Seq (initialize n nsapays) (flip_coins))
	    (\s. if ((get_Array_i (s "Coins") i) = Tails)
		 then 1 else 0) =
	 (\s. 1/2))``,
   REPEAT STRIP_TAC
   << [METIS_TAC [flip_coins_result_part1],
       METIS_TAC [flip_coins_result_part2],
       METIS_TAC [flip_coins_result_part3]]);

??????????????????????????????????????????????? *)

(* ----------------------- set_announcements proofs ------------------------ *)

val set_announcements_term = store_thm
  ("set_announcements_term",
   ``!n nsapays. (n > 0) ==>
	(wp (Program [initialize n nsapays; flip_coins; set_announcements]) One = One)``,
	REPEAT STRIP_TAC
	++ `wp (Program [initialize n nsapays; flip_coins; set_announcements]) One =
	    wp (Seq (initialize n nsapays) (flip_coins)) (wp set_announcements One)`
		by METIS_TAC [Program_def, wp_def, seq_assoc]
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ Suff `wp set_announcements One = One`
	>> METIS_TAC [flip_coins_term]
	++ SIMP_TAC std_ss [set_announcements_def, Program_def, wp_def]
	++ `wp (New_Array "Announces" "N") One = One`
		by RW_TAC posreal_ss [New_Array_def, wp_def, assign_eta, One_def]
	++ Suff `(wp (For_0_to_n "i" "N"
            		[Assign "currentcoin"
               			(\s. get_Array_i (s "Coins") (num_of_value (s "i")));
             		If (\s. num_of_value (s "i") = 0)
               			(Assign "previouscoin"
                  			(\s. get_Array_i (s "Coins") (num_of_value (s "N") - 1)))
               			(Assign "previouscoin"
                  			(\s. get_Array_i (s "Coins") (num_of_value (s "i") - 1)));
             		If (\s. s "i" = s "payer") (Assign "pays" (\s. Yes))
               			(Assign "pays" (\s. No));
             		Assign_Array_i "Announces" "i"
               			(\s. xor [s "previouscoin"; s "currentcoin"; s "pays"])]) One) = One`
	>> RW_TAC std_ss []
	++ POP_ASSUM (K ALL_TAC)
	++ MATCH_MP_TAC For_i_0_to_n_variant_rule
	++ SRW_TAC [] []
	>> (RW_TAC std_ss [Program_def, wp_def, assign_eta, If_def, lin_eta, Leq_def, Assign_Array_i_def]
	    ++ `~((if 0 <= int_of_value (s "i") then 1 else 0) = infty)`
			by RW_TAC posreal_ss []
	    ++ Q.UNABBREV_TAC `x'`
	    ++ `((bound1 (if s "i" = s "payer" then 1 else 0)) * 
		(if 0 <= int_of_value (s "i") then 1 else 0) +
		(1 - (bound1 (if s "i" = s "payer" then 1 else 0))) * 
		(if 0 <= int_of_value (s "i") then 1 else 0)) =
		(if 0 <= int_of_value (s "i") then 1 else 0)`
			by PROVE_TAC [bound1_eq_lemma]
	    ++ ASM_REWRITE_TAC []
	    ++ POP_ASSUM (K ALL_TAC)
	    ++ Q.UNABBREV_TAC `x`
	    ++ PROVE_TAC [bound1_eq_lemma, le_refl])
	++ `Leq (\s. (if int_of_value (s "i") < int_of_value (s "N") /\
				     0 <= int_of_value (s "i") /\
				     (int_of_value (s "N") - int_of_value (s "i") = N)
				  then 1 else 0))
			    (\s. (if int_of_value (s "N") - int_of_value (s "i") <= N 
				  then 1 else 0))`
			by (RW_TAC posreal_ss [Leq_def]
			    ++ RW_TAC posreal_ss []
			    ++ METIS_TAC [INT_LE_REFL])
	++ Suff `(wp (Program
            		[Assign "currentcoin"
               			(\s. get_Array_i (s "Coins") (num_of_value (s "i")));
             		If (\s. num_of_value (s "i") = 0)
               			(Assign "previouscoin"
                  			(\s. get_Array_i (s "Coins") (num_of_value (s "N") - 1)))
               			(Assign "previouscoin"
                  			(\s. get_Array_i (s "Coins") (num_of_value (s "i") - 1)));
             		If (\s. s "i" = s "payer") (Assign "pays" (\s. Yes))
               			(Assign "pays" (\s. No));
             		Assign_Array_i "Announces" "i"
               			(\s. xor [s "previouscoin"; s "currentcoin"; s "pays"])])
         	(\s. (if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0))) =
		(\s. (if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0))`
	>> (RW_TAC std_ss [] ++ METIS_TAC [leq_trans])
	++ RW_TAC std_ss [Program_def, wp_def, assign_eta, If_def, lin_eta, Assign_Array_i_def, FUN_EQ_THM]
	++ `~((if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0) = infty)`
		by RW_TAC posreal_ss []
	++ Q.UNABBREV_TAC `x'`
	++ `((bound1 (if s "i" = s "payer" then 1 else 0)) * 
		(if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0) +
		(1 - (bound1 (if s "i" = s "payer" then 1 else 0))) * 
		(if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0)) =
		(if int_of_value (s "N") - int_of_value (s "i") <= N then 1 else 0)`
			by PROVE_TAC [bound1_eq_lemma]
	++ ASM_REWRITE_TAC []
	++ POP_ASSUM (K ALL_TAC)
	++ Q.UNABBREV_TAC `x`
	++ PROVE_TAC [bound1_eq_lemma]);

(* ???????????????????????????????????????????????

val set_announcements_result = store_thm
   ("set_announcements_result",
   ``!n nsapays i.
     (i < n) ==>
	wp (Program [initialize n nsapays; flip_coins; set_announcements])
	   (\s. let a = (get_Array_i (s "Announces") i) in
		if i = (s "payer")
		then
		   (let p = Yes in
		    if i = 0
		    then
			(let (c1, c2) = (get_Array_i (s "Coins") 0, get_Array_i (s "Coins") n - 1) in
			 if a = (xor [p; c1; c2]) then 1 else 0)
		    else
		    	(let (c1, c2) = (get_Array_i (s "Coins") i, get_Array_i (s "Coins") i - 1) in
			 if a = (xor [p; c1; c2]) then 1 else 0))
		else
		   (let p = No in
		    if i = 0
		    then
			(let (c1, c2) = (get_Array_i (s "Coins") 0, get_Array_i (s "Coins") n - 1) in
			 if a = (xor [p; c1; c2]) then 1 else 0)
		    else
		    	(let (c1, c2) = (get_Array_i (s "Coins") i, get_Array_i (s "Coins") i - 1) in
			 if a = (xor [p; c1; c2]) then 1 else 0))) = One``,
   ???);

??????????????????????????????????????????????? *)

(* ------------------------- compute_result proofs ------------------------- *)

val compute_result_term = store_thm
  ("compute_result_term",
   ``!n nsapays. (n>0) ==>
	(wp (Program [initialize n nsapays; flip_coins; set_announcements; compute_result]) One = One)``,
   REPEAT STRIP_TAC
   ++ `wp (Program [initialize n nsapays; flip_coins; set_announcements; compute_result]) One =
       wp (Program [initialize n nsapays; flip_coins; set_announcements]) (wp compute_result One)`
	by METIS_TAC [Program_def, wp_def, seq_assoc]
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM (K ALL_TAC)
   ++ Suff `wp compute_result One = One`
   >> METIS_TAC [set_announcements_term]
   ++ RW_TAC posreal_ss [compute_result_def, wp_def, One_def]);

(* ???????????????????????????????????????????????

val compute_result_result = store_thm
  ("compute_result_result",
   ``!n nsapays.
	if nsapays
	then
	   wp (Program [initialize n nsapays; flip_coins; set_announcements; compute_result])
	      (\s. if (s "result") = No then 1 else 0) = One
	else
	   wp (Program [initialize n nsapays; flip_coins; set_announcements; compute_result])
	      (\s. if (s "result") = Yes then 1 else 0) = One``,
   ????);

??????????????????????????????????????????????? *)

(* ----------------------------- dc_prog proofs ---------------------------- *)

val dcprog_term = store_thm
  ("dcprog_term",
   ``!n nsapays. (n > 0) ==>
	(wp (dcprog n nsapays) One = One)``,
   METIS_TAC [dcprog_def, compute_result_term]);

(* ???????????????????????????????????????????????

val dcprog_result = store_thm
  ("dcprog_result",
   ``!n nsapays f f'.
	(n > 1) ==>
	   if nsapays
	   then
		wp (dcprog n nsapays) (\s. if (s "result") = No then 1 else 0) = One
	   else
		(wp (dcprog n nsapays) (\s. if (s "result") = Yes then 1 else 0) = One) /\
		(Leq (wp (dcprog n nsapays)
			 (\s. if ~(i = (s "payer"))
			      then
				(if (f (s "N") (s "Announces") (s "result")) = (s "payer") 
				 then 1 else 0)
			      else
				0))
		     (\s. if ~ (i = (s "payer")) then (1/n) else 0)) /\
		(Leq (wp (dcprog n nsapays)
			 (\s. if ~(i = (s "payer"))
			      then
				(if i = 0
				 then
				    (if (f (s "N") (s "Announces") (s "result")
					   (get_Array_i (s "Coins") 0)
					   (get_Array_i (s "Coins") (n-1))) =
					(s "payer")
				     then 1 else 0)
				 else
				    (if (f (s "N") (s "Announces") (s "result")
					   (get_Array_i (s "Coins") i)
					   (get_Array_i (s "Coins") (i-1))) =
					(s "payer")
				     then 1 else 0))
			      else 0))
		     (\s. if ~(i = (s "payer")) then (1/(n-1)) else 0))``,
   ??????);

??????????????????????????????????????????????? *)

val _ = export_theory();