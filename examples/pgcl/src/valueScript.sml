(* ========================================================================= *)
(* Create "valueTheory"                   		    	             *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib", "wpTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory wpTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "value"                                         *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "value";

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
(* The HOL type we use to model values                                       *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype `value =
		Null
	      | Int of int
	      |	Array of value list`;

(* ------------------------------------------------------------------------- *)
(* Useful Functions for Turning Values into nums or ints                     *)
(* ------------------------------------------------------------------------- *)

val int_of_value_def = Define
   `int_of_value (Int i) = i`;

val num_of_value_def = Define
   `num_of_value i = Num (int_of_value i)`;

(* ------------------------------------------------------------------------- *)
(* Definitions for dealing with Array assignment                             *)
(* ------------------------------------------------------------------------- *)

val update_nth_def = Define
 `(update_nth l 0 v = v :: TL l) /\
  (update_nth l (SUC n) v = HD l :: update_nth (TL l) n v)`;

val update_nth_length = store_thm
 ("update_nth_length",
  ``!l n v.
      n < LENGTH l ==> (LENGTH (update_nth l n v) = LENGTH l)``,
  Induct_on `n`
  ++ Cases_on `l`
  ++ RW_TAC arith_ss [update_nth_def, HD, TL, LENGTH]);

val update_nth_el = store_thm
 ("update_nth_el",
  ``!n v l k.
      n < LENGTH l /\ k < LENGTH l ==>
      (EL k (update_nth l n v) = if k = n then v else EL k l)``,
  Induct_on `n`
  ++ Cases_on `l`
  ++ Cases_on `k`
  ++ RW_TAC arith_ss [EL, update_nth_def, HD, TL, LENGTH]);

(* use EL n l instead of get_nth *)

(* use SNOC for reverse of CONS *)

val update_Array_i_def = Define
   `update_Array_i (Array l) i v = Array (update_nth l i v)`;

val get_Array_i_def = Define
   `get_Array_i (Array l) i = EL i l`;

val Array_length_def = Define
   `Array_length (Array l) = LENGTH l`;

val update_Array_i_length = store_thm
 ("update_Array_i_length",
  ``!a i v.
      (?l. (a = Array l)) /\ i < Array_length a ==> 
          (Array_length (update_Array_i a i v) = Array_length a)``,
  RW_TAC arith_ss [] 
  ++ FULL_SIMP_TAC arith_ss [Array_length_def, update_Array_i_def, update_nth_length] 
  ++ MATCH_MP_TAC update_nth_length);

val update_Array_i_el = store_thm
 ("update_Array_i_el",
  ``!i v a k. (?l. (a = Array l)) /\
      i < Array_length a /\ k < Array_length a ==>
      (get_Array_i (update_Array_i a i v) k = if k = i then v else get_Array_i a k)``,
  RW_TAC arith_ss []
   ++ FULL_SIMP_TAC arith_ss [update_Array_i_def, get_Array_i_def, Array_length_def]
   ++ RW_TAC arith_ss [update_nth_el]);

val extend_Array_def = Define
  `extend_Array (Array l) v = Array (SNOC v l)`;

val extend_Array_length = store_thm
 ("extend_Array_length",
  ``!a v. (?l. (a = Array l)) ==> ((Array_length (extend_Array a v)) = ((Array_length a) + 1))``,
  RW_TAC arith_ss []
  ++ RW_TAC arith_ss [extend_Array_def, Array_length_def, LENGTH_SNOC]);

val extend_Array_el = store_thm
  ("extend_Array_el",
   ``!a v i. (?l. (a = Array l)) /\
             i < SUC(Array_length a) ==>
               (get_Array_i (extend_Array a v) i = 
                  if (i = (Array_length a)) then v else get_Array_i a i)``,
  RW_TAC arith_ss []
  ++ FULL_SIMP_TAC arith_ss [get_Array_i_def, extend_Array_def, Array_length_def, EL_SNOC, EL_LENGTH_SNOC]);

val Assign_Array_num_i = Define
   `Assign_Array_num_i v i (e:value state -> value) = Assign v (\s. update_Array_i (s v) i (e s))`;

val Assign_Array_i = Define
   `Assign_Array_i v i (e:value state -> value) = 
       Assign v (\(s:value state). update_Array_i (s v) (num_of_value(s i)) (e s))`;

val Assign_Array_extend = Define
   `Assign_Array_extend v (e:value state -> value) = Assign v (\(s:value state). extend_Array (s v) (e s))`;

val Assign_Array_empty = Define
   `Assign_Array_empty v = Assign v (\s. Array [])`;

val n_list_def = Define
   `(n_list 0 x = []) /\
    (n_list (SUC n) x = x::(n_list (n) x))`;

val length_of_n_list = store_thm
  ("length_of_n_list",
   ``!n x. LENGTH (n_list n x) = n``,
   REPEAT STRIP_TAC
   ++ Induct_on `n`
   ++ RW_TAC arith_ss [LENGTH, n_list_def]);

val New_Array = Define
   `New_Array a n = Assign a (\s. Array (n_list (num_of_value (s n)) Null))`;

val NondetAssign_Array_num_i_def = Define
   `NondetAssign_Array_num_i a i xs = 
	Nondets (MAP (\x. Assign_Array_num_i a i (\s. x)) xs)`; 

val NondetAssign_Array_i_def = Define
   `NondetAssign_Array_i a i xs =
	Nondets (MAP (\x. Assign_Array_i a i (\s. x)) xs)`;

val ProbAssign_Array_num_i_def = Define
   `ProbProbAssign_Array_num_i a i xs =
	Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_num_i a i (\s. x))) xs)`;

val ProbAssign_Array_i_def = Define
   `ProbAssign_Array_i a i xs =
	Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_i a i (\s. x))) xs)`;

val NondetAssign_Array_extend_def = Define
   `NondetAssign_Array_extend a xs =
	Nondets (MAP (\x. Assign_Array_extend a (\s. x)) xs)`;

val ProbAssign_Array_extend_def = Define
   `ProbAssign_Array_extend a xs =
	Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_extend a (\s. x))) xs)`;

val For_0_to_n_def = Define
   `For_0_to_n i n l = For i (\s. Int 0) (\s. (int_of_value(s i)) < (int_of_value(s n))) (\s. Int ((int_of_value(s i)) + 1)) l`;

(* ------------------------------------------------------------------------- *)
(* Showing the need for SUB-linearity for value states.                      *)
(* ------------------------------------------------------------------------- *)

val sublinear_necessary_value = store_thm
  ("sublinear_necessary_value",
   ``?p : value command. ?r1 r2 s.
       wp p r1 s + wp p r2 s < wp p (\s'. r1 s' + r2 s') s``,
   MATCH_MP_TAC sublinear_necessary
   ++ Q.EXISTS_TAC `Null`
   ++ Q.EXISTS_TAC `Int 0`
   ++ RW_TAC std_ss []);

val _ = export_theory();
