(* ========================================================================= *)
(* Create "valueTheory"                                                      *)
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
Theory value
Ancestors
  combin list rich_list string integer real poset posreal
  expectation wp
Libs
  intLib realLib metisLib posrealLib


(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "value"                                         *)
(* ------------------------------------------------------------------------- *)

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

Datatype: value =
                Null
              | Int of int
              | Array of value list
End

(* ------------------------------------------------------------------------- *)
(* Useful Functions for Turning Values into nums or ints                     *)
(* ------------------------------------------------------------------------- *)

Definition int_of_value_def:
    int_of_value (Int i) = i
End

Definition num_of_value_def:
    num_of_value i = Num (int_of_value i)
End

(* ------------------------------------------------------------------------- *)
(* Definitions for dealing with Array assignment                             *)
(* ------------------------------------------------------------------------- *)

Definition update_nth_def:
  (update_nth l 0 v = v :: TL l) /\
  (update_nth l (SUC n) v = HD l :: update_nth (TL l) n v)
End

Theorem update_nth_length:
    !l n v.
      n < LENGTH l ==> (LENGTH (update_nth l n v) = LENGTH l)
Proof
  Induct_on `n`
  ++ Cases_on `l`
  ++ RW_TAC arith_ss [update_nth_def, HD, TL, LENGTH]
QED

Theorem update_nth_el:
    !n v l k.
      n < LENGTH l /\ k < LENGTH l ==>
      (EL k (update_nth l n v) = if k = n then v else EL k l)
Proof
  Induct_on `n`
  ++ Cases_on `l`
  ++ Cases_on `k`
  ++ RW_TAC arith_ss [EL, update_nth_def, HD, TL, LENGTH]
QED

(* use EL n l instead of get_nth *)

(* use SNOC for reverse of CONS *)

Definition update_Array_i_def:
    update_Array_i (Array l) i v = Array (update_nth l i v)
End

Definition get_Array_i_def:
    get_Array_i (Array l) i = EL i l
End

Definition Array_length_def:
    Array_length (Array l) = LENGTH l
End

Theorem update_Array_i_length:
    !a i v.
      (?l. (a = Array l)) /\ i < Array_length a ==>
          (Array_length (update_Array_i a i v) = Array_length a)
Proof
  RW_TAC arith_ss []
  ++ FULL_SIMP_TAC arith_ss [Array_length_def, update_Array_i_def, update_nth_length]
  ++ MATCH_MP_TAC update_nth_length
QED

Theorem update_Array_i_el:
    !i v a k. (?l. (a = Array l)) /\
      i < Array_length a /\ k < Array_length a ==>
      (get_Array_i (update_Array_i a i v) k = if k = i then v else get_Array_i a k)
Proof
  RW_TAC arith_ss []
   ++ FULL_SIMP_TAC arith_ss [update_Array_i_def, get_Array_i_def, Array_length_def]
   ++ RW_TAC arith_ss [update_nth_el]
QED

Definition extend_Array_def:
   extend_Array (Array l) v = Array (SNOC v l)
End

Theorem extend_Array_length:
    !a v. (?l. (a = Array l)) ==> ((Array_length (extend_Array a v)) = ((Array_length a) + 1))
Proof
  RW_TAC arith_ss []
  ++ RW_TAC arith_ss [extend_Array_def, Array_length_def, LENGTH_SNOC]
QED

Theorem extend_Array_el:
     !a v i. (?l. (a = Array l)) /\
             i < SUC(Array_length a) ==>
               (get_Array_i (extend_Array a v) i =
                  if (i = (Array_length a)) then v else get_Array_i a i)
Proof
  RW_TAC arith_ss []
  ++ FULL_SIMP_TAC arith_ss [get_Array_i_def, extend_Array_def, Array_length_def, EL_SNOC, EL_LENGTH_SNOC]
QED

Definition Assign_Array_num_i:
    Assign_Array_num_i v i (e:value state -> value) = Assign v (\s. update_Array_i (s v) i (e s))
End

Definition Assign_Array_i:
    Assign_Array_i v i (e:value state -> value) =
       Assign v (\(s:value state). update_Array_i (s v) (num_of_value(s i)) (e s))
End

Definition Assign_Array_extend:
    Assign_Array_extend v (e:value state -> value) = Assign v (\(s:value state). extend_Array (s v) (e s))
End

Definition Assign_Array_empty:
    Assign_Array_empty v = Assign v (\s. Array [])
End

Definition n_list_def:
    (n_list 0 x = []) /\
    (n_list (SUC n) x = x::(n_list (n) x))
End

Theorem length_of_n_list:
     !n x. LENGTH (n_list n x) = n
Proof
   REPEAT STRIP_TAC
   ++ Induct_on `n`
   ++ RW_TAC arith_ss [LENGTH, n_list_def]
QED

Definition New_Array:
    New_Array a n = Assign a (\s. Array (n_list (num_of_value (s n)) Null))
End

Definition NondetAssign_Array_num_i_def:
    NondetAssign_Array_num_i a i xs =
        Nondets (MAP (\x. Assign_Array_num_i a i (\s. x)) xs)
End

Definition NondetAssign_Array_i_def:
    NondetAssign_Array_i a i xs =
        Nondets (MAP (\x. Assign_Array_i a i (\s. x)) xs)
End

Definition ProbAssign_Array_num_i_def:
    ProbProbAssign_Array_num_i a i xs =
        Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_num_i a i (\s. x))) xs)
End

Definition ProbAssign_Array_i_def:
    ProbAssign_Array_i a i xs =
        Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_i a i (\s. x))) xs)
End

Definition NondetAssign_Array_extend_def:
    NondetAssign_Array_extend a xs =
        Nondets (MAP (\x. Assign_Array_extend a (\s. x)) xs)
End

Definition ProbAssign_Array_extend_def:
    ProbAssign_Array_extend a xs =
        Probs (MAP (\x. (1/ & (LENGTH xs), Assign_Array_extend a (\s. x))) xs)
End

Definition For_0_to_n_def:
    For_0_to_n i n l = For i (\s. Int 0) (\s. (int_of_value(s i)) < (int_of_value(s n))) (\s. Int ((int_of_value(s i)) + 1)) l
End

(* ------------------------------------------------------------------------- *)
(* Showing the need for SUB-linearity for value states.                      *)
(* ------------------------------------------------------------------------- *)

Theorem sublinear_necessary_value:
     ?p : value command. ?r1 r2 s.
       wp p r1 s + wp p r2 s < wp p (\s'. r1 s' + r2 s') s
Proof
   MATCH_MP_TAC sublinear_necessary
   ++ Q.EXISTS_TAC `Null`
   ++ Q.EXISTS_TAC `Int 0`
   ++ RW_TAC std_ss []
QED

