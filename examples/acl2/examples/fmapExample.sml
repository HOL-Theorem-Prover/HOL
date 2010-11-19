(*****************************************************************************)
(* Test script for encoding using finite maps.                               *)
(* This is based on the opsem script with translations placed after each     *)
(* definition to mark progress.                                              *)
(*****************************************************************************)

set_trace "Unicode" 0;
set_trace "pp_annotations" 0;

app load ["acl2encodeLib", "stringLib", "finite_mapTheory", "intLib",
          "pred_setTheory","whileTheory","optionTheory","unwindLib", "finite_mapTheory"];
open HolKernel Parse boolLib bossLib
     stringLib IndDefLib IndDefRules finite_mapTheory relationTheory
     arithmeticTheory prim_recTheory
     pred_setTheory whileTheory combinTheory optionTheory unwindLib;
intLib.deprecate_int();
clear_overloads_on "TC"; (* Stop TC R printing as TC^+ *)


val _ =
 Hol_datatype
  `value = Scalar of int | Array  of (num |-> int)`;

val _ = acl2encodeLib.initialise_type ``:value``;

val _ = type_abbrev("state", ``:string |-> value``);
val _ = type_abbrev("sfun",  ``:state  ->  state``);
val _ = type_abbrev("pred",  ``:state  ->  bool``);
val _ = type_abbrev("vars",  ``:string ->  bool``);

val isScalar_def =
 Define
  `(isScalar(Scalar n) = T) /\ (isScalar(Array a) = F)`;

val _ = acl2encodeLib.translate_simple_function [(``isScalar``, "acl2isScalar")] isScalar_def;

val ScalarOf_def =
 Define
  `ScalarOf(Scalar n) = n`;

val _ = acl2encodeLib.translate_simple_function [(``ScalarOf``, "acl2ScalarOf")] ScalarOf_def;

val isArray_def =
 Define
  `(isArray(Array a) = T) /\ (isArray(Scalar n) = F)`;

val _ = acl2encodeLib.translate_simple_function [(``isArray``, "acl2isArray")] isArray_def;

val ArrayOf_def =
 Define
  `ArrayOf(Array a) = a`;

val _ = encodeLib.set_bottom_value ``:num |-> int`` ``FEMPTY : num |-> int``;

val _ = acl2encodeLib.translate_simple_function [(``ArrayOf``, "acl2ArrayOf")] ArrayOf_def;

(*---------------------------------------------------------------------------*)
(* Syntax of the programming language.					     *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Natural number (nexp), boolean (bexp) and array expressions (aexp)        *)
(* are defined by datatypes with simple evaluation semantics.                *)
(*---------------------------------------------------------------------------*)

val _ =
 Hol_datatype
  `nexp = Var of string
        | Arr of string => nexp
        | Const of int
        | Plus of nexp => nexp
        | Sub of nexp => nexp
        | Times of nexp => nexp
        | Div of nexp => nexp
        | Min of nexp => nexp`;

val _ = acl2encodeLib.initialise_type ``:nexp``;

val _ =
 Hol_datatype
  `bexp = Equal of nexp => nexp
        | Less of nexp => nexp
        | LessEq of nexp => nexp
        | Greater of nexp => nexp
        | GreaterEq of nexp => nexp
        | And of bexp => bexp
        | Or of bexp => bexp
        | Not of bexp`;

val _ = acl2encodeLib.initialise_type ``:bexp``;


val neval_def =
 Define
  `(neval (Var v) s = ScalarOf(s ' v)) /\
   (neval (Arr a e) s = (ArrayOf(s ' a) ' (Num(neval e s)))) /\
   (neval (Const c) s = c) /\
   (neval (Plus e1 e2) s = integer$int_add (neval e1 s) (neval e2 s)) /\
   (neval (Sub e1 e2) s = integer$int_sub (neval e1 s) (neval e2 s)) /\
   (neval (Times e1 e2) s = integer$int_mul (neval e1 s) (neval e2 s)) /\
   (neval (Div e1 e2) s = integer$int_quot (neval e1 s) (neval e2 s)) /\
   (neval (Min e1 e2) s = integer$int_min (neval e1 s) (neval e2 s))`;

(*****************************************************************************)
(* neval is not a complete function. It cannot complete if any variable in   *)
(* the expression is not in the environment. Therefore, we must define an    *)
(* auxilliary function to determine when a call to neval is safe             *)
(*                                                                           *)
(* Unfortunately, this will rely on neval to determine array indices.        *)
(* To avoid a mutually recurse translation we define 'safe_neval' that acts  *)
(* as 'neval' but returns 0 where 'neval' would stop evaluating.             *)
(*****************************************************************************)

val safe_neval_def = 
  Define 
  `(safe_neval (Var v) s = if v IN FDOM s /\ isScalar (s ' v) then ScalarOf(s ' v) else 0i) /\
   (safe_neval (Arr a e) s = if a IN FDOM s /\ isArray (s ' a) /\ integer$int_le 0i (safe_neval e s) /\ Num (safe_neval e s) IN FDOM (ArrayOf (s ' a)) then (ArrayOf(s ' a) ' (Num(safe_neval e s))) else 0i) /\
   (safe_neval (Const c) s = c) /\
   (safe_neval (Plus e1 e2) s = integer$int_add (safe_neval e1 s) (safe_neval e2 s)) /\
   (safe_neval (Sub e1 e2) s = integer$int_sub (safe_neval e1 s) (safe_neval e2 s)) /\
   (safe_neval (Times e1 e2) s = integer$int_mul (safe_neval e1 s) (safe_neval e2 s)) /\
   (safe_neval (Div e1 e2) s = if safe_neval e2 s = 0i then 0i else integer$int_quot (safe_neval e1 s) (safe_neval e2 s)) /\
   (safe_neval (Min e1 e2) s = integer$int_min (safe_neval e1 s) (safe_neval e2 s))`;

(*****************************************************************************)
(* We can then use this to define nevaluates as follows:                     *)
(*****************************************************************************)

val nevaluates_def = 
  Define `(nevaluates (Var v) s = v IN FDOM s /\ isScalar (s ' v)) /\
          (nevaluates (Arr a e) s = a IN FDOM s /\ isArray (s ' a) /\ integer$int_le 0i (safe_neval e s) /\ nevaluates e s /\ Num (safe_neval e s) IN FDOM (ArrayOf (s ' a))) /\
	  (nevaluates (Const c) s = T) /\
	  (nevaluates (Plus e1 e2) s = nevaluates e1 s /\ nevaluates e2 s) /\
	  (nevaluates (Sub e1 e2) s = nevaluates e1 s /\ nevaluates e2 s) /\
	  (nevaluates (Times e1 e2) s = nevaluates e1 s /\ nevaluates e2 s) /\
	  (nevaluates (Div e1 e2) s = ~(safe_neval e2 s = 0i) /\ nevaluates e1 s /\ nevaluates e2 s) /\
	  (nevaluates (Min e1 e2) s = nevaluates e1 s /\ nevaluates e2 s)`;

(*****************************************************************************)
(* ...and prove that this implies we are correct.                            *)
(*****************************************************************************)

val neval_safe_theorem1 = store_thm("neval_safe_theorem1",
    ``!e s. nevaluates e s ==> (safe_neval e s = neval e s)``,
    Induct THEN RW_TAC std_ss [nevaluates_def, safe_neval_def, neval_def]);

(*****************************************************************************)
(* We now begin by translating safe_neval.                                   *)
(*****************************************************************************)

val ONE_ONE_str = prove(``ONE_ONE str``, RW_TAC std_ss [ONE_ONE_THM]);
val ONE_ONE_nat = prove(``ONE_ONE nat``, RW_TAC std_ss [ONE_ONE_THM, sexpTheory.nat_def, translateTheory.INT_CONG, integerTheory.INT_INJ]);

val _ = acl2encodeLib.translate_conditional_function [(``safe_neval``,"acl2safe_neval")] [ONE_ONE_str, ONE_ONE_nat] safe_neval_def;

val _ = acl2encodeLib.translate_conditional_function [(``nevaluates``,"acl2nevaluates")] [ONE_ONE_str, ONE_ONE_nat] nevaluates_def;

(*****************************************************************************)
(* The next stage is to translate neval as a 'limit' function using          *)
(* nevaluates as the limit.                                                  *)
(*****************************************************************************)

(*

val _ =
 Hol_datatype
  `aexp = ArrConst  of (num |-> int)           (* array constant *)
        | ArrVar    of string                  (* array variable *)
        | ArrUpdate of aexp => nexp => nexp`;  (* array update   *)

val _ = acl2encodeLib.initialise_type ``:aexp``;

val beval_def =
 Define
  `(beval (Equal e1 e2) s = (neval e1 s = neval e2 s)) /\
   (beval (Less e1 e2) s = integer$int_lt (neval e1 s) (neval e2 s)) /\
   (beval (LessEq e1 e2) s = integer$int_le (neval e1 s) (neval e2 s)) /\
   (beval (Greater e1 e2) s = integer$int_gt (neval e1 s) (neval e2 s)) /\
   (beval (GreaterEq e1 e2) s = integer$int_ge (neval e1 s) (neval e2 s)) /\
   (beval (And b1 b2) s = (beval b1 s /\ beval b2 s)) /\
   (beval (Or b1 b2) s = (beval b1 s \/ beval b2 s)) /\
   (beval (Not e) s = ~(beval e s))`;

val aeval_def =
 Define
  `(aeval (ArrConst f) s = f)
   /\
   (aeval (ArrVar v) s = ArrayOf(s ' v))
   /\
   (aeval (ArrUpdate a e1 e2) s = aeval a s |+ (Num(neval e1 s), neval e2 s))`;

val naeval_def =
 Define
  `(naeval (INL e) s = Scalar(neval e s))
   /\
   (naeval (INR a) s = Array(aeval a s))`;

val Update_def =
 Define
  `Update v e s = s |+ (v, naeval e s)`;

val UpdateCases =
 store_thm
  ("UpdateCases",
   ``(Update v (INL e) s = s |+ (v, Scalar(neval e s)))
     /\
     (Update v (INR a) s = s |+ (v, Array(aeval a s)))``,
   RW_TAC std_ss [Update_def,naeval_def]);

(* Convert a value or array to a constant expression *)
val Exp_def =
 Define
  `(Exp(Scalar n) = INL(Const n))
   /\
   (Exp(Array f)  = INR(ArrConst f))`;

val Update_Exp =
 store_thm
  ("Update_Exp",
   ``!v val s. Update v (Exp val) s = s |+ (v, val)``,
   Cases_on `val`
    THEN RW_TAC std_ss [UpdateCases,Exp_def,aeval_def,neval_def]);

val _ = acl2encodeLib.translate_conditional_function [(``neval``, "acl2neval")] [] neval_def;


val tf_def = Define `tf (x : int |-> int) = if 0i IN FDOM x then x ' 0i else 0i`;

val oneone_int = ONEONE_ENC_THM ``:int``;

val _ = acl2encodeLib.translate_conditional_function [(``tf``, "test_tf")] [oneone_int] tf_def handle e => acl2encodeLib.Raise e;
*)