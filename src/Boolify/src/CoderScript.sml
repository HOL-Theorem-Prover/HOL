(*===========================================================================*)
(* Showing Encoding and Decoding to be inverse operations.                   *)
(*===========================================================================*)

(* Interactive mode
app load ["rich_listTheory", "EncodeTheory", "DecodeTheory"];
*)

open HolKernel boolLib Parse bossLib pairTheory pairTools
     arithmeticTheory listTheory rich_listTheory EncodeTheory
     mesonLib optionTheory DecodeTheory;

val REVERSE = Tactical.REVERSE;

val _ = new_theory "Coder";

(*---------------------------------------------------------------------------
     decode turns a decoding parser of type
       bool list -> ('a # bool list) option
     into a straight function of type
       bool list -> 'a

     domain parser identifies the set of bool lists where it is valid
     to apply decode parser (i.e., any bool list l such that parser l
     results in a successful parse with no bools remaining: SOME (t, []))
 ---------------------------------------------------------------------------*)

val decode_def = Define `decode f = FST o THE o f`;

val domain_exists = store_thm
  ("domain_exists",
   ``?d. !f x. x IN d f = ?y. f x = SOME (y, [])``,
   Q.EXISTS_TAC `\f x. ?y. f x = SOME (y, [])` THEN
   SIMP_TAC bool_ss [IN_DEF]);

val domain_def =
  Definition.new_specification
  ("domain_def", ["domain"], domain_exists);

val _ = add_const "domain";

val inverse_def = Define
  `inverse e l =
   if ?x t. l = APPEND (e x) t then SOME (@(x, t). l = APPEND (e x) t)
   else NONE`;

val inverse_none = prove
  (``!e l. (inverse e l = NONE) = (!x t. ~(l = APPEND (e x) t))``,
   RW_TAC std_ss [inverse_def] THEN
   POP_ASSUM MP_TAC THEN
   RW_TAC std_ss []);

(*   
val inverse_some = prove
  (``!e l x t.
       wf_encoder e ==>
       ((inverse e l = SOME (x, t)) = (l = APPEND (e x) t))``,
*)

val _ = export_theory ();
