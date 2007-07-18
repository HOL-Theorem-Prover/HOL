(* ========================================================================= *)
(* Create "syntaxTheory" containing the syntax of a small imperative         *)
(* probabilistic language.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory;
open posetTheory posrealTheory posrealLib expectationTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "syntax"                                        *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "syntax";

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
(* The HOL type we use to model states                                       *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("state", Type `:string -> 'a`);

val assign_def = Define
  `assign v (e : 'a state -> 'a) (s:'a state) w = if v = w then e s else s w`;

val assign_eta = store_thm
  ("assign_eta",
   ``!v e s. assign v e s = \w. if w = v then e s else s w``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss [assign_def]);

(* ------------------------------------------------------------------------- *)
(* Probabilisitic programs: syntax                                           *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `command =
       Abort
     | Consume of ('a state -> posreal)
     | Assign of string => ('a state -> 'a)
     | Seq of command => command
     | Nondet of command => command
     | Prob of ('a state -> posreal) => command => command
     | While of ('a state -> bool) => command`;

val Assert_def = Define
  `Assert (x : 'a state -> posreal) (c : 'a command) = c`;

val Skip_def = Define `Skip = Consume (\s. 0)`;

val Program_def = Define
  `(Program [] = Skip) /\
   (Program [c] = c) /\
   (Program (c :: c' :: cs) = Seq c (Program (c' :: cs)))`;

val If_def = Define `If c a b = Prob (\s. if c s then 1 else 0) a b`;

(* wp (Nondets []) should evaluate to the identity for Nondet, which is *)
(* Magic. But we don't allow magic (i.e., miraculous) programs, so we *)
(* underspecify Nondets to avoid this nasty case. *)

val Nondets_def = Define
  `(Nondets [x] = x) /\
   (Nondets (x :: y :: z) = Nondet x (Nondets (y :: z)))`;

val NondetAssign_def = Define
  `NondetAssign v xs = Nondets (MAP (\x. Assign v (\s. x)) xs)`;

val guards_def = Define
  `(guards cs [] = if cs = [] then Abort else Nondets cs) /\
   (guards cs ((p, c) :: rest) =
    If p (guards (c :: cs) rest) (guards cs rest))`;

val Guards_def = Define `Guards l = guards [] l`;

val (Probs_def, _) = Defn.tprove
  (Defn.Hol_defn "Probs_def"
   `(Probs [] = Abort) /\
    (Probs ((p, x) :: rest) =
     Prob (\v. p) x (Probs (MAP (\ (q, y). (q / (1 - p), y)) rest)))`,
   TotalDefn.WF_REL_TAC `measure LENGTH`
   ++ RW_TAC list_ss []);

val _ = save_thm ("Probs_def", Probs_def);

val ProbAssign_def = Define
  `ProbAssign v xs =
   Probs (MAP (\x. (1 / & (LENGTH xs), Assign v (\s. x))) xs)`;

val For_def = Define
   `For i init cond incr c =
  	Seq (Assign i init)
	    (While cond (Seq (Program c) (Assign i incr)))`;

val WhileProgram_def = Define `WhileProgram c l = While c (Program l)`;

val _ = export_theory();
