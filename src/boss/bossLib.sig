signature bossLib =
sig

  include Abbrev
  type fixity   = Parse.fixity
  type simpset  = simpLib.simpset

  (* Make definitions *)

  val Hol_datatype : hol_type quotation -> unit
  val Define       : term quotation -> thm
  val xDefine      : string -> term quotation -> thm
  val Hol_defn     : string -> term quotation -> defn
  val Hol_reln     : term quotation -> thm * thm * thm
  val WF_REL_TAC   : term quotation -> tactic

  (* Fetch the rewrite rules for a type. *)

  val type_rws : string -> thm list

  (* Case-splitting and induction operations *)

  val Cases             : tactic
  val Induct            : tactic
  val recInduct         : thm -> tactic
  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic

  (* Support for proof by contradiction *)

  val SPOSE_NOT_THEN : (thm -> tactic) -> tactic

  (* Support for assertional-style proofs *)

  val by  : term quotation * tactic -> tactic   (* infix *)


  (* First order proof automation *)

  val PROVE     : thm list -> term quotation -> thm
  val PROVE_TAC : thm list -> tactic

  (* Cooperating decision procedures *)

  val DECIDE     : term quotation -> thm
  val DECIDE_TAC : tactic

  (* Simplification *)

  val std_ss   : simpset   (* bool + option + pair + sum *)
  val arith_ss : simpset
  val list_ss  : simpset
  val &&       : simpset * thm list -> simpset  (* infix && *)
  val RW_TAC   : simpset -> thm list -> tactic
  val EVAL     : term quotation -> thm

  (* A compound automated reasoner. *)

  val ZAP_TAC  : simpset -> thm list -> tactic


end;
