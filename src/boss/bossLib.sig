signature bossLib =
sig

local
  type thm      = Thm.thm
  type term     = Term.term
  type hol_type = Type.hol_type
  type fixity   = Parse.fixity
  type tactic   = Abbrev.tactic
  type simpset  = simpLib.simpset
  type defn     = Defn.defn
  type 'a quotation = 'a Portable.frag list
in

  (* Make definitions *)

  val Hol_datatype : hol_type quotation -> unit
  val Hol_fun      : string -> term quotation -> defn
  val xDefine      : string -> term quotation -> thm
  val Define       : term quotation -> thm

  val ind_suffix : string ref
  val def_suffix : string ref

  (* Fetch the rewrite rules for a type. *)

  val type_rws : string -> thm list

  (* Case-splitting and induction operations *)

  val Cases     : tactic
  val Induct    : tactic
  val Cases_on  : term quotation -> tactic
  val Induct_on : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val recInduct         : thm -> tactic

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
  val base_ss  : simpset
  val arith_ss : simpset
  val list_ss  : simpset
  val &&       : simpset * thm list -> simpset  (* infix && *)
  val RW_TAC   : simpset -> thm list -> tactic

  (* A compound automated reasoner. *)
  val ZAP_TAC  : simpset -> thm list -> tactic

end

end;
