signature splitLib =
sig
  include Abbrev

  (* One split of a term, with the first rule that applies.  The rules
     are analysed when the conversion is built. *)
  val SPLIT_CONV : thm list -> conv

  (* Splits the first assumption that one of the assumption rules applies
     to; one that merely mentions a rule's constant is passed over. *)
  val SPLIT_ASM_TAC : thm list -> tactic

  (* One split, of the conclusion if possible, else of an assumption *)
  val SPLIT_TAC : thm list -> tactic

  (* The assumption-splitting form of a conclusion split rule *)
  val mk_asm_split : thm -> thm

  (* A rule analysed as the splitter uses it.  split_forms th gives the
     forms of th that are applied: an assumption rule as it is, and a
     conclusion rule together with its mk_asm_split form.  SPLIT_RULE_TAC
     is SPLIT_TAC over analysed rules. *)
  type split_rule
  val split_forms : thm -> split_rule list
  val SPLIT_RULE_TAC : split_rule list -> tactic

  (* Datatype case split rules: for the conclusion, for assumptions, and
     both *)
  val type_split_of : hol_type -> thm
  val type_asm_split_of : hol_type -> thm
  val type_split_rules : hol_type -> thm list

  (* The datatype split rules for the case constants applied to all their
     arguments in the terms; the first form groups them by type. *)
  val goal_split_rule_groups : term list -> (hol_type * thm list) list
  val goal_split_rules : term list -> thm list

  (* The groups by the TypeBase of the given context *)
  val goal_split_rule_groups_of :
      Context.t -> term list -> (hol_type * thm list) list

  (* Enables the persistent [split] theorem attribute; see its help entry
     for use in theory scripts.  Fails if another split attribute is
     registered.  Repeating the call has no effect, but it must be called
     again after Context.restore to a point before it. *)
  val enable_split_attribute : unit -> unit

  (* Retracts the [split] rule [Thy.]name, in the current theory and its
     descendants; an unqualified name is in the current theory.  Fails if
     the attribute is not enabled. *)
  val exclude_split : string -> unit

  (* The [split] rules; none if the attribute is not enabled *)
  val split_thms : unit -> thm list
  val named_split_thms : unit -> (string * thm) list

  (* The [split] rules of the given context; none if the attribute is not
     enabled there *)
  val named_split_thms_of : Context.t -> (string * thm) list

  (* Whether a split rule splits assumptions, and the name a split rule
     is known by (in del_split and ExclX "split:...") *)
  val is_asm_split : thm -> bool
  val split_thm_name : thm -> string
end
