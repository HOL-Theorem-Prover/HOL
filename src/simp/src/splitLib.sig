signature splitLib =
sig
  include Abbrev

  (* Analyse the supplied rules when the conversion is constructed. *)
  val SPLIT_CONV : thm list -> conv

  (* Split the first assumption an assumption rule applies to.  Naming a
     rule's head constant does not make an assumption splittable, so a
     later assumption is reached when an earlier one only mentions it. *)
  val SPLIT_ASM_TAC : thm list -> tactic

  (* Perform one split, preferring the conclusion to assumptions. *)
  val SPLIT_TAC : thm list -> tactic

  (* Derive the assumption-splitting form of a conclusion split rule. *)
  val mk_asm_split : thm -> thm

  (* A rule as the splitter analyses it.  [split_forms] answers the
     forms of one rule the splitter applies -- an assumption rule as it
     stands, a conclusion rule together with the assumption rule
     [mk_asm_split] derives from it -- already analysed, so that a
     caller deciding which of the two a rule is gets that answer out of
     the analysis the splitter goes on to use rather than out of a walk
     of its own.  [SPLIT_RULE_TAC] is [SPLIT_TAC] over rules so
     analysed. *)
  type split_rule
  val split_forms : thm -> split_rule list
  val SPLIT_RULE_TAC : split_rule list -> tactic

  (* Cached datatype split rules.  [type_split_rules] is the derived pair
     the splitter applies. *)
  val type_split_of : hol_type -> thm
  val type_asm_split_of : hol_type -> thm
  val type_split_rules : hol_type -> thm list

  (* Datatype split rules whose case constants occur as saturated
     applications in the supplied terms.  The grouped form lets a caller
     apply per-type policy without repeating the goal walk. *)
  val goal_split_rule_groups : term list -> (hol_type * thm list) list
  val goal_split_rules : term list -> thm list

  (* Explicitly claim the persistent [split] attribute with private rule storage.
     Idempotent once enabled in the current Context; an existing split
     attribute or generic split theorem set is rejected before mutation.
     A removed dispatcher is restored by identity without replay; a
     foreign function under the dispatcher's name is rejected.
     Call before using [split] or loading theories whose data must replay.
     Exported theories explicitly load splitPersistLib and record it with
     Theory.add_ML_dependency on the earliest split-bearing theory.
     No simpLib dependency is needed for this initialization. Registration
     and rules follow Context.restore; after rewinding before opt-in,
     call this API again rather than relying on a cached module load.
     Serialized theory initialization, not a concurrent proof operation.
     Registers no generic ThmSetData set. *)
  val enable_split_attribute : unit -> unit

  (* Persistently retract [Thy.]Name, resolving an unqualified name in the
     current theory. Requires enabled registration; never implicitly opts in.
     Unlike simpExtLib.del_split this writes a REMOVE for descendant replay.
     Retracting an absent name is harmless. Does not delete the theorem.
     REMOVE keys stay resolved across replay and Context.restore.
     Pinned contexts reject writes, including initialization above. *)
  val exclude_split : string -> unit

  (* The private persistent [split] rules.  Before opt-in these return []
     without registering or adopting data.
     Pure/local and TypeBase splitting never require opt-in. *)
  val split_thms : unit -> thm list
  val named_split_thms : unit -> (string * thm) list

  (* Registration helpers used by simpExtLib. *)
  val is_asm_split : thm -> bool
  val split_thm_name : thm -> string
end
