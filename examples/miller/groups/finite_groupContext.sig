signature finite_groupContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)

  (* Contextual rewriting *)
  val finite_group_pc : precontext;
  val finite_group_c : context;

end

