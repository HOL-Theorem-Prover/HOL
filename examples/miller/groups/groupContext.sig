signature groupContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)

  (* Contextual rewriting *)
  val group_pc : precontext;
  val group_c : context;

end

