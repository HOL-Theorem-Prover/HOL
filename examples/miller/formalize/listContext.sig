signature listContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)
  val list_sc : subtype_context_element list;

  (* Contextual rewriting *)
  val list_pc : precontext;
  val list_c : context;

end

