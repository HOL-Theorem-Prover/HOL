signature numContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)
  val num_sc : subtype_context_element list;

  (* Contextual rewriting *)
  val num_pc : precontext;
  val num_c : context;

end

