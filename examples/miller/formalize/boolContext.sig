signature boolContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)
  val bool_sc : subtype_context_element list;

  (* Contextual rewriting *)
  val bool_pc : precontext;
  val bool_c : context;

end

