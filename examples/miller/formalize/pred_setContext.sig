signature pred_setContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)
  val pred_set_sc : subtype_context_element list;

  (* Contextual rewriting *)
  val pred_set_pc : precontext;
  val pred_set_c : context;

end

