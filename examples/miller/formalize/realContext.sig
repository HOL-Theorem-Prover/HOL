signature realContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)
  val real_sc : subtype_context_element list;

  (* Contextual rewriting *)
  val real_pc : precontext;
  val real_c : context;

end

