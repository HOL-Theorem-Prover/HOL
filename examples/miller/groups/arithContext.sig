signature arithContext =
sig

  type subtype_context_element = subtypeTools.subtype_context_element
  type precontext = subtypeTools.precontext
  type context = subtypeTools.context

  (* Subtype checking *)

  (* Contextual rewriting *)
  val arith_pc : precontext;
  val arith_c : context;

end

