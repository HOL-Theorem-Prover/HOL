signature core_decompilerLib =
sig

   val configure: {pc_tm: Term.term,
                   init_fn: unit -> unit,
                   pc_conv: Conv.conv -> Conv.conv,
                   triple_fn: string -> helperLib.instruction,
                   component_vars: Term.term list} -> unit

   val core_decompile: string -> Term.term quotation -> Thm.thm * Thm.thm

end
