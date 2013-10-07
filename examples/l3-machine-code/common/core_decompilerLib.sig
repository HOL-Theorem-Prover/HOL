signature core_decompilerLib =
sig

   val configure: {pc_tm: Term.term,
                   init_fn: unit -> unit,
                   triple_fn: string -> helperLib.instruction,
                   swap_fn: Term.term -> Term.term} -> unit

   val core_decompile: string -> Term.term quotation -> Thm.thm * Thm.thm

end
