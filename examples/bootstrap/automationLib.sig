signature automationLib =
sig

    include Abbrev

    val to_deep : thm -> thm

    val parse_dec : term Portable.quotation -> term
    val parse_exp : term Portable.quotation -> term
    val define_code : term Portable.quotation -> thm
    val get_program : term -> term
    val update_mem : thm -> unit
    val write_hol_string_to_file : string -> term -> unit
    val apply_at_pat_conv : term -> conv -> conv
    val get_comments : unit -> term
    val attach_comment : term Portable.quotation -> unit

end
