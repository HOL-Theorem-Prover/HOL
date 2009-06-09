signature export_codeLib =
sig

    include Abbrev

    val write_code_to_file   : string -> thm -> unit

end
