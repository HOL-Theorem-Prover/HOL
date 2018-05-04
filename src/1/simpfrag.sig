signature simpfrag =
sig

  include Abbrev
  type convdata = { name: string,
                    key: (term list * term) option,
                    trace: int,
                    conv: (term list -> term -> thm) -> term list -> conv}

  type simpfrag = { convs: convdata list, rewrs: thm list}

  val empty_simpfrag : simpfrag
  val add_rwts : simpfrag -> thm list -> simpfrag
  val add_convs : convdata list -> simpfrag -> simpfrag

  val register_simpfrag_conv : {name: string, code: thm -> convdata} -> unit
  val lookup_simpfrag_conv : string -> (thm -> convdata) option
  val simpfrag_conv_tag : string  (* used to mark TypeBase extra sexps *)

end
