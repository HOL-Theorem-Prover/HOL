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

end;
