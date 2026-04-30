structure simpfrag :> simpfrag =
struct

open Abbrev

type convdata = { name: string,
                  key: (term list * term) option,
                  trace: int,
                  conv: (term list -> term -> thm) -> term list -> conv}

type simpfrag = { convs: convdata list, rewrs: thm list}

val empty_simpfrag = {convs = [], rewrs = []};

fun add_rwts {convs, rewrs} newrwts = {convs = convs, rewrs = rewrs @ newrwts};

fun add_convs cds {convs, rewrs} = {convs = convs@cds, rewrs = rewrs}

val sconv_db : (thm -> convdata) Symtab.table ref = ref Symtab.empty

fun register_simpfrag_conv {name,code} =
  sconv_db := Symtab.update (name, code) (!sconv_db)

fun lookup_simpfrag_conv k = Symtab.lookup (!sconv_db) k

val simpfrag_conv_tag = "ssfrag_CONV"

end;
