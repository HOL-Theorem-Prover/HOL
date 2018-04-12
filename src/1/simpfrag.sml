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

val sconv_db = ref (Binarymap.mkDict String.compare : (string,thm -> convdata) Binarymap.dict)

fun register_simpfrag_conv {name,code} =
  sconv_db := Binarymap.insert(!sconv_db, name, code)

fun lookup_simpfrag_conv k = Binarymap.peek(!sconv_db, k)

val simpfrag_conv_tag = "ssfrag_CONV"

end;
