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

end;
