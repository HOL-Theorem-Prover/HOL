signature Induction =
sig
  include Abbrev
  type thry = TypeBasePure.typeBase

   val mk_induction
     : thry -> {fconst : term, R : term, SV : term list,
                pat_TCs_list: (term * term list) list}
            -> thm

end;
