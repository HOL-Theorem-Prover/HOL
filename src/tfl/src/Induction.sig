signature Induction =
sig
  type term = Term.term
  type thm  = Thm.thm
  type thry = TypeBase.typeBase

   val mk_induction 
     : thry -> {fconst : term, R : term, SV : term list,
                pat_TCs_list: (term * term list) list}
            -> thm

end;
