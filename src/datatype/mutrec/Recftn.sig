signature Recftn =
sig
  type term = Term.term
  type fixity = Parse.fixity
  type thm  = Thm.thm

  val define_mutual_functions
      : {name:string,
         def : term,
         fixities : fixity list option,
         rec_axiom: thm} -> thm
end;
