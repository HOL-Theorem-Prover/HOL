signature Def_MN_Func =
sig
  type term = Term.term
  type thm = Thm.thm

   val define_mutual_functions
         :{name:string,
           def : term,
           fixities : Parse.fixity list option,
           rec_axiom: thm} -> thm
end