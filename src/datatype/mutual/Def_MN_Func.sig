signature Def_MN_Func =
sig 
  type term = Term.term
  type thm = Thm.thm
  type fixity = Term.fixity
  
   val define_mutual_functions 
         :{name:string,
           def : term,
           fixities : fixity list option,
           rec_axiom: thm} -> thm
end 