signature HolLex =
   sig
     val makeLexer  : (int -> string) 
                      -> Term.term list ref 
                      -> unit 
                      -> (HolUserDeclarations.svalue,
                          HolUserDeclarations.pos) HolTokens.token
   end

