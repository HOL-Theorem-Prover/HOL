(* DFA.sig *)

signature DFA =
sig

  val make_dfa : Syntax.rules ->
                   (string * int) list * (* initial state indexes *)
                   Syntax.automata Array.array * (* state array *)
		   (int * Syntax.location) list list (* actions *)
end
