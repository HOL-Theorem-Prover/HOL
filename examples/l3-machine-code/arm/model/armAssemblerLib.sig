signature armAssemblerLib =
sig
   val init: unit -> unit
   val arm_code: 'a frag list -> string list
   val arm_code_with_warnings: 'a frag list -> string list * assemblerLib.lines
   val print_arm_code: 'a frag list -> unit
end
