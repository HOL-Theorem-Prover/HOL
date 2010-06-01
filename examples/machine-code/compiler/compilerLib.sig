signature compilerLib =
sig

  include Abbrev

  (* supported targets are "arm", "ppc" and "x86" *)

  (* mc_define defines a function and puts the definition on a queue
     waiting to be compiled, returns function definition and pre *)
  val mc_define        : term quotation -> thm * thm

  (* mc_compile fname target: compiles function fname to target code,
     returns a Hoare triple containing the generated code *)
  val mc_compile       : string -> string -> thm

  (* mc_compile_all fname: compiles function fname to all targets *)
  val mc_compile_all   : string -> (string * thm) list

  (* these functions expose the back-end functions *)
  val compile      : string -> term -> thm * thm * thm
  val compile_all  : term -> (string * thm) list * thm * thm

  (* the tactic used for proving function equivalence *)
  val COMPILER_TAC : tactic

end
