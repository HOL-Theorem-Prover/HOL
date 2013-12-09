signature quantHeuristicsLibFunRemove =
sig

  include Abbrev

  type quant_fun_remove_arg;

  val QUANT_FUN_REMOVE_CONV : quant_fun_remove_arg list -> conv
  val QUANT_FUN_REMOVE_ss   : quant_fun_remove_arg list -> simpLib.ssfrag

  (* very simple for to state that some function can be remove.
     First argument is a theorem of the form
       "IS_REMOVABLE_QUANT_FUN (\x. f x)".
     It is important, that there is lambda abstraction, but "f x" can be complicated
     and even contain free variables.

     The string is suffix used for the new variable names and the
     thm list is a list of rewrite theorems used carefully to bring every(!)
     occourence of x into an context of the form "f x".  *)

  val remove_thm_arg : thm -> string -> thm list -> quant_fun_remove_arg

end
