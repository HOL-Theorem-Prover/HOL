signature optionLib =
sig
  include optionSyntax

   val option_rws : thm
   val OPTION_rws : computeLib.compset -> unit
end;
