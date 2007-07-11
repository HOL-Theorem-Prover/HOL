signature basic_evalLib =
sig
   include Abbrev

   val eval      : int * term * term * term -> thm
end
