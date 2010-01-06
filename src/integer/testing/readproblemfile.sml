structure readproblemfile :> readproblemfile =
struct
open HolKernel boolLib

open TextIO
fun readterm is = let
  fun readtilemptyline acc =
      case inputLine is of
        SOME s => if s = "\n" then
                    SOME (SOME (Parse.Term
                                    [QUOTE (String.concat (List.rev acc))]))
                    handle HOL_ERR _ => SOME NONE
                  else readtilemptyline (s::acc)
      | NONE => NONE
in
  readtilemptyline []
end

fun foldl f acc is =
  case readterm is of
    NONE => acc
  | SOME t => foldl f (f(t,acc)) is

fun app f = foldl (fn (t,_) => ignore (f t)) ()

end
