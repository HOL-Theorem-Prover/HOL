structure readproblemfile :> readproblemfile =
struct
open HolKernel boolLib

open TextIO
fun readterm is = let
  fun readtilemptyline acc = let
    val line = inputLine is
  in
    if line = "\n" then
      SOME (SOME (Parse.Term [QUOTE (String.concat (List.rev acc))]))
      handle HOL_ERR _ => SOME NONE
    else if line = "" then NONE
    else readtilemptyline (line::acc)
  end
in
  readtilemptyline []
end

fun foldl f acc is =
  case readterm is of
    NONE => acc
  | SOME t => foldl f (f(t,acc)) is

fun app f = foldl (fn (t,_) => ignore (f t)) ()

end
