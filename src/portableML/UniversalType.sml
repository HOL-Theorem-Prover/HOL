structure UniversalType :> UniversalType =
struct

  (* stolen from MLton webpage: http://mlton.org/UniversalType *)
type t = exn

fun 'a embed () = let
  exception E of 'a
  fun project (e: t): 'a option =
      case e of
        E a => SOME a
      | _ => NONE
in
  (E, project)
end
end (* struct *)
