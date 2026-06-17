structure HM_Progress :> HM_Progress =
struct

val total = ref 0

(* U+2193 DOWNWARDS ARROW in UTF-8 (3 bytes, 1 display column).
   Marks the count-down variant of the progress field so the reader
   sees "decreasing" rather than mistaking the number for a built
   count. *)
val down_arrow = "\226\134\147"

fun init announce n =
    (total := n;
     if n > 0 then
       announce ("Building " ^ Int.toString n ^
                 " theory file" ^ (if n = 1 then "" else "s"))
     else ())

fun note_completion g ok cmd =
    if ok then
      case cmd of
          HM_DepGraph.BuiltInCmd
            (HM_DepGraph.BIC_BuildScript _, _) =>
              if !total > 0 then
                let val built = HM_DepGraph.theories_built g
                in
                  if !total <= 99 then
                    (* "[dd/dd]" fits in 7 display columns *)
                    SOME ("[" ^ Int.toString built ^
                          "/" ^ Int.toString (!total) ^ "]")
                  else
                    (* Count down to keep the field narrow *)
                    SOME ("[" ^ down_arrow ^
                          Int.toString (!total - built) ^ "]")
                end
              else NONE
        | _ => NONE
    else NONE

end
