structure fspathTrie :> fspathTrie =
struct

datatype t = FSPT of (string,t)Binarymap.dict
  (* map to a tree whose only key is "" to show that prefix ends here *)

val e_dict = Binarymap.mkDict String.compare
val empty = FSPT e_dict
val truet = FSPT (Binarymap.insert(e_dict, "", empty))

(* We're treating all the prefixes in the tree as directories, for which the
   OS.Path representation has a trailing "" element in the arcs list *)
fun checkPath s =
    let
      val {isAbs,vol,arcs} = OS.Path.fromString s
      val _ = isAbs orelse raise Fail ("fspathTrie: relative path " ^ s)
      val _ = vol = "" orelse raise Fail ("fspathTrie: don't use volumes: " ^ s)
    in
      if List.last arcs = "" then arcs else arcs @ [""]
    end

fun insertPath s t =
    let fun recurse p (FSPT t) =
            case p of
                [] => raise Fail "fspathTrie.insertPath empty path"
              | [""] => truet
              | c::cs =>
                case Binarymap.peek(t,c) of
                    NONE => FSPT (Binarymap.insert(t,c,recurse cs empty))
                  | SOME t' => FSPT (Binarymap.insert(t,c,recurse cs t'))
    in
      recurse (checkPath s) t
    end

fun hasPrefix (FSPT t) s =
    let fun recurse acc p t =
            case p of
                [] => NONE
              | c::cs =>
                case Binarymap.peek (t, c) of
                    NONE => NONE
                  | SOME (FSPT t') =>
                    if isSome (Binarymap.peek(t',"")) then
                      SOME
                        (OS.Path.toString
                           {vol="", isAbs = false, arcs = List.rev (c::acc)})
                    else
                      recurse (c::acc) cs t'
    in
      recurse [] (checkPath s) t
    end

end;
