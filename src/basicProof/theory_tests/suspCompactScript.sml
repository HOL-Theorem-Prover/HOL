(*  At export, markerLib drops each suspension add that a later remove
    in the same theory cancels, keeping every remove.  Counts the adds
    and removes the ancestors' theory files keep. *)

Theory suspCompact[bare]
Ancestors suspNone suspCrossB suspCrossThm suspSibD

Libs HolKernel Parse boolLib markerLib

fun count pat s =
    let
      val n = size pat
      fun recurse i acc =
          if i + n > size s then acc
          else if String.substring (s, i, n) = pat then
            recurse (i + n) (acc + 1)
          else recurse (i + 1) acc
    in
      recurse 0 0
    end

fun check thy store expected =
    let
      val data = Theory.LoadableThyData.segment_data_string
                   {thy = thy, thydataty = "suspension." ^ store ^ ".deltas"}
      val got = Option.map (fn s => (count "(add" s, count "(rm" s)) data
      fun pr NONE = "no data"
        | pr (SOME (a, r)) = Int.toString a ^ " adds, " ^
                             Int.toString r ^ " removes"
    in
      if got = expected then ()
      else raise Fail (thy ^ " " ^ store ^ ": expected " ^ pr expected ^
                       ", got " ^ pr got)
    end

(* no suspensions: no data written *)
val _ = check "suspNone" "theorems" NONE
val _ = check "suspNone" "resumptions" NONE

(* suspended here, resumed and finalised in suspCrossB: the add stays *)
val _ = check "suspCrossA" "theorems" (SOME (1, 0))
(* resumed and finalised here: only the removes stay *)
val _ = check "suspCrossB" "theorems" (SOME (0, 1))
val _ = check "suspCrossB" "resumptions" (SOME (0, 1))

(* suspended, resumed and finalised in one theory *)
val _ = check "suspCrossThm" "theorems" (SOME (0, 2))
val _ = check "suspCrossThm" "resumptions" (SOME (0, 2))

(* resumptions in sibling theories, finalised in suspSibD *)
val _ = check "suspSibA" "theorems" (SOME (1, 0))
val _ = check "suspSibB" "resumptions" (SOME (1, 0))
val _ = check "suspSibC" "resumptions" (SOME (1, 0))
val _ = check "suspSibD" "theorems" (SOME (0, 1))
val _ = check "suspSibD" "resumptions" (SOME (0, 1))

val _ =
    List.app
      (fn n => case lookup_suspension n of
                   NONE => ()
                 | SOME _ => raise Fail (n ^ " still suspended"))
      ["cross_thm", "th1", "th2", "sib_thm"]
