structure MLSYSPortable =
struct

exception Interrupt = SML90.Interrupt

fun listDir s = let
  val ds = FileSys.openDir s
  fun recurse acc =
      case FileSys.readDir ds of
        NONE => acc
      | SOME f => recurse (f :: acc)
in
  recurse [] before FileSys.closeDir ds
end



fun pointer_eq (x:'a, y:'a) = PolyML.pointerEq(x,y)
fun ref_to_int (x : 'a ref) = 0 (* needs fixing *)

fun catch_SIGINT () = ()


end;
