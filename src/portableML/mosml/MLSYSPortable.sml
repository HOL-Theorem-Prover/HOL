structure MLSYSPortable =
struct

exception Interrupt = General.Interrupt

val listDir = Mosml.listDir

(*---------------------------------------------------------------------------
    Efficiency hack.
 ---------------------------------------------------------------------------*)

local val cast : 'a -> int = Obj.magic
in
fun pointer_eq (x:'a, y:'a) = (cast x = cast y)
fun ref_to_int (r : 'a ref) = cast r
end;

local
  (* magic to ensure that interruptions (SIGINTs) are actually seen by the
    linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
in

fun catch_SIGINT () = ignore (catch_interrupt true)

val md5sum = Mosml.md5sum
val time = Mosml.time

end

structure HOLSusp = Susp

end (* struct *)
