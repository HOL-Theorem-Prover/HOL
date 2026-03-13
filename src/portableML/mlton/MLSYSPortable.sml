structure MLSYSPortable =
struct

exception Interrupt = SML90.Interrupt

fun pointer_eq (x: 'a, y: 'a) = MLton.eq (x, y)
fun ref_to_int (x: 'a ref) = 0

fun listDir s =
  let
    val ds = OS.FileSys.openDir s
    fun recurse acc =
      case OS.FileSys.readDir ds of
        NONE => acc
      | SOME f => recurse (f :: acc)
  in
    recurse [] before OS.FileSys.closeDir ds
  end

fun catch_SIGINT () = ()

fun md5sum _ = raise Fail "md5sum not implemented"

fun time f x =
  let
    val t = Timer.startRealTimer ()
    val y = f x
    val elapsed = Timer.checkRealTimer t
  in
    print ("Real: " ^ Time.fmt 3 elapsed ^ "\n"); y
  end

structure HOLSusp = Susp

fun reraise e = raise e

fun display_exn f e = raise e

fun make_counter {inc, init} =
  let val counter = ref init
  in fn () => let val n = !counter in counter := n + inc; n end
  end

fun syncref init =
  let val v = ref init
  in
    {get = fn () => !v,
     upd = fn f => let val (r, v') = f (!v) in v := v'; r end}
  end

end
