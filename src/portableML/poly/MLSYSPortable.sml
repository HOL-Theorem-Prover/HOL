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

fun md5sum s =
  let
    val mstate = MD5.update (MD5.init, Byte.stringToBytes s)
    val hash = MD5.final mstate
  in
    MD5.toBase64String hash
  end;

fun time f x =
  let
    fun p t =
      let
        val s = Time.fmt 3 t
      in
        case size (List.last (String.fields (fn x => x = #".") s)) of 3 => s
        | 2 => s ^ "0"
        | 1 => s ^ "00"
        | _ => raise Fail "mlibPortable.time"
      end
    val c = Timer.startCPUTimer ()
    val r = Timer.startRealTimer ()
    fun pt () =
      let
        val {usr, sys, gc} = Timer.checkCPUTimer c
        val real = Timer.checkRealTimer r
      in
        print
        ("User: " ^ p usr ^ "  System: " ^ p sys ^
         "  GC: " ^ p gc ^ "  Real: " ^ p real ^ "\n")
      end
    val y = f x handle e => (pt (); raise e)
    val () = pt ()
  in
    y
  end;

structure HOLSusp = Susp

end;
