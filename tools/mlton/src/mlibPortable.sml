(* ========================================================================= *)
(* MLTON SPECIFIC FUNCTIONS                                                  *)
(* Created by Joe Hurd, September 2002                                       *)
(* ========================================================================= *)

structure mlibPortable :> mlibPortable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "MLton";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

fun pointer_eq x y = MLton.eq (x,y);

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* MD5 cryptographic hashing.                                                *)
(* ------------------------------------------------------------------------- *)

fun md5 s =
  let
    val mstate = MD5.update (MD5.init, Byte.stringToBytes s)
    val hash = MD5.final mstate
  in
    MD5.toBase64String hash
  end;

end
