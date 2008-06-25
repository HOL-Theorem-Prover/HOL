(* ========================================================================= *)
(* MOSCOW ML SPECIFIC FUNCTIONS                                              *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

structure mlibPortable :> mlibPortable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "polyml";

(* ------------------------------------------------------------------------- *)
(* Ensuring that interruptions (SIGINTs) are actually seen by the            *)
(* linked executable as Interrupt exceptions.                                *)
(* ------------------------------------------------------------------------- *)

(*
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;
*)

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

fun pointer_eq a b = PolyML.pointerEq (a, b);

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
