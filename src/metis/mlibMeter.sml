(* ========================================================================= *)
(* METERING TIME AND INFERENCES                                              *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon", "mlibMatch"];
*)

(*
*)
structure mlibMeter :> mlibMeter =
struct

open mlibUseful;

infix |-> ::> @> oo ## ::* ::@;

(* ------------------------------------------------------------------------- *)
(* Search limits                                                             *)
(* ------------------------------------------------------------------------- *)

type limit = {time : real option, infs : int option};

val unlimited = {time = NONE, infs = NONE};

val expired = {time = SOME 0.0, infs = SOME 0};

fun limit_to_string {time, infs} =
  "{time = " ^
   (case time of NONE => "unlimited"
    | SOME r => Real.fmt (StringCvt.FIX (SOME 3)) r ^ "s") ^
   ", infs = " ^
   (case infs of NONE => "unlimited" | SOME i => int_to_string i) ^
   "}";

(* ------------------------------------------------------------------------- *)
(* mlibMeter readings.                                                           *)
(* ------------------------------------------------------------------------- *)

type meter_reading = {time : real, infs : int};

val zero_reading = {time = 0.0, infs = 0};

fun add_readings {time : real, infs} {time = time', infs = infs'} =
  {time = time + time', infs = infs + infs'};

fun pp_meter_reading pp {time, infs} =
  let
    open PP
    val () = begin_block pp INCONSISTENT 1
    val () = add_string pp "{";
    val () = begin_block pp INCONSISTENT 2
    val () = add_string pp "time ="
    val () = add_break pp (1, 0)
    val () = add_string pp (Real.fmt (StringCvt.FIX (SOME 3)) time)
    val () = end_block pp
    val () = add_string pp ","
    val () = add_break pp (1, 0)
    val () = begin_block pp INCONSISTENT 2
    val () = add_string pp "infs ="
    val () = add_break pp (1, 0)
    val () = pp_int pp infs
    val () = end_block pp
    val () = add_string pp "}"
    val () = end_block pp
  in
    ()
  end;

fun meter_reading_to_string r =
  PP.pp_to_string (!LINE_LENGTH) pp_meter_reading r;

(* ------------------------------------------------------------------------- *)
(* mlibMeters record time and inferences.                                        *)
(* ------------------------------------------------------------------------- *)

type meter = {read : unit -> meter_reading, log : (int -> unit), lim : limit};

fun new_time_meter () =
  let
    val tmr = Timer.startCPUTimer ()
    fun read () =
      (fn {usr, sys, ...} => Time.+ (usr, sys))
      (Timer.checkCPUTimer tmr)
  in
    pos o Time.toReal o read
  end;

fun new_inference_meter () =
  let
    val infs = ref 0
    fun read () = !infs
  in
    (read, fn n => infs := !infs + n)
  end;

fun new_meter lim : meter =
  let
    val tread = new_time_meter ()
    val (iread,ilog) = new_inference_meter ()
  in
    {read = (fn () => {time = tread (), infs = iread ()}),
     log = ilog, lim = lim}
  end;

fun sub_meter {read, log, lim = _} lim =
  let
    val {time = init_time : real, infs = init_infs} = read ()
    fun sub {time, infs} =
      {time = pos (time - init_time), infs = infs - init_infs}
  in
    {read = sub o read, log = log, lim = lim}
  end;

val read_meter = fn ({read, ...} : meter) => read ();

val check_meter = fn ({read, lim = {time, infs}, ...} : meter) =>
  let
    val {time = t, infs = i} = read ()
  in
    (case time of NONE => true | SOME time => t < time) andalso
    (case infs of NONE => true | SOME infs => i < infs)
  end;

val record_infs = fn ({log, ...} : meter) => log;

val pp_meter = pp_map read_meter pp_meter_reading;

end
