(* ========================================================================= *)
(* METERING TIME AND INFERENCES                                              *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
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

fun pp_limit pp {time,infs} =
  let
    open PP
    val () = begin_block pp INCONSISTENT 1
    val () = add_string pp "{";
    val () = begin_block pp INCONSISTENT 2
    val () = add_string pp "time ="
    val () = add_break pp (1,0)
    val () =
      case time of NONE => add_string pp "unlimited"
      | SOME t => add_string pp (Real.fmt (StringCvt.FIX (SOME 3)) t)
    val () = end_block pp
    val () = add_string pp ","
    val () = add_break pp (1,0)
    val () = begin_block pp INCONSISTENT 2
    val () = add_string pp "infs ="
    val () = add_break pp (1,0)
    val () =
      case infs of NONE => add_string pp "unlimited"
      | SOME i => add_string pp (int_to_string i)
    val () = end_block pp
    val () = add_string pp "}"
    val () = end_block pp
  in
    ()
  end;

fun limit_to_string l = PP.pp_to_string (!LINE_LENGTH) pp_limit l;

(* ------------------------------------------------------------------------- *)
(* mlibMeter readings.                                                           *)
(* ------------------------------------------------------------------------- *)

type meter_reading = {time : real, infs : int};

val zero_reading = {time = 0.0, infs = 0};

fun add_readings {time : real, infs} {time = time', infs = infs'} =
  {time = time + time', infs = infs + infs'};

val pp_meter_reading =
  pp_map (fn {time,infs} => {time = SOME time, infs = SOME infs}) pp_limit;

fun meter_reading_to_string r =
  PP.pp_to_string (!LINE_LENGTH) pp_meter_reading r;

(* ------------------------------------------------------------------------- *)
(* mlibMeters record time and inferences.                                        *)
(* ------------------------------------------------------------------------- *)

type meter =
  {rdt : unit -> real, rdi : unit -> int, log : (int -> unit), lim : limit};

fun new_time_meter () =
  let
    val tmr = Timer.startCPUTimer ()
    fun read () =
      (fn {usr,sys,...} => Time.+ (usr,sys))
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
  let val (rdi,log) = new_inference_meter ()
  in {rdt = new_time_meter (), rdi = rdi, log = log, lim = lim}
  end;

fun sub_meter ({rdt, rdi, log, lim = _} : meter) lim =
  let
    val init_time = rdt () and init_infs = rdi ()
    fun sbt time = pos (time - init_time)
    fun sbi infs = infs - init_infs
  in
    {rdt = sbt o rdt, rdi = sbi o rdi, log = log, lim = lim}
  end;

fun record_infs ({log,...} : meter) = log;

fun read_infs ({rdi,...} : meter) = rdi ();

fun read_meter ({rdt,rdi,...} : meter) = {time = rdt (), infs = rdi ()};

fun check_meter ({rdt, rdi, lim = {time, infs}, ...} : meter) =
  (case time of NONE => true | SOME time => rdt () < time) andalso
  (case infs of NONE => true | SOME infs => rdi () < infs);

val pp_meter = pp_map read_meter pp_meter_reading;

end
