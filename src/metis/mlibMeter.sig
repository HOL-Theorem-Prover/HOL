(* ========================================================================= *)
(* METERING TIME AND INFERENCES                                              *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibMeter =
sig

type 'a pp = 'a mlibUseful.pp

(* Search limits *)
type limit          = {time : real option, infs : int option}
val unlimited       : limit
val expired         : limit
val pp_limit        : limit pp
val limit_to_string : limit -> string

(* mlibMeter readings *)
type meter_reading          = {time : real, infs : int}
val zero_reading            : meter_reading
val add_readings            : meter_reading -> meter_reading -> meter_reading
val pp_meter_reading        : meter_reading pp
val meter_reading_to_string : meter_reading -> string

(* mlibMeters record time and inferences *)
type meter
val new_meter   : limit -> meter
val sub_meter   : meter -> limit -> meter
val record_infs : meter -> int -> unit
val read_meter  : meter -> meter_reading
val read_infs   : meter -> int
val check_meter : meter -> bool
val pp_meter    : meter pp

end
