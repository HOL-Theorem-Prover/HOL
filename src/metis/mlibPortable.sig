(* ========================================================================= *)
(* ML SPECIFIC FUNCTIONS                                                     *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibPortable =
sig

(* The ML implementation *)
val ml : string

(* Pointer equality using the run-time system *)
val pointer_eq : 'a -> 'a -> bool

(* Timing function applications *)
val time : ('a -> 'b) -> 'a -> 'b

(* MD5 cryptographic hashing *)
val md5 : string -> string

end
