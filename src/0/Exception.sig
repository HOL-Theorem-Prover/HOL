(* ===================================================================== *)
(* FILE          : Exception.sig                                         *)
(* DESCRIPTION   : Signature for HOL exceptions.                         *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 15, 1991                                    *)
(*                                                                       *)
(* Modified      : 27 October, 1991, E. L. Gunter                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)


signature Exception =
sig
    exception HOL_ERR of {origin_structure:string,
			  origin_function:string,
			  message:string}
    val print_HOL_ERR : exn -> unit
    val Raise : exn -> 'a
end;
