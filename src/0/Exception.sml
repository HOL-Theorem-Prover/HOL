(* ===================================================================== *)
(* FILE          : exception.sml                                         *)
(* DESCRIPTION   : This defines a single error format for hol90. There   *)
(*                 is one exception constructor:                         *)
(*                                                                       *)
(*                     HOL_ERR : {origin_structure:string,               *)
(*                                origin_function:string,                *)
(*                                message:string} -> exn                 *)
(*                                                                       *)
(*                 It takes three strings: the structure name, what      *)
(*                 routine it is being raised in, and what the message   *)
(*                 is. There is an (assignable) function for printing    *)
(*                 HOL_ERRs, plus an experimental function Raise that    *)
(*                 will print out exceptions at the site of occurrence.  *)
(*                 It may prove to be helpful in debugging.              *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 12, 1991                                    *)
(*                                                                       *)
(* Modified      : 27 October, 1991, E. L. Gunter                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)


structure Exception  :> Exception =
struct

exception HOL_ERR of {origin_structure:string,
		      origin_function:string,
		      message:string}

fun print_HOL_ERR (HOL_ERR sss) = !Globals.output_HOL_ERR sss
  | print_HOL_ERR _ = print_HOL_ERR(HOL_ERR{origin_structure="Exception",
                                            origin_function="print_HOL_ERR",
                                            message="not a HOL error"})

fun Raise (e as HOL_ERR sss) = 
     ( if (!Globals.print_exceptions)
       then !Globals.output_HOL_ERR sss else ();
       raise e)
  | Raise (e as _) = raise e

end  (* EXCEPTION *)
