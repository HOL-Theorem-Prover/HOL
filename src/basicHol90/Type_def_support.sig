(* ===================================================================== *)
(* FILE          : type_def_support.sig                                  *)
(* DESCRIPTION   : Signature for routines supporting type definitions.   *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Type_def_support =
sig
    val ABS_REP_THM : Thm.thm
    val define_new_type_bijections :{name:string,
				     ABS:string,
				     REP:string,
				     tyax:Thm.thm} -> Thm.thm
    val prove_rep_fn_one_one : Thm.thm -> Thm.thm
    val prove_rep_fn_onto    : Thm.thm -> Thm.thm
    val prove_abs_fn_onto    : Thm.thm -> Thm.thm
    val prove_abs_fn_one_one : Thm.thm -> Thm.thm
end;
