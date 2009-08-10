(* =====================================================================*)
(* FILE          : mut_rec_ty.sig                                       *)
(* DESCRIPTION   : signature of theorems returned by MutRecDefFunc      *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter and Myra VanInwegen, based on comments   *)
(*                 by Tom Melham                                        *)
(* DATE          : 92.08.08                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature MutRecDef =
 sig
  type thm = Thm.thm

  val define_type
      : {type_name : string,
	 constructors : {name:string,
                         arg_info : TypeInfo.type_info list}list} list
         ->
           {New_Ty_Induct_Thm     :thm,
            New_Ty_Uniqueness_Thm :thm,
            New_Ty_Existence_Thm  :thm}
    end
