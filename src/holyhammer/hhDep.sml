(* ===================================================================== *)
(* FILE          : hhDep.sml                                             *)
(* DESCRIPTION   : Accessing recorded dependencies. Associating          *)
(*                 identifiers with theorems.                            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhDep :> hhDep =
struct

open HolKernel Abbrev boolLib Tag Dep

val ERR = mk_HOL_ERR "hhDep"

(* Fetching theorem *)

fun thm_of_depid (thy,n) =
  let
    val thml = DB.thms thy
    fun find_number x =
      if (depnumber_of o depid_of o dep_of o tag o snd) x = n
      then x
      else raise ERR "find_number" ""
  in
    tryfind find_number thml 
    handle _ => raise ERR "thm_of_depid" "Not found"
  end

fun exists_depid did = can thm_of_depid did



end
