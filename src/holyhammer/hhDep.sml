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
      if (depnumber_of o depid_of_dep o dep_of o tag o snd) x = n
      then x
      else raise ERR "find_number" ""
  in
    tryfind find_number thml handle _ => raise ERR "thm_of_depid" "Not found"
  end

fun exists_depid did = can thm_of_depid did
fun exists_depconj (did,a) = exists_depid did

(* Fetching conjuncts *)

local 

fun fetch_conj_helper (thm,a) = case a of
    []             => thm
  | DEP_LEFT :: m  => fetch_conj_helper (CONJUNCT1 (SPEC_ALL thm), m)
  | DEP_RIGHT :: m => fetch_conj_helper (CONJUNCT2 (SPEC_ALL thm), m)

in

fun thm_of_depconj (did,a) =
  GEN_ALL (fetch_conj_helper (snd (thm_of_depid did), rev a))

fun hh_fetch_conj (thm,a) = 
  GEN_ALL (fetch_conj_helper (thm, rev (read_depaddress a)))

end
  
(* Fetching dependencies and removing erased dependencies *)

local 

fun dtree_of thm = case (dep_of o tag) thm of
    DEP_SAVED (did,dt1,dt2) => dt2
  | DEP_UNSAVED dt          => dt

in

fun dcl_of_thm thm = 
  let 
    val dt = dtree_of thm 
    val l = dest_depleaf (collapse_deptree dt) 
  in
    filter exists_depconj l
  end

fun deptree_of_thm thm =
  let fun loop dt =
        case dt of
          DEP_NODE(dt1,dt2) => DEP_NODE (loop dt1, loop dt2)
        | DEP_LEAF dcl      => DEP_LEAF (filter exists_depconj dcl)
  in
    loop (dtree_of thm)
  end

end

(* Print conjuncts returned by holyhammer *)

fun string_of_depconj ((thy,n),a) = 
  let val s = thy ^ "Theory." ^ fst (thm_of_depid (thy,n)) in
    if null a 
    then s
    else "hhDep.hh_fetch_conj (" ^ s ^ ",\"" ^ number_depaddress a ^ "\")"
  end

fun string_of_depconjl depconjl = 
  "[" ^ String.concatWith "," (map string_of_depconj depconjl) ^ "]"

end
