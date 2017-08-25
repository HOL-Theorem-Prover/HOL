(* ========================================================================== *)
(* FILE          : hhsExec.sml                                                *)
(* DESCRIPTION   : Execute SML strings                                        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsExec :> hhsExec = 
struct

open HolKernel Abbrev boolLib hhsTools hhsTimeout

val ERR = mk_HOL_ERR "hhsExec"

(* -----------------------------------------------------------------------------
   Global references
   -------------------------------------------------------------------------- *)

val hhs_bool_glob = ref false
val hhs_tacticl_glob = ref []
val hhs_string_glob = ref ""
val hhs_goal_glob = ref ([],F)

(* -----------------------------------------------------------------------------
   Execute strings as sml code
   -------------------------------------------------------------------------- *)

fun exec_sml file s =
  let
    val path = HOLDIR ^ "/src/tactictoe/code/" ^ file
    val oc = TextIO.openOut path
    fun os s = TextIO.output (oc,s)
  in
    os s;
    TextIO.closeOut oc;
    ((QUse.use path; true) handle _ => false)
  end

(* -----------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

fun is_thm s =
  exec_sml "is_thm" ("val _ = Thm.dest_thm (" ^ s ^ ")")

fun is_tactic s =
  exec_sml "is_tactic" ("val _ = Tactical.VALID (" ^ s ^ ")")

fun is_pointer_eq s1 s2 =
  let 
    val b = exec_sml "is_pointer_eq" 
              ("val _ = hhsExec.hhs_bool_glob := PolyML.pointerEq (" ^ 
               s1 ^ "," ^ s2 ^ ")")
  in
    b andalso (!hhs_bool_glob)
  end

(* -----------------------------------------------------------------------------
   Read tactics
   -------------------------------------------------------------------------- *)

fun tactic_of_sml s =
  let
    val b = exec_sml "tactic_of_sml" 
    ("val _ = hhsExec.hhs_tacticl_glob := [Tactical.VALID ( " ^ s ^ " )]")
  in
    if b then hd (!hhs_tacticl_glob) else raise ERR "tactic_of_sml" s
  end

fun tacticl_of_sml sl =
  let 
    fun mk_valid s = "Tactical.VALID ( " ^ s ^ " )"
    val tacticl = "[" ^ String.concatWith ", " (map mk_valid sl) ^ "]"
    val b = exec_sml "tacticl_of_sml" 
              ("val _ = hhsExec.hhs_tacticl_glob := " ^ tacticl)
  in
    if b then !hhs_tacticl_glob
      else raise ERR "tacticl_of_sml" (String.concatWith " " sl)
  end

(* -----------------------------------------------------------------------------
   Apply tactics
   -------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_tac tac g = 
  SOME (fst (timeOut (!hhs_tactic_time) (TC_OFF tac) g))
  handle _ => NONE

fun rec_stac stac g =
  let val tac = tactic_of_sml stac in
    SOME (fst (timeOut (2.0 * (!hhs_tactic_time)) (TC_OFF tac) g))
  end
  handle _ => NONE

fun rec_sproof stac g =
  let 
    val tac = tactic_of_sml stac
    val tim = 2.0 * (Time.toReal (!hhs_search_time))
  in
    SOME (fst (timeOut tim (TC_OFF tac) g))
  end
  handle _ => NONE
 
 
(* -----------------------------------------------------------------------------
   Read string
   -------------------------------------------------------------------------- *)

fun string_of_sml s =
  let 
    val b = exec_sml "string_of_sml" 
      ("val _ = hhsExec.hhs_string_glob := (" ^ s ^ " )")
  in
    if b then !hhs_string_glob else raise ERR "string_of_sml" s
  end

(* -----------------------------------------------------------------------------
   Read goal
   -------------------------------------------------------------------------- *)

fun goal_of_sml s =
  let 
    val b = exec_sml "goal_of_sml" 
      ("val _ = hhsExec.hhs_goal_glob := (" ^ s ^ " )")
  in
    if b then !hhs_goal_glob else raise ERR "goal_of_sml" s
  end
 
(* ---------------------------------------------------------------------------
   Finding the type of an expression.
   -------------------------------------------------------------------------- *)

val type_cache = ref (dempty String.compare)

fun type_of_sml s = 
  if dmem s (!type_cache) then dfind s (!type_cache) else
    let 
      val file = tactictoe_dir ^ "/code/sml_type_of_out"
      val cmd = "PolyML.print ( " ^ s ^ " );"
      val b   = hhsRedirect.hide file (exec_sml "sml_type_of") cmd
    in
      if b 
      then 
        let 
          val sl = hhsLexer.hhs_lex (last (readl file))
          val (_,tyl) = split_sl ":" sl
          val ty = String.concatWith " " tyl
        in
          (type_cache := dadd s ty (!type_cache); ty)
        end
      else (debug ("Error: type_of_sml: " ^ s); raise ERR "type_of_sml" s)
    end


  


end (* struct *)
