(* ========================================================================== *)
(* FILE          : hhsExec.sml                                                *)
(* DESCRIPTION   : Execute SML strings                                        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsExec :> hhsExec = 
struct

open HolKernel Abbrev boolLib hhsTools hhsTimeout Tactical

val ERR = mk_HOL_ERR "hhsExec"

(* -----------------------------------------------------------------------------
   Global references
   -------------------------------------------------------------------------- *)

val hhs_bool_glob = ref false
val hhs_tacticl_glob = ref []
val hhs_tactic_glob = ref (FAIL_TAC "hhsExec")
val hhs_string_glob = ref ""
val hhs_goal_glob = ref ([],F)

(* -----------------------------------------------------------------------------
   Execute strings as sml code
   -------------------------------------------------------------------------- *)

fun exec_sml file s =
  let
    val path = 
      HOLDIR ^ "/src/tactictoe/code/" ^ current_theory () ^ "_" ^ file
    val oc = TextIO.openOut path
    fun os s = TextIO.output (oc,s)
  in
    os s;
    TextIO.closeOut oc;
    can QUse.use path
  end

(* -----------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

fun is_thm s = exec_sml "is_thm" ("val _ = Thm.dest_thm (" ^ s ^ ")")

fun is_tactic s = exec_sml "is_tactic" ("val _ = Tactical.VALID (" ^ s ^ ")")

fun is_string s = exec_sml "is_string" ("val _ = String.isPrefix (" ^ s ^ ")")

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

val hhs_invalid_flag = ref false

fun mk_valid s = if !hhs_invalid_flag then s else "Tactical.VALID (" ^ s ^ ")"

fun tacticl_of_sml sl =
  let
    val tacticl = "[" ^ String.concatWith ", " (map mk_valid sl) ^ "]"
    val programl =
      [
       "structure tactictoe_fake_struct = struct",
       "  val _ = hhsExec.hhs_tacticl_glob := " ^ tacticl,
       "end"
      ]
    val b = exec_sml "tacticl_of_sml" (String.concatWith "\n" programl)
  in
    if b then !hhs_tacticl_glob
      else raise ERR "tacticl_of_sml" (String.concatWith " " (first_n 10 sl))
  end

fun tactic_of_sml s = 
  let
    val tactic = mk_valid s
    val program = "val _ = hhsExec.hhs_tactic_glob := " ^ tactic
    val b = exec_sml "tactic_of_sml" program
  in
    if b then !hhs_tactic_glob else raise ERR "tactic_of_sml" s
  end
  
(* -----------------------------------------------------------------------------
   Apply tactics
   -------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_tac tim tac g = 
  SOME (fst (timeOut tim (TC_OFF tac) g))
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
   Read hh
   -------------------------------------------------------------------------- *)

val (hh_stac_glob: (goal -> string option) ref) = ref (fn x => NONE)

fun update_hh_stac () =
  let 
    val b = exec_sml "hh_stac_of_sml" 
      ("val _ = hhsExec.hh_stac_glob := holyHammer.hh_stac")
  in
    if b then () else raise ERR "hh_stac_of_sml" ""
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

fun after_last_colon_aux acc charl = case charl of
    #":" :: m => implode acc
  | a :: m => after_last_colon_aux (a :: acc) m
  | [] => raise ERR "after_last_colon" ""

fun after_last_colon s = after_last_colon_aux [] (rev (explode s))
 
fun drop_sig s = last (String.tokens (fn x => x = #".") s)
  
fun type_of_sml s = 
  if dmem s (!type_cache) then dfind s (!type_cache) else
    let 
      val file = tactictoe_dir ^ "/code/sml_type_of_out"
      val cmd = "PolyML.print ( " ^ s ^ " );"
      val b   = exec_sml "sml_type_of" cmd
    in
      if b 
      then 
        let 
          val s = after_last_colon (String.concatWith " " (readl file))
          val ty = String.concatWith " " (map drop_sig (hhsLexer.hhs_lex s))
        in
          (type_cache := dadd s (SOME ty) (!type_cache); SOME ty)
        end
      else 
        (
        debug ("Error: type_of_sml: " ^ s); 
        type_cache := dadd s NONE (!type_cache);
        NONE
        )
    end


end (* struct *)
