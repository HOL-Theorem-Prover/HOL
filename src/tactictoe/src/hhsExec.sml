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
   Type of values
   -------------------------------------------------------------------------- *)

fun string_of_pretty p =
  let
    val acc = ref []
    fun f s = acc := s :: !acc
  in
    PolyML.prettyPrint (f,80) p;
    String.concatWith " " (rev (!acc))
  end

fun drop_sig s = last (String.tokens (fn x => x = #".") s)

fun smltype_of_value l s =
  let
    val v = assoc s l handle _ => raise ERR "type_of_value" s
    val t = PolyML.NameSpace.Values.typeof v;
    val p = PolyML.NameSpace.Values.printType (t,0,NONE)
  in
    string_of_pretty p
  end

fun is_thm_value l s =
  let 
    val s1 = smltype_of_value l s
    val s2 = hhsLexer.hhs_lex s1
  in 
    case s2 of
      [a] => (drop_sig a = "thm" handle _ => false)
    | _   => false
  end

(* -----------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

val hhs_thm = ref TRUTH

fun is_thm s = exec_sml "is_thm" ("val _ = Thm.dest_thm (" ^ s ^ ")")

fun thm_of_sml s =
  let val b = exec_sml "thm_of_sml" ("hhsExec.hhs_thm := " ^ s) in
    if b then SOME (s, !hhs_thm) else NONE
  end

fun namespace_thms () =
  let 
    val l0 = #allVal (PolyML.globalNameSpace) () 
    val l1 = filter (is_thm_value l0) (map fst l0)
  in
    List.mapPartial thm_of_sml l1
  end

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
  
fun timed_tactic_of_sml s =
  let
    val tactic = mk_valid s
    val program = 
      "let fun f () = hhsExec.hhs_tactic_glob := " ^ tactic ^ " in " ^
      "hhsTimeout.timeOut 0.1 f () end"
    val b = exec_sml "tactic_of_sml" program
  in
    if b then !hhs_tactic_glob else raise ERR "timed_tactic_of_sml" s
  end

(* -----------------------------------------------------------------------------
   Apply tactics
   -------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_tac tim tac g = 
  SOME (fst (timeOut tim (TC_OFF tac) g))
  handle _ => NONE

fun rec_stac tim stac g =
  let val tac = tactic_of_sml stac in
    SOME (fst (timeOut tim (TC_OFF tac) g))
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
   Read metis and hh from the future
   -------------------------------------------------------------------------- *)

val (hh_stac_glob: 
   (int -> (int, real) Redblackmap.dict * (string * fea_t) list ->
    int -> goal -> string option) ref) = 
  ref (fn _ => (fn _ => (fn _ => (fn _ => NONE))))

fun update_hh_stac () =
  let 
    val b = exec_sml "update_hh_stac" 
      (
      String.concatWith "\n"
      [
      "load \"holyHammer\";",
      "val _ = hhsExec.hh_stac_glob := holyHammer.hh_stac;"
      ]
      )
  in
    if b then () else raise ERR "update_hh_stac" ""
  end

val metis_tac_glob: (thm list -> tactic) option ref = ref NONE

fun update_metis_tac () =
  let 
    val b = exec_sml "update_metis_tac" 
      (
      String.concatWith "\n"
      [
      "load \"metisTools\";",
      "val _ = hhsExec.metis_tac_glob := SOME metisTools.METIS_TAC;"
      ]
      )
  in
    if b then () else raise ERR "update_metis_tac" ""
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
 
end (* struct *)
