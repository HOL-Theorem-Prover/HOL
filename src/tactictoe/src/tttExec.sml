(* ========================================================================== *)
(* FILE          : tttExec.sml                                                *)
(* DESCRIPTION   : Execute SML strings                                        *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttExec :> tttExec =
struct

open HolKernel Abbrev boolLib tttTools tttTimeout tttLexer Tactical

val ERR = mk_HOL_ERR "tttExec"

(* -----------------------------------------------------------------------------
   Global references
   -------------------------------------------------------------------------- *)

val ttt_bool_glob = ref false
val ttt_tacticl_glob = ref []
val ttt_tactic_glob = ref (FAIL_TAC "tttExec")
val ttt_qtactic_glob = ref (fn _ => FAIL_TAC "tttExec")
val ttt_string_glob = ref ""
val ttt_goal_glob = ref ([],F)

(* -----------------------------------------------------------------------------
   Execute strings as sml code
   -------------------------------------------------------------------------- *)

fun exec_sml file s =
  let
    val path = ttt_code_dir ^ "/" ^ current_theory () ^ "_" ^ file
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
    val s2 = tttLexer.ttt_lex s1
  in
    case s2 of
      [a] => (drop_sig a = "thm" handle _ => false)
    | _   => false
  end

(* -----------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

val ttt_thm = ref TRUTH

val ttt_thml : thm list ref = ref []

fun is_thm s = exec_sml "is_thm" ("val _ = Thm.dest_thm (" ^ s ^ ")")

fun thm_of_sml s =
  let val b = exec_sml "thm_of_sml" ("tttExec.ttt_thm := " ^ s) in
    if b then SOME (s, !ttt_thm) else NONE
  end

fun thml_of_sml sl =
  let
    val s = "[" ^ String.concatWith ", " sl ^ "]"
    val b = exec_sml "thm_of_sml" ("tttExec.ttt_thml := " ^ s)
  in
    if b then SOME (combine (sl, !ttt_thml)) else NONE
  end

fun namespace_thms () =
  let
    val l0 = #allVal (PolyML.globalNameSpace) ()
    val l1 = filter (is_thm_value l0) (map fst l0)
  in
    case thml_of_sml l1 of
      SOME l2 => l2
    | NONE => List.mapPartial thm_of_sml l1
  end

fun safe_namespace_thms () =
  let
    val l0 = #allVal (PolyML.globalNameSpace) ()
    val l1 = (map fst l0)
  in
    List.mapPartial thm_of_sml l1
  end


fun is_tactic s = exec_sml "is_tactic" ("val _ = Tactical.VALID (" ^ s ^ ")")

fun is_string s = exec_sml "is_string" ("val _ = String.isPrefix (" ^ s ^ ")")

fun is_pointer_eq s1 s2 =
  let
    val b = exec_sml "is_pointer_eq"
              ("val _ = tttExec.ttt_bool_glob := PolyML.pointerEq (" ^
               s1 ^ "," ^ s2 ^ ")")
  in
    b andalso (!ttt_bool_glob)
  end

(* -----------------------------------------------------------------------------
   Read tactics
   -------------------------------------------------------------------------- *)

val ttt_invalid_flag = ref false

fun mk_valid s = "Tactical.VALID (" ^ s ^ ")"

fun tactic_of_sml s =
  let
    val tactic = mk_valid s
    val program =
      "let fun f () = tttExec.ttt_tactic_glob := (" ^ tactic ^ ") in " ^
      "tttTimeout.timeOut 1.0 f () end"
    val b = exec_sml "tactic_of_sml" program
  in
    if b then !ttt_tactic_glob else raise ERR "tactic_of_sml" s
  end

fun qtactic_of_sml s =
  let
    val program =
      "let fun f () = tttExec.ttt_qtactic_glob := (" ^ s ^ ") in " ^
      "tttTimeout.timeOut 0.1 f () end"
    val b = exec_sml "qtactic_of_sml" program
  in
    if b then !ttt_qtactic_glob else raise ERR "qtactic_of_sml" s
  end


(* -----------------------------------------------------------------------------
   Apply tactics
   -------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_tac tim tac g =
  SOME (fst (timeOut tim (TC_OFF tac) g))
  handle _ => NONE

fun app_qtac tim tac g =
  timeOut tim (trace ("show_typecheck_errors", 0) tac) g
  handle _ => NONE

fun rec_stac tim stac g =
  let val tac = tactic_of_sml stac in
    SOME (fst (timeOut tim (TC_OFF tac) g))
  end
  handle _ => NONE

fun rec_sproof stac g =
  let
    val tac = tactic_of_sml stac
    val tim = Time.toReal (!ttt_search_time)
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
      ("val _ = tttExec.ttt_string_glob := (" ^ s ^ " )")
  in
    if b then !ttt_string_glob else raise ERR "string_of_sml" s
  end

val ttt_term_glob = ref T
val ttt_termlist_glob = ref [T]

fun is_stype s =
  let
    fun not_in cl c = not (mem c cl)
    fun test c = not_in [#"\t",#"\n",#" ",#"\""] c
  in
    List.find test (explode (rm_comment (rm_squote s))) = SOME #":"
  end

fun term_of_sml s =
  let
    val b = exec_sml "term_of_sml"
      ("val _ = tttExec.ttt_term_glob := " ^
       "Parse.Term [HolKernel.QUOTE " ^ s ^ "]")
  in
    if b
    then !ttt_term_glob
    else raise ERR "term_of_sml" s
  end

fun hol4terml_of_sml i s =
  let
    val b = exec_sml ("hol4terml_of_sml" ^ int_to_string i)
      ("val _ = tttExec.ttt_termlist_glob := " ^ s)
  in
    if b
    then !ttt_termlist_glob
    else raise ERR "hol4term_of_sml" s
  end


(* -----------------------------------------------------------------------------
   Read metis and hh from the future
   -------------------------------------------------------------------------- *)

val hh_stac_glob:
  (string -> 
     (int, real) Redblackmap.dict *
     (string * fea_t) list *
     (string, goal * int list) Redblackmap.dict ->
   int -> goal -> string option) ref =
  ref (fn _ => (fn _ => (fn _ => (fn _ => NONE))))

fun update_hh_stac () =
  let
    val b = exec_sml "update_hh_stac"
      (
      String.concatWith "\n"
      [
      "load \"holyHammer\";",
      "val _ = tttExec.hh_stac_glob := holyHammer.hh_stac;"
      ]
      )
  in
    if b then () else raise ERR "update_hh_stac" ""
  end

val create_fof_glob:
  (string -> thm -> unit) ref = ref (fn _ => (fn _ => ()))

fun update_create_fof () =
  let
    val b = exec_sml "update_create_fof"
      (
      String.concatWith "\n"
      [
      "load \"holyHammer\";",
      "val _ = tttExec.create_fof_glob := holyHammer.create_fof;"
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
      "val _ = tttExec.metis_tac_glob := SOME metisTools.METIS_TAC;"
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
      ("val _ = tttExec.ttt_goal_glob := (" ^ s ^ " )")
  in
    if b then !ttt_goal_glob else raise ERR "goal_of_sml" s
  end

end (* struct *)
