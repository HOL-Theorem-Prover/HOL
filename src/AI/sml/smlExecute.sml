(* ========================================================================= *)
(* FILE          : smlExecute.sml                                            *)
(* DESCRIPTION   : Execute SML strings                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlExecute :> smlExecute =
struct

open HolKernel Abbrev boolLib Tactical anotherLib smlTimeout smlLexer

val ERR = mk_HOL_ERR "smlExec"

val sml_dir = HOLDIR ^ "/src/AI/sml"
val sml_code_dir = sml_dir ^ "/code"

(* -------------------------------------------------------------------------
   Global references
   ------------------------------------------------------------------------- *)

val sml_bool_glob = ref false
val sml_tacticl_glob = ref []
val sml_tactic_glob = ref (FAIL_TAC "smlExec")
val sml_qtactic_glob = ref (fn _ => FAIL_TAC "smlExec")
val sml_string_glob = ref ""
val sml_goal_glob = ref ([],F)
val sml_term_glob = ref T
val sml_termlist_glob = ref [T]
val sml_thm_glob = ref TRUTH
val sml_thml_glob : thm list ref = ref []

(* -------------------------------------------------------------------------
   Execute strings as sml code
   ------------------------------------------------------------------------- *)

fun exec_sml file s =
  let
    val path = sml_code_dir ^ "/" ^ current_theory () ^ "_" ^ file
    val oc = TextIO.openOut path
    fun os s = TextIO.output (oc,s)
  in
    os s;
    TextIO.closeOut oc;
    can QUse.use path
  end




(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

fun is_thm s = exec_sml "is_thm" ("val _ = Thm.dest_thm (" ^ s ^ ")")

fun thm_of_sml s =
  let val b = exec_sml "thm_of_sml" ("smlExec.sml_thm_glob := " ^ s) in
    if b then SOME (s, !sml_thm_glob) else NONE
  end

fun thml_of_sml sl =
  let
    val s = "[" ^ String.concatWith ", " sl ^ "]"
    val b = exec_sml "thm_of_sml" ("smlExec.sml_thml_glob := " ^ s)
  in
    if b then SOME (combine (sl, !sml_thml_glob)) else NONE
  end



fun is_tactic s = exec_sml "is_tactic" ("val _ = Tactical.VALID (" ^ s ^ ")")

fun is_string s = exec_sml "is_string" ("val _ = String.isPrefix (" ^ s ^ ")")

fun is_pointer_eq s1 s2 =
  let
    val b = exec_sml "is_pointer_eq"
              ("val _ = smlExec.sml_bool_glob := PolyML.pointerEq (" ^
               s1 ^ "," ^ s2 ^ ")")
  in
    b andalso (!sml_bool_glob)
  end

(* -------------------------------------------------------------------------
   Read tactics
   ------------------------------------------------------------------------- *)

fun mk_valid s = "Tactical.VALID (" ^ s ^ ")"

fun tactic_of_sml s =
  let
    val tactic = mk_valid s
    val program =
      "let fun f () = smlExec.sml_tactic_glob := (" ^ tactic ^ ") in " ^
      "smlTimeout.timeOut 1.0 f () end"
    val b = exec_sml "tactic_of_sml" program
  in
    if b then !sml_tactic_glob else raise ERR "tactic_of_sml" s
  end

fun qtactic_of_sml s =
  let
    val program =
      "let fun f () = smlExec.sml_qtactic_glob := (" ^ s ^ ") in " ^
      "smlTimeout.timeOut 0.1 f () end"
    val b = exec_sml "qtactic_of_sml" program
  in
    if b then !sml_qtactic_glob else raise ERR "qtactic_of_sml" s
  end


(* -------------------------------------------------------------------------
   Apply tactics
   ------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_tac tim tac g =
  SOME (fst (timeOut tim (TC_OFF tac) g))
  handle Interrupt => raise Interrupt | _ => NONE

fun app_qtac tim tac g =
  timeOut tim (trace ("show_typecheck_errors", 0) tac) g
  handle Interrupt => raise Interrupt | _ => NONE

fun rec_stac tim stac g =
  let val tac = tactic_of_sml stac in
    SOME (fst (timeOut tim (TC_OFF tac) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE



(* todo: sml_search_time should be a parameter *)
val sml_search_time = 15.0

fun rec_sproof stac g =
  let val tac = tactic_of_sml stac in
    SOME (fst (timeOut sml_search_time (TC_OFF tac) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

(* -------------------------------------------------------------------------
   Read string
   ------------------------------------------------------------------------- *)

fun string_of_sml s =
  let
    val b = exec_sml "string_of_sml"
      ("val _ = smlExec.sml_string_glob := (" ^ s ^ " )")
  in
    if b then !sml_string_glob else raise ERR "string_of_sml" s
  end

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
      ("val _ = smlExec.sml_term_glob := " ^
       "Parse.Term [HolKernel.QUOTE " ^ s ^ "]")
  in
    if b
    then !sml_term_glob
    else raise ERR "term_of_sml" s
  end

fun hol4terml_of_sml i s =
  let
    val b = exec_sml ("hol4terml_of_sml" ^ int_to_string i)
      ("val _ = smlExec.sml_termlist_glob := " ^ s)
  in
    if b
    then !sml_termlist_glob
    else raise ERR "hol4term_of_sml" s
  end


(* -------------------------------------------------------------------------
   Import metis from the future
   ------------------------------------------------------------------------- *)

val metis_tac_glob: (thm list -> tactic) option ref = ref NONE

fun update_metis_tac () =
  let
    val b = exec_sml "update_metis_tac"
      (
      String.concatWith "\n"
      [
      "load \"metisTools\";",
      "val _ = smlExec.metis_tac_glob := SOME metisTools.METIS_TAC;"
      ]
      )
  in
    if b then () else raise ERR "update_metis_tac" ""
  end

(* ------------------------------------------------------------------------
   Read goal
   ------------------------------------------------------------------------ *)

fun goal_of_sml s =
  let
    val b = exec_sml "goal_of_sml"
      ("val _ = smlExec.sml_goal_glob := (" ^ s ^ " )")
  in
    if b then !sml_goal_glob else raise ERR "goal_of_sml" s
  end

(* ------------------------------------------------------------------------
   Prover wrapper
   ------------------------------------------------------------------------ *) 

fun time_prove prover tmax premises tm =
  let
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = prover thml
    val (r,t) = add_time (app_tac tmax tac) (mk_goal tm)
  in
    if r = SOME [] then SOME (tm,t) else NONE
  end

fun minimize_aux prover t l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if isSome (time_prove prover t (l1 @ m) tm)
    then minimize_aux prover t l1 m tm
    else minimize_aux prover t (a :: l1) m tm
    
fun miniprove prover t tml tm = 
  if isSome (time_prove prover t tml tm) 
  then SOME (minimize_aux prover t [] tml tm)
  else NONE

(* --------------------------------------------------------------------------
   Compiler tricks to extract theorem from the namespace
   ------------------------------------------------------------------------- *)

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
    val s2 = smlLexer.partial_sml_lexer s1
  in
    case s2 of
      [a] => (drop_sig a = "thm" handle _ => false)
    | _   => false
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

end (* struct *)
