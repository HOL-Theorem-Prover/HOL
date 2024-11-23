(* ========================================================================= *)
(* FILE          : smlExecute.sml                                            *)
(* DESCRIPTION   : Execute SML strings                                       *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlExecute :> smlExecute =
struct

open HolKernel Abbrev boolLib Tactical aiLib smlTimeout smlLexer

val ERR = mk_HOL_ERR "smlExec"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val sml_bool_glob = ref false
val sml_tactic_glob = ref (FAIL_TAC "smlExecute")
val sml_string_glob = ref ""
val sml_goal_glob = ref ([],F)
val sml_thm_glob = ref TRUTH
val sml_thml_glob = ref []

(* -------------------------------------------------------------------------
   Execute strings as sml code
   ------------------------------------------------------------------------- *)

fun quse_string s =
  let
    val stream = TextIO.openString (HolParser.fromString false s)
    fun infn () = TextIO.input1 stream
  in
    (
    while not (TextIO.endOfStream stream) do PolyML.compiler (infn, []) ();
    TextIO.closeIn stream;
    true
    )
    handle Interrupt => (TextIO.closeIn stream; raise Interrupt)
        | _ => (TextIO.closeIn stream; false)
  end

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

fun string_of_pretty p =
  let
    val acc = ref []
    fun f s = acc := s :: !acc
  in
    PolyML.prettyPrint (f,80) p;
    String.concatWith " " (rev (!acc))
  end

fun smltype_of_value l s =
  let
    val v = assoc s l handle HOL_ERR _ => raise ERR "type_of_value" s
    val t = PolyML.NameSpace.Values.typeof v
    val p = PolyML.NameSpace.Values.printType (t,0,NONE)
  in
    string_of_pretty p
  end

fun is_local_value s =
  mem s (map fst (#allVal (PolyML.globalNameSpace) ()))

fun is_thm_value l s =
  let
    val s1 = smltype_of_value l s
    val s2 = smlLexer.partial_sml_lexer s1
  in
    case s2 of
      [a] => (drop_sig a = "thm" handle HOL_ERR _ => false)
    | _   => false
  end

fun is_thm s = quse_string ("val _ : Thm.thm = (" ^ s ^ ")")
fun is_tactic s = quse_string ("val _ : Tactic.tactic = (" ^ s ^ ")")
fun is_string s = quse_string ("val _ : String.string = (" ^ s ^ ")")
fun is_simpset s = quse_string ("val _ : simpLib.simpset = (" ^ s ^ ")")
fun is_thml s = quse_string ("val _ : Thm.thm List.list = (" ^ s ^ ")")

fun is_stype s =
  let
    fun not_in cl c = not (mem c cl)
    fun test c = not_in [#"\t",#"\n",#" ",#"\""] c
  in
    List.find test (explode (rm_comment (rm_squote s))) = SOME #":"
  end

fun is_pointer_eq s1 s2 =
  let
    val b = quse_string
      ("val _ = smlExecute.sml_bool_glob := PolyML.pointerEq (" ^
         s1 ^ "," ^ s2 ^ ")")
  in
    b andalso (!sml_bool_glob)
  end

(* -------------------------------------------------------------------------
   Readers
   ------------------------------------------------------------------------- *)

fun thm_of_sml s =
  if is_thm s then
    let val b = quse_string ("smlExecute.sml_thm_glob := " ^ s) in
      if b then SOME (s, !sml_thm_glob) else NONE
    end
  else NONE

fun thml_of_sml sl =
  let
    val s = "[" ^ String.concatWith " , " sl ^ "]"
    val b = quse_string ("smlExecute.sml_thml_glob := " ^ s)
  in
    if b then SOME (!sml_thml_glob) else NONE
  end

fun mk_valid s = "Tactical.VALID (" ^ s ^ ")"

fun tactic_of_sml tim s =
  let
    val tactic = mk_valid s
    val program =
      "let fun f () = smlExecute.sml_tactic_glob := (" ^ tactic ^ ") in " ^
      "smlTimeout.timeout " ^ rts tim ^ " f () end"
    val b = quse_string program
  in
    if b then !sml_tactic_glob else raise ERR "tactic_of_sml" s
  end

fun string_of_sml s =
  let
    val b = quse_string ("val _ = smlExecute.sml_string_glob := (" ^ s ^ " )")
  in
    if b then !sml_string_glob else raise ERR "string_of_sml" s
  end

fun goal_of_sml s =
  let
    val b = quse_string ("val _ = smlExecute.sml_goal_glob := (" ^ s ^ " )")
  in
    if b then !sml_goal_glob else raise ERR "goal_of_sml" s
  end

(* -------------------------------------------------------------------------
   Apply tactic string
   ------------------------------------------------------------------------- *)

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun app_stac tim stac g =
  let val tac = tactic_of_sml tim stac in
    SOME (fst (timeout tim (TC_OFF tac) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

end (* struct *)
