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
   Result slots.  A reader compiles a string that puts its value in a slot
   of the thread running it, which the reader then takes: a string
   compiled at the same time on another thread has a slot of its own.
   ------------------------------------------------------------------------- *)

type 'a slot = 'a Thread_Data.var

fun put slot x = Thread_Data.put slot (SOME x)

val sml_bool_slot : bool slot = Thread_Data.var ()
val sml_tactic_slot : tactic slot = Thread_Data.var ()
val sml_string_slot : string slot = Thread_Data.var ()
val sml_goal_slot : goal slot = Thread_Data.var ()
val sml_thm_slot : thm slot = Thread_Data.var ()
val sml_thml_slot : thm list slot = Thread_Data.var ()

(* -------------------------------------------------------------------------
   Execute strings as sml code.  The compiler prints nothing: a string
   that does not compile makes quse_string false.
   ------------------------------------------------------------------------- *)

val silent =
  [PolyML.Compiler.CPOutStream (K ()),
   PolyML.Compiler.CPErrorMessageProc (K ())]

fun quse_string s =
  let
    val stream = TextIO.openString
                   (HOLSource.fromString {quietOpen = false, print = K()} s)
    fun infn () = TextIO.input1 stream
  in
    (
    while not (TextIO.endOfStream stream) do
      PolyML.compiler (infn, silent) ();
    TextIO.closeIn stream;
    true
    )
    handle Interrupt => (TextIO.closeIn stream; raise Interrupt)
        | _ => (TextIO.closeIn stream; false)
  end

(* The value program, a declaration that puts it in slot, puts there.
   The slot is left empty. *)
fun take slot program =
  let
    val _ = Thread_Data.put slot NONE
    val compiled = quse_string program
    val value = Thread_Data.get slot
  in
    Thread_Data.put slot NONE;
    if compiled then value else NONE
  end

fun put_program slot e =
  "val _ = smlExecute.put smlExecute." ^ slot ^ " ( " ^ e ^ " )"

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
  take sml_bool_slot
    (put_program "sml_bool_slot" ("PolyML.pointerEq (" ^ s1 ^ "," ^ s2 ^ ")"))
  = SOME true

(* -------------------------------------------------------------------------
   Readers
   ------------------------------------------------------------------------- *)

fun thm_of_sml s =
  if is_thm s then
    Option.map (fn th => (s, th))
      (take sml_thm_slot (put_program "sml_thm_slot" s))
  else NONE

fun thml_of_sml sl =
  take sml_thml_slot
    (put_program "sml_thml_slot" ("[" ^ String.concatWith " , " sl ^ "]"))

fun mk_valid s = "Tactical.VALID (" ^ s ^ ")"

fun tactic_of_sml tim s =
  let
    val program = put_program "sml_tactic_slot"
      ("smlTimeout.timeout " ^ rts tim ^ " (fn () => " ^ mk_valid s ^ ") ()")
  in
    case take sml_tactic_slot program of
        SOME tac => tac
      | NONE => raise ERR "tactic_of_sml" s
  end

(* Recording runs a previously successful source proof in a disposable HOL
   subprocess.  Do not introduce a Poly/ML timeout thread while constructing
   its instrumented tactic: a worker that fails to stop can outlive the
   timeout and wedge the otherwise valid theory recording. *)
fun tactic_of_sml_no_timeout s =
  case take sml_tactic_slot (put_program "sml_tactic_slot" (mk_valid s)) of
      SOME tac => tac
    | NONE => raise ERR "tactic_of_sml_no_timeout" s

fun string_of_sml s =
  case take sml_string_slot (put_program "sml_string_slot" s) of
      SOME x => x
    | NONE => raise ERR "string_of_sml" s

fun goal_of_sml s =
  case take sml_goal_slot (put_program "sml_goal_slot" s) of
      SOME x => x
    | NONE => raise ERR "goal_of_sml" s

(* -------------------------------------------------------------------------
   Apply tactic string
   ------------------------------------------------------------------------- *)

val TC_OFF = HOLFlags.with_bflags [(Parse.show_typecheck_errors, false)]

(* A tactic does its work once it has both the goal and the context, so
   both the trace setting and the timeout have to span that application,
   not merely the one that builds the context-awaiting closure. *)
fun app_stac tim stac g =
  let
    val tac = tactic_of_sml tim stac
    val ctxt = Context.snapshot()
    val run = TC_OFF (Lib.C tac ctxt)
  in
    SOME (fst (timeout tim run g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

end (* struct *)
