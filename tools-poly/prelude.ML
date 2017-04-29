
(* this is an -*- sml -*- file *)
val () = PolyML.print_depth 0;

open HolKernel Parse boolLib proofManagerLib

(* Install pretty-printers *)

local
  fun pp2polypp (ppfn: PP.ppstream -> 'b -> unit) =
    let
      fun f pps x = Parse.respect_width_ref Globals.linewidth ppfn pps x
                    handle e => Raise e
    in
      fn depth => fn printArgTypes => fn e: 'b =>
        PolyML.PrettyString (PP.pp_to_string (!Globals.linewidth) f e)
    end
  fun gprint g pps t =
    let
      val tyg = Parse.type_grammar ()
      val (_, ppt) = Parse.print_from_grammars (tyg, g)
    in
      ppt pps t
    end
  val ppg = term_grammar.prettyprint_grammar gprint
  val ppgrules = term_grammar.prettyprint_grammar_rules gprint
  fun locpp pps l = PP.add_string pps (locn.toShortString l)
  fun pp_redblackmap pps (d: ('a,'b) Redblackmap.dict) =
    PP.add_string pps
      ("<Redblackmap(" ^ Int.toString (Redblackmap.numItems d) ^ ")>")
  fun pp_redblackset pps (s: 'a Redblackset.set) =
    PP.add_string pps
      ("<Redblackset(" ^ Int.toString (Redblackset.numItems s) ^ ")>")
in
  val () =
  ( if PolyML.Compiler.compilerVersionNumber < 560 then
      let
        fun pp_typebase _ _ (_: TypeBasePure.typeBase) =
          PolyML.PrettyString "<typeBase>"
        fun pp_seq _ _ (_: 'a seq.seq) = PolyML.PrettyString "<seq>"
      in
        PolyML.addPrettyPrinter pp_typebase
      ; PolyML.addPrettyPrinter pp_seq
      ; PolyML.addPrettyPrinter (pp2polypp HOLset.pp_holset)
      end
    else
      let
        fun pp_db _ _ (c: DB.class) =
          PolyML.PrettyString
            (case c of
               DB.Thm => "Thm"
             | DB.Axm => "Axm"
             | DB.Def => "Def")
        fun pp_delta depth printArgTypes (d: 'a delta) =
          case d of
            Lib.SAME => PolyML.PrettyString "SAME"
          | Lib.DIFF a =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "DIFF", PolyML.PrettyBreak (1, 0),
                  printArgTypes (a, depth)])
        fun pp_verdict depth (pra, prb) (v: ('a, 'b) Lib.verdict) =
          case v of
            Lib.PASS (a: 'a) =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "PASS", PolyML.PrettyBreak (1, 0),
                  pra (a, depth)])
          | Lib.FAIL (b: 'b) =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "FAIL", PolyML.PrettyBreak (1, 0),
                  prb (b, depth)])
        fun pp_frag depth printArgTypes (f: 'a HOLPP.frag) =
          case f of
            HOLPP.QUOTE s =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "QUOTE", PolyML.PrettyBreak (1, 0),
                  PolyML.prettyRepresentation (s, depth)])
          | HOLPP.ANTIQUOTE a =>
              PolyML.PrettyBlock
                (2, false, [],
                 [PolyML.PrettyString "ANTIQUOTE", PolyML.PrettyBreak (1, 0),
                  printArgTypes (a, depth)])
        fun pp_breakstyle _ _ (b: HOLPP.break_style) =
          PolyML.PrettyString
            (case b of
               HOLPP.CONSISTENT => "CONSISTENT"
             | HOLPP.INCONSISTENT => "INCONSISTENT")
      in
        PolyML.addPrettyPrinter pp_db
      ; PolyML.addPrettyPrinter pp_delta
      ; PolyML.addPrettyPrinter pp_verdict
      ; PolyML.addPrettyPrinter pp_frag
      ; PolyML.addPrettyPrinter pp_breakstyle
      end
  ; PolyML.addPrettyPrinter (pp2polypp ppg)
  ; PolyML.addPrettyPrinter (pp2polypp ppgrules)
  ; PolyML.addPrettyPrinter (pp2polypp locpp)
  ; PolyML.addPrettyPrinter (pp2polypp pp_redblackmap)
  ; PolyML.addPrettyPrinter (pp2polypp pp_redblackset)
  ; PolyML.addPrettyPrinter
      (pp2polypp (Parse.term_pp_with_delimiters Hol_pp.pp_term))
  ; PolyML.addPrettyPrinter
      (pp2polypp (Parse.type_pp_with_delimiters Hol_pp.pp_type))
  ; PolyML.addPrettyPrinter (pp2polypp Pretype.pp_pretype)
  ; PolyML.addPrettyPrinter (pp2polypp Hol_pp.pp_thm)
  ; PolyML.addPrettyPrinter (pp2polypp Hol_pp.pp_theory)
  ; PolyML.addPrettyPrinter (pp2polypp type_grammar.prettyprint_grammar)
  ; PolyML.addPrettyPrinter (pp2polypp proofManagerLib.pp_proof)
  ; PolyML.addPrettyPrinter (pp2polypp proofManagerLib.pp_proofs)
  ; PolyML.addPrettyPrinter (pp2polypp Rewrite.pp_rewrites)
  ; PolyML.addPrettyPrinter (pp2polypp TypeBasePure.pp_tyinfo)
  ; PolyML.addPrettyPrinter (pp2polypp DefnBase.pp_defn)
  ; PolyML.addPrettyPrinter (pp2polypp Arbnum.pp_num)
  ; PolyML.addPrettyPrinter (pp2polypp Arbint.pp_int)
  ; PolyML.addPrettyPrinter (pp2polypp Arbrat.pp_rat)
  )
end

(*---------------------------------------------------------------------------*
   Switch in and out of quiet mode
 *---------------------------------------------------------------------------*)

structure HOL_Interactive :>
  sig
    val toggle_quietdec : unit -> bool
    val amquiet : unit -> bool
    val print_banner : unit -> unit
  end =
struct
  infix ++
  val op ++ = OS.Path.concat
  val qd = ref true
  fun toggle_quietdec () =
    if !qd then
      ( PolyML.Compiler.prompt1 := "> "
      ; PolyML.Compiler.prompt2 := "# "
      ; PolyML.print_depth 100
      ; qd := false
      ; false
      )
    else
      ( PolyML.Compiler.prompt1 := ""
      ; PolyML.Compiler.prompt2 := ""
      ; PolyML.print_depth 0
      ; qd := true
      ; true
      )
  fun amquiet () = !qd
  val build_stamp =
    let
      val stampstr = TextIO.openIn (HOLDIR ++ "tools" ++ "build-stamp")
      val stamp = TextIO.inputAll stampstr before TextIO.closeIn stampstr
    in
      stamp
    end
    handle _ => ""
  val id_string =
    "HOL-4 [" ^ Globals.release ^ " " ^ Lib.int_to_string Globals.version ^
    " (" ^ Thm.kernelid ^ ", " ^ build_stamp ^ ")]\n\n"
  val exit_string =
    if Systeml.OS = "winNT" then
      "To exit type <Control>-Z <Return>  (*not* quit();)"
    else
      "To exit type <Control>-D"
  val line =
    "\n---------------------------------------------------------------------\n"

  fun print_banner () =
    TextIO.output (TextIO.stdOut,
      line ^
      "       " ^ id_string ^
      "       For introductory HOL help, type: help \"hol\";\n" ^
      "       " ^ exit_string ^
      line)
end;

(*---------------------------------------------------------------------------*
 * Set up the help paths.                                                    *
 * Set parameters for parsing and help.                                      *
 *---------------------------------------------------------------------------*)

val use = QUse.use

local
  infix ++
  val op ++ = OS.Path.concat
  fun hol_use p s =
    let
      val nm = HOLDIR ++ p ++ s
    in
      use (nm ^ ".sig")
    ; use (nm ^ ".sml")
    end
in
  val _ = HOL_Interactive.print_banner()
  val () =
    ( hol_use ("help" ++ "src-sml") "Database"
    ; hol_use ("tools-poly" ++ "poly") "Help"
    ; PolyML.use (HOLDIR ++ "tools" ++ "makefile-includes.ML")
    ; List.app Meta.fakeload ["PP", "PolyML", "Posix"]
    ; Globals.interactive := true
    ; Parse.current_backend := Parse.interactive_ppbackend ()
    ; term_pp_prefix := "``"
    ; term_pp_suffix := "``"
    ; type_pp_prefix := "``"
    ; type_pp_suffix := "``"
    ; Feedback.set_trace "pp_annotations" 1
    ; PolyML.use (HOLDIR ++ "tools" ++ "check-intconfig.sml")
    )
end;

local
  infix ++
  val op ++ = OS.Path.concat
  val path = Path.toString o Path.fromString
  fun HELP s = path (HOLDIR ++ "help" ++ s)
  val SIGOBJ = path (HOLDIR ++ "sigobj")
  val () =
    ( Help.indexfiles := HELP "HOL.Help" :: !Help.indexfiles
    ; Help.helpdirs   := HOLDIR :: SIGOBJ :: !Help.helpdirs
    ; Help.specialfiles :=
        {file = "help" ++ "Docfiles" ++ "HOL.help",
         term = "hol",
         title = "HOL Overview"} :: !Help.specialfiles
    ; Help.displayLines := 60
    )
in
  val help = Help.help
end

val _ = HOL_Interactive.toggle_quietdec ()
val _ = List.app holpathdb.extend_db
                 (holpathdb.search_for_extensions ReadHMF.find_includes
                                                  [OS.FileSys.getDir()])
