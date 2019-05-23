
(* this is an -*- sml -*- file *)
val () = PolyML.print_depth 0;

open HolKernel Parse boolLib proofManagerLib

(* Install pretty-printers *)

val _ = let
  fun pp2polypp (ppfn: 'b -> HOLPP.pretty) =
    let
    in
      fn depth => fn printArgTypes => fn e: 'b => ppfn e
    end
  fun gprint g =
    let
      val tyg = Parse.type_grammar ()
      val (_, ppt) = Parse.print_from_grammars (tyg, g)
    in
      smpp.lift ppt
    end
  val ppg = Parse.mlower o term_grammar.prettyprint_grammar gprint
  val ppgrules = Parse.mlower o term_grammar.prettyprint_grammar_rules gprint
  fun locpp l = PP.add_string (locn.toShortString l)
  fun pp_redblackmap (d: ('a,'b) Redblackmap.dict) =
    PP.add_string
      ("<Redblackmap(" ^ Int.toString (Redblackmap.numItems d) ^ ")>")
  fun pp_redblackset (s: 'a Redblackset.set) =
    PP.add_string
      ("<Redblackset(" ^ Int.toString (Redblackset.numItems s) ^ ")>")
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
  fun pp_symtab d printArgTypes (t : 'a Symtab.table) =
      Symtab.pp (fn a => printArgTypes(a,d-1)) t
  fun pp_inttab d printArgTypes (t : 'a Inttab.table) =
      Inttab.pp (fn a => printArgTypes(a,d-1)) t
  fun pp_knametab d printArgTypes (t : 'a KNametab.table) =
      KNametab.pp (fn a => printArgTypes(a,d-1)) t
  fun pp_seq _ _ (s:'a seq.seq) = HOLPP.add_string "<seq>"
  fun pp_typebase _ _ (tb:TypeBasePure.typeBase) = HOLPP.add_string "<typeBase>"
in
  (* would like to put these all in a list and List.app over them, but
     unfortunately, they all have different types; can't bind addPrettyPrinter to
     more convenient, abbreviating, name either; it seems to be too magic *)
  PolyML.addPrettyPrinter HOLset.pp_holset;
  PolyML.addPrettyPrinter pp_breakstyle;
  PolyML.addPrettyPrinter pp_db;
  PolyML.addPrettyPrinter pp_delta;
  PolyML.addPrettyPrinter pp_frag;
  PolyML.addPrettyPrinter pp_inttab;
  PolyML.addPrettyPrinter pp_knametab;
  PolyML.addPrettyPrinter pp_seq;
  PolyML.addPrettyPrinter pp_symtab;
  PolyML.addPrettyPrinter pp_typebase;
  PolyML.addPrettyPrinter pp_verdict;

  PolyML.addPrettyPrinter (pp2polypp (Parse.term_pp_with_delimiters Hol_pp.pp_term));
  PolyML.addPrettyPrinter (pp2polypp (Parse.type_pp_with_delimiters Hol_pp.pp_type));
  PolyML.addPrettyPrinter (pp2polypp Arbint.pp_int);
  PolyML.addPrettyPrinter (pp2polypp Arbnum.pp_num);
  PolyML.addPrettyPrinter (pp2polypp Arbrat.pp_rat);
  PolyML.addPrettyPrinter (pp2polypp DefnBase.pp_defn);
  PolyML.addPrettyPrinter (pp2polypp HOLPP.pp_pretty);
  PolyML.addPrettyPrinter (pp2polypp Hol_pp.pp_theory);
  PolyML.addPrettyPrinter (pp2polypp Hol_pp.pp_thm);
  PolyML.addPrettyPrinter (pp2polypp Pretype.pp_pretype);
  PolyML.addPrettyPrinter (pp2polypp Rewrite.pp_rewrites);
  PolyML.addPrettyPrinter (pp2polypp Tag.pp_tag);
  PolyML.addPrettyPrinter (pp2polypp TypeBasePure.pp_tyinfo);
  PolyML.addPrettyPrinter (pp2polypp locpp);
  PolyML.addPrettyPrinter (pp2polypp pp_redblackmap);
  PolyML.addPrettyPrinter (pp2polypp pp_redblackset);
  PolyML.addPrettyPrinter (pp2polypp ppg);
  PolyML.addPrettyPrinter (pp2polypp ppgrules);
  PolyML.addPrettyPrinter (pp2polypp proofManagerLib.pp_proof);
  PolyML.addPrettyPrinter (pp2polypp proofManagerLib.pp_proofs);
  PolyML.addPrettyPrinter (pp2polypp type_grammar.prettyprint_grammar)
end

val _ = PolyML.use (OS.Path.concat(HOLDIR, "tools-poly/holinteractive.ML"));

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
    ; ReadHMF.extend_path_with_includes {verbosity = 0, lpref = loadPath}
    ; List.app Meta.fakeload ["PP", "PolyML", "Posix"]
    ; Globals.interactive := true
    ; Parse.current_backend := Parse.interactive_ppbackend ()
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
