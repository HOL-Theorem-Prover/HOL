val _ = use "poly/poly-init2.ML";

(* ----------------------------------------------------------------------
    Establish the basic environment and bring in the HOL kernel
   ---------------------------------------------------------------------- *)

val _ = 
  loadPath := (OS.Path.concat (Systeml.HOLDIR, "sigobj")) :: (!loadPath);

val _ = app load ["boolLib", "goalstackLib", "Arbrat"];

open HolKernel Parse boolLib goalstackLib;

(* Loading HolKernel installs the "standard" set of infixes, which are
   set up in src/0/Overlay.sml *)

(*---------------------------------------------------------------------------*
 *   Install prettyprinters                                                  *
 *---------------------------------------------------------------------------*)

local
  open PP;
  fun with_pp ppfn pps x =
      Parse.respect_width_ref Globals.linewidth ppfn pps x handle e => Raise e;
  fun pp_from_stringfn sf pps x = PP.add_string pps (sf x);
  fun pp2polypp (f : ppstream -> 'a -> unit)
              (putString : string -> unit,
               beginBlock : int * bool -> unit,
               spaceBlock : int * int -> unit,
               endBlock : unit -> unit)
              (dpth_limit : int)
              recursive_print
              (e : 'a) = 
    putString (pp_to_string (!Globals.linewidth) f e);
in
  val _ = PolyML.install_pp (pp2polypp (with_pp (Parse.term_pp_with_delimiters Hol_pp.pp_term)));
  val _ = PolyML.install_pp (pp2polypp (with_pp (Parse.type_pp_with_delimiters Hol_pp.pp_type)));
  val _ = PolyML.install_pp (pp2polypp (with_pp Hol_pp.pp_thm));
  val _ = PolyML.install_pp (pp2polypp (with_pp Hol_pp.pp_theory));
  val _ = PolyML.install_pp (pp2polypp (with_pp type_grammar.prettyprint_grammar));
  val _ = PolyML.install_pp (pp2polypp (with_pp term_grammar.prettyprint_grammar));

  val _ = PolyML.install_pp (pp2polypp (with_pp goalstackLib.pp_proofs));
  val _ = PolyML.install_pp (pp2polypp (with_pp goalstackLib.pp_goalstack));
  val _ = PolyML.install_pp (pp2polypp (with_pp Rewrite.pp_rewrites));
  val _ = PolyML.install_pp (pp2polypp (with_pp TypeBasePure.pp_tyinfo));
  val _ = PolyML.install_pp (pp2polypp (with_pp DefnBase.pp_defn));
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbnum.pp_num));
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbint.pp_int));
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbrat.pp_rat));
end;


(*---------------------------------------------------------------------------*
 * Set up the help paths.                                                    *
 *---------------------------------------------------------------------------*)

(*
local
  open Path
  fun HELP s = toString(fromString(concat(HOLDIR, concat("help",s))))
  val SIGOBJ = toString(fromString(concat(HOLDIR, "sigobj")))
in
  val () = indexfiles := HELP "HOL.Help" :: !indexfiles
  val () = helpdirs   := HOLDIR :: SIGOBJ :: !helpdirs
  val () = Help.specialfiles :=
             {file = "help/Docfiles/README.Hol98",
              term = "hol", title = "Hol98 Overview"}
             :: !Help.specialfiles
end
*)


(*---------------------------------------------------------------------------*
 *  Set parameters for parsing and help.                                     *
 *---------------------------------------------------------------------------*)

(*
val _ = quotation := true
val _ = Help.displayLines := 60;
*)

(*---------------------------------------------------------------------------*
 *  Set up compile_theory function                                           *
 *---------------------------------------------------------------------------*)
(*
fun compile_theory () = let
  val name = current_theory()
  val signame = name^"Theory.sig"
  val smlname = name^"Theory.sml"
  fun readable f = FileSys.access(f, [FileSys.A_READ])
in
  if readable signame andalso readable smlname then let
  in
     Meta.compileStructure ["Overlay"] signame;
     Meta.compileStructure ["Overlay"] smlname;
     print ("Compiled "^name^" theory files.\n")
  end
  else
     print "No theory files on disk; perhaps export_theory() required.\n"
end
*)

(* ----------------------------------------------------------------------
    Set interactive flag to true
   ---------------------------------------------------------------------- *)

(*
val _ = Globals.interactive := true;
*)

(*---------------------------------------------------------------------------*
 * Print a banner.                                                           *
 *---------------------------------------------------------------------------*)

val build_stamp =
 let open TextIO Path;
     val stampstr = openIn (concat(HOLDIR, concat("tools", "build-stamp")));
     val stamp = inputAll stampstr before closeIn stampstr;
 in
     stamp
 end handle _ => "";

local
 fun has_dq file =
      let
        val istrm = TextIO.openIn file
        fun loop() =
            case TextIO.input1 istrm of
              NONE => false
            | SOME #"`" => true
            | SOME _ => loop()
      in
        loop() before TextIO.closeIn istrm
      end handle IO.Io _ => false;
  infix ++;
  fun p1 ++ p2 = OS.Path.concat (p1, p2);
  open Systeml;
  fun unquote_to file1 file2 =
      systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2];
in
fun use s =
  if has_dq s then
    let
      val filename = OS.FileSys.tmpName()^".hol"
    in
      if OS.Process.isSuccess (unquote_to s filename) then
        (PolyML.use filename; OS.FileSys.remove filename)
        handle e => (OS.FileSys.remove filename handle _ => (); raise e)
      else (TextIO.output(TextIO.stdOut,
                          ("Failed to translate file: "^s^"\n"));
            raise Fail "use")
    end
  else PolyML.use s;
end;

fun prelude_main () =
let
val _ =
TextIO.output(TextIO.stdOut,
  "\n-----------------------------------------------------------------\n"
  ^"       HOL-4 ["
  ^Globals.release^" "^Lib.int_to_string(Globals.version)^build_stamp
  ^"]\n\n       For introductory HOL help, type: help \"hol\";\n"
  ^"-----------------------------------------------------------------\n\n");

(* ----------------------------------------------------------------------
    if present, look at a Holmakefile in the current directory to see
    if we should extend the loadPath
   ---------------------------------------------------------------------- *)

val _ = if FileSys.access ("Holmakefile", [FileSys.A_READ]) then let
            open Holmake_types;
            fun base_env s =
                case s of
                  "HOLDIR" => [LIT HOLDIR]
                | "SIGOBJ" => [VREF "HOLDIR", LIT "/sigobj"]
                | _ => (case Process.getEnv s of
                          NONE => [LIT ""]
                        | SOME v => [LIT v]);
            val toks = ReadHMF.read "Holmakefile";
            val env = extend_env toks base_env;
            fun envlist id =
                map dequote (tokenize (perform_substitution env [VREF id]));
            val hmake_includes = envlist "INCLUDES";
          in
            case hmake_includes of
              [] => ()
            | _ =>
              (print "[extending loadPath with Holmakefile INCLUDES variable]\n";
               loadPath := !loadPath @ hmake_includes)
          end handle e => (print "[bogus Holmakefile in current directory \
                                 \- ignoring it]\n";
                           TextIO.flushOut TextIO.stdErr;
                           ())
        else ();
val _ =
  (term_pp_prefix := "``";   term_pp_suffix := "``";
   type_pp_prefix  := "``";   type_pp_suffix := "``");
in
()
end;


(* Local variables: *)
(* mode: sml *)
(* end: *)
