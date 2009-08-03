(* this is an -*- sml -*- file *)
val _ = PolyML.print_depth 0;
local in
open HolKernel Parse boolLib proofManagerLib;

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
  fun gprint g pps t = let
    val tyg = Parse.type_grammar()
    val (_, ppt) = Parse.print_from_grammars (tyg,g)
  in
    ppt pps t
  end
  fun ppg pps g = term_grammar.prettyprint_grammar gprint pps g
  fun locpp pps l = PP.add_string pps (locn.toShortString l)
in
  val _ = PolyML.install_pp (pp2polypp (with_pp Kind.pp_qkind))
  val _ = PolyML.install_pp (pp2polypp (with_pp (Parse.term_pp_with_delimiters Hol_pp.pp_term)));
  val _ = PolyML.install_pp (pp2polypp (with_pp (Parse.type_pp_with_delimiters Hol_pp.pp_type)));
  val _ = PolyML.install_pp (pp2polypp (with_pp Pretype.pp_pretype))
  val _ = PolyML.install_pp (pp2polypp (with_pp Hol_pp.pp_thm));
  val _ = PolyML.install_pp (pp2polypp (with_pp Hol_pp.pp_theory));
  val _ = PolyML.install_pp (pp2polypp (with_pp kind_grammar.prettyprint_grammar));
  val _ = PolyML.install_pp (pp2polypp (with_pp type_grammar.prettyprint_grammar));
  val _ = PolyML.install_pp (pp2polypp (with_pp ppg))

  val _ = PolyML.install_pp (pp2polypp (with_pp proofManagerLib.pp_proof));
  val _ = PolyML.install_pp (pp2polypp (with_pp proofManagerLib.pp_proofs));
  val _ = PolyML.install_pp (pp2polypp (with_pp Rewrite.pp_rewrites))
  val _ = PolyML.install_pp (pp2polypp (with_pp TypeBasePure.pp_tyinfo))
  val _ = PolyML.install_pp (pp2polypp (with_pp DefnBase.pp_defn))
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbnum.pp_num))
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbint.pp_int))
  val _ = PolyML.install_pp (pp2polypp (with_pp Arbrat.pp_rat))
  val _ = PolyML.install_pp (pp2polypp (with_pp locpp))
end;

(*---------------------------------------------------------------------------*
 * Set up the help paths.                                                    *
 *---------------------------------------------------------------------------*)

local
  open Path
  fun HELP s = toString(fromString(concat(HOLDIR, concat("help",s))))
  val SIGOBJ = toString(fromString(concat(HOLDIR, "sigobj")))
in
  val () = Help.indexfiles := HELP "HOL.Help" :: !Help.indexfiles
  val () = Help.helpdirs   := HOLDIR :: SIGOBJ :: !Help.helpdirs
  val () = Help.specialfiles :=
             {file = "help/Docfiles/README.Hol98",
              term = "hol", title = "Hol98 Overview"}
             :: !Help.specialfiles
  val help = Help.help
end


(*---------------------------------------------------------------------------*
 *  Set parameters for parsing and help.                                     *
 *---------------------------------------------------------------------------*)

val _ = Help.displayLines := 60;


local
 fun try_remove f = ((OS.FileSys.remove f) handle OS.SysErr _ => ());
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
      val filename = OS.FileSys.tmpName()
    in
      (if OS.Process.isSuccess (unquote_to s filename) then
         (PolyML.use filename; OS.FileSys.remove filename)
       else (TextIO.output(TextIO.stdOut,
                           ("Failed to translate file: "^s^"\n"));
             raise Fail "use"))
      handle e => (try_remove filename; raise e)
    end
  else PolyML.use s;
end;

val _ = Globals.interactive := true;

val build_stamp =
 let open TextIO Path;
     val stampstr = openIn (concat(HOLDIR, concat("tools", "build-stamp")));
     val stamp = inputAll stampstr before closeIn stampstr;
 in
     stamp
 end handle _ => "";

val _ =
TextIO.output(TextIO.stdOut,
  "\n-----------------------------------------------------------------\n"
  ^"    HOL-Omega ["
  ^Globals.release^" "^Lib.int_to_string(Globals.version)^build_stamp
  ^"]\n\n       For introductory HOL help, type: help \"hol\";\n"
  ^"-----------------------------------------------------------------\n\n");

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
end;
structure HOL_Interactive :> sig val toggle_quietdec : unit -> bool end =
struct
  local val qd = ref false
  in
  fun toggle_quietdec () =
      if !qd then (PolyML.Compiler.prompt1 := "> ";
                   PolyML.Compiler.prompt2 := "# ";
                   PolyML.print_depth 100;
                   qd := false;
                   false)
      else (PolyML.Compiler.prompt1 := "";
            PolyML.Compiler.prompt2 := "";
            PolyML.print_depth 0;
            qd := true;
            true)
  end
end

val _ = PolyML.print_depth 100;

