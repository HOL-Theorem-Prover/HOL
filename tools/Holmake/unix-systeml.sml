structure Systeml :> Systeml = struct

(* This is the UNIX implementation of the Systeml functionality.  It is the
   very first thing compiled by the HOL build process so it absolutely
   can not depend on any other HOL source code. *)

local
  open Process
  fun squote s = concat ["'", s, "'"]
  fun unix_trans c = case c of #"'" => "'\\''" | x => str x
  val unix_quote = squote o String.translate unix_trans
  fun concat_wspaces munge acc strl =
    case strl of
      [] => concat (List.rev acc)
    | [x] => concat (List.rev (munge x :: acc))
    | (x::xs) => concat_wspaces munge (" " :: munge x :: acc) xs
in

  val systeml = system o concat_wspaces unix_quote []

  fun xable_string s = s

  fun mk_xable file =
      if systeml ["chmod", "a+x", file] = success then file
      else (print ("unable to set execute permission on "^file^".\n");
            raise Fail "mk_xable")


fun normPath s = Path.toString(Path.fromString s)

fun fullPath slist =
    normPath (List.foldl (fn (p1,p2) => Path.concat(p2,p1))
                         (hd slist) (tl slist))


(* these values are filled in by configure.sml *)
val HOLDIR =
val MOSMLDIR =
val OS =

val DEPDIR =
val GNUMAKE =

  fun emit_hol_script target qend =
      let val ostrm = TextIO.openOut target
          fun output s = TextIO.output(ostrm, s)
          val sigobj = unix_quote (fullPath [HOLDIR, "sigobj"])
          val std_prelude = unix_quote (fullPath [HOLDIR, "std.prelude"])
          val mosml = unix_quote (fullPath [MOSMLDIR, "bin", "mosml"])
      in
        output  "#!/bin/sh\n";
        output  "# The bare hol98 script\n\n";
        output (String.concat[mosml," -quietdec -P full -I ", sigobj, " ",
                              std_prelude, " $* ", unix_quote qend, "\n"]);
        TextIO.closeOut ostrm;
        mk_xable target
      end


  fun emit_hol_unquote_script target qend =
      let val ostrm = TextIO.openOut target
          fun output s = TextIO.output(ostrm, s)
          val qfilter = unix_quote (fullPath [HOLDIR, "bin", "unquote"])
          val sigobj = unix_quote (fullPath [HOLDIR, "sigobj"])
          val std_prelude = unix_quote (fullPath [HOLDIR, "std.prelude"])
          val mosml = unix_quote (fullPath [MOSMLDIR, "bin", "mosml"])
          val qinit =
              unix_quote (fullPath [HOLDIR, "tools", "unquote-init.sml"])
      in
        output  "#!/bin/sh\n";
        output  "# The hol98 script (with quote preprocessing)\n\n";
        output  (String.concat [qfilter, " | ", mosml," -quietdec -P full -I ",
                                sigobj, " ", std_prelude, " ", qinit,
                                " $* ", unix_quote qend, "\n"]);
        TextIO.closeOut ostrm;
        mk_xable target
      end
end (* local *)

end; (* struct *)
