structure Systeml :> Systeml = struct

(* This is the UNIX implementation of the Systeml functionality.  It is the
   very first thing compiled by the HOL build process so it absolutely
   can not depend on any other HOL source code. *)

local
  open Process
  fun squote s = concat ["'", s, "'"];
  fun concat_wspaces munge acc strl =
    case strl of
      [] => concat (List.rev acc)
    | [x] => concat (List.rev (munge x :: acc))
    | (x::xs) => concat_wspaces munge (" " :: munge x :: acc) xs
in

  fun systeml  l = let
    fun unix_trans c = case c of #"'" => "'\\''" | x => str x
    val command = concat_wspaces (squote o String.translate unix_trans) [] l
  in
    system command
  end

  fun xable_string s = s

  fun mk_xable file =
      if systeml ["chmod", "a+x", file] = success then file
      else (print ("unable to set execute permission on "^file^".\n");
            raise Fail "mk_xable")

  fun emit_hol_script target mosml std_prelude qend =
      let val ostrm = TextIO.openOut target
          fun output s = TextIO.output(ostrm, s)
      in
        output  "#!/bin/sh\n";
        output  "# The bare hol98 script\n\n";
        output (String.concat[mosml," -quietdec -P full ",
                              std_prelude, " $* ", qend, "\n"]);
        TextIO.closeOut ostrm;
        mk_xable target
      end


  fun emit_hol_unquote_script target qfilter mosml std_prelude qinit qend =
      let val ostrm = TextIO.openOut target
          fun output s = TextIO.output(ostrm, s)
      in
        output  "#!/bin/sh\n";
        output  "# The hol98 script (with quote preprocessing)\n\n";
        output  (String.concat [qfilter, " | ", mosml," -quietdec -P full ",
                                std_prelude, " ", qinit, " $* ", qend, "\n"]);
        TextIO.closeOut ostrm;
        mk_xable target
      end
end (* local *)

val HOLDIR =
val MOSMLDIR =
val OS =

val DEPDIR =
val GNUMAKE =



end; (* struct *)
