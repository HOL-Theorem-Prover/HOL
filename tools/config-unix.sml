(* Unix configuration *)

local
  open Process
in

  fun xable_string s = s
  val MK_XABLE_RHS = "(unix_systeml [\"chmod\", \"a+x\", file]; file)"
  val systeml = unix_systeml
  val SYSTEML_NAME = "unix_systeml"

  fun mk_xable file =
    if systeml ["chmod", "a+x", file] = success then file
    else (print ("unable to set execute permission on "^file^".\n");
          raise Fail "mk_xable");


end;


(*---------------------------------------------------------------------------
       Write out scripts for running HOL.
 ---------------------------------------------------------------------------*)

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
   end;


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
   end;

