(* Unix configuration *)

local val XABLE  = "chmod a+x"   (* set execute permission *)
      open Process
in
fun mk_xable file =
  if system (XABLE^" "^file) = success then file
  else (print ("unable to set execute permission on "^file^".\n");
        raise Fail "mk_xable");

val MK_XABLE_RHS =
  String.concat ["(Process.system (\"",XABLE," \"^file); file)"];

end;


(*---------------------------------------------------------------------------
       Write out scripts for running HOL.
 ---------------------------------------------------------------------------*)

fun emit_hol_script target mosml std_prelude =
   let val ostrm = TextIO.openOut target
       fun output s = TextIO.output(ostrm, s)
   in
      output  "#!/bin/sh\n";
      output  "# The bare hol98 script\n\n";
      output (String.concat[mosml," -quietdec -P full ",std_prelude," $*\n"]);
      TextIO.closeOut ostrm;
      mk_xable target
   end;


fun emit_hol_unquote_script target qfilter hol qinit =
   let val ostrm = TextIO.openOut target
       fun output s = TextIO.output(ostrm, s)
   in
      output  "#!/bin/sh\n";
      output  "# The hol98 script (with quote preprocessing)\n\n";
      output  (String.concat [qfilter, " | ", hol, " ", qinit, " $*\n"]);
      TextIO.closeOut ostrm;
      mk_xable target
   end;

(*---------------------------------------------------------------------------
        Set C-compiler options for building robdd library.
 ---------------------------------------------------------------------------*)

use (fullPath [holdir, "tools", "config-robdd.sml"]);
