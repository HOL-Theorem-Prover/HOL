(* Windows NT configuration *)

fun mk_xable file =   (* returns the name of the executable *)
  let val exe = file^".exe"
      val _ = FileSys.remove exe handle _ => ()
  in
    FileSys.rename{old=file, new=exe};
    exe
  end


val MK_XABLE_RHS =
 "let val exe = file^\".exe\" \
\       val _ = FileSys.remove exe handle _ => () \
\  in \
\    FileSys.rename{old=file, new=exe}; \
\    exe \
\  end"


(*---------------------------------------------------------------------------
             Write out scripts for running HOL.
 ---------------------------------------------------------------------------*)

local fun fopen file =
       let val _ = FileSys.remove file handle _ => ()
       in TextIO.openOut file
       end
in
fun emit_hol_script target mosml std_prelude qend =
   let val ostrm = fopen(target^".bat")
       fun output s = TextIO.output(ostrm, s)
   in
      output  "rem The bare hol98 script\n\n";
      output (String.concat[mosml," -quietdec -P full ", std_prelude,
                            " %* ", qend, "\n"]);
      TextIO.closeOut ostrm
   end;


fun emit_hol_unquote_script target qfilter mosml std_prelude qinit qend =
   let val ostrm = fopen(target^".bat")
       fun output s = TextIO.output(ostrm, s)
       fun munge s = String.translate (fn #"/" => "\\\\" | c => c) s
   in
      output  "rem The hol98 script (with quote preprocessing)\n\n";
      output  (String.concat [munge qfilter, " | ", mosml,
                              " -quietdec -P full ",
                              std_prelude, " ", qinit, " %* ", qend, "\n"]);
      TextIO.closeOut ostrm
   end
end;

(*---------------------------------------------------------------------------
        Set C-compiler options for building robdd library.
 ---------------------------------------------------------------------------*)

use (fullPath [holdir, "tools", "config-robdd.sml"]);
