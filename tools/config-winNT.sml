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

val systeml = winnt_systeml
val SYSTEML_NAME = "winnt_systeml"

(*---------------------------------------------------------------------------
             Write out scripts for running HOL.
 ---------------------------------------------------------------------------*)

local
  fun fopen file = let
    val _ = FileSys.remove file handle _ => ()
  in
    TextIO.openOut file
  end
  fun munge s = String.translate (fn #"/" => "\\" | c => str c) s
  fun q s = "\""^munge s^"\""
in
  fun emit_hol_script target mosml std_prelude qend = let
    val ostrm = fopen(target^".bat")
    fun output s = TextIO.output(ostrm, s)
  in
    output "@echo off\n";
    output  "rem The bare hol98 script\n\n";
    output (String.concat["call ", q mosml, " -P full ", q std_prelude,
                          " %* ", q qend, "\n"]);
    TextIO.closeOut ostrm
  end;


  fun emit_hol_unquote_script target qfilter mosml std_prelude qinit qend = let
    val ostrm = fopen(target^".bat")
    fun output s = TextIO.output(ostrm, s)
  in
    output  "@echo off\n";
    output  "rem The hol98 script (with quote preprocessing)\n\n";
    output  (String.concat ["call ", q qfilter, " | ", q mosml,
                          " -P full ",
                            q std_prelude, " ", q qinit, " %* ",
                            q qend, "\n"]);
    TextIO.closeOut ostrm
  end
end;

