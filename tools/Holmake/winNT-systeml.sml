structure Systeml = struct

local
  fun dquote s = concat ["\"", s, "\""];
  fun concat_wspaces munge acc strl =
    case strl of
      [] => concat (List.rev acc)
    | [x] => concat (List.rev (munge x :: acc))
    | (x::xs) => concat_wspaces munge (" " :: munge x :: acc) xs
  open Process
in
  fun systeml l = let
    val command = "call "^concat_wspaces dquote [] l
  in
    Process.system command
  end

  fun xable_string s = s^".exe"
  fun mk_xable file =   (* returns the name of the executable *)
      let val exe = file^".exe"
          val _ = FileSys.remove exe handle _ => ()
      in
        FileSys.rename{old=file, new=exe};
        exe
      end
local
  fun fopen file = (FileSys.remove file handle _ => (); TextIO.openOut file)
  fun munge s = String.translate (fn #"/" => "\\" | c => str c) s
  fun q s = "\""^munge s^"\""
in
fun emit_hol_script target mosml std_prelude qend =
 let val ostrm = fopen(target^".bat")
     fun output s = TextIO.output(ostrm, s)
 in
    output "@echo off\n";
    output  "rem The bare hol98 script\n\n";
    output (String.concat["call ", q mosml, " -P full ", q std_prelude,
                          " %* ", q qend, "\n"]);
    TextIO.closeOut ostrm
 end


fun emit_hol_unquote_script target qfilter mosml std_prelude qinit qend =
 let val ostrm = fopen(target^".bat")
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
end

end; (* struct *)


