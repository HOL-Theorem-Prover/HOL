structure Doc2markdown =
struct

open ParseDoc

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun capitalise s = CharVector.tabulate (
  size s,
  (fn i => if i = 0 then Char.toUpper (String.sub (s,0))
           else Char.toLower (String.sub(s,i)))
);

fun trans_secnm "DESCRIBE" = "Description"
  | trans_secnm s = capitalise s

fun brkt_text s = s

fun markdown (name,sectionl) ostrm =
    let fun out s = TextIO.output(ostrm, s)
        fun outss ss = out (Substring.string ss)
        fun mdtext elem =
            case elem of
                BRKT ss => out ("`" ^ brkt_text (Substring.string ss) ^ "`")
              | EMPH ss => out ("*" ^ Substring.string ss ^ "*")
              | PARA => out "\n\n"
              | TEXT ss => outss ss
              | XMPL ss => out ("```" ^ Substring.string ss ^ "```\n")

        fun mdsection sec =
            case sec of
                SEEALSO sslist =>
                (out "## See Also\n\n";
                 out (String.concatWith ", " (map Substring.string sslist));
                 out "\n\n")
              | TYPE ss =>
                (out ("## Type\n\n```\n" ^ Substring.string ss ^ "\n```\n\n"))
              | FIELD (secnm, textelems) =>
                (out ("## " ^ trans_secnm secnm ^ "\n\n");
                 List.app mdtext textelems;
                 out "\n")

    in
      List.app mdsection sectionl
    end


fun trans mddir docdir ((str,nm), docfile) = let
  val docbase = OS.Path.base docfile
  val docpath = OS.Path.concat (docdir, docfile)
  val outfile = OS.Path.joinBaseExt{base = OS.Path.concat(mddir, docbase),
                                    ext = SOME "md"}
  val ostrm = TextIO.openOut outfile
in
    markdown ((if str <> "" then str ^ "." else "")^nm, parse_file docpath) ostrm
  ; TextIO.closeOut ostrm
end handle e => die ("Exception raised: " ^ General.exnMessage e)


fun docdir_to_mddir docdir mddir =
    let  open OS.FileSys
         val docfiles = ParseDoc.find_docfiles docdir
         val _ = isDir mddir orelse die ("Directory "^ mddir^" doesn't exist")
         val (tick,finish) =
             Flash.initialise ("Directory "^docdir^": ", Binarymap.numItems docfiles)
    in
      Binarymap.app (fn d => (trans mddir docdir d; tick())) docfiles;
      finish();
      OS.Process.exit OS.Process.success
    end



fun main() =
    case CommandLine.arguments() of
        [docdir,mddir] => docdir_to_mddir docdir mddir
      | otherwise => (print "Usage: Doc2markdown <docdir> <markdown-dir>\n";
                      OS.Process.exit OS.Process.failure)
end (* struct *)
