structure Doc2Tex =
struct

open ParseDoc


fun occurs s ss = not (Substring.isEmpty (#2 (Substring.position s ss)));
fun equal x y = (x = y)

fun warn s = TextIO.output(TextIO.stdErr, s)
fun out(str,s) = TextIO.output(str, s)

fun every P ss =
    case Substring.getc ss of
      NONE => true
    | SOME (c, ss') => P c andalso every P ss'

val verbstr = "%|^$!()*&"
fun find_verbchar ss = let
  fun loop n = let
    val candidate = String.extract(verbstr,n,SOME 1)
  in
    if occurs candidate ss then loop (n + 1)
    else candidate
  end
in
  loop 0
end handle Subscript =>
           raise Fail "bracketed string with too many exotic characters!"

fun print_verb1(ss, ostr) = let
  val c = find_verbchar ss
in
  out(ostr, "{\\small\\verb" ^ c);
  out(ostr, Substring.string ss);
  out(ostr, c ^ "}")
end

fun print_verbblock (ss, ostr) =
    (out(ostr,"\\begin{Verbatim}");
     out(ostr, Substring.string ss);
     out(ostr, "\\end{Verbatim}\n"))

(*
fun print_verbblock (ss, ostr) =
    (out(ostr, "{\\par\\samepage\\setseps\\small\n");
     out(ostr,"\\begin{verbatim}");
     out(ostr, Substring.string ss);
     out(ostr, "\\end{verbatim}}"))
*)

val lastminute_fixes =
    String.translate (fn #"#" => "\\#"
                       | #"&" => "\\&"
                       | #"_" => "\\_"
                       | c => str c)

fun print_markup(m, ostr) =
    case m of
      PARA => out(ostr, "\n\n")
    | TEXT ss => out(ostr, lastminute_fixes (Substring.string ss))
    | BRKT ss => print_verb1(ss, ostr)
    | XMPL ss => print_verbblock(ss, ostr)

fun print_type (ss, ostr) =
    if occurs "\n" ss then
      (out(ostr, "{\\small\n\\begin{verbatim}");
       out(ostr, Substring.string ss);
       out(ostr, "\n\\end{verbatim}\n}\\egroup\n\n"))
    else
      (out(ostr, "\\noindent");
       print_verb1(ss, ostr);
       out(ostr, "\\egroup\n\n"))

fun print_list(ssl, ostr) =
    case ssl of
      [] => ()
    | [x] => out(ostr, lastminute_fixes (Substring.string x))
    | x::xs => (out(ostr, lastminute_fixes (Substring.string x) ^ ", ");
                print_list (xs, ostr))

fun indent_munge mlist =
    case mlist of
      [] => []
    | ((x as XMPL _) :: (t as TEXT ts) :: rest) =>
      if every Char.isSpace ts then
        x :: indent_munge rest
      else
        x :: TEXT (Substring.full "\\noindent ") :: t :: indent_munge rest
    | m::ms => m :: indent_munge ms


val ignored_sections = ["KEYWORDS", "LIBRARY", "STRUCTURE", "DOC"]
fun should_ignore s = List.exists (fn t => t = s) ignored_sections

fun print_section(s, ostr) =
    case s of
      TYPE ss => print_type(ss,ostr)
    | FIELD (s, mlist) =>
      if should_ignore s then ()
      else (out(ostr, "\\" ^ s ^ "\n");
            app (fn m => print_markup(m, ostr)) (indent_munge mlist);
            out(ostr, "\n\n"))
    | SEEALSO ssl => (out(ostr, "\\SEEALSO\n");
                      print_list (ssl, ostr);
                      out(ostr, ".\n\n"))

fun print_docpart (slist, ostr) = let
  fun find_structpart [] = NONE
    | find_structpart (FIELD("STRUCTURE", [TEXT m])::_) = SOME m
    | find_structpart (_ :: t) = find_structpart t
  fun find_docpart [] = raise Fail "Can't happen - empty section list"
    | find_docpart (FIELD("DOC", [TEXT m]) :: _) = m
    | find_docpart (_ :: t) = raise Fail "Can't happen \\DOC not first entry"
  val docpart = lastminute_fixes (Substring.string (find_docpart slist))
  val prettypart =
      case find_structpart slist of
        NONE => docpart
      | SOME ss => docpart ^ "\\hfill(" ^
                   lastminute_fixes (Substring.string ss) ^ ")"
in
  out (ostr, "\\DOC{"^docpart^"}{"^prettypart^"}\n\n")
end


fun do_the_work dir dset outstr = let
  fun appthis dnm = let
    val cname = core_dname dnm
    val file = parse_file (OS.Path.concat(dir,dnm ^ ".doc"))
  in
    print_docpart(file, outstr);
    app (fn s => print_section (s,outstr)) file;
    out(outstr, "\\ENDDOC\n\n")
  end
in
  Binaryset.app appthis dset
end


fun main () =
    case CommandLine.arguments() of
      [docdir, texfile] => let
        val texfstr = TextIO.openAppend texfile
        val docfiles = find_docfiles docdir
      in
        do_the_work docdir docfiles texfstr;
        TextIO.closeOut texfstr;
        OS.Process.exit OS.Process.success
      end
    | _ =>
      (warn ("Usage: "^CommandLine.name()^ " <doc directory> <TeX file>\n");
       OS.Process.exit OS.Process.failure);


end (* struct *)
