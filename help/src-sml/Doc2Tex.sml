structure Doc2Tex =
struct

open ParseDoc


fun occurs s ss = not (Substring.isEmpty (#2 (Substring.position s ss)));
fun equal x y = (x = y)

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun out(str,s) = TextIO.output(str, s)

fun every P ss =
    case Substring.getc ss of
      NONE => true
    | SOME (c, ss') => P c andalso every P ss'

fun mem x l = List.exists (fn e => e = x) l

val verbstr = "|^$!()*&+-@/'\""
fun find_verbchar avoids ss = let
  fun loop n = let
    val candidate = String.extract(verbstr,n,SOME 1)
  in
    if occurs candidate ss orelse mem candidate avoids then loop (n + 1)
    else candidate
  end
in
  loop 0
end handle Subscript =>
           raise Fail "bracketed string with too many exotic characters!"

fun findvc3 avoids ss =
  let
    val c1 = find_verbchar avoids ss
    val c2 = find_verbchar (c1::avoids) ss
    val c3 = find_verbchar (c1::c2::avoids) ss
  in
    (c1,c2,c3)
  end

fun mktheta (com,argl,argr) = [
  (UnicodeChars.ldquo, com ^ "ldquo" ^ argl ^ argr),
  (UnicodeChars.rdquo, com ^ "rdquo" ^ argl ^ argr),
  (UnicodeChars.sup_minus ^ UnicodeChars.sup_1,
   com ^ "(" ^ com ^ "sp" ^ argl ^ "-1" ^ argr ^ com ^ ")"),
  ("\194\171", com ^ "guillemotleft" ^ argl ^ argr),
  ("\194\187", com ^ "guillemotright" ^ argl ^ argr),
  ("\226\128\185", com ^ "guilsinglleft" ^ argl ^ argr),
  ("\226\128\186", com ^ "guilsinglright" ^ argl ^ argr)
]

fun print_verb1(ss, ostr) = let
  val vd = find_verbchar [] ss
  val (com,argl,argr) = findvc3 [vd] ss
  val verbtheta =
      map (fn (a,b) => {redex = a, residue = b}) (mktheta(com,argl,argr))
in
  out(ostr, "{\\small\\Verb[commandchars=" ^ String.concat [com,argl,argr] ^
            "]" ^ vd);
  out(ostr, stringfindreplace.subst verbtheta (Substring.string ss));
  out(ostr, vd ^ "}")
end

fun print_verbblock (ss, ostr) =
  let
    val (com,argl,argr) = findvc3 [] ss
    val verbtheta =
      map (fn (a,b) => {redex = a, residue = b}) (mktheta(com,argl,argr))
  in
    out(ostr,"\\begin{Verbatim}[commandchars=" ^ String.concat[com,argl,argr] ^
             "]\n");
    out(ostr, stringfindreplace.subst verbtheta (Substring.string ss));
    out(ostr, "\\end{Verbatim}\n")
  end

val lastminute_fixes =
    String.translate (fn #"#" => "\\#"
                       | #"&" => "\\&"
                       | #"_" => "\\_"
                       | c => str c)

fun print_markup(m, ostr) =
    case m of
      PARA => out(ostr, "\n\n")
    | TEXT ss => out(ostr, lastminute_fixes (Substring.string ss))
    | EMPH ss => out(ostr,
                     "\\emph{" ^ lastminute_fixes (Substring.string ss) ^ "}")
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

val verbose = ref false

fun do_the_work dir dset outstr = let
  fun appthis dnm = let
    val _ = if !verbose then warn ("Processing "^dnm) else ()
    val cname = core_dname dnm
    val file = parse_file (OS.Path.concat(dir,dnm ^ ".doc"))
               handle ParseError msg => die ("Parse error in "^dnm^": "^msg)
  in
    print_docpart(file, outstr);
    app (fn s => print_section (s,outstr)) file;
    out(outstr, "\\ENDDOC\n\n")
  end handle e => die ("Exception raised (" ^ dnm ^ ".doc): " ^
                       General.exnMessage e)
in
  Binaryset.app appthis dset
end


fun main () = let
  fun handle_args (docdir, texfile) = let
    val texfstr = TextIO.openAppend texfile
    val docfiles = find_docfiles docdir
  in
    do_the_work docdir docfiles texfstr;
    TextIO.closeOut texfstr;
    OS.Process.exit OS.Process.success
  end
in
  case CommandLine.arguments() of
    [docdir, texfile] => handle_args (docdir, texfile)
  | ["-v", docdir, texfile] => (verbose := true; handle_args(docdir,texfile))
  | _ =>
    (warn ("Usage: "^CommandLine.name()^
           " [-v] <doc directory> <TeX file>\n");
     warn ("  -v      be verbose about what's happening.");
     OS.Process.exit OS.Process.failure)
end


end (* struct *)
