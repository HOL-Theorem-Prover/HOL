structure Doc2Tex =
struct

open ParseDoc


fun occurs s ss = not (Substring.isEmpty (#2 (Substring.position s ss)));
fun equal x y = (x = y)

fun stripdoc_suff s = String.extract(s, 0, SOME (size s - 4))
fun hasdoc_suff s =
    String.extract(s, size s - 4, NONE) = ".doc"
    handle Subscript => false

fun valid_doc_name s = hasdoc_suff s

fun core_dname dnm = let
  val toks = String.tokens (equal #".") dnm
in
  if length toks = 2 then hd (tl toks) else hd toks
end

fun structpart dnm =  hd (String.tokens (equal #".") dnm)


(* returns a set of file-names from the given directory that are .doc
   files *)
fun find_docfiles dirname = let
  val dirstr = FileSys.openDir dirname
  fun name_compare(s1,s2) = let
    (* names already less .doc suffix *)
    val lower = String.map Char.toLower
    val s1tok = lower (core_dname (Symbolic.tosymb s1))
    val s2tok = lower (core_dname (Symbolic.tosymb s2))
  in
    case String.compare (s1tok, s2tok) of
      EQUAL => String.compare(lower (structpart s1), lower (structpart s2))
    | x => x
  end
  fun insert s t =
      if valid_doc_name s then Binaryset.add(t, stripdoc_suff s)
      else (TextIO.output(TextIO.stdErr, "Ignoring: "^s^"\n"); t)
  fun loop acc =
      case FileSys.readDir dirstr of
        SOME s => loop (insert s acc)
      | NONE => (FileSys.closeDir dirstr; acc)
in
  loop (Binaryset.empty name_compare)
end

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
  TextIO.output(ostr, "{\\small\\verb" ^ c);
  TextIO.output(ostr, Substring.string ss);
  TextIO.output(ostr, c ^ "}")
end

fun print_verbblock (ss, ostr) =
    (TextIO.output(ostr, "{\\par\\samepage\\setseps\\small\n");
     TextIO.output(ostr,"\\begin{verbatim}");
     TextIO.output(ostr, Substring.string ss);
     TextIO.output(ostr, "\\end{verbatim}\n}"))

fun print_markup(m, ostr) =
    case m of
      PARA => TextIO.output(ostr, "\n\n")
    | TEXT ss => TextIO.output(ostr, Substring.string ss)
    | BRKT ss => print_verb1(ss, ostr)
    | XMPL ss => print_verbblock(ss, ostr)

fun print_type (ss, ostr) =
    if occurs "\n" ss then
      (TextIO.output(ostr, "{\\small\n\\begin{verbatim}");
       TextIO.output(ostr, Substring.string ss);
       TextIO.output(ostr, "\n\\end{verbatim}\n}\\egroup\n\n"))
    else
      (TextIO.output(ostr, "\\noindent");
       print_verb1(ss, ostr);
       TextIO.output(ostr, "\\egroup\n\n"))

fun print_list(ssl, ostr) =
    case ssl of
      [] => ()
    | [x] => TextIO.output(ostr, Substring.string x)
    | x::xs => (TextIO.output(ostr, Substring.string x ^ ", ");
                print_list (xs, ostr))

fun print_section(s, ostr) =
    case s of
      TYPE ss => print_type(ss,ostr)
    | FIELD (s, mlist) => (TextIO.output(ostr, "\\" ^ s);
                           app (fn m => print_markup(m, ostr)) mlist;
                           TextIO.output(ostr, "\n\n"))
    | SEEALSO ssl => (TextIO.output(ostr, "\\SEEALSO\n");
                      print_list (ssl, ostr);
                      TextIO.output(ostr, ".\n"))


fun do_the_work dir dset outstr = let
  fun appthis dnm = let
    val cname = core_dname dnm
    val file = parse_file (Path.concat(dir,dnm ^ ".doc"))
  in
    app (fn s => print_section(s,outstr)) file
  end
in
  Binaryset.app appthis dset
end


val _ =
    case CommandLine.arguments() of
      [docdir, texfile] => let
        val texfstr = TextIO.openOut texfile
        val docfiles = find_docfiles docdir
      in
        do_the_work docdir docfiles texfstr;
        TextIO.closeOut texfstr;
        OS.Process.exit OS.Process.success
      end
    | _ =>
      (TextIO.output(TextIO.stdErr,
                     "Usage: "^CommandLine.name()^
                     " <doc directory> <TeX file>\n");
       OS.Process.exit OS.Process.failure);


end (* struct *)