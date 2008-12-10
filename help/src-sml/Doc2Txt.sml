structure Doc2Txt =
struct

open ParseDoc

val pagewidth = 70;

val separator = String.implode (List.tabulate(pagewidth, fn _ => #"-"))

fun out(str,s) = TextIO.output(str, s)
fun warn s = TextIO.output(TextIO.stdErr, s)

fun print_type strm ss = out(strm, Substring.string ss ^ "\n\n")

fun print_filled_words strm col wlist =
    case wlist of
      [] => col
    | (w::ws) => let
        val sz = Substring.size w
      in
        if col = 0 then
          (out(strm, Substring.string w);
           print_filled_words strm sz ws)
        else if sz + 1 + col > pagewidth then
          (out(strm, "\n"); print_filled_words strm 0 wlist)
        else
          (out(strm, " "); out(strm, Substring.string w);
           print_filled_words strm (col + sz + 1) ws)
      end

fun print_markups strm mlist =
    case mlist of
      [] => ()
    | (m::ms) => let
      in
        case m of
          PARA => (out(strm, "\n\n"); print_markups strm ms)
        | TEXT ss => (out(strm, Substring.string ss);
                      print_markups strm ms)
        | BRKT ss => (out(strm, "{" ^ Substring.string ss ^ "}");
                      print_markups strm ms)
        | XMPL ss => (out(strm, Substring.string ss);
                      print_markups strm ms)
      end


fun listify [] = raise Fail "Empty SEEALSO list -- impossible"
  | listify [x] = [Substring.full (Substring.string x ^ ".")]
  | listify (x::xs) = Substring.full (Substring.string x ^ ",") ::
                      listify xs

fun print_list strm ssl = print_filled_words strm 0 (listify ssl)

fun ignore_these s = List.exists (fn s' => s' = s) ["DOC", "STRUCTURE"]

fun write_section strm s =
    case s of
      TYPE ss => print_type strm ss
    | FIELD(s, mlist) =>
      if ignore_these s then ()
      else let
        in
          out(strm, s  ^ "\n");
          print_markups strm mlist;
          out(strm, "\n\n")
        end
    | SEEALSO ssl => (out(strm, "SEEALSO\n");
                      print_list strm ssl;
                      out(strm, "\n\n"))


fun print_docpart (slist, ostr) = let
  fun find_structpart [] = NONE
    | find_structpart (FIELD("STRUCTURE", [TEXT m])::_) = SOME m
    | find_structpart (_ :: t) = find_structpart t
  fun find_docpart [] = raise Fail "Can't happen - empty section list"
    | find_docpart (FIELD("DOC", [TEXT m]) :: _) = m
    | find_docpart (_ :: t) = raise Fail "Can't happen \\DOC not first entry"
  val docpart = Substring.string (find_docpart slist)
  val prettier =
      case find_structpart slist of
        NONE => docpart
      | SOME ss => docpart ^
                   (StringCvt.padLeft #" " (pagewidth - String.size docpart)
                                      ("(" ^ Substring.string ss ^ ")"))
in
  out (ostr, separator ^ "\n");
  out (ostr, prettier ^ "\n");
  out (ostr, separator ^ "\n")
end

fun do_one_file docdir destdir dname = let
  val file = parse_file (OS.Path.concat(docdir, dname ^ ".doc"))
  val outputstr = TextIO.openOut (OS.Path.concat(destdir, dname ^ ".adoc"))
in
  print_docpart (file, outputstr);
  app (write_section outputstr) file;
  out(outputstr, separator ^"\n");
  TextIO.closeOut outputstr
end


fun main () =
    case CommandLine.arguments() of
      [docdir, destdir] => let
        val docfiles = find_docfiles docdir
        open Binaryset
        val (tick,finish) =
            Flash.initialise ("Directory "^docdir^": ", numItems docfiles)
      in
        app (fn d => (do_one_file docdir destdir d; tick())) docfiles;
        finish();
        OS.Process.exit OS.Process.success
      end
    | _ =>
      (warn ("Usage: "^CommandLine.name()^ " <doc directory> "^
             "<destination directory>\n");
       OS.Process.exit OS.Process.failure);

end (* struct *)
