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


fun max_bticks s =
    let fun doit prevbtcount mx i =
            if i < 0 then Int.max(mx,prevbtcount)
            else if String.sub(s, i) = #"`" then
              doit (prevbtcount + 1) mx (i - 1)
            else doit 0 (Int.max(prevbtcount, mx)) (i - 1)
    in
      doit 0 0 (size s - 1)
    end

fun brkt_text s =
    let val btcount = max_bticks s
        val btstring = CharVector.tabulate (btcount, fn _ => #"`")
    in
      if btcount = 0 then s
      else
        btstring ^ " " ^ s ^ " " ^ btstring
    end

val emph_text = String.translate (fn #"*" => "\\*" | c => str c)
fun xmpl_text s = "    " ^ String.translate (fn #"\n" => "\n    " | c => str c) s

fun html_linkify s = "[" ^ s ^ "](" ^ s ^ ".html)"

fun text_encode ss = let
  (* passes over a substring, replacing single apostrophes with &rsquo;
     backquotes with &lsquo; and the "latex" encodings of nice double-quotes:
     `` with &ldquo; and '' with &rdquo;
     Also encodes the < > and & characters into HTML appropriate forms. *)
  open Substring
  datatype state = backquote | apostrophe | normal of int * substring
  val lsquo = "\226\128\152"
  val rsquo = "\226\128\153"
  val ldquo = "\226\128\156"
  val rdquo = "\226\128\157"
  fun recurse acc s ss =
      case (s, getc ss) of
        (backquote, NONE) => (lsquo :: acc)
      | (apostrophe, NONE) => (rsquo :: acc)
      | (normal(n,ss0), NONE) => (string ss0 :: acc)
      | (normal (n,ss0), SOME(#"'", ss')) =>
          recurse (string (slice(ss0,0,SOME n)) :: acc) apostrophe ss'
      | (normal(n,ss0), SOME(#"`", ss')) =>
          recurse (string (slice(ss0,0,SOME n))::acc) backquote ss'
      | (normal(n,ss0), SOME(c, ss')) => recurse acc (normal(n + 1, ss0)) ss'
      | (apostrophe, SOME(#"'", ss')) =>
          recurse (rdquo :: acc) (normal(0,ss')) ss'
      | (apostrophe, SOME(#"`", ss')) =>
          recurse (rsquo :: acc) backquote ss'
      | (apostrophe, SOME _) =>
          recurse (rsquo :: acc) (normal(0,ss)) ss
      | (backquote, SOME(#"`", ss')) =>
          recurse (ldquo :: acc) (normal(0,ss')) ss'
      | (backquote, SOME(#"'", ss')) =>
          recurse (lsquo :: acc) apostrophe ss'
      | (backquote, SOME _) =>
          recurse (lsquo :: acc) (normal(0,ss)) ss
in
  String.concat (List.rev (recurse [] (normal(0,ss)) ss))
end

fun markdown (name,sectionl) ostrm =
    let fun out s = TextIO.output(ostrm, s)
        fun outss ss = out (Substring.string ss)
        fun mdtext elem =
            case elem of
                BRKT ss => out ("`" ^ brkt_text (Substring.string ss) ^ "`")
              | EMPH ss => out ("*" ^ emph_text (Substring.string ss) ^ "*")
              | PARA => out "\n\n"
              | TEXT ss => out (text_encode ss)
              | XMPL ss => out (xmpl_text (Substring.string ss))

        fun mdsection sec =
            case sec of
                SEEALSO sslist =>
                (out "\n### See also\n\n";
                 out (String.concatWith
                        ", "
                        (map (html_linkify o Substring.string) sslist));
                 out "\n\n")
              | TYPE ss => out ("\n```\n" ^ Substring.string ss ^ "\n```\n\n")
              | FIELD ("DOC", [TEXT ss]) => out ("## `" ^ brkt_text (Substring.string ss) ^ "`\n\n")
              | FIELD (secnm, textelems) =>
                case secnm of
                    "STRUCTURE" => ()
                  | "KEYWORDS" => ()
                  | _ => (out ("\n### " ^ trans_secnm secnm ^ "\n\n");
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
