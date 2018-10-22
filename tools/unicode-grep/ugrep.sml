local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate4 z
in
fun updateT z = let
  fun from chattiness files_wmatches help tests =
    {
      chattiness = chattiness, files_wmatches = files_wmatches, help = help,
      tests = tests
    }
  fun from' tests help files_wmatches chattiness =
    {
      chattiness = chattiness, files_wmatches = files_wmatches, help = help,
      tests = tests
    }
  fun to f {chattiness, files_wmatches, help, tests} =
    f chattiness files_wmatches help tests
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)


fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (warn s; OS.Process.exit OS.Process.failure)
fun succeed s = (print (s^"\n"); OS.Process.exit OS.Process.success)

type checkfn = bool -> string -> int -> (string * Substring.substring) -> bool

type t = {
  chattiness : int,
  files_wmatches : bool,
  help : bool,
  tests : (string * (checkfn * string)) list
};


(* acceptable Unicode characters are

                  UTF-8
    ‘   U+2018   0xE28098
    ’   U+2019   0xE28099
    “   U+201C   0xE2809C
    ”   U+201D   0xE2809D
*)

fun includes_unicode s =
  let
    val sz = size s
    fun recurse i =
      if i = sz then false
      else
        let val c = ord (String.sub(s,i))
        in
          if c = 0xE2 then quote_char2 (i + 1)
          else if c > 127 then true
          else recurse (i + 1)
        end
    and quote_char2 i =
        if i = sz then true
        else if ord (String.sub(s,i)) = 0x80 then quote_char3 (i + 1)
        else true
    and quote_char3 i =
        if i = sz then true
        else
          let val c = ord (String.sub(s,i))
          in
            if c = 0x98 orelse c = 0x99 orelse c = 0x9C orelse c = 0x9D then
              recurse (i + 1)
            else true
          end
  in
    recurse 0
  end

fun line_error qp fname linenum tag line =
  if qp then false
  else
    (print (fname^":"^Int.toString linenum^": " ^ tag ^ ": " ^ line);
     false)


fun check_unicode qp fname linenum (line,ss) =
  let
    val (p,s) = Substring.position "UOK" ss
  in
    if Substring.size s <> 0 then true
    else
      if includes_unicode line then
        line_error qp fname linenum "Unicode violation" line
      else true
  end

fun check_tabs qp fname linenum (line,ss) =
  let
    open Holmake_tools
    val (p,s) = Substring.position "\t" ss
    val highlightTAB =
        String.translate (fn c => if c = #"\t" then boldred "\\t" else str c)
  in
    if Substring.size s = 0 then true
    else
      line_error qp fname linenum "Includes TAB" (highlightTAB line)
  end

fun check_length qp fname linenum (line,ss) =
  let
    val sz = String.size line
  in
    if String.sub(line, sz - 1) <> #"\n" then
      line_error qp fname linenum "Last char not NL" line
    else if sz > 81 then
      line_error qp fname linenum "Line-length > 80" line
    else true
  end

fun check_twspace qp fname linenum (line,ss) =
  let
    val sz = String.size line
    val pos = if String.sub(line,sz - 1) = #"\n" then sz - 2 else sz - 1
  in
    if pos >= 0 andalso Char.isSpace (String.sub(line, pos)) then
      line_error qp fname linenum "Trailing whitespace" line
    else true
  end

fun checkfile (opts as {chattiness,files_wmatches,...}:t) sofar fname =
  let
    val istrm = TextIO.openIn fname
    fun recurse linenum sofar =
      case TextIO.inputLine istrm of
          NONE => (TextIO.closeIn istrm; sofar)
        | SOME line =>
          let
            val ss = Substring.full line
            val qp = (chattiness = 0) orelse files_wmatches
            fun foldthis ((_, (f, tag)), (b, tags)) =
              let
                val b' = f qp fname linenum (line,ss)
              in
                (b andalso b', if not b' then tag::tags else tags)
              end
            val (c, tags) = List.foldl foldthis (true, []) (#tests opts)
          in
            if not c andalso (files_wmatches orelse chattiness = 0) then
              (TextIO.closeIn istrm;
               if files_wmatches andalso chattiness > 0 then
                 print (fname ^ ": " ^ String.concatWith ", " tags ^ "\n")
               else ();
               false)
            else
              recurse (linenum + 1) (c andalso sofar)
          end
  in
    recurse 1 sofar
  end

fun is_generated opts fname =
  let
    open String
    val {base,ext} = OS.Path.splitBaseExt fname
    fun suff s = isSuffix s base
    fun suffs sl = List.exists suff sl
  in
    case ext of
        SOME "uo" => true
      | SOME "ui" => true
      | SOME "sig" => suffs ["Theory", "ML"]
      | SOME "sml" => suffs [".lex", ".grm", ".grm-sig", "Theory", "ML"]
      | _ => false
  end


fun do_dirstream opts dname ds sofar wlist =
  let
    fun recurse sofar dworklist =
      case OS.FileSys.readDir ds of
          NONE => (OS.FileSys.closeDir ds; (sofar, dworklist))
        | SOME fname =>
          let
            val fullp = OS.Path.concat(dname, fname)
          in
            if OS.FileSys.isLink fullp then recurse sofar dworklist
            else if OS.FileSys.isDir fullp then recurse sofar (fullp::dworklist)
            else
              let
                val {base,ext} = OS.Path.splitBaseExt fname
              in
                if (ext = SOME "sml" orelse ext = SOME "sig") andalso
                   not (is_generated opts fname) andalso
                   fname <> "selftest.sml" andalso
                   fname <> "EmitTeX.sml"
                then
                  recurse (checkfile opts sofar fullp) dworklist
                else
                  recurse sofar dworklist
              end
          end
  in
    recurse sofar wlist
  end
and do_dirs (opts:t) sofar wlist =
    case wlist of
        [] => sofar
      | d::res =>
        let
          val ds = OS.FileSys.openDir d
          val _ = if #chattiness opts > 1 then warn ("Checking "^d) else ()
          val (sofar, wlist) = do_dirstream opts d ds sofar res
        in
          do_dirs opts sofar wlist
        end

fun fupdbool sel b t = updateT t (U sel b) $$
fun fupdchattiness c t = updateT t (U #chattiness c) $$

val default : t =
    { help = false, chattiness = 1, files_wmatches = false,
      tests = [("unicode", (check_unicode, "Unicode present")),
               ("tabs", (check_tabs, "TAB present")),
               ("linelength", (check_length, "Line too long (or no final NL)")),
               ("trailing_wspace", (check_twspace, "Trailing whitespace"))]
    }

fun remove_test s sl =
  case sl of
      [] => []
    | (s',f) :: rest => if s' = s then rest else (s',f) :: remove_test s rest

fun fupdtests f t = updateT t (U #tests (f (#tests t))) $$

val options = let
  open GetOpt
in
  [
    {help = "show this message", long = ["help"], short = "h?",
     desc = NoArg (fn () => fupdbool #help true)},
    {help = "Just print files with problems", long = ["files-with-matches"],
     short = "l", desc = NoArg (fn () => fupdbool #files_wmatches true)},
    {help = "No line-length check", long = ["nolinelen"], short = "",
     desc = NoArg (fn () => fupdtests (remove_test "linelength"))},
    {help = "be less chatty", long = ["quiet"], short = "q",
     desc = NoArg (fn () => fupdchattiness 0)},
    {help = "allow Unicode", long = ["unicodeok"], short = "u",
     desc = NoArg (fn () => fupdtests (remove_test "unicode"))},
    {help = "be more verbose", long = [], short = "v",
     desc = NoArg (fn () => fupdchattiness 2)}
  ]
end

fun usage_str() =
  GetOpt.usageInfo {
    header =
        "Usage:\n\
        \  " ^ CommandLine.name() ^ " [options] dir1 dir2 .. dirn\n\n\
        \Recursively grep over dirs looking for style violations.",
    options = options
  }

fun read_cline args =
  GetOpt.getOpt { argOrder = GetOpt.Permute,
                  options = options,
                  errFn = warn }
                args



fun main() =
  let
    val (upds, args) = read_cline(CommandLine.arguments())
    val opts = List.foldl (fn (f,a) => f a) default upds
  in
    if #help opts then succeed (usage_str())
    else if null args then die (usage_str())
    else
      let
        val result = do_dirs opts true args
      in
        OS.Process.exit
          (if result then OS.Process.success else OS.Process.failure)
      end
  end


(*
#!/bin/bash

if [ $# -eq 1 ]
then
    if [ $1 = "-h" -o $1 = "-?" ]
    then
        echo "Usage:"
        echo "  $0 dir1 dir2 .. dirn"
        echo
        echo "Recursively grep over dirs looking for non-ASCII characters"
        echo "If no directories given, run in HOL's src directory"
        exit 0
    fi
fi

cmd="grep -R -n -v -E '^[[:print:][:space:]]*$|UOK' --include='*.sml' --exclude='*Theory.sml' --exclude='*Theory.sig' --exclude selftest.sml --exclude EmitTeX.sml"

if [ $# -eq 0 ]
then
    LC_ALL=C eval $cmd $(dirname $0)/../src/
else
    LC_ALL=C eval $cmd "$@"
fi
*)
