structure Md2TeX =
struct

(* gets a directory and sorts the filenames into reasonable order for the reference manual (alphabetical by entry-point rather than structure name), also
   concatenates the files in that order, inserting

     \renewcommand{\currentstruct}{\texttt{<structname>}}

   before each one

*)

fun die s = (
  TextIO.output(TextIO.stdErr, s ^ "\n");
  OS.Process.exit OS.Process.failure
);

fun equal x y = (x = y)

val dotfields = String.fields (equal #".")
fun decode_stem s =
    case dotfields s of
        [x] => s
      | ["", x] => UC_ASCII_Encode.decode x
      | [str,x] => s
      | [str, "", x] => str ^ "." ^ UC_ASCII_Encode.decode x
      | _ => die ("decode_stem: badly encoded stem: " ^ s)


fun getMDFiles dir =
    let val dirStrm = OS.FileSys.openDir dir
        fun loop A =
            case OS.FileSys.readDir dirStrm of
                SOME f =>
                let
                  val {base,ext} = OS.Path.splitBaseExt f
                in
                  case ext of
                     SOME "md" =>
                     loop ((OS.Path.joinBaseExt {
                               base = decode_stem base,ext = ext
                             }, OS.Path.concat(dir,f))::A)
                   | _ => loop A
                end
              | NONE => (OS.FileSys.closeDir dirStrm;
                         A)
    in
      loop [] handle e => (
        OS.FileSys.closeDir dirStrm handle _ => ();
        die ("getMDFiles in " ^ dir ^ " threw exn " ^ General.exnMessage e)
      )
    end

fun takedrop n l = if n <= 0 then ([], l)
                   else case l of
                            [] => ([], [])
                          | h::t => let val (p,d) = takedrop (n - 1) t
                                    in
                                      (h::p, d)
                                    end

fun merge _ [] l2 = l2
  | merge _ l1 [] = l1
  | merge cmp (l1 as (h1::t1)) (l2 as (h2::t2)) =
    case cmp (h1,h2) of
        GREATER => h2 :: merge cmp l1 t2
      | _ => h1 :: merge cmp t1 l2

fun msort cmp l =
    case l of
        [] => []
      | [x] => [x]
      | _ => let val (p,s) = takedrop (length l div 2) l
             in
               merge cmp (msort cmp p) (msort cmp s)
             end

val lowerCase = CharVector.map Char.toLower
fun parts s =
    case dotfields s of
        [] => die "parts: no fields is impossible "
      | [x] => die "parts: 1 field is impossible"
      | [x,_] => (lowerCase x, "")
      | [x,y,_] => (lowerCase y,x)
      | _ => die "parts: >3 fields is impossible"

fun identCmp ((s1,_),(s2,_)) =
    let val (first1, second1) = parts s1
        val (first2, second2) = parts s2
    in
      case String.compare(first1, first2) of
        EQUAL => String.compare(second1, second2)
      | r => r
    end

fun catAFile fname =
    let val istrm = TextIO.openIn fname
        fun loop () = case TextIO.inputLine istrm of
                          SOME s => (print s ; loop())
                        | NONE => TextIO.closeIn istrm
    in
      loop()
    end handle e => die ("catAFile " ^ fname ^ ": exception raised " ^ General.exnMessage e)


fun output1 (fname,orig) =
    let val str_name = case dotfields fname of
                               [onlyOne, _] => "structure"
                             | [str, _, _] => str
                             | _ => die ("output1: dotfields impossible: "^fname)
    in
      print ("\n\\renewcommand{\\currentstruct}{\\texttt{" ^ str_name ^ "}}\n\n");
      catAFile orig
    end

fun printLn s = print (s ^ "\n")

fun doit dir =
    let val files = getMDFiles dir
        val sorted = msort identCmp files
    in
      (* List.app (fn (s1,s2) => printLn (s1 ^ " -- " ^ s2)) sorted *)
      List.app output1 sorted
    end

fun usage strm exitcode = (
  TextIO.output(
      strm,
      CommandLine.name() ^ " [<dirname> | -h]\n\n\
      \  dirname defaults to current directory if omitted.\n\
      \  -h displays this help message.\n");
  OS.Process.exit exitcode
);


fun main () =
    let
      val dir = case CommandLine.arguments() of
                    ["-h"] => usage TextIO.stdOut OS.Process.success
                  | [d] => d
                  | [] => OS.FileSys.getDir()
                  | _ => usage TextIO.stdErr OS.Process.failure
    in
      doit dir
    end




end
