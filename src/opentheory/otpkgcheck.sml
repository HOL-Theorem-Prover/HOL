(* ========================================================================
   otpkgcheck -- check an OpenTheory package description's import graph

       otpkgcheck FILE.thy ...

   A block of a .thy file is composed in an environment built from the
   blocks its own `import:` lines name.  When a block's article mentions a
   constant or type operator that another block of the same file defines,
   and that block is not imported, opentheory's removeDead pass ends up
   holding one symbol of that name undefined and another defined, and
   rejects the package with

       different constants named "..."

   -- after the whole tree has been built, and naming only the first such
   symbol.  This program decides the same question from the articles
   alone, in seconds, and names every missing import at once.

   opentheory will accept a longer route in some cases: a definition
   travels through an intermediate block when that block's own exported
   theorems happen to mention the symbol.  We deliberately do not model
   that.  Relying on it makes a package description fragile -- which
   theorems an article exports is not something a .thy file controls, so
   a package that only just composes today can break when an unrelated
   script gains or loses a theorem.  Requiring the direct import is both
   simpler to check and stable under that kind of change.

   A .thy whose articles have not been built is skipped, so this is a
   no-op outside an OpenTheory-kernel build.

   A block that relies on a longer route today is recorded in FILE.imports-ok
   beside FILE.thy, one `block import' pair to a line, so that the existing
   ones do not have to be settled before the check can catch new ones.
   ======================================================================== *)

fun out s = TextIO.output(TextIO.stdOut, s)
fun err s = TextIO.output(TextIO.stdErr, s)
fun die s = (err ("otpkgcheck: " ^ s ^ "\n");
             OS.Process.exit OS.Process.failure)

(* ---- strings ---------------------------------------------------------- *)

fun trim s =
  Substring.string (Substring.dropr Char.isSpace
                      (Substring.dropl Char.isSpace (Substring.full s)))

fun afterPrefix p s =
  if String.isPrefix p s then SOME (trim (String.extract(s, size p, NONE)))
  else NONE

fun unquote s =
  if size s >= 2 andalso String.sub(s, 0) = #"\"" andalso
     String.sub(s, size s - 1) = #"\""
  then String.substring(s, 1, size s - 2) else s

val tokens = String.tokens Char.isSpace

(* ---- string sets, as sorted duplicate-free lists ----------------------- *)

fun insert (x, []) = [x]
  | insert (x, l as y :: ys) =
    case String.compare (x, y) of
        LESS => x :: l
      | EQUAL => l
      | GREATER => y :: insert (x, ys)

fun mkSet l = List.foldl insert [] l
fun member (x, l) = List.exists (fn y => y = x) l

(* ---- the .thy file ----------------------------------------------------- *)

type block = {name : string, imports : string list,
              article : string option, isPackage : bool,
              interp : (string * string) list}

fun parseInterp s =
  case afterPrefix "interpret:" s of
      NONE => NONE
    | SOME rest =>
      let
        val rest = case afterPrefix "const" rest of
                       SOME r => r
                     | NONE => getOpt (afterPrefix "type" rest, rest)
      in
        case String.fields (fn c => c = #"\"") rest of
            _ :: from :: mid :: to :: _ =>
            if trim mid = "as" then SOME (from, to) else NONE
          | _ => NONE
      end

fun blockHead s =
  if size s > 1 andalso String.sub(s, size s - 1) = #"{" then
    let val nm = trim (String.substring(s, 0, size s - 1)) in
      if nm <> "" andalso
         List.all (fn c => Char.isAlphaNum c orelse c = #"-" orelse c = #"_")
                  (explode nm)
      then SOME nm else NONE
    end
  else NONE

fun readThy path =
  let
    val is = TextIO.openIn path handle _ => die ("cannot read " ^ path)
    fun add (b : block, s) =
      let val {name, imports, article, isPackage, interp} = b in
        case afterPrefix "import:" s of
            SOME i => {name = name, imports = imports @ [i], article = article,
                       isPackage = isPackage, interp = interp}
          | NONE =>
        case afterPrefix "article:" s of
            SOME a => {name = name, imports = imports,
                       article = SOME (unquote a), isPackage = isPackage,
                       interp = interp}
          | NONE =>
        case afterPrefix "package:" s of
            SOME _ => {name = name, imports = imports, article = article,
                       isPackage = true, interp = interp}
          | NONE =>
        case parseInterp s of
            SOME p => {name = name, imports = imports, article = article,
                       isPackage = isPackage, interp = interp @ [p]}
          | NONE => b
      end
    fun loop (cur, acc) =
      case TextIO.inputLine is of
          NONE => List.rev (case cur of NONE => acc | SOME b => b :: acc)
        | SOME line =>
          let val s = trim line in
            case cur of
                NONE => (case blockHead s of
                             SOME nm =>
                             loop (SOME {name = nm, imports = [],
                                         article = NONE, isPackage = false,
                                         interp = []}, acc)
                           | NONE => loop (NONE, acc))
              | SOME b => if s = "}" then loop (NONE, b :: acc)
                          else loop (SOME (add (b, s)), acc)
          end
  in
    loop (NONE, []) before TextIO.closeIn is
  end

(* ---- an article's symbols --------------------------------------------- *)

(* `opentheory info --symbols` prints four sections, continuation lines
   indented by two spaces:
       N external type operators: ...
       N external constants: ...
       N defined type operators: ...
       N defined constants: ...
   Symbols are tagged by kind so a type operator and a constant of the
   same name stay distinct. *)

fun runSymbols art =
  let
    val tmp = OS.FileSys.tmpName ()
    val cmd = "opentheory info --symbols 'article:" ^ art ^ "' > " ^ tmp ^
              " 2>&1"
    val st = OS.Process.system cmd
    val is = TextIO.openIn tmp
    val txt = TextIO.inputAll is before TextIO.closeIn is
    val _ = OS.FileSys.remove tmp handle _ => ()
  in
    if OS.Process.isSuccess st then txt
    else die ("opentheory --symbols failed on " ^ art ^ "\n" ^ txt)
  end

datatype sect = EXT of string | DEF of string

fun sectOf line =
  let
    fun tag ("type" :: _) = SOME "type "
      | tag ("constants:" :: _) = SOME "const "
      | tag _ = NONE
  in
    case tokens line of
        _ :: "external" :: rest => Option.map EXT (tag rest)
      | _ :: "defined" :: rest => Option.map DEF (tag rest)
      | _ => NONE
  end

fun afterColon s =
  let
    fun go i = if i >= size s then s
               else if String.sub(s, i) = #":" then
                 String.extract (s, i + 1, NONE)
               else go (i + 1)
  in go 0 end

fun parseSymbols txt =
  let
    fun go ([], _, e, d) = (mkSet e, mkSet d)
      | go (l :: ls, sect, e, d) =
        let
          fun tagged t str = List.map (fn x => t ^ x) (tokens str)
        in
          case sectOf l of
              SOME (EXT t) =>
              go (ls, SOME (EXT t), tagged t (afterColon l) @ e, d)
            | SOME (DEF t) =>
              go (ls, SOME (DEF t), e, tagged t (afterColon l) @ d)
            | NONE =>
              if not (String.isPrefix "  " l) orelse trim l = "" then
                go (ls, NONE, e, d)
              else
                case sect of
                    SOME (EXT t) => go (ls, sect, tagged t l @ e, d)
                  | SOME (DEF t) => go (ls, sect, e, tagged t l @ d)
                  | NONE => go (ls, NONE, e, d)
        end
  in
    go (String.fields (fn c => c = #"\n") txt, NONE, [], [])
  end

fun applyInterp interp sym =
  let
    val (tag, name) =
      if String.isPrefix "type " sym
      then ("type ", String.extract (sym, 5, NONE))
      else ("const ", String.extract (sym, 6, NONE))
  in
    case List.find (fn (f, _) => f = name) interp of
        SOME (_, t) => tag ^ t
      | NONE => sym
  end

(* ---- the check --------------------------------------------------------- *)

fun fileExists f = OS.FileSys.access (f, []) handle _ => false

(* FILE.imports-ok: `block import' per line, # starts a comment *)
fun readAccepted path =
  let
    val f = OS.Path.joinBaseExt {base = OS.Path.base path,
                                 ext = SOME "imports-ok"}
  in
    if not (fileExists f) then []
    else
      let
        val is = TextIO.openIn f
        fun loop acc =
          case TextIO.inputLine is of
              NONE => List.rev acc
            | SOME l =>
              let
                val l = case CharVectorSlice.findi (fn (_, c) => c = #"#")
                                                   (CharVectorSlice.full l) of
                            SOME (i, _) => String.substring (l, 0, i)
                          | NONE => l
              in
                case tokens l of
                    [b, i] => loop ((b, i) :: acc)
                  | _ => loop acc
              end
      in
        loop [] before TextIO.closeIn is
      end
  end

fun checkThy path =
  let
    val dir = OS.Path.dir (OS.FileSys.fullPath path)
    val blocks = readThy path
    val accepted = readAccepted path
    fun resolve a = OS.Path.mkAbsolute {path = a, relativeTo = dir}
    val arts = List.mapPartial
                 (fn b => Option.map (fn a => (b, resolve a)) (#article b))
                 blocks
    val base = OS.Path.file path
  in
    if List.exists #isPackage blocks orelse
       List.exists (fn (_, a) => not (fileExists a)) arts
    then (out ("otpkgcheck: " ^ base ^ ": skipped (articles not built)\n"); 0)
    else
      let
        val syms = List.map
                     (fn (b, a) =>
                         let
                           val (e, d) = parseSymbols (runSymbols a)
                           val f = applyInterp (#interp b)
                         in
                           (#name b, (mkSet (List.map f e),
                                      mkSet (List.map f d)))
                         end)
                     arts
        fun symsOf n = Option.map #2 (List.find (fn (m, _) => m = n) syms)
        fun definerOf s =
          Option.map #1
            (List.find (fn (_, (_, d)) => member (s, d)) syms)
        fun check (n, (e, _)) =
          let
            val imports = case List.find (fn b => #name b = n) blocks of
                              SOME b => #imports b
                            | NONE => []
            fun ok p = List.exists (fn (b, i) => b = n andalso i = p) accepted
            fun wanted s =
              case definerOf s of
                  SOME p => if p <> n andalso not (member (p, imports)) andalso
                               not (ok p)
                            then SOME (p, s) else NONE
                | NONE => NONE
            val needs = List.mapPartial wanted e
            val ps = mkSet (List.map #1 needs)
            fun say p =
              let
                val ss = List.map #2 (List.filter (fn (q, _) => q = p) needs)
                val n' = length ss
                val shown = List.take (ss, Int.min (3, n'))
              in
                out (base ^ ": block '" ^ n ^ "' must import '" ^ p ^
                     "' [" ^ Int.toString n' ^ ": " ^
                     String.concatWith ", " shown ^
                     (if n' > 3 then ", ..." else "") ^ "]\n")
              end
          in
            List.app say ps; length ps
          end
      in
        List.foldl (fn (x, a) => a + check x) 0 syms
      end
  end

fun main () =
  let
    val args = CommandLine.arguments ()
    val _ = if null args then die "usage: otpkgcheck FILE.thy ..." else ()
    val n = List.foldl (fn (f, a) => a + checkThy f) 0 args
  in
    if n = 0 then OS.Process.exit OS.Process.success
    else (err ("otpkgcheck: " ^ Int.toString n ^ " missing import(s)\n");
          OS.Process.exit OS.Process.failure)
  end
