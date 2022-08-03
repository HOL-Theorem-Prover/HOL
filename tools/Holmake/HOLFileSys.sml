structure HOLFileSys :> HOLFileSys =
struct

open HOLFS_dtype
open HFS_NameMunge

fun string_part0 (Theory s) = s
  | string_part0 (Script s) = s
  | string_part0 (Other s) = s
fun string_part1 (RawArticle s) = s
  | string_part1 (ProcessedArticle s) = s
fun string_part (UO c)  = string_part0 c
  | string_part (UI c)  = string_part0 c
  | string_part (SML c) = string_part0 c
  | string_part (SIG c) = string_part0 c
  | string_part (ART c) = string_part1 c
  | string_part (DAT s) = s
  | string_part (Unhandled s) = s

fun isProperSuffix s1 s2 =
    if size s1 < size s2 andalso String.isSuffix s1 s2 then
      SOME (String.substring(s2,0,size s2 - size s1))
    else NONE

fun toCodeType s = let
  val possprefix = isProperSuffix "Theory" s
in
  if (isSome possprefix) then Theory (valOf possprefix)
  else let
    val possprefix = isProperSuffix "Script" s
  in
    if isSome possprefix then Script (valOf possprefix)
    else Other s
  end
end

fun toArticleType s = let
  val possprefix = isProperSuffix ".ot" s
in
  if (isSome possprefix) then ProcessedArticle (valOf possprefix)
  else RawArticle s
end

fun toFile s0 = let
  val {base = s, ext} = OS.Path.splitBaseExt s0
in
  case ext of
    SOME "sml" => SML (toCodeType s)
  | SOME "sig" => SIG (toCodeType s)
  | SOME "uo"  => UO (toCodeType s)
  | SOME "ui"  => UI (toCodeType s)
  | SOME "art" => ART (toArticleType s)
  | SOME "dat" => if String.isSuffix "Theory" s then
                    DAT (String.extract(s,0,SOME(size s - 6)))
                  else Unhandled s0
  |    _       => Unhandled s0
end

fun extract_theory slist =
  case slist of
      [] => NONE
    | s :: rest => (case toFile s of
                        SML (Theory thy) => SOME thy
                      | _ => extract_theory rest)

fun codeToString c =
  case c of
    Theory s => s ^ "Theory"
  | Script s => s ^ "Script"
  | Other s  => s

fun articleToString c =
  case c of
    RawArticle s => s
  | ProcessedArticle s => s ^ ".ot"

fun fromFile f =
  case f of
    UO c  => codeToString c ^ ".uo"
  | UI c  => codeToString c ^ ".ui"
  | SIG c => codeToString c ^ ".sig"
  | SML c => codeToString c ^ ".sml"
  | ART c => articleToString c ^ ".art"
  | DAT s => s ^ "Theory.dat"
  | Unhandled s => s

fun fromFileNoSuf f =
  case f of
    UO c  => codeToString c
  | UI c  => codeToString c
  | SIG c => codeToString c
  | SML c => codeToString c
  | ART a => articleToString a
  | DAT s => s
  | Unhandled s => s




fun file_compare (f1, f2) = String.compare (fromFile f1, fromFile f2)

fun primary_dependent f =
    case f of
      UO c => SOME (SML c)
    | UI c => SOME (SIG c)
    | SML (Theory s) => SOME (SML (Script s))
    | SIG (Theory s) => SOME (SML (Script s))
    | DAT s => SOME (SML (Script s))
    | ART (RawArticle s) => SOME (SML (Script s))
    | ART (ProcessedArticle s) => SOME (ART (RawArticle s))
    | _ => NONE

fun readfn f = toFSfn false f (* eta-expanded for value restriction *)
fun readfn1 f (x,y) = toFSfn false (fn s => f(s,y)) x

fun writefn f = toFSfn true f (* eta-expanded for value restriction *)
fun writefn1 f (x,y) = toFSfn true (fn s => f(s,y)) x

fun toFS s = case HOLtoFS s of NONE => s | SOME {fullfile = s', ...} => s'

val closeIn = TextIO.closeIn
val closeOut = TextIO.closeOut
val flushOut = TextIO.flushOut
val input = TextIO.input
val inputAll = TextIO.inputAll
val inputLine = TextIO.inputLine
val openIn = readfn TextIO.openIn
val openOut = writefn TextIO.openOut
val openAppend = writefn TextIO.openAppend
val output = TextIO.output
val stdErr = TextIO.stdErr
val stdOut = TextIO.stdOut

fun stdErr_out s = (output (stdErr, s); flushOut stdErr)

fun print s = TextIO.print s
fun println s = print (s ^ "\n")

val modTime = readfn OS.FileSys.modTime
val setTime = writefn1 OS.FileSys.setTime
val access = readfn1 OS.FileSys.access
val A_READ = OS.FileSys.A_READ
val A_WRITE = OS.FileSys.A_WRITE
val A_EXEC = OS.FileSys.A_EXEC
fun exists_readable s = access(s, [A_READ])
val remove = writefn OS.FileSys.remove
fun rename{old,new} =
    writefn (fn s => OS.FileSys.rename {old = toFS old, new = s}) new

val isLink = readfn OS.FileSys.isLink
val isDir = OS.FileSys.isDir
val getDir = OS.FileSys.getDir
val chDir = OS.FileSys.chDir
val mkDir = OS.FileSys.mkDir
val rmDir = OS.FileSys.rmDir
type dirstream = HFS_NameMunge.dirstream
val openDir = HFS_NameMunge.openDir
val readDir = HFS_NameMunge.readDir
val closeDir = HFS_NameMunge.closeDir


fun read_files {dirname} P action =
    let
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop () =
          case readDir ds of
              NONE => closeDir ds
            | SOME nextfile =>
              (if P nextfile then action nextfile else (); loop())
    in
      loop() handle e => (closeDir ds; raise e);
      closeDir ds
    end

val read_files_with_objs = HFS_NameMunge.read_files_with_objs



end (* struct *)
