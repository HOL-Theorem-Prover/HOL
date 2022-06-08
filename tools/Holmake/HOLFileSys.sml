structure HOLFileSys :> HOLFileSys =
struct

open HOLFS_dtype

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

fun exists_readable s = OS.FileSys.access(s, [OS.FileSys.A_READ])

val closeIn = TextIO.closeIn
val closeOut = TextIO.closeOut
val flushOut = TextIO.flushOut
val input = TextIO.input
val inputAll = TextIO.inputAll
val inputLine = TextIO.inputLine
val openIn = TextIO.openIn
val openOut = TextIO.openOut
val output = TextIO.output
val stdErr = TextIO.stdErr
val stdOut = TextIO.stdOut

fun stdErr_out s = (TextIO.output (TextIO.stdErr, s);
                    TextIO.flushOut TextIO.stdErr)

fun print s = TextIO.print s
fun println s = print (s ^ "\n")

end (* struct *)
