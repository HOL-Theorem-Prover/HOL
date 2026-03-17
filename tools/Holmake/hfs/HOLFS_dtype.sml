structure HOLFS_dtype =
struct

datatype CodeType =
         Theory of string
       | Script of string
       | Other of string

datatype ArticleType =
         RawArticle of string
       | ProcessedArticle of string

datatype File =
         SML of CodeType
       | SIG of CodeType
       | UO of CodeType
       | UI of CodeType
       | ART of ArticleType
       | DAT of string
       | Unhandled of string

fun map_CodeType f ct =
    case ct of
        Theory s => Theory (f s)
      | Script s => Script (f s)
      | Other s => Other (f s)

fun codeTypeToString (Theory s) = "Theory(" ^ String.toString s ^ ")"
  | codeTypeToString (Script s) = "Script(" ^ String.toString s ^ ")"
  | codeTypeToString (Other s) = "Other(" ^ String.toString s ^ ")"
fun articleTypeToString (RawArticle s) = "RawArticle(" ^ String.toString s ^ ")"
  | articleTypeToString (ProcessedArticle s) =
    "ProcessedArticle(" ^ String.toString s ^ ")"

fun fileToString (SML c) = "SML(" ^ codeTypeToString c ^ ")"
  | fileToString (SIG c) = "SIG(" ^ codeTypeToString c ^ ")"
  | fileToString (UO c) = "UO(" ^ codeTypeToString c ^ ")"
  | fileToString (UI c) = "UI(" ^ codeTypeToString c ^ ")"
  | fileToString (ART at) = "ART(" ^ articleTypeToString at ^ ")"
  | fileToString (DAT s) = "DAT(" ^ String.toString s ^ ")"
  | fileToString (Unhandled s) = "Unhandled(" ^ String.toString s ^ ")"

fun createDirIfNecessary s =
    if OS.FileSys.isDir s handle OS.SysErr _ => false then ()
    else if OS.FileSys.access(s,[]) then
      raise Fail ("createDirIfNecessary: path " ^ s ^
                  " already exists but is not a directory")
    else
      let val {dir,file} = OS.Path.splitDirFile s
      in
        if dir = "" then (* happens if s is a relative path *)
          if file = "" then ()
          else OS.FileSys.mkDir file
        else
          let val _ = createDirIfNecessary dir
          in
            if file <> "" then OS.FileSys.mkDir s
            else ()
          end
      end

end
