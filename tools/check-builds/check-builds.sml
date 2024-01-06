structure check_builds =
struct
datatype filetype = GoodDir | SMLfile | Other

fun categorise f f0 =
    if OS.FileSys.isDir f then
      if String.sub(f0, 0) <> #"." then GoodDir else Other
    else case #ext (OS.Path.splitBaseExt f0) of
             SOME "sml" => SMLfile
           | _ => Other

fun get_subdirs d =
    let val ds = OS.FileSys.openDir d
        fun recurse (smlp, subs) =
            case OS.FileSys.readDir ds of
                NONE => (OS.FileSys.closeDir ds; (smlp, subs))
              | SOME fname0 =>
                let
                  val fname = OS.Path.concat(d,fname0)
                in
                  case categorise fname fname0 of
                      Other => recurse (smlp, subs)
                    | GoodDir => recurse (smlp, fname :: subs)
                    | SMLfile => recurse (true, subs)
                end
    in
      recurse (false, [])
    end


fun traverse wlist A =
    case wlist of
        [] => A
      | [] :: ds => traverse ds A
      | (d::ds) :: Ds =>
        let val (smlp, children) = get_subdirs d
        in
          if smlp then
            let val dstrm = OS.FileSys.openDir (OS.Path.concat(d,".holobjs"))
            in
              OS.FileSys.closeDir dstrm;
              traverse (children :: ds :: Ds) A
            end handle OS.SysErr _ => traverse (children :: ds :: Ds) (d :: A)
          else traverse (children :: ds :: Ds) A
        end


fun commonPrefix2 s1 s2 =
    let
      val limit = Int.min (size s1, size s2)
      fun recurse n =
          if n >= limit then n
          else if String.sub(s1, n) = String.sub(s2,n) then recurse (n + 1)
          else n
    in
      String.substring(s1, 0, recurse 0)
    end

fun commonPrefix slist =
    let fun recurse s0 slist =
            if size s0 = 0 then s0
            else
              case slist of
                  [] => s0
                | s :: ss => recurse (commonPrefix2 s0 s) ss
    in
      case slist of
          [] => ""
        | s::ss => recurse s ss
    end

fun handleArgs slist =
    let
      val d = OS.FileSys.getDir()
    in
      case slist of
          [] => [[d]]
        | ds => [map (fn s => OS.Path.mkAbsolute{path = s, relativeTo = d})
                     slist]
    end

fun main() =
    let val cline = CommandLine.arguments()
        val
    in
      case cline of
