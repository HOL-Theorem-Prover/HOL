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
                    | GoodDir => recurse (smlp, (fname ^ "/") :: subs)
                    | SMLfile => recurse (true, subs)
                end
    in
      recurse (false, [])
    end


fun traverse ignores wlist A =
    case wlist of
        [] => A
      | [] :: ds => traverse ignores ds A
      | (d::ds) :: Ds =>
        let val (smlp, children0) = get_subdirs d
            fun goodWRTIgnores d =
                List.all (fn i => not (String.isSubstring i d)) ignores
            val children = List.filter goodWRTIgnores children0
            open OS.FileSys
        in
          if smlp then
            let val dstrm =
                    openDir (OS.Path.concat(d,".hol/logs"))
                    handle OS.SysErr _ => openDir(OS.Path.concat(d, ".hol/objs"))
            in
              closeDir dstrm;
              traverse ignores (children :: ds :: Ds) A
            end handle OS.SysErr _ =>
                       traverse ignores (children :: ds :: Ds) (d :: A)
          else traverse ignores (children :: ds :: Ds) A
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

fun usage_string() =
    CommandLine.name() ^ " [-h|-?] dir1 dir2 .. dirn\n" ^
    "  -h                  Show this message\n\
    \  --ignoring file     Ignore directories with prefixes from <file>\n\
    \  -?                  Show this message\n\n\
    \With no directories scan current directory and its children\n"

fun usage code =
    (TextIO.output(TextIO.stdErr, usage_string());
     OS.Process.exit code);

fun handleArgs slist =
    let
      val d = OS.FileSys.getDir()
      fun mkAbs s = OS.Path.mkAbsolute{path = s, relativeTo = d}
    in
      case slist of
          [] => (NONE, [[d]])
        | ["-h"] => usage OS.Process.success
        | ["-?"] => usage OS.Process.success
        | ["--ignoring"] => usage OS.Process.failure
        | "--ignoring" :: file :: rest => (SOME file, [map mkAbs rest])
        | "--" :: rest => (NONE, [map mkAbs rest])
        | d::ds => if size d > 0 andalso String.sub(d, 0) = #"-" then
                     usage OS.Process.failure
                   else (NONE, [map mkAbs slist])
    end

fun splitAtI pfx n slist =
    if n <= 0 then (pfx, slist)
    else
      case slist of
          [] => (pfx, slist)
        | s :: rest => splitAtI (s::pfx) (n - 1) rest

fun merge l1 l2 =
    case (l1, l2) of
        ([], _) => l2
      | (_, []) => l1
      | (s1 :: rest1, s2 :: rest2) =>
        case String.compare(s1,s2) of
            GREATER => s2 :: merge l1 rest2
         |  _ => s1 :: merge rest1 l2

fun merge_sort slist =
    case slist of
        [] => []
      | [s] => [s]
      | _ =>
        let
          val (l1, l2) = splitAtI [] (length slist div 2) slist
        in
          merge (merge_sort l1) (merge_sort l2)
        end

fun readIgnores filename =
    let val istrm = TextIO.openIn filename
        fun doit A = case TextIO.inputLine istrm of
                         NONE => (TextIO.closeIn istrm; A)
                       | SOME s => doit (s :: A)
        val lines = doit []
        fun dropWS s =
            let open Substring
                val ss = full s
            in
              string (dropl Char.isSpace (dropr Char.isSpace ss))
            end
    in
      map dropWS lines
    end


end (* struct *)
