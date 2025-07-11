structure HFS_NameMunge :> HFS_NameMunge =
struct


infix ++
val op++ = OS.Path.concat
exception DirNotFound
val HOLOBJDIR = ".hol/objs"
val HOLOBJDIR_arcs = [".hol", "objs"]
val HOLOBJDIR_arcs' = ["objs", ".hol"]
  (* yes, flipped, as they're inserted into a list that is then reversed;
     see insert_before_last *)

fun base_app {dirname} P action a0 =
    let
      open OS.FileSys
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop a =
          case readDir ds of
              NONE => (closeDir ds; a)
            | SOME nextfile =>
              loop (if P nextfile then action nextfile a else a)
    in
      loop a0 handle e => (closeDir ds; raise e) before
      closeDir ds
    end



fun insert_before_last A es [] = raise Fail "HFS_NameMunge: insert_before_last"
  | insert_before_last A es [last] = (List.rev (es @ A), last)
  | insert_before_last A es (h::t) = insert_before_last (h::A) es t

fun isPSuffix sfx s =
    size sfx < size s andalso String.isSuffix sfx s

fun last_and_revfront A [] = raise Fail "HFS_NameMunge: last_and_revfront"
  | last_and_revfront A [t] = (A, t)
  | last_and_revfront A (h::t) = last_and_revfront (h::A) t

(* nm is the filename as HOL thinks it is; if that name is fine, then the
   function returns NONE; otherwise the function returns SOME(name', dir)
   where the name' is the complete path to where the filename actually needs
   to be, and dir is the directory that may need to be checked for existence
*)
fun HOLtoFS nm =
    let
      val {isAbs, vol, arcs} = OS.Path.fromString nm
      val (parent_paths, file) = last_and_revfront [] arcs
      val {base,ext} = OS.Path.splitBaseExt file
      val changep =
          case (parent_paths, ext) of
              ("sigobj" :: _, _) => false
            | (_, SOME s) => s = "uo" orelse s = "ui" orelse
                             (isPSuffix "Theory" base andalso
                              (s = "sml" orelse s = "dat" orelse s = "sig"))
            | (_, NONE) => false
    in
      if changep then
        let
          val (arcs', last) = insert_before_last [] HOLOBJDIR_arcs' arcs
          val dir = OS.Path.toString {isAbs = isAbs, vol = vol, arcs = arcs'}
        in
          SOME {fullfile = OS.Path.concat(dir, last), dir = dir}
        end
      else NONE
    end

fun toFSfn writep f nm =
    let
      open OS.FileSys
      val aclist = (if writep then [A_WRITE] else []) @ [A_READ, A_EXEC]
    in
      case HOLtoFS nm of
          NONE => f nm
        | SOME {dir, fullfile = nm'} =>
          if OS.FileSys.access(dir, []) then
            if access(dir, aclist) andalso isDir dir
            then
              f nm'
            else raise Fail ("HFS_NameMunge: " ^ dir ^ " exists but is not " ^
                             "accessible directory")
          else if writep then
            (HOLFS_dtype.createDirIfNecessary dir; f nm')
          else f nm'
    end

type dirstream = string * OS.FileSys.dirstream * OS.FileSys.dirstream option ref

fun openDir s : dirstream =
    let val ds = OS.FileSys.openDir s
    in
      (s, ds, ref NONE)
    end

fun readDir (dirname, ds, r as ref subdsopt) =
    case subdsopt of
        NONE => (case OS.FileSys.readDir ds of
                     NONE => NONE
                   | SOME s =>
                     if s = ".hol" then
                       let val p = OS.Path.concat(dirname, HOLOBJDIR)
                       in
                         if OS.FileSys.isDir p handle OS.SysErr _ => false then
                           let val ds' = OS.FileSys.openDir p
                           in
                             case OS.FileSys.readDir ds' of
                                 NONE => (OS.FileSys.closeDir ds';
                                          OS.FileSys.readDir ds)
                               | SOME s' => (r := SOME ds'; SOME s')
                           end
                         else SOME s
                       end
                     else SOME s)
      | SOME ds' => (case OS.FileSys.readDir ds' of
                         NONE => (r := NONE;
                                  OS.FileSys.closeDir ds';
                                  OS.FileSys.readDir ds)
                       | SOME s => SOME s)

fun closeDir (_, ds, r as ref subdsopt) =
    (OS.FileSys.closeDir ds;
     case subdsopt of
         NONE => ()
       | SOME ds' => (OS.FileSys.closeDir ds'; r := NONE))

fun pushdir d f a0 =
    if OS.FileSys.isDir d handle OS.SysErr _ => false then
      let val d0 = OS.FileSys.getDir()
          val _ = OS.FileSys.chDir d
          val res = f a0 handle e => (OS.FileSys.chDir d0; raise e)
      in
        OS.FileSys.chDir d0;
        res
      end
    else a0


fun read_files_with_objs {dirname} P action a0 =
    base_app
      {dirname=dirname}
      (fn s => s = ".hol" orelse P s)
      (fn s => fn a =>
          if s = ".hol" then
            pushdir
              (dirname ++ HOLOBJDIR)
              (base_app
                 {dirname="."} P
                 (fn s =>
                     action {fakearcs=HOLOBJDIR_arcs, base = s}))
              a
          else action {fakearcs=[],base=s} a)
      a0

fun clean_last () =
    OS.FileSys.rmDir HOLOBJDIR handle OS.SysErr _ => ()

end (* struct *)
