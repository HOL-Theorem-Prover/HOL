structure HFS_NameMunge :> HFS_NameMunge =
struct


exception DirNotFound
val HOLOBJDIR = ".holobjs"

fun base_app {dirname} P action =
    let
      open OS.FileSys
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



fun insert_before_last A e [] = raise Fail "HFS_NameMunge: insert_before_last"
  | insert_before_last A e [last] = (List.rev (e::A), last)
  | insert_before_last A e (h::t) = insert_before_last (h::A) e t

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
                              (s = "sml" orelse s = "dat"))
            | (_, NONE) => false
    in
      if changep then
        let
          val (arcs', last) = insert_before_last [] HOLOBJDIR arcs
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
            (OS.FileSys.mkDir dir; f nm')
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
                     if s = HOLOBJDIR then
                       let val p = OS.Path.concat(dirname, s)
                       in
                         if OS.FileSys.isDir p then
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

fun pushdir d f =
    let val d0 = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir d
        val res = f () handle e => (OS.FileSys.chDir d0; raise e)
    in
      OS.FileSys.chDir d0;
      res
    end

fun read_files_with_objs {dirname} P action =
    base_app
      {dirname=dirname}
      (fn s => s = HOLOBJDIR orelse P s)
      (fn s => if s = HOLOBJDIR then
                 pushdir (OS.Path.concat(dirname, HOLOBJDIR))
                         (fn () => base_app {dirname="."} P action)
               else action s)

fun clean_last () =
    OS.FileSys.rmDir HOLOBJDIR handle OS.SysErr _ => ()

end (* struct *)
