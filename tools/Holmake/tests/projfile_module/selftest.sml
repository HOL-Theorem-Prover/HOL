open testutils

val op++ = OS.Path.concat

(* Build a synthetic project tree under ./scratch and exercise the
   HMProject API on it.  We do not run any external Holmake; this test
   is purely about the find_root / load / discover_dirs surface. *)

val scratch = OS.FileSys.getDir() ++ "scratch"

fun mkdirs p =
    if OS.FileSys.access (p, []) andalso
       (OS.FileSys.isDir p handle OS.SysErr _ => false)
    then ()
    else (mkdirs (OS.Path.getParent p); OS.FileSys.mkDir p)

fun touch p =
    let val s = TextIO.openOut p in TextIO.closeOut s end

fun write p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

val () = rm_rf scratch

val proj = scratch ++ "proj"
val ext = scratch ++ "extproj"

val () = List.app mkdirs [
  proj ++ "subA",
  proj ++ "subB" ++ "nested",
  proj ++ "subC",
  proj ++ "source_only",
  proj ++ "excluded_dir",
  proj ++ ".hol",
  proj ++ ".git",
  ext ++ "lib"
]

(* `source_only/` deliberately has no Holmakefile -- the new semantic
   is that directories below the project root join the project's set
   regardless. *)
val () = List.app touch [
  proj ++ "subA" ++ "Holmakefile",
  proj ++ "subB" ++ "Holmakefile",
  proj ++ "subB" ++ "nested" ++ "Holmakefile",
  proj ++ "subC" ++ "Holmakefile",
  proj ++ "excluded_dir" ++ "Holmakefile",
  proj ++ ".hol" ++ "Holmakefile",
  proj ++ ".git" ++ "Holmakefile",
  ext ++ "Holmakefile",
  ext ++ "lib" ++ "Holmakefile"
]

val ext_rel = OS.Path.mkRelative {path = ext, relativeTo = proj}
val () = write (proj ++ "holproject.toml")
  ("name = \"demo\"\n\
   \exclude = [\"excluded_dir\"]\n\
   \\n\
   \[projects.ext]\n\
   \path = \"" ^ String.toString ext_rel ^ "\"\n")

(* ---- find_root from a deep subdir ---- *)

val _ = tprint "HMProject.find_root walks up to project root"
val _ =
  case HMProject.find_root { start = proj ++ "subB" ++ "nested" } of
      SOME r => if OS.Path.mkCanonical r = OS.Path.mkCanonical proj then OK ()
                else die ("got " ^ r ^ ", expected " ^ proj)
    | NONE => die "got NONE"

val _ = tprint "HMProject.find_root returns NONE outside any project"
val _ =
  case HMProject.find_root { start = scratch } of
      NONE => OK ()
    | SOME r => die ("unexpected hit: " ^ r)

(* ---- load ---- *)

val cfg = HMProject.load { root = proj }

val _ = tprint "HMProject.load reads name"
val _ = if #name cfg = SOME "demo" then OK ()
        else die ("got " ^ Option.getOpt (#name cfg, "<none>"))

val _ = tprint "HMProject.load resolves exclude to absolute"
val _ =
  case #exclude cfg of
      [p] => if OS.Path.mkCanonical p =
                OS.Path.mkCanonical (proj ++ "excluded_dir")
             then OK () else die ("got " ^ p)
    | _ => die "expected exactly one exclude entry"

val _ = tprint "HMProject.load resolves externals to absolute"
val _ =
  case #externals cfg of
      [{id = "ext", path = p, exclude = _}] =>
        if OS.Path.mkCanonical p = OS.Path.mkCanonical ext then OK ()
        else die ("got " ^ p)
    | _ => die "expected exactly one external named ext"

(* ---- discover_dirs ---- *)

fun canon_set xs =
    Binaryset.addList
      (Binaryset.empty String.compare, List.map OS.Path.mkCanonical xs)

val _ = tprint "HMProject.discover_dirs includes every non-excluded dir"
val _ =
  let val got = canon_set (HMProject.discover_dirs cfg)
      val expected = canon_set [
        proj,
        proj ++ "subA",
        proj ++ "subB",
        proj ++ "subB" ++ "nested",
        proj ++ "subC",
        proj ++ "source_only",
        ext,
        ext ++ "lib"
      ]
  in if Binaryset.equal (got, expected) then OK ()
     else die ("got " ^ String.concatWith ", " (Binaryset.listItems got))
  end

val _ = tprint "HMProject.discover_dirs respects exclude and dot-dir skips"
val _ =
  let val got = canon_set (HMProject.discover_dirs cfg)
      val excluded = canon_set [
        proj ++ "excluded_dir",
        proj ++ ".hol",
        proj ++ ".git"
      ]
      val any_excluded =
          List.exists (fn d => Binaryset.member (got, d))
                      (Binaryset.listItems excluded)
  in if any_excluded then die "an excluded or dot-dir leaked into result"
     else OK ()
  end

(* ---- holproject.local.toml overrides project file's [projects.<id>] ---- *)

val alt_ext = scratch ++ "altproj"
val () = mkdirs (alt_ext ++ "sub")
val () = touch (alt_ext ++ "sub" ++ "Holmakefile")
val () = write (proj ++ "holproject.local.toml")
  ("[projects.ext]\npath = \"" ^ String.toString alt_ext ^ "\"\n")

val cfg2 = HMProject.load { root = proj }

val _ = tprint "holproject.local.toml overrides project file"
val _ =
  case #externals cfg2 of
      [{id = "ext", path = p, exclude = _}] =>
        if OS.Path.mkCanonical p = OS.Path.mkCanonical alt_ext then OK ()
        else die ("got " ^ p ^ ", expected " ^ alt_ext)
    | _ => die "expected exactly one external named ext"

val _ = tprint "discover_dirs follows the overridden external"
val _ =
  let val got = canon_set (HMProject.discover_dirs cfg2)
  in if Binaryset.member (got, OS.Path.mkCanonical (alt_ext ++ "sub"))
     then OK ()
     else die "altproj/sub not in discover_dirs output"
  end

(* ---- per-external [projects.<id>].exclude ---- *)

val ext_excl_root = scratch ++ "extexcl"
val () = List.app mkdirs [
  ext_excl_root ++ "keep",
  ext_excl_root ++ "drop"
]
val () = List.app touch [
  ext_excl_root ++ "keep" ++ "Holmakefile",
  ext_excl_root ++ "drop" ++ "Holmakefile"
]
val () = write (proj ++ "holproject.local.toml")
  ("[projects.ext]\npath = \"" ^ String.toString ext_excl_root ^ "\"\n\
   \exclude = [\"drop\"]\n")

val cfg3 = HMProject.load { root = proj }

val _ = tprint "load picks up [projects.<id>].exclude"
val _ =
  case #externals cfg3 of
      [{id = "ext", path = _, exclude = [d]}] =>
        if OS.Path.mkCanonical d =
           OS.Path.mkCanonical (ext_excl_root ++ "drop")
        then OK () else die ("exclude path: got " ^ d)
    | _ => die "expected one external with one exclude"

val _ = tprint "discover_dirs honors per-external exclude"
val _ =
  let val got = canon_set (HMProject.discover_dirs cfg3)
      val kept  = OS.Path.mkCanonical (ext_excl_root ++ "keep")
      val dropd = OS.Path.mkCanonical (ext_excl_root ++ "drop")
  in if Binaryset.member (got, kept) andalso
        not (Binaryset.member (got, dropd))
     then OK ()
     else die ("expected keep present, drop absent; got " ^
               String.concatWith ", " (Binaryset.listItems got))
  end

val () = rm_rf scratch
