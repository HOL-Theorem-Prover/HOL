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
  ext ++ "lib",
  ext ++ "subWithProjectFile"
]

(* `source_only/` deliberately has no Holmakefile --
   directories below the project root join the project's directory set
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
  ext ++ "lib" ++ "Holmakefile",
  ext ++ "subWithProjectFile" ++ "holproject.toml",
  ext ++ "holproject.toml"
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
val () = touch (alt_ext ++ "holproject.toml")
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
  ext_excl_root ++ "drop" ++ "Holmakefile",
  ext_excl_root ++ "holproject.toml"
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

(* ---- inherit the external's own [exclude] ---- *)

val inh_ext = scratch ++ "inh_ext"
val inh_proj = scratch ++ "inh_proj"

fun ext_excludes (cfg : HMProject.config) =
    case #externals cfg of
        [{id = "ext", path = _, exclude = excl}] => excl
      | _ => (die "expected exactly one external named ext"; [])

fun excl_contains excl d =
    List.exists (fn p => OS.Path.mkCanonical p = OS.Path.mkCanonical d) excl

val () = List.app mkdirs [
  inh_ext ++ "keep",
  inh_ext ++ "skipme",
  inh_proj
]
val () = List.app touch [
  inh_ext ++ "keep" ++ "Holmakefile",
  inh_ext ++ "skipme" ++ "Holmakefile"
]
val () = write (inh_ext ++ "holproject.toml")
  ("name = \"inh_ext\"\nexclude = [\"skipme\"]\n")

val inh_ext_rel =
    OS.Path.mkRelative {path = inh_ext, relativeTo = inh_proj}
val () = write (inh_proj ++ "holproject.toml")
  ("name = \"inh_proj\"\n\
   \[projects.ext]\n\
   \path = \"" ^ String.toString inh_ext_rel ^ "\"\n")

val inh_cfg = HMProject.load { root = inh_proj }

val _ = tprint "external's own [exclude] is inherited into its config"
val _ =
  let val excl = ext_excludes inh_cfg
  in if excl_contains excl (inh_ext ++ "skipme") then OK ()
     else die ("excludes did not include skipme; got [" ^
               String.concatWith ", " excl ^ "]")
  end

val _ = tprint "discover_dirs honors inherited external exclude"
val _ =
  let val got = canon_set (HMProject.discover_dirs inh_cfg)
      val kept = OS.Path.mkCanonical (inh_ext ++ "keep")
      val skipped = OS.Path.mkCanonical (inh_ext ++ "skipme")
  in if Binaryset.member (got, kept) andalso
        not (Binaryset.member (got, skipped))
     then OK ()
     else die ("expected keep present, skipme absent; got " ^
               String.concatWith ", " (Binaryset.listItems got))
  end

val () = mkdirs (inh_ext ++ "other")
val () = touch (inh_ext ++ "other" ++ "Holmakefile")
val () = write (inh_proj ++ "holproject.toml")
  ("name = \"inh_proj\"\n\
   \[projects.ext]\n\
   \path = \"" ^ String.toString inh_ext_rel ^ "\"\n\
   \exclude = [\"other\"]\n")

val inh_cfg2 = HMProject.load { root = inh_proj }

val _ = tprint "consumer and inherited excludes union, not override"
val _ =
  let val got = canon_set (HMProject.discover_dirs inh_cfg2)
      val kept = OS.Path.mkCanonical (inh_ext ++ "keep")
      val skipped = OS.Path.mkCanonical (inh_ext ++ "skipme")
      val other = OS.Path.mkCanonical (inh_ext ++ "other")
  in if Binaryset.member (got, kept) andalso
        not (Binaryset.member (got, skipped)) andalso
        not (Binaryset.member (got, other))
     then OK ()
     else die ("expected keep present, skipme+other absent; got " ^
               String.concatWith ", " (Binaryset.listItems got))
  end

(* Grandchild project carrying its own holproject.toml is pruned by
   discover_under's hasProjFile filter regardless, so the recursion
   stays one-level even without explicit guard. *)
val () = List.app mkdirs [
  inh_ext ++ "sub",
  inh_ext ++ "sub" ++ "nope"
]
val () = List.app touch [
  inh_ext ++ "sub" ++ "Holmakefile",
  inh_ext ++ "sub" ++ "nope" ++ "Holmakefile"
]
val () = write (inh_ext ++ "sub" ++ "holproject.toml")
  ("name = \"grandchild\"\nexclude = [\"nope\"]\n")

val inh_cfg4 = HMProject.load { root = inh_proj }

val _ = tprint "external-of-external is not recursed into"
val _ =
  let val got = canon_set (HMProject.discover_dirs inh_cfg4)
      val sub = OS.Path.mkCanonical (inh_ext ++ "sub")
  in if not (Binaryset.member (got, sub))
     then OK ()
     else die "grandchild project dir leaked into discover_dirs"
  end

(* ---- inherit the external's own [external_includes] ---- *)

val ei_ext = scratch ++ "ei_ext"
val ei_proj = scratch ++ "ei_proj"
val ei_shared = scratch ++ "ei_shared"
val ei_myinc = scratch ++ "ei_myinc"

val () = List.app mkdirs [ei_ext, ei_proj, ei_shared, ei_myinc]

val ei_ext_rel = OS.Path.mkRelative {path = ei_ext, relativeTo = ei_proj}

val () = write (ei_ext ++ "holproject.toml")
  ("name = \"ei_ext\"\n\
   \external_includes = [\"../ei_shared\", \"$(HOLDIR)/src/whatever\"]\n")
val () = write (ei_proj ++ "holproject.toml")
  ("name = \"ei_proj\"\n\
   \[projects.ext]\n\
   \path = \"" ^ String.toString ei_ext_rel ^ "\"\n")

val ei_cfg = HMProject.load { root = ei_proj }

fun ext_inc (cfg : HMProject.config) = #external_includes cfg

val _ = tprint
   "inherited external_includes resolved against the external's root"
val _ = if excl_contains (ext_inc ei_cfg) ei_shared then OK ()
        else die ("got [" ^ String.concatWith ", " (ext_inc ei_cfg) ^ "]")

val _ = tprint "$(HOLDIR) is expanded in inherited external_includes"
val _ =
  let val expected = Systeml.HOLDIR ++ "src" ++ "whatever"
  in if excl_contains (ext_inc ei_cfg) expected then OK ()
     else die ("expected " ^ expected ^ "; got [" ^
               String.concatWith ", " (ext_inc ei_cfg) ^ "]")
  end

val () = write (ei_proj ++ "holproject.toml")
  ("name = \"ei_proj\"\n\
   \external_includes = [\"../ei_myinc\"]\n\
   \[projects.ext]\n\
   \path = \"" ^ String.toString ei_ext_rel ^ "\"\n")

val ei_cfg2 = HMProject.load { root = ei_proj }

val _ = tprint "consumer and inherited external_includes union, not override"
val _ =
  if excl_contains (ext_inc ei_cfg2) ei_shared andalso
     excl_contains (ext_inc ei_cfg2) ei_myinc
  then OK ()
  else die ("got [" ^ String.concatWith ", " (ext_inc ei_cfg2) ^ "]")

val () = write (ei_ext ++ "holproject.toml") "= = =\n"

val _ = tprint
   "malformed external holproject.toml aborts load with file path"
val _ =
  (HMProject.load { root = ei_proj };
   die "expected load to abort")
  handle Fail s =>
    if String.isSubstring (ei_ext ++ "holproject.toml") s
    then OK ()
    else die ("Fail raised but external path not in message: " ^ s)

val () = OS.FileSys.remove (ei_ext ++ "holproject.toml")

val _ = tprint
   "external with no holproject.toml aborts load with external's path"
val _ =
  (HMProject.load { root = ei_proj };
   die "expected load to abort")
  handle Fail s =>
    if String.isSubstring ei_ext s
    then OK ()
    else die ("Fail raised but external root not in message: " ^ s)

val () = rm_rf scratch
