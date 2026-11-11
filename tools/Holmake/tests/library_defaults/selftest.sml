open testutils Holmake_types

fun default_target dir =
    let
      val cwd = OS.FileSys.getDir ()
      val path = OS.Path.concat (Systeml.HOLDIR, "src/" ^ dir)
      val _ = OS.FileSys.chDir path
      val (_, _, _, target) = ReadHMF.read "Holmakefile" (base_environment ())
      val _ = OS.FileSys.chDir cwd
    in
      target
    end

fun show_target NONE = "no default target"
  | show_target (SOME s) = s

fun check dir =
    (tprint ("Default target builds the whole " ^ dir ^ " library");
     require_msg (check_result (fn target => target = SOME "all"))
                 show_target default_target dir)

val _ = List.app check ["real", "floating-point"]
