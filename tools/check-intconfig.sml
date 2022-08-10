let
  fun checkfor f =
    if FileSys.access (f, [FileSys.A_READ]) then SOME f else NONE
  fun loadConfig f = let
      val oldq = HOL_Interactive.amquiet()
    in
      print ("[Use-ing configuration file "^f^"]\n");
      oldq orelse HOL_Interactive.toggle_quietdec();
      use f;
      ignore (oldq orelse HOL_Interactive.toggle_quietdec())
    end
in
  (* check if custom configuration is declared *)
  case Process.getEnv "HOL_CONFIG" of
    NONE =>
      (case
        Lib.get_first Process.getEnv ["HOME",
                                      (* windows things *)
                                      "HOMEPATH", "APPDATA"]
      of
        SOME dir =>
          Option.app loadConfig
            (Lib.get_first (fn s => checkfor (Path.concat(dir,s)))
              ["hol-config.sml", "hol-config.ML",
                ".hol-config", ".hol-config.sml",
                ".hol-config.ML"])
        | NONE => ())
    | SOME the_custom_config =>
      case checkfor the_custom_config of
        NONE => print ("[Ignoring configuration from HOL_CONFIG:"^ the_custom_config ^" (unreadable or empty)]\n")
        | SOME f => loadConfig f
end;
