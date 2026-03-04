(* check-intconfig.sml - User Configuration File Loading
   =====================================================

   This file is loaded at the end of interactive session initialization
   for both Poly/ML and Moscow ML. It checks for and loads user
   configuration files in the following order:

   1. If HOL_NOCONFIG environment variable is set, skip all config loading
   2. If --noconfig command line flag is present, skip all config loading
   3. If HOL_CONFIG environment variable is set, load that file
   4. Otherwise, look for these files in $HOME (or %APPDATA% on Windows):
      - hol-config.sml
      - hol-config.ML
      - .hol-config
      - .hol-config.sml
      - .hol-config.ML

   The configuration file can contain any SML code to customize the
   interactive environment (e.g., setting traces, loading libraries).
*)

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
  case Process.getEnv "HOL_NOCONFIG" of
      SOME _ => ()
    | NONE =>
      if List.exists (fn s => s = "--noconfig") (CommandLine.arguments()) then ()
      else
        (* check if custom configuration is declared *)
        case Process.getEnv "HOL_CONFIG" of
            NONE =>
            (case
                Lib.get_first Process.getEnv ["HOME",
                                              (* windows things *)
                                              "HOMEPATH", "APPDATA"]
               of
                  SOME dir =>
                  Option.app
                    loadConfig
                    (Lib.get_first (fn s => checkfor (Path.concat(dir,s)))
                                   ["hol-config.sml", "hol-config.ML",
                                    ".hol-config", ".hol-config.sml",
                                    ".hol-config.ML"])
                | NONE => ())
          | SOME the_custom_config =>
            case checkfor the_custom_config of
                NONE => print ("[Ignoring configuration from HOL_CONFIG:"^
                               the_custom_config ^" (unreadable or empty)]\n")
              | SOME f => loadConfig f
end;
