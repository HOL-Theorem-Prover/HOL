case
  Lib.get_first Process.getEnv ["HOME",
                                (* windows things *)
                                "HOMEPATH", "APPDATA"]
of
  NONE => ()
| SOME d => let
    fun checkfor s = let
      val f = Path.concat(d,s)
    in
      if FileSys.access (f, [FileSys.A_READ]) then SOME f else NONE
    end
  in
    case Lib.get_first checkfor ["hol-config.sml", "hol-config.ML",
                                 ".hol-config", ".hol-config.sml",
                                 ".hol-config.ML"]
    of
      NONE => ()
    | SOME f => let
        val oldq = HOL_Interactive.amquiet()
      in
        print ("[Use-ing configuration file "^f^"]\n");
        oldq orelse HOL_Interactive.toggle_quietdec();
        use f;
        ignore (oldq orelse HOL_Interactive.toggle_quietdec())
      end
  end;


