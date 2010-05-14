structure Holmake_tools :> Holmake_tools =
struct


open Systeml

structure Path = OS.Path
structure FileSys = OS.FileSys

type output_functions = {warn : string -> unit, info : string -> unit,
                         tgtfatal : string -> unit,
                         diag : string -> unit}

fun output_functions {quiet_flag: bool, debug:bool} = let
  val execname = CommandLine.name()
  open TextIO
  fun msg strm s = (output(strm, execname ^ ": "^s^"\n"); flushOut strm)
  fun donothing _ = ()
  val warn = if not quiet_flag then msg stdErr else donothing
  val info = if not quiet_flag then msg stdOut else donothing
  val tgtfatal = msg stdErr
  val diag = if debug then msg stdErr else donothing
in
  {warn = warn, diag = diag, tgtfatal = tgtfatal, info = info}
end

fun do_lastmade_checks (ofns : output_functions) {no_lastmakercheck} = let
  val {warn,diag,...} = ofns
  val mypath = find_my_path()
  val _ = diag ("running "^mypath )
  fun write_lastmaker_file () = let
    val outstr = TextIO.openOut ".HOLMK/lastmaker"
  in
    TextIO.output(outstr, mypath ^ "\n");
    TextIO.closeOut outstr
  end handle IO.Io _ => ()

  val known_ok =
      if not no_lastmakercheck andalso
         FileSys.access (".HOLMK/lastmaker", [FileSys.A_READ])
      then let
          val _ = diag "Found a lastmaker file to look at."
          val istrm = TextIO.openIn ".HOLMK/lastmaker"
        in
          case TextIO.inputLine istrm of
            NONE => (warn "Empty Last Maker file";
                     TextIO.closeIn istrm;
                     write_lastmaker_file();
                     false)
          | SOME s => let
              open Substring
              val path = string (dropr Char.isSpace (full s))
              val _ = TextIO.closeIn istrm
            in
              if FileSys.access (path, [FileSys.A_READ, FileSys.A_EXEC])
              then
                mypath = path orelse
                (warn ("*** Switching to execute "^path);
                 Systeml.exec(path, "--nolmbc"::CommandLine.arguments()))
              else (warn "Garbage in Last Maker file";
                    write_lastmaker_file();
                    false)
            end
        end
      else (write_lastmaker_file(); false)
in
  if not known_ok andalso not no_lastmakercheck then let
      open FileSys
      val _ = diag "Looking to see if I am in a HOL distribution."
      fun checkdir () =
          access ("sigobj", [A_READ, A_EXEC]) andalso
          isDir "sigobj" andalso
          access ("bin/Holmake", [A_READ, A_EXEC])
      fun traverse () = let
        val d = getDir()
      in
        if checkdir() then
          SOME (Path.concat (d, "bin/Holmake"))
        else if Path.isRoot d then NONE
        else (chDir Path.parentArc; traverse())
      end
      val start = getDir()
    in
      case traverse () before chDir start of
        NONE => diag "Not in a HOL distribution"
      | SOME p =>
        if p = mypath then diag "In the right HOL distribution"
        else (warn ("*** Switching to execute "^p);
              Systeml.exec (p, "--nolmbc"::CommandLine.arguments()))
    end
  else ()
end

end (* struct *)
