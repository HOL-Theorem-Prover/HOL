(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure FindInPath:
sig
  (** Search in the process environment path, and look for an executable
    * with this name.
    *)
  val find: string -> FilePath.t option
end =
struct

  fun contents dir =
    let
      (** Loop through dirstream and accumulate list.
        * No need to reverse the result since dirstream is arbitrary order.
        *)
      val dirstream = Posix.FileSys.opendir (FilePath.toHostPath dir)
      fun loop acc =
        case Posix.FileSys.readdir dirstream of
          SOME s => loop (s :: acc)
        | NONE => acc
      val result = loop []
    in
      Posix.FileSys.closedir dirstream;
      result
    end


  fun isExecutable path =
    Posix.FileSys.access (FilePath.toHostPath path, [Posix.FileSys.A_EXEC])


  fun find name =
    let
      val dirs =
        List.map (FilePath.fromUnixPath o OS.Path.toUnixPath)
          (String.tokens (fn c => c = #":")
             (Option.valOf (Posix.ProcEnv.getenv "PATH")))

      fun executableInDir dir =
        (List.exists (fn x => x = name) (contents dir)
         andalso isExecutable (FilePath.join (dir, FilePath.fromFields [name])))
        handle _ => false
    in
      case List.find executableInDir dirs of
        SOME dir => SOME (FilePath.join (dir, FilePath.fromFields [name]))
      | NONE => NONE
    end
    handle _ => NONE

end
