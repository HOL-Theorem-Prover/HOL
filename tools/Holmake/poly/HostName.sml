(* Hostname lookup for Poly/ML (and mlton) builds of Holmake/build.
   Uses Posix.ProcEnv.uname; avoids the subprocess Mosml.run "hostname"
   would spawn (and the temp-files Mosml.run creates under it).  The
   Moscow ML build path uses tools/Holmake/mosml/HostName.sml instead,
   which calls Mosml.run since Posix isn't available there. *)
structure HostName : sig val get : unit -> string end =
struct
  fun get () =
      case List.find (fn (k,_) => k = "nodename") (Posix.ProcEnv.uname ()) of
          SOME (_, v) => v
        | NONE => ""
end
