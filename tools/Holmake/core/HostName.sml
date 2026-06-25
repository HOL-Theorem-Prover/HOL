(* Hostname lookup for Poly/ML and mlton builds.  Avoids the subprocess
   Mosml.run "hostname" would spawn (and the temp files it creates).
   The Moscow ML build path uses tools/Holmake/mosml/HostName.sml
   instead, which calls Mosml.run since Posix isn't available there. *)
structure HostName :> HostName =
struct
  fun get () =
      case List.find (fn (k,_) => k = "nodename") (Posix.ProcEnv.uname ()) of
          SOME (_, v) => v
        | NONE => ""
end
