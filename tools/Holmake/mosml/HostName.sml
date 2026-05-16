(* Hostname lookup for Moscow ML builds.  Moscow ML's basis lacks the
   Posix module, so we fall back to shelling out via Mosml.run.  The
   Poly/ML and mlton paths use tools/Holmake/poly/HostName.sml. *)
structure HostName :> HostName =
struct
  fun get () =
      case Mosml.run "hostname" [] "" of
          Mosml.Success s =>
            if size s > 0 andalso String.sub (s, size s - 1) = #"\n"
            then String.substring (s, 0, size s - 1)
            else s
        | _ => ""
end
