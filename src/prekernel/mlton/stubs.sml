(* Stubs for structures that are normally generated at configure time
   or are Poly/ML-specific *)

structure Systeml =
struct
  val HOLDIR = case OS.Process.getEnv "HOLDIR" of
                   SOME d => d
                 | NONE => raise Fail "HOLDIR not set"
  val release = "mlton"
  val version = 0
end

structure CoreReplVARS =
struct
  val linewidth = ref 72
end

structure Path = OS.Path
