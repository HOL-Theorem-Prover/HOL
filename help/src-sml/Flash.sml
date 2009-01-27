structure Flash :> Flash =
struct


val prelimstr = ref ""

fun init (s,t) = let
  val count = ref 0
  fun one () = (count := !count + 1;
                print ("\r"^s);
                print (StringCvt.padLeft #" " 4
                                         (Int.toString (!count * 100 div t)));
                print "%")
in
  (one, (fn () => print "\n"))
end

fun donowt() = ()

val initialise = let
  val null = (fn _ => (donowt, donowt))
in
  case OS.Process.getEnv "TERM" of
    SOME "emacs" => null
  | SOME "dumb" => null
  | SOME s => init
  | NONE => null
end


end; (* struct *)
