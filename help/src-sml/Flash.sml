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

val spinChars = "|/-\\"

fun initSpinner (prefix, total) = let
  val count = ref 0
  val clearLen = String.size prefix + 30
  val blanks = CharVector.tabulate (clearLen, fn _ => #" ")
  fun tick () =
    let
      val n = !count
      val remaining = total - n
      val c = String.sub (spinChars, n mod 4)
    in
      count := n + 1;
      print ("\r" ^ prefix ^ "[" ^ String.str c ^ "] " ^
             Int.toString remaining ^ " remaining   ");
      TextIO.flushOut TextIO.stdOut
    end
  fun finish () =
    (print ("\r" ^ blanks ^ "\r");
     TextIO.flushOut TextIO.stdOut)
in
  (tick, finish)
end

fun donowt() = ()
val null_pair = (donowt, donowt)

fun guarded mk p =
  case OS.Process.getEnv "TERM" of
    SOME "emacs" => null_pair
  | SOME "dumb" => null_pair
  | SOME _ => mk p
  | NONE => null_pair

fun initialise p = guarded init p
fun initialise_spinner p = guarded initSpinner p


end; (* struct *)
