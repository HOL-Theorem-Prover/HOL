open Polyhash

exception ProfileEntryNotFound

val ptable = mkPolyTable (100, ProfileEntryNotFound)

type time = Time.time
type call_info = {gc : time, sys : time, usr : time, n : int}

fun time f x = let
  val timer = Timer.startCPUTimer()
  val result = f x
  val timetaken = Timer.checkCPUTimer timer
in
  (result, timetaken)
end

fun profile nm f x =
    case peek ptable nm of
      NONE => let
        val (result, {usr,sys,gc}) = time f x
        val _ = insert ptable (nm, {usr = usr, gc = gc, sys = sys, n = 1})
      in
        result
      end
    | SOME {usr = usr0, sys = sys0, gc = gc0, n = n0} => let
        val (result, {usr = usr1, sys = sys1, gc = gc1}) = time f x
        open Time
        val _ = insert ptable (nm, {usr = usr0 + usr1, gc = gc0 + gc1,
                                    sys = sys0 + sys1, n = Int.+(n0,1)})
      in
        result
      end

fun reset1 nm = ignore (remove ptable nm) handle ProfileEntryNotFound => ()

fun reset_all () = filter (fn x => false) ptable

fun results () = Listsort.sort (fn (i1, i2) => String.compare(#1 i1, #1 i2))
                               (listItems ptable)


fun output_profile_result outstr (nm, {usr, sys, gc, n}) = let
  val pl = StringCvt.padLeft #" " 8
  fun print s = TextIO.output(outstr, s)
  val _ = print (StringCvt.padRight #" " 25 nm)
  val _ = print (StringCvt.padLeft #" " 7 (Int.toString n))
  val _ = print (pl (Time.toString usr)^" "^pl (Time.toString sys)^" "^
                 pl (Time.toString gc)^"\n")
in
  ()
end

fun output_profile_results out = app (output_profile_result out)

val print_profile_result = output_profile_result TextIO.stdOut

val print_profile_results = output_profile_results TextIO.stdOut
