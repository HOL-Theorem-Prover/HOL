open Polyhash

val ptable = mkPolyTable (100, Fail "Profiler Not Found")

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
        val (result, timetaken) = time f x
        val _ = insert ptable (nm, timetaken)
      in
        result
      end
    | SOME {usr = usr0, sys = sys0, gc = gc0} => let
        val (result, {usr = usr1, sys = sys1, gc = gc1}) = time f x
        open Time
        val _ = insert ptable (nm, {usr = usr0 + usr1, gc = gc0 + gc1,
                                    sys = sys0 + sys1})
      in
        result
      end

fun reset1 nm = ignore (remove ptable nm)

fun reset_all () = filter (fn x => false) ptable

fun results () = Listsort.sort (fn (i1, i2) => String.compare(#1 i1, #1 i2))
                               (listItems ptable)


