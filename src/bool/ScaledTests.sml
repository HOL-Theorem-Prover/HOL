fun usr_time f x = let
  val t0 = #usr (Timer.checkCPUTimer Globals.hol_clock)
  val _ = f x
in
  Time.-(#usr (Timer.checkCPUTimer Globals.hol_clock), t0)
end

fun average f m n = let
  fun recurse m acc =
      if m = 0 then acc
      else recurse (m - 1) (Time.toReal (usr_time f n) :: acc)
  val results = recurse m []
in
  List.foldl Real.+ 0.0 results / real (length results)
end

fun test_upto {f,ntrials,max_size,filename} = let
  val outstr = TextIO.openOut filename
  fun recurse x =
      if x > max_size then ()
      else let
          val _ = print ("Run #"^Int.toString x^" ... ");
          val res = average f ntrials x
          val _ = print "done\n"
        in
          TextIO.output(outstr,
                        Int.toString x ^ "  " ^ Real.toString res ^ "\n");
          TextIO.flushOut outstr;
          recurse (x + 1)
        end
in
  recurse 1 ; TextIO.closeOut outstr
end
