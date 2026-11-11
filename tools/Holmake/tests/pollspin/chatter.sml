(* A job that talks steadily and costs almost nothing to run.

   both/ needs a chatty neighbour for the hung-up job to hide behind,
   and the measurement there is the difference between a build with
   that neighbour and one without, so whatever the neighbour itself
   costs is noise.  A shell loop pacing itself with `sleep' spends a
   process per tick, and process creation is both expensive and
   erratic on a loaded machine -- enough, measured on a busy Mac, to
   swamp the difference being looked for.  One process that sleeps
   between writes costs nothing and varies by nothing.

   The gap matters: it has to stay under the work loop's idle grace,
   or a loop that judges idleness per round would get to pad between
   messages and the build would not provoke the spin it is meant
   to. *)

fun say i =
    (print ("chat " ^ Int.toString i ^ "\n");
     TextIO.flushOut TextIO.stdOut)

fun loop i =
    if i >= 400 then ()
    else (say i;
          OS.Process.sleep (Time.fromMilliseconds 5);
          loop (i + 1))

val _ = loop 0
