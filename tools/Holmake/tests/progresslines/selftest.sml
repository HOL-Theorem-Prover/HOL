(* Where Holmake's output is going somewhere that won't act on a
   carriage return -- a log file, a pipe, an Emacs compilation buffer
   -- it must restrict itself to whole lines.

   The directory scan is the output that has to adapt: on a terminal
   it is an animation, one frame naming each directory as it is
   reached, each frame overwriting the last.  Printed one per line
   those frames are just noise, so off a terminal only the final
   frame, the summary of how many directories were scanned, is
   printed.  (The terminal rendering itself can't be checked from
   here: it would take a pty.)
*)

open testutils

infix ++
val op++ = OS.Path.concat
val holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"

fun readfile f =
    let val is = TextIO.openIn f
    in TextIO.inputAll is before TextIO.closeIn is
    end

(* Run Holmake to completion in testdir and return the lines it
   printed.  stdin comes from /dev/null so that nothing can prompt,
   and the redirection is the point of the test: it is what makes
   Holmake's stdout not a terminal.  `-r' is so that all three of the
   fixture's directories have something to build, which puts several
   jobs in front of the display at once -- the case whose frames used
   to run together into a single line. *)
fun hm_output () =
    let
      val d0 = OS.FileSys.getDir()
      val _ = OS.FileSys.chDir "testdir"
      val cmd = holmake ^ " -r --no-cache < /dev/null > output 2>&1"
      val res = OS.Process.system cmd
      val out = readfile "output"
      val _ = OS.FileSys.chDir d0
    in
      if OS.Process.isSuccess res then String.fields (fn c => c = #"\n") out
      else (die ("Holmake in testdir failed:\n" ^ out); [])
    end

val lines = hm_output ()

fun count p = List.length (List.filter p lines)
fun shown () = "Holmake printed:\n" ^ String.concatWith "\n" lines

val _ = tprint "Scan frames are not printed one per line"
val _ = case List.filter (String.isSubstring "Scanning ") lines of
            [] => OK()
          | ls => die ("per-directory scan lines:\n" ^
                       String.concatWith "\n" ls)

(* testdir and the two directories its INCLUDES names *)
val _ = tprint "The scan's last frame is printed, as a line"
val _ = case count (String.isSubstring "Scanned 3 directories") of
            1 => OK()
          | 0 => die ("no scan summary; " ^ shown())
          | n => die (Int.toString n ^ " scan summaries; " ^ shown())

(* The whole point: everything printed can be read as it stands. *)
val _ = tprint "No output line carries a carriage return"
val _ = case List.filter (String.isSubstring "\r") lines of
            [] => OK()
          | ls => die (Int.toString (length ls) ^ " line(s) with a CR; " ^
                       shown())
