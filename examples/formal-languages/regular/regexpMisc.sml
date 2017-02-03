structure regexpMisc :> regexpMisc = 
struct

fun succeed() = OS.Process.terminate OS.Process.success
fun fail() = OS.Process.terminate OS.Process.failure;

fun stdOut_print s = let open TextIO in output(stdOut,s); flushOut stdOut end;
fun stdErr_print s = let open TextIO in output(stdErr,s); flushOut stdErr end;

fun spread s [] = []
  | spread s [x] = [x]
  | spread s (h::t) = h::s::spread s t;

fun spreadln s k n [] = []
  | spreadln s k n [x] = [x]
  | spreadln s k n (h::t) =
      if n <= 0
        then h::s::"\n  "::spreadln s k k t
        else h::s::spreadln s k (n-1) t;

end
