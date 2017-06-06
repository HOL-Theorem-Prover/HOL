structure regexpMisc :> regexpMisc =
struct

fun succeed() = OS.Process.terminate OS.Process.success
fun fail() = OS.Process.terminate OS.Process.failure;

fun stdOut_print s = let open TextIO in output(stdOut,s); flushOut stdOut end;
fun stdErr_print s = let open TextIO in output(stdErr,s); flushOut stdErr end;

fun spread s [] = []
  | spread s [x] = [x]
  | spread s (h::t) = h::s::spread s t;

fun spreadln {sep:string, ln:string, width:int} =
 let fun spr n [] = []
       | spr n [x] = [x]
       | spr n (h::t) =
          if n <= 0
            then h::sep::ln::spr width t
            else h::sep::spr (n-1) t
 in
  spr width
 end;

fun bigUpto b t =
 let open IntInf
     val one = IntInf.fromInt 1
     fun up i A = if i > t then A else up (i + one) (i :: A)
 in
    List.rev (up b [])
 end;

end
