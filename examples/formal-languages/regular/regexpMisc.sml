structure regexpMisc :> regexpMisc =
struct

fun succeed() = OS.Process.terminate OS.Process.success
fun fail() = OS.Process.terminate OS.Process.failure;

fun stdOut_print s = let open TextIO in output(stdOut,s); flushOut stdOut end;
fun stdErr_print s = let open TextIO in output(stdErr,s); flushOut stdErr end;

fun spread s [] = []
  | spread s [x] = [x]
  | spread s (h::t) = h::s::spread s t;

fun spreadlnWith {sep:string, ln:string, width:int} f =
 let fun spr n [] = []
       | spr n [x] = [f x]
       | spr n (h::t) =
          let val hstring = f h
           in if n <= 0
               then hstring::sep::ln::spr width t
               else hstring::sep::spr (n-1) t
           end
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
