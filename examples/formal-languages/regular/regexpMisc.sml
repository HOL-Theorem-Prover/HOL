structure regexpMisc :> regexpMisc =
struct

open HolKernel;

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

val one = IntInf.fromInt 1

fun bigUpto b t =
 let open IntInf
     fun up i A = if i > t then A else up (i + one) (i :: A)
 in
    List.rev (up b [])
 end;

fun bigIntervals ilist =
 let open IntInf
     val slist = Listsort.sort IntInf.compare ilist
     fun follows j i = (j = i) orelse (j = i + one)
     fun chop (left,last,[]) A = (left,last)::A
       | chop (left,last,h::t) A =
          if follows h last
           then chop (left,h,t) A
           else chop (h,h,t) ((left,last)::A)
 in
    case slist
      of [] => []
       | (i::t) => rev (chop (i,i,t) [])
 end;

val intervals =
    map (IntInf.toInt##IntInf.toInt) o bigIntervals o map IntInf.fromInt

fun twoE i = IntInf.pow (IntInf.fromInt 2,i);

end
