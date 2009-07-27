structure Profile :> Profile =
struct

open Binarymap

type time = Time.time
type call_info = {gc : time, sys : time, usr : time, n : int}

val ptable = ref (Binarymap.mkDict String.compare : (string,call_info)dict)

datatype 'a result = OK of 'a | Ex of exn

fun return (OK x) = x | return (Ex e) = raise e

fun time f x = let
  val timer = Timer.startCPUTimer()
  val result = OK (f x) handle e => Ex e
  val timetaken = Timer.checkCPUTimer timer
in
  (result, timetaken)
end

fun profile nm f x =
    case peek (!ptable, nm) of
      NONE => let
        val (result, {usr,sys,gc}) = time f x
      in
        ptable := insert (!ptable, nm, {usr = usr, gc = gc, sys = sys, n = 1});
        return result
      end
    | SOME {usr = usr0, sys = sys0, gc = gc0, n = n0} => let
        val (result, {usr = usr1, sys = sys1, gc = gc1}) = time f x
        open Time
      in
        ptable := insert (!ptable, nm, {usr = usr0 + usr1, gc = gc0 + gc1,
                                     sys = sys0 + sys1, n = Int.+ (n0, 1)});
        return result
      end

fun reset1 nm =
    ptable := #1 (remove (!ptable, nm)) handle Binarymap.NotFound => ()

fun reset_all () = ptable := Binarymap.mkDict String.compare

fun results () = Listsort.sort (fn (i1, i2) => String.compare (#1 i1, #1 i2))
                               (listItems (!ptable))


fun output_profile_results outstr results =
let
  fun foldl_map_this ((nm_width, usr_width, sys_width, gc_width, n_width),
                      (nm, {usr, sys, gc, n})) =
    let val usr = Time.toString usr
        val sys = Time.toString sys
        val gc = Time.toString gc
        val n = Int.toString n
        fun max (i, s) = Int.max (i, String.size s)
    in
      ((max (nm_width, nm), max (usr_width, usr), max (sys_width, sys),
         max (gc_width, gc), max (n_width, n)),
       (nm, usr, sys, gc, n))
    end
  val ((nm_width, usr_width, sys_width, gc_width, n_width), strings) =
    Lib.foldl_map foldl_map_this ((25, 8, 8, 8, 7), results)
  fun print s = TextIO.output (outstr, s)
  fun app_this (nm, usr, sys, gc, n) = (
    print (StringCvt.padRight #" " nm_width nm); print " ";
    print (StringCvt.padLeft #" " n_width n); print " ";
    print (StringCvt.padLeft #" " usr_width usr); print " ";
    print (StringCvt.padLeft #" " sys_width sys); print " ";
    print (StringCvt.padLeft #" " gc_width gc); print "\n"
  )
in
  List.app app_this strings
end

fun output_profile_result outstr result =
  output_profile_results outstr [result]

val print_profile_result = output_profile_result TextIO.stdOut

val print_profile_results = output_profile_results TextIO.stdOut

end
