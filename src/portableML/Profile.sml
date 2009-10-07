structure Profile :> Profile =
struct

open Binarymap

type time = Time.time
type call_info = {gc : time, sys : time, usr : time, n : int}

val ptable = ref (Binarymap.mkDict String.compare : (string,call_info)dict)

datatype 'a result = OK of 'a | Ex of exn

fun return (OK x) = x | return (Ex e) = raise e
fun is_Ex (Ex e) = true | is_Ex _ = false

fun time f x = let
  val timer = Timer.startCPUTimer()
  val result = OK (f x) handle e => Ex e
  val timetaken = Timer.checkCPUTimer timer
in
  (result, timetaken)
end

fun add_profile nm timefx =
    case peek (!ptable, nm) of
      NONE => let
        val {usr,sys,gc} = timefx
      in
        ptable := insert (!ptable, nm, {usr = usr, gc = gc, sys = sys, n = 1})
      end
    | SOME {usr = usr0, sys = sys0, gc = gc0, n = n0} => let
        val {usr = usr1, sys = sys1, gc = gc1} = timefx
        open Time
      in
        ptable := insert (!ptable, nm, {usr = usr0 + usr1, gc = gc0 + gc1,
                                     sys = sys0 + sys1, n = Int.+ (n0, 1)})
      end



fun profile_exn_opt do_exn do_ok do_both nm f x =
    let
        val (result, timefx) = time f x
        val _ = if do_both then add_profile nm timefx else ();
        val _ = if is_Ex result andalso do_exn then 
                  add_profile (nm ^ "_exn") timefx else ()
        val _ = if not (is_Ex result) andalso do_ok then 
                  add_profile (nm ^ "_OK") timefx else ()
    in
        return result
    end;

fun profile nm          = profile_exn_opt false false true nm;
fun profile_with_exn nm = profile_exn_opt true true true nm;
fun profile_no_exn nm   = profile_exn_opt false true false nm;


fun reset1 nm =
    ptable := #1 (remove (!ptable, nm)) handle Binarymap.NotFound => ()

fun reset_all () = ptable := Binarymap.mkDict String.compare

fun results () = Listsort.sort (fn (i1, i2) => String.compare (#1 i1, #1 i2))
                               (listItems (!ptable))


fun foldl_map _ (acc, []) = (acc, [])
  | foldl_map f (acc, x :: xs) =
    let val (acc', y) = f (acc, x)
        val (acc'', ys) = foldl_map f (acc', xs)
    in (acc'', y :: ys) end

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
    foldl_map foldl_map_this ((25, 8, 8, 8, 7), results)
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
