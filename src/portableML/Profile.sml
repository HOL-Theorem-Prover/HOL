structure Profile :> Profile =
struct

open Binarymap

type time = Time.time
type call_info = {real:time, gc : time, sys : time, usr : time, n : int}

val ptable = ref (Binarymap.mkDict String.compare : (string,call_info)dict)

datatype 'a result = OK of 'a | Ex of exn

fun return (OK x) = x | return (Ex e) = raise e

fun time f x = let
  val timer2 = Timer.startRealTimer()
  val timer = Timer.startCPUTimer()

  val result = OK (f x) handle e => Ex e

  val timetaken = Timer.checkCPUTimes timer
  val timetaken2 = Timer.checkRealTimer timer2
in
  (result, (timetaken,timetaken2))
end

type timedata = {nongc : {usr:Time.time, sys: Time.time},
                 gc : {usr:Time.time, sys: Time.time}}

fun add_profile nm timefx =
    case peek (!ptable, nm) of
      NONE => let
        val ({nongc,gc}:timedata,real) = timefx
        val data =
            {usr = #usr nongc, sys = #sys nongc, gc = Time.+(#usr gc, #sys gc),
             n = 1, real = real}
      in
        ptable := insert (!ptable, nm, data)
      end
    | SOME {usr = usr0, sys = sys0, gc = gc0, n = n0, real = real0} => let
        val ({nongc, gc}:timedata, real1) = timefx
        open Time
        val data =
            {usr = usr0 + #usr nongc, sys = sys0 + #sys nongc,
             gc = gc0 + #usr gc + #sys gc, n = Int.+(n0, 1),
             real = real0 + real1}
      in
        ptable := insert (!ptable, nm, data)
      end

fun profile_exn_opt do_exn do_ok do_both nm f x =
  let
    val (result, timefx) = time f x
    val _ = if do_both then add_profile nm timefx else ()
    val _ = case result of OK _ =>
        if do_ok then add_profile (nm ^ "_OK") timefx else ()
      | Ex e =>
        (case do_exn of NONE => ()
        | SOME false => add_profile (nm ^ "_exn") timefx
        | SOME true => add_profile (nm ^ "_" ^ exnName e) timefx)
  in
    return result
  end

fun profile nm = profile_exn_opt NONE false true nm
fun profile_with_exn nm = profile_exn_opt (SOME false) true true nm
fun profile_with_exn_name nm = profile_exn_opt (SOME true) true true nm
fun profile_no_exn nm = profile_exn_opt NONE true false nm

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
  fun foldl_map_this ((nm_width, real_width, usr_width, sys_width, gc_width, n_width),
                      (nm, {usr, sys, gc, real, n})) =
    let val usr = Time.toString usr
        val sys = Time.toString sys
        val gc = Time.toString gc
        val real = Time.toString real
        val n = Int.toString n
        fun max (i, s) = Int.max (i, String.size s)
    in
      ((max (nm_width, nm), max (real_width, real), max (usr_width, usr), max (sys_width, sys),
         max (gc_width, gc), max (n_width, n)),
       (nm, real, usr, sys, gc, n))
    end

  val ((nm_width, real_width, usr_width, sys_width, gc_width, n_width), strings) =
    foldl_map foldl_map_this ((25, 8, 8, 8, 8, 7), results)
  fun print s = TextIO.output (outstr, s)

  fun app_this (nm, real, usr, sys, gc, n) = (
    print (StringCvt.padRight #" " nm_width nm); print " ";
    print (StringCvt.padLeft #" " n_width n); print " ";
    print (StringCvt.padLeft #" " real_width real); print " ";
    print (StringCvt.padLeft #" " usr_width usr); print " ";
    print (StringCvt.padLeft #" " sys_width sys); print " ";
    print (StringCvt.padLeft #" " gc_width gc); print "\n"
  )
in
  List.app app_this (("Label","real","user","system","gc","#calls")::strings)
end

fun output_profile_result outstr result =
  output_profile_results outstr [result]

val print_profile_result = output_profile_result TextIO.stdOut

val print_profile_results = output_profile_results TextIO.stdOut

end
