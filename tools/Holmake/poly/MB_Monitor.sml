structure MB_Monitor :> MB_Monitor =
struct

open terminal_primitives ProcessMultiplexor Holmake_tools

fun nstr_subhandler f nm n s =
    f n s
    handle e =>
           die_with (General.exnName e ^ " raised by " ^ nm ^ " " ^
                     Int.toString n ^ " \"" ^ String.toString s ^ "\"")

val five_sec = Time.fromSeconds 5
val W_EXITED = Posix.Process.W_EXITED

fun Pstatus_to_string st =
  let
    open Posix.Process
  in
    case st of
        W_EXITED => "OK"
      | W_EXITSTATUS w8 => Word8.toString w8
      | W_SIGNALED s => "Signal "^SysWord.toString (Posix.Signal.toWord s)
      | W_STOPPED s => "Stopped "^SysWord.toString (Posix.Signal.toWord s)
  end

val green = boldgreen
val red = boldred

fun nextchar #"|" = #"/"
  | nextchar #"/" = #"-"
  | nextchar #"-" = #"\\"
  | nextchar #"\\" = #"|"
  | nextchar c = c

val time_units = [("m", 60), ("h", 60), ("d", 24)]

fun compact_time sz0 withsecs ld rd t =
    let
      val sz = sz0 - (size ld + size rd)
      val numSecs = Time.toSeconds t
      val n_s = LargeInt.toString numSecs
      val (su,sn) = if withsecs then ("s", 1) else ("", 0)
      fun helper i n =
          if i > 2 then ld ^ CharVector.tabulate(sz-1, fn _ => #"9") ^ "d" ^ rd
          else let
            val (u, f) = List.nth(time_units, i)
            val n' = LargeInt.div(n,f)
            val n'_s = LargeInt.toString n'
          in
            if size n'_s + 1 > sz then helper (i + 1) n'
            else StringCvt.padLeft #" " sz0 (ld ^ n'_s ^ u ^ rd)
          end
    in
      if size n_s + sn > sz then helper 0 numSecs
      else StringCvt.padLeft #" " sz0 (ld ^ n_s ^ su ^ rd)
    end

val yellow_timelimit = Time.fromSeconds 10
val red_timelimit = Time.fromSeconds 30

datatype monitor_status = MRunning of char
                        | Stalling of Time.time
(* statusString is always 3 characters; with a nonspace rightmost, except
   if it's showing exactly 3 space characters *)
fun statusString (MRunning c) = StringCvt.padLeft #" " 3 (str c)
  | statusString (Stalling t) =
    let
      val colourf = if Time.<(t, yellow_timelimit) then (fn x => x)
                    else if Time.<(t,red_timelimit) then boldyellow
                    else red
    in
      if Time.<(t, Time.fromSeconds 5) then "   "
      else colourf (compact_time 3 false "" "" t)
    end

fun rtrunc n s =
  if String.size s > n then
    "... " ^ String.substring(s, String.size s - (n - 4), n - 4)
  else StringCvt.padRight #" " n s
val rtrunc = nstr_subhandler rtrunc "rtrunc"

fun trashsfxes sfxes s =
  case List.find (fn sfx => String.isSuffix sfx s) sfxes of
      NONE => s
    | SOME sfx => substring(s,0,size s - size sfx)

fun polish0 tag =
  trashsfxes ["Theory", "Theory.sig", "Theory.sml", "Theory.dat"] tag

fun truncate width s =
  if String.size s > width then
    let
      open OS.Path
      val {arcs,isAbs,vol} = fromString s
      fun t s = truncate width s
    in
      if length arcs > 1 andalso String.size (hd arcs) >= 3 then
        t (".. " ^ toString {arcs=tl arcs,isAbs = false, vol = vol})
      else
        let
          val e = case ext s of NONE => "" | SOME s => s
        in
          if String.size e > 2 then t (base s ^ "..")
          else if width > 3 then
            String.substring(s,0,width-3) ^ ".."
          else
            String.substring(s,0,width)
        end
    end
  else s
val truncate = nstr_subhandler truncate "truncate"

fun polish tgtw s = StringCvt.padRight #" " tgtw (truncate tgtw (polish0 s))
val polish = nstr_subhandler polish "polish"


val cheat_string =      "Saved CHEAT _"
val fastcheat_string =  "Saved FAST-CHEAT _"
val oracle_string =     "Saved ORACLE thm _"
val used_cheat_string = "(used CHEAT)"

fun delsml_sfx s =
  if String.isSuffix ".sml" s orelse String.isSuffix ".sig" s then
    String.substring(s, 0, size s - 4)
  else if String.isSuffix "Theory.dat" s then
    String.substring(s, 0, size s - 4)
  else s

val width_check_delay = Time.fromMilliseconds 1000

type procinfo = {os : TextIO.outstream, tb : tailbuffer.t,
                 status : monitor_status, start_time : Time.time}

fun pinfo_upd (tb', stat) ({os,tb,status,start_time}:procinfo) =
    {os = os, tb = tb', status = stat, start_time = start_time}


fun prettydir dir =
    let
      (* input dir is already absolute *)
      val hmdir = Holmake_tools.hmdir.fromPath {origin = "/", path = dir}
      val dir = Holmake_tools.hmdir.pretty_dir hmdir
      val dir = Holmake_tools.nice_dir dir
      val {arcs,...} = OS.Path.fromString dir
      val arcs = if hd arcs = "~" orelse String.sub(hd arcs, 0) = #"$" then
                   tl arcs
                 else arcs
    in
      String.concatWith "/" arcs
    end

(* right align, and put dots on left *)
fun rlsquash_to wdth s =
    if wdth <= 0 then ""
    else if size s < wdth then
      StringCvt.padLeft #" " wdth s
    else if wdth <= 6 then
      (*   1 <= wdth <= 6 /\ wdth <= size s ==>
           size s + 1 - wdth IN [1..size s]
         and String.extract(s, size s, NONE) returns empty string
      *)
      " " ^ String.extract(s, size s + 1 - wdth, NONE)
    else
      (*   6 < wdth <= size s ==>
           size s + 4 - wdth IN [4..size s - 3]
         4 is fine as size s > 6, and size s - 3 < size s
      *)
      " ..." ^ String.extract(s, size s + 4 - wdth, NONE)

val rlsquash_to = nstr_subhandler rlsquash_to "rlsquash_to"

fun new {info,warn,genLogFile,time_limit,multidir} =
  let
    val monitor_map =
        ref (Binarymap.mkDict jobkey_compare : (jobkey,procinfo)Binarymap.dict)
    val last_width_check = ref (Time.now())
    val width = ref (getWidth())
    val last_child_cputime = let
      val {cutime,...} = Posix.ProcEnv.times()
    in
      ref cutime
    end

    fun Width () =
      let
        val t = Time.now()
      in
        if Time.>(Time.-(t, !last_width_check), width_check_delay) then
          (last_width_check := t; width := getWidth(); !width)
        else !width
      end
    val check_time =
        case time_limit of
            NONE => (fn (_,_,k) => k ())
          | SOME t => (fn (delay,key,k) =>
                          if Time.>(delay,t) then SOME(Kill key) else k())
    fun ttydisplay_map () =
      let
        val _ = print "\r"
        val width = Width()
        val job_count = Binarymap.numItems (!monitor_map)
      in
        if job_count > 1 then
          let
            val tgtw = width div job_count - 4
          in
            if tgtw >= 1 then (
              Binarymap.app (
                fn (jk as (_, {tag,dir}),{status,...}) =>
                   print (polish tgtw tag ^ statusString status ^ " ")
              ) (!monitor_map);
              print CLR_EOL
            ) else
              let fun foldthis ((_, {tag,dir}), {status,...}, worstopt) =
                      case status of
                          Stalling t => (case worstopt of
                                             NONE => SOME (tag,t,status)
                                           | SOME (tag0,t0,s0) =>
                                             if Time.<(t0,t) then
                                               SOME(tag,t,status)
                                             else worstopt)
                        | _ => worstopt
                  val worstopt =
                      Binarymap.foldl foldthis NONE (!monitor_map)
                  val pfx = Int.toString job_count ^ " jobs"
                  val pad = StringCvt.padRight #" " width
                  val print = print o pad
              in
                if width <= size pfx then print "Working"
                else if width <= size pfx + 25 then
                  print pfx
                else
                  case worstopt of
                      SOME (tag,_,status) =>
                      print (pfx ^ ": most stalled = " (* 17 chars *) ^
                             polish (width - (size pfx + 17))
                                    (tag ^ statusString status))
                    | NONE => print (pfx ^ ": all running")
              end
          end
        else
          case Binarymap.listItems (!monitor_map) of
              [] => ()
            | (jk as (_, {tag,dir}),{tb,status,...}) :: _ =>
              let
                val s = case tailbuffer.last_line tb of NONE => "" | SOME s => s
                val tgtw = width div 4
              in
                print (polish tgtw tag ^
                       rtrunc (width - tgtw - 5) (": " ^ s) ^ " " ^
                       (case status of
                            Stalling _ => statusString status
                          | _ => "   "));
                print CLR_EOL
              end
      end
    fun id (s:string) = s
    val (startmsg, infopfx, display_map, green, red, boldyellow, dim, bold,
         CLR_EOL) =
        if strmIsTTY TextIO.stdOut then
          ((fn s => ()), "\r", ttydisplay_map, green, red, boldyellow, dim,
           bold, CLR_EOL)
        else
          ((fn s => info ("Starting work on " ^ delsml_sfx s)), "",
           (fn () => ()),
           id, id, id, id, id, "")
    fun stdhandle jkey f =
      case Binarymap.peek (!monitor_map, jkey) of
          NONE => (warn ("Lost monitor info for "^jobkey_toString jkey); NONE)
        | SOME info => f info
    fun taginfo {tag,dir} dirstr timestr (colour,verdict) =
        let
          val sfxsz = size timestr + 7
          val sfxstr = timestr ^ colour (StringCvt.padLeft #" " 7 verdict)
          val remspace = Width() - (sfxsz + 1)
          val tagstr = delsml_sfx tag
          val tagsz = size tagstr
          fun maybe_dim s = if size s <> 0 then dim s else s
        in
          info (infopfx ^ tagstr ^
                maybe_dim (rlsquash_to (remspace - tagsz) dirstr) ^
                sfxstr ^ CLR_EOL)
        end
    fun lrpad (s1,s2) =
        let val w = Width () and sz1 = noesc_size s1 and sz2 = noesc_size s2
        in
          if sz1 + sz2 < w then
            s1 ^ CharVector.tabulate(w - (sz1 + sz2), fn _ => #" ") ^ s2
          else s1 ^ " " ^ s2
        end
    fun monitor msg =
      case msg of
          StartJob (jk as (_, {tag,...}), {dir}) =>
          let
            val strm = TextIO.openOut (genLogFile{tag = tag, dir = dir})
            val tb = tailbuffer.new {
                  numlines = 50,
                  patterns = [cheat_string, oracle_string, used_cheat_string,
                              fastcheat_string]
                }
          in
            monitor_map :=
              Binarymap.insert(!monitor_map, jk,
                               {os = strm, tb = tb, status = MRunning #"|",
                                start_time = Time.now()});
            startmsg tag;
            display_map();
            NONE
          end
        | Output(jk as (_, tag), t, chan, msg) =>
          stdhandle jk
            (fn (pinfo as {os = strm,tb,status=stat,...}) =>
                let
                  val stat' = case stat of MRunning c => MRunning (nextchar c)
                                         | Stalling _ => MRunning #"|"
                  open tailbuffer
                in
                  TextIO.output(strm,msg);
                  TextIO.flushOut strm;
                  monitor_map :=
                    Binarymap.insert(!monitor_map, jk,
                                     pinfo_upd (append msg tb, stat') pinfo);
                  display_map();
                  NONE
                end)
        | NothingSeen(jkey as (_, tag), {delay,...}) =>
          let
            fun after_check (pi as {os = strm, status = stat, tb, start_time}) =
              let
                val stat' =
                    case stat of
                        MRunning c => if Time.>(delay, five_sec) then
                                        Stalling delay
                                      else MRunning c
                      | Stalling _ => Stalling delay
              in
                monitor_map :=
                  Binarymap.insert(!monitor_map, jkey,
                                   pinfo_upd (tb, stat') pi);
                display_map();
                NONE
              end
          in
            stdhandle
              jkey
              (fn pinfo =>
                  check_time (delay, jkey, (fn () => after_check pinfo)))
          end
        | Terminated(jk as (_, td as {tag,dir}), st, _) =>
          stdhandle jk
            (fn {os = strm,tb,status=stat,start_time} =>
                let
                  val {fulllines,lastpartial,patterns_seen} =
                    tailbuffer.output tb
                  fun seen s = Holmake_tools.member s patterns_seen
                  val status_string = Pstatus_to_string st
                  val {cutime,...} = Posix.ProcEnv.times()
                  val this_childs_time = Time.-(cutime, !last_child_cputime)
                  val _ = last_child_cputime := cutime
                  val utstr = compact_time 6 true "(" ")" this_childs_time
                  val dirstr = if multidir then prettydir dir else ""
                  val tinfo = taginfo td dirstr utstr
                in
                  if st = W_EXITED then
                    if seen cheat_string orelse seen used_cheat_string then
                      tinfo (boldyellow, "CHEATED")
                    else if seen fastcheat_string then
                      tinfo (boldyellow, "F-CHEAT")
                    else
                      tinfo ((if seen oracle_string then boldyellow else green),
                             "OK")
                  else
                    (tinfo (red, "FAIL<" ^ status_string ^ ">");
                     List.app (fn s => info (" " ^ dim s)) fulllines;
                     if lastpartial <> "" then info (" " ^ dim lastpartial)
                     else ());
                  TextIO.closeOut strm;
                  monitor_map := #1 (Binarymap.remove(!monitor_map, jk));
                  display_map();
                  NONE
                end)
        | MonitorKilled(jk as (_, td as {tag,dir}), _) =>
          let
            val {cutime,...} = Posix.ProcEnv.times()
            val this_childs_time = Time.-(cutime,!last_child_cputime)
            val _ = last_child_cputime := cutime
            val utstr = compact_time 6 true "(" ")" this_childs_time
            val dirstr = if multidir then prettydir dir else ""
          in
            stdhandle jk
               (fn {os = strm,tb, status = stat,...} =>
                   (taginfo td dirstr utstr (red, "MKILLED");
                    TextIO.closeOut strm;
                    monitor_map := #1 (Binarymap.remove(!monitor_map, jk));
                    display_map();
                    NONE))
          end
        | _ => NONE
  in
    (monitor,
     {coloured_info =
      (fn (s1,s2) => info (lrpad (infopfx ^ s1, s2 ^ " " ^ CLR_EOL))),
      red = red, green = green, bold = bold})
  end



end
