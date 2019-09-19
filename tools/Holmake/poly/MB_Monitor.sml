structure MB_Monitor :> MB_Monitor =
struct

open ProcessMultiplexor Holmake_tools

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

(* thanks to Rob Arthan for this function *)
fun strmIsTTY (outstream : TextIO.outstream) =
  let
    val (wr as TextPrimIO.WR{ioDesc,...},buf) =
	TextIO.StreamIO.getWriter(TextIO.getOutstream outstream);
    val _ =
        TextIO.setOutstream (outstream, TextIO.StreamIO.mkOutstream(wr, buf))
  in
    case ioDesc of
	NONE => false
      | SOME desc => (OS.IO.kind desc = OS.IO.Kind.tty)
  end

val green = boldgreen
val red = boldred

fun nextchar #"|" = #"/"
  | nextchar #"/" = #"-"
  | nextchar #"-" = #"\\"
  | nextchar #"\\" = #"|"
  | nextchar c = c

val time_units = [("m", 60), ("h", 60), ("d", 24)]

fun compact_time sz withsecs t =
    let
      val numSecs = Time.toSeconds t
      val n_s = LargeInt.toString numSecs
      val (su,sn) = if withsecs then ("s", 1) else ("", 0)
      fun helper i n =
          if i > 2 then CharVector.tabulate(sz-1, fn _ => #"9") ^ "d"
          else let
            val (u, f) = List.nth(time_units, i)
            val n' = LargeInt.div(n,f)
            val n'_s = LargeInt.toString n'
          in
            if size n'_s + 1 > sz then helper (i + 1) n'
            else StringCvt.padLeft #" " sz (n'_s ^ u)
          end
    in
      if size n_s + sn > sz then helper 0 numSecs
      else StringCvt.padLeft #" " sz (n_s ^ su)
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
      else colourf (compact_time 3 false t)
    end

fun rtrunc n s =
  if String.size s > n then
    "... " ^ String.substring(s, String.size s - (n - 4), n - 4)
  else StringCvt.padRight #" " n s

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
          else String.substring(s,0,width-3) ^ ".."
        end
    end
  else s

fun polish tgtw s = StringCvt.padRight #" " tgtw (truncate tgtw (polish0 s))

val cheat_string = "Saved CHEAT _"
val oracle_string = "Saved ORACLE thm _"
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


fun squash_to wdth s =
    if size s < wdth then StringCvt.padRight #" " wdth s
    else "..." ^ String.extract(s, size s - (wdth - 4), NONE) ^ " "


fun new {info,warn,genLogFile,time_limit} =
  let
    val monitor_map =
        ref (Binarymap.mkDict String.compare : (string,procinfo)Binarymap.dict)
    val last_width_check = ref (Time.now())
    val width = ref (getWidth())
    val last_child_cputime = ref Time.zeroTime
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
            Binarymap.app (fn (k,{status,...}) =>
                              print (polish tgtw k ^ statusString status ^ " "))
                          (!monitor_map);
            print CLR_EOL
          end
        else
          case Binarymap.listItems (!monitor_map) of
              [] => ()
            | (k,{tb,status,...}) :: _ =>
              let
                val s = case tailbuffer.last_line tb of NONE => "" | SOME s => s
                val tgtw = width div 4
              in
                print (polish tgtw k ^
                       rtrunc (width - tgtw - 5) (": " ^ s) ^ " " ^
                       (case status of
                            Stalling _ => statusString status
                          | _ => "   "));
                print CLR_EOL
              end
      end
    fun id (s:string) = s
    val (startmsg, infopfx, display_map, green, red, boldyellow, dim, CLR_EOL) =
        if strmIsTTY TextIO.stdOut then
          ((fn s => ()), "\r", ttydisplay_map, green, red, boldyellow, dim,
           CLR_EOL)
        else
          ((fn s => info ("Starting work on " ^ delsml_sfx s)), "",
           (fn () => ()),
           id, id, id, id, "")
    fun stdhandle tag f =
      case Binarymap.peek (!monitor_map, tag) of
          NONE => (warn ("Lost monitor info for "^tag); NONE)
        | SOME info => f info
    fun taginfo tag colour pfx s =
      info (infopfx ^
            squash_to (Width() - (7 + String.size pfx) - 1) (delsml_sfx tag) ^
            pfx ^ colour (StringCvt.padLeft #" " 7 s) ^ CLR_EOL)
    fun monitor msg =
      case msg of
          StartJob (_, tag) =>
          let
            val strm = TextIO.openOut (genLogFile{tag = tag})
            val tb = tailbuffer.new {
                  numlines = 10,
                  patterns = [cheat_string, oracle_string, used_cheat_string]
                }
          in
            monitor_map :=
              Binarymap.insert(!monitor_map, tag,
                               {os = strm, tb = tb, status = MRunning #"|",
                                start_time = Time.now()});
            startmsg tag;
            display_map();
            NONE
          end
        | Output((_, tag), t, chan, msg) =>
          stdhandle tag
            (fn (pinfo as {os = strm,tb,status=stat,...}) =>
                let
                  val stat' = case stat of MRunning c => MRunning (nextchar c)
                                         | Stalling _ => MRunning #"|"
                  open tailbuffer
                in
                  TextIO.output(strm,msg);
                  TextIO.flushOut strm;
                  monitor_map :=
                    Binarymap.insert(!monitor_map, tag,
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
                  Binarymap.insert(!monitor_map, tag, pinfo_upd (tb, stat') pi);
                display_map();
                NONE
              end
          in
            stdhandle
              tag
              (fn pinfo =>
                  check_time (delay, jkey, (fn () => after_check pinfo)))
          end
        | Terminated((_, tag), st, _) =>
          stdhandle tag
            (fn {os = strm,tb,status=stat,start_time} =>
                let
                  val {fulllines,lastpartial,patterns_seen} =
                    tailbuffer.output tb
                  fun seen s = Holmake_tools.member s patterns_seen
                  val taginfo = taginfo tag
                  val status_string = Pstatus_to_string st
                  val {cutime,...} = Posix.ProcEnv.times()
                  val this_childs_time = Time.-(cutime, !last_child_cputime)
                  val _ = last_child_cputime := cutime
                  val utstr = compact_time 5 true this_childs_time
                  val rtstr = compact_time 5 true
                                           (Time.-(Time.now(), start_time))
                  val pfx = "real: " ^ rtstr ^ "  user: " ^ utstr
                in
                  if st = W_EXITED then
                    if seen cheat_string orelse seen used_cheat_string then
                      taginfo boldyellow pfx "CHEATED"
                    else
                      taginfo
                        (if seen oracle_string then boldyellow else green)
                        pfx "OK"
                  else (taginfo red pfx ("FAIL<" ^ status_string ^ ">");
                        List.app (fn s => info (" " ^ dim s)) fulllines;
                        if lastpartial <> "" then info (" " ^ dim lastpartial)
                        else ());
                  TextIO.closeOut strm;
                  monitor_map := #1 (Binarymap.remove(!monitor_map, tag));
                  display_map();
                  NONE
                end)
        | MonitorKilled((_, tag), _) =>
          stdhandle tag
            (fn {os = strm,tb, status = stat,...} =>
                (taginfo tag red "" "M-KILLED";
                 TextIO.closeOut strm;
                 monitor_map := #1 (Binarymap.remove(!monitor_map, tag));
                 display_map();
                 NONE))
        | _ => NONE
  in
    monitor
  end



end
