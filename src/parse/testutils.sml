structure testutils :> testutils =
struct

open Lib Feedback

datatype testresult = datatype Exn.result
datatype die_mode = ProcessExit | FailException | Remember of int ref

val linewidth = ref 80
val output_linewidth = Holmake_tools.getWidth()

fun is_result (Exn.Res _) = true
  | is_result _ = false
fun crush padding w s =
  let
    val extra = " ..."
    val exsize = UTF8.size extra
    val desired_size = UTF8.size s + exsize
  in
    if desired_size <= w - padding then
      UTF8.padRight #" " w (s ^ extra)
    else
      UTF8.padRight #" " w (UTF8.substring(s,0,w - padding - exsize) ^ extra)
  end
val rmNLs = String.translate (fn #"\n" => " " | #"\t" => " " | c => str c)

fun squish_spaces s =
    let
      fun recurse A ss =
          let
            val (pfx,sfx) = Substring.position "  " ss
          in
            if Substring.size sfx = 0 then
              Substring.concatWith " " (List.rev (pfx::A))
            else
              recurse (pfx::A)
                      (Substring.dropl Char.isSpace sfx)
          end
    in
      recurse [] (Substring.full s)
    end

fun tprint0 n s =
    s |> rmNLs |> squish_spaces
      |> crush n (output_linewidth - 3)
      |> print
val tprint = tprint0 0
val timed_tprint = tprint0 14 (* width of standard extra timing info *)

fun printsize s =
    let
      fun normal c s =
          case UTF8.getChar s of
              NONE => c
            | SOME ((_, 27), rest) => escape c rest
            | SOME (_, rest) => normal (c + 1) rest
      and escape c s =
          case UTF8.getChar s of
              NONE => c + 1
            | SOME (("[", _), rest) => ANSIp c rest
            | SOME (_, rest) => normal (c - 1) rest
                (* bare escape consumes next 2, it seems *)
      and ANSIp c s = (* ANSI parameters *)
          case UTF8.getChar s of
              NONE => c
            | SOME ((_, i), rest) =>
                if 0x30 <= i andalso i <= 0x3F then ANSIp c rest
                else ANSIib c s
      and ANSIib c s = (* ANSI intermediate bytes *)
          case UTF8.getChar s of
              NONE => c
            | SOME ((_, i), rest) =>
                if 0x20 <= i andalso i <= 0x2F then ANSIib c rest
                else ANSIfinal c s
      and ANSIfinal c s = (* ANSI final bytes *)
          case UTF8.getChar s of
              NONE => c
            | SOME(_, rest) => normal c rest
    in
      normal 0 s
    end

fun tadd s =
    let
      val (pfx,sfx) = Substring.position "\n" (Substring.full s)
    in
      for_se 1 (printsize (Substring.string pfx)) (fn _ => print "\008");
      print s
    end

fun checkterm pfx s =
  case OS.Process.getEnv "TERM" of
      NONE => s
    | SOME term =>
      if String.isPrefix "xterm" term orelse
         String.isPrefix "tmux" term then
        pfx ^ s ^ "\027[0m"
      else
        s

val bold = checkterm "\027[1m"
val boldred = checkterm "\027[31m\027[1m"
val boldgreen = checkterm "\027[32m\027[1m"
val red = checkterm "\027[31m"
val dim = checkterm "\027[2m"
val clear = checkterm "\027[0m"

val FAILEDstr = "\027[2CFAILED!"
val diemode = ref ProcessExit
val S = HOLPP.add_string
fun pretty_die p =
  (tadd (boldred FAILEDstr ^ "\n");
   HOLPP.prettyPrint (print, output_linewidth) p;
   print "\n";
   case (!diemode) of
       ProcessExit => OS.Process.exit OS.Process.failure
     | FailException => raise (Fail ("DIE:" ^ HOLPP.pp_to_string 75 (K p) ()))
     | Remember iref => (iref := !iref + 1))
fun die s = pretty_die (S s)
fun OK () = print (boldgreen "OK" ^ "\n")
fun exit_count0 iref =
    OS.Process.exit
      (if !iref = 0 then OS.Process.success
       else
         (print ("Failure count = " ^ Int.toString (!iref) ^ "\n");
          OS.Process.failure))

fun unicode_off f = Feedback.trace ("Unicode", 0) f
fun raw_backend f =
    Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) f

fun quietly f =
    Feedback.quiet_messages $ Feedback.quiet_warnings $
      Portable.with_flag (Feedback.emit_ERR, false) f

local
  val pfxsize = size "Testing printing of ..." + 3
    (* 3 for quotations marks and an extra space *)
in
fun standard_tpp_message s = let
  open UTF8
  fun trunc s =
    if size s + pfxsize > output_linewidth - 18 then
      let
        val s' = substring(s,0,output_linewidth - 22 - pfxsize)
      in
        s' ^ " ..."
      end
    else s
  fun pretty s = s |> String.translate (fn #"\n" => "\\n" | c => str c)
                   |> trunc
in
  "Testing printing of "^UnicodeChars.lsquo ^ pretty s ^ UnicodeChars.rsquo
end
end (* local *)

exception InternalDie of HOLPP.pretty
fun tppw width {input=s,output,testf} = let
  val _ = tprint (testf s)
  val t = Parse.Term [QUOTE s]
          handle HOL_ERR _ => raise InternalDie (S "Parse failed!")
  val cres = Exn.capture (HOLPP.pp_to_string width Parse.pp_term) t
  fun f s = String.translate
              (fn #" " => UTF8.chr 0x2423 | #"\n" => "\n      " | c => str c) s
in
  case cres of
      Exn.Exn e => die ("  Pretty printer raised exception:\n    " ^
                        General.exnMessage e)
    | Exn.Res res =>
      if res = output then OK()
      else
        die ("  Saw:\n    >|" ^ clear (f res) ^
             "|<\n  rather than \n    >|" ^ clear (f output) ^ "|<\n")
end handle InternalDie p => pretty_die p
fun tpp s = tppw (!linewidth) {input=s,output=s,testf=standard_tpp_message}

fun tpp_expected r = tppw (!linewidth) r

fun timed f check x =
  let
    val cputimer = Timer.startCPUTimer()
    val res = Res (f x) handle e => Exn e
    val {nongc = {usr,...}, gc = {usr = gc,...}} = Timer.checkCPUTimes cputimer
    val usr_s = "(" ^ Time.toString usr ^"s)      "
    val gc_s = if Time.toReal usr > 0.000001 andalso
                  Time.toReal gc / Time.toReal usr > 0.20
               then
                 boldred ("[GC = " ^ Time.toString gc ^ "] ")
               else ""
    val _ = tadd (gc_s ^ usr_s)
  in
    check res
  end

fun exncheck f (Res a) = f a
  | exncheck f (Exn e) = die ("  Unexpected EXN:\n    "^General.exnMessage e)

fun convtest (nm,conv,tm,expected) =
  let
    open Term
    val _ = timed_tprint nm
    fun c th =
      let
        val (l,r) =
            let
              val (eql, r) = dest_comb (Thm.concl th)
              val (eq, l) = dest_comb eql
              val _ = assert (same_const equality) eq
            in
              (l,r)
            end handle e =>
              raise InternalDie
                    (S ("Didn't get equality; rather exn "^
                        General.exnMessage e))
        open HOLPP
      in
        if aconv l tm then
          if aconv r expected then OK()
          else raise InternalDie (block CONSISTENT 2 [
                                     S "Got:", add_break(1,0),
                                     Parse.pp_term r
                                   ])
        else
          raise InternalDie (block CONSISTENT 2 [
                                S "Conv result LHS =", add_break(1,0),
                                Parse.pp_term l])
      end
  in
    timed conv (exncheck c) tm
  end handle InternalDie p => pretty_die p

fun check_HOL_ERRexn P e =
    case e of
        HOL_ERR{origin_structure,origin_function,message,...} =>
          P (origin_structure, origin_function, message)
      | _ => false

fun check_HOL_ERR P (Res _) = false
  | check_HOL_ERR P (Exn e) = check_HOL_ERRexn P e

fun is_struct_HOL_ERR st1 = check_HOL_ERRexn (fn (st2,_,_) => st1 = st2)
fun check_result P (Res r) = P r
  | check_result P _ = false



fun require_msgk P pr f k x =
    let
      open HOLPP
      fun idie s = raise InternalDie s
      fun check res =
          if P res then (OK(); res)
          else
            case res of
                Exn e => idie (
                          block CONSISTENT 0 [
                            S " ", add_break(1,0),
                            block CONSISTENT 2[
                              S "Unexpected exception:", add_break(1,0),
                              S (General.exnMessage e)
                            ]
                          ]
                        )
              | Res y => idie (
                          block CONSISTENT 0 [
                            S " ", add_break(1,0),
                            block CONSISTENT 2[
                              S "Unexpected result:", add_break(1,0),
                              pr y
                            ]
                          ]
                        )
      val result = timed f check x
    in
      k result
    end handle InternalDie p => pretty_die p
fun require_pretty_msg P pr f x = require_msgk P pr f (fn _ => ()) x
fun require_msg P pr = require_pretty_msg P (S o pr)
fun require P f x = require_msg P (fn _ => "") f x

fun shouldfail {printarg,testfn,printresult,checkexn} arg =
  let
    val _ = tprint (printarg arg)
    fun check (Res r) = false
      | check (Exn e) = checkexn e
  in
    require_msg check printresult testfn arg
  end

end (* struct *)
