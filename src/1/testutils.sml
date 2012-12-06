structure testutils :> testutils =
struct

open Lib

val linewidth = ref 80

fun die s = (print (s ^ "\n"); OS.Process.exit OS.Process.failure)

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))

fun unicode_off f = Feedback.trace ("Unicode", 0) f
fun raw_backend f =
    Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) f

local
  val pfxsize = size "Testing printing of `` ..."
in
fun standard_tpp_message s = let
  fun trunc s = if size s + pfxsize > 62 then let
                  val s' = String.substring(s,0,58 - pfxsize)
                in
                  s' ^ " ..."
                end
                else s
  fun pretty s = s |> String.translate (fn #"\n" => "\\n" | c => str c)
                   |> trunc
in
  "Testing printing of `"^pretty s^"`"
end
end (* local *)

fun tppw width {input=s,output,testf} = let
  val _ = tprint (testf s)
  val t = Parse.Term [QUOTE s]
  val res = Portable.pp_to_string width Parse.pp_term t
in
  if res = output then print "OK\n" else die "FAILED!\n"
end
fun tpp s = tppw (!linewidth) {input=s,output=s,testf=standard_tpp_message}

fun tpp_expected r = tppw (!linewidth) r




end (* struct *)
