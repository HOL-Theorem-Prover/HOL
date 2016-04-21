structure testutils :> testutils =
struct

open Lib

val linewidth = ref 80
fun checkterm pfx s =
  case OS.Process.getEnv "TERM" of
      NONE => s
    | SOME term =>
      if String.isPrefix "xterm" term then
        pfx ^ s ^ "\027[0m"
      else
        s

val bold = checkterm "\027[1m"
val boldred = checkterm "\027[31m\027[1m"
val boldgreen = checkterm "\027[32m\027[1m"
val red = checkterm "\027[31m"
val dim = checkterm "\027[2m"

fun die s = (print (boldred s ^ "\n"); OS.Process.exit OS.Process.failure)
fun OK () = print (boldgreen "OK" ^ "\n")

fun tprint s = print (UTF8.padRight #" " 78 (s ^ " ... "))

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
  if res = output then OK() else die ("FAILED!\n  Saw: >|" ^ res ^ "|<")
end
fun tpp s = tppw (!linewidth) {input=s,output=s,testf=standard_tpp_message}

fun tpp_expected r = tppw (!linewidth) r




end (* struct *)
