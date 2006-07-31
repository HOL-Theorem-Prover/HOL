(* tests for string and character parsing *)
open HolKernel Parse
fun q (QUOTE s) = "Q\"" ^ String.toString s ^ "\""
  | q (ANTIQUOTE a) = "AQ"

fun printq [] = ""
  | printq [x] = q x
  | printq (x::xs) = q x ^ " " ^ printq xs

open stringSyntax
val testdata = [(`#"("`, fromMLchar #"("),
                (`"\n^`)"`, fromMLstring "\n`)")]

fun do_test (q,res) = let
  val _ = print (StringCvt.padRight #" " 40 (printq q))
  val _ = print (StringCvt.padRight #" " 25 ("``" ^ term_to_string res ^ "``"))
in
  if aconv (Term q) res then print "OK\n"
  else (print "FAILED!\n"; OS.Process.exit OS.Process.failure)
end

val _ = app do_test testdata

val _ = OS.Process.exit OS.Process.success




