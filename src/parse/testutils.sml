structure testutils :> testutils =
struct

open Lib

val linewidth = ref 80

fun crush extra w s =
  let
    val exsize = UTF8.size extra
    val desired_size = UTF8.size s + exsize
  in
    if desired_size <= w then
      UTF8.padRight #" " w (s ^ extra)
    else
      UTF8.substring(s,0,w-exsize) ^ extra
  end

fun tprint s = print (crush " ...  " 77 s)

fun tadd s =
  (for_se 1 (UTF8.size s) (fn _ => print "\008");
   print s)

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

val really_die = ref true;
fun die s =
  (tadd (boldred s ^ "\n");
   if (!really_die) then OS.Process.exit OS.Process.failure
   else raise (Fail ("DIE:" ^ s)))
fun OK () = print (boldgreen "OK" ^ "\n")

fun unicode_off f = Feedback.trace ("Unicode", 0) f
fun raw_backend f =
    Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) f

local
  val pfxsize = size "Testing printing of ..." + 3
    (* 3 for quotations marks and an extra space *)
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
  "Testing printing of "^UnicodeChars.lsquo ^ pretty s ^ UnicodeChars.rsquo
end
end (* local *)

fun tppw width {input=s,output,testf} = let
  val _ = tprint (testf s)
  val t = Parse.Term [QUOTE s]
  val res = Portable.pp_to_string width Parse.pp_term t
in
  if res = output then OK() else die ("\n  FAILED!  Saw: >|" ^ res ^ "|<")
end
fun tpp s = tppw (!linewidth) {input=s,output=s,testf=standard_tpp_message}

fun tpp_expected r = tppw (!linewidth) r

fun convtest (nm,conv,tm,expected) =
  let
    open Term
    val _ = tprint nm
    val (l,r) = let
      val (eql, r) = dest_comb (Thm.concl (conv tm))
      val (eq, l) = dest_comb eql
      val _ = assert (same_const equality) eq
    in
      (l,r)
    end handle e =>
               die ("Didn't get equality; rather exn "^ General.exnMessage e)
  in
    if aconv l tm then
      if aconv r expected then OK()
      else die ("Got: " ^ Parse.term_to_string r)
    else die ("Conv result LHS = " ^ Parse.term_to_string l)
  end

end (* struct *)
