structure testutils :> testutils =
struct

open Lib Feedback testutilsBase

val S = HOLPP.add_string

fun raw_backend f =
    Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) f

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

end (* struct *)
