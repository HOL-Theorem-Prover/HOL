open HolKernel Parse boolLib bossLib
open md5Theory testutils wordsLib

fun md5 str = let
  val xs = str |> explode |> map (Word8.fromInt o Char.ord)
  val state = MD5.init
  val state = MD5.update(state,Word8Vector.fromList xs)
  val state = MD5.final state
  in MD5.toHexString state end

(*
    Some testing
*)

fun run_test str = let
  val _ = tprint ("MD5("^str^")")
  fun testf str =
      let
        val str_tm = str |> stringSyntax.fromMLstring
      in
        EVAL (mk_comb(“md5”,str_tm))
             |> concl |> rand |> stringSyntax.fromHOLstring
      end
in
  require_msg (check_result (equal (md5 str))) (fn x => x)
              testf str
end

val _ = app run_test ["hi","there","This is a longer string.",
                      "Mun mummoni mun mammani. Mun mammani muni mut." ^
                      "Mun mummoni mun mammani. Mun mammani muni mut." ^
                      "Mun mummoni mun mammani. Mun mammani muni mut." ^
                      "Mun mummoni mun mammani. Mun mammani muni mut." ^
                      "Mun mummoni mun mammani. Mun mammani muni mut."]
