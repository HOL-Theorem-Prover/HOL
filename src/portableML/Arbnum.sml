(* Author: Michael Norrish *)

(* very simple-minded implementation of arbitrary precision natural
   numbers *)

structure Arbnum :> Arbnum =
struct

open Arbnumcore;

fun pp_num n = HOLPP.PrettyString (toString n)

local
   open StringCvt HOLPP
in
   fun base_pp_num BIN n = HOLPP.PrettyString ("0b" ^ toBinString n)
     | base_pp_num OCT n = HOLPP.PrettyString ("0" ^ toOctString n)
     | base_pp_num DEC n = HOLPP.PrettyString (toString n)
     | base_pp_num HEX n = HOLPP.PrettyString ("0x" ^ toHexString n)
end

end
