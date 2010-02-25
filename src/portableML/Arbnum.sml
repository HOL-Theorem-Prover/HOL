(* Author: Michael Norrish *)

(* very simple-minded implementation of arbitrary precision natural
   numbers *)

structure Arbnum :> Arbnum =
struct

open Arbnumcore;

fun pp_num ppstrm n = HOLPP.add_string ppstrm (toString n);

local open StringCvt HOLPP in
  fun base_pp_num BIN ppstrm n = add_string ppstrm ("0b" ^ toBinString n)
    | base_pp_num OCT ppstrm n = add_string ppstrm ("0" ^ toOctString n)
    | base_pp_num DEC ppstrm n = add_string ppstrm (toString n)
    | base_pp_num HEX ppstrm n = add_string ppstrm ("0x" ^ toHexString n)
end;

end

