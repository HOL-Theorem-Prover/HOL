structure ASCIInumbersLib :> ASCIInumbersLib =
struct

open HolKernel Parse boolLib computeLib;
open numposrepLib ASCIInumbersTheory

structure Parse = struct
  open Parse
  val (Type, Term) =
     parse_from_grammars ASCIInumbersTheory.ASCIInumbers_grammars
end
open Parse

(* ------------------------------------------------------------------------- *)

local
   val thms =
      [s2n_def, n2s_def, HEX_def, UNHEX_def,
       num_from_bin_string_def, num_from_oct_string_def,
       num_from_dec_string_def, num_from_hex_string_def,
       num_to_bin_string_def, num_to_oct_string_def,
       num_to_dec_string_def, num_to_hex_string_def,
       fromBinString_def, fromDecString_def, fromHexString_def]
in
   fun add_ASCIInumbers_compset cmp = computeLib.add_thms thms cmp
end

val () = add_ASCIInumbers_compset computeLib.the_compset

(* ------------------------------------------------------------------------- *)

(* Testing...

open ASCIInumbersLib

val tst = Count.apply EVAL

tst ``s2n 3 UNHEX "12110"``;
tst ``n2s 3 HEX 21328``;
tst ``num_from_bin_string "10111"``;
tst ``num_from_oct_string "72140"``;
tst ``num_from_dec_string "72149"``;
tst ``num_from_hex_string "abaaf"``;
tst ``num_to_bin_string 0b110111``;
tst ``num_to_oct_string 123``;
tst ``num_to_dec_string 23768``;
tst ``num_to_hex_string 0xAAFF11``;

*)

end
