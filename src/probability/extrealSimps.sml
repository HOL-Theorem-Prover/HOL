structure extrealSimps :> extrealSimps = struct

open HolKernel Parse boolLib bossLib;
open simpLib extrealTheory;

fun name_to_thname s = ({Thy = "extreal", Name = s}, DB.fetch "extreal" s);

val EXTREAL_ss = named_rewrites_with_names
   "EXTREAL" $ map name_to_thname
  ["extreal_le_simps",
   "extreal_lt_simps",
   "extreal_0_simps",
   "extreal_1_simps"];

val _ = register_frag EXTREAL_ss;

end
