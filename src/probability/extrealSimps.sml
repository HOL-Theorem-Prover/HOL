structure extrealSimps :> extrealSimps = struct

open HolKernel Parse boolLib bossLib;
open simpLib;
open extrealTheory;

val name_to_thname = fn s => ({Thy = "extreal", Name = s}, DB.fetch "extreal" s);

val EXT_INEQ_ss = named_rewrites_with_names "EXT_INEQ" $ map name_to_thname [
    "extreal_le_simp","extreal_lt_simp","extreal_0_simp"];

val _ = register_frag EXT_INEQ_ss;

end
