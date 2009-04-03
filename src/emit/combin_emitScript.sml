open HolKernel boolLib bossLib Parse;
open EmitML combinTheory;

val _ = new_theory "combin_emit";

val defs = map DEFN [S_THM, K_THM, I_THM, W_THM, C_THM, o_THM, APPLY_UPDATE_THM]

val _ = eSML "combin" defs;
val _ = eCAML "combin" defs;

val _ = export_theory ();
