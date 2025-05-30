open HolKernel Parse boolLib
open pred_setTheory generic_termsTheory binderLib nomsetTheory nomdatatype
open testutils

val tyname0 = "name";
val tyname1 = "pi";

val gvar_rep_t = “:unit”;
val u_tm = mk_var("u", gvar_rep_t);
val glam_rep_t = “:unit + unit”;
val d_tm = mk_var("d", glam_rep_t);
val lp =
  “(\n lfvs ^d_tm tns uns.
     n = 0 /\ lfvs = 1 /\ tns = [] /\ uns = [] \/
     n = 1 /\ lfvs = 0 /\ ISL d /\ tns = [] ∧ uns = [] \/
     n = 1 /\ lfvs = 0 /\ ISR d /\ tns = [1] ∧ uns = [0]
    )”;

val _ = tprint "Deriving type 0"
val _ = require (check_result (K true))
                (new_type_step1 tyname0 0 [])
                {lp = lp}

val _ = tprint "Deriving type 1"
val _ = require (check_result (K true))
                (new_type_step1 tyname1 1 [])
                {lp = lp}
