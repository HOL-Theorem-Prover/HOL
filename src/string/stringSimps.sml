structure stringSimps :> stringSimps =
struct

open HolKernel boolLib simpLib stringTheory stringLib;

val char_rewrites = [CHR_ORD,CHAR_EQ_THM,ORD_11];
val string_rewrites = 
     STRING_CASE_DEF::STRING_11::STRING_DISTINCT::
     EXPLODE_EQNS::IMPLODE_EQNS::STRING_SIZE_DEF::
     EXPLODE_11::EXPLODE_IMPLODE::IMPLODE_EXPLODE::char_rewrites;


val key = mk_eq(mk_var("x",string_ty),mk_var("y",string_ty));

val STRING_ss = SIMPSET {ac = [], congs = [],
                   convs = [{conv = K (K string_EQ_CONV),
                             key= SOME ([], key),
                             name = "string_EQ_CONV",
                             trace = 2}],
                   dprocs = [], filter = NONE, 
                   rewrs = string_rewrites}

end
