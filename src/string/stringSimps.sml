structure stringSimps :> stringSimps =
struct

open HolKernel boolLib simpLib stringTheory stringLib;

val char_rewrites = [CHR_ORD];

val string_rewrites =
      STRING_CASE_DEF::STRING_11::STRING_DISTINCT::
      EXPLODE_EQNS::IMPLODE_EQNS::STRLEN_DEF::
      EXPLODE_11::EXPLODE_IMPLODE::IMPLODE_EXPLODE::char_rewrites;


val key = mk_eq(mk_var("x",string_ty),mk_var("y",string_ty));
val key2 = mk_eq(mk_var("x",char_ty),mk_var("y",char_ty));

val STRING_ss = SSFRAG {ac = [], congs = [],
                    convs = [{conv = K (K string_EQ_CONV),
                              key= SOME ([], key),
                              name = "string_EQ_CONV",
                              trace = 2},
                              {conv = K (K char_EQ_CONV),
                              key= SOME ([], key2),
                              name = "char_EQ_CONV",
                              trace = 2}],
                    dprocs = [], filter = NONE,
                    rewrs = string_rewrites};


end

