structure HolHeader = 
struct
open Parse_support;

fun make_cond tyvars tm0 tm1 tm2 =
    list_make_comb[make_atom tyvars "COND", prec_parse tm0, tm1, tm2];

val rbinder = bind_restr_term;

fun HOL_PARSE_ERR{function,message} = 
 Exception.HOL_ERR{origin_structure = "HOL grammar",
             origin_function = function,
             message = message};

type arg = (int,Type.hol_type) Lib.istream

end
