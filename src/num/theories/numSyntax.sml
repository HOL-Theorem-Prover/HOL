structure numSyntax :> numSyntax =
struct
  open HolKernel Abbrev;

  local open arithmeticTheory whileTheory numeralTheory in end;

  val ERR = mk_HOL_ERR "numSyntax";

(*---------------------------------------------------------------------------
          Constants
 ---------------------------------------------------------------------------*)

  val num = mk_thy_type{Thy="num", Tyop="num", Args=[]}

  val zero_tm      = prim_mk_const {Name="0",       Thy="num"}
  val suc_tm       = prim_mk_const {Name="SUC",     Thy="num"}
  val pre_tm       = prim_mk_const {Name="PRE",     Thy="prim_rec"}
  val measure_tm   = prim_mk_const {Name="measure", Thy="prim_rec"}
  val less_tm      = prim_mk_const {Name="<",       Thy="prim_rec"}
  val numeral_tm   = prim_mk_const {Name="NUMERAL", Thy="arithmetic"}
  val alt_zero_tm  = prim_mk_const {Name="ZERO",    Thy="arithmetic"}
  val bit1_tm      = prim_mk_const {Name="BIT1",    Thy="arithmetic"}
  val bit2_tm      = prim_mk_const {Name="BIT2",    Thy="arithmetic"}
  val plus_tm      = prim_mk_const {Name="+",       Thy="arithmetic"}
  val minus_tm     = prim_mk_const {Name="-",       Thy="arithmetic"}
  val mult_tm      = prim_mk_const {Name="*",       Thy="arithmetic"}
  val exp_tm       = prim_mk_const {Name="EXP",     Thy="arithmetic"}
  val div_tm       = prim_mk_const {Name="DIV",     Thy="arithmetic"}
  val mod_tm       = prim_mk_const {Name="MOD",     Thy="arithmetic"}
  val div2_tm      = prim_mk_const {Name="DIV2",    Thy="arithmetic"}
  val mod_2exp_tm  = prim_mk_const {Name="MOD_2EXP",Thy="arithmetic"}
  val greater_tm   = prim_mk_const {Name=">",       Thy="arithmetic"}
  val geq_tm       = prim_mk_const {Name=">=",      Thy="arithmetic"}
  val leq_tm       = prim_mk_const {Name="<=",      Thy="arithmetic"}
  val even_tm      = prim_mk_const {Name="EVEN",    Thy="arithmetic"}
  val odd_tm       = prim_mk_const {Name="ODD",     Thy="arithmetic"}
  val min_tm       = prim_mk_const {Name="MIN",     Thy="arithmetic"}
  val max_tm       = prim_mk_const {Name="MAX",     Thy="arithmetic"}
  val num_case_tm  = prim_mk_const {Name="num_case",Thy="arithmetic"}
  val fact_tm      = prim_mk_const {Name="FACT",    Thy="arithmetic"}
  val funpow_tm    = prim_mk_const {Name="FUNPOW",  Thy="arithmetic"}
  val divmod_tm    = prim_mk_const {Name="DIVMOD",  Thy="arithmetic"};
  val while_tm     = prim_mk_const {Name="WHILE",   Thy="while"}
  val least_tm     = prim_mk_const {Name="LEAST",   Thy="while"};


(*---------------------------------------------------------------------------
          Constructors
 ---------------------------------------------------------------------------*)

  fun mk_monop c tm = mk_comb(c,tm)
  fun mk_binop c (tm1,tm2) = mk_comb(mk_comb(c,tm1),tm2);

  val mk_suc      = mk_monop suc_tm
  val mk_pre      = mk_monop pre_tm
  val mk_plus     = mk_binop plus_tm
  val mk_minus    = mk_binop minus_tm
  val mk_mult     = mk_binop mult_tm
  val mk_exp      = mk_binop exp_tm
  val mk_div      = mk_binop div_tm
  val mk_mod      = mk_binop mod_tm
  val mk_div2     = mk_monop div2_tm
  val mk_mod_2exp = mk_binop mod_2exp_tm
  val mk_less     = mk_binop less_tm
  val mk_greater  = mk_binop greater_tm
  val mk_geq      = mk_binop geq_tm
  val mk_leq      = mk_binop leq_tm
  val mk_even     = mk_monop even_tm
  val mk_odd      = mk_monop odd_tm
  val mk_min      = mk_binop min_tm
  val mk_max      = mk_binop max_tm
  val mk_fact     = mk_monop fact_tm

  fun mk_num_case(b,f,n) =
      list_mk_comb(inst[alpha |-> type_of b] num_case_tm, [b,f,n]);

  fun mk_funpow(f,n,x) =
      list_mk_comb(inst [alpha |-> type_of x] funpow_tm, [f,n,x]);

  fun mk_while(P,g,x) =
      list_mk_comb(inst [alpha |-> type_of x] while_tm, [P,g,x]);

  fun mk_least P = 
      mk_comb(inst [alpha |-> fst(dom_rng(type_of P))] least_tm, P);

  fun mk_divmod(m,n,a) = list_mk_comb(divmod_tm, [m,n,a]);

  fun mk_measure (f,x,y) = 
      list_mk_comb(inst [alpha |-> type_of x] measure_tm, [f,x,y]);

  (* Partial application of measure is often more useful *)
  fun mk_cmeasure f = 
     mk_comb(inst [alpha |-> fst(dom_rng (type_of f))] measure_tm, f);


(*---------------------------------------------------------------------------
          Destructors
 ---------------------------------------------------------------------------*)

  val dest_suc      = dest_monop suc_tm      (ERR "dest_suc" "")
  val dest_pre      = dest_monop pre_tm      (ERR "dest_pre" "")
  val dest_plus     = dest_binop plus_tm     (ERR "dest_plus" "")
  val dest_minus    = dest_binop minus_tm    (ERR "dest_minus" "")
  val dest_mult     = dest_binop mult_tm     (ERR "dest_mult" "")
  val dest_exp      = dest_binop exp_tm      (ERR "dest_exp" "")
  val dest_div      = dest_binop div_tm      (ERR "dest_div" "")
  val dest_mod      = dest_binop mod_tm      (ERR "dest_mod" "")
  val dest_div2     = dest_monop div2_tm     (ERR "dest_div2" "")
  val dest_mod_2exp = dest_binop mod_2exp_tm (ERR "dest_mod_2exp" "")
  val dest_less     = dest_binop less_tm     (ERR "dest_less" "")
  val dest_greater  = dest_binop greater_tm  (ERR "dest_greater" "")
  val dest_geq      = dest_binop geq_tm      (ERR "dest_geq" "")
  val dest_leq      = dest_binop leq_tm      (ERR "dest_leq" "")
  val dest_even     = dest_monop even_tm     (ERR "dest_even" "")
  val dest_odd      = dest_monop odd_tm      (ERR "dest_odd" "");
  val dest_min      = dest_binop min_tm      (ERR "dest_min" "")
  val dest_max      = dest_binop max_tm      (ERR "dest_max" "")
  val dest_fact     = dest_monop fact_tm     (ERR "dest_fact" "");
  val dest_least    = dest_monop least_tm    (ERR "dest_least" "");

  fun dest_num_case tm =
    case strip_comb tm
     of (ncase,[b,f,n]) =>
         if same_const num_case_tm ncase
         then (b,f,n)
         else raise ERR "dest_num_case" "not an application of \"num_case\""
      | _ => raise ERR "dest_num_case" "not an application of \"num_case\""

  fun dest_funpow tm =
    case strip_comb tm
     of (funpow,[f,n,x]) =>
         if same_const funpow_tm funpow
         then (f,n,x)
         else raise ERR "dest_funpow" "not an application of \"FUNPOW\""
      | _ => raise ERR "dest_funpow" "not an application of \"FUNPOW\"";


  fun dest_while tm =
    case strip_comb tm
     of (whle,[P,g,x]) =>
         if same_const while_tm whle
         then (P,g,x)
         else raise ERR "dest_while" "not an application of \"WHILE\""
      | _ => raise ERR "dest_while" "not an application of \"WHILE\"";

  fun dest_divmod tm =
    case strip_comb tm
     of (dm,[m,n,a]) =>
         if same_const divmod_tm dm
         then (m,n,a)
         else raise ERR "dest_divmod" "not an application of \"divmod\""
      | _ => raise ERR "dest_divmod" "not an application of \"divmod\"";

  fun dest_measure tm =
    case strip_comb tm
     of (m,[f,x,y]) =>
         if same_const measure_tm m
         then (f,x,y)
         else raise ERR "dest_measure" "not an application of \"measure\""
      | _ => raise ERR "dest_measure" "not an application of \"measure\"";

  fun dest_cmeasure tm =
    case total dest_comb tm
     of NONE => raise ERR "dest_cmeasure" "not an application of \"measure\""
      | SOME (m,f) => if same_const measure_tm m then f
                      else raise ERR "dest_cmeasure" 
                                     "not an application of \"measure\""

(*---------------------------------------------------------------------------
          Query operations
 ---------------------------------------------------------------------------*)

  val is_suc      = can dest_suc
  val is_pre      = can dest_pre
  val is_plus     = can dest_plus
  val is_minus    = can dest_minus
  val is_mult     = can dest_mult
  val is_exp      = can dest_exp
  val is_div      = can dest_div
  val is_mod      = can dest_mod
  val is_div2     = can dest_div2
  val is_mod_2exp = can dest_mod_2exp
  val is_less     = can dest_less
  val is_greater  = can dest_greater
  val is_geq      = can dest_geq
  val is_leq      = can dest_leq
  val is_even     = can dest_even
  val is_odd      = can dest_odd
  val is_min      = can dest_min
  val is_max      = can dest_max
  val is_num_case = can dest_num_case
  val is_fact     = can dest_fact
  val is_funpow   = can dest_funpow
  val is_while    = can dest_while
  val is_least    = can dest_least
  val is_divmod   = can dest_divmod
  val is_measure  = can dest_measure


(*---------------------------------------------------------------------------
     Numerals are treated specially
 ---------------------------------------------------------------------------*)

  val mk_numeral = Literal.gen_mk_numeral {
    mk_comb  = Term.mk_comb,
    ALT_ZERO = alt_zero_tm,
    ZERO     = zero_tm,
    NUMERAL  = numeral_tm,
    BIT1     = bit1_tm,
    BIT2     = bit2_tm
  };

  val dest_numeral = Literal.dest_numeral
  val is_numeral   = Literal.is_numeral

  val int_of_term = Arbnum.toInt o dest_numeral
  fun term_of_int i = mk_numeral(Arbnum.fromInt i)

(*---------------------------------------------------------------------------
     Dealing with lists of things to be added or multiplied.
 ---------------------------------------------------------------------------*)

  fun list_mk_plus (h::t) = rev_itlist (C (curry mk_plus)) t h
    | list_mk_plus [] = raise ERR "list_mk_plus" "empty list";

  fun list_mk_mult (h::t) = rev_itlist (C (curry mk_mult)) t h
    | list_mk_mult [] = raise ERR "list_mk_mult" "empty list";

  val strip_plus = strip_binop (total dest_plus)
  val strip_mult = strip_binop (total dest_mult)

(*---------------------------------------------------------------------------
     Lifting ML Arbnums to HOL nums
 ---------------------------------------------------------------------------*)

fun lift_num ty arbnum = mk_numeral arbnum

end
