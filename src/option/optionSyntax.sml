structure optionSyntax :> optionSyntax =
struct

local open sumTheory optionTheory in end;

open HolKernel Abbrev;

val ERR = mk_HOL_ERR "optionSyntax";

(*---------------------------------------------------------------------------
        option types
 ---------------------------------------------------------------------------*)

fun mk_option ty = mk_thy_type{Tyop="option",Thy="option",Args=[ty]};

fun dest_option ty =
  case total dest_thy_type ty
   of SOME{Tyop="option", Thy="option", Args=[ty]} => ty
    | other => raise ERR "dest_option" "not an option type";

val is_option = can dest_option;


(*---------------------------------------------------------------------------
     Constants of the theory
 ---------------------------------------------------------------------------*)

val none_tm        = prim_mk_const{Name="NONE",        Thy="option"}
val some_tm        = prim_mk_const{Name="SOME",        Thy="option"}
val the_tm         = prim_mk_const{Name="THE",         Thy="option"}
val option_map_tm  = prim_mk_const{Name="OPTION_MAP",  Thy="option"}
val option_join_tm = prim_mk_const{Name="OPTION_JOIN", Thy="option"}
val is_some_tm     = prim_mk_const{Name="IS_SOME",     Thy="option"}
val is_none_tm     = prim_mk_const{Name="IS_NONE",     Thy="option"}
val option_case_tm = prim_mk_const{Name="option_case", Thy="option"}


(*---------------------------------------------------------------------------
     Applications of constants
 ---------------------------------------------------------------------------*)

fun mk_none ty = inst [alpha |-> ty] none_tm
fun mk_some tm = mk_comb(inst [alpha |-> type_of tm] some_tm, tm)

fun mk_the tm =
  mk_comb(inst[alpha |-> dest_option (type_of tm)] the_tm,tm)
  handle HOL_ERR _ => raise ERR "mk_the" "";

fun mk_option_map (f,opt) =
 case total (dom_rng o type_of) f
  of SOME (d,r) => list_mk_comb(inst[alpha|->d,beta|->r]option_map_tm,[f,opt])
   | NONE => raise ERR "mk_option_map" "";

fun mk_option_join tm =
 mk_comb
  (inst[alpha |-> dest_option(dest_option(type_of tm))] option_join_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_option_join" "";

fun mk_is_none tm =
  mk_comb(inst[alpha |-> dest_option(type_of tm)]is_none_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_is_none" "";

fun mk_is_some tm =
  mk_comb(inst[alpha |-> dest_option(type_of tm)]is_some_tm, tm)
  handle HOL_ERR _ => raise ERR "mk_is_some" "";

fun mk_option_case (n,s,p) =
 case total dest_thy_type (type_of p)
  of SOME{Tyop="option", Thy="option", Args=[ty]}
      => list_mk_comb
            (inst[beta |-> type_of n, alpha |-> ty]option_case_tm, [n,s,p])
   | otherwise => raise ERR "mk_option_case" "";


(*---------------------------------------------------------------------------
         Destructor operations
 ---------------------------------------------------------------------------*)

fun dest_none tm =
 if same_const none_tm tm then type_of tm else raise ERR "dest_none" "";

val dest_some    = dest_monop some_tm    (ERR "dest_some" "")
val dest_the     = dest_monop the_tm     (ERR "dest_the" "")
val dest_is_none = dest_monop is_none_tm (ERR "dest_is_none" "")
val dest_is_some = dest_monop is_some_tm (ERR "dest_is_some" "")

val dest_option_map = dest_binop option_map_tm   (ERR "dest_option_map" "")
val dest_option_join = dest_monop option_join_tm (ERR "dest_option_join" "")

fun dest_option_case tm =
 let val (f,z) = with_exn dest_comb tm (ERR "dest_option_case" "")
     val (x,y) = dest_binop option_case_tm (ERR "dest_option_case" "") f
 in (x,y,z)
 end

(*---------------------------------------------------------------------------
         Query operations
 ---------------------------------------------------------------------------*)

val is_none        = can dest_none
val is_some        = can dest_some
val is_the         = can dest_the
val is_is_none     = can dest_is_none
val is_is_some     = can dest_is_none
val is_option_map  = can dest_option_map
val is_option_join = can dest_option_join
val is_option_case = can dest_option_case


(*---------------------------------------------------------------------------*)
(* Lifting from ML options to HOL options                                    *)
(*---------------------------------------------------------------------------*)

fun lift_option ty =
  let open TypeBasePure
      val none = cinst ty none_tm
      val some = cinst ty some_tm
      fun lift f NONE = none
        | lift f (SOME x) = mk_comb(some,f x)
  in lift
  end

end
