structure combinSyntax :> combinSyntax =
struct

open HolKernel Parse boolLib;  local open combinTheory in end;

val K_tm = prim_mk_const{Name="K", Thy="combin"}
val S_tm = prim_mk_const{Name="S", Thy="combin"}
val I_tm = prim_mk_const{Name="I", Thy="combin"}
val C_tm = prim_mk_const{Name="C", Thy="combin"}
val W_tm = prim_mk_const{Name="W", Thy="combin"}
val o_tm = prim_mk_const{Name="o", Thy="combin"};

val update_tm = prim_mk_const{Name="UPDATE", Thy="combin"};

fun mk_K(x,y) =
   list_mk_comb(inst[alpha |-> type_of x,
                     beta |-> type_of y]K_tm, [x,y]);

fun mk_K_1 (tm,ty) = mk_comb(inst [alpha |-> type_of tm,
                                   beta  |-> ty] K_tm,tm)

fun mk_S(f,g,x) =
 let val (fdom,frng) = dom_rng(type_of f)
     val (ty1,ty2) = dom_rng frng
 in list_mk_comb(inst[alpha |-> fdom,
                      beta |-> ty1, gamma |-> ty2]S_tm, [f,g,x])
 end

fun mk_I x = mk_comb(inst[alpha |-> type_of x]I_tm, x)

fun mk_C(f,x,y) =
 let val (fdom,frng) = dom_rng(type_of f)
     val (ty1,ty2) = dom_rng frng
 in list_mk_comb(inst[alpha |-> fdom,
                      beta  |-> ty1,
                      gamma |-> ty2]C_tm, [f,x,y])
 end

fun mk_W(f,x) =
  let val (ty1,rng) = dom_rng (type_of f)
      val (_,ty2) = dom_rng rng
  in list_mk_comb(inst[alpha |-> ty1, beta |-> ty2]W_tm, [f,x])
 end

fun mk_o(f,g) =
 let val (fdom,frng) = dom_rng(type_of f)
     val (gdom,_)    = dom_rng(type_of g)
 in list_mk_comb
      (inst [alpha |-> gdom, beta |-> frng, gamma |-> fdom] o_tm, [f,g])
 end;

fun mk_update(f,g) =
 list_mk_comb
    (inst [alpha |-> type_of f, beta |-> type_of g] update_tm, [f,g])
 handle HOL_ERR _ => raise ERR "mk_update" "";

val dest_K   = dest_binop K_tm (ERR "dest_K"   "not K")
val dest_K_1 = dest_monop K_tm (ERR "dest_K_1" "not K")
val dest_S   = dest_triop S_tm (ERR "dest_S"   "not S")
val dest_I   = dest_monop I_tm (ERR "dest_I"   "not I")
val dest_C   = dest_triop C_tm (ERR "dest_C"   "not C")
val dest_W   = dest_binop W_tm (ERR "dest_W"   "not W")
val dest_o   = dest_binop o_tm (ERR "dest_o"   "not o")

val dest_update = dest_binop update_tm (ERR "dest_update"   "not =+")
val dest_update_comb = (dest_update ## I) o Term.dest_comb
val is_update_comb   = can dest_update_comb

fun strip_update tm =
let
  fun recurse t a =
        if not (is_update_comb t) then
          (List.rev a, t)
        else let val (u,t') = dest_update_comb t in
          recurse t' (u::a)
        end
in
  recurse tm []
end

val is_K   = can dest_K
val is_K_1 = can dest_K_1
val is_S   = can dest_S
val is_I   = can dest_I
val is_C   = can dest_C
val is_W   = can dest_W
val is_o   = can dest_o

val is_update = can dest_update

val fail_tm = prim_mk_const{Name="FAIL", Thy="combin"};

fun mk_fail (f,s,args) =
   list_mk_comb(inst[alpha |-> type_of f,
                     beta |-> bool]fail_tm,
                 f::mk_var(s,bool)::args);
fun dest_fail M =
  case strip_comb M
   of (c,f::s::args) =>
        if same_const c fail_tm then
          if is_var s then (f,fst(dest_var s),args)
          else raise ERR "dest_fail" "need a variable"
        else raise ERR "dest_fail" "not a FAIL term"
    | otherwise => raise ERR "dest_fail" "too few args";

val is_fail = can dest_fail;

end
