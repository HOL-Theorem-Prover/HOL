open HolKernel

open integerTheory

infix -->

val num_ty = mk_type{Tyop = "num", Args = []}
val int_ty = mk_type{Tyop = "int", Args = []}
val int_2op = int_ty --> (int_ty --> int_ty)
val int_rel = int_ty --> (int_ty --> Type.bool)

val int_injection = mk_const{Name = "int_of_num", Ty = num_ty --> int_ty}
val int_negation = mk_const{Name = "int_neg", Ty = int_ty --> int_ty}
fun is_int_literal t =
  (rator t = int_injection andalso Term.is_numeral (rand t)) orelse
  (rator t = int_negation andalso is_int_literal (rand t))
  handle HOL_ERR _ => false

val elim_thms = [INT_ADD_CALCULATE, INT_SUB_CALCULATE, INT_MUL_CALCULATE,
                 INT_DIV_CALCULATE, INT_MOD_CALCULATE, INT_EXP_CALCULATE,
                 INT_LT_CALCULATE, INT_LE_CALCULATE, INT_EQ_CALCULATE,
                 INT_GT_CALCULATE, INT_GE_CALCULATE, INT_DIVIDES_MOD0]
val elim_ints =
  simpLib.SIMP_CONV (simpLib.++(boolSimps.bool_ss, arithSimps.REDUCE_ss))
  elim_thms

fun reducer t = let
  val (_, args) = strip_comb t
  fun reducible t = is_int_literal t orelse is_numeral t
in
  if List.all reducible args then elim_ints t else basicHol90Lib.NO_CONV t
end

val x = mk_var{Name = "x", Ty = int_ty}
and y = mk_var{Name = "y", Ty = int_ty}
val n = mk_var{Name = "n", Ty = num_ty}

val basic_op_patterns =
  map (fn s => list_mk_comb(mk_const{Name = s, Ty = int_2op}, [x,y]))
  ["int_add", "int_sub", "int_mul", "int_div", "int_mod"]
val basic_rel_patterns =
  map (fn s => list_mk_comb(mk_const{Name = s, Ty = int_rel}, [x,y]))
  ["=", "int_lt", "int_le", "int_ge", "int_gt", "int_divides"]
val exp_pattern = list_mk_comb(mk_const{Name = "int_exp",
                                        Ty = int_ty --> (num_ty --> int_ty)},
                               [x,n])
fun mk_conv pat = {name = "Integer calculation", key = SOME([], pat),
                   trace = 2, conv = K (K reducer)}

val INT_REDUCE_ss = simpLib.SIMPSET
  {convs = map mk_conv (exp_pattern::(basic_op_patterns @ basic_rel_patterns)),
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

(* It's not clear to me that this is an ideal solution to the problem of
   calculating with integers.  In particular, the hidden embedding of the
   call to arithSimps.REDUCE_ss seems a bit dodgy somehow.  Still, you can
   be sure that only integers will get reduced when this ssdata value is
   used. *)