structure intSimps :> intSimps =
struct

open HolKernel boolLib integerTheory intSyntax Rsyntax

infix --> THENC

val num_ty = mk_thy_type{Tyop = "num", Thy = "num", Args = []}
val int_ty = mk_thy_type{Tyop = "int", Thy = "integer", Args = []}
val int_2op = int_ty --> (int_ty --> int_ty)
val int_rel = int_ty --> (int_ty --> Type.bool)

val int_injection = mk_thy_const{Name = "int_of_num", Thy = "integer",
                                 Ty = num_ty --> int_ty}
val int_negation = mk_thy_const{Name = "int_neg", Thy = "integer",
                                Ty = int_ty --> int_ty}
fun is_int_literal t =
  (rator t = int_injection andalso numSyntax.is_numeral (rand t)) orelse
  (rator t = int_negation andalso is_int_literal (rand t))
  handle HOL_ERR _ => false

val elim_thms = [INT_ADD_REDUCE, INT_SUB_REDUCE, INT_MUL_REDUCE,
                 INT_DIV_REDUCE, INT_MOD_REDUCE, INT_EXP_REDUCE,
                 INT_LT_REDUCE, INT_LE_REDUCE, INT_EQ_REDUCE,
                 INT_GT_REDUCE, INT_GE_REDUCE, INT_DIVIDES_REDUCE,
                 INT_ABS_NUM, INT_ABS_NEG, INT_QUOT_REDUCE, INT_REM_REDUCE]

fun int_compset () = let
  open computeLib
  val compset = reduceLib.num_compset()
  val _ = add_thms elim_thms compset
in
  compset
end;

(* ----------------------------------------------------------------------
    add integer reductions to the global compset
   ---------------------------------------------------------------------- *)

val _ = let open computeLib in add_funs elim_thms end;


val REDUCE_CONV = computeLib.CBV_CONV (int_compset())


val x = mk_var{Name = "x", Ty = int_ty}
and y = mk_var{Name = "y", Ty = int_ty}
val n = mk_var{Name = "n", Ty = num_ty}

val basic_op_terms =
  [plus_tm, minus_tm, mult_tm, div_tm, mod_tm, int_eq_tm,
   less_tm, leq_tm, great_tm, geq_tm, divides_tm, rem_tm, quot_tm]
val basic_op_patterns = map (fn t => list_mk_comb(t, [x,y])) basic_op_terms
val exp_pattern = list_mk_comb(exp_tm, [x,n])

fun reducible t = is_int_literal t orelse numSyntax.is_numeral t
fun reducer t = let
  val (_, args) = strip_comb t
in
  if List.all reducible args then REDUCE_CONV t else Conv.NO_CONV t
end

val rederr = HOL_ERR {origin_structure = "intSimps",
                      origin_function = "RED_CONV",
                      message = "Term not reducible"}
fun is_funtype ty = let
  val {Tyop,Thy,...} = dest_thy_type ty
in
  Tyop = "fun" andalso Thy = "min"
end
fun RED_CONV t = let
  val (f, args) = strip_comb t
  val _ = f = exp_tm orelse mem f basic_op_terms orelse raise rederr
  val _ = List.all reducible args orelse raise rederr
  val _ = not (is_funtype (type_of t)) orelse raise rederr
in
  REDUCE_CONV t
end

fun mk_conv pat = {name = "Integer calculation", key = SOME([], pat),
                   trace = 2, conv = K (K reducer)}

val INT_REDUCE_ss = simpLib.SIMPSET
  {convs = map mk_conv (exp_pattern::basic_op_patterns),
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val int_ss = simpLib.++(boolSimps.bool_ss, INT_REDUCE_ss)

fun collect_additive_consts tm = let
  val summands = strip_plus tm
in
  case summands of
    [] => raise Fail "strip_plus returned [] in collect_additive_consts"
  | [_] => NO_CONV tm
  | _ => let
    in
      case partition is_int_literal summands of
        ([], _) => NO_CONV tm
      | ([_], _) => NO_CONV tm
      | (_, []) => REDUCE_CONV tm
      | (numerals, non_numerals) => let
          val reorder_t = Psyntax.mk_eq(tm,
                           mk_plus(list_mk_plus non_numerals,
                                   list_mk_plus numerals))
          val reorder_thm =
            EQT_ELIM(AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM) reorder_t)
        in
          (K reorder_thm THENC REDUCE_CONV THENC
           TRY_CONV (REWR_CONV INT_ADD_RID)) tm
        end
    end
end

open simpLib

val INT_ADD_AC_ss =
    SIMPSET {ac = [(SPEC_ALL INT_ADD_ASSOC, SPEC_ALL INT_ADD_COMM)],
             convs = [], dprocs = [], filter = NONE, rewrs = [], congs = []}
val INT_MUL_AC_ss =
    SIMPSET {ac = [(SPEC_ALL INT_MUL_ASSOC, SPEC_ALL INT_MUL_COMM)],
             convs = [], dprocs = [], filter = NONE, rewrs = [], congs = []}

end;
