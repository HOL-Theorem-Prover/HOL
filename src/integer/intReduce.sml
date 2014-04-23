structure intReduce :> intReduce =
struct

open HolKernel boolLib integerTheory intSyntax simpLib

val ERR = mk_HOL_ERR "intSimps";

(*---------------------------------------------------------------------------*)
(* Integer-specific compset                                                  *)
(*---------------------------------------------------------------------------*)

val elim_thms = [INT_ADD_REDUCE, INT_SUB_REDUCE, INT_MUL_REDUCE,
                 INT_DIV_REDUCE, INT_MOD_REDUCE, INT_EXP_REDUCE,
                 INT_LT_REDUCE, INT_LE_REDUCE, INT_EQ_REDUCE,
                 INT_GT_REDUCE, INT_GE_REDUCE, INT_DIVIDES_REDUCE,
                 INT_ABS_NUM, INT_ABS_NEG, INT_QUOT_REDUCE, INT_REM_REDUCE,
                 INT_MAX, INT_MIN, NUM_OF_INT]

fun add_int_compset cmp = computeLib.add_thms elim_thms cmp

fun int_compset () =
   let
       val cmp = reduceLib.num_compset()
   in
      add_int_compset cmp; cmp
   end

(*---------------------------------------------------------------------------*)
(* Reducer for ground integer expressions                                    *)
(*---------------------------------------------------------------------------*)

val REDUCE_CONV = computeLib.CBV_CONV (int_compset())

(*---------------------------------------------------------------------------*)
(* Add integer reductions to the global compset                              *)
(*---------------------------------------------------------------------------*)

val _ = let open computeLib in add_funs elim_thms end;

(*---------------------------------------------------------------------------*)
(* Ground reduction conversions for integers (suitable for inclusion in      *)
(* simplifier, or as stand-alone                                             *)
(*---------------------------------------------------------------------------*)

local
  val num_ty = numSyntax.num
  val int_ty = intSyntax.int_ty
  val x = mk_var("x",int_ty)
  val y = mk_var("y",int_ty)
  val n = mk_var("n",num_ty)
  val basic_op_terms =
     [plus_tm, minus_tm, mult_tm, div_tm, mod_tm, int_eq_tm,
      less_tm, leq_tm, great_tm, geq_tm, divides_tm, rem_tm, quot_tm,
      min_tm, max_tm]
  val basic_op_patterns = map (fn t => list_mk_comb(t, [x,y])) basic_op_terms
  val exp_pattern = list_mk_comb(exp_tm, [x,n])
  val abs_patterns = [lhs (#2 (strip_forall (concl INT_ABS_NEG))),
                      lhs (#2 (strip_forall (concl INT_ABS_NUM)))]
  fun reducible t = is_int_literal t orelse numSyntax.is_numeral t
  fun reducer t =
    let val (_, args) = strip_comb t
    in if List.all reducible args then REDUCE_CONV t else Conv.NO_CONV t
    end
  fun mk_conv pat =
     {name = "Integer calculation",
      key = SOME([], pat), trace = 2,
      conv = K (K reducer)}
  val rederr = ERR "RED_CONV" "Term not reducible"
in
val INT_REDUCE_ss = SSFRAG
  {name=SOME"INT_REDUCE",
   convs = map mk_conv (exp_pattern::(abs_patterns @ basic_op_patterns)),
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

fun RED_CONV t =
 let val (f, args) = strip_comb t
     val _ = f = exp_tm orelse mem f basic_op_terms orelse raise rederr
     val _ = List.all reducible args orelse raise rederr
     val _ = not (Lib.can dom_rng (type_of t)) orelse raise rederr
 in
   REDUCE_CONV t
 end

end (* local *) ;

(*---------------------------------------------------------------------------*)
(* Add reducer to srw_ss                                                     *)
(*---------------------------------------------------------------------------*)

val _ = BasicProvers.augment_srw_ss [INT_REDUCE_ss];

(* Accumulate literal additions in integer expressions
    (doesn't do coefficient gathering - just adds up literals, and
     reassociates along the way)
*)
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
          val reorder_t = mk_eq(tm,
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

end
