structure DecideNum =
struct

local

open Exception Term Dsyntax Theory Rewrite
     Psyntax Conv DecisionConv DecisionSupport NumArith NumArithCons;
infix THENC;
infix ORELSEC;

local
   open NumHOLType
in
   val mult = mult
   val unops = [suc,pre]
   and arithops = [plus,minus,mult]
   and relops = [less,leq,great,geq]
   val binops = arithops @ relops
   fun op_name f = #Name (Rsyntax.dest_const f)
   fun is_num_const_struct tm =
      (is_num_const tm) orelse
      let val (f,args) = strip_comb tm
          val fname = op_name f (* Fails if f is not a constant *)
      in  case args
          of [arg] => (member fname unops) andalso (is_num_const_struct arg)
           | [arg1,arg2] =>
                (member fname arithops) andalso
                (is_num_const_struct arg1) andalso (is_num_const_struct arg2)
           | _ => false
      end
      handle _ => false
end;


fun num_discrim (_: bool) tm =
  if NumArithCons.is_num_const tm then (fn _ => tm, [])
  else let
    val (f,args) = strip_comb tm
  in
    case (length args) of
      0 => if (NumArithCons.is_num_var f) then (fn _ => tm,[])
           else Decide.failwith "num_discrim"
    | 1 => if (is_const f) andalso (member (op_name f) unops) then
             (fn args' => list_mk_comb (f,args'),args)
           else
             Decide.failwith "num_discrim"
    | 2 => if (is_const f) andalso (member (op_name f) binops) andalso
             (not (op_name f = mult) orelse
              (is_num_const_struct (arg1 tm)) orelse
              (is_num_const_struct (arg2 tm)))
             then (fn args' => list_mk_comb (f,args'),args)
           else Decide.failwith "num_discrim"
    | _ => Decide.failwith "num_discrim"
  end;

in

(*
val SUB_NORM_CONV =
 GEN_REWRITE_CONV Lib.I Rewrite.empty_rewrites
 [arithmeticTheory.SUB_LEFT_ADD,          arithmeticTheory.SUB_RIGHT_ADD,
  arithmeticTheory.SUB_LEFT_SUB,          arithmeticTheory.SUB_RIGHT_SUB,
  arithmeticTheory.LEFT_SUB_DISTRIB,      arithmeticTheory.RIGHT_SUB_DISTRIB,
  arithmeticTheory.SUB_LEFT_SUC,
  arithmeticTheory.SUB_LEFT_LESS_EQ,      arithmeticTheory.SUB_RIGHT_LESS_EQ,
  arithmeticTheory.SUB_LEFT_LESS,         arithmeticTheory.SUB_RIGHT_LESS,
  arithmeticTheory.SUB_LEFT_GREATER_EQ,  arithmeticTheory.SUB_RIGHT_GREATER_EQ,
  arithmeticTheory.SUB_LEFT_GREATER,      arithmeticTheory.SUB_RIGHT_GREATER,
  arithmeticTheory.SUB_LEFT_EQ,           arithmeticTheory.SUB_RIGHT_EQ,
  arithmeticTheory.PRE_SUB1
 ];
*)

(*--------------------------------------------------------------------------*)
(* REDEPTH_CONV is more efficient than TOP_DEPTH_CONV. Also, with           *)
(* TOP_DEPTH_CONV special measures are required to avoid looping, and       *)
(* conditional expression elimination has to be included.                   *)
(*--------------------------------------------------------------------------*)

val SUB_ELIM_CONV =
   REDEPTH_CONV
      (DecisionArithConvs.SUB_NORM_CONV ORELSEC
       DecisionArithConvs.NUM_COND_RATOR_CONV ORELSEC
       DecisionArithConvs.NUM_COND_RAND_CONV ORELSEC
       NormalizeBool.COND_ABS_CONV);

val ARITH_NORM_CONV = RULE_OF_CONV ARITH_LITERAL_NORM_CONV;

local

open NumArithCons LazyThm;

val mk_one = NumHOLType.term_of_num NumType.num1

in

fun ARITH_FALSE_CONV tm =
   if ((is_eq o dest_neg o #1 o dest_conj) tm handle HOL_ERR _ => false)
   then
   let val (diseq,conj) = dest_conj tm
       val (l,r) = dest_eq (dest_neg diseq)
       val disjl = mk_conj (mk_leq (mk_plus (mk_one,l),r),conj)
       and disjr = mk_conj (mk_leq (mk_plus (mk_one,r),l),conj)
       fun rule thl thr =
          RIGHT_CONV_RULE
             (LEFT_CONV (fn _ => thl) THENC RIGHT_CONV (fn _ => thr) THENC
              DecisionNormConvs.OR_F_CONV)
             ((LEFT_CONV (DecisionArithConvs.NOT_NUM_EQ_NORM_CONV) THENC
               DecisionNormConvs.RIGHT_DISJ_NORM_CONV) tm)
   in  apply_rule2 (fn _ => fn _ => ([],mk_eq (tm,F)),rule)
          (INEQS_FALSE_CONV disjl) (INEQS_FALSE_CONV disjr)
   end
   else INEQS_FALSE_CONV tm;

end;

val num_proc =
   {Name = "num",
    Description = "Linear arithmetic over natural numbers",
    Author = "Richard J. Boulton",
    Discriminator = num_discrim,
    Normalizer = SUB_ELIM_CONV THENC
                 NormalizeBool.EXPAND_BOOL_CONV NormalizeBool.Disjunctive
                    ARITH_NORM_CONV,
    Procedure = Decide.make_incremental_procedure LazyRules.CONJ
                   ARITH_FALSE_CONV}

end;

end; (* DecideNum *)
