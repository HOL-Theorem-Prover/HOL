(*===========================================================================
== LIBRARY:     reduce (part II)                                           ==
==                                                                         ==
== DESCRIPTION: Conversions to reduce arithmetic constant expressions      ==
==                                                                         ==
== AUTHOR:      Michael Norrish                                            ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              mn200@cl.cam.ac.uk                                         ==
==                                                                         ==
== DATE:        January 1999                                               ==
==                                                                         ==
== NOTE:        The original functionality in this file was provided by    ==
==              carefully written CONVs.  With the use of proper numerals  ==
==              (see numeralTheory), this is no longer necessary, and      ==
==              simple rewriting can be used for most tasks.               ==
==              It is the (untested) claim that this will be as efficient. ==
============================================================================*)

structure Arithconv :> Arithconv =
struct

fun failwith function = raise
 Exception.HOL_ERR{origin_structure = "Arithconv",
                   origin_function = function,
                           message = ""};

open HolKernel boolTheory basicHol90Lib Parse
open Num_conv;

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q

infix THEN |-> THENC;

val prove = Tactical.prove;
val num_CONV = Num_conv.num_CONV;
val MATCH_MP = Conv.MATCH_MP;

val num_ty   = mk_type{Tyop="num",  Args=[]};
val bool_ty  = mk_type{Tyop="bool", Args=[]};
val fun_ty   = fn (op_ty,arg_ty) => mk_type{Tyop="fun", Args=[op_ty,arg_ty]};
val b_b_ty   = fun_ty(bool_ty,bool_ty);
val b_b_b_ty = fun_ty(bool_ty,b_b_ty);
val n_b_ty   = fun_ty(num_ty,bool_ty);
val n_n_ty   = fun_ty(num_ty, num_ty);
val n_n_b_ty = fun_ty(num_ty,n_b_ty);
val n_n_n_ty = fun_ty(num_ty, n_n_ty);
val xv       = mk_var {Name= "x", Ty=num_ty};
val yv       = mk_var {Name= "y", Ty=num_ty};
val zv       = mk_var {Name= "z", Ty=num_ty};
val pv       = mk_var {Name= "p", Ty=num_ty};
val qv       = mk_var {Name= "q", Ty=num_ty};
val rv       = mk_var {Name= "r", Ty=num_ty};
val numeral  = mk_const{Name= "NUMERAL", Ty = n_n_ty};
val sucop    = mk_const{Name= "SUC", Ty = n_n_ty};
val preop    = mk_const{Name= "PRE", Ty = n_n_ty};
val plusop   = mk_const{Name = "+", Ty = n_n_n_ty};
val multop   = mk_const{Name = "*", Ty = n_n_n_ty};
val expop    = mk_const{Name = "EXP", Ty = n_n_n_ty};
val minusop  = mk_const{Name = "-", Ty = n_n_n_ty};
val beqop    = mk_const{Name= "=", Ty= b_b_b_ty};
val neqop    = mk_const{Name= "=", Ty= n_n_b_ty};
val ltop     = mk_const{Name= "<", Ty= n_n_b_ty};
val gtop     = mk_const{Name= ">", Ty= n_n_b_ty};
val leop     = mk_const{Name= "<=", Ty= n_n_b_ty};
val geop     = mk_const{Name= ">=", Ty= n_n_b_ty};
val evenop   = mk_const{Name= "EVEN", Ty = Type.-->(num_ty, bool_ty)}
val oddop    = mk_const{Name= "ODD", Ty = Type.-->(num_ty, bool_ty)}

val truth    = mk_const{Name = "T", Ty = bool_ty};
val falsity  = mk_const{Name = "F", Ty = bool_ty};

open numeralTheory

(*-----------------------------------------------------------------------*)
(* dest_op - Split application down spine, checking head operator        *)
(*-----------------------------------------------------------------------*)

fun dest_op opr tm =
    let val (opr',arg) = Dsyntax.strip_comb tm
    in
	if (opr=opr') then arg else failwith "dest_op"
    end;

(* a "conv-al" that takes a conv and makes it fail if the result is
   not either true, false or a numeral *)
fun TFN_CONV c t = let
  val result = c t
  val result_t = rhs (concl result)
in
  if result_t = truth orelse result_t = falsity orelse is_numeral result_t then
    result
  else
    failwith "TFN_CONV"
end


(*-----------------------------------------------------------------------*)
(* NEQ_CONV "[x] = [y]" = |- ([x] = [y]) = [x=y -> T | F]                *)
(*-----------------------------------------------------------------------*)

local val NEQ_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_eq])
in
fun NEQ_CONV tm =
  case dest_op neqop tm
   of [xn,yn] => (NEQ_RW tm handle HOL_ERR _ => failwith "NEQ_CONV")
    |    _    => failwith "NEQ_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LT_CONV "[x] < [y]" = |- ([x] < [y]) = [x<y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

local val LT_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lt])
in
fun LT_CONV tm =
  case dest_op ltop tm
   of [xn,yn] => (LT_RW tm handle HOL_ERR _ => failwith "LT_CONV")
    |   _     => failwith "LT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GT_CONV "[x] > [y]" = |- ([x] > [y]) = [x>y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

local val GT_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lt])
in
fun GT_CONV tm =
  case dest_op gtop tm
   of [_, _] => (GT_RW tm handle HOL_ERR _ => failwith "GT_CONV")
    |   _    => failwith "GT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LE_CONV "[x] <= [y]" = |- ([x]<=> [y]) = [x<=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

local val LE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lte])
in
fun LE_CONV tm =
  case dest_op leop tm
   of [xn,yn] => (LE_RW tm handle HOL_ERR _ => failwith "LE_CONV")
    |    _    => failwith "LE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GE_CONV "[x] >= [y]" = |- ([x] >= [y]) = [x>=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

local val GE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lte])
in
fun GE_CONV tm =
  case dest_op geop tm
   of [xn,yn] => (GE_RW tm handle HOL_ERR _ => failwith "GE_CONV")
    |    _    => failwith "GE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* EVEN_CONV "EVEN [x]" = |- EVEN [x] = [ x divisible by 2 -> T | F ]    *)
(*-----------------------------------------------------------------------*)

local
  val EC = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_evenodd])
in
  fun EVEN_CONV tm =
    case dest_op evenop tm of
      [xn] => (EC tm handle HOL_ERR _ => failwith "EVEN_CONV")
    | _ => failwith "EVEN_CONV"
end

(*-----------------------------------------------------------------------*)
(* ODD_CONV "ODD [x]" = |- ODD [x] = [ x divisible by 2 -> F | T ]       *)
(*-----------------------------------------------------------------------*)

local
  val OC = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_evenodd])
in
  fun ODD_CONV tm =
    case dest_op oddop tm of
      [xn] => (OC tm handle HOL_ERR _ => failwith "ODD_CONV")
    | _ => failwith "ODD_CONV"
end

(*-----------------------------------------------------------------------*)
(* SUC_CONV "SUC [x]" = |- SUC [x] = [x+1]                               *)
(*-----------------------------------------------------------------------*)

local val SUC_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_suc])
in
fun SUC_CONV tm =
 case dest_op sucop tm
  of [xn] => SUC_RW tm
   |  _   => failwith "SUC_CONV"
end;

(*-----------------------------------------------------------------------*)
(* PRE_CONV "PRE [n]" = |- PRE [n] = [n-1]                               *)
(*-----------------------------------------------------------------------*)

val save_zero = prove(Term`NUMERAL ALT_ZERO = 0`,
                      REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
                                   arithmeticTheory.ALT_ZERO]);
local
 val PRE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_pre,save_zero])
in
fun PRE_CONV tm =
  case dest_op preop tm
   of [xn] => (PRE_RW tm handle HOL_ERR _ => failwith "PRE_CONV")
    |  _   => failwith "PRE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* SBC_CONV "[x] - [y]" = |- ([x] - [y]) = [x - y]                       *)
(*-----------------------------------------------------------------------*)

local
 val SBC_RW =
   TFN_CONV (REWRITE_CONV
       [numeral_distrib, numeral_sub,iSUB_THM,
        iDUB_removal,numeral_pre, numeral_lt])
in
fun SBC_CONV tm =
  case dest_op minusop tm
   of [xn,yn] => (SBC_RW tm handle HOL_ERR _ => failwith "SBC_CONV")
    |    _    => failwith "SBC_CONV"
end;

(*-----------------------------------------------------------------------*)
(* ADD_CONV "[x] + [y]" = |- [x] + [y] = [x+y]                           *)
(*-----------------------------------------------------------------------*)

local
 val ADD_RW =
   TFN_CONV (REWRITE_CONV
      [numeral_distrib, numeral_add,numeral_suc, numeral_iisuc])
in
fun ADD_CONV tm =
  case dest_op plusop tm
   of [xn, yn] => (ADD_RW tm handle HOL_ERR _ => failwith "ADD_CONV")
    |    _     => failwith "ADD_CONV"
end;

(*-----------------------------------------------------------------------*)
(* MUL_CONV "[x] * [y]" = |- [x] * [y] = [x * y]                         *)
(*-----------------------------------------------------------------------*)

local
  val MUL_RW =
    TFN_CONV (REWRITE_CONV
      [numeral_distrib, numeral_add, numeral_suc,
       numeral_iisuc, numeral_mult, iDUB_removal, numeral_pre])
in
fun MUL_CONV tm =
  case dest_op multop tm
   of [xn,yn] => (MUL_RW tm handle HOL_ERR _ => failwith "MUL_CONV")
    |    _    => failwith "MUL_CONV"
end;

(*-----------------------------------------------------------------------*)
(* EXP_CONV "[x] EXP [y]" = |- [x] EXP [y] = [x ** y]                    *)
(*-----------------------------------------------------------------------*)

local
 val RW1 = REWRITE_CONV [numeral_distrib, numeral_exp]
 val RW2 = REWRITE_CONV [numeral_add, numeral_suc, numeral_iisuc,
                         numeral_mult, iDUB_removal, numeral_pre, iSQR]
 val EXP_RW = TFN_CONV (RW1 THENC RW2)
in
fun EXP_CONV tm =
  case dest_op expop tm
   of [xn,yn] => (EXP_RW tm handle HOL_ERR _ => failwith "EXP_CONV")
    |    _    => failwith "EXP_CONV"
end;

(*-----------------------------------------------------------------------*)
(* DIV_CONV "[x] DIV [y]" = |- [x] DIV [y] = [x div y]                   *)
(*-----------------------------------------------------------------------*)

val int_of_term = Term.dest_numeral
val term_of_int = Term.mk_numeral

fun provelt x y =
  EQT_ELIM (LT_CONV (list_mk_comb(ltop, [term_of_int x, term_of_int y])))

val DIV_CONV = let
  val divt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x DIV y = q)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC (arithmeticTheory.DIV_UNIQUE) THEN
	  EXISTS_TAC (--`r:num`--) THEN ASM_REWRITE_TAC[])
    and divop = (--`$DIV`--)
    and multop = (--`$*`--)
    and plusop = (--`$+`--)
in
  fn tm =>
  case (dest_op divop tm) of
    [xn,yn] => (let
      open Arbnum
      val x = int_of_term xn
      and y = int_of_term yn
      val q = x div y
      val p = q * y
      val r = x - p
      val pn = term_of_int p
      and qn = term_of_int q
      and rn = term_of_int r
      val p1 = MUL_CONV
        (mk_comb{Rator=mk_comb{Rator=multop, Rand=qn}, Rand=yn})
      and p2 = ADD_CONV
        (mk_comb{Rator=mk_comb{Rator=plusop, Rand=pn}, Rand=rn})
      and p3 = provelt r y
      and chain = INST [xv |-> xn, yv |-> yn, pv |-> pn,
                        qv |-> qn, rv |-> rn] divt
    in
      MP (MP (MP chain p1) p2) p3
    end handle HOL_ERR _ => failwith "DIV_CONV")
  | _ => failwith "DIV_CONV"
end;

(*-----------------------------------------------------------------------*)
(* MOD_CONV "[x] MOD [y]" = |- [x] MOD [y] = [x mod y]                   *)
(*-----------------------------------------------------------------------*)

val MOD_CONV =
let val modt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x MOD y = r)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC (arithmeticTheory.MOD_UNIQUE) THEN
	  EXISTS_TAC (--`q:num`--) THEN ASM_REWRITE_TAC[])
    and modop  = (--`$MOD`--)
    and multop = (--`$*`--)
    and plusop = (--`$+`--)
in
 fn tm =>
  case (dest_op modop tm)
   of [xn,yn] =>
      (let val x = int_of_term xn and y = int_of_term yn
           open Arbnum
           val q = x div y
           val p = q * y
           val r = x - p
           val pn = term_of_int p
           and qn = term_of_int q
           and rn = term_of_int r
           val p1 = MUL_CONV
                     (mk_comb{Rator=mk_comb{Rator=multop, Rand=qn}, Rand=yn})
           and p2 = ADD_CONV
                     (mk_comb{Rator=mk_comb{Rator=plusop, Rand=pn}, Rand=rn})
           and p3 = provelt r y
           and chain = INST [xv |-> xn, yv |-> yn, pv |-> pn,
                             qv |-> qn, rv |-> rn] modt
       in
         MP (MP (MP chain p1) p2) p3
      end handle HOL_ERR _ => failwith "MOD_CONV")
 | _ => failwith "MOD_CONV"
end;

end
