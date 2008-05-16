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

open HolKernel boolTheory boolLib Parse Rsyntax
     Num_conv numSyntax arithmeticTheory numeralTheory;

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars arithmeticTheory.arithmetic_grammars

val ERR = mk_HOL_ERR "Arithconv"
fun failwith function = raise (ERR function "")


(*---------------------------------------------------------------------------
    A "conv-al" that takes a conv and makes it fail if the
    result is not either true, false or a numeral.
 ---------------------------------------------------------------------------*)

fun TFN_CONV c t =
 let val result = c t
     val result_t = rhs (concl result)
 in
   if result_t = T orelse result_t = F orelse Literal.is_numeral result_t
     then result
     else failwith "TFN_CONV"
end


(*-----------------------------------------------------------------------*)
(* NEQ_CONV "[x] = [y]" = |- ([x] = [y]) = [x=y -> T | F]                *)
(*-----------------------------------------------------------------------*)

local 
 val NEQ_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_eq])
 val REFL_CLAUSE_num = INST_TYPE [alpha |-> num] REFL_CLAUSE
in
fun NEQ_CONV tm =
 case total boolLib.dest_eq tm
  of NONE => failwith "NEQ_CONV" 
   | SOME (n1,n2) =>
      if is_numeral n1 andalso is_numeral n2 
      then if n1=n2 then SPEC n1 REFL_CLAUSE_num
           else with_exn NEQ_RW tm (ERR "NEQ_CONV" "")
      else failwith "NEQ_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LT_CONV "[x] < [y]" = |- ([x] < [y]) = [x<y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

local val LT_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lt])
in
fun LT_CONV tm =
  if is_less tm then with_exn LT_RW tm (ERR "LT_CONV" "")
  else failwith "LT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GT_CONV "[x] > [y]" = |- ([x] > [y]) = [x>y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

local val GT_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lt])
in
fun GT_CONV tm =
  if is_greater tm then with_exn GT_RW tm (ERR "GT_CONV" "")
  else failwith "GT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LE_CONV "[x] <= [y]" = |- ([x]<=> [y]) = [x<=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

local val LE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lte])
in
fun LE_CONV tm =
 if is_leq tm then with_exn LE_RW tm (ERR "LE_CONV" "") else failwith "LE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GE_CONV "[x] >= [y]" = |- ([x] >= [y]) = [x>=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

local val GE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_lte])
in
fun GE_CONV tm =
 if is_geq tm then with_exn GE_RW tm (ERR "GE_CONV" "")
 else failwith "GE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* EVEN_CONV "EVEN [x]" = |- EVEN [x] = [ x divisible by 2 -> T | F ]    *)
(*-----------------------------------------------------------------------*)

local val EC = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_evenodd])
in
fun EVEN_CONV tm =
  if is_even tm then with_exn EC tm (ERR "EVEN_CONV" "")
  else failwith "EVEN_CONV"
end

(*-----------------------------------------------------------------------*)
(* ODD_CONV "ODD [x]" = |- ODD [x] = [ x divisible by 2 -> F | T ]       *)
(*-----------------------------------------------------------------------*)

local val OC = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_evenodd])
in
fun ODD_CONV tm =
 if is_odd tm then with_exn OC tm (ERR "ODD_CONV" "") else failwith "ODD_CONV"
end

(*-----------------------------------------------------------------------*)
(* SUC_CONV "SUC [x]" = |- SUC [x] = [x+1]                               *)
(*-----------------------------------------------------------------------*)

local val SUC_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_suc])
in
fun SUC_CONV tm =
 if is_suc tm then with_exn SUC_RW tm (ERR "SUC_CONV" "")
 else failwith "SUC_CONV"
end;

(*-----------------------------------------------------------------------*)
(* PRE_CONV "PRE [n]" = |- PRE [n] = [n-1]                               *)
(*-----------------------------------------------------------------------*)

local
  val PRE_RW = TFN_CONV (REWRITE_CONV [numeral_distrib, numeral_pre,NORM_0])
in
fun PRE_CONV tm =
 if is_pre tm then with_exn PRE_RW tm (ERR "PRE_CONV" "")
 else failwith "PRE_CONV"
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
  if is_minus tm then with_exn SBC_RW tm (ERR "SBC_CONV" "")
  else failwith "SBC_CONV"
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
 if is_plus tm then with_exn ADD_RW tm (ERR "ADD_CONV" "")
 else failwith "ADD_CONV"
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
  if is_mult tm then with_exn MUL_RW tm (ERR "MUL_CONV" "")
  else failwith "MUL_CONV"
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
  if is_exp tm then with_exn EXP_RW tm (ERR "EXP_CONV" "")
  else failwith "EXP_CONV"
end;

(*-----------------------------------------------------------------------*)
(* DIV_CONV "[x] DIV [y]" = |- [x] DIV [y] = [x div y]                   *)
(*-----------------------------------------------------------------------*)

fun provelt x y = EQT_ELIM (LT_CONV (mk_less(mk_numeral x, mk_numeral y)))

val xv = mk_var {Name= "x", Ty=num}
val yv = mk_var {Name= "y", Ty=num}
val zv = mk_var {Name= "z", Ty=num}
val pv = mk_var {Name= "p", Ty=num}
val qv = mk_var {Name= "q", Ty=num}
val rv = mk_var {Name= "r", Ty=num};

local val divt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x DIV y = q)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC (arithmeticTheory.DIV_UNIQUE) THEN
	  EXISTS_TAC (--`r:num`--) THEN ASM_REWRITE_TAC[])
in
fun DIV_CONV tm =
  let open Arbnum
      val (xn,yn) = dest_div tm
      val x = dest_numeral xn
      and y = dest_numeral yn
      val q = x div y
      val p = q * y
      val r = x - p
      val pn = mk_numeral p
      and qn = mk_numeral q
      and rn = mk_numeral r
      val p1 = MUL_CONV (mk_mult(qn,yn))
      and p2 = ADD_CONV (mk_plus(pn,rn))
      and p3 = provelt r y
      and chain = INST [xv |-> xn, yv |-> yn, pv |-> pn,
                        qv |-> qn, rv |-> rn] divt
  in
     MP (MP (MP chain p1) p2) p3
  end handle HOL_ERR _ => failwith "DIV_CONV"
           | Div => raise ERR "DIV_CONV" "attempt to divide by zero"
end;

(*-----------------------------------------------------------------------*)
(* MOD_CONV "[x] MOD [y]" = |- [x] MOD [y] = [x mod y]                   *)
(*-----------------------------------------------------------------------*)

local val modt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x MOD y = r)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC arithmeticTheory.MOD_UNIQUE THEN
	  EXISTS_TAC (--`q:num`--) THEN ASM_REWRITE_TAC[])
in
fun MOD_CONV tm =
 let open Arbnum
     val (xn,yn) = dest_mod tm
     val x = dest_numeral xn
     and y = dest_numeral yn
     val q = x div y
     val p = q * y
     val r = x - p
     val pn = mk_numeral p
     and qn = mk_numeral q
     and rn = mk_numeral r
     val p1 = MUL_CONV (mk_mult(qn,yn))
     and p2 = ADD_CONV (mk_plus(pn,rn))
     and p3 = provelt r y
     and chain = INST [xv |-> xn, yv |-> yn, pv |-> pn,
                       qv |-> qn, rv |-> rn] modt
   in
      MP (MP (MP chain p1) p2) p3
   end handle HOL_ERR _ => failwith "MOD_CONV"
            | Div => raise ERR "MOD_CONV" "attempt to take mod 0"
end;

val _ = Parse.temp_set_grammars ambient_grammars

end
