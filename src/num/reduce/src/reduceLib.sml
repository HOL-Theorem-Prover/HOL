structure reduceLib :> reduceLib =
struct

  open HolKernel Parse basicHol90Lib Boolconv Arithconv
       pairTheory arithmeticTheory numeralTheory computeLib;
  infix THEN |-> ;

type conv   = Abbrev.conv
type tactic = Abbrev.tactic
type thm    = Thm.thm

fun failwith function = raise
 Exception.HOL_ERR{origin_structure = "reduceLib",
                   origin_function = function,
                           message = ""};


(*-----------------------------------------------------------------------*)
(* RED_CONV - Try all the conversions in the library                     *)
(*-----------------------------------------------------------------------*)

val RED_CONV =
  let fun FAIL_CONV (s:string) tm = failwith s
  in
      Lib.itlist (Lib.curry (Conv.ORELSEC))
         [ADD_CONV,  AND_CONV,  BEQ_CONV,  COND_CONV, EVEN_CONV,
          DIV_CONV,  EXP_CONV,   GE_CONV,    GT_CONV, ODD_CONV,
          IMP_CONV,   LE_CONV,   LT_CONV,   MOD_CONV,
          MUL_CONV,  NEQ_CONV,  NOT_CONV,    OR_CONV,
          PRE_CONV,  SBC_CONV,  SUC_CONV] (FAIL_CONV "RED_CONV")
  end;

(*-----------------------------------------------------------------------*)
(* REDUCE_CONV - Perform above reductions at any depth.                  *)
(* Uses computeLib.                                                      *)
(*-----------------------------------------------------------------------*)

val bool_rewrites =
  (false,
   [ INST_TYPE [alpha |-> bool] REFL_CLAUSE,
     COND_CLAUSES, COND_ID, NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES,
     IMP_CLAUSES, EQ_CLAUSES ]);

val REFL_EQ_0 =
  INST_TYPE [alpha |-> Type `:num`] REFL_CLAUSE;

val NORM_0 = prove(Term `NUMERAL ALT_ZERO = 0`,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO]);

val numeral_rewrites =
  [ numeral_distrib, REFL_EQ_0, numeral_eq, numeral_suc, numeral_pre, NORM_0,
    numeral_iisuc, numeral_add, numeral_mult, iDUB_removal,
    numeral_sub, numeral_lt, numeral_lte, iSUB_THM,
    numeral_exp, numeral_evenodd, iSQR ];

val div_thm =
    prove
      (Term ` !x y q r. x DIV y =
              if (x = q * y + r) /\ (r < y) then q else x DIV y `,
       REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
       MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC (Term `r:num`) THEN
       ASM_REWRITE_TAC []);

val mod_thm =
    prove
      (Term ` !x y q r. x MOD y = 
              if (x = q * y + r) /\ (r < y) then r else x MOD y `,
       REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
       MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (Term `q:num`) THEN
       ASM_REWRITE_TAC []);


fun dest_op opr tm =
    let val (opr',arg) = Dsyntax.strip_comb tm in
    if (opr=opr') then arg else raise Fail "dest_op"
    end;

val divop = Term `$DIV`;
val modop = Term `$MOD`;

fun cbv_DIV_CONV tm =
  case (dest_op divop tm) of
    [x,y] => (let
      open Arbnum
      val (q,r) = divmod (dest_numeral x, dest_numeral y) in
      SPECL [x, y, mk_numeral q, mk_numeral r] div_thm
    end handle HOL_ERR _ => failwith "cbv_DIV_CONV")
  | _ => raise Fail "cbv_DIV_CONV";

fun cbv_MOD_CONV tm =
  case (dest_op modop tm) of
    [x,y] => (let
      open Arbnum
      val (q,r) = divmod (dest_numeral x, dest_numeral y) in
      SPECL [x, y, mk_numeral q, mk_numeral r] mod_thm
    end handle HOL_ERR _ => failwith "cbv_MOD_CONV")
  | _ => raise Fail "cbv_MOD_CONV";


fun reduce_rws () =
  let val rws = from_list bool_rewrites
      val _ = add_thms (true,numeral_rewrites) rws
      val _ = add_conv (divop, 2, cbv_DIV_CONV) rws
      val _ = add_conv (modop, 2, cbv_MOD_CONV) rws
  in rws end;


local val rws = reduce_rws() in
val REDUCE_CONV = CBV_CONV rws
end;

(* Define a basic computeLib.comp_rws extending reduce_rws with
 * simplifications about LET, pairs, curryfication, ...
 *)
fun basic_rws () =
  let val rws = reduce_rws ()
      val _ = add_thms (true, [strictify_thm LET_DEF, FST, SND])
      val _ = add_thms (false, [CURRY_DEF, UNCURRY_DEF])
  in rws end;


(*-----------------------------------------------------------------------*)
(* REDUCE_RULE and REDUCE_TAC - Inference rule and tactic versions.      *)
(*-----------------------------------------------------------------------*)

val REDUCE_RULE = Conv.CONV_RULE REDUCE_CONV;

val REDUCE_TAC = Conv.CONV_TAC REDUCE_CONV;


end;
