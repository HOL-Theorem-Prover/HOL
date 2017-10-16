(*****************************************************************************)
(* FILE          : sub_and_cond.sml                                          *)
(* DESCRIPTION   : Elimination of subtraction from natural number formulae   *)
(*                 and elimination of conditionals.                          *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 9th April 1992                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Sub_and_cond :> Sub_and_cond =
struct
  open Arbint HolKernel Parse boolLib RJBConv Thm_convs

val COND_ABS       = boolTheory.COND_ABS;
val TOP_DEPTH_CONV = Conv.TOP_DEPTH_CONV;

fun failwith function =
   raise HOL_ERR{origin_structure = "Sub_and_cond",
                 origin_function = function,
                 message = ""};


(*---------------------------------------------------------------------------*)
(* COND_ABS_CONV : conv                                                      *)
(*---------------------------------------------------------------------------*)

fun COND_ABS_CONV tm =
 (let val (v,bdy) = dest_abs tm
      val (cond,x,y) = dest_cond bdy
      val _ = assert (not o equal Type.bool o type_of) x
      val b = assert (not o Lib.op_mem aconv v o free_vars) cond
      val xf = mk_abs(v,x)
      and yf = mk_abs(v,y)
      val th1 = INST_TYPE [alpha |-> type_of v, beta |-> type_of x] COND_ABS
      val th2 = SPECL [b,xf,yf] th1
  in  CONV_RULE (RATOR_CONV (RAND_CONV (ABS_CONV
         (RATOR_CONV (RAND_CONV BETA_CONV) THENC RAND_CONV BETA_CONV) THENC
         ALPHA_CONV v))) th2
  end
 ) handle (HOL_ERR _) => failwith "COND_ABS_CONV";

(* ----------------------------------------------------------------------
    SUB_NORM_CONV' : bool -> term

    Eliminates as many subtractions as possible without introducing any
    goal-blowup in the term, knowing that it is going to be normalised
    subsequently.  In particular, the term is going to be negated and then
    converted to DNF.

    So, it's fine to introduce a disjunction at the top level or under
    another disjunction.  On the other hand, introducing a conjunction at
    this level has just doubled the goal size.

    The boolean is true at top-level and flips as negations are traversed.
   ---------------------------------------------------------------------- *)

fun termsig t =
  let val {Thy,Name,...} = dest_thy_const t
  in
    SOME(Thy,Name)
  end handle HOL_ERR _ => NONE

datatype termposn = Positive | Negative | Both
fun pneg Positive = Negative | pneg Negative = Positive | pneg Both = Both

val SUB_LEFT_LESS_EQ' =
    REWRITE_RULE [arithmeticTheory.LESS_EQ_0] arithmeticTheory.SUB_LEFT_LESS_EQ

val peqn_or_nleqp = let
  val p = mk_var("p", numSyntax.num)
  val n = mk_var("n", numSyntax.num)
  val peqn = mk_eq(p,n)
  val nlep = numSyntax.mk_leq(n,p)
  val l = mk_disj(peqn, nlep)
  val nle = mk_comb(numSyntax.leq_tm, n)
in
  IMP_ANTISYM_RULE
    (DISCH_ALL (DISJ_CASES (ASSUME l)
                           (EQ_MP (AP_TERM nle (ASSUME peqn) |> SYM)
                                  (SPEC n arithmeticTheory.LESS_EQ_REFL))
                           (ASSUME nlep)))
    (DISCH_ALL (DISJ2 peqn (ASSUME nlep)))
end


val SUB_LEFT_EQ0 = let
  open arithmeticTheory
in
  SUB_LEFT_EQ |> SPEC numSyntax.zero_tm
              |> REWRITE_RULE [ADD_CLAUSES, LESS_EQ_REFL, peqn_or_nleqp]
end
val SUB_RIGHT_EQ0 =
    CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ))) SUB_LEFT_EQ0

fun SUBEQC_CONV t =
  let
    open arithmeticTheory
    val (l,r) = dest_eq t
  in
    if numSyntax.is_minus l andalso numSyntax.is_numeral r then
      REWR_CONV SUB_RIGHT_EQ THENC RAND_CONV (RAND_CONV reduceLib.LE_CONV) THENC
      REWRITE_CONV []
    else if numSyntax.is_minus r andalso numSyntax.is_numeral l then
      REWR_CONV SUB_LEFT_EQ THENC RAND_CONV (LAND_CONV reduceLib.LE_CONV) THENC
      REWRITE_CONV []
    else NO_CONV
  end t


fun SUB_NORM_CONV' topp t =
  let
    open arithmeticTheory
    val (f, args) = strip_comb t
  in
    case (termsig f, length args) of
        (SOME("bool", "/\\"), 2) => BINOP_CONV (SUB_NORM_CONV' topp)
      | (SOME("bool", "\\/"), 2) => BINOP_CONV (SUB_NORM_CONV' topp)
      | (SOME("bool", "~"), 1) => RAND_CONV (SUB_NORM_CONV' (pneg topp))
      | (SOME("min", "==>"), 2) =>
        FORK_CONV (SUB_NORM_CONV' (pneg topp), SUB_NORM_CONV' topp)
      | (SOME("bool", "!"), 1) => RAND_CONV (ABS_CONV (SUB_NORM_CONV' topp))
      | (SOME("bool", "?"), 1) => RAND_CONV (ABS_CONV (SUB_NORM_CONV' topp))
      | (SOME("bool", "COND"), 3) =>
         BINOP_CONV (SUB_NORM_CONV' topp) THENC
         RATOR_CONV (RATOR_CONV (RAND_CONV (SUB_NORM_CONV' Both)))
      | (SOME("arithmetic", ">"), 2) =>
          REWR_CONV GREATER_DEF THENC SUB_NORM_CONV' topp
      | (SOME("arithmetic", ">="), 2) =>
          REWR_CONV GREATER_EQ THENC SUB_NORM_CONV' topp
      | (SOME("arithmetic", "<="), 2) =>
        (case topp of
             Positive => FIRST_CONV [REWR_CONV SUB_RIGHT_LESS_EQ,
                                     REWR_CONV SUB_LEFT_LESS_EQ', ALL_CONV]
           | _ => TRY_CONV (REWR_CONV SUB_RIGHT_LESS_EQ))
      | (SOME("prim_rec", "<"), 2) =>
        (case topp of
             Negative => FIRST_CONV [REWR_CONV SUB_LEFT_LESS,
                                     REWR_CONV SUB_RIGHT_LESS, ALL_CONV]
           | _ => TRY_CONV (REWR_CONV SUB_LEFT_LESS))
      | (SOME("min", "="), 2) =>
        FIRST_CONV [REWR_CONV SUB_LEFT_EQ0, REWR_CONV SUB_RIGHT_EQ0,
                    SUBEQC_CONV, ALL_CONV]
      | _ => ALL_CONV
  end t

val TRY_SUB_NORM = let
  open arithmeticTheory
in
  PURE_REWRITE_CONV [PRE_SUB1, SUB_EQUAL_0, SUB_RIGHT_SUB, LEFT_SUB_DISTRIB,
                     RIGHT_SUB_DISTRIB] THENC
  SUB_NORM_CONV' Positive
end

fun find_elim p t m = let
  fun doit t =
    if numSyntax.is_minus t then
      UNBETA_CONV t THENC
      REWR_CONV arithmeticTheory.SUB_ELIM_THM THENC
      BINDER_CONV (BINOP_CONV (RAND_CONV BETA_CONV)) THENC
      PURE_REWRITE_CONV [arithmeticTheory.ADD_CLAUSES,
                         arithmeticTheory.SUB_EQUAL_0,
                         arithmeticTheory.SUB_0]
    else NO_CONV
in
  case dest_term t of
      COMB(f,x) => find_elim (p o RATOR_CONV) f ORELSEC
                   find_elim (p o RAND_CONV) x ORELSEC doit t
    | LAMB(_, body) => if type_of body = bool then
                         p (ABS_CONV (find_elim I body))
                       else NO_CONV
    | _ => NO_CONV
end m

fun ELIM_SUB1 t = find_elim I t t

val NEW_SUB_ELIM_CONV = TRY_SUB_NORM THENC REPEATC ELIM_SUB1


(*---------------------------------------------------------------------------*)
(* SUB_AND_COND_ELIM_CONV : conv                                             *)
(*                                                                           *)
(* Subtraction cannot be eliminated without eliminating conditionals that    *)
(* enclose the subtraction operator. This function is not as delicate as it  *)
(* could be: it eliminates all conditionals in arithmetic formulae as well   *)
(* as eliminating natural number subtraction.                                *)
(*                                                                           *)
(* Care has to be taken with the conditional lifting theorems because they   *)
(* can loop if they try to move a conditional past another conditional, e.g. *)
(*                                                                           *)
(*    b1 => x | (b2 => y | z)                                                *)
(*                                                                           *)
(* Note also that these theorems are specialised for natural numbers. This   *)
(* prevents them from pulling the conditionals higher up the term than       *)
(* necessary prior to elimination.                                           *)
(*                                                                           *)
(* Also eliminates the predecessor function, PRE.                            *)
(*---------------------------------------------------------------------------*)

val COND_t = prim_mk_const {Name = "COND", Thy = "bool"}
fun TB c t =
  if Type.compare(type_of t, bool) = EQUAL then NO_CONV t
  else c t

val CASES_ELIM = let
  val p = mk_var("p", bool)
  val P = mk_var("P", bool --> bool)
in
  prove(mk_eq(mk_comb(P, p),
              mk_conj(mk_imp(p,mk_comb(P,T)), mk_imp(mk_neg p,mk_comb(P,F)))),
        ASM_CASES_TAC p THEN ASM_REWRITE_TAC[])
end

fun find_celim p t m = let
  fun isboolnum ty =
    Type.compare(ty, numSyntax.num) = EQUAL orelse
    Type.compare(ty, bool) = EQUAL
  fun doit t =
    if is_cond t andalso isboolnum (type_of t) then
      UNBETA_CONV (t |> rator |> rator |> rand) THENC
      REWR_CONV CASES_ELIM THENC
      BINOP_CONV (RAND_CONV BETA_CONV) THENC
      PURE_REWRITE_CONV [COND_CLAUSES]
    else NO_CONV
in
  case dest_term t of
      COMB(f,x) => find_celim (p o RATOR_CONV) f ORELSEC
                   find_celim (p o RAND_CONV) x ORELSEC doit t
    | LAMB(_, body) => if type_of body = bool then
                         p (ABS_CONV (find_celim I body))
                       else NO_CONV
    | _ => NO_CONV
end m

fun ELIM_COND1 t = find_celim I t t

fun op_of_app tm = op_of_app (rator tm) handle _ => tm
val SUB_AND_COND_ELIM_CONV =
   TOP_DEPTH_CONV
     (NUM_COND_RATOR_CONV ORELSEC
      (fn tm => if same_const (op_of_app tm) COND_t then failwith "fail"
                else NUM_COND_RAND_CONV tm) ORELSEC
      TB COND_ABS_CONV) THENC
   REPEATC ELIM_COND1 THENC
   NEW_SUB_ELIM_CONV


(*---------------------------------------------------------------------------*)
(* COND_ELIM_CONV : conv                                                     *)
(*                                                                           *)
(* This function eliminates all conditionals in a term that it can. If the   *)
(* term is a formula, only an abstraction can prevent the elimination, e.g.: *)
(*                                                                           *)
(*    COND_ELIM_CONV `(\m. (m = 0) => 0 | (m - 1)) (SUC n) = n` --->         *)
(*    |- ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n) =                         *)
(*       ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n)                           *)
(*                                                                           *)
(* Care has to be taken with the conditional lifting theorems because they   *)
(* can loop if they try to move a conditional past another conditional, e.g. *)
(*                                                                           *)
(*    b1 => x | (b2 => y | z)                                                *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val COND_ELIM_CONV =
   TOP_DEPTH_CONV
     (TB COND_RATOR_CONV ORELSEC
      (fn tm => if same_const (op_of_app tm) COND_t then failwith "fail"
                else TB COND_RAND_CONV tm) ORELSEC
      TB COND_ABS_CONV) THENC
   REPEATC ELIM_COND1

end
