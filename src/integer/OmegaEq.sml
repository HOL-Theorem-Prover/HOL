structure OmegaEq :> OmegaEq =
struct

(* ----------------------------------------------------------------------
    Implementation of equality removal for the Omega Test.  Is not
    guaranteed to remove all equalities, but will do so if all of the
    variables in the equality terms are quantified over at this
    level.

    Input:

      a term of the form

        ?v1...vn. c1 /\ .. /\ cn

      where some or none of the ci may be (integer) equalities,
      involving variables that may or may not be among the quantified
      vs.  Each conjunct is either an equality or a <= term, and in
      either, the variables must all be collected up, on the right
      side of the relation symbol and further there must always be a
      numeral (possibly zero) added in on the right of the RHS.

    Output:

      a QConv "verdict", that is, a theorem equating the input to
      something better, or raising the exception QConv.UNCHANGED.

   ---------------------------------------------------------------------- *)

open HolKernel boolLib
open intSyntax CooperSyntax CooperMath QConv integerTheory

open OmegaTheory

infix THENC THEN THENL ORELSEC ##

val (Type, Term) = parse_from_grammars Omega_grammars

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV
val TRY_CONV = TRY_QCONV

fun EVERY_CONJ_CONV c tm =
    if is_conj tm then BINOP_CONV (EVERY_CONJ_CONV c) tm
    else c tm

fun ERR f msg = HOL_ERR { origin_structure = "OmegaEq",
                          origin_function = f,
                          message = msg}

fun lhand t = rand (rator t)

(* ----------------------------------------------------------------------
    rel_coeff v tm

    returns the coefficient (a term that is a numeral) of variable v in
    relational term tm.  A relational term is of the form
       0 <relop>  r1 + ... + rn
    where all of the li and ri are either numerals multiplied by variables,
    or bare numerals.  Further, it is assumed that any given variable
    occurs once.  Returns zero as the coefficient of a variable not
    present.
   ---------------------------------------------------------------------- *)

fun rel_coeff v tm = let
  fun recurse t = let
    val (l,r) = dest_plus t
  in
    if rand r = v then lhand r
    else recurse l
  end handle HOL_ERR _ => if rand t = v then lhand t else zero_tm
in
  recurse (lhand (rand tm))
end


(* ----------------------------------------------------------------------
    find_eliminable_equality vset acc conjunctions

    finds an equality that can be eliminated from the conjunctions.  This
    has to be done wrt a set of variables that have scope over the
    conjunctions.  Returns a new version of acc, the fields of which are
      (leastv, conj, rest)
    of types
      ((term * Arbint) option * term option * term list)

    leastv is the variable that has the least coefficient coupled with
    that least coefficient.  NONE if there is none such.

    conj is the conjunct in which leastv was found to be least.  Again,
    NONE if there is nothing eliminable.

    rest is the list of all the unsatisfactory conjuncts.

   ---------------------------------------------------------------------- *)

fun find_eliminable_equality vs (acc as (leastv, conj, rest)) cs = let
  fun ocons NONE xs = xs | ocons (SOME x) xs = x::xs
  fun doclause (acc as (leastv, conj, rest)) c k = let
    val fvs = FVL [lhand (rand c)] empty_tmset
    val i = HOLset.intersection(vs,fvs)
    fun check_mins (v, (leastv, changed)) = let
      open Arbint
      val v_coeff = abs (int_of_term (rel_coeff v c))
    in
      case leastv of
        NONE => (SOME(v,v_coeff), true)
      | SOME(v', min) => if v_coeff < min then (SOME (v,v_coeff), true)
                         else (leastv, changed)
    end
    (* if this clause isn't interesting, we need to continue (by calling k)
       but we also need to put c onto the list of things seen so far; here's
       the "unchanged" accumulated state that we'll pass to k in these
       cases *)
    val unchanged_acc = (leastv, conj, c::rest)
  in
    case HOLset.numItems i of
      0 => k unchanged_acc
    | 1 => let
        val v = hd (HOLset.listItems i)
      in
        if Arbint.abs (int_of_term (rel_coeff v c)) = Arbint.one then
          (SOME (v,Arbint.one), SOME c, ocons conj rest)
        else k unchanged_acc
      end
    | sz => let
      in
        case HOLset.foldl check_mins (leastv, false) i of
          (least', true) => k (least', SOME c, ocons conj rest)
        | (_, false) => k unchanged_acc
      end
  end
in
  case cs of
    [] => acc
  | (c::cs) => if not (is_eq c) then
                 find_eliminable_equality vs (leastv,conj,c::rest) cs
               else
                 doclause acc c
                 (fn acc' => find_eliminable_equality vs acc' cs)
end

(* ----------------------------------------------------------------------
    sum_to_sumc tm

    takes tm (a sum of the form t1 + .. + tn) and returns a theorem of
    the form
       |- tm = sumc cs vs
    where cs is a list of numeral coefficients, and vs a list of
    variables (except that one of the vs will actually be the numeral 1).
   ---------------------------------------------------------------------- *)

val sumc_t = ``sumc``
fun sum_to_sumc tm = let
  fun dest_m t = dest_mult t handle HOL_ERR _ => (t, one_tm)
  val (cs, vs) = ListPair.unzip (map dest_m (strip_plus tm))
  fun mk_list l = listSyntax.mk_list(l, int_ty)
  val (cs_t, vs_t) = (mk_list ## mk_list) (cs, vs)
  val sumc_t = list_mk_comb(sumc_t, [cs_t, vs_t])
in
  SYM ((REWRITE_CONV [INT_ADD_ASSOC, sumc_def, INT_MUL_RID] THENC
        REWR_CONV INT_ADD_RID) sumc_t)
end

(* ----------------------------------------------------------------------
    sumc_eliminate reducer tm

    Takes a term of the form
      sumc (MAP f cs) vs
    and turns it into a regular sum, assuming that the last v will actually
    be the integer 1, using the reducer parameter to evaluate each
    instance of the application of f to c.
   ---------------------------------------------------------------------- *)

local
  val sumc_singleton = prove(
    ``!f (c:int). sumc (MAP f [c]) [1] = f c``,
    REWRITE_TAC [INT_ADD_RID, sumc_def, listTheory.MAP, INT_MUL_RID]);
  val sumc_nonsingle = prove(
    ``!f cs (c:int) v vs. sumc (MAP f (c::cs)) (v::vs) =
                    f c * v + sumc (MAP f cs) vs``,
    REWRITE_TAC [sumc_def, listTheory.MAP])
in
fun sumc_eliminate reducer tm = let
  fun recurse tm =
      if listSyntax.is_nil (rand (rand tm)) then
        (REWR_CONV sumc_singleton THENC reducer) tm
      else
        (REWR_CONV sumc_nonsingle THENC LAND_CONV (LAND_CONV reducer) THENC
         RAND_CONV recurse) tm
in
  if listSyntax.is_nil (rand tm) then
    REWRITE_CONV [listTheory.MAP, sumc_def]
  else
    recurse
end tm
end (* local *)


(* ----------------------------------------------------------------------
    eliminate_equality v tm

    Takes a variable v, and an equality tm, of the general form
        0 = r1 + .. + rn
    and returns a theorem which is an equation of the general form

      |- tm = ?s. (v = ....) /\ tm

   ---------------------------------------------------------------------- *)

val SYM_EQ_NEG = GSYM INT_EQ_NEG
fun eliminate_equality v tm = let
  open OmegaMath
  val instantiate_eqremoval =
      C MP TRUTH o CONV_RULE (LAND_CONV REDUCE_CONV) o
      PART_MATCH (lhand o rand) equality_removal
  val rhs_th = MOVE_VCOEFF_TO_FRONT v (rand tm)
  val cv_t = lhand (rand (concl rhs_th))
  val dealwith_negative_coefficient =
      if is_negated (lhand cv_t) then
        REWR_CONV SYM_EQ_NEG THENC
        FORK_CONV (REWR_CONV INT_NEG_0, NEG_SUM_CONV)
      else ALL_CONV
in
  RAND_CONV (K rhs_th) THENC dealwith_negative_coefficient THENC
  RAND_CONV (RAND_CONV sum_to_sumc) THENC instantiate_eqremoval THENC
  BINDER_CONV
     (LAND_CONV (* new equality conjunct *)
       (RAND_CONV (* rhs of equality *)
          (LAND_CONV (LAND_CONV REDUCE_CONV) THENC
           RAND_CONV (* sumc term *)
             (LAND_CONV (LAND_CONV (* first arg of MAP *)
                           (BINDER_CONV (RAND_CONV REDUCE_CONV THENC
                                         REWRITE_CONV [modhat_def] THENC
                                         REDUCE_CONV))) THENC
              sumc_eliminate (BETA_CONV THENC REDUCE_CONV)) THENC
             REWRITE_CONV [INT_MUL_LZERO, INT_ADD_RID, INT_ADD_ASSOC,
                           INT_ADD_LID])) THENC
     RAND_CONV (* old equality conjunct *)
       (REWRITE_CONV [sumc_def] THENC
        REWRITE_CONV [INT_MUL_RID, INT_ADD_ASSOC] THENC
        RAND_CONV (REWR_CONV INT_ADD_RID)))
end tm

val eliminate_equality =
    fn x => Profile.profile "eliminate_eq" (eliminate_equality x)




(* ----------------------------------------------------------------------
    OmegaEq : term -> thm

    Put all of the above together
   ---------------------------------------------------------------------- *)

fun push_exvar_to_bot v tm = let
  val (bv, body) = dest_exists tm
in
  if bv = v then (SWAP_VARS_CONV THENC
                  BINDER_CONV (push_exvar_to_bot v) ORELSEC
                  ALL_CONV)
  else (BINDER_CONV (push_exvar_to_bot v))
end tm

val S_AND_G_MULT = Profile.profile "S_AND_G_MULT" OmegaMath.S_AND_G_MULT
val EX_REFL = EQT_INTRO (SPEC_ALL EXISTS_REFL)
fun OmegaEq t = let
  val (exvars, body) = strip_exists t
  val exv_set = HOLset.addList(empty_tmset, exvars)
  val gcd_check = Profile.profile "gcd_check" OmegaMath.gcd_check
  val _ = length exvars > 0 orelse
          raise ERR "OmegaEq" "Term not existentially quantified"
  val conjns = strip_conj body
  val (vwithleast, conj, rest) =
      Profile.profile "find_elim_eq"
      (find_eliminable_equality exv_set (NONE, NONE, [])) conjns
  val _ = isSome vwithleast orelse raise UNCHANGED
  val (to_elim, elimc) = valOf vwithleast
  val c = valOf conj
  val newrhs = if null rest then c else mk_conj(c, list_mk_conj rest)
  val reordered_thm =
      EQT_ELIM (AC_CONV(CONJ_ASSOC, CONJ_COMM) (mk_eq(body, newrhs)))
  val bring_veq_to_top = let
    val (rCONV, finisher) = if null rest then (I, ALL_CONV)
                            else (LAND_CONV,
                                  LEFT_AND_EXISTS_CONV THENC
                                  BINDER_CONV (REWR_CONV (GSYM CONJ_ASSOC)))
  in
      if elimc = Arbint.one then
        rCONV (phase2_CONV to_elim THENC LAND_CONV (REWR_CONV INT_MUL_LID))
      else
        rCONV (eliminate_equality to_elim) THENC finisher
  end
  fun ifVarsRemain c t = if is_exists t then c t else ALL_QCONV t
  val (absify, unwinder) =
      if null rest andalso elimc = Arbint.one then
        (ALL_CONV, REWR_CONV EX_REFL)
      else (STRIP_QUANT_CONV (RAND_CONV (mk_abs_CONV to_elim)),
            REWR_CONV UNWIND_THM2 THENC BETA_CONV)
in
  STRIP_QUANT_CONV (K reordered_thm THENC bring_veq_to_top THENC absify) THENC
  push_exvar_to_bot to_elim THENC LAST_EXISTS_CONV unwinder THENC
  STRIP_QUANT_CONV
    (EVERY_CONJ_CONV (TRY_CONV (RAND_CONV S_AND_G_MULT THENC gcd_check))) THENC
  REWRITE_CONV [EXISTS_SIMP] THENC
  ifVarsRemain OmegaEq
end t

(* some test terms:

time OmegaEq   ``?x y z. 0 <= 2 * x + ~3 * y + 5 * z + 10 /\
                         (0  = 3 * x + 4 * y + ~7 * z + 3)``;

time OmegaEq   ``?i j. 0 <= 1 * i + 0 /\ 0 <= 1 * j + 0 /\
                       (0 = 3 * i + 5 * j + ~1 * n + 0)``;

time OmegaEq   ``?i j. (0 = 3 * i + 5 * j + ~1 * n + 0)``;

time OmegaEq   ``?i j. (0 = 3 * i + 6 * j + ~1 * n + 0)``;


*)


end;
