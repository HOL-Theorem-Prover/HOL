structure OmegaSymbolic =
struct

(* This file implements the horrid part of the Omega test, when you have to
   do quantifier elimination symbolically, and without the benefit of being
   able to work outside the logic.

   In particular, this means that this part of the procedure has to work
   using the theorems in OmegaTheory.

   Input is a term of the form
       ?x. r1 /\ r2 /\ .. rn
   where each rn is in "Omega leaf normal form", i.e.
       0 <= c1 * v1 + c2 * v2 + c3 * v3 + c
*)

open HolKernel boolLib intSyntax QConv

local open OmegaTheory in end

infix THENC THEN ORELSEC |->
infixr --> ##

val lhand = rand o rator

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV
val TRY_CONV = TRY_QCONV

fun ERR f msg = HOL_ERR { origin_structure = "OmegaSymbolic",
                          origin_function = f,
                          message = msg}

(* ----------------------------------------------------------------------
    clause_to_evals v t

    where v is a variable, and t is a conjunction of <= leaves.
    Returns a theorem of the form
       t = (evalleft v lefts /\ evalright v rights) /\ extras
    where t is not free in extras.  Extras may be the term T.

   ---------------------------------------------------------------------- *)

val evaluppers = ``Omega$evalupper``;
val evallowers = ``Omega$evallower``;

fun clause_to_evals v tm = let
  val conjs = strip_conj tm
  fun partition (acc as (uppers, lowers, extras)) clist =
      case clist of
        [] => acc
      | c::cs => let
          val summands = strip_plus (rand c)
        in
          (* we can take rand of everything because last numeral will be of
             general form (& num) *)
          case total (pluck (fn t => rand t = v)) summands of
            NONE => partition (uppers, lowers, c::extras) cs
          | SOME (vc, others) => let
              val cf = lhand vc
              val other_t = list_mk_plus others
            in
              if is_negated cf then
                partition((rand cf,other_t)::uppers, lowers, extras) cs
              else
                partition(uppers, (cf,mk_negated other_t)::lowers, extras) cs
            end
        end
  val (uppers, lowers, extras) = partition ([],[],[]) conjs
  val int_int_ty = pairSyntax.mk_prod(numSyntax.num, int_ty)
  fun to_tm_list tlist =
      case tlist of
        [] => listSyntax.mk_nil int_int_ty
      | (c,t)::ts => listSyntax.mk_cons(pairSyntax.mk_pair(rand c,t),
                                        to_tm_list ts)
  val uppers_t = to_tm_list uppers
  val lowers_t = to_tm_list lowers
  val extras_t = if null extras then boolSyntax.T else list_mk_conj extras
in
  mk_conj(mk_conj(list_mk_comb(evaluppers, [v, uppers_t]),
                  list_mk_comb(evallowers, [v, lowers_t])),
          extras_t)
end






end (* struct *)