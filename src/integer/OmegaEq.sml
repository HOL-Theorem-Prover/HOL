structure OmegaEq =
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
      either, the variables must all be collected up, though they
      don't need to be on any particular side of the relation symbol.

    Output:

      a QConv "verdict", that is, a theorem equating the input to
      something better, or raising the exception QConv.UNCHANGED.

   ---------------------------------------------------------------------- *)

open HolKernel boolLib
open intSyntax CooperSyntax CooperMath QConv

infix THENC ORELSEC ##

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2

fun ERR f msg = HOL_ERR { origin_structure = "OmegaEq",
                          origin_function = f,
                          message = msg}

fun myfind f [] = NONE
  | myfind f (x::xs) =
    case f x of
      NONE => myfind f xs
    | x => x
fun lhand t = rand (rator t)

fun rel_coeff v tm = let
  val (l,r) = (strip_plus ## strip_plus) (dest_eq tm)
  fun ok t = if is_mult t andalso rand t = v then SOME (lhand t) else NONE
in
  case myfind ok l of
    SOME c => c
  | _ => case myfind ok r of
           SOME c => c
         | NONE => zero_tm
end


fun find_eliminable_equality vs (acc as (elimp, leastv, conj, rest)) cs = let
  fun ocons NONE xs = xs | ocons (SOME x) xs = x::xs
  fun doclause (acc as (elimp, leastv, conj, rest)) c = let
    val fvs = FVL [c] empty_tmset
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
  in
    case HOLset.numItems i of
      0 => (false, acc)
    | 1 => let
        val v = hd (HOLset.listItems i)
      in
        if Arbint.abs (int_of_term (rel_coeff v c)) = Arbint.one then
          (true, (true, SOME (v,Arbint.one), SOME c, ocons conj rest))
        else (false, acc)
      end
    | sz => let
      in
        case HOLset.foldl check_mins (leastv, false) i of
          (least', true) => (false, (true, least', SOME c, ocons conj rest))
        | (_, false) => (false, acc)
      end
  end
in
  case cs of
    [] => acc
  | (c::cs) => if not (is_eq c) then
                 find_eliminable_equality vs (elimp,leastv,conj,c::rest) cs
               else
                 case doclause acc c of
                   (true, (_,lv,c,r')) => (true,lv,c,cs @ r')
                 | (_, acc') => find_eliminable_equality vs acc' cs
end




(* ----------------------------------------------------------------------
    OmegaEq : term -> thm

    Put all of the above together
   ---------------------------------------------------------------------- *)

fun OmegaEq t = let
  val (exvars, body) = strip_exists t
  val exv_set = HOLset.addList(empty_tmset, exvars)
  val _ = length exvars > 0 orelse
          raise ERR "OmegaEq" "Term not existentially quantified"
  val conjns = strip_conj body
  val (elimp, vwithleast, conj, rest) =
      find_eliminable_equality exv_set (false, NONE, NONE, conjns) conjns
  val _ = elimp orelse raise UNCHANGED
  val to_elim = valOf vwithleast
  val c = valOf conj
in
  AC_CONV(CONJ_ASSOC, CONJ_COMM) (mk_eq(body, mk_conj(c, list_mk_conj rest)))
end


end;
