structure OmegaShell :> OmegaShell =
struct

open HolKernel boolLib intSyntax integerTheory

(* Takes a closed Presburger arithmetic term over the integers and
   tries to decide it using the Omega procedure.

   Terms that are Presburger over the naturals or have free variables,
   or both, are dealt with by the procedures in IntDP_Munge.

   This code makes the decision as to whether or not OmegaSimple can be
   used, and also performs the necessary normalisation of the input.
*)

infix THENC THEN ORELSEC |->
infixr --> ##

val lhand = rand o rator

val REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV bool_rewrites

fun ERR f msg = HOL_ERR { origin_structure = "OmegaShell",
                          origin_function = f,
                          message = msg}

(* ----------------------------------------------------------------------
    check_for_early_equalities t

    t is of the form ?v1..vn. T, and T has been purged of all negations
    and connectives other than /\ and \/.
    Before throwing ourselves into DNF-ication, we check to see if T
    can be seen as
          (c * vi = ....) /\ P vi
    If so, the OmegaEq simplification might usefully be applied.  Moreover
    we may save on having to do it multiple times in lots of different
    disjuncts if we do it now rather than later.
   ---------------------------------------------------------------------- *)

val check_for_early_equalities = OmegaMath.OmegaEq




fun IS_NOT_EXISTS_CONV tm = if is_exists tm then NO_CONV tm else ALL_CONV tm

(* ----------------------------------------------------------------------
    normalise t

    Normalises t, where t is of the form
        ?v1..vn. T
    and T is a closed term involving usual boolean operators and leaf terms
    that are relational operators over integers.  T is put into DNF, and
    the leaf terms are all normalised as well.
   ---------------------------------------------------------------------- *)

val normalise = let
  fun push_exs tm = let
    val vs = map (#1 o dest_var) (#1 (strip_exists tm))
  in
    CooperSyntax.push_in_exists THENC EVERY_DISJ_CONV (RENAME_VARS_CONV vs)
  end tm
  open OmegaMath
in
  STRIP_QUANT_CONV (Canon.NNF_CONV leaf_normalise false THENC
                    REPEATC (CHANGED_CONV CSimp.csimp THENC
                             REWRITE_CONV [])) THENC
  push_exs THENC
  EVERY_DISJ_CONV
    (check_for_early_equalities THENC
     (IS_NOT_EXISTS_CONV ORELSEC
      (STRIP_QUANT_CONV Canon.PROP_DNF_CONV THENC
       push_exs THENC
       EVERY_DISJ_CONV (TRY_CONV eliminate_negative_divides) THENC
       EVERY_DISJ_CONV (TRY_CONV eliminate_positive_divides))))
end

(* ----------------------------------------------------------------------
    simple t

    Takes a closed term of form ?v1..vn. T and decides it using the
    OmegaSimple method.
   ---------------------------------------------------------------------- *)

fun callsimple t =
    (OmegaSimple.simple_CONV ORELSEC
     (OmegaSymbolic.eliminate_an_existential THENC
      EVERY_DISJ_CONV callsimple)) t

val simple =
  TRY_CONV (STRIP_QUANT_CONV OmegaMath.cond_removal) THENC
  normalise THENC
  EVERY_DISJ_CONV (REWRITE_CONV [] THENC
                   (IS_NOT_EXISTS_CONV ORELSEC
                    (OmegaMath.OmegaEq THENC
                     (IS_NOT_EXISTS_CONV ORELSEC callsimple))))


(* decide strategy is given a goal term which has already been prenexed *)

fun decide_strategy tm = let
  open CooperSyntax OmegaMath
in
  case goal_qtype tm of
    qsUNIV => PRENEX_CONV THENC flip_foralls THENC
              RAND_CONV simple THENC CooperMath.REDUCE_CONV
  | qsEXISTS => PRENEX_CONV THENC simple THENC CooperMath.REDUCE_CONV
  | EITHER => CooperMath.REDUCE_CONV
  | NEITHER => OmegaSymbolic.findelim_deep_existential THENC
               REWRITE_CONV [] THENC decide_strategy
end tm


(* in order to do prenexing, we need to remove quantifiers that hide
   within conditional guards.  There's a lot of faff happening here:
   why not just do away with conditional expressions from the outset?

   Two reasons:
  * rewriting the wrong way will double the term size because one
    rewrite is right for CNF and the other is right for DNF.
  * conditional expressions that repeat the same guard should have
    the case-split done on the guard just once. *)
fun remove_qs_from_guards tm = let
  val (g, t, e) = dest_cond tm
in
  if CooperSyntax.goal_qtype g <> CooperSyntax.EITHER then
    REWR_CONV COND_EXPAND tm
  else NO_CONV tm
end

val decide_closed_presburger =
    TOP_DEPTH_CONV remove_qs_from_guards THENC
    DEPTH_CONV EXISTS_UNIQUE_CONV THENC
    REWRITE_CONV [IMP_DISJ_THM] THENC
    decide_strategy

(* utility function for assessing how big a term will result when something
   is converted to DNF naively :
fun dnf_size t =
    if is_disj t then
      (op+ o (dnf_size ## dnf_size) o dest_disj) t
    else if is_conj t then
      (op* o (dnf_size ## dnf_size) o dest_conj) t
    else 1

*)


end (* struct *)
