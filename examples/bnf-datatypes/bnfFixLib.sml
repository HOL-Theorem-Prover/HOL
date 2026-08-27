structure bnfFixLib :> bnfFixLib =
struct

open HolKernel boolLib
open bnfInitialTheory

val ERR = mk_HOL_ERR "bnfFixLib"

(* ----------------------------------------------------------------------
    The parameters
   ---------------------------------------------------------------------- *)

fun functorTy (bnf : bnfLib.derived_bnf) = #1 (dom_rng (type_of (#set bnf)))
fun functorAt bnf ty = type_subst [alpha |-> ty] (functorTy bnf)

fun setOp bnf ty = Term.inst [alpha |-> ty] (#set bnf)
fun mapOp bnf (ty1,ty2) =
    let val f = mk_var("f", ty1 --> ty2)
    in
      mk_abs(f, #mkmap bnf f)
    end

(* ----------------------------------------------------------------------
    Each law is stated in bnfInitialTheory as a predicate over the
    parameters.  Proving an instance is: instantiate the stored law to
    the instance wanted (by matching, so that neither the law's type
    variables nor its variable names have to be known here), massage it
    into the predicate's right-hand side, and EQ_MP through the
    definition.
   ---------------------------------------------------------------------- *)

(* |- P args, given |- P args <=> body and a proof of body.  The
   definition is instantiated by ISPECL, and its right-hand side beta
   reduced, because the map parameter is a lambda. *)
fun byDefn defn args bodyth =
    let val eq = CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV))
                           (ISPECL args defn)
    in
      EQ_MP (SYM eq) bodyth
    end

(* I and o at a given instance, by matching rather than by assuming
   which of their type variables is which *)
fun Ify ty =
    let val t = combinSyntax.I_tm
    in Term.inst (match_type (type_of t) (ty --> ty)) t end
val mk_o = combinSyntax.mk_o

fun MapIdThm bnf ty =
    let val idmap = #mkmap bnf (Ify ty)
        val th = PART_MATCH lhs (#mapID bnf) idmap  (* |- map I = I *)
        val x = mk_var("x", functorAt bnf ty)
        val th = TRANS (AP_THM th x) (ISPEC x combinTheory.I_THM)
    in
      byDefn MapId_def [mapOp bnf (ty,ty)] (GEN x th)
    end

fun MapCompThm bnf (t1,t2,t3) =
    let val f = mk_var("f", t1 --> t2)
        val g = mk_var("g", t2 --> t3)
        (* the stored law is point-free: map g o map f = map (g o f) *)
        val target = mk_o (#mkmap bnf g, #mkmap bnf f)
        val th = PART_MATCH lhs (#mapO bnf) target
        val x = mk_var("x", functorAt bnf t1)
        val th = TRANS (SYM (ISPECL [#mkmap bnf g, #mkmap bnf f, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
    in
      byDefn MapComp_def [mapOp bnf (t1,t2), mapOp bnf (t2,t3),
                          mapOp bnf (t1,t3)]
             (GENL [f,g,x] th)
    end

fun NaturalThm bnf (t1,t2) =
    let val f = mk_var("f", t1 --> t2)
        val target = mk_o (setOp bnf t2, #mkmap bnf f)
        (* |- set2 o map f = IMAGE f o set1 *)
        val th = PART_MATCH lhs (#mapIMAGE bnf) target
        val x = mk_var("x", functorAt bnf t1)
        val rhs0 = rhs (concl th)
        val imgf = rand (rator rhs0) and set1 = rand rhs0
        val th = TRANS (SYM (ISPECL [setOp bnf t2, #mkmap bnf f, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
        val th = TRANS th (ISPECL [imgf, set1, x] combinTheory.o_THM)
    in
      byDefn Natural_def [mapOp bnf (t1,t2), setOp bnf t1, setOp bnf t2]
             (GENL [f,x] th)
    end

fun MapCongThm bnf (t1,t2) =
    let val f = mk_var("f", t1 --> t2)
        val x = mk_var("x", functorAt bnf t1)
        val target = mk_comb (#mkmap bnf f, x)
        (* |- (!a. a IN set x ==> f a = g a) ==> map f x = map g x; the
           law's own g is whatever variable is left over *)
        val th = PART_MATCH (lhs o snd o dest_imp) (#mapCONG bnf) target
        val g = case filter (fn v => not (aconv v f) andalso not (aconv v x))
                            (free_vars (concl th))
                 of [v] => v
                  | _ => raise ERR "MapCongThm" "cannot identify the law's g"
    in
      byDefn MapCong_def [mapOp bnf (t1,t2), setOp bnf t1] (GENL [f,g,x] th)
    end

end
