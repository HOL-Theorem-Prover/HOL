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


(* ----------------------------------------------------------------------
    The bound as an ordinal.

    The BNF's own bound is a set; the cardinality argument wants an
    ordinal whose predecessors match it.  One exists because the set
    embeds in a whole type, and the choice term names it without
    introducing a constant.
   ---------------------------------------------------------------------- *)

fun boundOrdinal bnf =
    let val B = #bnd bnf
        val bty = #1 (dom_rng (type_of B))
        val leUNIV = ISPEC B CARDLEQ_UNIV
        val leSUM = INST_TYPE [alpha |-> numSyntax.num, beta |-> bty]
                              bnfPrelimsTheory.UNIV_CARD_LE_ADDL
        val le = MATCH_MP cardinalTheory.cardleq_TRANS (CONJ leUNIV leSUM)
        val th = SELECT_RULE (MATCH_MP ordinalBasicTheory.cardeq_ordinals_exist
                                       le)
        val bd = rand (rand (rator (concl th)))
    in
      {bd = bd, cardeq = th,
       omega_le = MATCH_MP cardeq_preds_omega (CONJ (#bndINFINITE bnf) th)}
    end

fun setBoundThm bnf bd ty =
    let val cardeq = #cardeq (boundOrdinal bnf)
        val x = mk_var("x", functorAt bnf ty)
        val bounded = SPEC x (INST_TYPE [alpha |-> ty] (#bndthm bnf))
    in
      GEN x (MATCH_MP cardeq_preds_bound (CONJ cardeq bounded))
    end


(* ----------------------------------------------------------------------
    The cardinality bound.

    MINSET_CARDLEQ wants the laws at three instances: the carrier, the
    carrier with a point added, and the ordinals bounding F's sets.
   ---------------------------------------------------------------------- *)

fun nontrivialThm bnf ty =
    let val (w,th) = case #nontrivial bnf of
                         SOME p => p
                       | NONE => raise ERR "nontrivialThm"
                                       "the functor has no non-trivial set"
        val th = INST_TYPE [alpha |-> ty] th
        val w = Term.inst [alpha |-> ty] w
        val x = mk_var("x", functorAt bnf ty)
    in
      EXISTS (mk_exists (x, subst [w |-> x] (concl th)), w) th
    end

fun minsetBound bnf ty =
    let val {bd, omega_le, ...} = boundOrdinal bnf
        val ordty = type_of bd
        val abty = sumSyntax.mk_sum (ty, bool)
        val laws = LIST_CONJ [MapIdThm bnf ty,
                              MapCongThm bnf (ty,ty),
                              NaturalThm bnf (ty,abty),
                              MapCompThm bnf (ty,abty,ty),
                              MapIdThm bnf abty,
                              MapCongThm bnf (abty,abty),
                              NaturalThm bnf (abty,ordty),
                              NaturalThm bnf (ordty,abty),
                              MapCompThm bnf (abty,ordty,abty),
                              NaturalThm bnf (ordty,ordty),
                              nontrivialThm bnf ordty,
                              omega_le,
                              setBoundThm bnf bd ty,
                              setBoundThm bnf bd abty]
        val th = MATCH_MP MINSET_CARDLEQ laws
        (* and from the bounding set to the whole type it sits in *)
        val s = mk_var("s", functorAt bnf ty --> ty)
        val th = SPEC s th
        val bset = rand (concl th)
        val carrier = #1 (dom_rng (type_of bset))
        val th = GEN s (MATCH_MP cardinalTheory.cardleq_TRANS
                                 (CONJ th (ISPEC bset CARDLEQ_UNIV)))
    in
      {carrier = carrier, thm = th}
    end


(* ----------------------------------------------------------------------
    The initial algebra.

    The construction lives over three types: the bounded carrier that
    the cardinality argument produces, the product of all algebras over
    it, and F applied to that product.  Everything else is a matter of
    instantiating INITIALITY0 and LAMBEK, which is what the parameterised
    statement of those theorems is for.
   ---------------------------------------------------------------------- *)

type initial_algebra = {
  carrier : hol_type, prodty : hol_type, target : hol_type,
  alg : term, cons : term,
  bij : thm, init : thm, inhabited : thm, induction : thm,
  isALG : thm
}

fun witnessThm bnf ty =
    let val (w,th) = case #wit bnf of
                         SOME p => p
                       | NONE => raise ERR "witnessThm"
                                       "the functor has no empty witness"
        val th = INST_TYPE [alpha |-> ty] th
        val w = Term.inst [alpha |-> ty] w
        val x = mk_var("w", functorAt bnf ty)
    in
      EXISTS (mk_exists (x, subst [w |-> x] (concl th)), w) th
    end

fun initialAlgebra bnf =
    let val target = alpha
        val {carrier, thm = bound} = minsetBound bnf target
        (* the product's index type, and the product's carrier *)
        val idxty = pairSyntax.mk_prod (carrier --> bool,
                                        functorAt bnf carrier --> carrier)
        val prodty = idxty --> carrier
        fun mp p = mapOp bnf p
        fun st ty = setOp bnf ty
        val laws =
            CONJ (MapCongThm bnf (prodty,target))
                 (LIST_CONJ [NaturalThm bnf (prodty,carrier),
                             NaturalThm bnf (prodty,prodty),
                             MapIdThm bnf prodty,
                             MapCompThm bnf (prodty,prodty,carrier),
                             NaturalThm bnf (prodty,target),
                             MapCompThm bnf (prodty,carrier,target),
                             MapCompThm bnf (prodty,target,target),
                             NaturalThm bnf (carrier,target),
                             NaturalThm bnf (target,carrier),
                             MapCompThm bnf (target,carrier,target),
                             MapIdThm bnf target,
                             MapCongThm bnf (target,target),
                             bound])
        val init = MATCH_MP INITIALITY0 laws
        (* the carrier and the constructor, read back off the theorem *)
        val fpty = functorAt bnf prodty
        val algty = pairSyntax.mk_prod (prodty --> bool, fpty --> prodty)
        val (alg, cons) =
            pairSyntax.dest_pair
              (find_term (fn t => pairSyntax.is_pair t andalso
                                  Type.compare (type_of t, algty) = EQUAL)
                         (concl init))
        val ALG_tm = rator (rator (concl IALG_ALG))
        val algALG =
            PART_MATCH I IALG_ALG
              (list_mk_icomb (ALG_tm, [st prodty,
                                       pairSyntax.mk_pair (alg,cons)]))
        val lambek =
            MATCH_MP LAMBEK
              (LIST_CONJ [MapCongThm bnf (prodty,prodty),
                          MapIdThm bnf prodty,
                          NaturalThm bnf (fpty,prodty),
                          MapCompThm bnf (prodty,fpty,prodty),
                          MapCongThm bnf (prodty,fpty),
                          NaturalThm bnf (prodty,fpty),
                          algALG,
                          INST_TYPE [alpha |-> fpty] init,
                          INST_TYPE [alpha |-> prodty] init])
        (* IALG_INHABITED and IALG_ind mention the algebra's map and set
           parameters only inside IALG, so they are pinned by matching
           that subterm against the algebra just built *)
        val IALG_tm = repeat rator alg
        fun atAlg th =
            let val nargs = length (#2 (strip_comb alg))
                val pat = find_term
                            (fn t => let val (f,args) = strip_comb t
                                     in
                                       same_const f IALG_tm andalso
                                       length args = nargs
                                     end handle HOL_ERR _ => false)
                            (concl th)
            in
              INST_TY_TERM (match_term pat alg) th
            end
        val inhabited = atAlg (MATCH_MP IALG_INHABITED (witnessThm bnf prodty))
    in
      {carrier = carrier, prodty = prodty, target = target,
       alg = alg, cons = cons,
       bij = lambek, init = init, inhabited = inhabited, isALG = algALG,
       induction = atAlg IALG_ind}
    end


(* ----------------------------------------------------------------------
    The datatype.

    rich_new_type states its facts about the carrier as a predicate and
    NEWTYPE_INITIALITY states them as membership, so they are converted
    on the way in.
   ---------------------------------------------------------------------- *)

fun defineFixpoint {tyname, ABS, REP} bnf =
    let val ia = initialAlgebra bnf
        val prodty = #prodty ia
        val itype = newtypeTools.rich_new_type
                      {tyname = tyname, exthm = #inhabited ia,
                       ABS = ABS, REP = REP}
        val newty = #newty itype
        (* the rewrite has to be aimed: its pattern is a bare
           application, so a DEPTH_CONV would rewrite the result again
           and never stop *)
        val inIntro = REWR_CONV (GSYM pred_setTheory.SPECIFICATION)
        val termP_IN = GEN_ALL (CONV_RULE inIntro (#termP_term_REP itype))
        val repabs_IN =
            CONV_RULE (STRIP_QUANT_CONV (LAND_CONV inIntro))
                      (#repabs_pseudo_id itype)
        val abs = #term_ABS_t itype and rep = #term_REP_t itype
        val fnty = functorAt bnf newty
        (* the constructor is NCONS at this instance; defining it that
           way rather than as the unfolded lambda is what lets the
           recursion theorem be folded back to mention it *)
        val NCONS_tm = repeat rator (lhs (concl (SPEC_ALL NCONS_def)))
        val consbody = list_mk_icomb (NCONS_tm,
                                      [mapOp bnf (newty,prodty), #cons ia,
                                       rep, abs])
        val cons_def =
            new_definition (tyname ^ "_CONS_def",
                            mk_eq (mk_var (tyname ^ "_CONS",
                                           fnty --> newty), consbody))
        val cons = lhs (concl cons_def)
        val laws =
            LIST_CONJ [MapCompThm bnf (prodty,newty,prodty),
                       MapIdThm bnf prodty,
                       MapCongThm bnf (prodty,prodty),
                       NaturalThm bnf (newty,prodty),
                       NaturalThm bnf (prodty,newty),
                       MapCompThm bnf (newty,prodty,alpha),
                       MapCompThm bnf (prodty,newty,alpha),
                       MapCongThm bnf (prodty,alpha),
                       #absrep_id itype,
                       repabs_IN,
                       termP_IN,
                       #isALG ia,
                       #init ia]
        val recursion =
            CONV_RULE (DEPTH_CONV BETA_CONV)
                      (REWRITE_RULE [GSYM cons_def]
                                    (MATCH_MP NEWTYPE_RECURSION laws))
    in
      {newty = newty, cons = cons, cons_def = cons_def, recursion = recursion}
    end

end
