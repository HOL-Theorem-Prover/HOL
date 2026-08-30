structure bnfFixLib :> bnfFixLib =
struct

open HolKernel boolLib
open bnfInitialTheory bnfFixBNFTheory bnfMutualTheory

val ERR = mk_HOL_ERR "bnfFixLib"

(* ----------------------------------------------------------------------
    The parameters.

    The fixed point is taken over the functor's *first* argument; any
    other argument it was derived in is a parameter, which the
    construction carries along untouched and the new type keeps.  So
    everything here works with the map in the first argument alone —
    the n-ary map with I in the parameters' positions — and with the
    first argument's set function.

    Deriving the functor in its parameters as well is what lets the
    fixed point be registered as a functor in them afterwards; a caller
    that only wants the type can declare just the one argument, and
    every term below is then what the one-argument derivation gives.
   ---------------------------------------------------------------------- *)

(* I and o at a given instance, by matching rather than by assuming
   which of their type variables is which *)
fun Ify ty =
    let val t = combinSyntax.I_tm
    in Term.inst (match_type (type_of t) (ty --> ty)) t end
val mk_o = combinSyntax.mk_o

(* the recursive argument, and the parameters *)
fun recTy (bnf : bnfLib.derived_bnfn) = hd (#lives bnf)
fun paramTys (bnf : bnfLib.derived_bnfn) = tl (#lives bnf)

fun functorTy bnf = #1 (dom_rng (type_of (hd (#sets bnf))))

(* the functor at a whole tuple of arguments: the recursive one at ty and
   the parameters at ptys.  The construction only ever moves the
   recursive argument, but registering the fixed point moves the
   parameters too. *)
fun atArgs bnf (ty,ptys) =
    Term.inst (ListPair.mapEq (fn (l,t) => l |-> t) (#lives bnf, ty::ptys))
fun typeAtArgs bnf (ty,ptys) =
    type_subst (ListPair.mapEq (fn (l,t) => l |-> t) (#lives bnf, ty::ptys))

fun functorAtArgs bnf tys = typeAtArgs bnf tys (functorTy bnf)
fun setAtArgs bnf i tys = atArgs bnf tys (List.nth (#sets bnf, i))

fun functorAt bnf ty = functorAtArgs bnf (ty, paramTys bnf)
fun setOp bnf ty = setAtArgs bnf 0 (ty, paramTys bnf)

(* F's map with a tuple of functions on the parameters baked in, as a
   term and as the operator the laws are stated over.  The construction
   itself always carries the parameters along by I. *)
fun bmapT bnf f fs = #mkmap bnf (f :: fs)
fun bmapOp bnf (ty1,ty2) fs =
    let val f = mk_var("f", ty1 --> ty2)
    in
      mk_abs(f, bmapT bnf f fs)
    end

fun paramIs bnf = List.map Ify (paramTys bnf)
fun mkmapA bnf f = bmapT bnf f (paramIs bnf)
fun mapOp bnf (ty1,ty2) = bmapOp bnf (ty1,ty2) (paramIs bnf)

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

fun MapIdThm bnf ty =
    let val idmap = mkmapA bnf (Ify ty)
        val th = PART_MATCH lhs (#mapID bnf) idmap  (* |- map I .. I = I *)
        val x = mk_var("x", functorAt bnf ty)
        val th = TRANS (AP_THM th x) (ISPEC x combinTheory.I_THM)
    in
      byDefn MapId_def [mapOp bnf (ty,ty)] (GEN x th)
    end

(* the composite of two tuples of functions on the parameters, in the form
   the stored law's right-hand side ends up in: composing with I is not
   written as a composition there *)
fun normo t = rhs (concl (QCONV (PURE_REWRITE_CONV [combinTheory.I_o_ID]) t))
fun composeParams (fs,gs) = ListPair.mapEq (normo o mk_o) (gs,fs)

fun bMapCompThm bnf (t1,t2,t3) (fs,gs) =
    let val f = mk_var("f", t1 --> t2)
        val g = mk_var("g", t2 --> t3)
        (* the stored law is point-free: map g o map f = map (g o f) *)
        val target = mk_o (bmapT bnf g gs, bmapT bnf f fs)
        val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                   (PART_MATCH lhs (#mapO bnf) target)
        val x = mk_var("x", functorAtArgs bnf (t1, List.map (#1 o dom_rng o
                                                             type_of) fs))
        val th = TRANS (SYM (ISPECL [bmapT bnf g gs, bmapT bnf f fs, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
    in
      byDefn MapComp_def [bmapOp bnf (t1,t2) fs, bmapOp bnf (t2,t3) gs,
                          bmapOp bnf (t1,t3) (composeParams (fs,gs))]
             (GENL [f,g,x] th)
    end

fun MapCompThm bnf (t1,t2,t3) = bMapCompThm bnf (t1,t2,t3)
                                             (paramIs bnf, paramIs bnf)

(* naturality for argument i of the bundle: the source and target set
   functions are F's i-th, at the two tuples the bundle maps between.  For
   i = 0 this is Natural, for a parameter it is NaturalP, whose statement
   also quantifies over the function the recursive argument gets — which
   the parameter's atoms don't depend on. *)
(* |- setᵢ (map f fs x) = IMAGE fᵢ (setᵢ x), with the function the
   recursive argument gets and the element left free *)
fun bnatEq bnf i (t1,t2) fs =
    let val srcs = List.map (#1 o dom_rng o type_of) fs
        val tgts = List.map (#2 o dom_rng o type_of) fs
        val f = mk_var("f", t1 --> t2)
        val set1 = setAtArgs bnf i (t1,srcs)
        val set2 = setAtArgs bnf i (t2,tgts)
        val target = mk_o (set2, bmapT bnf f fs)
        (* the stored law is point-free: setᵢ o map f .. = IMAGE fᵢ o setᵢ *)
        val th = PART_MATCH lhs (List.nth (#mapIMAGE bnf, i)) target
        val x = mk_var("x", functorAtArgs bnf (t1,srcs))
        val imgf = rand (rator (rhs (concl th)))
        val th = TRANS (SYM (ISPECL [set2, bmapT bnf f fs, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
    in
      {f = f, x = x, img = imgf, src = set1, tgt = set2,
       thm = TRANS th (ISPECL [imgf, set1, x] combinTheory.o_THM)}
    end

fun bNaturalThm bnf i (t1,t2) fs =
    let val {f,x,img,src,tgt,thm} = bnatEq bnf i (t1,t2) fs
    in
      if i = 0 then
        byDefn Natural_def [bmapOp bnf (t1,t2) fs, src, tgt] (GENL [f,x] thm)
      else
        byDefn NaturalP_def
               [bmapOp bnf (t1,t2) fs, src, tgt, rand img]
               (GENL [f,x] thm)
    end

fun NaturalThm bnf (t1,t2) = bNaturalThm bnf 0 (t1,t2) (paramIs bnf)

(* |- !a. a IN s ==> t a = t a, the hypothesis a congruence makes about
   an argument whose two functions are the same *)
fun trivial_cong c =
    let val (a, body) = dest_forall c
        val (mem, eq) = dest_imp body
    in
      GEN a (DISCH mem (REFL (lhs eq)))
    end

fun trivialp c =
    let val (l,r) = dest_eq (#2 (dest_imp (#2 (dest_forall c))))
    in aconv l r end

(* Congruence between two bundles: the stored law instantiated so that
   the parameters get the functions the two bundles use there, with the
   hypotheses about a parameter both bundles treat the same discharged.
   Returns the two functions the recursive argument gets, the element
   variable, and

     |- <the hypotheses that are left> ==> map f us x = map g vs x

   Matching the conclusion's left-hand side fixes each of the first
   bundle's functions; the second's are read off the hypotheses, whose
   shape says which is which. *)
fun bcong bnf (t1,t2) (us,vs) =
    let val srcs = List.map (#1 o dom_rng o type_of) us
        val f = mk_var("f", t1 --> t2)
        val x = mk_var("x", functorAtArgs bnf (t1,srcs))
        val target = mk_comb (bmapT bnf f us, x)
        val th0 = PART_MATCH (lhs o snd o dest_imp) (#mapCONG bnf) target
        (* the law's two families of functions, read off its hypotheses:
           the conjunct for argument i says fᵢ a = gᵢ a *)
        fun families th =
            let val conjs = strip_conj (#1 (dest_imp (concl th)))
                fun eqOf c = #2 (dest_imp (#2 (dest_forall c)))
            in
              (List.map (rator o lhs o eqOf) conjs,
               List.map (rator o rhs o eqOf) conjs)
            end
        (* An argument the functor uses nowhere is left unconstrained by
           the match, its target type included, so both families have to
           be pinned to what the two bundles use there. *)
        fun pairs th =
            let val (fsL,gsL) = families th
            in
              ListPair.zipEq (tl fsL, us) @ ListPair.zipEq (tl gsL, vs)
            end
        val th1 =
            INST_TYPE (List.concat
                         (List.map (fn (l,v) => Type.match_type (type_of l)
                                                                (type_of v))
                                   (pairs th0)))
                      th0
        val th = INST (List.mapPartial
                         (fn (l,v) => if is_var l andalso not (aconv l v) then
                                        SOME (l |-> v)
                                      else NONE)
                         (pairs th1))
                      th1
        val gs = #2 (families th)
        val conjs = strip_conj (#1 (dest_imp (concl th)))
        val hyp = list_mk_conj (List.filter (not o trivialp) conjs)
        val parts = CONJUNCTS (ASSUME hyp)
        (* the assumed conjuncts are the non-trivial ones, in order *)
        fun facts ([], _) = []
          | facts (c::cs, ps) =
            if trivialp c then trivial_cong c :: facts (cs, ps)
            else hd ps :: facts (cs, tl ps)
    in
      (f, hd gs, x, DISCH hyp (MP th (LIST_CONJ (facts (conjs, parts)))))
    end

(* |- MapCong (bmapOp bnf (t1,t2) fs) (F's set for the recursive
   argument): the parameters are treated the same on both sides *)
fun bMapCongThm bnf (t1,t2) fs =
    let val (f,g,x,th) = bcong bnf (t1,t2) (fs,fs)
        val srcs = List.map (#1 o dom_rng o type_of) fs
    in
      byDefn MapCong_def [bmapOp bnf (t1,t2) fs, setAtArgs bnf 0 (t1,srcs)]
             (GENL [f,g,x] th)
    end

fun MapCongThm bnf (t1,t2) = bMapCongThm bnf (t1,t2) (paramIs bnf)

(* |- MapCongP mp1 mp2 stn sbᵢ uᵢ vᵢ, for two bundles that differ in the
   i-th parameter alone *)
fun bMapCongPThm bnf i (t1,t2) (us,vs) =
    let val (f,g,x,th) = bcong bnf (t1,t2) (us,vs)
        val srcs = List.map (#1 o dom_rng o type_of) us
    in
      byDefn MapCongP_def
             [bmapOp bnf (t1,t2) us, bmapOp bnf (t1,t2) vs,
              setAtArgs bnf 0 (t1,srcs), setAtArgs bnf (i + 1) (t1,srcs),
              List.nth (us,i), List.nth (vs,i)]
             (GENL [f,g,x] th)
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

(* the caller passes the ordinal's theorem: deriving it again here would
   repeat the whole choice-term construction, once per instance *)
fun setBoundThm bnf cardeq ty =
    let val x = mk_var("x", functorAt bnf ty)
        val bounded = SPEC x (INST_TYPE [recTy bnf |-> ty]
                                        (hd (#bndthms bnf)))
    in
      GEN x (MATCH_MP cardeq_preds_bound (CONJ cardeq bounded))
    end


(* ----------------------------------------------------------------------
    The cardinality bound.

    MINSET_CARDLEQ wants the laws at three instances: the carrier, the
    carrier with a point added, and the ordinals bounding F's sets.
   ---------------------------------------------------------------------- *)

(* |- ?x. st x <> {}, from the element bnfLib's inhabitation fact names *)
fun nontrivialThm bnf ty =
    let val (w,th) = case bnfLib.groundNonempty bnf 0 of
                         SOME p => p
                       | NONE => raise ERR "nontrivialThm"
                                       "the functor has no non-trivial set"
        val th = INST_TYPE [recTy bnf |-> ty] th
        val w = Term.inst [recTy bnf |-> ty] w
        val x = mk_var("x", functorAt bnf ty)
    in
      EXISTS (mk_exists (x, subst [w |-> x] (concl th)), w) th
    end

fun minsetBound bnf ty =
    let val {bd, omega_le, cardeq} = boundOrdinal bnf
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
                              setBoundThm bnf cardeq ty,
                              setBoundThm bnf cardeq abty]
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
    let val (w,th) = case bnfLib.groundEmpty bnf 0 of
                         SOME p => p
                       | NONE => raise ERR "witnessThm"
                                       "the functor has no empty witness"
        val th = INST_TYPE [recTy bnf |-> ty] th
        val w = Term.inst [recTy bnf |-> ty] w
        val x = mk_var("w", functorAt bnf ty)
    in
      EXISTS (mk_exists (x, subst [w |-> x] (concl th)), w) th
    end

fun initialAlgebra bnf =
    let (* the type variable initiality is stated at, so that INST_TYPE
           gives it at any carrier.  The functor's own argument will do:
           it is not free in anything the construction has built yet. *)
        val target = recTy bnf
        val {carrier, thm = bound} = minsetBound bnf target
        (* the product's index type, and the product's carrier *)
        val idxty = pairSyntax.mk_prod (carrier --> bool,
                                        functorAt bnf carrier --> carrier)
        val prodty = idxty --> carrier
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
                          INST_TYPE [target |-> fpty] init,
                          INST_TYPE [target |-> prodty] init])
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

type fixpoint = {newty : hol_type, cons : term, cons_def : thm,
                 recursion : thm, prim_recursion : thm, set_induction : thm}

fun defineFixpoint {tyname, ABS, REP} bnf : fixpoint =
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
                       MapCompThm bnf (newty,prodty,#target ia),
                       MapCompThm bnf (prodty,newty,#target ia),
                       MapCongThm bnf (prodty,#target ia),
                       #absrep_id itype,
                       repabs_IN,
                       termP_IN,
                       #isALG ia,
                       #init ia]
        (* the map operator is a lambda, and PRIM_REC_OF_ITER's
           hypotheses are stated over it, so the beta reduction that
           makes the theorem readable has to come last *)
        val recursion0 = REWRITE_RULE [GSYM cons_def]
                                      (MATCH_MP NEWTYPE_RECURSION laws)
        val recursion = CONV_RULE (DEPTH_CONV BETA_CONV) recursion0
        (* the target type variable, read off t's type *)
        val cty = #2 (dom_rng (type_of (#1 (dest_forall (concl recursion)))))
        val prodq = pairSyntax.mk_prod (newty, cty)
        val prim =
            CONV_RULE (DEPTH_CONV BETA_CONV)
              (MATCH_MP PRIM_REC_OF_ITER
                 (LIST_CONJ [MapCompThm bnf (newty,prodq,newty),
                             MapCompThm bnf (newty,prodq,cty),
                             MapIdThm bnf newty,
                             INST_TYPE [cty |-> prodq] recursion0,
                             INST_TYPE [cty |-> newty] recursion0]))
        (* induction with the hypothesis "for every sub-term in the
           set", which is the form that survives a nested recursion *)
        val set_induction =
            CONV_RULE (DEPTH_CONV BETA_CONV)
              (REWRITE_RULE [GSYM cons_def]
                 (MATCH_MP NEWTYPE_IND
                    (LIST_CONJ [MapCompThm bnf (prodty,newty,prodty),
                                MapIdThm bnf prodty,
                                MapCongThm bnf (prodty,prodty),
                                NaturalThm bnf (prodty,newty),
                                #absrep_id itype,
                                REWRITE_RULE [IALG_def] repabs_IN,
                                REWRITE_RULE [IALG_def] termP_IN])))
    in
      {newty = newty, cons = cons, cons_def = cons_def,
       recursion = recursion, prim_recursion = prim,
       set_induction = set_induction}
    end


(* ----------------------------------------------------------------------
    The datatype that does not recurse.

    An enumeration, a record, any sum of products the type itself does
    not occur in: the functor is constant in the recursive argument, and
    μα. C is C.  The construction above does not apply — its cardinality
    argument needs the recursive argument to be somewhere non-empty —
    and does not need to: a type in bijection with the functor satisfies
    the same three principles, by bnfInitialTheory's COPY_ theorems.

    So this returns a fixpoint like defineFixpoint's, and everything
    downstream — the constructors, the axiom, the case constants, the
    TypeBase entry — is the same code.  The new type's own functoriality
    is not defineFixpoint's business either: it is the functor's own,
    conjugated by the bijection, which is what transportBNF does.
   ---------------------------------------------------------------------- *)

(* a type variable named 'c, or the first 'cᵢ that is free *)
fun copyTyvar avoid =
    let fun go v k =
            if Lib.mem v avoid then
              go (mk_vartype ("'c" ^ Int.toString k)) (k + 1)
            else v
    in go (mk_vartype "'c") 1 end

type copy = {fixpoint : fixpoint, abs : term, rep : term,
             absrep : thm, repabs : thm}

fun defineCopy {tyname, ABS, REP} bnf : copy =
    let
      val ft = functorTy bnf
      val _ = not (Lib.mem (recTy bnf) (Type.type_vars ft)) orelse
              raise ERR "defineCopy"
                    "the functor uses the recursive argument"
      (* the new type, in bijection with the functor: the predicate is
         trivially true, so its two facts are the bijection's *)
      val x = mk_var ("x", ft)
      val P = mk_abs (x, boolSyntax.T)
      val arb = mk_arb ft
      val ex = EXISTS (mk_exists (x, mk_comb (P, x)), arb)
                      (EQT_ELIM (BETA_CONV (mk_comb (P, arb))))
      val itype = newtypeTools.rich_new_type
                    {tyname = tyname, exthm = ex, ABS = ABS, REP = REP}
      val newty = #newty itype
      val abst = #term_ABS_t itype
      val rept = #term_REP_t itype
      val absrep = GEN_ALL (#absrep_id itype)
      val repabs =
          let val th = #repabs_pseudo_id itype
              val (r, eq) = dest_forall (concl th)
              val triv = EQT_ELIM (BETA_CONV (#1 (dest_imp eq)))
          in
            GEN r (MP (SPEC r th) triv)
          end
      (* the same two facts as compositions, which is the form a
         transport of the functor's structure across them takes *)
      fun compEq (f, g, th) =
          let val x = mk_var ("x", #1 (dom_rng (type_of g)))
          in
            EXT (GEN x (TRANS (TRANS (ISPECL [f,g,x] combinTheory.o_THM)
                                     (SPEC x th))
                              (SYM (ISPEC x combinTheory.I_THM))))
          end
      val cons_def =
          new_definition (tyname ^ "_CONS_def",
                          mk_eq (mk_var (tyname ^ "_CONS", ft --> newty),
                                 abst))
      val cons = lhs (concl cons_def)
      val cty = copyTyvar (Type.type_vars ft)
      (* the map does nothing: the function for the recursive argument
         has nowhere to act, so what is left is the identity map *)
      val mapfact =
          let val h = mk_var ("h", newty --> cty)
              val af = mk_var ("af", ft)
              val beta = BETA_CONV (mk_comb (mapOp bnf (newty,cty), h))
              val idth = PART_MATCH lhs (#mapID bnf) (rhs (concl beta))
          in
            GENL [h, af] (TRANS (AP_THM (TRANS beta idth) af)
                                (ISPEC af combinTheory.I_THM))
          end
      (* and there are no sub-terms.  The set function is a composite
         built over the argument's own, which is the empty one; reducing
         it is the only way to see that. *)
      val setfact =
          let val af = mk_var ("af", ft)
              val th = QCONV (simpLib.SIMP_CONV (BasicProvers.srw_ss())
                                [combinTheory.S_DEF, combinTheory.o_DEF,
                                 combinTheory.K_DEF,
                                 pairTheory.setFST_thm, pairTheory.setSND_thm,
                                 bnfPrelimsTheory.BIMG_K0,
                                 bnfPrelimsTheory.BIMG_EQUAL])
                             (mk_comb (setOp bnf newty, af))
          in
            if pred_setSyntax.is_empty (rhs (concl th)) then GEN af th
            else raise ERR "defineCopy"
                       ("the functor's sub-term set did not reduce to the " ^
                        "empty set")
          end
      val facts = LIST_CONJ [absrep, repabs, mapfact]
      fun copy th =
          CONV_RULE (DEPTH_CONV BETA_CONV)
                    (REWRITE_RULE [GSYM cons_def] (MATCH_MP th facts))
    in
      {fixpoint =
         {newty = newty, cons = cons, cons_def = cons_def,
          recursion = copy COPY_RECURSION,
          prim_recursion = copy COPY_PRIM_REC,
          set_induction =
            CONV_RULE (DEPTH_CONV BETA_CONV)
              (REWRITE_RULE [GSYM cons_def]
                 (MATCH_MP COPY_IND (CONJ absrep setfact)))},
       abs = abst, rep = rept,
       absrep = compEq (abst, rept, absrep),
       repabs = compEq (rept, abst, repabs)}
    end


(* ----------------------------------------------------------------------
    Splitting the single constructor along the functor's sum-of-products
    structure, and stating the datatype's axiom the way the rest of HOL
    expects it.
   ---------------------------------------------------------------------- *)

fun factorsOf ty =
    if Type.compare (ty, oneSyntax.one_ty) = EQUAL then []
    else pairSyntax.strip_prod ty

(* the i-th summand's value, injected into the whole sum *)
fun mkInj [_] 0 v = v
  | mkInj (_::tys) 0 v = sumSyntax.mk_inl (v, sumSyntax.list_mk_sum tys)
  | mkInj (ty::tys) i v = sumSyntax.mk_inr (mkInj tys (i-1) v, ty)
  | mkInj [] _ _ = raise ERR "mkInj" "index out of range"

(* and back out again, which is what lets a branch read the mapped value
   without dispatching on it a second time *)
fun mkOut [_] 0 v = v
  | mkOut (_::_) 0 v = sumSyntax.mk_outl v
  | mkOut (_::tys) i v = mkOut tys (i-1) (sumSyntax.mk_outr v)
  | mkOut [] _ _ = raise ERR "mkOut" "index out of range"

fun projs 0 _ = []
  | projs 1 v = [v]
  | projs k v = pairSyntax.mk_fst v :: projs (k-1) (pairSyntax.mk_snd v)

val sum_CASE_tm = prim_mk_const {Thy = "sum", Name = "sum_CASE"}

fun mkCaseTerm [_] [(x,b)] scrut = subst [x |-> scrut] b
  | mkCaseTerm (_::tys) ((x,b)::bs) scrut =
      let val rv = mk_var ("r", sumSyntax.list_mk_sum tys)
      in
        list_mk_icomb (sum_CASE_tm,
                       [scrut, mk_abs (x,b),
                        mk_abs (rv, mkCaseTerm tys bs rv)])
      end
  | mkCaseTerm _ _ _ = raise ERR "mkCaseTerm" "malformed"

type constructors = {
  constructors : term list, defs : thm list, axiom : thm,
  legacy_axiom : thm, existential_axiom : thm, induction : thm option,
  set_induction : thm, distinct : thm option list, one_one : thm option list
}

fun defineConstructors names bnf fix : constructors =
    let val newty = #newty fix
        val cons = #cons fix
        val prim = #prim_recursion fix
        val cty = #2 (dom_rng (#2 (dom_rng
                        (type_of (#1 (dest_forall (concl prim)))))))
        val summands = sumSyntax.strip_sum (functorTy bnf)
        val n = length summands
        val _ = length names = n orelse
                raise ERR "defineConstructors"
                      ("the functor has " ^ Int.toString n ^ " summands")
        val rawFactors = map factorsOf summands
        fun atNew ty = type_subst [recTy bnf |-> newty] ty
        fun atC ty = type_subst [recTy bnf |-> cty] ty
        val newSummands = map atNew summands
        val cSummands = map atC summands
        (* a factor is recursive if the argument occurs in it at all,
           not only when it *is* the argument: a nested occurrence like
           ‘'a mylist’ hands the function mylistMAP h of it, which is the
           whole point of building the datatype over a BNF *)
        val isRec = map (fn ty => Lib.mem (recTy bnf) (type_vars ty))
        (* one constructor per summand *)
        fun mkOne (i, (nm, facs)) =
            let val argtys = map atNew facs
                val args = List.tabulate
                             (length facs,
                              fn j => mk_var ("a" ^ Int.toString j,
                                              List.nth (argtys, j)))
                val tup = if null args then oneSyntax.one_tm
                          else pairSyntax.list_mk_pair args
                val cvar = mk_var (nm, List.foldr (op -->) newty argtys)
                (* a record's constructor is named with a dot in it, so
                   the definition's binding name is not the constant's *)
                val bnm = String.translate (fn #"." => "_" | c => str c) nm
                val def = new_definition
                            (bnm ^ "_def",
                             mk_eq (list_mk_comb (cvar, args),
                                    mk_comb (cons, mkInj newSummands i tup)))
                val ctm = #1 (strip_comb (lhs (concl (SPEC_ALL def))))
                val recs = isRec facs
                val nonrecargs = map #2 (filter (not o #1) (zip recs args))
                val recargs = map #2 (filter #1 (zip recs args))
                (* what the function is handed for a recursive factor:
                   h x when the factor is the argument itself, and
                   Gmap h x when it occurs under a G *)
                val recmapped = map (atC o #2) (filter #1 (zip recs facs))
                val ftype = List.foldr (op -->) cty
                              (map type_of nonrecargs @ map type_of recargs @
                               recmapped)
                val fvar = mk_var ("f" ^ Int.toString i, ftype)
            in
              {name = nm, def = def, cons = ctm, args = args, recs = recs,
               nonrecargs = nonrecargs, recargs = recargs,
               recmapped = recmapped, fvar = fvar}
            end
        val cs = List.tabulate
                   (n, fn i => mkOne (i, (List.nth (names, i),
                                          List.nth (rawFactors, i))))
        (* the branch bodies: the constructor's own arguments come from
           af, the recursive results from the matching part of v *)
        val afv = mk_var ("af", functorAt bnf newty)
        val vv = mk_var ("v", functorAt bnf cty)
        fun branch (i, c) =
            let val xv = mk_var ("x", List.nth (newSummands, i))
                val yv = mkOut cSummands i vv
                val k = length (#args c)
                val xps = projs k xv
                val yps = projs k yv
                val recres = map #2 (filter #1 (zip (#recs c) yps))
                val xnonrec = map #2 (filter (not o #1) (zip (#recs c) xps))
                val xrec = map #2 (filter #1 (zip (#recs c) xps))
            in
              (xv, list_mk_comb (#fvar c, xnonrec @ xrec @ recres))
            end
        val tterm = mk_abs (afv, mk_abs (vv,
                      mkCaseTerm newSummands
                                 (List.tabulate (n, fn i =>
                                     branch (i, List.nth (cs,i))))
                                 afv))
        (* Rather than instantiating the equation at each constructor,
           expand the quantifier over the functor's shape: that gives
           both directions at once, so the axiom keeps its uniqueness,
           which is what an induction principle is derived from. *)
        val spec = CONV_RULE (DEPTH_CONV BETA_CONV) (SPEC tterm prim)
        val (hv, body) = dest_abs (rand (concl spec))
        val eqth = REWRITE_RULE (map (GSYM o #def) cs)
                     (simpLib.SIMP_CONV boolSimps.bool_ss
                        [sumTheory.FORALL_SUM, pairTheory.FORALL_PROD,
                         oneTheory.FORALL_ONE, sumTheory.SUM_MAP_def,
                         sumTheory.sum_case_def, sumTheory.OUTL,
                         sumTheory.OUTR, pairTheory.PAIR_MAP,
                         pairTheory.FST, pairTheory.SND, combinTheory.I_THM]
                        body)
        (* expanding the quantifier names the constructors' arguments
           after the product projections it went through; rename them to
           what a datatype axiom is normally written with *)
        fun renameOne c =
            if null (#args c) then ALL_CONV
            else RENAME_VARS_CONV (map (fst o dest_var) (#args c))
        fun renameConj [] = ALL_CONV
          | renameConj [c] = renameOne c
          | renameConj (c::cs) = LAND_CONV (renameOne c) THENC
                                 RAND_CONV (renameConj cs)
        val axiom =
            CONV_RULE (STRIP_QUANT_CONV
                         (RAND_CONV (ABS_CONV (renameConj cs))))
              (GENL (map #fvar cs)
                    (CONV_RULE (RAND_CONV (ABS_CONV (REWR_CONV (GEN hv eqth))))
                               spec))
        (* Prim_rec's derivations are older than the argument order
           TypeBase settled on: mk_fn abstracts the recursive results
           before the constructor's own arguments.  Permuting each f is
           one SPEC, so state the axiom the modern way and hand the
           legacy order to the derivations. *)
        val legacy =
            let fun perm c =
                    let val args = #nonrecargs c @ #recargs c
                        fun rvar j = mk_var ("r" ^ Int.toString j,
                                             List.nth (#recmapped c, j))
                        val rs = List.tabulate (length (#recmapped c), rvar)
                        val g = mk_var (fst (dest_var (#fvar c)) ^ "'",
                                        List.foldr (op -->) cty
                                          (#recmapped c @ map type_of args))
                    in
                      (g, list_mk_abs (args @ rs, list_mk_comb (g, rs @ args)))
                    end
                val ps = map perm cs
            in
              GENL (map #1 ps)
                   (CONV_RULE (DEPTH_CONV BETA_CONV)
                              (SPECL (map #2 ps) axiom))
            end
        (* Prim_rec's derivation counts recursive arguments by their
           type, so it cannot see a recursive result that arrived under
           another type operator.  For a nested recursion the natural
           induction principle is the set-based one anyway — the
           hypothesis is "for every sub-term in the set" — so this is
           left as NONE rather than forced. *)
        (* the set-based induction, split along the constructors: the
           hypothesis becomes "for every sub-term in the set", which is
           the form a nested recursion keeps *)
        val set_induction =
            REWRITE_RULE (map (GSYM o #def) cs)
              (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV
                 (PURE_REWRITE_CONV [bnfPrelimsTheory.BIMG_EQUAL,
                                     combinTheory.I_o_ID] THENC
                  simpLib.SIMP_CONV (BasicProvers.srw_ss())
                    [sumTheory.FORALL_SUM, pairTheory.FORALL_PROD,
                     oneTheory.FORALL_ONE, combinTheory.S_DEF,
                     combinTheory.o_DEF, combinTheory.K_DEF,
                     pairTheory.setFST_thm, pairTheory.setSND_thm])))
                 (#set_induction fix))
        (* whether this is a nested recursion is known structurally: a
           nested factor's mapped type is not the answer type.  Deciding
           it by catching an exception out of Prim_rec would swallow
           genuine failures there as well. *)
        val nested = List.exists
                       (List.exists (fn ty => Type.compare (ty,cty) <> EQUAL)
                                    o #recmapped) cs
        val induction = if nested then NONE
                        else SOME (Prim_rec.prove_induction_thm legacy)
        (* the derivations of distinctness and injectivity want the plain
           existential, which is also the form TypeBase stores *)
        val fvars = map #fvar cs
        val existential = GENL fvars (EXISTENCE (SPECL fvars axiom))
    in
      {constructors = map #cons cs, defs = map #def cs, axiom = axiom,
       legacy_axiom = legacy, induction = induction,
       set_induction = set_induction,
       existential_axiom = existential,
       distinct = Prim_rec.prove_constructors_distinct existential,
       one_one = Prim_rec.prove_constructors_one_one existential}
    end


(* ----------------------------------------------------------------------
    The new type as a functor.

    μα. F(α, β⃗) is a functor in the β⃗, and everything the BNF database
    stores about it comes out of the recursion principle and the laws F
    was derived with.  The map and the set functions are *defined* here,
    as instances of the recursion principle:

      MAP f⃗ (cons af) = cons (Fmap (MAP f⃗) f⃗ af)
      SETᵢ (cons af)  = Fsetᵢ af UNION BIGUNION (IMAGE SETᵢ (Fset₀ af))

    and each law is then one instance of the corresponding theorem in
    bnfFixBNFTheory, whose hypotheses are these equations, F's own laws at
    the instances involved, and the new type's induction principle.

    Nothing is registered: the result is a value, which a caller adds to
    a database with bnfBase.insert, or names and records.  An
    intermediate type — the scaffolding a mutual recursion goes through —
    should not end up in a theory's exports.
   ---------------------------------------------------------------------- *)

fun idxOf what xs x =
    let fun go _ [] = raise ERR what "no such argument"
          | go i (y::ys) = if y = x then i else go (i + 1) ys
    in go 0 xs end

fun upto k = List.tabulate (k, fn i => i)

(* n type variables named 'pre1 .. 'pren, avoiding those in use *)
fun freshTys pre n avoid =
    let fun go i acc k =
            if k = 0 then List.rev acc
            else
              let val v = mk_vartype (pre ^ Int.toString i)
              in
                if Lib.mem v avoid then go (i + 1) acc k
                else go (i + 1) (v::acc) (k - 1)
              end
    in
      go 1 [] n
    end

(* ∃M. ∀f⃗. P f⃗ (M f⃗), from ∀f⃗. ∃h. P f⃗ h *)
fun skolemN 0 = ALL_CONV
  | skolemN k = funpow (k - 1) BINDER_CONV SKOLEM_CONV THENC skolemN (k - 1)

type fixpoint_bnf = {
  key : KernelSig.kernelname, info : thm bnfBase_dtype.info,
  map_thm : thm, set_thms : thm list, relator_def : thm
}

fun fixpointBNF bnf (fix : fixpoint) : fixpoint_bnf =
    let
      val newty = #newty fix
      val consN = #cons fix
      val {Thy,Tyop,Args} = dest_thy_type newty
      val av = recTy bnf
      val params = paramTys bnf
      (* the parameters, in the order the new type's operator takes them:
         the map constant's arguments have to line up with the type's,
         and the derivation's own order need not *)
      val largs = List.filter (fn a => Lib.mem a params) Args
      val n = length largs
      val _ = n > 0 orelse
              raise ERR "fixpointBNF"
                    "the functor was derived in its recursive argument alone"
      (* A parameter the type doesn't have — because the functor uses it
         nowhere — still needs an entry in the map's argument list, and
         which one cannot matter: the map ignores it. *)
      fun byParams filler xs =
          List.map (fn p => case Lib.assoc1 p (ListPair.zipEq (largs, xs)) of
                                SOME (_,x) => x
                              | NONE => filler p)
                   params
      val toParams = byParams Ify            (* one function per argument *)
      val toParamTys = byParams (fn p => p)  (* one type *)
      val toParamArgs = byParams mk_arb      (* or one value *)
      (* F's set function for the new type's i-th argument *)
      fun psetIdx i = 1 + idxOf "fixpointBNF" params (List.nth (largs, i))

      (* the answer type variable of the recursion principle *)
      val rec_thm = #recursion fix
      val cty = #2 (dom_rng (type_of (#1 (dest_forall (concl rec_thm)))))

      (* the type variables the map maps into, and the ones mapO's second
         stage lands in *)
      val avoid = cty :: type_vars newty
      val tvs = freshTys "'c" n avoid
      val uvs = freshTys "'d" n (avoid @ tvs)
      fun tyTheta tys = ListPair.mapEq (fn (l,t) => l |-> t) (largs, tys)
      fun atLargs tys ty = type_subst (tyTheta tys) ty
      fun instLargs tys tm = Term.inst (tyTheta tys) tm
      fun instTyLargs tys th = INST_TYPE (tyTheta tys) th
      val mty = atLargs tvs newty
      val uty = atLargs uvs newty
      val consM = instLargs tvs consN

      fun numbered nm tys =
          List.tabulate (length tys,
                         fn i => mk_var(if n = 1 then nm
                                        else nm ^ Int.toString (i + 1),
                                        List.nth (tys, i)))
      val fs = numbered "f" (ListPair.mapEq (op -->) (largs, tvs))
      val gs = numbered "g" (ListPair.mapEq (op -->) (largs, tvs))
      val fs' = numbered "f" (ListPair.mapEq (op -->) (tvs, uvs))

      (* ------------------------------------------------------------
          the map
         ------------------------------------------------------------ *)

      (* the iterator at the target type, putting the constructor back
         together with the parameters' functions applied *)
      val mapB = bmapT bnf (Ify mty) (toParams fs)
      val v = mk_var("v", functorAtArgs bnf (mty, params))
      val t = mk_abs(v, mk_comb(consM, mk_comb(mapB, v)))
      val recM = INST_TYPE [cty |-> mty] rec_thm
      val ex0 = CONV_RULE (DEPTH_CONV BETA_CONV) (EXISTENCE (SPEC t recM))
      (* mapping the recursive argument and then the parameters is one
         map of both, which is F's own mapO *)
      val bridge =
          let val h = mk_var("h", newty --> mty)
              val target = mk_o (mapB, mkmapA bnf h)
              val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                         (PART_MATCH lhs (#mapO bnf) target)
              val af = mk_var("af", functorAtArgs bnf (newty, params))
          in
            TRANS (SYM (ISPECL [mapB, mkmapA bnf h, af] combinTheory.o_THM))
                  (AP_THM th af)
          end
      val mapname = Tyop ^ "MAP"
      val map_thm =
          new_specification
            (mapname ^ "_def", [mapname],
             CONV_RULE (skolemN n) (GENL fs (PURE_REWRITE_RULE [bridge] ex0)))
      val MAPtm = repeat rator (lhs (#2 (strip_forall (concl map_thm))))
      (* the map constant carries both instances in its type, so applying
         it needs them supplied: the functions say what they are *)
      fun mapTheta hs =
          let val srcs = List.map (#1 o dom_rng o type_of) hs
              val tgts = List.map (#2 o dom_rng o type_of) hs
          in
            tyTheta srcs @ ListPair.mapEq (fn (t,u) => t |-> u) (tvs, tgts)
          end
      fun mapApp hs = list_mk_comb (Term.inst (mapTheta hs) MAPtm, hs)

      (* ------------------------------------------------------------
          the set functions
         ------------------------------------------------------------ *)

      fun defSet i =
          let
            val setty = List.nth (largs, i) --> bool
            val j = psetIdx i
            val sb = setAtArgs bnf j (setty, params)
            val sa = setAtArgs bnf 0 (setty, params)
            val v = mk_var("v", functorAtArgs bnf (setty, params))
            val t = mk_abs(v, pred_setSyntax.mk_union
                                (mk_comb(sb,v),
                                 pred_setSyntax.mk_bigunion (mk_comb(sa,v))))
            val ex = CONV_RULE (DEPTH_CONV BETA_CONV)
                       (EXISTENCE (SPEC t (INST_TYPE [cty |-> setty] rec_thm)))
            (* a map of the recursive argument leaves the parameters'
               atoms alone and carries the sub-terms' along *)
            val pIs = paramIs bnf
            val cross = PURE_REWRITE_RULE [pred_setTheory.IMAGE_I]
                                  (#thm (bnatEq bnf j (newty,setty) pIs))
            val down = #thm (bnatEq bnf 0 (newty,setty) pIs)
            val nm = Tyop ^ "SET" ^
                     (if n = 1 then "" else Int.toString (i + 1))
          in
            new_specification (nm ^ "_def", [nm],
                               PURE_REWRITE_RULE [cross, down] ex)
          end
      val set_thms = List.map defSet (upto n)
      fun setTm i = repeat rator (lhs (#2 (strip_forall
                                            (concl (List.nth (set_thms, i))))))

      (* ------------------------------------------------------------
          the equations, as the parameters bnfFixBNFTheory is stated over
         ------------------------------------------------------------ *)

      fun stAt tys = setAtArgs bnf 0 (atLargs tys newty, toParamTys tys)
      fun sbAt tys i = setAtArgs bnf (psetIdx i) (atLargs tys newty,
                                                  toParamTys tys)
      fun fixindAt tys =
          byDefn FIXIND_def [instLargs tys consN, stAt tys]
                 (instTyLargs tys (#set_induction fix))
      fun fixsetAt tys i =
          byDefn FIXSET_def
                 [instLargs tys consN, stAt tys, sbAt tys i,
                  instLargs tys (setTm i)]
                 (instTyLargs tys (List.nth (set_thms, i)))
      (* the map at a tuple of functions: which tuple determines both
         instances, so the types come off the functions themselves *)
      fun fixmapAt hs =
          let val srcs = List.map (#1 o dom_rng o type_of) hs
              val tgts = List.map (#2 o dom_rng o type_of) hs
          in
            byDefn FIXMAP_def
                   [instLargs srcs consN, instLargs tgts consN,
                    bmapOp bnf (atLargs srcs newty, atLargs tgts newty)
                           (toParams hs),
                    mapApp hs]
                   (SPECL hs (INST_TYPE (mapTheta hs) map_thm))
          end

      (* ------------------------------------------------------------
          the laws
         ------------------------------------------------------------ *)

      val argIs = List.map Ify largs
      val x = mk_var("x", newty)

      val mapID =
          let val th = MATCH_MP FIXMAP_ID
                         (LIST_CONJ [MapCongThm bnf (newty,newty),
                                     MapIdThm bnf newty,
                                     fixindAt largs, fixmapAt argIs])
          in
            EXT (GEN x (TRANS (SPEC x th)
                              (SYM (ISPEC x combinTheory.I_THM))))
          end

      val mapO =
          let val fgs = composeParams (gs, fs')
              val th = MATCH_MP FIXMAP_O
                         (LIST_CONJ [bMapCongThm bnf (newty,uty)
                                                 (toParams fgs),
                                     bMapCompThm bnf (newty,mty,uty)
                                                 (toParams gs, toParams fs'),
                                     fixindAt largs,
                                     fixmapAt gs, fixmapAt fs', fixmapAt fgs])
              val M1 = mapApp gs
              val M2 = mapApp fs'
          in
            EXT (GEN x (TRANS (ISPECL [M2,M1,x] combinTheory.o_THM)
                              (SPEC x th)))
          end

      fun mapIMAGE i =
          GENL fs (MATCH_MP FIXSET_NATURAL
                     (LIST_CONJ [bNaturalThm bnf 0 (newty,mty) (toParams fs),
                                 bNaturalThm bnf (psetIdx i) (newty,mty)
                                             (toParams fs),
                                 fixindAt largs, fixmapAt fs,
                                 fixsetAt largs i, fixsetAt tvs i]))

      (* the congruence, one argument at a time: the two maps differ in
         the i-th function alone, and the whole law is the chain of those
         steps.  Each step's hypothesis is the law's i-th conjunct. *)
      val mapCONG =
          let
            fun mix j = List.tabulate (n, fn i => List.nth (if i < j then gs
                                                            else fs, i))
            fun step j =
                let val (us,vs) = (mix j, mix (j + 1))
                in
                  SPEC x (MATCH_MP FIXMAP_CONG
                            (LIST_CONJ [bMapCongPThm bnf (psetIdx j - 1)
                                          (newty,mty)
                                          (toParams us, toParams vs),
                                        fixindAt largs, fixsetAt largs j,
                                        fixmapAt us, fixmapAt vs]))
                end
            fun hypOf i =
                let val a = mk_var("a", List.nth (largs, i))
                in
                  mk_forall(a,
                    mk_imp(pred_setSyntax.mk_in(a, mk_comb(setTm i, x)),
                           mk_eq(mk_comb(List.nth (fs,i), a),
                                 mk_comb(List.nth (gs,i), a))))
                end
            val hyp = list_mk_conj (List.map hypOf (upto n))
            val parts = CONJUNCTS (ASSUME hyp)
            val steps = List.map (fn i => MP (step i) (List.nth (parts,i)))
                                 (upto n)
          in
            GENL (fs @ gs @ [x])
                 (DISCH hyp (List.foldl (fn (th,A) => TRANS A th)
                                        (hd steps) (tl steps)))
          end

      fun bndthm i =
          MATCH_MP FIXSET_CARDLEQ
            (LIST_CONJ [fixsetAt largs i, #bndINFINITE bnf,
                        INST_TYPE [av |-> newty]
                                  (List.nth (#bndthms bnf, psetIdx i)),
                        INST_TYPE [av |-> newty] (hd (#bndthms bnf)),
                        fixindAt largs])

      (* ------------------------------------------------------------
          witnesses and inhabitation
         ------------------------------------------------------------ *)

      val as_ = numbered "a" largs

      (* a base case for F is a base case for the new type, and the atoms
         it holds are exactly F's *)
      fun witOf (w,wth) =
          let
            val args = mk_arb newty :: toParamArgs as_
            val th = CONV_RULE (DEPTH_CONV BETA_CONV)
                       (SPECL args (INST_TYPE [av |-> newty] wth))
            val conjs = CONJUNCTS th
            val (A,_) = pred_setSyntax.dest_subset (concl (hd conjs))
            val empty = EQ_MP (ISPEC A pred_setTheory.SUBSET_EMPTY) (hd conjs)
            val body = mk_comb (consN, rand A)
            fun atArg i =
                let val eq = MATCH_MP FIXSET_EMPTY
                                      (CONJ (fixsetAt largs i) empty)
                in
                  PURE_ONCE_REWRITE_RULE [SYM eq]
                                         (List.nth (conjs, psetIdx i))
                end
            val restate = bnfLib.unbeta_at (LAND_CONV o RAND_CONV) as_ body
          in
            (list_mk_abs (as_, body),
             GENL as_ (LIST_CONJ (List.map (restate o atArg) (upto n))))
          end
      val fwits =
          List.filter
            (fn (_,th) =>
                pred_setSyntax.is_empty
                  (#2 (pred_setSyntax.dest_subset
                         (hd (strip_conj (#2 (strip_forall (concl th))))))))
            (#wits bnf)
      val _ = not (null fwits) orelse
              raise ERR "fixpointBNF" "the functor has no base case"

      fun inhOf i =
          case List.nth (#inhabits bnf, psetIdx i) of
              NONE => raise ERR "fixpointBNF"
                            ("argument " ^ Int.toString (i + 1) ^
                             " of the functor is never inhabited")
            | SOME (_,th) =>
              let
                val th = CONV_RULE (DEPTH_CONV BETA_CONV)
                           (SPEC_ALL (INST_TYPE [av |-> newty] th))
                val mem = MATCH_MP (MATCH_MP FIXSET_IN
                                             (fixsetAt largs i))
                                   th
                val v = #1 (pred_setSyntax.dest_in (concl mem))
                val body = rand (#2 (pred_setSyntax.dest_in (concl mem)))
              in
                (mk_abs (v, body),
                 GEN v (bnfLib.unbeta_at (RAND_CONV o RAND_CONV) [v] body mem))
              end

      (* ------------------------------------------------------------
          the relator, as the map and set functions determine it: two
          values are related when a value over the pairs maps onto both.
          The database stores one for every functor, though the
          derivation of composites doesn't consume it.
         ------------------------------------------------------------ *)

      val relator_def =
          let
            val prods = ListPair.mapEq pairSyntax.mk_prod (largs, tvs)
            val zty = atLargs prods newty
            val z = mk_var("z", zty)
            val y = mk_var("y", mty)
            val Rs = numbered "R" (ListPair.mapEq
                                     (fn (a,c) => a --> (c --> bool))
                                     (largs, tvs))
            (* FST and SND at the i-th pair type, pinned by matching
               their domain: their ranges are different halves of it *)
            fun proj tm i =
                Term.inst (match_type (#1 (dom_rng (type_of tm)))
                                      (List.nth (prods, i)))
                          tm
            fun projs tm = List.map (proj tm) (upto n)
            fun conjOf i =
                let val pv = mk_var("p", List.nth (prods, i))
                in
                  mk_forall(pv,
                    mk_imp(pred_setSyntax.mk_in
                             (pv, mk_comb(instLargs prods (setTm i), z)),
                           list_mk_comb(List.nth (Rs,i),
                                        [pairSyntax.mk_fst pv,
                                         pairSyntax.mk_snd pv])))
                end
            fun mapped tm = mk_comb(mapApp (projs tm), z)
            val body =
                mk_exists(z,
                  list_mk_conj
                    (List.map conjOf (upto n) @
                     [mk_eq(mapped pairSyntax.fst_tm, x),
                      mk_eq(mapped pairSyntax.snd_tm, y)]))
            val relty = List.foldr (op -->) (newty --> (mty --> bool))
                                   (List.map type_of Rs)
          in
            new_definition (Tyop ^ "REL_def",
                            mk_eq(mk_var(Tyop ^ "REL", relty),
                                  list_mk_abs(Rs @ [x,y], body)))
          end

      (* ------------------------------------------------------------
          and the database's canonical form: the live arguments named
          'a1 .. 'an, in the order the type takes them
         ------------------------------------------------------------ *)

      fun canonvar i = mk_vartype ("'a" ^ Int.toString (i + 1))
      val canon = ListPair.mapEq (fn (l,i) => l |-> canonvar i)
                                 (largs, upto n)
      (* an argument the fixed point isn't functorial in keeps whatever
         name it had, so it must not be one of the canonical ones *)
      val _ = List.all (fn {residue,...} =>
                           not (Lib.mem residue (type_vars newty)) orelse
                           Lib.mem residue largs)
                       canon orelse
              raise ERR "fixpointBNF"
                    "a dead argument of the type is named like a live one"
      val cinst = Term.inst canon
      val cthm = INST_TYPE canon
      val relator = lhs (concl relator_def)
    in
      {key = {Thy = Thy, Name = Tyop},
       map_thm = map_thm, set_thms = set_thms, relator_def = relator_def,
       info = bnfBase.bI {
         bnd = cinst (#bnd bnf),
         bndthms = List.map (cthm o bndthm) (upto n),
         canontype = type_subst canon newty,

         map = cinst MAPtm,
         mapID = cthm mapID,
         mapO = cthm mapO,
         mapIMAGE = List.map (cthm o mapIMAGE) (upto n),
         mapCONG = cthm mapCONG,

         relator = cinst relator,
         set = List.map (cinst o setTm) (upto n),

         wits = List.map ((fn (t,th) => (cinst t, cthm th)) o witOf) fwits,
         inhabits = List.map ((fn (t,th) => (cinst t, cthm th)) o inhOf)
                             (upto n)
       }}
    end

(* ----------------------------------------------------------------------
    The map and the set functions at each constructor.

    fixpointBNF defines them by the equation the recursion principle
    gives, whose right-hand side is a map of the whole functor; what a
    user reads, and what a size definition or a TypeBase entry is written
    with, is one equation per constructor.  Instantiating the equation at
    a constructor's own argument and simplifying the functor away turns
    one into the other, and the constructors' definitions fold the result
    back up.  Nothing here needs the functor's shape: the definition of
    each constructor says what to instantiate at.
   ---------------------------------------------------------------------- *)

(* taking a sum of products apart *)
val shapeRWs = [sumTheory.SUM_MAP_def, pairTheory.PAIR_MAP,
                combinTheory.I_THM, oneTheory.one]

(* and the same for a set function, which is built out of BIMG and a
   lifted union, and whose leaves are the components' set functions —
   stated as predicates, so set notation has to be put back *)
val setRWs = [bnfPrelimsTheory.BIMG_EQUAL, bnfPrelimsTheory.BIMG_K0,
              combinTheory.I_o_ID, combinTheory.S_DEF, combinTheory.o_DEF,
              combinTheory.K_DEF, pairTheory.setFST_thm,
              pairTheory.setSND_thm, LAM_EQ_SING, LAM_F_EMPTY,
              pred_setTheory.INSERT_UNION_EQ, BIGUNION_IMAGE_EMPTY]

(* eta reduction is part of unfolding a set term: the lifted union leaves
   a component's set function applied to a bound variable *)
val set_ss = simpLib.++ (BasicProvers.srw_ss(), boolSimps.ETA_ss)

fun constructorEqns (cs : constructors) (res : fixpoint_bnf) =
    let
      val defs = #defs cs
      val (mvars, _) = strip_forall (concl (#map_thm res))
      val fvars = List.take (mvars, length mvars - 1)
      (* the instance the map lands in, as its own functions say *)
      val theta = List.map (fn f => let val (d,r) = dom_rng (type_of f)
                                    in d |-> r end)
                           fvars
      val folds = List.map GSYM defs
      val tgtfolds = List.map (GSYM o INST_TYPE theta) defs
      (* the constructor's own argument, from its definition *)
      fun injOf def = rand (rhs (#2 (strip_forall (concl def))))
      fun unfold ss rws th =
          CONV_RULE (RAND_CONV (QCONV (simpLib.SIMP_CONV ss rws))) th
      fun mapEqn def =
          REWRITE_RULE (folds @ tgtfolds)
            (unfold boolSimps.bool_ss shapeRWs
                    (SPECL (fvars @ [injOf def]) (#map_thm res)))
      fun setEqn i def =
          REWRITE_RULE folds
            (unfold set_ss setRWs
                    (SPEC (injOf def) (List.nth (#set_thms res, i))))
    in
      {map_eqns = LIST_CONJ (List.map mapEqn defs),
       set_eqns = List.tabulate
                    (length (#set_thms res),
                     fn i => LIST_CONJ (List.map (setEqn i) defs))}
    end


(* ----------------------------------------------------------------------
    Mutual recursion, as a nested recursion.

    A mutually recursive pair arrives as one functor per type with the
    sibling as an extra argument — F1(α,'a1) and F2(α,'a1), where α is
    the type's own recursion and 'a1 the sibling's slot.  Nothing new is
    constructed for it:

      * take the second type's fixed point with the sibling's slot left a
        parameter, which is an ordinary datatype in that argument;
      * make it a functor and hand it on in memory;
      * define the first type as a recursion *nested* through it,
            T1 = μα. F1(α, ('a1 := α) T2)
        which is what the package already does;
      * and the second type is that datatype at T1.

    The pair's recursion principle is then one instance of
    bnfMutualTheory's, whose hypotheses are the two types' own
    principles, the sibling's map, and three instances of the functors'
    composition law.
   ---------------------------------------------------------------------- *)

type mutual = {
  ty1 : hol_type, ty2 : hol_type,     (* the two types *)
  cons1 : term, cons2 : term,         (* and their constructors *)
  fix1 : fixpoint, fix2 : fixpoint,   (* what each type's construction gave *)
  sibling : fixpoint_bnf,             (* the second type as a functor *)
  bnf1 : bnfLib.derived_bnfn,         (* each type's functor, as the *)
  bnf2 : bnfLib.derived_bnfn,         (* construction saw it *)
  db : bnfBase.t,                     (* the database, extended with it *)
  iterator : thm,                     (* the pair's principle, folded *)
  recursion : thm,                    (* and in full, as an iterator *)
  prim_recursion : thm,               (* and hearing the arguments too *)
  induction : thm
}

(* |- t1 = t2, when both sides normalise to the same thing.  Two set
   terms built by nesting one functor inside another are equal by the
   algebra of BIMG and the lifted union; normalising both is how a driver
   sees that without running a tactic. *)
val normRWs = setRWs @ [BIGUNION_IMAGE_UNION, BIGUNION_IMAGE_BIGUNION]
fun normEqWith rws (t1,t2) =
    let val cnv = QCONV (simpLib.SIMP_CONV set_ss (normRWs @ rws))
        val (e1,e2) = (cnv t1, cnv t2)
    in
      if aconv (rhs (concl e1)) (rhs (concl e2)) then TRANS e1 (SYM e2)
      else raise ERR "normEq"
                 ("no common normal form: " ^ term_to_string (rhs (concl e1)) ^
                  " and " ^ term_to_string (rhs (concl e2)))
    end

fun normEq (t1,t2) =
    let val cnv = QCONV (simpLib.SIMP_CONV set_ss normRWs)
        val (e1,e2) = (cnv t1, cnv t2)
    in
      if aconv (rhs (concl e1)) (rhs (concl e2)) then TRANS e1 (SYM e2)
      else raise ERR "normEq"
                 ("no common normal form: " ^ term_to_string (rhs (concl e1)) ^
                  " and " ^ term_to_string (rhs (concl e2)))
    end

(* the element variable and  |- map gs (map fs af) = map (gs o fs) af, at
   the instance the functions say: one instance of the composition law,
   pointwise.  The variable comes back because the caller has to
   generalise the very one the theorem is about. *)
fun mapOAt bnf (fs,gs) =
    let val target = mk_o (#mkmap bnf gs, #mkmap bnf fs)
        val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                   (PART_MATCH lhs (#mapO bnf) target)
        val srcs = List.map (#1 o dom_rng o type_of) fs
        val af = mk_var("af", functorAtArgs bnf (hd srcs, tl srcs))
    in
      (af,
       TRANS (SYM (ISPECL [#mkmap bnf gs, #mkmap bnf fs, af]
                          combinTheory.o_THM))
             (AP_THM th af))
    end

(* the answer type variable of a recursion principle *)
fun answerTy th = #2 (dom_rng (type_of (#1 (dest_forall (concl th)))))

fun defineMutual {tyname1, tyname2} db params (f1ty, f2ty) : mutual =
    let
      (* the sibling's slot, as the specification's translation names it *)
      val a1 = mk_vartype "'a1"
      val lives = alpha :: a1 :: params
      val pIs = List.map Ify params

      (* ---------------------------------------------------------------
          the sibling, as a datatype in the other type's slot
         --------------------------------------------------------------- *)
      val bnf2 = bnfLib.deriveBNFn db lives f2ty
      val fix2 = defineFixpoint {tyname = tyname2, ABS = tyname2 ^ "_ABS",
                                 REP = tyname2 ^ "_REP"} bnf2
      val res2 = fixpointBNF bnf2 fix2
      val db = bnfBase.insert (#key res2, #info res2) db
      val sibty = #newty fix2
      fun sibAt ty = type_subst [a1 |-> ty] sibty

      (* the sibling's map with a function in the other type's slot and
         identities elsewhere: the map the two recursions meet in *)
      val (mvars, _) = strip_forall (concl (#map_thm res2))
      val sibfs = List.take (mvars, length mvars - 1)
      val sibMAP =
          repeat rator (lhs (#2 (strip_forall (concl (#map_thm res2)))))
      fun smapArgs g =
          List.map (fn f => let val (d,_) = dom_rng (type_of f)
                            in if d = a1 then g else Ify d end)
                   sibfs
      fun smapTheta gs =
          List.concat (ListPair.mapEq
                         (fn (f,arg) =>
                             let val (d,r) = dom_rng (type_of f)
                                 val (d',r') = dom_rng (type_of arg)
                             in [d |-> d', r |-> r'] end)
                         (sibfs, gs))
      fun smapAt g =
          let val gs = smapArgs g
          in list_mk_comb (Term.inst (smapTheta gs) sibMAP, gs) end

      (* ---------------------------------------------------------------
          the first type, as a recursion nested through the sibling
         --------------------------------------------------------------- *)
      val bnf1 = bnfLib.deriveBNFn db (alpha :: params)
                                  (type_subst [a1 |-> sibAt alpha] f1ty)
      val fix1 = defineFixpoint {tyname = tyname1, ABS = tyname1 ^ "_ABS",
                                 REP = tyname1 ^ "_REP"} bnf1
      (* and the first functor in both its arguments, whose composition
         law the derivation below needs *)
      val bnfF1 = bnfLib.deriveBNFn db lives f1ty

      val ty1 = #newty fix1
      val ty2 = sibAt ty1
      val cons1 = #cons fix1
      val cons2 = Term.inst [a1 |-> ty1] (#cons fix2)

      (* the answer types: one per type, and distinct, whatever the two
         constructions happened to call theirs *)
      val answer1 = answerTy (#recursion fix1)
      val answer2 = answerTy (#recursion fix2)
      val avoid = [a1, answer1, answer2] @ type_vars ty1 @ type_vars sibty
      val (c1v, c2v) = case freshTys "'e" 2 avoid of
                           [x,y] => (x,y)
                         | _ => raise ERR "defineMutual" "no fresh variables"
      val rec1 = INST_TYPE [answer1 |-> c1v] (#recursion fix1)
      val rec2 = INST_TYPE [answer2 |-> c2v] (#recursion fix2)

      (* ---------------------------------------------------------------
          the maps bnfMutualTheory's parameters stand for
         --------------------------------------------------------------- *)
      val g = mk_var("g", ty1 --> c1v)
      val k2 = mk_var("k", ty2 --> c2v)
      val km = mk_var("k", sibAt c1v --> c2v)
      val h = mk_var("h", ty1 --> c1v)

      fun F2map (rc, sib) = #mkmap bnf2 (rc :: sib :: pIs)
      fun F1map (rc, sib) = #mkmap bnfF1 (rc :: sib :: pIs)

      val smap_op = mk_abs (g, smapAt g)
      val mpG_op = mk_abs (h, #mkmap bnf1 (h :: pIs))
      val mpH_op = mk_abs (km, F1map (Ify c1v, km))
      val mpK_op = mk_abs (g, mk_abs (k2, F1map (g, k2)))
      val mpBg_op = mk_abs (g, F2map (smapAt g, g))
      val mp2c_op = mk_abs (km, F2map (km, Ify c1v))
      val mp2n_op = mk_abs (k2, F2map (k2, Ify ty1))
      val mpQ_op = mk_abs (g, mk_abs (k2, F2map (k2, g)))
      val mp1a_op = mk_abs (g, F2map (Ify c2v, g))

      (* ---------------------------------------------------------------
          and the hypotheses
         --------------------------------------------------------------- *)
      val srec1 = byDefn SREC_def [cons1, mpG_op] rec1
      val srec2c = byDefn SREC_def
                          [Term.inst [a1 |-> c1v] (#cons fix2), mp2c_op]
                          (INST_TYPE [a1 |-> c1v] rec2)
      val srec2n = byDefn SREC_def [cons2, mp2n_op]
                          (INST_TYPE [a1 |-> ty1] rec2)
      val smapeq =
          let val gs = smapArgs g
              val th = SPECL gs (INST_TYPE (smapTheta gs) (#map_thm res2))
          in
            byDefn SMAP_def [cons2, Term.inst [a1 |-> c1v] (#cons fix2),
                             mpBg_op, smap_op]
                   (GEN g th)
          end
      val mutmap1 =
          let val (af, eq) = mapOAt bnfF1 ([g, smapAt g] @ pIs,
                                           [Ify c1v, km] @ pIs)
          in
            byDefn MUTMAP_def [mpG_op, mpH_op, mpK_op, smap_op]
                   (GENL [g, km, af] eq)
          end
      val mutmap2 =
          let val (af, eq) = mapOAt bnf2 ([smapAt g, g] @ pIs,
                                          [km, Ify c1v] @ pIs)
          in
            byDefn MUTMAP_def [mpBg_op, mp2c_op, mpQ_op, smap_op]
                   (GENL [g, km, af] eq)
          end
      val mutsplit =
          let val (af, eq) = mapOAt bnf2 ([k2, Ify ty1] @ pIs,
                                          [Ify c2v, g] @ pIs)
          in
            byDefn MUTSPLIT_def [mpQ_op, mp1a_op, mp2n_op]
                   (GENL [g, k2, af] (SYM eq))
          end

      (* the pair's principle, and the same thing with the two equations
         written out, which is what a caller reads *)
      val mutiter =
          MATCH_MP MUTUAL_RECURSION
                   (LIST_CONJ [srec1, srec2c, srec2n, smapeq,
                               mutmap1, mutmap2, mutsplit])
      val recursion =
          CONV_RULE (DEPTH_CONV BETA_CONV)
                    (REWRITE_RULE [MUTITER_def, MUTREC_def] mutiter)


      (* ------------------------------------------------------------
          primitive recursion for the pair

          The principle above hands each function only the results of the
          recursive calls; the axiom the rest of HOL is written against
          hands it the constructor's arguments too.  bnfMutualTheory
          bridges the two, over maps that take a function per *type*
          rather than per argument — so the functor whose own recursion
          is the second type takes them the other way round.
         ------------------------------------------------------------ *)
      fun pairMap bnf swap (g,k) =
          #mkmap bnf ((if swap then [k,g] else [g,k]) @ pIs)
      fun pairArg bnf swap (s1,s2) =
          if swap then functorAtArgs bnf (s2, s1 :: params)
          else functorAtArgs bnf (s1, s2 :: params)
      fun pairVars ((s1,s2),(t1,t2)) (n1,n2) =
          (mk_var(n1, s1 --> t1), mk_var(n2, s2 --> t2))
      fun pairOp bnf swap (src,tgt) =
          let val (g,k) = pairVars (src,tgt) ("g","k")
          in mk_abs(g, mk_abs(k, pairMap bnf swap (g,k))) end
      fun pairId bnf swap (s as (s1,s2)) =
          let val idmap = pairMap bnf swap (Ify s1, Ify s2)
              val x = mk_var("x", pairArg bnf swap s)
              val th = TRANS (AP_THM (PART_MATCH lhs (#mapID bnf) idmap) x)
                             (ISPEC x combinTheory.I_THM)
          in
            byDefn MapId2_def [pairOp bnf swap (s,s)] (GEN x th)
          end
      fun pairComp bnf swap (a,b,c) =
          let val (f1,f2) = pairVars (a,b) ("f1","f2")
              val (g1,g2) = pairVars (b,c) ("g1","g2")
              val (mab, mbc) = (pairMap bnf swap (f1,f2),
                                pairMap bnf swap (g1,g2))
              val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                         (PART_MATCH lhs (#mapO bnf)
                                                     (mk_o (mbc, mab)))
              val x = mk_var("x", pairArg bnf swap a)
              val th = TRANS (SYM (ISPECL [mbc, mab, x] combinTheory.o_THM))
                             (AP_THM th x)
          in
            byDefn MapComp2_def [pairOp bnf swap (a,b), pairOp bnf swap (b,c),
                                 pairOp bnf swap (a,c)]
                   (GENL [f1,f2,g1,g2,x] th)
          end
      val nn = (ty1, ty2)
      val cc = (c1v, c2v)
      val qq = (pairSyntax.mk_prod (ty1,c1v), pairSyntax.mk_prod (ty2,c2v))
      fun atAnswers (a1',a2') =
          INST_TYPE [c1v |-> a1', c2v |-> a2'] mutiter
      val prim_recursion =
          CONV_RULE (DEPTH_CONV BETA_CONV)
            (MATCH_MP MUTUAL_PRIM_REC
              (LIST_CONJ [atAnswers qq, atAnswers nn,
                        pairComp bnfF1 false (nn,qq,nn),
                        pairComp bnfF1 false (nn,qq,cc),
                        pairId bnfF1 false nn,
                        pairComp bnf2 true (nn,qq,nn),
                        pairComp bnf2 true (nn,qq,cc),
                        pairId bnf2 true nn]))

      (* ------------------------------------------------------------
          the induction principle

          Each type's own principle covers its own sub-terms; what ties
          them together is the sibling's set function for the first
          type's slot, and the fact that the first type's sub-terms are
          its direct occurrences together with the ones the sibling
          holds.  That fact is an identity between two ways of writing
          the same set term, so it is proved by normalising both.
         ------------------------------------------------------------ *)
      val stn1 = setAtArgs bnf1 0 (ty1, params)
      val st2 = setAtArgs bnf2 0 (ty2, ty1 :: params)
      val sb1 = setAtArgs bnfF1 0 (ty1, ty2 :: params)
      val sa1 = setAtArgs bnfF1 1 (ty1, ty2 :: params)
      val sb2 = setAtArgs bnf2 1 (ty2, ty1 :: params)
      val a1pos = idxOf "defineMutual" (#Args (dest_thy_type sibty)) a1
      val sibset = List.nth (#set_thms res2, a1pos)
      val S21 = Term.inst [a1 |-> ty1]
                  (repeat rator (lhs (#2 (strip_forall (concl sibset)))))
      val fixind1 = byDefn FIXIND_def [cons1, stn1] (#set_induction fix1)
      val fixind2 = byDefn FIXIND_def [cons2, st2]
                           (INST_TYPE [a1 |-> ty1] (#set_induction fix2))
      val fixset2 = byDefn FIXSET_def [cons2, st2, sb2, S21]
                           (INST_TYPE [a1 |-> ty1] sibset)
      val nestset =
          let
            val af = mk_var("af", functorAt bnf1 ty1)
            val nested =
                pred_setSyntax.mk_union
                  (mk_comb (sb1, af),
                   pred_setSyntax.mk_bigunion
                     (pred_setSyntax.mk_image (S21, mk_comb (sa1, af))))
          in
            byDefn NESTSET_def [stn1, sb1, sa1, S21]
                   (GEN af (normEq (mk_comb (stn1, af), nested)))
          end
      val induction =
          MATCH_MP MUTUAL_INDUCTION
                   (LIST_CONJ [fixind1, fixind2, nestset, fixset2])

    in
      {ty1 = ty1, ty2 = ty2, cons1 = cons1, cons2 = cons2,
       fix1 = fix1, fix2 = fix2, sibling = res2, bnf1 = bnf1, bnf2 = bnf2,
       db = db, iterator = mutiter, recursion = recursion,
       prim_recursion = prim_recursion, induction = induction}
    end


(* ----------------------------------------------------------------------
    The pair's induction principle, one clause per constructor.

    Expanding the quantifier over each functor's shape and simplifying its
    set functions away is the same step defineConstructors takes for a
    single type's set-based induction; here both clauses go through it at
    once, and the constructors of both types fold the result back up.

    The second type's constructors were defined over the sibling functor
    at its own parameter, so they are instantiated to the first type on
    the way in.
   ---------------------------------------------------------------------- *)

fun mutualInduction (cs1 : constructors, cs2 : constructors)
                    (mt : mutual) =
    let
      val theta = match_type (type_of (#cons (#fix2 mt)))
                             (type_of (#cons2 mt))
      val defs2 = List.map (INST_TYPE theta) (#defs cs2)
      val defs = #defs cs1 @ defs2
      val expand =
          PURE_REWRITE_CONV [bnfPrelimsTheory.BIMG_EQUAL,
                             combinTheory.I_o_ID] THENC
          QCONV (simpLib.SIMP_CONV set_ss
                   (setRWs @ [sumTheory.FORALL_SUM, pairTheory.FORALL_PROD,
                              oneTheory.FORALL_ONE]))
      (* expanding the quantifier names each constructor's arguments after
         the projections it went through; rename them to the constructor's
         own, as its definition has them *)
      fun renameOne def =
          case List.map (#1 o dest_var) (#1 (strip_forall (concl def))) of
              [] => ALL_CONV
            | ns => RENAME_VARS_CONV ns
      fun renameConj [] = ALL_CONV
        | renameConj [d] = renameOne d
        | renameConj (d::ds) = LAND_CONV (renameOne d) THENC
                               RAND_CONV (renameConj ds)
      val rename = LAND_CONV (renameConj (#defs cs1)) THENC
                   RAND_CONV (renameConj defs2)
    in
      CONV_RULE (STRIP_QUANT_CONV (LAND_CONV rename))
        (REWRITE_RULE (List.map GSYM defs)
           (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV expand)) (#induction mt)))
    end


(* ----------------------------------------------------------------------
    A whole family of mutually recursive types.

    The pair's reduction generalises by taking the family from the last
    member back.  Write the specification's functors over one slot
    variable per member of the family, and let Sⱼ be the type built for
    member j with the slots of the *earlier* members left as parameters:

        Sₙ = μα. Fₙ(v₁ .. v_{n-1}, α)
        Sⱼ = μα. Fⱼ(v₁ .. v_{j-1}, α, S_{j+1}(..α..) .. Sₙ(..α..))

    Each Sⱼ is an ordinary datatype whose recursion is nested through the
    ones after it, so nothing new is constructed; each is made a functor
    in what is left, in memory, so that the next one can nest through it.
    The family's own types are then S₁ and the later Sⱼ at the types
    already built.

    A caller says which type variable of each functor stands for which
    member of the family — the translation of a specification numbers
    them per functor, so the same 'a1 means different things in different
    ones — and the position of a member's *own* variable is where its
    recursion goes.
   ---------------------------------------------------------------------- *)

type family = {
  types : hol_type list,             (* the family's types, in order *)
  cons : term list,                  (* and their constructors *)
  fixes : fixpoint list,             (* what each construction gave *)
  bnfs : bnfLib.derived_bnfn list,   (* the functor each was built over *)
  functors : bnfLib.derived_bnfn list,
                                     (* and each specification's own functor,
                                        derived in every member's slot *)
  maps : fixpoint_bnf option list,   (* each member as a functor in the
                                        members before it, where it is one *)
  raw : (hol_type * hol_type list) list,
                                     (* each member's own type, and the
                                        arguments its operator takes *)
  slots : hol_type list,             (* the slot variable per member *)
  params : hol_type list,            (* the arguments they all keep *)
  db : bnfBase.t                     (* the database, extended with them *)
}

fun defineFamily {tynames} db params specs : family =
    let
      val n = length specs
      val _ = length tynames = n orelse
              raise ERR "defineFamily" "a name per type, please"
      (* one slot variable per member, in place of the per-functor ones *)
      val avoid = params @ List.concat (List.map (type_vars o #1) specs)
      val vs = freshTys "'m" n avoid
      fun normalise (fty, slots) =
          let val _ = length slots = n orelse
                      raise ERR "defineFamily" "a slot per member, please"
          in
            type_subst (ListPair.mapEq (fn (s,v) => s |-> v) (slots, vs)) fty
          end
      val ftys = List.map normalise specs
      fun slotIdx v = Lib.assoc1 v (Lib.zip vs (upto n))

      (* what has been built so far, by member: its type and the
         arguments its type operator takes *)
      fun built ks k =
          case Lib.assoc1 k ks of
              SOME (_,x) => x
            | NONE => raise ERR "defineFamily" "member not built yet"

      (* member k's type, in terms of the slots of the members before i
         and of α for member i itself *)
      fun exprAt ks i k =
          if k < i then List.nth (vs, k)
          else if k = i then alpha
          else
            let val (ty, args) = built ks k
            in
              type_subst
                (List.mapPartial
                   (fn a => case slotIdx a of
                                SOME (_,m) => SOME (a |-> exprAt ks i m)
                              | NONE => NONE)
                   args)
                ty
            end

      (* the members are built from the last back *)
      fun buildOne (i, acc) =
          let
            val (ks, fixes, bnfs, maps, db) = acc
            val theta = List.map (fn k => List.nth (vs,k) |-> exprAt ks i k)
                                 (List.filter (fn k => k > i) (upto n)) @
                        [List.nth (vs,i) |-> alpha]
            val fty = type_subst theta (List.nth (ftys, i))
            val lives = alpha :: List.take (vs, i) @ params
            val bnf = bnfLib.deriveBNFn db lives fty
            val nm = List.nth (tynames, i)
            val fix = defineFixpoint {tyname = nm, ABS = nm ^ "_ABS",
                                      REP = nm ^ "_REP"} bnf
            val ty = #newty fix
            val args = #Args (dest_thy_type ty)
            (* a member with no arguments left is a datatype in its own
               right, which the ones before it nest through as a constant *)
            val (res, db) =
                if List.exists (isSome o slotIdx) args orelse
                   List.exists (fn a => Lib.mem a params) args
                then
                  let val res = fixpointBNF bnf fix
                  in
                    (SOME res, bnfBase.insert (#key res, #info res) db)
                  end
                else (NONE, db)
          in
            ((i,(ty,args)) :: ks, fix :: fixes, bnf :: bnfs, res :: maps, db)
          end
      val (ks, fixes, bnfs, maps, db) =
          List.foldl buildOne ([], [], [], [], db) (List.rev (upto n))

      (* and the family's types: the first as it stands, the rest at the
         types before them *)
      val ty1 = #1 (built ks 0)
      fun finalTy k = type_subst [alpha |-> ty1] (exprAt ks 0 k)
      val types = ty1 :: List.map finalTy (tl (upto n))
      val consts = ListPair.mapEq
                     (fn (fix,ty) =>
                         let val cty = type_of (#cons fix)
                         in
                           Term.inst (match_type (#2 (dom_rng cty)) ty)
                                     (#cons fix)
                         end)
                     (fixes, types)
      (* each specification's own functor, derived in every member's slot:
         the maps the family's principles are stated over *)
      val functors =
          List.map (fn fty =>
                       bnfLib.deriveBNFn db (vs @ params)
                                         fty)
                   ftys
    in
      {types = types, cons = consts, fixes = fixes, bnfs = bnfs,
       functors = functors, maps = maps, raw = List.map #2 ks, slots = vs,
       params = params, db = db}
    end



(* the witnesses of a nest of existentials, and what they satisfy *)
fun witnesses (ws, th) =
    if is_exists (concl th) then
      witnesses (ws @ [mk_select (dest_exists (concl th))], SELECT_RULE th)
    else (ws, th)

(* ----------------------------------------------------------------------
    The family's recursion principle.

    Solve the family from the last member back.  At the point where
    member i is reached, the members after it have already been solved —
    as a family over member i's own slot — so their functions are exactly
    what member i's target needs to fold the parts of its own functor
    that belong to them.  Member i's own recursion then gives its
    function, and each later member's is that member's solution after the
    map that sends member i's values to their answers.  This is the
    pair's argument with the sibling a family rather than a type, and the
    driver does it once per member.

    So that a target hears the argument its constructor was applied to,
    and not only the results of the recursive calls, member i's function
    hands back that argument alongside its answer.  The members after it
    are then solved over the pair, and recover the argument by mapping
    FST before passing it on.  That this recovers it is member i's own
    uniqueness: FST after its function solves the recursion the identity
    solves.

    What comes out is existence, which is the shape HOL's own axiom for a
    mutually recursive family takes.
   ---------------------------------------------------------------------- *)

fun familyPrinciple (fam : family) =
    let
      val n = length (#types fam)
      val vs = #slots fam and raw = #raw fam and params = #params fam
      val pIs = List.map Ify params
      fun slotIdx v =
          Option.map #2 (Lib.assoc1 v (ListPair.zipEq (vs, upto n)))
      (* the answers, and the slots a level leaves to its caller *)
      val avoid = vs @ params @
                  List.concat (List.map (type_vars o #1) (#raw fam))
      val cs = freshTys "'r" n avoid
      val xs = freshTys "'x" n (avoid @ cs)

      (* member k's type when the members before it are given by env *)
      fun tyIn env k =
          let val (ty,args) = List.nth (raw, k)
          in
            type_subst
              (List.mapPartial
                 (fn a => Option.map (fn m => a |-> env m) (slotIdx a))
                 args)
              ty
          end
      (* and at level i, where the members before it are whatever the
         caller of that level's principle puts in their slots *)
      fun tyAt i k =
          tyIn (fn m => if m < i then List.nth (xs,m) else tyAt i m) k

      (* the types a member's own construction and its map are stated
         over, at level i *)
      fun levelTheta i j =
          List.map (fn m => List.nth (vs,m) |->
                            (if m < i then List.nth (xs,m) else tyAt i m))
                   (upto j)
      fun atLevel i j th = INST_TYPE (levelTheta i j) th
      fun instLevel i j tm = Term.inst (levelTheta i j) tm
      fun consAt i j = instLevel i j (#cons (List.nth (#fixes fam, j)))

      (* F_j's map with the given function at each member's slot and the
         parameters carried along *)
      fun famMap j fs = #mkmap (List.nth (#functors fam, j)) (fs @ pIs)

      (* member j as a functor in the members before it *)
      fun memberOf j =
          case List.nth (#maps fam, j) of
              NONE => raise ERR "familyPrimRecursion"
                            "a member with nothing to map"
            | SOME res => res
      fun memberInfo j = case #info (memberOf j) of bnfBase.bI r => r

      (* member j's own map, sending each member before it where the
         given functions say *)
      fun memberMap j fs =
          let
            val res = memberOf j
            val (mvars,_) = strip_forall (concl (#map_thm res))
            val fvars = List.take (mvars, length mvars - 1)
            val MAPtm = repeat rator
                          (lhs (#2 (strip_forall (concl (#map_thm res)))))
            (* one function per argument of the type operator, in its
               own order: what a slot gets is what the caller says, and a
               parameter is carried *)
            val args = #2 (List.nth (raw, j))
            val gs = List.map (fn a => case slotIdx a of
                                           SOME m => List.nth (fs, m)
                                         | NONE => Ify a)
                              args
            val theta =
                List.concat
                  (ListPair.mapEq
                     (fn (f,g) =>
                         let val (d,r) = dom_rng (type_of f)
                             val (d',r') = dom_rng (type_of g)
                         in [d |-> d', r |-> r'] end)
                     (fvars, gs))
          in
            (list_mk_comb (Term.inst theta MAPtm, gs),
             SPECL gs (INST_TYPE theta (#map_thm res)))
          end

      (* |- map gs (map fs x) = map (gs o fs) x for a family functor *)
      fun famMapO j (fs,gs) =
          let val Fj = List.nth (#functors fam, j)
              val target = mk_o (famMap j gs, famMap j fs)
              val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                         (PART_MATCH lhs (#mapO Fj) target)
              val srcs = List.map (#1 o dom_rng o type_of) fs
              val af = mk_var("af", typeAtArgs Fj (hd srcs, tl srcs @ params)
                                               (functorTy Fj))
          in
            (af, TRANS (SYM (ISPECL [famMap j gs, famMap j fs, af]
                                    combinTheory.o_THM))
                       (AP_THM th af))
          end

      (* the answer type of a recursion principle, whether or not its
         target hears the argument as well *)
      fun answerOf th =
          let fun final ty = case Lib.total dom_rng ty of
                                 NONE => ty
                               | SOME (_,r) => final r
          in final (type_of (#1 (dest_forall (concl th)))) end

      (* the function a level's caller puts in a member's slot, and the
         target it solves a member at *)
      fun uvar m = mk_var ("u" ^ Int.toString m,
                           List.nth (xs,m) --> List.nth (cs,m))
      fun hty i k = (if k < i then List.nth (xs,k) else tyAt i k) -->
                    List.nth (cs,k)
      fun tvar i j =
          let val hs = List.tabulate (n, fn k => mk_var ("h", hty i k))
              val (a,b) = dom_rng (type_of (famMap j hs))
          in mk_var ("t" ^ Int.toString j, a --> (b --> List.nth (cs,j))) end

      (* the equation member j's function satisfies at level i *)
      fun eqTerm i fns t j =
          let val consj = consAt i j
              val af = mk_var ("af", #1 (dom_rng (type_of consj)))
          in
            mk_forall (af,
              mk_eq (mk_comb (List.nth (fns, j), mk_comb (consj, af)),
                     list_mk_comb (t, [af, mk_comb (famMap j fns, af)])))
          end

      (* Reduce a target's application and nothing else.  A witness from
         a level below is a term this level has to match its own maps
         against, and it has a target's abstraction inside it, so
         reducing everywhere would leave the two spellings of it
         different. *)
      val betaTarget =
          CONV_RULE (STRIP_QUANT_CONV
                       (RAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)))

      (* Solve the family from member i on.  The members before it are
         the level's parameters: their slots hold whatever the caller
         says, and the functions there are what it hands over.  What
         comes back is that level's principle, over those functions and
         the targets. *)
      fun solve i =
        let
          val later = List.drop (upto n, i + 1)
          val us = List.tabulate (i, uvar)
          val ts = List.map (tvar i) (List.drop (upto n, i))
          fun targetOf j = List.nth (ts, j - i)
          val subS = if null later then NONE else SOME (solve (i + 1))
          val fixi = List.nth (#fixes fam, i)
          val consi = consAt i i
          val ci = List.nth (cs, i)
          (* member i hands back the value it was applied to along with
             its answer, so that the members after it can still say what
             they were given *)
          val qi = pairSyntax.mk_prod (tyAt i i, ci)
          fun projq sel =
              Term.inst (match_type (#1 (dom_rng (type_of sel))) qi) sel
          val recover = projq pairSyntax.fst_tm
          val answer = projq pairSyntax.snd_tm
          (* one function per member's slot: what the caller says at
             member i's own, the maps already built after it, and the
             identity at the members before it *)
          fun slotFns f ms =
              List.tabulate (n, fn k =>
                                if k < i then Ify (List.nth (xs,k))
                                else if k = i then f
                                else if k - i - 1 < length ms then
                                  List.nth (ms, k - i - 1)
                                else Ify (tyAt i k))
          (* the maps that carry the later members' values wherever the
             function at member i's slot sends them.  A member's own
             slots are those of the members before it, so what is not
             built yet is not asked for. *)
          fun transports f =
              List.foldl (fn (m, acc) =>
                             acc @ [#1 (memberMap m (slotFns f acc))])
                         [] later
          (* and what undoes such a transport *)
          val Us = transports recover
          val recFns = slotFns recover Us
          (* the sub-family, at whatever is put in member i's slot *)
          fun subInst (X, w, subts) =
              SPECL (us @ [w] @ subts)
                    (INST_TYPE [List.nth (xs,i) |-> X] (valOf subS))
          (* the members after this one hear the argument they were
             reached from by undoing the transport first *)
          val subtargets =
              List.map
                (fn j =>
                    let val R = famMap j recFns
                        val tj = targetOf j
                        val afv = mk_var("af", #1 (dom_rng (type_of R)))
                        val vv = mk_var("v", #1 (dom_rng (#2 (dom_rng
                                                    (type_of tj)))))
                    in
                      mk_abs (afv, mk_abs (vv,
                                list_mk_comb (tj, [mk_comb (R, afv), vv])))
                    end)
                later
          val (gs, subeqs) =
              if null later then ([], [])
              else let val (ws, th) =
                           witnesses ([], CONJUNCT1
                                            (subInst (qi, answer, subtargets)))
                   in (ws, List.map betaTarget (CONJUNCTS th)) end
          (* the answers the later members' functions give, and the ones
             the members before this one carry *)
          val outer = List.tabulate (n, fn k => if k < i then uvar k
                                                else if k = i then answer
                                                else List.nth (gs, k-i-1))
          (* the target member i's own recursion is solved at: rebuild
             its argument for one component of the pair, and fold what
             belongs to the later members for the other *)
          val vv = mk_var("v", #1 (dom_rng (type_of (famMap i outer))))
          val afv = mk_var("af", #1 (dom_rng (type_of consi)))
          val taui =
              mk_abs (afv, mk_abs (vv,
                pairSyntax.mk_pair
                  (mk_comb (consi, mk_comb (famMap i recFns, vv)),
                   list_mk_comb (targetOf i,
                                 [afv, mk_comb (famMap i outer, vv)]))))
          val reci = INST_TYPE [answerOf (#prim_recursion fixi) |-> qi]
                               (atLevel i i (#prim_recursion fixi))
          val eqP0 = SELECT_RULE (EXISTENCE (SPEC taui reci))
          val eqP = betaTarget eqP0
          val af = #1 (dest_forall (concl eqP))
          val Pi = rator (lhs (#2 (strip_forall (concl eqP))))
          val mapIDs = List.map (#mapID o memberInfo) later
          (* the recovery after a transport, member by member: the two
             maps compose slot by slot, and the caller's rewrites say
             what happens at member i's own *)
          fun chain P rws =
              let val Ms = transports P
              in
                List.foldl
                  (fn (m, acc) =>
                      acc @ [CONV_RULE
                               (RAND_CONV (QCONV (PURE_REWRITE_CONV
                                  (combinTheory.I_o_ID :: rws @ acc))))
                               (PART_MATCH lhs (#mapO (memberInfo m))
                                  (mk_o (List.nth (Us, m-i-1),
                                         List.nth (Ms, m-i-1))))])
                  [] later
              end
          (* |- famMap recFns (famMap (slotFns P ..) af) = af, once the
             recovery is known to undo what P does *)
          fun recovered P fstth j =
              let val rws = combinTheory.I_o_ID :: combinTheory.I_THM ::
                            fstth :: #mapID (List.nth (#functors fam, j)) ::
                            mapIDs @ chain P [fstth]
              in
                CONV_RULE (RAND_CONV (QCONV (PURE_REWRITE_CONV rws)))
                          (#2 (famMapO j (slotFns P (transports P), recFns)))
              end
          (* member i's function hands back the value it was applied to:
             the recovery after it solves the recursion the identity
             solves, and there is only one solution *)
          val fstP =
              let
                val idty = tyAt i i
                val idmap = famMap i (slotFns (Ify idty)
                                              (transports (Ify idty)))
                val x = mk_var("x", #1 (dom_rng (type_of consi)))
                val idrws = mapIDs @ [#mapID (List.nth (#functors fam, i)),
                                      combinTheory.I_THM]
                val idth =
                    GEN x
                      (TRANS (ISPEC (mk_comb (consi,x)) combinTheory.I_THM)
                             (SYM (AP_TERM consi
                                     (PURE_REWRITE_CONV idrws
                                        (mk_comb (idmap, x))))))
                val step =
                    PURE_REWRITE_RULE
                      (#2 (famMapO i (slotFns Pi (transports Pi), recFns)) ::
                       chain Pi [])
                      (TRANS (ISPECL [recover, Pi, mk_comb (consi, af)]
                                     combinTheory.o_THM)
                             (CONV_RULE
                                (RAND_CONV (REWR_CONV pairTheory.FST))
                                (AP_TERM recover (SPEC af eqP))))
                val uq =
                    CONJUNCT2
                      (CONV_RULE Conv.EXISTS_UNIQUE_CONV
                         (SPEC consi
                            (INST_TYPE [answerOf (#recursion fixi) |-> idty]
                                       (atLevel i i (#recursion fixi)))))
              in
                MP (SPECL [mk_o (recover, Pi), Ify idty] uq)
                   (CONJ (GEN af step) idth)
              end
          (* what a member's function is, once member i's is known: its
             own solution after the transport, which its target undoes *)
          fun composed P = ListPair.mapEq (fn (g,m) => mk_o (g,m))
                                          (gs, transports P)
          fun slotsOf P =
              List.tabulate (n, fn k => if k < i then uvar k
                                        else if k = i then mk_o (answer, P)
                                        else List.nth (composed P, k-i-1))
          (* and the equation it satisfies, from that member's own and
             the map laws *)
          fun upgrade P fstth j =
              let
                val d = j - i - 1
                val gj = List.nth (gs, d)
                val P' = slotFns P (transports P)
                val (_, mjeq) = memberMap j P'
                val consj = consAt i j
                val afj = mk_var("af", #1 (dom_rng (type_of consj)))
                val step1 = TRANS (ISPECL [gj, List.nth (transports P, d),
                                           mk_comb (consj, afj)]
                                          combinTheory.o_THM)
                                  (AP_TERM gj (SPEC afj mjeq))
                val inner = rand (rhs (concl (SPEC afj mjeq)))
                val step2 = TRANS step1 (SPEC inner (List.nth (subeqs, d)))
              in
                GEN afj
                  (PURE_REWRITE_RULE
                     [recovered P fstth j, #2 (famMapO j (P', outer))]
                     step2)
              end
          (* member i's own function is the answer half of the pair *)
          val eqi =
              GEN af
                (PURE_REWRITE_RULE
                   [#2 (famMapO i (slotFns Pi (transports Pi), outer))]
                   (TRANS (ISPECL [answer, Pi, mk_comb (consi, af)]
                                  combinTheory.o_THM)
                          (CONV_RULE (RAND_CONV (REWR_CONV pairTheory.SND))
                                     (AP_TERM answer (SPEC af eqP)))))
          val hs = List.drop (slotsOf Pi, i)
          val eqs = eqi :: List.map (upgrade Pi fstP) later
          val hvars = List.tabulate (n - i, fn d =>
                                        mk_var ("h" ^ Int.toString (i+d),
                                                hty i (i+d)))
          val existence =
              List.foldr (fn ((hv,h), th) =>
                             EXISTS (mk_exists (hv, subst [h |-> hv]
                                                          (concl th)), h) th)
                         (LIST_CONJ eqs)
                         (ListPair.zipEq (hvars, hs))

          (* ------------------------------------------------------------
              and only one solution.

              Whatever a solution's function for member i is, pairing it
              with the identity solves member i's own recursion at the
              very target the construction above used — the recovery
              undoes that pairing by beta alone — so that pairing is the
              one built here, and the sub-family's own principle says the
              members after it are what they were solved to be.
             ------------------------------------------------------------ *)
          fun fnsOf vars =
              List.tabulate (n, fn k => if k < i then uvar k
                                        else List.nth (vars, k - i))
          fun eqsOf vars =
              List.map (fn j => eqTerm i (fnsOf vars) (targetOf j) j)
                       (List.drop (upto n, i))
          (* λx. (x, h x), and what its two halves do *)
          fun pairing h =
              let
                val x = mk_var ("x", tyAt i i)
                val P = mk_abs (x, pairSyntax.mk_pair (x, mk_comb (h, x)))
                val beta = BETA_CONV (mk_comb (P, x))
                fun half (sel, proj) =
                    TRANS (TRANS (ISPECL [sel, P, x] combinTheory.o_THM)
                                 (AP_TERM sel beta))
                          (REWR_CONV proj (mk_comb (sel, rhs (concl beta))))
              in
                (P,
                 EXT (GEN x (TRANS (half (recover, pairTheory.FST))
                                   (SYM (ISPEC x combinTheory.I_THM)))),
                 EXT (GEN x (half (answer, pairTheory.SND))))
              end
          val uqi = CONJUNCT2 (CONV_RULE Conv.EXISTS_UNIQUE_CONV
                                         (SPEC taui reci))
          (* what a solution's functions have to be *)
          fun solutionFacts (vars, ass) =
              let
                val hi = hd vars
                val (P, fstth, sndth) = pairing hi
                val Ps = slotFns P (transports P)
                (* the members after this one, transported by what member
                   i does, solve the sub-family at member i's own slot *)
                val transported =
                    List.map (fn j => PURE_REWRITE_RULE [sndth]
                                                        (upgrade P fstth j))
                             later
                val subres =
                    if null later then []
                    else
                      CONJUNCTS
                        (MP (SPECL (List.tl vars @
                                    List.drop (slotsOf P, i + 1))
                                   (CONJUNCT2 (subInst (tyAt i i, hi,
                                                        List.tl ts))))
                            (CONJ (LIST_CONJ (List.tl ass))
                                  (LIST_CONJ transported)))
                (* so the pairing solves member i's own recursion, at the
                   target the construction solved it at *)
                val Peq =
                    GEN af
                      (TRANS (BETA_CONV (mk_comb (P, mk_comb (consi, af))))
                             (SYM (PURE_REWRITE_RULE
                                     ([recovered P fstth i,
                                       #2 (famMapO i (Ps, outer)), sndth] @
                                      List.map SYM subres @
                                      [SYM (SPEC af (hd ass))])
                                     ((RATOR_CONV BETA_CONV THENC BETA_CONV)
                                        (list_mk_comb
                                           (taui,
                                            [af, mk_comb (famMap i Ps,
                                                          af)]))))))
                val isP = MP (SPECL [P, Pi] uqi) (CONJ Peq eqP0)
              in
                (TRANS (SYM sndth) (AP_TERM (rator (mk_o (answer, P))) isP),
                 List.map (PURE_REWRITE_RULE [isP]) subres)
              end
          val hypH = list_mk_conj (eqsOf hvars)
          val kvars = List.tabulate (n - i, fn d =>
                                        mk_var ("k" ^ Int.toString (i+d),
                                                hty i (i+d)))
          val hypK = list_mk_conj (eqsOf kvars)
          val both = ASSUME (mk_conj (hypH, hypK))
          val uniqueness =
              let
                val (hi, hjs) = solutionFacts (hvars, CONJUNCTS
                                                        (CONJUNCT1 both))
                val (ki, kjs) = solutionFacts (kvars, CONJUNCTS
                                                        (CONJUNCT2 both))
              in
                GENL (hvars @ kvars)
                     (DISCH (mk_conj (hypH, hypK))
                            (LIST_CONJ
                               (TRANS hi (SYM ki) ::
                                ListPair.mapEq (fn (a,b) => TRANS a (SYM b))
                                               (hjs, kjs))))
              end
        in
          GENL (us @ ts) (CONJ existence uniqueness)
        end
    in
      solve 0
    end

(* its two halves *)
fun familyExistence th =
    let val (ts, _) = strip_forall (concl th)
    in GENL ts (CONJUNCT1 (SPECL ts th)) end
fun familyUniqueness th =
    let val (ts, _) = strip_forall (concl th)
    in GENL ts (CONJUNCT2 (SPECL ts th)) end

fun familyPrimRecursion fam = familyExistence (familyPrinciple fam)

(* ----------------------------------------------------------------------
    The same principle as an iterator: a target that ignores the
    argument its constructor was applied to hears only the results of
    the recursive calls.
   ---------------------------------------------------------------------- *)

fun familyRecursion fam =
    let
      val prim = familyPrimRecursion fam
      val (ts, _) = strip_forall (concl prim)
      val its =
          List.map (fn t =>
                       let val (a, rest) = dom_rng (type_of t)
                           val v = mk_var (#1 (dest_var t), rest)
                       in (v, mk_abs (mk_var("af", a), v)) end)
                   ts
    in
      GENL (List.map #1 its)
           (CONV_RULE (DEPTH_CONV BETA_CONV)
                      (SPECL (List.map #2 its) prim))
    end


(* ----------------------------------------------------------------------
    Reading a family's principles at its constructors.

    Each member's constructors were defined over its own construction,
    where the members before it are still parameters, so they are
    instantiated to the family's types on the way in; and expanding a
    quantifier over a functor's shape names the constructors' arguments
    after the projections it went through, so they are renamed to what
    the definitions call them.
   ---------------------------------------------------------------------- *)

fun familyDefs (css : constructors list) (fam : family) =
    ListPair.mapEq
      (fn ((cs,fix),cons) =>
          let val theta = match_type (type_of (#cons fix)) (type_of cons)
          in List.map (INST_TYPE theta) (#defs cs) end)
      (ListPair.zipEq (css, #fixes fam), #cons fam)

local
  fun renameOne def =
      case List.map (#1 o dest_var) (#1 (strip_forall (concl def))) of
          [] => ALL_CONV
        | ns => RENAME_VARS_CONV ns
  fun renameConj [] = ALL_CONV
    | renameConj [d] = renameOne d
    | renameConj (d::ds) = LAND_CONV (renameOne d) THENC
                           RAND_CONV (renameConj ds)
in
fun renameBlocks [] = ALL_CONV
  | renameBlocks [ds] = renameConj ds
  | renameBlocks (ds::rest) = LAND_CONV (renameConj ds) THENC
                              RAND_CONV (renameBlocks rest)
end

(* ----------------------------------------------------------------------
    The family's recursion principle, one clause per constructor.

    The principle above is stated over each functor's map: a target is
    handed the whole of a constructor's argument with the family's
    functions applied to whatever belongs to the family.  What a proof is
    written against is one equation per constructor instead, and getting
    there is the step defineConstructors takes for a single type — a case
    term over the functor's sum of products for each target, and then the
    quantifier over the functor's shape expanded.

    A target is handed the constructor's own arguments and then the
    results of the recursive calls, which is the order TypeBase settled
    on; what makes an argument recursive is that the map did something
    to it.

    Each member's constructors were defined over its own construction,
    where the members before it are still parameters, so they are
    instantiated to the family's types on the way in.
   ---------------------------------------------------------------------- *)

fun familyAxiomOf (defs : thm list list) recursion =
    let
      val (ts, _) = strip_forall (concl recursion)
      val _ = length ts = length defs orelse
              raise ERR "familyAxiom" "a definition list per member"
      (* one branch per constructor: it is handed the constructor's own
         arguments, from what it was applied to, and the results of the
         recursive calls, from what the map produced.  A factor whose
         type the map left alone is not one of the family's. *)
      fun member (t, ds) k =
          let
            val (fty, rest) = dom_rng (type_of t)
            (* a target that hears the arguments as well takes two *)
            val prim = Lib.can dom_rng rest
            val (vty, cty) = if prim then dom_rng rest else (fty, rest)
            val nSummands = sumSyntax.strip_sum fty
            val cSummands = sumSyntax.strip_sum vty
            val afv = mk_var ("af", fty)
            val vv = mk_var ("v", vty)
            fun branch i =
                let
                  val nfacs = factorsOf (List.nth (nSummands, i))
                  val cfacs = factorsOf (List.nth (cSummands, i))
                  val recs = ListPair.mapEq (fn (a,b) => a <> b) (nfacs, cfacs)
                  val xv = mk_var ("x", List.nth (nSummands, i))
                  val args =
                      if prim then
                        let val xps = projs (length nfacs) xv
                            val yps = projs (length cfacs)
                                            (mkOut cSummands i vv)
                            fun pick p xs = List.map #2
                                              (List.filter (p o #1)
                                                           (zip recs xs))
                        in pick not xps @ pick I xps @ pick I yps end
                      else projs (length cfacs) xv
                  val fvar = mk_var ("f" ^ Int.toString (k + i),
                                     List.foldr (op -->) cty
                                                (List.map type_of args))
                in
                  (fvar, (xv, list_mk_comb (fvar, args)))
                end
            val bs = List.tabulate (length ds, branch)
            val body = mkCaseTerm (if prim then nSummands else cSummands)
                                  (List.map #2 bs)
          in
            (List.map #1 bs,
             if prim then mk_abs (afv, mk_abs (vv, body afv))
             else mk_abs (vv, body vv))
          end
      val members =
          #2 (List.foldl
                (fn ((t,ds), (k,acc)) =>
                    let val m = member (t,ds) k
                    in (k + length ds, acc @ [m]) end)
                (0, []) (ListPair.zipEq (ts, defs)))
      (* expanding the quantifier over each functor's shape gives every
         constructor's equation at once, and the definitions fold the
         injections back into the constructors *)
      val expand =
          QCONV (simpLib.SIMP_CONV boolSimps.bool_ss
                   [sumTheory.FORALL_SUM, pairTheory.FORALL_PROD,
                    oneTheory.FORALL_ONE, sumTheory.SUM_MAP_def,
                    sumTheory.sum_case_def, sumTheory.OUTL, sumTheory.OUTR,
                    pairTheory.PAIR_MAP, pairTheory.FST, pairTheory.SND,
                    combinTheory.I_THM])
    in
      (* one clause per constructor, in one list: expanding a member's
         equation leaves its own clauses nested inside the family's, and
         what reads a datatype axiom expects them flat *)
      PURE_REWRITE_RULE [GSYM CONJ_ASSOC]
        (GENL (List.concat (List.map #1 members))
          (CONV_RULE
             (STRIP_QUANT_CONV (renameBlocks defs))
             (REWRITE_RULE (List.map GSYM (List.concat defs))
                (CONV_RULE (STRIP_QUANT_CONV expand)
                   (CONV_RULE (DEPTH_CONV BETA_CONV)
                      (SPECL (List.map #2 members) recursion))))))
    end


(* ----------------------------------------------------------------------
    The family's induction principle.

    A family's principle says its equations have exactly one solution;
    at the booleans that is an induction principle, which is how
    Prim_rec derives one for a single type.  Solve the family with each
    target handed "everything the map produced is true, or else the
    conclusion at this constructor": the constant-true functions are one
    solution, the predicates are another exactly when they satisfy the
    induction clauses, and uniqueness makes them equal.

    What a target is handed is what F's set functions hold of the mapped
    value, and naturality turns that into the sub-terms of the argument
    — so the hypothesis of a clause is "every sub-term the functor holds
    of this member's type satisfies that member's predicate", the same
    set-based hypothesis a nested recursion leaves a single type with.
   ---------------------------------------------------------------------- *)

fun familySetInductionOf (fam : family) (types, conss) principle =
    let
      val n = length types
      val params = #params fam
      val pIs = List.map Ify params
      val uq = familyUniqueness principle
      val (vars, _) = strip_forall (concl uq)
      val ts = List.take (vars, n)
      fun finalRange ty =
          case Lib.total dom_rng ty of NONE => ty | SOME (_,r) => finalRange r
      val atBool =
          INST_TYPE (List.map (fn t => finalRange (type_of t) |-> bool) ts) uq
      fun functorOf j = List.nth (#functors fam, j)
      fun famMap j fs = #mkmap (functorOf j) (fs @ pIs)
      (* |- setₘ (map fs x) = IMAGE fₘ (set x), pointwise: the stored law
         is point-free *)
      fun famNat j m fs =
          let val Fj = functorOf j
              val gs = fs @ pIs
              val srcs = List.map (#1 o dom_rng o type_of) gs
              val tgts = List.map (#2 o dom_rng o type_of) gs
              val set1 = setAtArgs Fj m (hd srcs, tl srcs)
              val set2 = setAtArgs Fj m (hd tgts, tl tgts)
              val mp = famMap j fs
              val th = PART_MATCH lhs (List.nth (#mapIMAGE Fj, m))
                                  (mk_o (set2, mp))
              val x = mk_var("x", functorAtArgs Fj (hd srcs, tl srcs))
              val img = rand (rator (rhs (concl th)))
          in
            TRANS (TRANS (SYM (ISPECL [set2, mp, x] combinTheory.o_THM))
                         (AP_THM th x))
                  (ISPECL [img, set1, x] combinTheory.o_THM)
          end
      val Ps = List.tabulate (n, fn j =>
                  mk_var ("P" ^ Int.toString j, List.nth (types,j) --> bool))
      val Ts = List.map (fn ty => mk_abs (mk_var("x",ty), boolSyntax.T)) types
      (* a member's functor need not hold values of every member's type;
         where it does not, there is nothing for that member's predicate
         to say *)
      fun holds j m =
          let val Fj = functorOf j
          in
            Lib.mem (List.nth (#lives Fj, m)) (type_vars (functorTy Fj))
          end
      fun slotsHeld j = List.filter (holds j) (upto n)
      (* What the sets of a mapped value say is what naturality turns
         into what the argument's own sets say, and that has to happen
         before anything takes a composite's set function apart. *)
      fun natConv j fs =
          QCONV (DEPTH_CONV BETA_CONV) THENC
          QCONV (PURE_REWRITE_CONV (List.map (fn m => famNat j m fs)
                                             (slotsHeld j))) THENC
          QCONV (PURE_REWRITE_CONV [bnfFixBNFTheory.IMAGE_ALL]) THENC
          QCONV (simpLib.SIMP_CONV boolSimps.bool_ss [])
      (* what a target is handed: everything the map produced is true *)
      fun allTrue j v =
          list_mk_conj
            (List.map
               (fn m =>
                   let val b = mk_var("b", bool)
                       val boolTys = List.tabulate (n, fn _ => bool) @ params
                       val s = setAtArgs (functorOf j) m (hd boolTys,
                                                          tl boolTys)
                   in
                     mk_forall (b, mk_imp (pred_setSyntax.mk_in
                                             (b, mk_comb (s, v)), b))
                   end)
               (slotsHeld j))
      fun afOf j =
          mk_var ("af", #1 (dom_rng (type_of (List.nth (conss, j)))))
      fun target j =
          let val af = afOf j
              val boolTys = List.tabulate (n, fn _ => bool) @ params
              val v = mk_var("v", functorAtArgs (functorOf j)
                                                (hd boolTys, tl boolTys))
          in
            mk_abs (af, mk_abs (v,
              mk_disj (allTrue j v,
                       mk_comb (List.nth (Ps,j),
                                mk_comb (List.nth (conss,j), af)))))
          end
      (* the hypothesis of a clause is what that says of the argument
         itself, which is what naturality turns it into *)
      fun hypEq j =
          let val af = afOf j
          in
            natConv j Ps (allTrue j (mk_comb (famMap j Ps, af)))
          end
      val hypEqs = List.tabulate (n, hypEq)
      fun clause j =
          let val af = afOf j
          in
            mk_forall (af,
              mk_imp (rhs (concl (List.nth (hypEqs, j))),
                      mk_comb (List.nth (Ps,j),
                               mk_comb (List.nth (conss,j), af))))
          end
      val clauses = list_mk_conj (List.tabulate (n, clause))
      val ass = CONJUNCTS (ASSUME clauses)
      (* the targets are handed to the principle as abstractions; what
         has to be proved of them is what they say *)
      val inst =
          CONV_RULE (LAND_CONV (DEPTH_CONV BETA_CONV))
                    (SPECL (List.tabulate (n, target) @ Ts @ Ps) atBool)
      val (antT, antP) = dest_conj (#1 (dest_imp (concl inst)))
      (* the constant-true functions solve the equations, since whatever
         the map produced is true of them *)
      val trueSide =
          LIST_CONJ
            (List.tabulate
               (n, fn j =>
                     EQT_ELIM (natConv j Ts (List.nth (strip_conj antT, j)))))
      (* and the predicates solve them exactly when the clauses hold *)
      val predSide =
          LIST_CONJ
            (List.tabulate
               (n, fn j =>
                     let val af = afOf j
                         val step = MATCH_MP bnfFixBNFTheory.IMP_DISJ_EQ
                                             (SPEC af (List.nth (ass, j)))
                     in
                       GEN af
                         (CONV_RULE
                            (RAND_CONV (LAND_CONV
                                          (K (SYM (List.nth (hypEqs, j))))))
                            step)
                     end))
      val res = CONJUNCTS (MP inst (CONJ trueSide predSide))
    in
      GENL Ps
        (DISCH clauses
           (LIST_CONJ
              (List.tabulate
                 (n, fn j =>
                       let val x = mk_var("x", List.nth (types,j))
                           val th = CONV_RULE (LAND_CONV BETA_CONV)
                                              (AP_THM (List.nth (res,j)) x)
                       in GEN x (EQ_MP th TRUTH) end))))
    end

(* ----------------------------------------------------------------------
    The family's induction principle, one clause per constructor.

    The set-based principle says "every sub-term the functor holds of a
    member's type satisfies that member's predicate"; expanding the
    quantifier over each functor's shape says it of each constructor's
    arguments instead, which is the form a proof is written against.
   ---------------------------------------------------------------------- *)

fun familyInductionOf (defs : thm list list) induction =
    let
      val expand =
          PURE_REWRITE_CONV [bnfPrelimsTheory.BIMG_EQUAL,
                             combinTheory.I_o_ID] THENC
          QCONV (simpLib.SIMP_CONV set_ss
                   (setRWs @ [sumTheory.FORALL_SUM, pairTheory.FORALL_PROD,
                              oneTheory.FORALL_ONE]))
    in
      PURE_REWRITE_RULE [GSYM CONJ_ASSOC]
        (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (renameBlocks defs)))
           (REWRITE_RULE (List.map GSYM (List.concat defs))
              (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV expand)) induction)))
    end


(* ----------------------------------------------------------------------
    The case constants.

    `Prim_rec.define_case_constant` builds these from a datatype axiom by
    a recursive definition, which is a route a nested axiom cannot take —
    `new_recursive_definition` rejects it.  Nothing about a case constant
    is recursive, though: it is the axiom with every target ignoring the
    results of the recursive calls, so the same equations come out of the
    axiom directly.

    The constants are named and stated exactly as the old package's are,
    since that is what the rest of the system reads:

      |- (!v f. bt_CASE Lf v f = v) /\
         !a0 a1 a2 v f. bt_CASE (Nd a0 a1 a2) v f = f a0 a1 a2

    An axiom over a family gives one per member.
   ---------------------------------------------------------------------- *)

fun defineCases ax0 =
    let
      (* uniqueness is no use here, and a family's axiom does not have it *)
      val (fvars, body0) = strip_forall (concl ax0)
      val ax = if is_exists1 body0 then
                 GENL fvars (EXISTENCE (SPECL fvars ax0))
               else ax0
      val (hvars, body) = strip_exists (#2 (strip_forall (concl ax)))
      (* one clause per constructor: what the function does to it, and
         what the target is handed *)
      fun clauseOf tm =
          let val (args, eq) = strip_forall tm
              val (h, capp) = dest_comb (lhs eq)
              val (cons, cargs) = strip_comb capp
              val (f, fargs) = strip_comb (rhs eq)
          in
            {h = h, cons = cons, cargs = cargs, f = f, fargs = fargs}
          end
      val clauses = List.map clauseOf (strip_conj body)
      fun clausesOf h = List.filter (fn c => aconv (#h c) h) clauses
      (* a branch takes the constructor's own arguments, in the order the
         constructor takes them, and is named as the old package names it *)
      fun branchesOf h =
          let
            val cs = clausesOf h
            val rty = #2 (dom_rng (type_of h))
            fun mk (c, (bs, away)) =
                let val nm = if null (#cargs c) then "v" else "f"
                    val ty = List.foldr (op -->) rty
                                        (List.map type_of (#cargs c))
                    val v = numvariant away (mk_var (nm, ty))
                in (bs @ [v], v :: away) end
          in
            #1 (List.foldl mk ([], List.concat (List.map #cargs cs)) cs)
          end
      val branches = List.map branchesOf hvars
      (* the target that ignores the recursive calls' results: what is
         not one of the constructor's arguments is one of those *)
      fun targetOf (c, b) =
          let
            fun freshen (t, (vs, away)) =
                if is_var t andalso List.exists (aconv t) (#cargs c) then
                  (vs @ [t], away)
                else
                  let val v = numvariant away (mk_var ("r", type_of t))
                  in (vs @ [v], v :: away) end
            val (vs, _) = List.foldl freshen
                            ([], #cargs c @ free_varsl (#fargs c))
                            (#fargs c)
          in
            (#f c, list_mk_abs (vs, list_mk_comb (b, #cargs c)))
          end
      val targets =
          List.concat
            (ListPair.mapEq
               (fn (h,bs) => ListPair.mapEq targetOf (clausesOf h, bs))
               (hvars, branches))
      val solved =
          let fun instOf f =
                  case List.find (fn (g,_) => aconv g f) targets of
                      SOME (_,t) => t
                    | NONE => f
          in
            CONV_RULE (DEPTH_CONV BETA_CONV)
                      (SPECL (List.map instOf fvars) ax)
          end
      (* the functions the equations are about *)
      val (sels, eqth) = witnesses ([], solved)
      val eqs = CONJUNCTS eqth
      fun defineOne (j, h) =
          let
            val bs = List.nth (branches, j)
            val sel = List.nth (sels, j)
            val (dty, rty) = dom_rng (type_of h)
            val tyname = #1 (dest_type dty)
            val x = numvariant (bs @ List.concat (List.map #cargs clauses))
                               (mk_var ("x", dty))
            val cname = Prim_rec.case_constant_name {type_name = tyname}
            val casetm = list_mk_abs (x :: bs, mk_comb (sel, x))
            val cvar = mk_var (cname, type_of casetm)
            fun equation (c, eq) =
                let val capp = list_mk_comb (#cons c, #cargs c)
                    val app = list_mk_comb (casetm, capp :: bs)
                in
                  GENL (#cargs c @ bs)
                       (TRANS (LIST_BETA_CONV app) (SPECL (#cargs c) eq))
                end
            val cs = clausesOf h
            fun aboutSel eq =
                aconv (rator (lhs (#2 (strip_forall (concl eq))))) sel
            val jeqs = List.filter aboutSel eqs
            val proved = LIST_CONJ (ListPair.mapEq equation (cs, jeqs))
            val ex = mk_exists (cvar, subst [casetm |-> cvar] (concl proved))
          in
            new_specification
              (Prim_rec.case_constant_defn_name {type_name = tyname},
               [cname], EXISTS (ex, casetm) proved)
          end
    in
      List.tabulate (length hvars, fn j => defineOne (j, List.nth (hvars, j)))
    end


(* ----------------------------------------------------------------------
    Defining a function by the axiom.

    This is `Prim_rec.new_recursive_definition` for an axiom whose
    recursive calls arrive under a map: that one expects each recursive
    occurrence to be the function applied to a variable, and refuses
    anything else.  The clauses a caller writes here are the same
    otherwise —

        rsize RLeaf = 0 /\
        rsize (RNode a l) = 1 + mylistSUM (mylistMAP rsize l)

    — with the recursive call in whatever shape the axiom hands it over:
    `f a` for a direct occurrence and `MAP f l` for one under a functor.
    An axiom over a family takes clauses for each of its functions at
    once.

    What the caller writes has to be *that* shape.  A definition written
    the way the old package's nested axioms take them — an auxiliary
    function over the operator recursed under, with its own family of
    clauses — is a different recursion, and this says so rather than
    guessing: `Define` is the route for those, since it can look for a
    well-founded relation.
   ---------------------------------------------------------------------- *)

fun defineRecursion {name, axiom, def} =
    let
      (* the axiom, as existence over the functions it defines *)
      val (fvars, body0) = strip_forall (concl axiom)
      val unique = is_exists1 body0
      val ax = if unique then GENL fvars (EXISTENCE (SPECL fvars axiom))
               else axiom
      fun clauseOf tm =
          let val (args, eq) = strip_forall tm
              val (h, capp) = dest_comb (lhs eq)
              val (cons, cargs) = strip_comb capp
              val (f, fargs) = strip_comb (rhs eq)
          in
            {h = h, capp = capp, cons = cons, cargs = cargs,
             f = f, fargs = fargs}
          end
      (* and the clauses the caller wrote, by the constructor they are
         about *)
      (* the function may take parameters before the argument it
         recurses on, as a size function does *)
      fun userClause tm =
          let val (_, eq) = strip_forall tm
              val (fn_, capp) = dest_comb (lhs eq)
              val (cons, _) = strip_comb capp
          in
            (cons, (fn_, capp, rhs eq))
          end
      fun paramsOf tm = List.rev (List.tl (List.rev (#2 (strip_comb tm))))
      val uclauses = List.map userClause (strip_conj def)
      (* the caller's quotation has its own names for the type
         variables; the axiom is read at those *)
      val tyS =
          let val (_, body1) = strip_exists (#2 (strip_forall (concl ax)))
              val cs = List.map clauseOf (strip_conj body1)
              fun tryOne c =
                  case List.find (fn (cons,_) => same_const cons (#cons c))
                                 uclauses of
                      NONE => NONE
                    | SOME (_, (_, ucapp, _)) =>
                        SOME (#2 (match_term (#capp c) ucapp))
          in
            case List.mapPartial tryOne cs of
                [] => raise ERR "defineRecursion"
                            "no clause matches any of the axiom's"
              | th :: _ => th
          end
      val ax = INST_TYPE tyS ax
      val (fvars, body1) = strip_forall (concl ax)
      val (hvars, body) = strip_exists body1
      val axclauses = List.map clauseOf (strip_conj body)
      val applied = Lib.op_mk_set aconv (List.map (#1 o #2) uclauses)
      val params = paramsOf (lhs (#2 (strip_forall (hd (strip_conj def)))))
      val fns = List.map (#1 o strip_comb) applied
      val _ = length applied = length hvars orelse
              raise ERR "defineRecursion"
                    ("the axiom defines " ^ Int.toString (length hvars) ^
                     " function(s) and these clauses define " ^
                     Int.toString (length applied) ^
                     ": a definition with a function of its own over the" ^
                     " operator recursed under is a different recursion," ^
                     " and Define is the route for it")
      (* the target the axiom is instantiated at, for one constructor *)
      fun targetOf (c : {h:term, capp:term, cons:term, cargs:term list,
                         f:term, fargs:term list}) =
          let
            val (fn_, ucapp, urhs) =
                case List.find (fn (cons,_) => same_const cons (#cons c))
                               uclauses of
                    SOME (_, x) => x
                  | NONE => raise ERR "defineRecursion"
                                  ("no clause for " ^
                                   term_to_string (#cons c))
            (* the caller's variables, in the axiom's places *)
            val (tmS, tyS) = match_term (#capp c) ucapp
            fun theirs tm = Term.subst tmS (Term.inst tyS tm)
            (* the caller's names for the functions, at the parameters
               they take: a clause may call any of them, not only its
               own *)
            val theirNames =
                ListPair.mapEq (fn (v,g) => v |-> g) (hvars, applied)
            fun atFn tm = Term.subst theirNames (theirs tm)
            (* a recursive call arrives as whatever the axiom hands the
               target: the function at an argument, or its map *)
            val cargs' = List.map theirs (#cargs c)
            fun freshen (t, (vs, away)) =
                if is_var t andalso List.exists (aconv t) cargs' then
                  (vs @ [t], away)
                else
                  let val v = numvariant away (mk_var ("r", type_of t))
                  in (vs @ [v], v :: away) end
            val results = List.map atFn (#fargs c)
            val (vs, _) = List.foldl freshen ([], cargs' @ free_varsl results)
                                     results
            val body =
                Term.subst (List.mapPartial
                              (fn (t,v) => if aconv t v then NONE
                                           else SOME (t |-> v))
                              (ListPair.zipEq (results, vs)))
                           urhs
            val _ = List.all (fn f => not (free_in f body)) applied orelse
                    raise ERR "defineRecursion"
                          ("the clause for " ^ term_to_string (#cons c) ^
                           " calls the function on something the axiom" ^
                           " does not hand it: Define is the route for that")
          in
            (#f c, list_mk_abs (vs, body))
          end
      val targets = List.map targetOf axclauses
      fun instOf f = case List.find (fn (g,_) => aconv g f) targets of
                         SOME (_,t) => t
                       | NONE => f
      val solved = CONV_RULE (DEPTH_CONV BETA_CONV)
                             (SPECL (List.map instOf fvars) ax)
      (* a function with parameters is one function of them all *)
      fun skolemAll 0 = ALL_CONV
        | skolemAll m = skolemN (length params) THENC
                        BINDER_CONV (skolemAll (m - 1))
      val closed = if null params then solved
                   else CONV_RULE (skolemAll (length hvars))
                                  (GENL params solved)
      val def = new_specification (name, List.map (#1 o dest_var) fns, closed)
      (* what the axiom's own uniqueness says of the function just
         defined: anything satisfying the same clauses is it *)
      val uniqueness =
          if not unique then NONE
          else
            let
              val insts = List.map instOf fvars
              val uq = CONV_RULE (DEPTH_CONV BETA_CONV)
                         (CONJUNCT2
                            (CONV_RULE Conv.EXISTS_UNIQUE_CONV
                               (SPECL insts (INST_TYPE tyS axiom))))
              val (hs, _) = strip_forall (concl uq)
              val consts =
                  List.map (#1 o strip_comb o lhs o #2 o strip_forall)
                           (strip_conj (#2 (strip_forall (concl def))))
              fun theOne v =
                  case List.find (fn c => #1 (dest_const c) =
                                          #1 (dest_var v)) consts of
                      SOME c => list_mk_comb (c, params)
                    | NONE => raise ERR "defineRecursion" "no constant"
              val hvs = List.take (hs, length hvars)
              val spec = SPECL (hvs @ List.map theOne fns) uq
              val (ant, _) = dest_imp (concl spec)
              val (mine, theirs) = dest_conj ant
            in
              SOME (GENL (params @ hvs)
                         (DISCH mine (MP spec (CONJ (ASSUME mine)
                                                    (SPECL params def)))))
            end
    in
      {definition = def, unique = uniqueness}
    end


(* ----------------------------------------------------------------------
    The size function.

    TypeBase is where a size belongs — it is what `Define` measures a
    well-founded recursion with — so it is defined here, where the entry
    is made, out of what the axiom says.  A constructor's size is one
    plus what each of its arguments contributes, and what an argument
    contributes is its own type's size: `TypeBasePure.type_size_pre`
    builds that term, given the sizes of the type's parameters and of
    the type itself.

    The one difference from `Datatype`'s scheme is where a recursive
    argument sits under another functor.  Its size there is a fold —
    `list_size (rose_size f) l` — and the axiom hands the recursive
    calls over as a *map*, so what is defined is

        rose_size f (RNode a l) = 1 + f a + list_size I (MAP (rose_size f) l)

    which says the same and is the shape the axiom can take.  A type
    whose functor has an argument with no size — a function space, say —
    gets no size at all, and TypeBase is content without one.
   ---------------------------------------------------------------------- *)

fun defineSize {tyname} axiom =
    let
      val (fvars0, body0) = strip_forall (concl axiom)
      val axE = if is_exists1 body0 then
                  GENL fvars0 (EXISTENCE (SPECL fvars0 axiom))
                else axiom
      val num = numSyntax.num
      (* the answers a size gives are numbers.  What the clauses are read
         off is the existence half; what defines the function is the
         axiom as it came, since its uniqueness is what the size's own
         lemma turns on. *)
      val theta =
          let val (hs, _) = strip_exists (#2 (strip_forall (concl axE)))
          in List.map (fn h => #2 (dom_rng (type_of h)) |-> num) hs end
      val axE = INST_TYPE theta axE
      val ax = INST_TYPE theta axiom
      val (hvars, body) = strip_exists (#2 (strip_forall (concl axE)))
      val tys = List.map (#1 o dom_rng o type_of) hvars
      val targs = #Args (dest_thy_type (hd tys))
      val _ = List.all (fn ty => #Args (dest_thy_type ty) = targs) tys orelse
              raise ERR "defineSize"
                    "the family's members take different arguments"
      (* one size for each of the type's arguments, and one function per
         member, which is what is being defined *)
      val fs = List.tabulate
                 (length targs,
                  fn i => mk_var ("f" ^ Int.toString i,
                                  List.nth (targs, i) --> num))
      val sizes =
          List.map (fn ty =>
                       let val nm = #Tyop (dest_thy_type ty) ^ "_size"
                       in
                         mk_var (nm, List.foldr (op -->) (ty --> num)
                                                (List.map type_of fs))
                       end)
                   tys
      fun sizeApp i = list_mk_comb (List.nth (sizes, i), fs)
      (* what a value of a given type contributes *)
      fun theta ty =
          case List.find (fn (t,_) => t = ty)
                         (ListPair.zipEq (targs, fs)) of
              SOME (_, f) => SOME f
            | NONE =>
              case List.find (fn (t,_) => t = ty)
                             (ListPair.zipEq (tys, upto (length tys))) of
                  SOME (_, i) => SOME (sizeApp i)
                | NONE => NONE
      fun sizeOf ty =
          TypeBasePure.type_size_pre theta (TypeBase.theTypeBase()) ty
      fun contribution tm = mk_comb (sizeOf (type_of tm), tm)
      (* the clauses: one per constructor, with the recursive calls
         where the axiom hands them over *)
      fun clauseOf j tm =
          let
            val (args, eq) = strip_forall tm
            val (h, capp) = dest_comb (lhs eq)
            val (_, cargs) = strip_comb capp
            val (_, fargs) = strip_comb (rhs eq)
            val members = ListPair.zipEq (hvars, upto (length tys))
            val i = case List.find (fn (v,_) => aconv v h) members of
                        SOME (_, i) => i
                      | NONE => raise ERR "defineSize" "clause of no member"
            fun atSize tm = Term.subst (ListPair.mapEq
                                          (fn (v,k) => v |-> sizeApp k)
                                          (hvars, upto (length tys)))
                                       tm
            (* an argument the axiom hands a result for contributes
               what that result's own type says of it, and any other
               contributes what its own type says; what a type with no
               size of its own says is nothing *)
            fun beta tm = rhs (concl (QCONV (DEPTH_CONV BETA_CONV) tm))
            fun pieceFor a =
                case List.find (fn t => not (is_var t) andalso free_in a t)
                               fargs of
                    SOME r => beta (contribution (atSize r))
                  | NONE => beta (contribution a)
            val pieces =
                List.filter (fn t => not (aconv t numSyntax.zero_tm))
                            (List.map pieceFor cargs)
            val body =
                case pieces of
                    [] => numSyntax.zero_tm
                  | _ => List.foldl (fn (p,acc) => numSyntax.mk_plus (acc, p))
                                    (numSyntax.term_of_int 1) pieces
          in
            list_mk_forall (cargs,
                            mk_eq (mk_comb (sizeApp i, capp), body))
          end
      val clauses =
          list_mk_conj (List.map (clauseOf 0) (strip_conj body))
      val {definition = def, unique = uq} =
          defineRecursion {name = tyname ^ "_size_def", axiom = ax,
                           def = clauses}
      (* what the entry keeps is the constant the definition made, not
         the variable the clauses were written with *)
      val consts =
          List.map (#1 o strip_comb o lhs o #2 o strip_forall)
                   (strip_conj (#2 (strip_forall (concl def))))
      fun constFor v =
          case List.find (fn c => #1 (dest_const c) = #1 (dest_var v))
                         consts of
              SOME c => c
            | NONE => raise ERR "defineSize" "the definition made no constant"
    in
      SOME {sizes = List.map constFor sizes, definition = def, unique = uq}
    end


(* ----------------------------------------------------------------------
    The lemma that connects the two shapes of a nested size.

    A size of a nested argument is a fold — `mylist_size (rose_size f) l`
    — and what the axiom hands over is a map, so the size defined above
    reads `mylist_size (\x. x) (mylistMAP (rose_size f) l)`.  A measure
    over the operator recursed under is written the first way, so the two
    have to be connected, and as a *termination* simplification: TFL's
    prover keeps its own set and does not read the ambient one.

    No induction is needed.  `\x. T_size (\x. x) (TMAP f x)` satisfies
    the very clauses the size was defined by — the constructor case by
    the map equation, the size equation and the component's own
    composition law — so the axiom's uniqueness says it *is* the size at
    those functions.
   ---------------------------------------------------------------------- *)

fun sizeMapLemma {unique, sizedef, mapeqn, sizes} =
    let
      val (uvars, ubody) = strip_forall (concl unique)
      val (params, hvar) =
          (List.take (uvars, length uvars - 1), List.last uvars)
      (* the map, at the numbers the sizes give *)
      val mapapp = lhs (#2 (strip_forall (hd (strip_conj (concl mapeqn)))))
      val (mtm, margs) = strip_comb mapapp
      val mfs = List.take (margs, length margs - 1)
      val theta = List.map (fn f => #2 (dom_rng (type_of f)) |->
                                    numSyntax.num)
                           mfs
      val mtm = Term.inst theta mtm
      val gs = ListPair.mapEq (fn (f,p) => mk_var (#1 (dest_var f),
                                                   type_of p))
                              (List.map (Term.inst theta) mfs, params)
      val mapAt = list_mk_comb (mtm, gs)
      (* the size at the identity, of what the map produced: the same
         constant, at the numbers the map lands in *)
      val sizetm = List.hd sizes
      val numty = numSyntax.num
      val idfns = List.map (fn _ => let val v = mk_var ("x", numty)
                                    in mk_abs (v, v) end)
                           params
      val x = mk_var ("x", #1 (dom_rng (type_of mapAt)))
      val sizeAtNum =
          let val wanted =
                  List.foldr (op -->)
                             (#2 (dom_rng (type_of mapAt)) --> numty)
                             (List.map type_of idfns)
          in
            Term.inst (match_type (type_of sizetm) wanted) sizetm
          end
      val S = mk_abs (x, list_mk_comb (sizeAtNum,
                                       idfns @ [mk_comb (mapAt, x)]))
      (* what it has to satisfy is the clause set the size was defined
         by, and both sides of each clause reach the same normal form *)
      val spec = SPECL (gs @ [S]) unique
      val (ant, _) = dest_imp (concl spec)
      val rws = [mapeqn, SPEC_ALL sizedef, combinTheory.o_DEF,
                 combinTheory.I_THM]
      fun proveClause cl =
          let val (vs, eq) = strip_forall cl
          in
            GENL vs (normEqWith rws (lhs eq, rhs eq))
          end
      val clauses = LIST_CONJ (List.map proveClause (strip_conj ant))
      val isSize = MP spec clauses
      val y = mk_var ("y", type_of x)
    in
      GENL (gs @ [y])
           (CONV_RULE (LAND_CONV BETA_CONV) (AP_THM isSize y))
    end


(* ----------------------------------------------------------------------
    The TypeBase entry.

    `TypeBasePure.gen_datatype_info` derives the nchotomy, the case
    congruences, distinctness and injectivity from the axiom, the
    induction principle and the case definitions, and marks the members
    of a family after the first as copies of the first's axiom and
    induction — so what the package owes it is those three things, all
    of which the steps above produce.

    What it does not derive is the simplification set for the new
    constants: a type built here comes with a map and a set function per
    argument, whose constructor equations are exactly what a user wants
    the simplifier to know.  They are passed in, one list per type, in
    the order the case definitions come.
   ---------------------------------------------------------------------- *)

fun typeBaseInfo {axiom, induction, case_defs, rewrites} =
    let
      (* TypeBase reads the existence half; the size's own lemma wants
         the uniqueness, so an axiom that carries it is welcome here *)
      val (fvars, body) = strip_forall (concl axiom)
      val existence = if is_exists1 body then
                        GENL fvars (EXISTENCE (SPECL fvars axiom))
                      else axiom
      val tyinfos = TypeBasePure.gen_datatype_info
                      {ax = existence, ind = induction,
                       case_defs = case_defs}
      val _ = length rewrites = length tyinfos orelse
              raise ERR "typeBaseInfo" "a rewrite list per type, please"
      (* the size, which is what a well-founded recursion over the type
         is measured with.  It is defined here because this is where the
         sizes it is built out of are: a component's own, from its
         entry. *)
      val sized =
          case tyinfos of
              [] => NONE
            | ti :: _ =>
              case defineSize {tyname = #2 (TypeBasePure.ty_name_of ti)}
                              axiom of
                  NONE => NONE
                | SOME {sizes, definition, unique} =>
                  SOME (sizes, definition, unique,
                        TypeBasePure.ty_name_of ti)
      (* and what a termination proof over this type needs to know
         about its size, proved and exported where the size is made *)
      val _ =
          case sized of
              SOME (szs, def, SOME uq, (_, tyname)) =>
              let
                fun aboutTy th =
                    let val l = lhs (#2 (strip_forall
                                           (hd (strip_conj (concl th)))))
                    in
                      #Tyop (dest_thy_type (type_of l)) = tyname
                    end handle HOL_ERR _ => false
              in
                case List.find aboutTy (List.concat rewrites) of
                    NONE => ()
                  | SOME mapeqn =>
                    let val nm = tyname ^ "_size_MAP"
                        val lem = sizeMapLemma {unique = uq, sizedef = def,
                                                mapeqn = mapeqn, sizes = szs}
                    in
                      ignore (save_thm (nm, lem))
                    ; TotalDefn.export_termsimp nm
                    end
              end
            | _ => ()
      fun withSize (i, tyi) =
          case sized of
              NONE => tyi
            | SOME (szs, def, _, orig) =>
              let val {convs, rewrs} = TypeBasePure.simpls_of tyi
              in
                TypeBasePure.put_size
                  (List.nth (szs, i),
                   if i = 0 then TypeBasePure.ORIG def
                   else TypeBasePure.COPY (orig, def))
                  (* what add_std_simpls would have put there, had the
                     size been known when the entry was made *)
                  (TypeBasePure.put_simpls
                     {convs = convs, rewrs = rewrs @ [def]} tyi)
              end
      fun withRewrs (tyi, ths) =
          let val {convs, rewrs} = TypeBasePure.simpls_of tyi
          in
            TypeBasePure.put_simpls {convs = convs, rewrs = rewrs @ ths} tyi
          end
    in
      List.tabulate
        (length tyinfos,
         fn i => withSize (i, withRewrs (List.nth (tyinfos, i),
                                         List.nth (rewrites, i))))
    end


(* ----------------------------------------------------------------------
    A specification, as written.

    This is the front end's first half: the `Datatype:` syntax the old
    package takes, through the parser and `parse_bnf`, to what the
    construction wants — a functor per member with the variable standing
    for each member in it, the specification's own type variables, and
    the constructors' names.

    What it does not do yet is any of the rest of what the syntax
    promises: records become a single constructor of their fields, and
    nothing here handles the attributes or the naming conventions the
    old entry points carry.
   ---------------------------------------------------------------------- *)

type spec = {
  tynames : string list,
  params : hol_type list,
  functors : (hol_type * hol_type list) list,
  constructors : string list list,
  fields : string list option list
}

fun parseSpec q : spec =
    let
      val asts = ParseDatatype.hparse (Parse.type_grammar()) q
      val {tynames, params, functors} =
          bnfLib.specToFunctors (parse_bnf.parse2ftor asts)
      (* a record is one constructor of its fields, named the way the
         record apparatus looks it up *)
      fun namesOf (nm, form) =
          case form of
              ParseDatatype.Constructors cs => List.map #1 cs
            | ParseDatatype.Record _ =>
                [TypeBasePure.mk_recordtype_constructor nm]
      fun fieldsOf (_, form) =
          case form of
              ParseDatatype.Constructors _ => NONE
            | ParseDatatype.Record flds => SOME (List.map #1 flds)
    in
      {tynames = tynames, params = params, functors = functors,
       constructors = List.map namesOf asts,
       fields = List.map fieldsOf asts}
    end


(* and the same steps for a family as it comes out of the construction *)
fun familyAxiom css fam recursion =
    familyAxiomOf (familyDefs css fam) recursion
fun familyInduction css fam induction =
    familyInductionOf (familyDefs css fam) induction
fun familySetInduction (fam : family) principle =
    familySetInductionOf fam (#types fam, #cons fam) principle

(* ----------------------------------------------------------------------
    Collapsing a family onto types of its own.

    The construction builds a family from the last member back, each
    member a datatype in the slots of the members before it, so member j
    comes out as an *instance* — `:('b1, 'b1 ft1) ft2` — of an operator
    that takes those slots as arguments.  What the specification says,
    and what a TypeBase entry is keyed on, is an operator over the
    specification's own variables alone.

    So once the family is built, and only then, each member is copied
    onto a type of its own: a new type in bijection with the instance,
    with the constructors and the principle carried across.  Everything
    the transport needs is the functors' composition and identity laws
    with ABS and REP at the slots — the same two laws every step here
    uses.
   ---------------------------------------------------------------------- *)

type collapsed = {
  types : hol_type list,        (* the types of the family's own *)
  abs : term list,              (* into them, out of the instances *)
  rep : term list,
  absrep : thm list,            (* |- ABS o REP = I, and the other way *)
  repabs : thm list,
  cons : term list,             (* the constructors, at the new types *)
  cons_defs : thm list,
  principle : thm               (* and what they satisfy *)
}

fun collapseFamily {tynames} (fam : family) principle : collapsed =
    let
      val n = length (#types fam)
      val params = #params fam
      val pIs = List.map Ify params
      fun famMap j fs = #mkmap (List.nth (#functors fam, j)) (fs @ pIs)
      (* a type of its own per member, in bijection with the instance *)
      fun copy (j, nm) =
          let
            val rep_ty = List.nth (#types fam, j)
            val x = mk_var ("x", rep_ty)
            val P = mk_abs (x, boolSyntax.T)
            val arb = mk_arb rep_ty
            val ex = EXISTS (mk_exists (x, mk_comb (P, x)), arb)
                            (EQT_ELIM (BETA_CONV (mk_comb (P, arb))))
          in
            newtypeTools.rich_new_type
              {tyname = nm, exthm = ex, ABS = nm ^ "_ABS", REP = nm ^ "_REP"}
          end
      val copies = List.tabulate (n, fn j => copy (j, List.nth (tynames, j)))
      val newtys = List.map #newty copies
      val abss = List.map #term_ABS_t copies
      val reps = List.map #term_REP_t copies
      (* the two directions, as compositions: what the maps need *)
      fun compEq (f, g, th) =
          let val x = mk_var ("x", #1 (dom_rng (type_of g)))
          in
            EXT (GEN x
                   (TRANS (TRANS (ISPECL [f, g, x] combinTheory.o_THM)
                                 (SPEC x th))
                          (SYM (ISPEC x combinTheory.I_THM))))
          end
      val absreps =
          List.tabulate
            (n, fn j => compEq (List.nth (abss,j), List.nth (reps,j),
                                GEN_ALL (#absrep_id (List.nth (copies,j)))))
      val repabss =
          List.tabulate
            (n, fn j =>
                  let val th = #repabs_pseudo_id (List.nth (copies,j))
                      val (r, eq) = dest_forall (concl th)
                      val triv = EQT_ELIM (BETA_CONV (lhs (#1 (dest_imp eq)))
                                           handle HOL_ERR _ =>
                                             BETA_CONV (#1 (dest_imp eq)))
                  in
                    compEq (List.nth (reps,j), List.nth (abss,j),
                            GEN r (MP (SPEC r th) triv))
                  end)
      (* the constructors, and what a member's argument does on the way
         across *)
      fun repArgs j = famMap j reps
      fun absArgs j = famMap j abss
      fun defineCons j =
          let
            val nm = List.nth (tynames, j)
            val body = mk_o (List.nth (abss, j),
                             mk_o (List.nth (#cons fam, j), repArgs j))
            val cvar = mk_var (nm ^ "_CONS", type_of body)
          in
            new_definition (nm ^ "_CONS_def", mk_eq (cvar, body))
          end
      val cons_defs = List.tabulate (n, defineCons)
      val conss = List.map (lhs o concl) cons_defs
      (* the two directions pointwise, which is what the constructors'
         definitions unfold against *)
      fun pointwise j =
          let val r = mk_var ("r", List.nth (#types fam, j))
              val th = #repabs_pseudo_id (List.nth (copies, j))
              val (v, eq) = dest_forall (concl th)
              val triv = EQT_ELIM (BETA_CONV (#1 (dest_imp eq)))
          in GEN r (MP (SPEC r th) (INST [v |-> r] triv)) end
      (* |- map gs (map fs x) = map (gs o fs) x, at the family's functor *)
      fun famMapO j (fs,gs) =
          let val Fj = List.nth (#functors fam, j)
              val target = mk_o (famMap j gs, famMap j fs)
              val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                         (PART_MATCH lhs (#mapO Fj) target)
              val srcs = List.map (#1 o dom_rng o type_of) fs
              val af = mk_var("af", typeAtArgs Fj (hd srcs, tl srcs @ params)
                                               (functorTy Fj))
          in
            (af, TRANS (SYM (ISPECL [famMap j gs, famMap j fs, af]
                                    combinTheory.o_THM))
                       (AP_THM th af))
          end
      (* and one direction after the other is nothing at all *)
      fun undo j (fs, gs, rws) =
          let val (af, comp) = famMapO j (fs,gs)
              val ids = [#mapID (List.nth (#functors fam, j)),
                         combinTheory.I_THM]
          in
            (af, CONV_RULE (RAND_CONV (QCONV (PURE_REWRITE_CONV (rws @ ids))))
                           comp)
          end
      fun Fold j = #1 (dom_rng (type_of (absArgs j)))
      fun Fnew j = #1 (dom_rng (type_of (repArgs j)))
      (* what a constructor at the new types is: across, built, and back *)
      fun consAcross j =
          let val af = mk_var ("af", Fnew j)
              val th = PURE_REWRITE_RULE [combinTheory.o_THM]
                         (AP_THM (List.nth (cons_defs, j)) af)
          in (af, th) end

      (* ------------------------------------------------------------
          the principle, carried across
         ------------------------------------------------------------ *)
      val (oldts, _) = strip_forall (concl principle)
      fun answersOf j =
          #1 (dom_rng (#2 (dom_rng (type_of (List.nth (oldts, j))))))
      fun cty j = #2 (dom_rng (#2 (dom_rng (type_of (List.nth (oldts, j))))))
      val newts =
          List.tabulate
            (n, fn j => mk_var (#1 (dest_var (List.nth (oldts, j))),
                                Fnew j --> (answersOf j --> cty j)))
      (* the target the old principle is solved at reads its argument
         across first *)
      fun oldTarget j =
          let val af = mk_var ("af", Fold j)
              val v = mk_var ("v", answersOf j)
              val t = List.nth (newts, j)
          in
            mk_abs (af, mk_abs (v, list_mk_comb (t, [mk_comb (absArgs j, af),
                                                     v])))
          end
      val inst = SPECL (List.tabulate (n, oldTarget)) principle
      (* the equation a function of the new types satisfies *)
      fun newEqTerm j (hs : term list) =
          let val af = mk_var ("af", Fnew j)
          in
            mk_forall (af,
              mk_eq (mk_comb (List.nth (hs, j),
                              mk_comb (List.nth (conss, j), af)),
                     list_mk_comb (List.nth (newts, j),
                                   [af, mk_comb (famMap j hs, af)])))
          end
      (* ------------------------------------------------------------ *)
      val (ws, oldeqs) =
          let val (ws, th) = witnesses ([], CONJUNCT1 inst)
          in (ws, CONJUNCTS th) end
      val newhs = ListPair.mapEq mk_o (ws, reps)
      fun carry j =
          let
            val (af, consth) = consAcross j
            val hj = List.nth (ws, j) and repj = List.nth (reps, j)
            (* what the constructor was applied to, across *)
            val inner = rand (rand (rhs (concl consth)))
            (* the constructor's argument, read across and back *)
            val built = rand (rhs (concl consth))
            val step1 =
                TRANS (ISPECL [hj, repj, mk_comb (List.nth (conss,j), af)]
                              combinTheory.o_THM)
                      (AP_TERM hj (TRANS (AP_TERM repj consth)
                                         (SPEC built (pointwise j))))
            val step2 = TRANS step1 (SPEC inner (List.nth (oldeqs, j)))
            val (_, back) = undo j (reps, abss, absreps)
            val (_, folded) = famMapO j (reps, ws)
            (* the target's own application has to go first: what the
               maps compose to is inside it.  Only that one, though —
               the witnesses below carry targets of their own. *)
            val beta = CONV_RULE (RAND_CONV (RATOR_CONV BETA_CONV THENC
                                             BETA_CONV))
                                 step2
          in
            GEN af (PURE_REWRITE_RULE [back, folded] beta)
          end
      val newEqs = List.tabulate (n, carry)
      val existence =
          let val hvars = List.tabulate
                            (n, fn j => mk_var ("h" ^ Int.toString j,
                                                type_of (List.nth (newhs, j))))
          in
            List.foldr (fn ((hv,h), th) =>
                           EXISTS (mk_exists (hv, subst [h |-> hv] (concl th)),
                                   h) th)
                       (LIST_CONJ newEqs)
                       (ListPair.zipEq (hvars, newhs))
          end
      (* ------------------------------------------------------------
          and only one solution, since a solution over the new types is
          one over the old at the same targets
         ------------------------------------------------------------ *)
      val uniqueness =
          let
            fun vars s = List.tabulate
                           (n, fn j => mk_var (s ^ Int.toString j,
                                               List.nth (newtys,j) --> cty j))
            val (hvs, kvs) = (vars "h", vars "k")
            fun eqsFor vs = list_mk_conj (List.tabulate (n, fn j =>
                                                            newEqTerm j vs))
            val both = ASSUME (mk_conj (eqsFor hvs, eqsFor kvs))
            fun across vs = ListPair.mapEq mk_o (vs, abss)
            fun oldEq (vs, ass) j =
                let
                  val af = mk_var ("af", Fold j)
                  val hj = List.nth (vs, j) and absj = List.nth (abss, j)
                  val (_, there) = undo j (abss, reps, repabss)
                  (* the constructor at the new types, at the argument
                     read across, is the old one read across *)
                  val (afv, consth) = consAcross j
                  val cth = PURE_REWRITE_RULE [there]
                              (INST [afv |-> mk_comb (absArgs j, af)] consth)
                  val old = mk_comb (List.nth (#cons fam, j), af)
                  val step1 = TRANS (ISPECL [hj, absj, old]
                                            combinTheory.o_THM)
                                    (AP_TERM hj (SYM cth))
                  val step2 = TRANS step1
                                (SPEC (mk_comb (absArgs j, af))
                                      (List.nth (ass, j)))
                  val (_, folded) = famMapO j (abss, vs)
                  val step3 = PURE_REWRITE_RULE [folded] step2
                  (* the old principle hands its target the argument
                     unapplied, so put the abstraction back *)
                  val wanted = list_mk_comb (oldTarget j,
                                             [af, rand (rhs (concl step3))])
                in
                  GEN af (TRANS step3
                            (SYM ((RATOR_CONV BETA_CONV THENC BETA_CONV)
                                    wanted)))
                end
            fun oldEqs (vs, ass) = List.tabulate (n, oldEq (vs, ass))
            fun side (vs, half) = LIST_CONJ (oldEqs (vs, CONJUNCTS half))
            val res =
                MP (SPECL (across hvs @ across kvs) (CONJUNCT2 inst))
                   (CONJ (side (hvs, CONJUNCT1 both))
                         (side (kvs, CONJUNCT2 both)))
            (* what that says of the functions themselves *)
            fun strip j =
                let val th = List.nth (CONJUNCTS res, j)
                    val repj = List.nth (reps, j)
                    (* composing with REP on the right leaves the
                       functions themselves *)
                    val cmp = rator (rator (mk_o (lhs (concl th), repj)))
                in
                  PURE_REWRITE_RULE [GSYM combinTheory.o_ASSOC,
                                     List.nth (absreps, j),
                                     combinTheory.I_o_ID]
                                    (AP_THM (AP_TERM cmp th) repj)
                end
          in
            GENL (hvs @ kvs)
                 (DISCH (mk_conj (eqsFor hvs, eqsFor kvs))
                        (LIST_CONJ (List.tabulate (n, strip))))
          end
    in
      {types = newtys, abs = abss, rep = reps, absrep = absreps,
       repabs = repabss, cons = conss, cons_defs = cons_defs,
       principle = GENL newts (CONJ existence uniqueness)}
    end



(* ----------------------------------------------------------------------
    The collapsed family's constructors, one per summand of each
    member's functor — the same split defineConstructors makes for a
    single type, at the types the family was put on.
   ---------------------------------------------------------------------- *)

fun collapsedConstructors names (coll : collapsed) =
    let
      fun member (j, cons) =
          let
            val fty = #1 (dom_rng (type_of cons))
            val summands = sumSyntax.strip_sum fty
            val nms = List.nth (names, j)
            val _ = length nms = length summands orelse
                    raise ERR "collapsedConstructors"
                          ("member " ^ Int.toString j ^ " has " ^
                           Int.toString (length summands) ^ " constructors")
            val newty = #2 (dom_rng (type_of cons))
            fun mkOne (i, nm) =
                let
                  val facs = factorsOf (List.nth (summands, i))
                  val args = List.tabulate
                               (length facs,
                                fn k => mk_var ("a" ^ Int.toString k,
                                                List.nth (facs, k)))
                  val tup = if null args then oneSyntax.one_tm
                            else pairSyntax.list_mk_pair args
                  val cvar = mk_var (nm, List.foldr (op -->) newty facs)
                in
                  new_definition
                    (nm ^ "_def",
                     mk_eq (list_mk_comb (cvar, args),
                            mk_comb (cons, mkInj summands i tup)))
                end
            val defs = List.tabulate (length nms,
                                      fn i => mkOne (i, List.nth (nms, i)))
          in
            {constructors = List.map (#1 o strip_comb o lhs o #2 o strip_forall
                                      o concl)
                                     defs,
             defs = defs}
          end
    in
      List.tabulate (length (#cons coll),
                     fn j => member (j, List.nth (#cons coll, j)))
    end


(* ----------------------------------------------------------------------
    The BNF structure of a type defined as a copy of another.

    A collapsed member is a new type in bijection with a composite of
    functors already in the database — `:('b1, 'b1 ft1) ft2` is one — and
    a composite's structure is what deriveBNFn gives.  So the new type's
    map is that composite's map conjugated by the bijection, its set
    functions are the composite's after the representation, and every law
    is the composite's with `REP o ABS = I` or `ABS o REP = I` applied in
    the middle.

    Nothing here is particular to a family: this is what any type defined
    as a copy of a functor needs in order to be one itself.
   ---------------------------------------------------------------------- *)

type copied_bnf = {
  key : KernelSig.kernelname,
  info : thm bnfBase_dtype.info,
  map_def : thm,          (* |- MAP f.. = ABS o map f.. o REP *)
  set_defs : thm list,    (* |- SETi = seti o REP *)
  relator_def : thm
}

fun transportBNF {abs, rep, absrep, repabs} (bnf : bnfLib.derived_bnfn)
    : copied_bnf =
    let
      val (rep_ty, newty) = dom_rng (type_of abs)
      val {Thy, Tyop, Args} = dest_thy_type newty
      val largs = #lives bnf
      val n = length largs
      val avoid = type_vars newty @ type_vars rep_ty
      val tvs = freshTys "'c" n avoid
      val uvs = freshTys "'d" n (avoid @ tvs)
      fun tyTheta tys = ListPair.mapEq (fn (l,t) => l |-> t) (largs, tys)
      fun atLargs tys ty = type_subst (tyTheta tys) ty
      fun instLargs tys tm = Term.inst (tyTheta tys) tm
      fun numbered nm tys =
          List.tabulate (length tys,
                         fn i => mk_var (if n = 1 then nm
                                         else nm ^ Int.toString (i + 1),
                                         List.nth (tys, i)))
      val fs = numbered "f" (ListPair.mapEq (op -->) (largs, tvs))
      val gs = numbered "g" (ListPair.mapEq (op -->) (largs, tvs))
      val fs' = numbered "g" (ListPair.mapEq (op -->) (tvs, uvs))
      (* the bijection, pointwise and at whatever instance is wanted *)
      fun pointwiseOf th =
          let val l = lhs (concl th)
              val (f, g) = (rand (rator l), rand l)
              val x = mk_var ("x", #1 (dom_rng (type_of g)))
          in
            GEN x (TRANS (TRANS (SYM (ISPECL [f,g,x] combinTheory.o_THM))
                                (AP_THM th x))
                         (ISPEC x combinTheory.I_THM))
          end
      val absrepP = pointwiseOf absrep     (* |- !x. ABS (REP x) = x *)
      val repabsP = pointwiseOf repabs     (* |- !r. REP (ABS r) = r *)
      fun absAt tys = instLargs tys abs
      fun repAt tys = instLargs tys rep

      (* ------------------------------------------------------------
          the map and the set functions
         ------------------------------------------------------------ *)
      val mapname = Tyop ^ "MAP"
      val mapty = List.foldr (op -->) (newty --> atLargs tvs newty)
                             (List.map type_of fs)
      val map_def =
          new_definition
            (mapname ^ "_def",
             mk_eq (list_mk_comb (mk_var (mapname, mapty), fs),
                    mk_o (absAt tvs, mk_o (#mkmap bnf fs, repAt largs))))
      val MAPtm = repeat rator (lhs (#2 (strip_forall (concl map_def))))
      fun mapTheta hs =
          let val srcs = List.map (#1 o dom_rng o type_of) hs
              val tgts = List.map (#2 o dom_rng o type_of) hs
          in
            tyTheta srcs @ ListPair.mapEq (fn (t,u) => t |-> u) (tvs, tgts)
          end
      fun mapApp hs = list_mk_comb (Term.inst (mapTheta hs) MAPtm, hs)
      (* |- MAP hs x = ABS (map hs (REP x)), at the variable it names.
         Only the compositions this definition introduced are unfolded:
         the map and the set functions underneath may be compositions
         themselves, and those have to stay as the database has them. *)
      val unfoldO = REWR_CONV combinTheory.o_THM
      fun mapPt hs =
          let val srcs = List.map (#1 o dom_rng o type_of) hs
              val x = mk_var ("x", atLargs srcs newty)
          in
            (x, CONV_RULE (RAND_CONV (unfoldO THENC RAND_CONV unfoldO))
                          (AP_THM (SPECL hs (INST_TYPE (mapTheta hs) map_def))
                                  x))
          end
      fun setname i = Tyop ^ "SET" ^ (if n = 1 then "" else
                                      Int.toString (i + 1))
      val set_defs =
          List.map (fn i =>
                       let val body = mk_o (List.nth (#sets bnf, i), rep)
                       in
                         new_definition
                           (setname i ^ "_def",
                            mk_eq (mk_var (setname i, type_of body), body))
                       end)
                   (upto n)
      fun setTm i = lhs (concl (List.nth (set_defs, i)))
      fun setPt tys i =
          let val x = mk_var ("x", atLargs tys newty)
              val th = INST_TYPE (tyTheta tys) (List.nth (set_defs, i))
          in
            (x, CONV_RULE (RAND_CONV unfoldO) (AP_THM th x))
          end

      (* ------------------------------------------------------------
          the laws, each the composite's with the bijection undone in
          the middle
         ------------------------------------------------------------ *)
      val Is = List.map Ify largs
      val mapID =
          let val (x, pt) = mapPt Is
          in
            EXT (GEN x
                   (TRANS (PURE_REWRITE_RULE [#mapID bnf, combinTheory.I_THM,
                                              absrepP] pt)
                          (SYM (ISPEC x combinTheory.I_THM))))
          end
      (* |- map ks (map hs y) = map (ks o hs) y, underneath *)
      fun underO (hs, ks) y =
          let val th = PART_MATCH lhs (#mapO bnf)
                                  (mk_o (#mkmap bnf ks, #mkmap bnf hs))
          in
            TRANS (SYM (ISPECL [#mkmap bnf ks, #mkmap bnf hs, y]
                               combinTheory.o_THM))
                  (AP_THM th y)
          end
      val mapO =
          let
            val comps = ListPair.mapEq mk_o (fs', fs)
            val (x, ptf) = mapPt fs
            val (y, ptg) = mapPt fs'
            val (z, ptc) = mapPt comps
            val repx = mk_comb (repAt largs, x)
            val inner = rhs (concl ptf)
            val step =
                TRANS (ISPECL [mapApp fs', mapApp fs, x] combinTheory.o_THM)
                      (TRANS (AP_TERM (mapApp fs') ptf)
                             (INST [y |-> inner] ptg))
            val undone = PURE_REWRITE_RULE [repabsP] step
          in
            EXT (GEN x
                   (TRANS (TRANS undone
                                 (AP_TERM (absAt uvs) (underO (fs, fs') repx)))
                          (SYM (INST [z |-> x] ptc))))
          end
      (* the database keeps this one applied, and quantified *)
      fun mapIMAGE i =
          let
            val (x, ptf) = mapPt fs
            val (sx, ptsx) = setPt largs i
            val (sy, ptsy) = setPt tvs i
            val seti = List.nth (#sets bnf, i)
            val setiAt = Term.inst (tyTheta tvs) seti
            val repx = mk_comb (repAt largs, x)
            val fi = List.nth (fs, i)
            val imgtm = rator (pred_setSyntax.mk_image
                                 (fi, mk_comb (seti, repx)))
            (* what naturality says underneath *)
            val under =
                let val th = PART_MATCH lhs (List.nth (#mapIMAGE bnf, i))
                                        (mk_o (setiAt, #mkmap bnf fs))
                in
                  TRANS (SYM (ISPECL [setiAt, #mkmap bnf fs, repx]
                                     combinTheory.o_THM))
                        (TRANS (AP_THM th repx)
                               (ISPECL [imgtm, seti, repx] combinTheory.o_THM))
                end
            (* the set of the mapped value, back down to the
               representation and up again *)
            val down =
                TRANS (INST [sy |-> mk_comb (mapApp fs, x)] ptsy)
                      (AP_TERM setiAt
                         (PURE_REWRITE_RULE [repabsP]
                                            (AP_TERM (repAt tvs) ptf)))
          in
            GENL (fs @ [x])
                 (TRANS (TRANS down under)
                        (AP_TERM imgtm (SYM (INST [sx |-> x] ptsx))))
          end
      val mapCONG =
          let
            val x = mk_var ("x", newty)
            val repx = mk_comb (repAt largs, x)
            fun hypOf i =
                let val a = mk_var ("a", List.nth (largs, i))
                in
                  mk_forall (a,
                    mk_imp (pred_setSyntax.mk_in (a, mk_comb (setTm i, x)),
                            mk_eq (mk_comb (List.nth (fs,i), a),
                                   mk_comb (List.nth (gs,i), a))))
                end
            val hyps = list_mk_conj (List.tabulate (n, hypOf))
            val ass = CONJUNCTS (ASSUME hyps)
            (* what the hypotheses say of the representation *)
            fun under i =
                PURE_REWRITE_RULE [#2 (setPt largs i)] (List.nth (ass, i))
            val inst =
                PART_MATCH (#2 o dest_imp) (#mapCONG bnf)
                           (mk_eq (mk_comb (#mkmap bnf fs, repx),
                                   mk_comb (#mkmap bnf gs, repx)))
            val same = MP inst (LIST_CONJ (List.tabulate (n, under)))
            val (_, ptf) = mapPt fs
            val (_, ptg) = mapPt gs
          in
            GENL (fs @ gs @ [x])
                 (DISCH hyps (TRANS (TRANS ptf (AP_TERM (absAt tvs) same))
                                    (SYM ptg)))
          end
      fun bndthm i =
          let val (x, pt) = setPt largs i
              val th = SPEC (mk_comb (repAt largs, x))
                            (List.nth (#bndthms bnf, i))
          in
            GEN x (PURE_REWRITE_RULE [SYM pt] th)
          end
      (* |- SETi (ABS r) = seti r, which is what a witness needs *)
      fun setAbs i r =
          let val (x, pt) = setPt largs i
              val abs_r = mk_comb (absAt largs, r)
          in
            PURE_REWRITE_RULE [repabsP] (INST [x |-> abs_r] pt)
          end
      fun witOf (w, wth) =
          let
            val as_ = #1 (strip_forall (concl wth))
            val wapp = list_mk_comb (w, as_)
            val body = mk_comb (absAt largs, wapp)
            val conjs = CONJUNCTS (SPECL as_ wth)
            fun atArg i =
                PURE_ONCE_REWRITE_RULE [SYM (setAbs i wapp)]
                                       (List.nth (conjs, i))
            val restate = bnfLib.unbeta_at (LAND_CONV o RAND_CONV) as_ body
          in
            (list_mk_abs (as_, body),
             GENL as_ (LIST_CONJ (List.map (restate o atArg) (upto n))))
          end
      fun inhOf i =
          case List.nth (#inhabits bnf, i) of
              NONE => raise ERR "transportBNF"
                            ("argument " ^ Int.toString (i + 1) ^
                             " of the functor is never inhabited")
            | SOME (t, th) =>
              let
                val v = #1 (dest_forall (concl th))
                val tapp = mk_comb (t, v)
                val body = mk_comb (absAt largs, tapp)
                val mem = PURE_ONCE_REWRITE_RULE [SYM (setAbs i tapp)]
                                                 (SPEC v th)
              in
                (mk_abs (v, body),
                 GEN v (bnfLib.unbeta_at (RAND_CONV o RAND_CONV) [v] body mem))
              end

      (* ------------------------------------------------------------
          the relator, as the map and the set functions determine it
         ------------------------------------------------------------ *)
      val relator_def =
          let
            val prods = ListPair.mapEq pairSyntax.mk_prod (largs, tvs)
            val zty = atLargs prods newty
            val z = mk_var ("z", zty)
            val x = mk_var ("x", newty)
            val y = mk_var ("y", atLargs tvs newty)
            val Rs = numbered "R" (ListPair.mapEq
                                     (fn (a,c) => a --> (c --> bool))
                                     (largs, tvs))
            fun proj tm i =
                Term.inst (match_type (#1 (dom_rng (type_of tm)))
                                      (List.nth (prods, i)))
                          tm
            fun projs tm = List.map (proj tm) (upto n)
            fun conjOf i =
                let val pv = mk_var ("p", List.nth (prods, i))
                in
                  mk_forall (pv,
                    mk_imp (pred_setSyntax.mk_in
                              (pv, mk_comb (instLargs prods (setTm i), z)),
                            list_mk_comb (List.nth (Rs,i),
                                          [pairSyntax.mk_fst pv,
                                           pairSyntax.mk_snd pv])))
                end
            fun mapped tm = mk_comb (mapApp (projs tm), z)
            val body =
                mk_exists (z,
                  list_mk_conj
                    (List.map conjOf (upto n) @
                     [mk_eq (mapped pairSyntax.fst_tm, x),
                      mk_eq (mapped pairSyntax.snd_tm, y)]))
            val relty = List.foldr (op -->) (newty --> (atLargs tvs newty -->
                                                        bool))
                                   (List.map type_of Rs)
          in
            new_definition (Tyop ^ "REL_def",
                            mk_eq (mk_var (Tyop ^ "REL", relty),
                                   list_mk_abs (Rs @ [x,y], body)))
          end

      (* ------------------------------------------------------------
          and the database's canonical form
         ------------------------------------------------------------ *)
      fun canonvar i = mk_vartype ("'a" ^ Int.toString (i + 1))
      val canon = ListPair.mapEq (fn (l,i) => l |-> canonvar i)
                                 (largs, upto n)
      val _ = List.all (fn {residue,...} =>
                           not (Lib.mem residue (type_vars newty)) orelse
                           Lib.mem residue largs)
                       canon orelse
              raise ERR "transportBNF"
                    "a dead argument of the type is named like a live one"
      val cinst = Term.inst canon
      val cthm = INST_TYPE canon
    in
      {key = {Thy = Thy, Name = Tyop},
       map_def = map_def, set_defs = set_defs, relator_def = relator_def,
       info = bnfBase.bI {
         bnd = cinst (#bnd bnf),
         bndthms = List.map (cthm o bndthm) (upto n),
         canontype = type_subst canon newty,

         map = cinst MAPtm,
         mapID = cthm mapID,
         mapO = cthm mapO,
         mapIMAGE = List.map (cthm o mapIMAGE) (upto n),
         mapCONG = cthm mapCONG,

         relator = cinst (lhs (concl relator_def)),
         set = List.map (cinst o setTm) (upto n),

         wits = List.map ((fn (t,th) => (cinst t, cthm th)) o witOf)
                         (#wits bnf),
         inhabits = List.map ((fn (t,th) => (cinst t, cthm th)) o inhOf)
                             (upto n)
       }}
    end


(* ----------------------------------------------------------------------
    The collapsed family's map, one constructor at a time.

    A collapsed member's map is defined through the bijection, so what it
    does at a constructor is what the member's own map does at the
    constructor underneath.  That is reached by unfolding — the
    constructors, the bijection and the members' own equations — and what
    the unfolding leaves is folded back by the definitions themselves,
    normalised the same way, with the representation's own naturality to
    put a member's map back together.

    The set functions are not here yet: their two sides normalise to
    different shapes, because the one that goes through the map pushes
    the representation inside the sets and the other does not.  Closing
    that wants the components' naturality in the set normaliser, which
    is the same polish the pair's set equations are waiting for.
   ---------------------------------------------------------------------- *)

fun collapsedEqns (coll : collapsed) (fam : family) (cbnfs : copied_bnf list)
                  (ccs : {constructors : term list, defs : thm list} list) =
    let
      val n = length (#types coll)
      (* the definitions, applied: a composition the definition made is
         unfolded, and one the database keeps is left alone *)
      val unfoldO = REWR_CONV combinTheory.o_THM
      (* the definition's own compositions, and only those: a map or a
         set function underneath may be a composition itself, and the
         database keeps it that way *)
      fun applied k th =
          let val l = lhs (concl (SPEC_ALL th))
              val x = mk_var ("x", #1 (dom_rng (type_of l)))
              fun unfoldN 1 = unfoldO
                | unfoldN m = unfoldO THENC RAND_CONV (unfoldN (m - 1))
          in
            CONV_RULE (RAND_CONV (unfoldN k)) (AP_THM (SPEC_ALL th) x)
          end
      fun pointwiseOf th =
          let val l = lhs (concl th)
              val (f, g) = (rand (rator l), rand l)
              val x = mk_var ("r", #1 (dom_rng (type_of g)))
          in
            GEN x (TRANS (TRANS (SYM (ISPECL [f,g,x] combinTheory.o_THM))
                                (AP_THM th x))
                         (ISPEC x combinTheory.I_THM))
          end
      val consP = List.map (applied 2) (#cons_defs coll)
      val mapP = List.map (applied 2 o #map_def) cbnfs
      val setP = List.concat (List.map (List.map (applied 1) o #set_defs)
                                       cbnfs)
      val repabsP = List.map pointwiseOf (#repabs coll)
      fun memberOf j =
          case List.nth (#maps fam, j) of
              SOME r => r
            | NONE => raise ERR "collapsedEqns" "a member with nothing to map"
      val memberEqns =
          List.concat (List.map (fn j => #map_thm (memberOf j) ::
                                         #set_thms (memberOf j))
                                (upto n))
      val unfoldRWs = List.concat (List.map #defs ccs) @ consP @ mapP @ setP @
                      repabsP @ memberEqns
      (* the sets of a constructor's arguments come out grouped by where
         the member's own set function found them; union is associative
         and commutative, and that is the whole difference *)
      val acRWs = unfoldRWs @ [bnfFixBNFTheory.EQUAL_SING,
                               simpLib.AC pred_setTheory.UNION_ASSOC
                                          pred_setTheory.UNION_COMM]
      (* the database with the collapsed types in it, which is what says
         what an argument's own set function is *)
      val db = List.foldl (fn (r, d) => bnfBase.insert (#key r, #info r) d)
                          (#db fam) cbnfs
      fun norm tm =
          rhs (concl (QCONV (simpLib.SIMP_CONV set_ss
                               (setRWs @ shapeRWs @ unfoldRWs))
                            tm))
      fun normth tm =
          QCONV (simpLib.SIMP_CONV set_ss (setRWs @ shapeRWs @ unfoldRWs)) tm
      (* what the representation does to a mapped value: this is what
         puts a member's own map back together underneath a
         constructor, and it cannot be in the unfolding — the map's
         definition reads the other way *)
      val absrepP = List.map pointwiseOf (#absrep coll)
      fun natREP j =
          let
            val ap = List.nth (mapP, j)
            val body = rhs (concl ap)
            val absC = rator body
            val (rC, tC) = dom_rng (type_of absC)
            val repj = List.nth (#rep coll, j)
            val repC = Term.inst (match_type (type_of repj) (tC --> rC)) repj
            val step = AP_TERM repC ap
            val red = PART_MATCH lhs (List.nth (repabsP, j))
                                 (rhs (concl step))
          in
            GEN_ALL (SYM (TRANS step red))
          end
      (* the definitions themselves, normalised the same way: what
         folds the result back up *)
      val folds =
          List.map (GSYM o normth)
            (List.concat
               (List.map (fn cs => List.map (lhs o #2 o strip_forall o concl)
                                            (#defs cs))
                         ccs) @
             List.map (lhs o concl o SPEC_ALL) (mapP @ setP))
      fun eqnsFor j =
          let
            val mapdef = #map_def (List.nth (cbnfs, j))
            val mapapp = lhs (concl (SPEC_ALL mapdef))
            val fvars = #1 (strip_forall (concl mapdef))
            val defs = #defs (List.nth (ccs, j))
            val backs = List.tabulate (n, natREP) @ absrepP @ folds
            fun capp def = lhs (#2 (strip_forall (concl def)))
            fun args def = #2 (strip_comb (capp def))
            fun mapEqn def =
                GENL (fvars @ args def)
                     (REWRITE_RULE backs (normth (mk_comb (mapapp, capp def))))
            (* what each of the constructor's arguments contributes to
               the i-th set: whatever that argument's own type's set
               function says, which is a composite the database can
               derive — a member's own for a member, {a} for a
               parameter, and nothing for a type the parameter does not
               occur in *)
            fun setOf ty i =
                List.nth (#sets (bnfLib.deriveBNFn db (#params fam) ty), i)
            fun setEqn i def =
                let
                  val as_ = args def
                  val setj = lhs (concl (List.nth
                                    (#set_defs (List.nth (cbnfs, j)), i)))
                  val pieces = List.map (fn a => mk_comb (setOf (type_of a) i,
                                                          a))
                                        as_
                  val rhs =
                      case List.rev pieces of
                          [] => pred_setSyntax.mk_empty
                                  (List.nth (#params fam, i))
                        | p::ps => List.foldl pred_setSyntax.mk_union p ps
                  (* the composite's own set term is what says what an
                     argument contributes; what it *says* is tidier *)
                  val tidy = [bnfPrelimsTheory.BIMG_EQUAL,
                              combinTheory.I_o_ID,
                              bnfFixBNFTheory.EQUAL_SING,
                              pred_setTheory.INSERT_UNION_EQ,
                              pred_setTheory.UNION_EMPTY]
                in
                  (* aimed at the right-hand side: `(=) a = {a}` would
                     otherwise rewrite the equation itself *)
                  GENL as_
                       (CONV_RULE (RAND_CONV (QCONV (PURE_REWRITE_CONV tidy)))
                          (normEqWith acRWs (mk_comb (setj, capp def), rhs)))
                end
          in
            {map_eqns = LIST_CONJ (List.map mapEqn defs),
             set_eqns = List.tabulate
                          (length (#set_defs (List.nth (cbnfs, j))),
                           fn i => LIST_CONJ (List.map (setEqn i) defs))}
          end
    in
      List.tabulate (n, eqnsFor)
    end


end
