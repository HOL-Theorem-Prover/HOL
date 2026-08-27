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
                val def = new_definition
                            (nm ^ "_def",
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
      fun upto k = List.tabulate (k, fn i => i)

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
         siblings = [],

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
  recursion : thm, induction : thm    (* and the two principles in full *)
}

(* |- t1 = t2, when both sides normalise to the same thing.  Two set
   terms built by nesting one functor inside another are equal by the
   algebra of BIMG and the lifted union; normalising both is how a driver
   sees that without running a tactic. *)
val normRWs = setRWs @ [BIGUNION_IMAGE_UNION, BIGUNION_IMAGE_BIGUNION]
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
       induction = induction}
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

end
