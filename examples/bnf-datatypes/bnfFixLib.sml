structure bnfFixLib :> bnfFixLib =
struct

open HolKernel boolLib
open bnfInitialTheory

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
fun functorAt bnf ty = type_subst [recTy bnf |-> ty] (functorTy bnf)

fun setOp bnf ty = Term.inst [recTy bnf |-> ty] (hd (#sets bnf))
(* the map in the recursive argument alone *)
fun mkmapA bnf f = #mkmap bnf (f :: List.map Ify (paramTys bnf))
fun mapOp bnf (ty1,ty2) =
    let val f = mk_var("f", ty1 --> ty2)
    in
      mk_abs(f, mkmapA bnf f)
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

fun MapIdThm bnf ty =
    let val idmap = mkmapA bnf (Ify ty)
        val th = PART_MATCH lhs (#mapID bnf) idmap  (* |- map I .. I = I *)
        val x = mk_var("x", functorAt bnf ty)
        val th = TRANS (AP_THM th x) (ISPEC x combinTheory.I_THM)
    in
      byDefn MapId_def [mapOp bnf (ty,ty)] (GEN x th)
    end

fun MapCompThm bnf (t1,t2,t3) =
    let val f = mk_var("f", t1 --> t2)
        val g = mk_var("g", t2 --> t3)
        (* the stored law is point-free: map g o map f = map (g o f) *)
        val target = mk_o (mkmapA bnf g, mkmapA bnf f)
        (* the parameters' functions are matched to I on the left, so the
           right-hand side has I o I in their positions *)
        val th = PURE_REWRITE_RULE [combinTheory.I_o_ID]
                                   (PART_MATCH lhs (#mapO bnf) target)
        val x = mk_var("x", functorAt bnf t1)
        val th = TRANS (SYM (ISPECL [mkmapA bnf g, mkmapA bnf f, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
    in
      byDefn MapComp_def [mapOp bnf (t1,t2), mapOp bnf (t2,t3),
                          mapOp bnf (t1,t3)]
             (GENL [f,g,x] th)
    end

fun NaturalThm bnf (t1,t2) =
    let val f = mk_var("f", t1 --> t2)
        val target = mk_o (setOp bnf t2, mkmapA bnf f)
        (* |- set2 o map f .. = IMAGE f o set1 *)
        val th = PART_MATCH lhs (hd (#mapIMAGE bnf)) target
        val x = mk_var("x", functorAt bnf t1)
        val rhs0 = rhs (concl th)
        val imgf = rand (rator rhs0) and set1 = rand rhs0
        val th = TRANS (SYM (ISPECL [setOp bnf t2, mkmapA bnf f, x]
                                    combinTheory.o_THM))
                       (AP_THM th x)
        val th = TRANS th (ISPECL [imgf, set1, x] combinTheory.o_THM)
    in
      byDefn Natural_def [mapOp bnf (t1,t2), setOp bnf t1, setOp bnf t2]
             (GENL [f,x] th)
    end

(* |- !a. a IN s ==> t a = t a, the hypothesis a congruence makes about
   an argument whose two functions are the same *)
fun trivial_cong c =
    let val (a, body) = dest_forall c
        val (mem, eq) = dest_imp body
    in
      GEN a (DISCH mem (REFL (lhs eq)))
    end

fun MapCongThm bnf (t1,t2) =
    let val f = mk_var("f", t1 --> t2)
        val x = mk_var("x", functorAt bnf t1)
        val target = mk_comb (mkmapA bnf f, x)
        (* |- (!a. a IN set₁ x ==> f a = g a) /\ .. ==> map f .. x = map g .. x,
           one conjunct per argument.  Matching the conclusion's left-hand
           side fixes each f; the g's are read off the conjuncts, whose
           shape says which is which. *)
        val th = PART_MATCH (lhs o snd o dest_imp) (#mapCONG bnf) target
        val conjs = strip_conj (#1 (dest_imp (concl th)))
        val gs = List.map (rator o rhs o #2 o dest_imp o #2 o dest_forall)
                          conjs
        (* the parameters are carried along by I, so their congruence
           hypotheses are about I on both sides and hold outright *)
        val th = INST (List.map (fn g => g |-> Ify (#1 (dom_rng (type_of g))))
                                (tl gs))
                      th
        val conjs = strip_conj (#1 (dest_imp (concl th)))
        val hyp = hd conjs
        val th = DISCH hyp
                       (MP th (LIST_CONJ (ASSUME hyp ::
                                          List.map trivial_cong (tl conjs))))
    in
      byDefn MapCong_def [mapOp bnf (t1,t2), setOp bnf t1]
             (GENL [f, hd gs, x] th)
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

fun defineConstructors names bnf fix =
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

end
