(* Checked binary short-Weierstrass scalar evaluation.
   See ellipticCertificateLib.sig for theorem inputs and tactic branch layout.
   BINARY_SCALAR_CONV accepts an addition conversion and curve/membership
   proofs over any matching field representation. SCALAR_CONV specializes to
   literal GF p points using prime, curve and point-membership theorems.
   The *_CERTIFICATE_TAC interfaces expose bounded milestone or operation
   goals, discharged by matching *_STEP_TAC calls; proposed trajectories and
   modular inverses are untrusted. Successful conversion equalities are cached
   per converter, and input theorem hypotheses remain part of the proof. *)

structure ellipticCertificateLib :> ellipticCertificateLib =
struct

open HolKernel boolLib bossLib boolSyntax
open shortWeierstrassTheory shortWeierstrassGroupTheory ellipticTorsionTheory
open ellipticCertificatesTheory fieldInstancesTheory

val ERR = mk_HOL_ERR "ellipticCertificateLib" "SCALAR_CONV"

fun integer tm = Arbnum.toLargeInt (numSyntax.dest_numeral tm)

fun numeral n = numSyntax.mk_numeral (Arbnum.fromLargeInt n)
val infinity = ``ECInfinity:num sw_point``
val affine = ``ECAffine:num->num->num sw_point``
val scalar_pattern =
  ``(sw_group (GF p) (a:num) (b:num)).exp (P:num sw_point) n``
val scalar_head = fst (strip_comb scalar_pattern)
val inverse_head = fst (strip_comb ``(GF (p:num)).prod.inv (x:num)``)

fun scalar_key tm =
  let val (head,args) = strip_comb tm in
    if is_const head andalso same_const head scalar_head andalso length args = 3
    then SOME tm else NONE
  end


fun point tm =
  if aconv tm infinity then NONE
  else
    case strip_comb tm of
      (c,[x,y]) =>
        if same_const c affine
        then SOME (integer x,integer y)
        else raise ERR "Expected a literal curve point"
    | _ => raise ERR "Expected a literal curve point"

(* Candidate generation is untrusted. sw_GF_prod_inv_witness checks the
   residue bounds and product, so neither Euclid nor its result is an oracle. *)
fun inverse p x =
  let
    fun euclid (a,b,u,v) =
      if b = 0 then u
      else euclid (b,IntInf.mod(a,b),v,u - IntInf.div(a,b) * v)
  in IntInf.mod (euclid (x,p,1,0),p) end

(* Field-independent binary proof; the supplied addition conversion returns
   kernel equalities, so alternative concrete field representations share it. *)
fun binary_scalar_conv_from seed add_conv curve member tm =
  let
    val (theta,types) = match_term
      ``(sw_group (r:'a field) a b).exp P n`` tm
    fun value t = Term.subst theta (Term.inst types t)
    val r = value ``r:'a field``
    val a = value ``a:'a``
    val b = value ``b:'a``
    val P = value ``P:'a sw_point``
    val n = integer (value ``n:num``)
    val premises = CONJ curve member
    val _ =
      if aconv (concl premises)
        ``ShortWeierstrassCurve ^r ^a ^b /\ ^P IN sw_points ^r ^a ^b``
      then () else raise ERR "Mismatched curve or point certificate"
    fun scalar k =
      let val expression =
        ``(sw_group ^r ^a ^b).exp ^P ^(numeral k)``
      in
        case seed expression of
          SOME th => th
        | NONE =>
        if k=0 then REWRITE_CONV [sw_scalar_zero] expression
        else
          let
            val half = IntInf.div(k,2)
            val even = IntInf.mod(k,2)=0
            val previous = if even then NONE else seed
              ``(sw_group ^r ^a ^b).exp ^P ^(numeral (k-1))``
          in
            case previous of
              SOME prev =>
                let
                  (* An operation milestone supplies the preceding even
                     scalar, so this odd transition checks only one add. *)
                  val law = MP (PART_MATCH (lhs o rand) sw_scalar_add
                    ``(sw_group ^r ^a ^b).exp ^P (1 + ^(numeral (k-1)))``)
                    premises
                  val one = MP (PART_MATCH (lhs o rand) sw_scalar_one
                    ``(sw_group ^r ^a ^b).exp ^P 1``) premises
                  val normalized = CONV_RULE
                    (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) law
                  val substituted = CONV_RULE
                    (RAND_CONV
                      (LAND_CONV (REWR_CONV one) THENC
                       RAND_CONV (REWR_CONV prev))) normalized
                in TRANS substituted (add_conv (rhs (concl substituted))) end
            | NONE =>
                let
                  val binary = if even then sw_scalar_double
                               else sw_scalar_double_add
                  val law = MP
                    (ISPECL [r,a,b,P,numeral half] binary) premises
                  val normalized = CONV_RULE
                    (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) law
                  val substituted = SUBS [scalar half] normalized
                  (* Preserve the binary converter when no adjacent
                     operation milestone is supplied. *)
                  val evaluate = if even then add_conv
                                 else RAND_CONV add_conv THENC add_conv
                  val evaluated = evaluate (rhs (concl substituted))
                in TRANS substituted evaluated end
          end
      end
  in scalar n end

fun binary_scalar_conv add_conv curve member =
  binary_scalar_conv_from (K NONE) add_conv curve member

(* The candidate trajectory is not a proof. Each milestone becomes a separate
   kernel-checked goal, with only its preceding milestone available as a
   hypothesis. Operation mode prepares at most width complete binary bits,
   resuming from an assumed prefix; window mode retains its original API. *)
fun scalar_certificate_tac operations width candidate curve member (asl,w) _ =
  let
    val _ = if width > 0 then () else raise ERR "Nonpositive scalar window"
    val scalar = find_term (fn t => isSome (scalar_key t)) w
    val (theta,types) = match_term
      ``(sw_group (r:'a field) a b).exp P n`` scalar
    fun value t = Term.subst theta (Term.inst types t)
    val r = value ``r:'a field``
    val a = value ``a:'a``
    val b = value ``b:'a``
    val P = value ``P:'a sw_point``
    val n = integer (value ``n:num``)
    val _ =
      if aconv (concl (CONJ curve member))
        ``ShortWeierstrassCurve ^r ^a ^b /\ ^P IN sw_points ^r ^a ^b``
      then () else raise ERR "Mismatched curve or point certificate"
    val zero = Term.inst [alpha |-> type_of a] ``ECInfinity:'a sw_point``
    (* Parse the typed prefixes once, not once per proposed operation. The
       trajectory still constructs only untrusted terms, never proofs. *)
    val add_prefix = ``sw_add ^r ^a ^b``
    val add_P = mk_comb (add_prefix,P)
    val scalar_prefix = rator scalar
    fun add U V = candidate (mk_comb (mk_comb (add_prefix,U),V))
    fun add_base V = candidate (mk_comb (add_P,V))
    fun bits 0 acc = acc
      | bits k acc = bits (IntInf.div(k,2)) (IntInf.mod(k,2)::acc)
    fun equation k Q =
      mk_eq (mk_comb (scalar_prefix,numeral k),Q)
    val digits = bits n []
    fun prefixes [] k = [(k,[])]
      | prefixes (remaining as bit::rest) k =
          (k,remaining) :: prefixes rest (2*k+bit)
    val prefix_suffixes = if operations then prefixes digits 0 else []
    fun assumed_prefix eq best =
      if not operations orelse not (is_eq eq) then best
      else
        let val (left,Q) = dest_eq eq in
          if not (is_comb left) orelse
             not (aconv (rator left) scalar_prefix) orelse
             not (numSyntax.is_numeral (rand left))
          then best
          else
            let val k = integer (rand left) in
              case List.find (fn (prefix,_) => prefix=k) prefix_suffixes of
                NONE => best
              | SOME (_,remaining) =>
                  (case best of
                     SOME (previous,_,_,_) =>
                       if previous >= k then best
                       else SOME (k,Q,remaining,eq)
                   | NONE => SOME (k,Q,remaining,eq))
            end
        end
    val seed = foldl (fn (eq,best) => assumed_prefix eq best) NONE asl
    val (start_k,start_Q,remaining,seed_eq) =
      case seed of
        NONE => (0,zero,digits,NONE)
      | SOME (k,Q,remaining,eq) => (k,Q,remaining,SOME eq)
    fun milestones [] _ _ _ acc = (rev acc,[])
      | milestones (remaining as bit::rest) i k Q acc =
        if operations andalso i=width then (rev acc,remaining)
        else
        let
          val doubled = add Q Q
          val next = if bit=0 then doubled else add_base doubled
          val twice = 2*k
          val k' = twice + bit
          val boundary = i+1=width orelse null rest
          val acc' =
            if operations then
              let val doubled_acc = equation twice doubled :: acc in
                if bit=0 then doubled_acc else equation k' next :: doubled_acc
              end
            else if boundary then equation k' next :: acc else acc
        in
          milestones rest
            (if boundary andalso not operations then 0 else i+1)
            k' next acc'
        end
    val (equations,pending) = milestones remaining 0 start_k start_Q []
    val continuation = not (null pending)
    val final =
      if not (null equations) then ASSUME (List.last equations)
      else case seed_eq of
        SOME eq => ASSUME eq
      | NONE => REWRITE_CONV [sw_scalar_zero] scalar
    val rewritten = if continuation then NONE
                    else SOME (REWRITE_CONV [final] w)
    val residual = Option.map (rhs o concl) rewritten
    fun implications [] _ = []
      | implications (eq::eqs) previous =
          (case previous of NONE => eq | SOME p => mk_imp (p,eq)) ::
          implications eqs (SOME eq)
    val claims = implications equations seed_eq
    val subgoals =
      map (fn claim => (asl,claim)) claims @
      (if continuation then [(concl final::asl,w)]
       else case residual of
         SOME tm => if aconv tm T then [] else [(asl,tm)]
       | NONE => raise ERR "Missing scalar residual")
    fun validate proofs =
      let
        val steps = List.take (proofs,length claims)
        val rest = List.drop (proofs,length claims)
        fun chain [] previous = previous
          | chain (th::ths) previous =
              chain ths (SOME (case previous of NONE => th
                | SOME prev => MP th prev))
        val result =
          if continuation then hd rest
          else case (rewritten,residual) of
            (SOME rewrite,SOME tm) =>
              if aconv tm T then EQT_ELIM rewrite
              else EQ_MP (SYM rewrite) (hd rest)
          | _ => raise ERR "Missing scalar rewrite"
      in
        case chain steps (Option.map ASSUME seed_eq) of NONE => result
        | SOME proved => PROVE_HYP proved result
      end
  in (subgoals,validate) end

fun BINARY_SCALAR_CERTIFICATE_TAC width =
  scalar_certificate_tac false width

fun BINARY_SCALAR_OPERATION_CERTIFICATE_TAC maxbits =
  scalar_certificate_tac true maxbits

fun BINARY_SCALAR_STEP_TAC add_conv curve member =
  REPEAT DISCH_TAC THEN
  (fn (asl,w) =>
    let
      fun seed tm =
        case List.find (fn a => is_eq a andalso aconv (lhs a) tm) asl of
          NONE => NONE
        | SOME a => SOME (ASSUME a)
    in
      (CONV_TAC (LAND_CONV
        (binary_scalar_conv_from seed add_conv curve member)) THEN REFL_TAC)
        (asl,w)
    end)

(* Retain successful kernel equalities for this certificate-bound converter,
   not failed matches or mutable inverse-evaluation state. Rejected inputs must
   raise HOL_ERR so ORELSEC-based traversals continue into their subterms. *)
fun BINARY_SCALAR_CONV add_conv curve member =
  Conv.memoize scalar_key (Redblackmap.mkDict Term.compare)
    (K true) (ERR "Expected a curve scalar expression")
    (binary_scalar_conv add_conv curve member)

(* Compile field projections while the modulus is schematic, rather than
   repeatedly reducing large instantiated field records during each addition. *)
fun gf_specialize th =
  REWRITE_RULE [GF_eval, GF_sum_inv, monoidTheory.monoid_exp_def,
                numeralTheory.numeral_funpow]
    (Q.INST [`r` |-> `GF (p:num)`]
      (INST_TYPE [alpha |-> ``:num``] (SPEC_ALL th)))

val gf_addition_rules = map gf_specialize
  [sw_add_def, sw_slope_def, sw_add_x_def, sw_add_y_def]

val gf_program_heads = ``GF`` ::
  map (fst o strip_comb o lhs o concl o hd o BODY_CONJUNCTS) gf_addition_rules

fun gf_scalar_tools prime curve member tm =
  let
    val (theta,_) = match_term scalar_pattern tm
    fun value t = Term.subst theta t
    val p = value ``p:num``
    val a = value ``a:num``
    val b = value ``b:num``
    val P = value ``P:num sw_point``
    val modulus = integer p
    val _ = integer a
    val _ = integer b
    val _ = point P
    val r = ``GF ^p``
    val _ =
      if aconv (concl prime) ``prime ^p`` then ()
      else raise ERR "Mismatched prime certificate"
    val arithmetic = certificateComputeLib.EVAL_CONV ()
    (* Recompile the program into this compset: copied default rules retain
       references to their original tables and cannot see inverse witnesses. *)
    val addition_cs = List.foldl
      (fn (head,cs) => computeLib.scrub_const cs head)
      (certificateComputeLib.EVAL_COMPSET ())
      gf_program_heads

    fun inverse_rule x =
      let
        val xt = numeral x
        val y = numeral (inverse modulus x)
        val rule = SPECL [p,xt,y] sw_GF_prod_inv_witness
        val numeric = arithmetic
          ``^xt < ^p /\ ^xt <> 0 /\ ^y < ^p /\ (^xt * ^y) MOD ^p = 1``
      in MP rule (CONJ prime (EQT_ELIM numeric)) end

    (* Only the current addition's checked witness is needed. Appending every
       ground inverse as a rewrite would make matching grow at each bit. *)
    val inverse_witness = ref (NONE : thm option)
    fun inverse_conv tm =
      case !inverse_witness of
        SOME th => if aconv tm (lhs (concl th)) then th else raise UNCHANGED
      | NONE => raise UNCHANGED
    val addition_cs = computeLib.add_conv
      (inverse_head,2,inverse_conv) addition_cs

    val addition_cs = computeLib.add_thms
      (numeralTheory.numeral_funpow :: gf_addition_rules) addition_cs
    val add_pattern =
      ``sw_add ^r ^a ^b (U:num sw_point) (V:num sw_point)``

    fun candidate expression =
      let
        val (substitution,_) = match_term add_pattern expression
        val U = Term.subst substitution ``U:num sw_point``
        val V = Term.subst substitution ``V:num sw_point``
        fun affine_point (x,y) = list_mk_comb (affine,[numeral x,numeral y])
        fun residue x = IntInf.mod (x,modulus)
      in
        case (point U,point V) of
          (NONE,_) => V
        | (_,NONE) => U
        | (SOME(x1,y1),SOME(x2,y2)) =>
            if x1=x2 andalso residue(y1+y2)=0 then infinity
            else
              let
                val numerator = if x1=x2 then 3*x1*x1 + integer a
                                else y2-y1
                val denominator = residue (if x1=x2 then 2*y1 else x2-x1)
                val slope = residue (numerator * inverse modulus denominator)
                val x3 = residue (slope*slope-x1-x2)
                val y3 = residue (slope*(x1-x3)-y1)
              in affine_point (x3,y3) end
      end

    fun add_conv expression =
      let
        val (substitution,_) = match_term add_pattern expression
        val U = Term.subst substitution ``U:num sw_point``
        val V = Term.subst substitution ``V:num sw_point``
        val _ = inverse_witness :=
          case (point U,point V) of
            (SOME(x1,y1),SOME(x2,y2)) =>
              if x1=x2 andalso y1<>y2 then NONE else
              let
                val denominator = IntInf.mod
                  (if x1=x2 then 2*y1 else x2-x1,modulus)
              in if denominator=0 then NONE
                 else SOME (inverse_rule denominator) end
          | _ => NONE
        (* CBV evaluates each let-bound slope before substituting it into the
           coordinates; rewriting first duplicates large arithmetic terms. *)
        val th = with_flag (computeLib.auto_import_definitions,false)
          (computeLib.WEAK_CBV_CONV addition_cs) expression
        val _ = point (rhs (concl th))
      in th end

  in (candidate,add_conv) end

fun gf_scalar_conv prime curve member tm =
  let val (_,add_conv) = gf_scalar_tools prime curve member tm
  in binary_scalar_conv add_conv curve member tm end

fun SCALAR_CERTIFICATE_TAC width prime curve member (goal as (_,w)) =
  let
    val scalar = find_term (fn t => isSome (scalar_key t)) w
    val (candidate,_) = gf_scalar_tools prime curve member scalar
  in BINARY_SCALAR_CERTIFICATE_TAC width candidate curve member goal end

fun SCALAR_STEP_TAC prime curve member (goal as (_,w)) =
  let
    val scalar = find_term (fn t => isSome (scalar_key t)) w
    val (_,add_conv) = gf_scalar_tools prime curve member scalar
  in BINARY_SCALAR_STEP_TAC add_conv curve member goal end

fun SCALAR_CONV prime curve member =
  Conv.memoize scalar_key (Redblackmap.mkDict Term.compare)
    (K true) (ERR "Expected a curve scalar expression")
    (gf_scalar_conv prime curve member)

end
