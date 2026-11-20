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
open shortWeierstrassSyntax
open certificateComputeLib

val ERR = mk_HOL_ERR "ellipticCertificateLib" "SCALAR_CONV"

val infinity = mk_ECInfinity numSyntax.num
val affine = Term.inst [alpha |-> numSyntax.num] ECAffine_tm
val scalar_pattern = mk_sw_scalar
  (polynomialSyntax.mk_GF (mk_var ("p",numSyntax.num)),
   mk_var ("a",numSyntax.num),mk_var ("b",numSyntax.num),
   mk_var ("P",type_of infinity),mk_var ("n",numSyntax.num))
val inverse_head = polynomialSyntax.monoid_inv_tm
val prime_head = prim_mk_const {Thy = "divides", Name = "prime"}

fun scalar_key tm =
  (dest_sw_scalar tm; SOME tm) handle HOL_ERR _ => NONE


fun point tm =
  if aconv tm infinity then NONE
  else
    case strip_comb tm of
      (c,[x,y]) =>
        if same_const c affine
        then SOME (integer x,integer y)
        else raise ERR "Expected a literal curve point"
    | _ => raise ERR "Expected a literal curve point"

(* Field-independent binary proof; the supplied addition conversion returns
   kernel equalities, so alternative concrete field representations share it. *)
fun binary_scalar_conv_from seed add_conv curve member tm =
  let
    val (r,a,b,P,nt) = dest_sw_scalar tm
    val n = integer nt
    val premises = CONJ curve member
    val _ =
      if aconv (concl premises)
        (mk_conj (mk_ShortWeierstrassCurve (r,a,b),
          pred_setSyntax.mk_in (P,mk_sw_points (r,a,b))))
      then () else raise ERR "Mismatched curve or point certificate"
    fun scalar k =
      let val expression = mk_comb (rator tm,literal k)
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
              (mk_comb (rator tm,literal (k-1)))
          in
            case previous of
              SOME prev =>
                let
                  (* An operation milestone supplies the preceding even
                     scalar, so this odd transition checks only one add. *)
                  val law = MP (PART_MATCH (lhs o rand) sw_scalar_add
                    (mk_comb (rator tm,
                      numSyntax.mk_plus (literal 1,literal (k-1)))))
                    premises
                  val one = MP (PART_MATCH (lhs o rand) sw_scalar_one
                    (mk_comb (rator tm,literal 1))) premises
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
                    (ISPECL [r,a,b,P,literal half] binary) premises
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
    val (r,a,b,P,nt) = dest_sw_scalar scalar
    val n = integer nt
    val _ =
      if aconv (concl (CONJ curve member))
        (mk_conj (mk_ShortWeierstrassCurve (r,a,b),
          pred_setSyntax.mk_in (P,mk_sw_points (r,a,b))))
      then () else raise ERR "Mismatched curve or point certificate"
    val zero = mk_ECInfinity (type_of a)
    (* Construct the typed prefixes once, not once per proposed operation. The
       trajectory still constructs only untrusted terms, never proofs. *)
    val add_prefix = list_mk_icomb (sw_add_tm,[r,a,b])
    val add_P = mk_comb (add_prefix,P)
    val scalar_prefix = rator scalar
    fun add U V = candidate (mk_comb (mk_comb (add_prefix,U),V))
    fun add_base V = candidate (mk_comb (add_P,V))
    fun bits 0 acc = acc
      | bits k acc = bits (IntInf.div(k,2)) (IntInf.mod(k,2)::acc)
    fun equation k Q =
      mk_eq (mk_comb (scalar_prefix,literal k),Q)
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
  in
    certificateComputeLib.MILESTONE_GOALS
      {goal=(asl,w),equations=equations,seed=seed_eq,
       continuation=continuation,final=final}
  end

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
    (INST [mk_var ("r",polynomialSyntax.mk_ring_type numSyntax.num) |->
             polynomialSyntax.mk_GF (mk_var ("p",numSyntax.num))]
      (INST_TYPE [alpha |-> numSyntax.num] (SPEC_ALL th)))

val gf_addition_rules = map gf_specialize
  [sw_add_def, sw_slope_def, sw_add_x_def, sw_add_y_def]

val gf_program_heads = polynomialSyntax.GF_tm ::
  map (fst o strip_comb o lhs o concl o hd o BODY_CONJUNCTS) gf_addition_rules

fun gf_scalar_tools prime curve member tm =
  let
    val (theta,_) = match_term scalar_pattern tm
    fun value t = Term.subst theta t
    val p = value (mk_var ("p",numSyntax.num))
    val a = value (mk_var ("a",numSyntax.num))
    val b = value (mk_var ("b",numSyntax.num))
    val P = value (mk_var ("P",type_of infinity))
    val modulus = integer p
    val _ = integer a
    val _ = integer b
    val _ = point P
    val r = polynomialSyntax.mk_GF p
    val _ =
      if aconv (concl prime) (mk_comb (prime_head,p)) then ()
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
        val xt = literal x
        val y = literal (inverse_candidate modulus x)
        val rule = SPECL [p,xt,y] sw_GF_prod_inv_witness
        val numeric = arithmetic (list_mk_conj
          [numSyntax.mk_less (xt,p),
           mk_neg (mk_eq (xt,numSyntax.zero_tm)),
           numSyntax.mk_less (y,p),
           mk_eq (numSyntax.mk_mod (numSyntax.mk_mult (xt,y),p),
                  literal 1)])
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
    val add_pattern = mk_sw_add
      (r,a,b,mk_var ("U",type_of infinity),mk_var ("V",type_of infinity))

    fun candidate expression =
      let
        val (substitution,_) = match_term add_pattern expression
        val U = Term.subst substitution (mk_var ("U",type_of P))
        val V = Term.subst substitution (mk_var ("V",type_of P))
        fun affine_point (x,y) = list_mk_comb (affine,[literal x,literal y])
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
                val slope =
                  residue (numerator * inverse_candidate modulus denominator)
                val x3 = residue (slope*slope-x1-x2)
                val y3 = residue (slope*(x1-x3)-y1)
              in affine_point (x3,y3) end
      end

    fun add_conv expression =
      let
        val (substitution,_) = match_term add_pattern expression
        val U = Term.subst substitution (mk_var ("U",type_of P))
        val V = Term.subst substitution (mk_var ("V",type_of P))
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
        val th = HOLFlags.with_bflags
          [(computeLib.auto_import_definitions,false)]
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
