(* Checked quadratic-field arithmetic and curve certificates.
   See pairingCurveCertificateLib.sig for argument order and branch layout.
   FIELD_CONV and SCALAR_CONV support numeric PolyModRing (GF p) [1;0;1],
   with canonical ascending lists ([] zero), not arbitrary extension towers.
   Supply closed prime and field proofs, plus matching curve and membership
   proofs for scalars. SCALAR_CERTIFICATE_TAC / SCALAR_STEP_TAC and
   POWER_CERTIFICATE_TAC / POWER_STEP_TAC expose bounded operation proofs.
   Candidate coordinates, inverses and power trajectories are never theorems:
   checked operations against the existing quotient field justify each step. *)

structure pairingCurveCertificateLib :> pairingCurveCertificateLib =
struct

open HolKernel boolLib bossLib Conv
open fieldTheory fieldInstancesTheory polyModuloRingTheory
open ellipticCertificatesTheory shortWeierstrassTheory shortWeierstrassGroupTheory

val ERR = mk_HOL_ERR "pairingCurveCertificateLib"
fun integer tm = Arbnum.toLargeInt (numSyntax.dest_numeral tm)
fun numeral n = numSyntax.mk_numeral (Arbnum.fromLargeInt n)
fun polynomial xs = listSyntax.mk_list (map numeral xs,numSyntax.num)
fun coefficients tm = map integer (#1 (listSyntax.dest_list tm))
fun trim (xs:IntInf.int list) =
  let fun drop (0::rest) = drop rest | drop rest = rest
  in rev (drop (rev xs)) end

(* Euclid only proposes a candidate.  Its result is checked by the generic
   inverse witness theorem against the actual PolyModRing multiplication. *)
fun inverse p x =
  let fun loop (a,b,u,v) =
    if b = 0 then IntInf.mod (u,p)
    else loop (b,IntInf.mod(a,b),v,u-IntInf.div(a,b)*v)
  in loop (x,p,1,0) end

fun field_conv prime field =
  let
    val _ = null (hyp prime) andalso null (hyp field)
      orelse raise ERR "FIELD_CONV" "Expected closed certificates"
    val pterm = rand (concl prime)
    val p = integer pterm
    val f = ``[1n;0;1]``
    val r = ``PolyModRing (GF ^pterm) ^f``
    val _ = aconv (concl field) ``Field ^r``
      orelse raise ERR "FIELD_CONV" "Expected the numeric quadratic quotient field"
    val remainder = polynomialCertificateLib.REMAINDER_CONV prime f
    val bounded = polynomialCertificateLib.BOUNDED_CONV ()
    val coefficient_ring = MATCH_MP field_is_ring (MATCH_MP GF_field prime)
    val monic = EQT_ELIM (bounded ``poly_monic (GF ^pterm) ^f``)
    val leading = MP
      (SPEC f (MATCH_MP polyMonicTheory.poly_monic_ulead coefficient_ring))
      monic
    val degree = bounded ``poly_deg (GF ^pterm) ^f``
    (* A sum (or a constant product) is already below the modulus degree.
       Its checked reduction needs no quotient witness or polynomial product. *)
    val short_remainder_rule = GEN ``x:num list``
      (CONV_RULE
        (LAND_CONV (REWRITE_CONV [leading,degree]))
        (SPECL [``x:num list``,f]
          (MATCH_MP polyDivisionTheory.poly_mod_less coefficient_ring)))
    val add_rule = SIMP_CONV (srw_ss()) [poly_mod_ring_def]
      ``^r.sum.op (x:num list) y``
    val mult_rule = SIMP_CONV (srw_ss()) [poly_mod_ring_def]
      ``^r.prod.op (x:num list) y``
    val sumop = ``^r.sum.op``
    val prodop = ``^r.prod.op``
    val negop = ``^r.sum.inv``
    val invop = ``^r.prod.inv``
    val powop = ``^r.prod.exp``
    val sumpow = ``^r.sum.exp``
    val zero = ``^r.sum.id``
    val one = ``^r.prod.id``
    val sum_monoid = ``^r.sum``
    val prod_monoid = ``^r.prod``
    val carrier = ``^r.carrier``
    val zero_rule = (REWRITE_CONV [poly_mod_ring_ids] THENC bounded) zero
    val one_rule = (REWRITE_CONV [poly_mod_ring_ids] THENC bounded) one
    val exp_one_rule = MATCH_MP field_exp_1 field
    val exp_add_rule = MATCH_MP field_exp_add field
    val sum_inverse_rule = ISPEC r sw_field_sum_inv_witness
    val prod_inverse_rule = ISPEC r sw_field_prod_inv_witness
    val element_rewrite = REWRITE_CONV [poly_mod_ring_element]
    val membership_check = element_rewrite THENC bounded
    val choose_branch = REWRITE_CONV [COND_CLAUSES]
    (* Expand one curve operation at its head, never rewrite through its
       branches or let bodies before their operands have been evaluated. *)
    val curve_rules = List.concat (map
      (fn th => BODY_CONJUNCTS
        (INST [``r:num list field`` |-> r]
          (INST_TYPE [alpha |-> ``:num list``] (SPEC_ALL th))))
      [sw_add_def,sw_slope_def,sw_add_x_def,sw_add_y_def])
    val curve_program = map
      (fn th => let val (head,args) = strip_comb (lhs (concl th))
                in (head,length args,REWR_CONV th) end) curve_rules
    fun expand_curve expression =
      let val (head,args) = strip_comb expression in
        case List.find (fn (h,n,_) => is_const head andalso same_const head h andalso
          length args = n) curve_program of
          SOME _ =>
            SOME (FIRST_CONV
              (map #3 (List.filter
                (fn (h,n,_) => same_const head h andalso length args = n)
                curve_program)) expression)
        | NONE => NONE
      end
    fun literal_pair x =
      case coefficients x of
        [] => (0,0)
      | [a] => (a,0)
      | [a,b] => (a,b)
      | _ => raise ERR "FIELD_CONV" "Noncanonical quadratic representative"
    fun neg_candidate x =
      polynomial (trim (map (fn a => IntInf.mod(~a,p)) (coefficients x)))
    fun inv_candidate x =
      let
        val (a,b) = literal_pair x
        val d = inverse p (IntInf.mod(a*a+b*b,p))
      in polynomial (trim [IntInf.mod(a*d,p),IntInf.mod(~b*d,p)]) end
    (* Normalize the polynomial operand once. Only a genuinely quadratic
       product needs REMAINDER_CONV's full division witness. *)
    fun evaluate_operation expression =
      let
        val expanded = FIRST_CONV
          [REWR_CONV add_rule,REWR_CONV mult_rule] expression
        val operand = RATOR_CONV (RAND_CONV bounded) (rhs (concl expanded))
        val reduced = rhs (concl operand)
        val x = rand (rator reduced)
        val result =
          if length (coefficients x) <= 2 then
            let
              val rule = SPEC x short_remainder_rule
              val premise = fst (dest_imp (concl rule))
            in MP rule (EQT_ELIM (bounded premise)) end
          else remainder reduced
      in TRANS expanded (TRANS operand result) end
    fun finish tm =
      let
        (* Reuse checked witnesses within one addition, without retaining its
           intermediate coordinates for the lifetime of a scalar converter. *)
        val membership = Conv.memoize SOME (Redblackmap.mkDict Term.compare)
          (aconv T) (ERR "FIELD_CONV" "Unproved field membership")
          membership_check
        val operation = Conv.memoize SOME (Redblackmap.mkDict Term.compare)
          (K true) UNCHANGED evaluate_operation
        fun member x = EQT_ELIM (membership (pred_setSyntax.mk_in (x,carrier)))
        val negation = Conv.memoize SOME (Redblackmap.mkDict Term.compare)
          (K true) UNCHANGED
          (fn expression =>
            let
              val x = rand expression
              val y = neg_candidate x
              val rule = SPECL [x,y] sum_inverse_rule
              val sum = operation (list_mk_comb (sumop,[x,y]))
              val sum_zero = TRANS sum (SYM zero_rule)
              val premise = CONJ field (LIST_CONJ [member x,member y,sum_zero])
            in MP rule premise end)
        fun normalize expression =
          if numSyntax.is_numeral expression orelse can coefficients expression
             orelse aconv expression r
          then REFL expression
          else if boolSyntax.is_let expression then
            (* Evaluate shared bindings before substitution, preserving literal operands. *)
            (RAND_CONV normalize THENC REWR_CONV LET_THM THENC
             BETA_CONV THENC normalize) expression
          else if boolSyntax.is_cond expression then
            let
              val (condition,_,_) = boolSyntax.dest_cond expression
              val decision = normalize condition
            in
              (RATOR_CONV (RATOR_CONV (RAND_CONV (K decision))) THENC
               choose_branch THENC normalize) expression
            end
          else
            (case expand_curve expression of
               SOME expansion =>
                 TRANS expansion (normalize (rhs (concl expansion)))
             | NONE =>
                 let
                   val children =
                     let val (head,args) = strip_comb expression in
                       if length args = 2 andalso
                          List.exists (aconv head) [sumop,prodop,powop,sumpow]
                       then BINOP_CONV normalize expression
                       else if length args = 1 andalso
                               (aconv head negop orelse aconv head invop)
                       then RAND_CONV normalize expression
                       else if is_comb expression then COMB_CONV normalize expression
                       else if is_abs expression then ABS_CONV normalize expression
                       else REFL expression
                     end
                   val evaluated = step (rhs (concl children))
                 in TRANS children evaluated end)
        and checked expression =
          let val result = normalize expression in
            if aconv (rhs (concl result)) T then EQT_ELIM result
            else raise ERR "FIELD_CONV"
              ("Unproved field witness: " ^ term_to_string (rhs (concl result)))
          end
        and step expression =
          let
            val (h,args) =
              if is_comb expression andalso
                 (aconv (rator expression) negop orelse
                  aconv (rator expression) invop)
              then (rator expression,[rand expression])
              else if is_comb expression andalso is_comb (rator expression)
              then (rator (rator expression),
                    [rand (rator expression),rand expression])
              else (expression,[])
          in
            if (aconv h sumop orelse aconv h prodop) andalso length args = 2
            then operation expression
            else if aconv h negop andalso length args = 1
            then negation expression
            else if aconv h invop andalso length args = 1 then
              let
                val x = hd args
                val y = inv_candidate x
                val rule = SPECL [x,y] prod_inverse_rule
                val premise = CONJ field (LIST_CONJ
                  [member x,checked ``^x <> ^r.sum.id``,member y,
                   checked ``^r.prod.op ^x ^y = ^r.prod.id``])
              in MP rule premise end
            else if aconv h powop andalso length args = 2 then
              power (hd args) (integer (List.nth(args,1)))
            else if aconv h sumpow andalso length args = 2 then
              let
                val x = hd args
                val k = integer (List.nth(args,1))
              in
                if k = 0 then
                  REWRITE_CONV [monoidTheory.monoid_exp_0] expression
                else
                  let
                    val previous = numeral (k-1)
                    val rule = ISPECL [sum_monoid,x,previous]
                      monoidTheory.monoid_exp_SUC
                    val rule = CONV_RULE
                      (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) rule
                  in TRANS rule (normalize (rhs (concl rule))) end
              end
            else if aconv expression zero then zero_rule
            else if aconv expression one then one_rule
            else if type_of expression = numSyntax.num
            then QCONV certificateComputeLib.NAT_CONV expression
            else if type_of expression = bool then membership_check expression
            else REFL expression
          end
        and power x k =
          let val expression = list_mk_comb (powop,[x,numeral k]) in
            if k = 0 then
              (REWRITE_CONV [monoidTheory.monoid_exp_0] THENC normalize) expression
            else if k = 1 then
              let val rule = SPEC x exp_one_rule
              in MP rule (member x) end
            else if IntInf.mod(k,2) = 1 then
              let
                val rule = ISPECL [prod_monoid,x,numeral (k-1)]
                  monoidTheory.monoid_exp_SUC
                val rule = CONV_RULE
                  (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) rule
                val substituted = SUBS [power x (k-1)] rule
              in TRANS substituted (normalize (rhs (concl substituted))) end
            else
              let
                val half = numeral (IntInf.div(k,2))
                val law = SPECL [half,half]
                  (MP (SPEC x exp_add_rule) (member x))
                val law = CONV_RULE
                  (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) law
                val substituted = SUBS [power x (IntInf.div(k,2))] law
              in TRANS substituted (normalize (rhs (concl substituted))) end
          end
      in normalize tm end
  in finish end

(* Retain only the last field's immutable program and closed setup proofs.
   Membership and operation witnesses are allocated inside finish, so no
   inverse witness or intermediate coordinate crosses conversion calls. *)
val FIELD_CONV =
  let
    val previous = ref (NONE : (term * term * conv) option)
  in
    fn prime => fn field =>
      let
        val _ = null (hyp prime) andalso null (hyp field)
          orelse raise ERR "FIELD_CONV" "Expected closed certificates"
        val key = (concl prime,concl field)
      in
        case !previous of
          SOME (p,f,convert) =>
            if aconv (#1 key) p andalso aconv (#2 key) f then convert
            else
              let val convert = field_conv prime field
              in previous := SOME (#1 key,#2 key,convert); convert end
        | NONE =>
            let val convert = field_conv prime field
            in previous := SOME (#1 key,#2 key,convert); convert end
      end
  end

fun SCALAR_CONV prime field curve member =
  let
    val arithmetic = FIELD_CONV prime field
    val addition = ``sw_add:num field->num->num->num sw_point->
      num sw_point->num sw_point``
    fun add expression =
      let
        val (head,args) = strip_comb expression
        val _ = length args = 5 andalso same_const head addition
          orelse raise ERR "SCALAR_CONV" "Expected a full curve addition"
      in arithmetic expression end
    val scalar = ellipticCertificateLib.BINARY_SCALAR_CONV add curve member
    val infinity = ``ECInfinity:num list sw_point``
    val affine = ``ECAffine:num list->num list->num list sw_point``
    fun finish expression =
      let
        val result = scalar expression
        val point = rhs (concl result)
        val (head,args) = strip_comb point
        val _ =
          if aconv point infinity then ()
          else if is_const head andalso same_const head affine andalso
                  length args = 2 andalso List.all (can coefficients) args
          then ()
          else raise ERR "SCALAR_CONV" "Point arithmetic did not normalize"
      in result end
  in finish end

(* Milestone coordinates are only proposals. The shared tactic emits separate
   implication goals, reconstructed by the checked addition conversion above;
   callers enumerate their branches explicitly to bound each proof step. *)
fun addition_candidate prime =
  let
    val p = integer (rand (concl prime))
    fun residue n = IntInf.mod(n,p)
    fun pair tm =
      case coefficients tm of
        [] => (0,0)
      | [x] => (x,0)
      | [x,y] => (x,y)
      | _ => raise ERR "SCALAR_CERTIFICATE_TAC" "Nonquadratic coordinate"
    fun literal (x,y) = polynomial (trim [x,y])
    fun plus ((a,b),(c,d)) = (residue(a+c),residue(b+d))
    fun neg (a,b) = (residue(~a),residue(~b))
    fun minus ((a,b),(c,d)) = (residue(a-c),residue(b-d))
    fun times ((a,b),(c,d)) =
      (residue(a*c-b*d),residue(a*d+b*c))
    fun square (a,b) = (residue(a*a-b*b),residue(2*a*b))
    fun scale n (a,b) = (residue(n*a),residue(n*b))
    fun inv (a,b) =
      let val d = inverse p (residue(a*a+b*b))
      in (residue(a*d),residue(~b*d)) end
    val infinity = ``ECInfinity:num list sw_point``
    val affine = ``ECAffine:num list->num list->num list sw_point``
    type point_value =
      ((IntInf.int * IntInf.int) * (IntInf.int * IntInf.int)) option
    (* Candidate-only caches retain decoded inputs, never theorems. The first
       affine input is the fixed generator; the latest output supplies the
       next operation without decoding four freshly encoded numerals. *)
    val fixed = ref (NONE : (term * point_value) option)
    val latest = ref (NONE : (term * point_value) option)
    fun decode_point tm =
      if aconv tm infinity then NONE
      else
        case strip_comb tm of
          (head,[x,y]) =>
            if is_const head andalso same_const head affine
            then SOME (pair x,pair y)
            else raise ERR "SCALAR_CERTIFICATE_TAC" "Expected literal point"
        | _ => raise ERR "SCALAR_CERTIFICATE_TAC" "Expected literal point"
    fun point tm =
      case !latest of
        SOME (previous,value) =>
          if aconv tm previous then value else fixed_point tm
      | NONE => fixed_point tm
    and fixed_point tm =
      case !fixed of
        SOME (generator,value) =>
          if aconv tm generator then value else decode_point tm
      | NONE =>
          let
            val value = decode_point tm
            val _ = if isSome value then fixed := SOME (tm,value) else ()
          in value end
    fun output value tm = (latest := SOME (tm,value); tm)
    fun propose expression =
      case strip_comb expression of
        (_,[_,a,_,u,v]) =>
          let
            val first = point u
            val second = if aconv u v then first else point v
          in
            case (first,second) of
              (NONE,_) => output second v
            | (_,NONE) => output first u
            | (SOME(x1,y1),SOME(x2,y2)) =>
                if x1=x2 andalso y1=neg y2 then output NONE infinity
                else
                  let
                    val (numerator,denominator) =
                      if x1=x2 then
                        (plus(scale 3 (square x1),pair a),scale 2 y1)
                      else (minus(y2,y1),minus(x2,x1))
                    val m = times(numerator,inv denominator)
                    val x3 = minus(minus(square m,x1),x2)
                    val y3 = minus(times(m,minus(x1,x3)),y1)
                  in
                    output (SOME (x3,y3))
                      (list_mk_comb(affine,[literal x3,literal y3]))
                  end
          end
      | _ => raise ERR "SCALAR_CERTIFICATE_TAC" "Expected full curve addition"
  in propose end

fun SCALAR_CERTIFICATE_TAC prime field curve member =
  ellipticCertificateLib.BINARY_SCALAR_OPERATION_CERTIFICATE_TAC
    16 (addition_candidate prime) curve member

fun SCALAR_STEP_TAC prime field curve member =
  ellipticCertificateLib.BINARY_SCALAR_STEP_TAC
    (FIELD_CONV prime field) curve member

(* Only the immutable field program is shared with FIELD_CONV. Power
   candidates and their prefix values live in a single bounded preparation. *)
fun power_setup prime field =
  let
    val _ = null (hyp prime) andalso null (hyp field)
      orelse raise ERR "POWER_CERTIFICATE_TAC" "Expected closed certificates"
    val pterm = rand (concl prime)
    val p = integer pterm
    val r = ``PolyModRing (GF ^pterm) [1n;0;1]``
    val _ = aconv (concl prime) ``prime ^pterm`` andalso
            aconv (concl field) ``Field ^r``
      orelse raise ERR "POWER_CERTIFICATE_TAC" "Mismatched field certificates"
    val arithmetic = FIELD_CONV prime field
  in (r,p,arithmetic,``^r.prod.exp``,``^r.prod.op``) end

fun power_arguments powop tm =
  if is_comb tm andalso is_comb (rator tm) andalso
     aconv (rator (rator tm)) powop
  then (rand (rator tm),integer (rand tm))
  else raise ERR "POWER_CERTIFICATE_TAC" "Expected a literal field power"

fun quadratic_pair p tm =
  let
    val pair =
      case coefficients tm of
        [] => (0,0)
      | [a] => (a,0)
      | [a,b] => (a,b)
      | _ => raise ERR "POWER_CERTIFICATE_TAC" "Nonquadratic representative"
    val (a,b) = pair
    val _ = a >= 0 andalso a < p andalso b >= 0 andalso b < p andalso
            aconv tm (polynomial (trim [a,b]))
      orelse raise ERR "POWER_CERTIFICATE_TAC" "Noncanonical representative"
  in pair end

fun POWER_CERTIFICATE_TAC prime field (asl,w) _ =
  let
    val (r,p,arithmetic,powop,_) = power_setup prime field
    val power = find_term (can (power_arguments powop)) w
    val (x,n) = power_arguments powop power
    val base = quadratic_pair p x
    val _ = EQT_ELIM (arithmetic ``^x IN ^r.carrier``)
    val prefix = rator power
    fun bits 0 acc = acc
      | bits k acc = bits (IntInf.div(k,2)) (IntInf.mod(k,2)::acc)
    val digits = bits n []
    fun prefixes [] k = [(k,[])]
      | prefixes (remaining as bit::rest) k =
          (k,remaining) :: prefixes rest (2*k+bit)
    val prefix_suffixes = prefixes digits 0
    fun assumed_prefix eq best =
      if not (is_eq eq) then best
      else
        let val (left,Q) = dest_eq eq in
          if not (is_comb left) orelse not (aconv (rator left) prefix) orelse
             not (numSyntax.is_numeral (rand left))
          then best
          else
            let val k = integer (rand left) in
              case List.find (fn (previous,_) => previous=k) prefix_suffixes of
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
    val (start_k,start_value,remaining,seed_eq) =
      case seed of
        NONE => (0,(1,0),digits,NONE)
      | SOME (k,Q,remaining,eq) =>
          (k,quadratic_pair p Q,remaining,SOME eq)
    fun times ((a,b),(c,d)) =
      (IntInf.mod(a*c-b*d,p),IntInf.mod(a*d+b*c,p))
    fun equation k (a,b) =
      mk_eq (mk_comb (prefix,numeral k),polynomial (trim [a,b]))
    (* Pure ML multiplication proposes at most sixteen complete binary bits.
       Every doubling and every odd multiplication has its own proof goal. *)
    fun milestones [] _ _ _ acc = (rev acc,[])
      | milestones (remaining as bit::rest) i k value acc =
          if i=16 then (rev acc,remaining)
          else
            let
              val doubled = times (value,value)
              val twice = 2*k
              val even_acc = equation twice doubled :: acc
              val next = if bit=0 then doubled else times (doubled,base)
              val k' = twice+bit
              val acc' = if bit=0 then even_acc
                         else equation k' next :: even_acc
            in milestones rest (i+1) k' next acc' end
    val (equations,pending) = milestones remaining 0 start_k start_value []
    val continuation = not (null pending)
    val final =
      if not (null equations) then ASSUME (List.last equations)
      else case seed_eq of
        SOME eq => ASSUME eq
      | NONE => arithmetic power
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
       | NONE => raise ERR "POWER_CERTIFICATE_TAC" "Missing power residual")
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
          | _ => raise ERR "POWER_CERTIFICATE_TAC" "Missing power rewrite"
      in
        case chain steps (Option.map ASSUME seed_eq) of NONE => result
        | SOME proved => PROVE_HYP proved result
      end
  in (subgoals,validate) end

fun POWER_STEP_TAC prime field =
  REPEAT DISCH_TAC THEN
  (fn (asl,w) =>
    let
      val (r,p,arithmetic,powop,_) = power_setup prime field
      val power = lhs w
      val (x,k) = power_arguments powop power
      val _ = quadratic_pair p x
      val member = EQT_ELIM (arithmetic ``^x IN ^r.carrier``)
      fun seed n =
        let val expression = list_mk_comb (powop,[x,numeral n]) in
          case List.find (fn a => is_eq a andalso aconv (lhs a) expression) asl of
            SOME a =>
              let val _ = quadratic_pair p (rhs a) in ASSUME a end
          | NONE => raise ERR "POWER_STEP_TAC" "Missing preceding power equality"
        end
      val checked =
        if k=0 then
          (REWRITE_CONV [monoidTheory.monoid_exp_0] THENC arithmetic) power
        else
          let
            val even = IntInf.mod(k,2)=0
            val previous = if even then IntInf.div(k,2) else k-1
            val left = seed previous
            val right = if even then left
                        else MP (SPEC x (MATCH_MP field_exp_1 field)) member
            val add_rule = MP (SPEC x (MATCH_MP field_exp_add field)) member
            val law = SPECL [numeral previous,
                            numeral (if even then previous else 1)] add_rule
            val normalized = CONV_RULE
              (LAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV)) law
            val substituted = CONV_RULE
              (RAND_CONV
                (LAND_CONV (REWR_CONV left) THENC
                 RAND_CONV (REWR_CONV right))) normalized
          in TRANS substituted (arithmetic (rhs (concl substituted))) end
    in
      (CONV_TAC (LAND_CONV (K checked)) THEN REFL_TAC) (asl,w)
    end)

end
