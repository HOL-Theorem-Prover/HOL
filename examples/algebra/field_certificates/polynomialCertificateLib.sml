(* Checked polynomial arithmetic over GF p; see polynomialCertificateLib.sig.
   The context takes a theorem of prime <numeral> and a canonical ascending
   num-list monic modulus of positive degree; [] represents polynomial zero.
   ARITH_CONV / BOUNDED_CONV normalize bounded list arithmetic; REMAINDER_CONV
   and MODPOW_CONV prove remainders without unfolding abstract division.
   RABIN12_RULE returns irreducibility for a degree-twelve modulus;
   NO_ROOTS_RULE returns an empty root set when its certificate checks.
   ML division, powering support and Euclid calculations only propose data:
   HOL proves the bounded remainder/Bezout identities before using the rules. *)

structure polynomialCertificateLib :> polynomialCertificateLib =
struct

open HolKernel boolLib bossLib Conv

val ERR = mk_HOL_ERR "polynomialCertificateLib"
val numeral = numSyntax.mk_numeral o Arbnum.fromString
fun integer tm = Arbnum.toLargeInt (numSyntax.dest_numeral tm)
fun literal n = numSyntax.mk_numeral (Arbnum.fromLargeInt n)
fun coefficients tm = map integer (#1 (listSyntax.dest_list tm))
fun polynomial xs = listSyntax.mk_list (map literal xs,numSyntax.num)

(* Candidate arithmetic: none of these ML functions constructs a theorem. *)
fun trim (xs:IntInf.int list) =
  let fun drop (0::rest) = drop rest | drop rest = rest
  in rev (drop (rev xs)) end
fun add p ([],ys) = trim ys
  | add p (xs,[]) = trim xs
  | add p (x::xs,y::ys) = trim (IntInf.mod (x+y,p) :: add p (xs,ys))
fun scale p c xs = trim (map (fn x => IntInf.mod (c*x,p)) xs)
fun sub p (xs,ys) = add p (xs,scale p (~1) ys)
fun mul p ([],_) = []
  | mul p (x::xs,ys) = add p (scale p x ys,0::mul p (xs,ys))
fun inv p a =
  let
    fun loop (r,s,t,u) =
      if s = 0 then
        if r = 1 then IntInf.mod (t,p)
        else raise ERR "inv" "Noninvertible candidate coefficient"
      else let val q = IntInf.div (r,s)
           in loop (s,r-q*s,u,t-q*u) end
  in loop (p,a,0,1) end
fun divide p (a,b) =
  if null b then raise ERR "divide" "Zero candidate divisor"
  else
    let
      val ib = inv p (List.last b)
      fun loop (q,r) =
        if length r < length b then (trim q,r)
        else
          let
            val k = length r-length b
            val c = IntInf.mod (List.last r*ib,p)
            val t = List.tabulate (k,fn _ => 0) @ [c]
          in loop (add p (q,t),sub p (r,mul p (t,b))) end
    in loop ([],trim a) end
fun bezout p (a,b) =
  let
    fun loop (r,s,u,v,w,z) =
      if null s then
        if length r = 1 then
          let val c = inv p (hd r)
          in (scale p c u,scale p c v) end
        else raise ERR "bezout" "Polynomials are not coprime"
      else
        let val (q,t) = divide p (r,s)
        in loop (s,t,w,z,sub p (u,mul p (q,w)),
                             sub p (v,mul p (q,z))) end
  in loop (a,b,[1],[],[],[1]) end

(* GF_eval supplies the computational interface while GF itself remains
   abstract. Unfolding GF would expose noncomputable monoid records.
   Evaluate only bounded list arithmetic, never a large power or poly_mod. *)

val structural = REWRITE_CONV
  [polynomialTheory.poly_mult_def, polynomialTheory.poly_add_def,
   polynomialTheory.weak_mult_def, polynomialTheory.weak_cmult_def,
   polynomialTheory.weak_add_def,
   polyWeakTheory.poly_shift_1_cons,
   polyWeakTheory.poly_shift_of_zero,
   polynomialTheory.poly_zero, fieldInstancesTheory.GF_eval,
   listTheory.NOT_CONS_NIL, listTheory.CONS_11]

(* Expose weak coefficient arithmetic before CBV, but leave chop opaque until
   coefficient-zero guards are decided; unfolding both branches is exponential. *)
fun BOUNDED_CONV () =
  let val evaluate = certificateComputeLib.EVAL_CONV ()
  in structural THENC certificateComputeLib.NAT_CONV THENC
     structural THENC evaluate
  end

fun ARITH_CONV tm = BOUNDED_CONV () tm

fun context prime f =
  let
    val _ = null (hyp prime) orelse
      raise ERR "context" "Expected a closed primality theorem"
    val (head,args) = strip_comb (concl prime)
    val _ = is_const head andalso
      same_const head (prim_mk_const {Thy = "divides", Name = "prime"}) andalso
      length args = 1 orelse
      raise ERR "context" "Expected prime numeral"
    val bounded_conv = BOUNDED_CONV ()
    fun checked tm = EQT_ELIM (bounded_conv tm)
    val pterm = rand (concl prime)
    val p = integer pterm
    val r = ``GF ^pterm``
    val ring = MATCH_MP fieldTheory.field_is_ring
      (MATCH_MP fieldInstancesTheory.GF_field prime)
    val finite = MATCH_MP fieldInstancesTheory.GF_finite_field prime
    val monic = checked ``poly_monic ^r ^f``
    val positive = checked ``0 < poly_deg ^r ^f``
    val fcs = coefficients f
    val remainder_head = rator ``poly_mod ^r``
    fun dest_remainder origin tm =
      case strip_comb tm of
        (head,[r',a,f']) =>
          if not (same_const head remainder_head) then
            raise ERR origin "Expected polynomial remainder"
          else if aconv r r' andalso aconv f f' then a
          else raise ERR origin "Mixed coefficient ring or modulus"
      | _ => raise ERR origin "Expected polynomial remainder"
    fun reduce tm =
      let
        val a = dest_remainder "REMAINDER_CONV" tm
        val value = bounded_conv a
        val at = rhs (concl value)
        val acs = coefficients at
        val (q,b) = divide p (acs,fcs)
        val qt = polynomial q
        val bt = polynomial b
        val rule = SPECL [at,f,qt,bt]
          (MATCH_MP polynomialCertificateTheory.polynomial_certificate_remainder ring)
        val premise = fst (dest_imp (concl rule))
        val transport = AP_THM (AP_TERM ``poly_mod ^r`` value) f
      in TRANS transport (MP rule (checked premise)) end
    fun power tm =
      let
        val powerterm = dest_remainder "MODPOW_CONV" tm
        val (a,e) =
          case total dest_comb powerterm of
            SOME (partial,e) =>
              (case total dest_comb partial of
                 SOME (head,a) =>
                   if aconv head ``(PolyRing ^r).prod.exp`` then (a,e)
                   else raise ERR "MODPOW_CONV" "Expected polynomial power"
               | NONE => raise ERR "MODPOW_CONV" "Expected polynomial power")
          | NONE => raise ERR "MODPOW_CONV" "Expected polynomial power"
        val k =
          case total numSyntax.dest_numeral e of
            SOME k => k
          | NONE => raise ERR "MODPOW_CONV" "Expected closed natural exponent"
        val aproof = checked ``Poly ^r ^a``
        val props = LIST_CONJ [aproof,monic,positive]
        val base = reduce ``poly_mod ^r ^a ^f``
        val expnorm =
          RATOR_CONV (RAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV))
        fun recurse n =
          let
            val nt = numSyntax.mk_numeral n
            val target = ``poly_mod ^r ((PolyRing ^r).prod.exp ^a ^nt) ^f``
          in
            if n = Arbnum.zero then
              let val value = bounded_conv (rand (rator target))
              in TRANS (AP_THM (AP_TERM ``poly_mod ^r`` value) f)
                   (reduce ``poly_mod ^r ^(rhs (concl value)) ^f``) end
            else
              let
                val (half,bit) = Arbnum.divmod (n,Arbnum.fromInt 2)
                val hterm = numSyntax.mk_numeral half
                val subproof = recurse half
                val rule = if bit = Arbnum.zero
                  then polynomialCertificateTheory.polynomial_certificate_pow_even
                  else polynomialCertificateTheory.polynomial_certificate_pow_odd
                val step = MP (SPECL [a,f,hterm] (MATCH_MP rule ring)) props
                val step = CONV_RULE (LAND_CONV expnorm) step
                val result = (REWRITE_CONV [subproof,base] THENC
                  DEPTH_CONV (fn t => reduce t)) (rhs (concl step))
              in TRANS step result end
          end
      in recurse k end
    fun pow n =
      let val nt = literal n
      in power ``poly_mod ^r ((PolyRing ^r).prod.exp [0n;1] ^nt) ^f`` end
    fun difference powerproof =
      let
        val b = sub p (coefficients (rhs (concl powerproof)),[0,1])
        val bt = polynomial b
        val (u,v) = bezout p (fcs,b)
        val ut = polynomial u
        val vt = polynomial v
        val sum = bounded_conv ``(PolyRing ^r).sum.op [0n;1] ^bt``
        val result = TRANS powerproof (SYM sum)
      in (bt,ut,vt,result) end
  in (p,r,ring,finite,monic,power,pow,difference,reduce) end

fun MODPOW_CONV prime f tm =
  let
    val (_,_,_,_,_,power,_,_,_) = context prime f
    val norm =
      (QCONV
         (RATOR_CONV (RAND_CONV (RAND_CONV certificateComputeLib.NAT_CONV))) tm
       handle HOL_ERR _ =>
         raise ERR "MODPOW_CONV" "Expected polynomial power remainder")
  in TRANS norm (power (rhs (concl norm))) end

fun REMAINDER_CONV prime f =
  let val (_,_,_,_,_,_,_,_,reduce) = context prime f
  in reduce end

fun normalize_x prime ring =
  SIMP_CONV (srw_ss())
    [ring, MATCH_MP fieldInstancesTheory.GF_field prime,
     fieldTheory.field_one_ne_zero, polyMonicTheory.poly_X_def,
     fieldInstancesTheory.GF_zero, fieldInstancesTheory.GF_one,
     fieldInstancesTheory.GF_card]

fun RABIN12_RULE prime f =
  let
    val (p,r,ring,finite,_,_,pow,difference,reduce) = context prime f
    val bounded_conv = BOUNDED_CONV ()
    fun compose m n left right =
      let
        val a = rhs (concl left)
        val b = rhs (concl right)
        val rule = SPECL [f,a,b,literal m,literal n]
          (MATCH_MP
            polynomialCertificateTheory.polynomial_certificate_frobenius_compose
            finite)
        val premise = fst (dest_imp (concl rule))
        val proof = TAC_PROOF (([],premise),
          CONV_TAC (normalize_x prime ring) THEN
          CONV_TAC certificateComputeLib.NAT_CONV THEN
          REWRITE_TAC [left,right] THEN
          CONV_TAC bounded_conv)
        val step = CONV_RULE
          (LAND_CONV (normalize_x prime ring THENC
                      certificateComputeLib.NAT_CONV)) (MP rule proof)
      in TRANS step (reduce (rhs (concl step))) end
    val t1 = pow p
    val t2 = compose 1 1 t1 t1
    val t4power = compose 2 2 t2 t2
    val t6power = compose 4 2 t4power t2
    val t12 = compose 6 6 t6power t6power
    val (b4,u4,v4,t4) = difference t4power
    val (b6,u6,v6,t6) = difference t6power
    val rule = SPECL [f,b4,b6,u4,v4,u6,v6]
      (MATCH_MP polynomialCertificateTheory.polynomial_certificate_rabin12 finite)
    val premise = fst (dest_imp (concl rule))
    val proof = TAC_PROOF (([],premise),
      CONV_TAC (normalize_x prime ring) THEN
      CONV_TAC certificateComputeLib.NAT_CONV THEN
      REWRITE_TAC [t4,t6,t12] THEN
      CONV_TAC bounded_conv)
  in MP rule proof end

fun NO_ROOTS_RULE prime f =
  let
    val (p,r,ring,finite,_,_,pow,difference,_) = context prime f
    val bounded_conv = BOUNDED_CONV ()
    val (b,u,v,t) = difference (pow p)
    val rule = SPECL [f,b,u,v]
      (MATCH_MP polynomialCertificateTheory.polynomial_certificate_no_roots finite)
    val premise = fst (dest_imp (concl rule))
    val proof = TAC_PROOF (([],premise),
      CONV_TAC (normalize_x prime ring) THEN
      REWRITE_TAC [t] THEN
      CONV_TAC bounded_conv)
  in MP rule proof end

end
