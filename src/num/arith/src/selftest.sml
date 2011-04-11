open simpLib Parse HolKernel boolLib

fun die s = (print s; Process.exit Process.failure)

fun pr s = print (StringCvt.padRight #" " 60 s)

val _ = pr "Testing REDUCE_ss ..."
val ss = simpLib.empty_ss ++ numSimps.REDUCE_ss
val th = QCONV (SIMP_CONV ss []) ``(0 :num) DIV 0``
val _ = if not (aconv (rhs (concl th)) ``(0 :num) DIV 0``) then
          die "FAILED!\n"
        else print "OK\n"

val _ = pr "Testing SUC_FILTER_ss ..."
val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.SUC_FILTER_ss
val th = QCONV (SIMP_CONV ss [arithmeticTheory.FUNPOW])
               ``FUNPOW (f:'a->'a) 2 x``
val _ = if not (aconv (rhs (concl th)) ``(f:'a -> 'a) (f x)``) then
          die "FAILED!\n"
        else print "OK\n"

val arith_ss = boolSimps.bool_ss ++ numSimps.ARITH_ss
val SIMP_CONV = fn ss => fn thl => QCONV (SIMP_CONV ss thl)
val _ = pr "Testing coefficient gathering in ARITH_ss (1) ..."
val _ = if not (aconv (rhs (concl (SIMP_CONV arith_ss [] ``x + x + x``)))
                      ``3 * x``)
        then die "FAILED!\n"
        else print "OK\n"
val _ = pr "Testing coefficient gathering in ARITH_ss (2) ..."
val _ = if not (aconv (rhs (concl (SIMP_CONV arith_ss [] ``x + x * 2``)))
                      ``3 * x``)
        then die "FAILED\n"
        else print "OK\n"

val _ = pr "Testing arith on ground ctxt ..."
val _ = let
  val (res, vfn) = ASM_SIMP_TAC arith_ss [] ([``2 <= 0``], ``F``)
in
  if null res andalso concl (vfn []) = F then print "OK\n"
  else die "FAILED!\n"
end

val _ = pr "Testing with hypothesis-less context ..."
val _ = let
  val _ = new_constant("foo", ``:num``)
  val foo_ax = new_axiom("foo_ax", ``3 < foo``)
  val goal = ``1 < foo``
  val (res, vfn) = ASM_SIMP_TAC arith_ss [foo_ax] ([], goal)
in
  if null res andalso aconv (concl (vfn [])) goal then print "OK\n"
  else die "FAILED\n"
end

val _ = pr "Testing Alexey Gotsman's arith d.p. problem ..."
val _ = let
  val t =
   ``(e*bv_c+e*(2*bv_cout+wb_sum)+wbs_sum =
        bv_cin+e*(bv_c+wb_a+wb_b)+wbs_a+wbs_b)
     ==>
     (2n*e*bv_cout+e*wb_sum+wbs_sum = bv_cin+e*wb_a+e*wb_b+wbs_a+wbs_b)``
  val result = SOME (Arith.ARITH_CONV t) handle HOL_ERR _ => NONE
in
  case result of
    SOME th => if rhs (concl th) = boolSyntax.T then print "OK\n"
               else die "FAILED!\n"
  | NONE => die "FAILED!\n"
end

val _ = pr "Testing r-cache behaviour with CONJ_ss ..."
val _ = let
  val t = ``(168 = 0) /\ (13 = 13) /\ (105 = 1)``
  open boolSimps
  val result =
      SIMP_CONV (bool_ss ++ CONJ_ss ++ numSimps.ARITH_ss) [] t
in
  if null (hyp result) andalso rhs (concl result) = boolSyntax.F then
    print "OK\n"
  else die "FAILED!\n"
end

val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.MOD_ss ++
         numSimps.ARITH_RWTS_ss
val _ = pr "Testing MOD_ss with constant denominator ..."
val _ = let
  val t = ``(6 * x + 7 + 10 * y) MOD 6``
  val result = SIMP_CONV ss [] t
in
  if aconv (rhs (concl result)) ``(1 + 4 * y) MOD 6`` then print "OK\n"
  else die "FAILED!\n"
end handle _ => die "FAILED!\n"

val _ = pr "Testing MOD_ss with variable denominator ..."
val _ = let
  val t = ``(4 + 3 * n + 1) MOD n``
  val result = SIMP_CONV ss [ASSUME ``0 < n``] t
in
  if aconv (rhs (concl result)) ``5 MOD n`` then print "OK\n"
  else die "FAILED!\n"
end handle _ => die "FAILED!\n"

val _ = Process.exit Process.success
