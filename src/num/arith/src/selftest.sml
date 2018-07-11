open simpLib Parse HolKernel boolLib

open testutils

val pr = tprint

val ss = simpLib.empty_ss ++ numSimps.REDUCE_ss
val _ = convtest("Testing REDUCE_ss on ``0 DIV 0``",
                 QCONV (SIMP_CONV ss[]),
                 ``(0 :num) DIV 0``,
                 ``(0 :num) DIV 0``)

val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.SUC_FILTER_ss
val _ = convtest ("Testing SUC_FILTER_ss",
                  QCONV (SIMP_CONV ss [arithmeticTheory.FUNPOW]),
                  ``FUNPOW (f:'a->'a) 2 x``,
                  ``(f:'a -> 'a) (f x)``);

val arith_ss = boolSimps.bool_ss ++ numSimps.ARITH_ss
val SIMP_CONV = fn ss => fn thl => QCONV (SIMP_CONV ss thl)
val _ = convtest("Testing coefficient gathering in ARITH_ss (1)",
                 SIMP_CONV arith_ss [], ``x + x + x``, ``3 * x``)
val _ = convtest("Testing coefficient gathering in ARITH_ss (2)",
                 SIMP_CONV arith_ss [], ``x + x * 2``, ``3 * x``)

val _ = pr "Testing arith on ground ctxt"
val _ = let
  fun c (res, vfn) =
    if null res andalso concl (vfn []) = F then OK()
    else die "FAILED!\n"
in
  timed(ASM_SIMP_TAC arith_ss []) (exncheck c) ([``2 <= 0``], ``F``)
end

val _ = pr "Testing with hypothesis-less context"
val _ = let
  val _ = new_constant("foo", ``:num``)
  val foo_ax = new_axiom("foo_ax", ``3 < foo``)
  val goal = ``1 < foo``
  fun c (res,vfn) =
    if null res andalso aconv (concl (vfn [])) goal then OK()
    else die "FAILED\n"
in
  timed (ASM_SIMP_TAC arith_ss [foo_ax]) (exncheck c) ([], goal)
end

val _ = new_constant("dimindex", ``:'a itself -> num``)
val _ = convtest ("Testing norming of polymorphic num-range constants",
                  QCONV (SIMP_CONV arith_ss []),
                  “n + dimindex(:'a) + dimindex(:'b) - 1”,
                  “n + (dimindex(:'a) + dimindex(:'b)) - 1”)

val _ = convtest ("COND_ELIM_CONV(1)", Sub_and_cond.COND_ELIM_CONV,
   “z = (if P then x else y:num)”,
   “(P ==> (z:num = x)) /\ (~P ==> (z = y))”);

val _ = convtest ("COND_ELIM_CONV(2)", Sub_and_cond.COND_ELIM_CONV,
   “(if P then x else y:num) = z”,
   “(P ==> (x:num = z)) /\ (~P ==> (y = z))”);

val _ = convtest ("COND_ELIM_CONV(3)", Sub_and_cond.COND_ELIM_CONV,
   “x < a + (if P then y else z:num)”,
   “(P ==> x < a + y) /\ (~P ==> x < a + z)”);

val _ = convtest ("COND_ELIM_CONV(4)", Sub_and_cond.COND_ELIM_CONV,
   “a + (if P then y else z:num) < x”,
   “(P ==> x < a + y) /\ (~P ==> x < a + z)”);

fun TRUE_ARITH nm t =
  convtest("ARITH_CONV: "^nm, Arith.ARITH_CONV, t, boolSyntax.T)

val _ = TRUE_ARITH
          "Alexey Gotsman's problem ..."
          ``(e*bv_c+e*(2*bv_cout+wb_sum)+wbs_sum =
              bv_cin+e*(bv_c+wb_a+wb_b)+wbs_a+wbs_b)
            ==>
            (2n*e*bv_cout+e*wb_sum+wbs_sum = bv_cin+e*wb_a+e*wb_b+wbs_a+wbs_b)``

val _ = TRUE_ARITH
          "Testing arith on nested COND clause"
          ``x <= y ==> x <= y + if p then q else r``

val _ = TRUE_ARITH
          "Subtraction term 1 (should be very quick)"
          ``1 <= x /\ (i = 1) ==> (x - PRE i - SUC (PRE i - PRE i) = x - 1)``

val _ = TRUE_ARITH
          "Subtraction + cond (should be very quick)"
          ``(if x = 0 then 1 else 0) = 1 - x``

val _ = TRUE_ARITH
          "Distributing subtraction over multiplication"
          ``0 < b ⇒ (a * b − a = (b − 1) * a)``

val _ = TRUE_ARITH
          "Horrible subtraction + conditional"
          ``!j i. i <> j ==>
              (if (if i < j then i + 1 else i − 1) < j then
                 j − if i < j then i + 1 else i − 1
               else (if i < j then i + 1 else i − 1) − j) <
              if i < j then j − i else i − j``

val _ = pr "Testing r-cache behaviour with CONJ_ss"
val _ = let
  val t = ``(168 = 0) /\ (13 = 13) /\ (105 = 1)``
  open boolSimps
  val result =
      SIMP_CONV (bool_ss ++ CONJ_ss ++ numSimps.ARITH_ss) [] t
in
  if null (hyp result) andalso rhs (concl result) = boolSyntax.F then
    OK()
  else die "FAILED!\n"
end

val ss = boolSimps.bool_ss ++ numSimps.REDUCE_ss ++ numSimps.MOD_ss ++
         numSimps.ARITH_RWTS_ss
val _ = pr "Testing MOD_ss with constant denominator"
val _ = let
  val t = ``(6 * x + 7 + 10 * y) MOD 6``
  val result = SIMP_CONV ss [] t
in
  if aconv (rhs (concl result)) ``(1 + 4 * y) MOD 6`` then OK()
  else die "FAILED!\n"
end handle _ => die "FAILED!\n"

val _ = pr "Testing MOD_ss with variable denominator"
val _ = let
  val t = ``(4 + 3 * n + 1) MOD n``
  val result = SIMP_CONV ss [ASSUME ``0 < n``] t
in
  if aconv (rhs (concl result)) ``5 MOD n`` then OK()
  else die "FAILED!\n"
end handle _ => die "FAILED!\n"

val _ = tprint "Testing MOD_ss with SUC"
val _ = let
  val t = ``(SUC (x MOD 3) + 10) MOD 3``
  val result = SIMP_CONV ss [] t
in
  if aconv (rhs (concl result)) ``(SUC x + 1) MOD 3`` then OK()
  else die "FAILED!\n"
end

val _ = tprint "Testing MOD_ss with EXP"
val _ = let
  val t = ``((x MOD 3 + 10) ** 10 + 10) MOD 3``
  val result = SIMP_CONV ss [] t
in
  if aconv (rhs (concl result)) ``((x + 1) ** 10 + 1) MOD 3`` then OK()
  else die "FAILED!\n"
end

val _ = Process.exit Process.success
