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
    if null res andalso Feq (concl (vfn [])) then OK()
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
   “(P ==> a + y < x) /\ (~P ==> a + z < x)”);

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

val _ = TRUE_ARITH "Existential in implication on left"
                   “(2 < j ==> ?u. 0 < u ∧ u <= j − 1) ∧ 0 < j ==> 1 <= j”

val _ = pr "Testing r-cache behaviour with CONJ_ss"
val _ = let
  val t = ``(168 = 0) /\ (13 = 13) /\ (105 = 1)``
  open boolSimps
  val result =
      SIMP_CONV (bool_ss ++ CONJ_ss ++ numSimps.ARITH_ss) [] t
in
  if null (hyp result) andalso aconv (rhs (concl result)) boolSyntax.F then
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

val _ = List.app convtest [
  ("Testing MOD_ss with EXP", SIMP_CONV ss [],
   “((x MOD 3 + 10) ** 10 + 10) MOD 3”, “((x + 1) ** 10 + 1) MOD 3”),
  ("AND_CONV(1)", Boolconv.AND_CONV, “(\x. x) p /\ (\y. y) p”,
   “(\a:bool. a) p”),
  ("OR_CONV(1)", Boolconv.OR_CONV, “(\x. x) p \/ (\y. y) p”, “(\a:bool. a) p”),
  ("IMP_CONV(1)", Boolconv.IMP_CONV, “(\x. x) p ==> (\y. y) p”, “T”),
  ("BEQ_CONV(1)", Boolconv.BEQ_CONV, “(\x. x) (p:bool) = (\y. y) p”, “T”),
  ("COND_CONV(1)", Boolconv.COND_CONV, “if b then (\x:'a. x) else (\y. y)”,
   “\a:'a. a”),
  ("sum_eq_norm", NumRelNorms.sum_eq_norm, “SUC (SUC (SUC n)) = 3”, “n = 0”),
  ("ARITH_NORM_ss(1)", SIMP_CONV (ss ++ numSimps.ARITH_NORM_ss) [], “SUC m - 9”, “m - 8”),
  ("ARITH_NORM_ss(2)", SIMP_CONV (ss ++ numSimps.ARITH_NORM_ss) [], “SUC m - 4”, “m - 3”),
  ("ARITH_NORM_ss(3)", SIMP_CONV (ss ++ numSimps.ARITH_NORM_ss) [], “SUC m - 0”, “SUC m”)
];

val _ = Feedback.emit_WARNING := false

val _ = let
  open boolSimps numSimps
  val _ = clear_arith_caches()
  val _ = tprint "Checking cache-fouling with theorems about constants(1)"
  val c1c2 = new_specification("c1c2", ["c1", "c2"],
                Q.prove(‘∃c d:num. c < d’,
                        MAP_EVERY Q.EXISTS_TAC [‘0’, ‘1’] >>
                        reduceLib.REDUCE_TAC));
  val tm = “c1 <> 0 \/ c2 <> 0”
  val ss = bool_ss ++ ARITH_ss
  val _ = QCONV (SIMP_CONV ss []) tm (* taint *)
    (* examine cache with
         Cache.cache_values numSimps.arith_cache
    *)
  fun check (Exn.Res th) = rhs (concl th) ~~ T
    | check _ = false
  val _ = require_msg check (term_to_string o rhs o concl)
                      (SIMP_CONV (bool_ss ++ ARITH_ss) [c1c2])
                      tm

  val _ = tprint "Checking cache-fouling with theorems about constants(2)"
  val c3_def = new_definition("c3", “c3 = 10”)
  val goal = ([“c3 < x”, “x < 3”], “p:bool”)
  val _ = VALID (FULL_SIMP_TAC ss []) goal
  fun prg(asl,w) =
      "([" ^ String.concatWith ", " (map term_to_string asl) ^ "], " ^
      term_to_string w ^ ")"
  fun pr (sgs, vf) =
      "[" ^ String.concatWith ",\n     " (map prg sgs) ^ "]"
  val _ = require_msg (check_result (null o #1)) pr
                      (VALID (FULL_SIMP_TAC ss [c3_def]))
                      goal

  fun cached_simp thl g = VALID (FULL_SIMP_TAC ss thl) g
  fun uncached_simp thl g =
      (clear_arith_caches(); VALID (FULL_SIMP_TAC ss thl)) g

  val list_eq = Portable.list_eq and pair_eq = Portable.pair_eq
  fun tac_result_eq (sgs1, vf1) (sgs2, vf2) =
      list_eq (pair_eq (list_eq aconv) aconv) sgs1 sgs2
  fun testseq s =
      (map (fn (a,x) => cached_simp a x) s,
       map (fn (a,x) => uncached_simp a x) s)

  val _ = tprint "Checking cached/uncached equivalency (1)"
  val seq1 = [([c3_def], goal), ([], goal)]
  val _ = require (check_result (uncurry (list_eq tac_result_eq))) testseq seq1

  val _ = tprint "Checking cached/uncached equivalency (2)"
  val seq2 = [([], goal), ([c3_def], goal)]
  val _ = require (check_result (uncurry (list_eq tac_result_eq))) testseq seq2

  val _ = tprint "Checking cached/uncached equivalency (3)"
  val seq3 = [([], goal), ([c3_def], goal), ([], goal)]
  val _ = require (check_result (uncurry (list_eq tac_result_eq))) testseq seq3
in
  app delete_const ["c1", "c2", "c3", "foo"]
end

val _ = let
  open numSimps boolSimps
  val asm = “(2 < j ==> ?u. 0 < u /\ u <= j - 1) /\ 0 < j”
  val g = mk_imp(asm, “1 <= j”)
  val g' = “!u. (2 < j ==> 0 < u /\ u <= j - 1) /\ 0 < j ==> 1<= j”
  fun tts t = "“" ^ term_to_string t ^ "”"
  fun pr_goal (asl,g) = "([" ^ String.concatWith ", " (map term_to_string asl) ^
                        "], " ^ tts g ^ ")"
  fun pr_result (sgs, _) =
      "[" ^ String.concatWith ", " (map pr_goal sgs) ^ "]"
  fun test0 g =
      (clear_arith_caches(); simp_tac (bool_ss ++ ARITH_ss) [] ([], g))
  fun test (msg, g) =
      (tprint msg;
       require_msg
         (check_result (fn (sgs, vfn) => null sgs andalso concl (vfn []) ~~ g))
         pr_result
         test0
         g)

in
  app (ignore o test) [
    ("Github issue 642 assumption handling (1)", g'),
    ("Github issue 642 assumption handling (2)", g)
  ]
end

val _ = let
  open BasicProvers
  val _ = quietly srw_ss()
  val _ = tprint "srw_ss() on num_CASE (NUMERAL ...)"
in
  require_msg (check_result (aconv “20” o rhs o concl))
              thm_to_string
              (SIMP_CONV (srw_ss()) [])
              “case 11 of 0 => 3 | SUC n => n * 2”
end

val _ = let
  open Cache
  fun mk_test_cache cap =
      CACHE {capacity=cap, per_key_cap=1000}
            ((fn _ => true), (fn _ => fn tm => REFL tm))
  fun touch (cconv, _) tm = ignore (cconv [] tm)
  fun touch_all c tms = app (touch c) tms
  fun keys_of (_, cache) = map #1 (cache_values cache)
  fun expect b = if b then OK() else die "FAILED\n"

  val _ = tprint "Cache: enforces capacity bound"
  val c0 = mk_test_cache 4
  val _ = touch_all c0 [“1n”, “2n”, “3n”, “4n”, “5n”, “6n”]
  val _ = expect (length (keys_of c0) = 4)

  val _ = tprint "Cache: drops least-recently-used key on overflow"
  val c1 = mk_test_cache 4
  val _ = touch_all c1 [“1n”, “2n”, “3n”, “4n”, “5n”]
  val ks1 = keys_of c1
  val _ = expect (length ks1 = 4 andalso
                  not (List.exists (aconv “1n”) ks1) andalso
                  List.exists (aconv “5n”) ks1)

  val _ = tprint "Cache: cache hit bumps key to most-recently-used"
  val c2 = mk_test_cache 4
  val _ = touch_all c2 [“1n”, “2n”, “3n”, “4n”, “1n”, “5n”]
  val ks2 = keys_of c2
  val _ = expect (length ks2 = 4 andalso
                  List.exists (aconv “1n”) ks2 andalso
                  not (List.exists (aconv “2n”) ks2))

  val _ = tprint "Cache: clear_cache resets the cache"
  val c3 = mk_test_cache 4
  val _ = touch_all c3 [“1n”, “2n”]
  val _ = clear_cache (#2 c3)
  val _ = expect (null (keys_of c3))
  val _ = touch c3 “7n”
  val _ = expect (length (keys_of c3) = 1)

  val _ = tprint "Cache: per-key entry list bounded under repeated misses"
  fun failing_conv (_:thm list) (_:term) : thm = failwith "always fails"
  val pkc = 8
  val (cconv4, cache4) =
      CACHE {capacity=100, per_key_cap=pkc}
            ((fn _ => true), failing_conv)
  val key = “7n + 7n = 14n”  (* bool, as the failure-trace handler expects *)
  fun assumption i = ASSUME (mk_var ("p_" ^ Int.toString i, Type.bool))
  fun trial i = (cconv4 [assumption i] key; ()) handle _ => ()
  val n_trials = 100
  val _ = List.tabulate (n_trials, trial)
  val stored =
      case List.find (aconv key o #1) (cache_values cache4) of
        NONE => []
      | SOME (_, lst) => lst
  (* Each stored entry's hypset contains the assumption's bool variable.
     Stored list is cons-order — newest at head — so the surviving
     indices should be n_trials-1 down to n_trials-pkc. *)
  fun idx_of_entry (terms, _) =
      case List.mapPartial
             (fn t => if is_var t then
                        Int.fromString
                          (String.extract (#1 (dest_var t), 2, NONE))
                      else NONE)
             terms of
        []     => NONE
      | i :: _ => SOME i
  val survivors = List.mapPartial idx_of_entry stored
  val expected = List.tabulate (pkc, fn k => n_trials - 1 - k)
  val _ = if length stored = pkc andalso survivors = expected then OK()
          else die ("FAILED: " ^ Int.toString (length stored) ^
                    " entries; survivors [" ^
                    String.concatWith "," (map Int.toString survivors) ^
                    "]\n")

  val _ = tprint "Cache: repeat call returns hit without rerunning conv"
  val n_calls = ref 0
  fun counting_conv (_:thm list) tm =
      (n_calls := !n_calls + 1; REFL tm)
  val (cconv5, _) =
      CACHE {capacity=4, per_key_cap=4}
            ((fn _ => true), counting_conv)
  val r1 = cconv5 [] “1n”
  val r2 = cconv5 [] “1n”
  val r3 = cconv5 [] “2n”
  val _ = expect (!n_calls = 2 andalso
                  aconv (concl r1) (concl r2) andalso
                  aconv (concl r3) (mk_eq (“2n”, “2n”)))
in
  ()
end

val _ = Process.exit Process.success
