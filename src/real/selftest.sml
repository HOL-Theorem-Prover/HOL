open HolKernel Parse bossLib boolLib;

open simpLib realSimps isqrtLib RealArith RealField bitArithLib;

open testutils;

(* The original version and old port by Hurd *)
val REAL_ARITH0 = RealArith.OLD_REAL_ARITH;
(* The new port, only suppports integral coefficients *)
val REAL_ARITH1 = RealArith.REAL_ARITH;
(* The new port, also suppports rational coefficients *)
val REAL_ARITH2 = RealField.REAL_ARITH;

val s = SIMP_CONV (bossLib.std_ss ++ REAL_REDUCE_ss) [LET_THM]

fun test conv nm (problem, result) = let
  val t2s = trace ("Unicode", 0) term_to_string
in
  convtest("[" ^ nm ^ "] " ^ t2s problem ^ " = " ^ t2s result,
           conv, problem, result)
end;

val real_reduce_simp_tests = [
  (“~~3r”        , “3r”),
  (“3r + 4”      , “7r”),
  (“3 - 4r”      , “~1r”),
  (“abs (~20r)”  , “20r”),
  (“abs (1/6)”   , “1/6”),
  (“abs (~3/6)”  , “1/2”),
  (“abs 0”       , “0”),
  (“3r * 3/4”    , “9/4”),
  (“6/~8”        , “~3/4”),
  (“1/3 + 1/2”   , “5/6”),
  (“1/2 = 0”     , “F”),
  (“0 + 3r”      , “3r”),
  (“3r * 0”      , “0r”),
  (“~0r”         , “0r”),
  (“1r - 0”      , “1r”),
  (“1 / 10 + 0r” , “1r/10”),
  (“0r + 1 / 10” , “1r/10”),
  (“1/2 * 0r”    , “0r”),
  (“0r * 1/2”    , “0r”),
  (“flr 10”      , “10n”),
  (“clg 12”      , “12n”),
  (“flr (1/10)”  , “0n”),
  (“clg (1/10)”  , “1n”),
  (“flr (131/10)”, “13n”),
  (“clg (131/10)”, “14n”),
  (“flr (-2/4)”  , “0n”),
  (“clg (-2/4)”  , “0n”)
]

val _ = List.app (test s "simp") real_reduce_simp_tests
val _ = List.app (test EVAL "EVAL") real_reduce_simp_tests

fun isunch UNCHANGED = true | isunch _ = false
val _ = List.app (shouldfail {testfn = s, printresult = thm_to_string,
                              printarg = fn t => "Testing SIMP_CONV “" ^
                                                 term_to_string t ^
                                                 "” raises UNCHANGED",
                              checkexn = isunch})
                 [“flr x”, “clg x”, “flr (10/x)”, “clg (10/x)”,
                  “flr (-x/5)”, “clg(-x/5)”]


val _ = List.app
          (fn (s1,s2) => tpp_expected
                           {testf=standard_tpp_message, input=s1, output=s2})
          [("realinv 2", "2⁻¹"), ("inv (TC R)", "R⁺ ᵀ")]
val _ = tpp "¬p ∧ q"                                                   (* UOK *)

fun nftest (r as (n,c,t1,t2)) =
    let
      fun test (t1,t2) = (Exn.capture c t1, Exn.capture c t2)
      fun check t res =
          case res of
              Exn.Res (Exn.Res rth, Exn.Exn Conv.UNCHANGED) =>
                rhs (concl rth) ~~ t
            | _ => false
      fun pr1 t (Exn.Exn e) = "On first call, unexpected exn: " ^
                                General.exnMessage e
        | pr1 t (Exn.Res th) = if is_eq (concl th) andalso
                                  rhs (concl th) ~~ t
                               then ""
                               else "On first call, unexpected thm:\n  " ^
                                    thm_to_string th
      fun nlnzero "" = "" | nlnzero s = s ^ "\n"
      fun pr2 (Exn.Exn Conv.UNCHANGED) s = s
        | pr2 (Exn.Exn e) s = nlnzero s ^ "On 2nd call, unexpected exn: " ^
                              General.exnMessage e
        | pr2 (Exn.Res th) s = nlnzero s ^ "On 2nd call, unexpected thm:\n  " ^
                               thm_to_string th
      fun pr t (r1,r2) = pr2 r2 (pr1 t r1)
    in
      tprint (n ^ ": " ^ term_to_string t1 ^ " TO: " ^ term_to_string t2);
      require_msg (check t2) (pr t2) test (t1,t2)
    end
fun simpl ths = SIMP_CONV (BasicProvers.srw_ss()) ths
fun asimpl ths = SIMP_CONV (BasicProvers.srw_ss() ++ numSimps.ARITH_ss) ths
val simp = simpl []
val _ = List.app nftest [
      ("MULCANON01", REALMULCANON, “x:real * y * x”, “x pow 2 * y”),
      ("MULCANON02", REALMULCANON, “x:real * y * x * 2”, “2 * (x pow 2 * y)”),
      ("MULCANON03", REALMULCANON,
       “10 * (x:real) * y * x pow 3 * y * x pow 4 * z * 6”,
       “60 * (x pow 8 * y pow 2 * z)”),
      ("MULCANON04", REALMULCANON, “x * 1r * z”, “x:real * z”),
      ("MULCANON05", REALMULCANON, “x * y * inv x * a”, “a * y * NZ x”),
      ("MULCANON06", REALMULCANON, “b * x pow 2 * y * inv x * a”,
       “a * b * x * y”),
      ("MULCANON07", REALMULCANON, “b * x * y * inv (x pow 2) * 2 * a”,
       “2 * (a * b * inv x * y)”),
      ("MULCANON08", REALMULCANON, “b * x * y * inv (x pow 2) * a * inv x”,
       “a * b * inv x pow 2 * y”),
      ("MULCANON09", REALMULCANON, “x * 2r”, “2r * x”),
      ("MULCANON10", REALMULCANON, “x * 2r * y”, “2r * (x * y)”),
      ("MULCANON11", REALMULCANON, “x * 3 * y * x pow n * z”,
       “3 * (x * y * z * x pow n)”),
      ("MULCANON12", REALMULCANON, “2 pow x * z * 10 * 2 pow n”,
       “10 * (z * 2 pow n * 2 pow x)”),
      ("MULCANON13", REALMULCANON, “-(2 pow x) * z * -10 * 2 pow n”,
       “10 * (z * 2 pow n * 2 pow x)”),
      ("MULCANON14", REALMULCANON, “inv 2 pow x * z * 2 pow x”, “z:real”),
      ("MULCANON15", REALMULCANON, “inv (2 pow x) * z * 3 * 2 pow x”,
       “3 * z:real”),
      ("MULCANON16", REALMULCANON, “inv (2 pow x) * z * 3”,
       “3 * (z * inv (2 pow x))”),
      ("MULCANON17", REALMULCANON, “4 * (inv 2 * z)”, “2r * z”),
      ("MULCANON18", REALMULCANON,
       “2 * (inv 3 * z * 2 * inv 10)”, “(2r/15) * z”),
      ("MULCANON19", REALMULCANON, “2 * (inv 3 * z * 6 * inv 4)”, “z:real”),
      ("MULCANON21", REALMULCANON, “-z * x: real”, “-x * z:real”),
      ("MULCANON22", REALMULCANON, “2 * (-inv 3 * z * 6 * inv 4)”, “-z:real”),
      ("MULCANON23", REALMULCANON,
       “(2/3) * (z * y:real)”, “(2/3) * (y * z:real)”),
      ("MULCANON24", REALMULCANON,
       “2 pow x * y pow 2 * 2 pow x * inv y”, “y * (2 pow x) pow 2”),
      ("MULCANON25", REALMULCANON,
       “x * y * (2 pow b) pow 2 * inv 2 pow b”, “x * y * 2 pow b”),
      ("MULCANON26", REALMULCANON, “2 * x * inv 2 pow 2”, “1/2 * x:real”),
      ("MULCANON27", REALMULCANON, “2r * y * 3 / (x * y)”,
       “6r * (inv x * NZ y)”),
      ("MULCANON28", REALMULCANON, “x * (9r * y)”, “9r * (x * y)”),
      ("MULCANON29", REALMULCANON, “x * y / 2 * x”, “1/2 * (x pow 2 * y)”),
      ("MULCANON30", REALMULCANON, “-(-a * x:real)”, “a * x : real”),
      ("MULCANON31", REALMULCANON, “-(2/3r)”, “-2 / 3r”),
      ("MULCANON32", REALMULCANON, “-a * -x:real”, “a * x : real”),
      ("MULCANON33", REALMULCANON, “-x * z * 2 pow 0 * y : real”,
       “-x * y * z : real”),
      ("MULCANON34", REALMULCANON, “2 * s pow 2 / 64”, “1 / 32 * s pow 2”),
      ("MULCANON35", REALMULCANON,
       “-exp hx * p pow 2 * exp hx * (1 - p)”,
       “-(p pow 2) * (exp hx) pow 2 * (1 - p)”),
      ("MULCANON36", REALMULCANON, “-1 * (x * y) : real”, “-x * y:real”),
      ("MULCANON37", REALMULCANON, “-1 * x : real”, “-x:real”),
      ("MULCANON38", REALMULCANON, “1r * x”, “x:real”),

      ("MULRELNORM01", simp,
       “z <> 0 ⇒ 2r * z pow 2 * inv yy = 5 * z pow 2 * inv y * a”,
       “z <> 0 ⇒ 2 * inv yy = 5 * (a * inv y)”),
      ("MULRELNORM02", simp, “z * 4 = inv x * 6”, “2 * z = 3 * inv x”),
      ("MULRELNORM03", simp,
       “y <> 0 ==> 2 * inv y pow 2 <= 9 * inv y * z”,
       “y <> 0 ==> 2 <= 9 * (y * z)”),
      ("MULRELNORM04", simp,
       “inv (2 pow x) * inv y pow 2 <= 9 * inv y * inv 2 pow x”,
       “inv y pow 2 <= 9 * inv y”),
      ("MULRELNORM05", simp,
       “y <> 0 ==>
        inv (2 pow x) * inv y pow 2 <= 9 * inv y pow 6 * inv 2 pow x”,
       “y <> 0 ==> y pow 4 <= 9”),
      ("MULRELNORM06", simp,
       “0 < x ==> 3 * x pow 2 <= x”, “0 < x ==> 3 * x <= 1r”),
      ("MULRELNORM07", simp,
       “0 < x ==> 3 * x pow 2 <= inv x”, “0 < x ==> 3 * x pow 3 <= 1r”),
      ("MULRELNORM08", simp, “2 * x <= inv 2 * y * z”, “4r * x <= y * z”),
      ("MULRELNORM09", simp, “2 * x <= 1/2 * (y * z:real)”, “4r * x <= y * z”),
      ("MULRELNORM10", simp,
       “3/4 * x <= 5/6 * (y * z:real)”, “9r * x <= 10 * (y * z)”),
      ("MULRELNORM11", simp, “0r < x ==> x <= x * y”, “0r < x ==> 1 <= y”),
      ("MULRELNORM12", simpl [ASSUME “x <> 0r”, ASSUME “x < 0r”,
                              ASSUME “x < 1r”],
       “inv x < 1r”, “T”),
      ("MULRELNORM13", simp, “x <> 0 /\ x < 0 ==> inv x < 1r”,
       “x <> 0 /\ x < 0 ==> x < 1”),
      ("MULRELNORM14", simp, “x <> 0 /\ 0 < x ==> inv x < 1r”,
       “x <> 0 /\ 0 < x ==> 1 < x”),
      ("MULRELNORM15", simp, “2r * x = 1/2 * z”, “4 * x = z”),
      ("MULRELNORM16", asimpl [ASSUME “m < lg : num”],
       “inv (2 pow m) < 2 * inv (2 pow lg)”,
       “2 pow lg < 2 * 2 pow m”),
      ("MULRELNORM17", simpl [ASSUME “0r < U”],
       “U * a * b <= -U”, “a * b <= -1”),
      ("MULRELNORM18", simp, “-x * y * z = a * -b * c:real”, “x * y * z = a * b * c:real”),
      ("MULRELNORM19", simp, “-2 * x * y * z = a * -6 * b * c:real”,
       “x * y * z = 3 * (a * b * c):real”),
      ("MULRELNORM20", simp, “-x * y * z < a * -b * c:real”, “a * b * c < x * y * z:real”),
      ("MULRELNORM21", simp, “-2 * x * y * z < a * -3 * b * c:real”,
       “3 * (a * b * c) < 2 * (x * y * z):real”),
      ("MULRELNORM22", simp, “-x * y * z <= a * -b * c:real”, “a * b * c <= x * y * z:real”),
      ("MULRELNORM23", simp, “x * -2 * y * z <= a * -b * c:real”,
       “a * b * c <= 2 * (x * y * z):real”),
      ("MULRELNORM24", simp, “x * -2 * y * z <= a * b * c:real”,
       “-2 * (x * y * z):real <= a * b * c”),
      ("MULRELNORM25", simp, “x * -2 * y <= 6r”, “-x * y <= 3r”),
      ("MULRELNORM26", simp, “x * -2 * y = 6r * z”, “x * y = -3r * z”),
      ("MULRELNORM27", simp, “x * -2 * y = 6r”, “x * y = -3r”),
      ("MULRELNORM28", simp, “x * -2 * y = z”, “2 * (x * y) = -z”),
      ("MULRELNORM29", simp, “x * -2 * y = -a * z * -b”, “2 * (x * y) = -a * b * z”),
      ("MULRELNORM30", simp, “4r * B <= 4 * (A * B)”, “B:real <= A * B”),
      ("MULRELNORM31", simp,
       “X * 2 pow e1 * 2 pow e2 < 2 pow e3 * (2 pow e2) pow 2”,
       “X * 2 pow e1 < 2 pow e2 * 2 pow e3”),
      ("MULRELNORM32", simp, “x / 2r = y”, “x = 2 * y”),
      ("MULRELNORM33", simp, “x pow 4 = (inv x) pow 3”, “x = 0 \/ x pow 7 = 1”),
      ("ADDCANON1", REALADDCANON, “10 + x * 2 + x * y + 6 + x”,
       “3 * x + x * y + 16”)
    ]

val simpc = SIMP_CONV (srw_ss() ++ ARITH_ss ++ REAL_ARITH_ss)
val _ = shouldfail {
      checkexn = (fn UNCHANGED => true | _ => false),
      printarg =
      fn _ => "simp w/o nat d.p. but with real d.p. leaves input unchanged",
      printresult = thm_to_string,
      testfn = simpc [Excl "NUM_ARITH_DP"]
    } “4n < x ==> 2 < x”
val _ = shouldfail {
      checkexn = (fn UNCHANGED => true | _ => false),
      printarg =
      fn _ => "simp with nat d.p. but w/o real d.p. leaves input unchanged",
      printresult = thm_to_string,
      testfn = simpc [Excl "REAL_ARITH_DP"]
    } “4r < x ==> 2 < x”

val _ = tprint "Removing nat d.p. still lets real d.p. work"
val _ = require_msg (check_result (aconv “bool$T”))
                    term_to_string
                    (rhs o concl o simpc [Excl "NUM_ARITH_DP"])
                    “4r < x ==> 2 < x”
val _ = tprint "Removing real d.p. still lets nat d.p. work"
val _ = require_msg (check_result (aconv “bool$T”))
                    term_to_string
                    (rhs o concl o simpc [Excl "REAL_ARITH_DP"])
                    “4n < x ==> 2 < x”

fun isqrt_test (r as (n,f,df)) =
    let
      fun check res = aconv df (snd (dest_comb (concl res)));
    in
      tprint (n ^ ": " ^ term_to_string f ^ " = " ^ term_to_string df);
      require_msg (check_result check) (term_to_string o concl) iSQRT_COMPUTE_CONV f
    end;

val _ = List.app isqrt_test [
      ("iSQRT00", “sqrt 0”,    “(0 :real)”),
      ("iSQRT01", “sqrt 4”,    “(2 :real)”),
      ("iSQRT02", “sqrt 1024”, “(32 :real)”)];

(* Tests of various real arithmetic conversions in RealArith.sml *)
fun real_int_reduce_test (r as (n,f,df)) =
    let
      fun check res = aconv df (snd (dest_comb (concl res)));
    in
      tprint (n ^ ": " ^ term_to_string f ^ " = " ^ term_to_string df);
      require_msg (check_result check) (term_to_string o concl) REAL_INT_REDUCE_CONV f
    end;

val _ = List.app real_int_reduce_test [
      ("REAL_INT_ADD00", “&0 + &1”, “&1”),
      ("REAL_INT_ADD01", “&1 + &99999”, “&100000”),
      ("REAL_INT_SUB00", “&10000 - &10000”, “&0”),
      ("REAL_INT_SUB01", “&10000 - &1”, “&9999”),
      ("REAL_INT_NEG00", “~&0”, “&0”),
      ("REAL_INT_NEG01", “~~&1”, “&1”),
      ("REAL_INT_MUL00", “&0 * &1000”, “&0”),
      ("REAL_INT_MUL01", “&877 * &27644437”, “&24244171249”),
      ("REAL_INT_POW00", “&2 pow 0”, “&1”),
      ("REAL_INT_POW01", “&2 pow 32”, “&4294967296”),
      ("REAL_INT_ABS00", “abs (&1)”, “&1”),
      ("REAL_INT_ABS01", “abs (~&1)”, “&1”),
      ("REAL_INT_RED00", “((&1 + &2) * &3 - abs(~&5)) pow 2 + &1”, “&17”)
      ];

(* Tests of REAL_ARITH(s) *)
fun real_arith_test prover (r as (n,tm)) =
    let
      fun check res = aconv tm (concl res);
    in
      tprint (n ^ ": " ^ term_to_string tm);
      require_msg (check_result check) (term_to_string o concl) prover tm
    end;

(* Tests for REAL_ARITH1 *)
val _ = List.app (real_arith_test REAL_ARITH1) [
      ("REAL_ARITH1_00", “x + y:real = y + x”),
      ("REAL_ARITH1_01", “&0 < x ==> &0 <= x”),
      ("REAL_ARITH1_02", “x + ~x = &0”),
      ("REAL_ARITH1_03", “&0 <= x ==> &0 <= y ==> &0 <= x + y”),
      ("REAL_ARITH1_04", “&1 * x + &0 = x”),
      ("REAL_ARITH1_05", “&3 * x + &4 * x = &7 * x”),
      ("REAL_ARITH1_06", “&300 * x + &400 * x = &700 * x”),
      ("REAL_ARITH1_07", “x < y:real ==> x <= y”),
      ("REAL_ARITH1_08", “(x + z:real = y + z) ==> (x = y)”),
      ("REAL_ARITH1_09", “(x <= y:real /\ y <= z) ==> x <= z”),
      ("REAL_ARITH1_10", “x:real <= y ==> y < z ==> x < z”),
      ("REAL_ARITH1_11", “&0 < x /\ &0 < y ==> x + y < &1
                     ==> &144 * x + &100 * y < &144”),
      ("REAL_ARITH1_12", “!x y. x <= ~y <=> x + y <= &0”),

      ("REAL_ARITH1_13", “0 <= &n”),
      ("REAL_ARITH1_14", “0 < &SUC n”), (* this is a new feature *)
      ("REAL_ARITH1_14", “0 < b ==> a < (a :real) + b”)
    ];

(* Tests for REAL_ARITH2, some passed REAL_ARITH1 but failed here *)
val _ = List.app (real_arith_test REAL_ARITH2) [
      (* self test sample, cf. REAL_HALF *)
      ("REAL_ARITH2_00", “x / 3 + x / 3 + x / 3 = x”),

      (* from somewhere *)
      ("REAL_ARITH2_01", “abs x <= abs y ==> 0 <= abs x /\ abs x <= abs y”),

      (* from iterateTheory.FINITE_REAL_INTERVAL *)
      ("REAL_ARITH2_02", “a + x / y < b <=> x / y < b - a:real”),

      (* from iterateTheory.SUM_GP_BASIC *)
      ("REAL_ARITH2_03", “1 - x * x pow n + (1 - x) * (x * x pow n) = 1 - x * (x * x pow n)”),

      (* from real_topologyTheory.LINEAR_INJECTIVE_LEFT_INVERSE
         NOTE: Hurd's REAL_ARITH can solve this but HOL-Light's original one cannot.
       *)
      ("REAL_ARITH2_04", “((f :real->real) (&0 * &0) = &0 * f (&0)) ==> (&0 = f (&0))”),

      (* from real_topologyTheory.SEQ_HARMONIC_OFFSET *)
      ("REAL_ARITH2_05", “0 < e ==> N <> 0 ==> 0 < &N ==> realinv (&N) < e ==>
                          -a <= &M ==> &M + &N <= &n ==> &n + a <> 0 ==> &N <= abs (&n + a)”),

      (* from real_topologyTheory.CLOSED_STANDARD_HYPERPLANE *)
      ("REAL_ARITH2_06", “closed {x | 1 * x = (a:real)} ==> closed {x | x = (a:real)}”),

      (* from integrationTheory.FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG *)
      ("REAL_ARITH2_07", “x = (b:real) ==> &0 < &1 ==> 0 <= e / 2 pow (4 + n b) * 0”)
    ];

fun real_poly_test (r as (n,f,df)) =
    let
      fun check res = aconv df (snd (dest_comb (concl res)));
    in
      tprint (n ^ ": " ^ term_to_string f ^ " = " ^ term_to_string df);
      require_msg (check_result check) (term_to_string o concl) REAL_POLY_CONV f
    end;

val _ = List.app real_poly_test [
      ("REAL_POLY_00", “1 - x * x pow n + (1 - x) * (x * x pow n)”,
                       “-1 * x pow SUC (SUC n) + 1”),
      ("REAL_POLY_01", “3 * (x * realinv 3)”, “x:real”),
      ("REAL_POLY_02", “e / 2 pow (4 + n b) * 0”, “0”)
    ];

(* Tests for REAL_RING *)
val _ = List.app (real_arith_test REAL_RING) [
      ("REAL_RING_00", “(inv(x) * inv(y) = &1) \/ ~(y = &0) \/ ~(x = &0) \/ ~(x * y = &1)”)
    ];

(* Tests for REAL_FIELD *)
val _ = List.app (real_arith_test REAL_FIELD) [
      ("REAL_FIELD_00", “x * y = &1 ==> inv x * inv y = &1”),

      (* This example is from HOL-Light's sets.ml *)
      ("REAL_FIELD_01", “a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                                   &n:real = &m)”)
    ];

(* check prefer/deprecate real *)
val grammars = (type_grammar(),term_grammar())
val _ = realLib.prefer_real()
val _ = tprint "Checking parse of 0 < x gives reals when reals preferred"
val expected1 = realSyntax.mk_less(realSyntax.zero_tm,
                                   mk_var("x", realSyntax.real_ty))
val _ = require_msg (check_result (aconv expected1)) term_to_string
                    (quietly Parse.Term) ‘0 < x’
val _ = temp_set_grammars grammars

val _ = realLib.deprecate_real();
val _ = tprint "Checking parse of 0 < x gives nats when reals deprecated"
val expected2 = numSyntax.mk_less(numSyntax.zero_tm,
                                  mk_var("x", numSyntax.num))
val _ = require_msg (check_result (aconv expected2)) term_to_string
                    (quietly Parse.Term) ‘0 < x’
val _ = temp_set_grammars grammars

(* tests for bitArithLib *)
val _ = convtest("Testing karatsuba_conv on ``1 * 2``",
                  karatsuba_conv,
                 ``1 * (2:num)``,
                 ``2:num``)

val _ = convtest("Testing karatsuba_conv on ``64 * 128``",
                  karatsuba_conv,
                 ``64 * (128:num)``,
                 ``8192:num``)

val _ = convtest("Testing karatsuba_conv on ``1 * 2``",
                  real_mul_conv,
                 ``1 * (2:real)``,
                 ``2:real``)

val _ = convtest("Testing real_mul_conv on ``64 * 128``",
                  real_mul_conv,
                 ``64 * (128:real)``,
                 ``8192:real``)


val _ = Process.exit Process.success
