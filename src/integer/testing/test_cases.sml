structure test_cases :> test_cases =
struct

open Abbrev
open HolKernel Parse;

fun test_term c (n,t,b) = let
  val _ = print (StringCvt.padRight #" " 25 n)
  val _ = Profile.reset_all()
  val timer = Timer.startCPUTimer ()
  val result = SOME (SOME (c t))
    handle Interrupt => SOME NONE
         | _ => NONE
  val {usr,sys} = Timer.checkCPUTimer timer
  val gc = Timer.checkGCTime timer
  val (verdictmsg, verdict) =
    case result of
      SOME (SOME th) => let
      in
        case Lib.total boolSyntax.rhs (concl th) of
          SOME r =>
          if b andalso r = boolSyntax.T orelse
             not b andalso r = boolSyntax.F
          then
            ("OK", true)
          else ("Bad EQN", false)
        | NONE => ("Not an EQN", false)
      end
    | SOME NONE => ("Interrupted", false)
    | NONE => ("Raised exception", false)
  val _ = print (StringCvt.padRight #" " 17 verdictmsg)
  val pl = StringCvt.padLeft #" " 6
  val _ = print (pl (Time.toString usr)^" "^pl (Time.toString sys)^" "^
                 pl (Time.toString gc))
  val _ = print "\n"
in
  verdict
end

fun A s = ("at."^s, concl (DB.fetch "arithmetic" s), true)
fun I s = ("it."^s, concl (DB.fetch "integer" s), true)
fun L (t,s) = (s,t,true)
fun T (s,t) = (s,t,true)

val terms_to_test =
  [T ("INT_GROUP", Term`?!x:int. (!y. x + y = y) /\ (!y. ?!z. y + z = x)`),
   T ("Mike1",
        ``?(k:num) (j:num) (i:num).
            (i >= 0 /\ j >= 0 /\ k >= 0 /\ ~((i = 0) \/ (j = 0) \/ (k = 0)) /\
            ~(i = j) /\ ~(i = k) /\ (j = k)) /\ i < j + k``),
   T ("Mike2",
      ``?(k:num) (j:num) (i:num).
           (((((i >= 0 /\ j >= 0 /\ k >= 0) /\
           ~(((i = 0) \/ (j = 0)) \/ (k = 0))) /\ ~(i = j)) /\ ~(i = k)) /\
           (j = k)) /\ i < j + k``),
   T ("BUG1",
    ``(?x. y <= x /\ x <= z /\ 2i * z + 1 <= x /\ x <= 2 * y) =
    y <= z /\ 2 * z + 1 <= 2 * y /\ y <= 2 * y /\ 2 * z + 1 <= z``),
   T ("ILP1", Term`?z y x. 2n * x + 3 * y < 4 * z ==> 5 * x < 3 * y + z`),
   T ("ILP2",
      Term`?z y x v u. ~9 * u + ~12 * v + 4 * x + 5 * y + ~10 * z = 17`),
   ("aILP1",
    Term`!z y x v u.
            (3 * u + 6 * v + ~9 * x + ~5 * y + 6 * z = 86) ==>
            (1 * u + 4 * v + 17 * x + ~18 * y + ~5 * z = ~24)`, false),
   ("PUGH1", Term`?x y:int. 27 <= 11 * x + 13 * y /\ 11 * x + 13 * y <= 45 /\
                            ~10 <= 7 * x - 9 * y /\ 7 * x - 9 * y <= 4`,
    false),
   T ("3-5", Term`!n:num. 7 < n ==> ?i j. 3 * i + 5 * j = n`),
   T ("SUNRISE1", Term`!x0:num x:num y0:num y:num.
      (x0 = x) /\ (y0 = y) ==>
      (if 100 < y then
         (if 100 < y0 then y - 10 = y0 - 10 else y - 10 = 91)
       else
         101 - (y + 11) < 101 - y0 /\
         !x.
           (if 100 < y + 11 then x = y + 11 - 10 else x = 91) ==>
           101 - x < 101 - y0 /\
           !x1.
             (if 100 < x then x1 = x - 10 else x1 = 91) ==>
             (if 100 < y0 then x1 = y0 - 10 else x1 = 91))`),
   ("DIV1", Term`!x. 0 <= x = x / 2 <= x`, false),
   ("DIV2", Term`!x. (x / 2 = x) = (x = 0)`, false),
   T ("DIV3", Term`!i. (i % 10) % 10 = i % 10`),
   T ("DIV4", Term`?!i. 2 < i /\ (i / 2 = 1)`),
   T ("NDIV1", Term`!x. 0 < x ==> x DIV 2 < x`),
   T ("NDIV2", Term`(x MOD 2) MOD 2 = x MOD 2`),
   T ("NDIV3", Term`?!n. 2 < n /\ (n DIV 2 = 1)`),
   T ("KXSDIV1", Term`!n. ~(n = 0) /\ EVEN n ==> (n - 2) DIV 2 < n`),
   T ("KXSDIV2", Term`!n. ~(n = 0) /\ ~EVEN n ==> (n - 1) DIV 2 < n`),
   T ("simp_divides1", ``!x. 0 < x /\ 2 int_divides x ==> 1 < x``),
   T ("simp_divides2", ``!x. 0 <= x /\ ~(2 int_divides x) ==> 1 <= x``),
   T ("sub_zero_coeff", Term`!x y:int. 0 < x ==> y - x < y`),
   T ("10000.9391",
    Term`~(v <
        SUC
          (SUC z + (SUC (SUC (SUC (SUC v)) + (v + (SUC u + v))) + u + y) +
           v)) ==>
      SUC 0 < 0 + (v + x) + SUC (v + v) /\
      (z + z >= 0 + v \/ (z + v = 0) /\ u <= u)`),
   T ("10000.2223",
    Term`SUC 0 < (u :num) +
           (0 +
            SUC
              (SUC
                 ((z :num) +
                  (SUC (0 + u) + SUC (v :num) + SUC u + u +
                   (0 + SUC (SUC z + (x :num)) + 0) + 0))) +
            SUC (z + u)) + x + ((y :num) + z + u) + 0`),
   T ("EX1_NOT_COMM", ``~((?!x y. (x = y) \/ (x = SUC y)) =
                         (?!y x. (x = y) \/ (x = SUC y)))``),
   T ("NUM1", Term`!n:num m. n + m > 10 ==> n + 2 * m > 10`),
   T ("ABS1", Term `!p. 0 <= ABS(p)`),
   T ("ABS2", Term `!p. ABS (ABS(p)) = ABS(p)`),
   T ("ABS3", Term `!p. (ABS(p) = 0) = (p = 0)`),
   T ("ABS4", Term `!p. (ABS(p) = p) = 0 <= p`),
   T ("ABS5", Term `!p. ABS ~p = ABS p`),
   T ("ABS6", Term `!p. ABS(p) <= 0 = (p = 0)`),
   T ("ABS7", Term `!p. ~(ABS(p) < 0)`),
   T ("ABS8", Term `!p q.
           (ABS(p) < q = p < q /\ ~q < p) /\
           (q < ABS(p) = q < p \/ p < ~q) /\
      (~1*ABS(p) < q = ~q < p \/ p < q) /\
      (q < ~1*ABS(p) = p < ~q /\ q < p)`),
   T ("ABS9", Term `!p q.
            (ABS(p) <= q = p <= q /\ ~q <= p) /\
            (q <= ABS(p) = q <= p \/ p <= ~q) /\
         (~1*ABS(p) <= q = ~q <= p \/ p <= q) /\
         (q <= ~1*ABS(p) = p <= ~q /\ q <= p)`),
   T ("ABS10", Term `!p q.
           ((ABS(p) = q) = (p = q) /\ 0 < q \/ (p = ~q) /\ 0 <= q) /\
           ((q = ABS(p)) = (p = q) /\ 0 < q \/ (p = ~q) /\ 0 <= q)`),
   A "ADD",
   A "EVEN",
   A "EQ_ADD_LCANCEL",
   I "INT_DOUBLE",
   I "INT_EQ_NEG",
   I "INT_ADD_RID_UNIQ",
   T ("BIGINT1", Term`!x. 100i * x > 213 ==> 100 * x > 251`),
   T ("BIGINT2", Term`!x. ~213 < 100i * x ==> ~251 < 100 * x`),
   T ("MIKE.NUM", Term`!q r:num. (7 = r + q * 3) /\ r < 3 ==> (r = 1)`),
   T ("INT_MULT_NORM", Term`(2 * m = r + k' * (2 * p)) ==> ?s. r = 2i * s`),
   T ("NUM_MULT_NORM", Term`(2 * m = r + k' * (2 * p)) ==> ?s. r = 2n * s`),
   A "ZERO_LESS_EQ", A "TWO", A "TIMES2", A "SUC_SUB1", A "SUC_ONE_ADD",
   A "SUC_NOT", A "SUC_ADD_SYM", A "SUB_SUB", A "SUB_RIGHT_SUB",
   A "SUB_RIGHT_LESS_EQ", A "SUB_RIGHT_LESS", A "SUB_RIGHT_GREATER_EQ",
   A "SUB_RIGHT_GREATER", A "SUB_RIGHT_EQ", A "SUB_RIGHT_ADD", A "SUB_PLUS",
   A "SUB_MONO_EQ", A "SUB_LESS_OR", A "SUB_LESS_EQ_ADD", A "SUB_LESS_EQ",
   A "SUB_LESS_0", A "SUB_LEFT_SUC", A "SUB_LEFT_SUB",
   A "SUB_LEFT_LESS_EQ", A "SUB_LEFT_LESS", A "SUB_LEFT_GREATER_EQ",
   A "SUB_LEFT_GREATER", A "SUB_LEFT_EQ", A "SUB_LEFT_ADD",
   A "SUB_EQUAL_0", A "SUB_EQ_EQ_0", A "SUB_EQ_0",
   A "SUB_CANCEL",

   A "SUB_ADD", A "SUB_0", A "SUB",
   A "PRE_SUC_EQ", A "PRE_SUB1", A "PRE_SUB",
   A "OR_LESS", A "ONE", A "ODD_OR_EVEN",
   A "ODD_EXISTS", A "ODD_EVEN", A "ODD_DOUBLE", A "ODD_ADD", A "ODD",
   A "num_CASES",
   A "NOT_ZERO_LT_ZERO", A "NOT_SUC_LESS_EQ_0", A "NOT_SUC_LESS_EQ",
   A "NOT_SUC_ADD_LESS_EQ", A "NOT_ODD_EQ_EVEN", A "NOT_NUM_EQ",
   A "NOT_LESS_EQUAL", A "NOT_LESS", A "NOT_LEQ", A "NOT_GREATER_EQ",
   A "NOT_GREATER", A "MULT_RIGHT_1", A "MULT_LEFT_1", A "MULT_0",

   A "LESS_TRANS",
   A "LESS_SUC_NOT",
   A "LESS_SUC_EQ_COR",
   A "LESS_SUB_ADD_LESS",
   A "LESS_OR_EQ_ADD",
   A "LESS_OR_EQ",
   A "LESS_OR",
   A "LESS_NOT_SUC",
   A "LESS_MONO_REV",
   A "LESS_MONO_EQ",
   A "LESS_MONO_ADD_INV",
   A "LESS_MONO_ADD_EQ",
   A "LESS_MONO_ADD",
   A "LESS_LESS_SUC",
   A "LESS_LESS_EQ_TRANS",
   A "LESS_LESS_CASES",
   A "LESS_IMP_LESS_OR_EQ",
   A "LESS_IMP_LESS_ADD",
   A "LESS_EQUAL_ANTISYM",
   A "LESS_EQUAL_ADD",
   A "LESS_EQ_TRANS",
   A "LESS_EQ_SUC_REFL",
   A "LESS_EQ_SUB_LESS",
   A "LESS_EQ_REFL",
   A "LESS_EQ_MONO_ADD_EQ",
   A "LESS_EQ_MONO",
   A "LESS_EQ_LESS_TRANS",
   A "LESS_EQ_LESS_EQ_MONO",
   A "LESS_EQ_IMP_LESS_SUC",
   A "LESS_EQ_EXISTS",
   A "LESS_EQ_CASES",
   A "LESS_EQ_ANTISYM",
   A "LESS_EQ_ADD_SUB",
   A "LESS_EQ_ADD",
   A "LESS_EQ_0",
   A "LESS_EQ",
   A "LESS_CASES_IMP",
   A "LESS_CASES",
   A "LESS_ANTISYM",
   A "LESS_ADD_SUC",
   A "LESS_ADD_NONZERO",
   A "LESS_ADD_1",
   A "LESS_ADD",
   A "LESS_0_CASES",
   A "LE",
   A "INV_PRE_LESS_EQ",
   A "INV_PRE_LESS",
   A "INV_PRE_EQ",
  L (Term`!x:int y z. x < y /\ y < z ==> x < z`, "pt1"),
  L (Term`?x y:int. 4 * x + 3 * y = 10`, "pt2"),
  L (Term`!x. 3i * x < 4 * x ==> x > 0`, "pt3"),
  L (Term`?y. !x:int. x + y = x`, "pt4"),
  L (Term`?y. (!x:int. x + y = x) /\
              !y'. (!x. x + y' = x) ==> (y = y')`, "pt5"),
  L (Term`!x. 3 int_divides x /\ 2 int_divides x ==> 6 int_divides x`, "pt6"),
  L (Term`?!y:int. !x. x + y = x`, "pt7"),
  L (Term`!x. ?!y. x + y = 0i`, "pt8"),
  L (Term`?x y. (x + y = 6i) /\ (2 * x + 3 * y = 11)`, "pt9"),
  L (Term`!x z:int. ?!y. x - y = z`, "pt10"),
  L (Term`!x y z:int. 2 * x < y /\ y < 2 * z ==>
                 ?w. ((y = 2 * w) \/ (y = 2 * w + 1)) /\
                     x <= w /\ w < z`, "pt11"),
  L (Term`(0 :num) < SUC (u' :num) ==> (0 :num) < (m :num) ==>
          (0 :num) < (n :num) ==> ~(m = (0 :num)) ==>
          n + (u' * m + m) < m ==> u' * m + m <= n ==> F`, "NONPB1"),
  L (Term`((n :num) = (r :num) + (i :num) * (m :num)) ==>
          r < m ==> (n MOD m = r) ==> (n DIV m = i) ==>
          ~(m = (0 :num))`, "NONPB2"),
  L (Term`(e*bv_c+e*(2*bv_cout+wb_sum)+wbs_sum =
             bv_cin+e*(bv_c+wb_a+wb_b)+wbs_a+wbs_b)
          ==>
           (2n*e*bv_cout+e*wb_sum+wbs_sum = bv_cin+e*wb_a+e*wb_b+wbs_a+wbs_b)`,
     "AG_NAT"),
  L (Term`(e*bv_c+e*(2*bv_cout+wb_sum)+wbs_sum =
             bv_cin+e*(bv_c+wb_a+wb_b)+wbs_a+wbs_b)
          ==>
           (2i*e*bv_cout+e*wb_sum+wbs_sum = bv_cin+e*wb_a+e*wb_b+wbs_a+wbs_b)`,
     "AG_INT"),
  L (Term`x * y < y * x + 1i`, "IMUL_NORM"),
  L (Term`x * y < y * x + 1n`, "NMUL_NORM"),
  L (``Num i < SUC (Num i)``, "Num1"),
  L (``0 < i ==> (ODD (Num i) = ?j. i = 2 * j + 1)``, "Num2"),
  L (``0i < & (Num (ABS a1 - 1)) + 1``, "Num3"),
  L (``0i < &(Num (f (x:'a) - 1)) + 1``, "Num4a"),
  L (``0i < (if 0 <= f (x:'a) - 1i then f x - 1 else &(g (f x - 1))) + 1``,
     "Num4b")
];

val omega_test_terms = [
  L (``(x MOD 1001 + y MOD 1001) MOD 1001 = (x + y) MOD 1001``, "MOD_ADD1001"),
  L (``((n DIV 100000) MOD 2 = 0) ==> n MOD 200000 < 100000``, "DIV_LT100000"),
  L (``i < (nb - 1) % 256 /\ 0 <= nb /\ nb < 256 /\ 0 <= i /\ i < 256 ==>
       i < (i + 1) % 256``, "MATTHEWS_I256"),
  L (``i < (nb - 1) MOD 256 /\ 0 <= nb /\ nb < 256 /\ 0 <= i /\ i < 256 ==>
       i < (i + 1) MOD 256``, "MATTHEWS_N256"),
  L (``i < (nb - 1) % 2147483648 /\ 0 <= nb /\ nb < 2147483648 /\ 0 <= i /\
       i < 2147483648 ==> i < (i + 1) % 2147483648``, "MATTHEWS_I2^31"),
  L (``i < (nb - 1) MOD 2147483648 /\ 0 <= nb /\ nb < 2147483648 /\ 0 <= i /\
       i < 2147483648 ==> i < (i + 1) MOD 2147483648``, "MATTHEWS_N2^31"),
  L (``0 <= i /\ i <= 100 ==> (Num i + 11 = (Num i + 11) MOD 429467296)``,
     "MATTHEWS_Num"),
  L (``0 <= i /\ i <= 100 ==> (Num (i + 11) = (Num i + 11) MOD 429467296)``,
     "MATTHEWS_Num'")
]

val cooper_test_terms = [
(*  L (``?s:int e n d m oh r y.
        0 < s /\ s <= 9 /\ 0 <= e /\ e <= 9 /\ 0 <= n /\ n <= 9 /\
        0 <= d /\ d <= 9 /\ 0 < m /\ m <= 9 /\ 0 <= oh /\ oh <= 9 /\
        0 <= r /\ r <= 9 /\ 0 <= y /\ y <= 9 /\ ~(s = e) /\ ~(s = n) /\
        ~(s = d) /\ ~(s = m) /\ ~(s = oh) /\ ~(s = r) /\ ~(s = y) /\
        ~(e = n) /\ ~(e = d) /\ ~(e = m) /\ ~(e = oh) /\ ~(e = r) /\
        ~(e = y) /\ ~(n = d) /\ ~(n = m) /\ ~(n = oh) /\ ~(n = r) /\
        ~(n = y) /\ ~(d = m) /\ ~(d = oh) /\ ~(d = r) /\ ~(d = y) /\
        ~(m = oh) /\ ~(m = r) /\ ~(m = y) /\ ~(oh = r) /\ ~(oh = y) /\
        ~(r = y) /\
        (1000 * s + 100 * e + 10 * n + d + 1000 * m + 100 * oh + 10 * r +
         e =
         10000 * m + 1000 * oh + 100 * n + 10 * e + y)``,
     "SEND_MORE_MONEY") *)
]

val goals_to_test = [
  ("van Leeuwen",
   ([``0i <= i``, ``i :int < maxchar``,
     ``!n. 0i <= n /\ n < i ==> (skips ArrayApp n = 0i)``],
    ``maxchar - i > 0i``)),
  ("natural number 1", ([``n:num > 4``], ``n:num > 3``)),
  ("natural number 2",
   ([``n:num < p + 1``, ``!m:num. m < p ==> ~(n < m + 1)``], ``p:num = n``))
]

fun test_goal tac (name, g) = let
  val _ = print (StringCvt.padRight #" " 25 name)
  val result = SOME (SOME (tac g)) handle Interrupt => SOME NONE
                                        | _ => NONE
  val (verdictmsg, verdict) =
      case result of
        SOME (SOME (subgoals, _)) => if null subgoals then ("OK", true)
                                     else ("Subgoals remain", false)
      | SOME NONE => ("Interrupted", false)
      | NONE => ("Raised exception", false)
  val _ = print (verdictmsg ^  "\n")
in
  verdict
end


fun perform_tests conv tactic =
    (print "Testing terms\n";
     List.all (test_term conv) terms_to_test) andalso
    (print "Testing goals\n";
     List.all (test_goal tactic) goals_to_test)

fun perform_omega_tests conv =
    (print "Testing Omega terms\n";
     List.all (test_term conv) omega_test_terms)

fun perform_cooper_tests conv =
    (print "Testing Cooper terms\n";
     List.all (test_term conv) cooper_test_terms)

end; (* struct *)
