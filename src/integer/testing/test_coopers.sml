open HolKernel Parse;

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

open Cooper;

fun test_term (n,t) = let
  val _ = print (StringCvt.padRight #" " 25 n)
  val timer = Timer.startCPUTimer ()
  val result = SOME (SOME (COOPER_CONV t))
    handle Interrupt => SOME NONE
         | _ => NONE
  val {usr,sys,gc} = Timer.checkCPUTimer timer
  val verdict =
    case result of
      SOME (SOME _) => "OK"
    | SOME NONE => "Interrupted"
    | NONE => "Raised exception"
  val _ = print (StringCvt.padRight #" " 17 verdict)
  val pl = StringCvt.padLeft #" " 6
  val _ = print (pl (Time.toString usr)^" "^pl (Time.toString sys)^" "^
                 pl (Time.toString gc)^"\n")
in
  ()
end

fun A s = ("at."^s, concl (DB.theorem "arithmetic" s))
fun L (t,s) = (s,t)

val terms_to_test =
  [("INT_GROUP", Term`?!x:int. (!y. x + y = y) /\ (!y. ?!z. y + z = x)`),
   ("ILP1", Term`?z y x. 2n * x + 3 * y < 4 * z ==> 5 * x < 3 * y + z`),
   ("ILP2", Term`?z y x v u. ~9 * u + ~12 * v + 4 * x + 5 * y + ~10 * z = 17`),
   ("aILP1",
    Term`!z y x v u.
            (3 * u + 6 * v + ~9 * x + ~5 * y + 6 * z = 86) ==>
            (1 * u + 4 * v + 17 * x + ~18 * y + ~5 * z = ~24)`),
   ("PUGH1", Term`?x y:int. 27 <= 11 * x + 13 * y /\ 11 * x + 13 * y <= 45 /\
                            ~10 <= 7 * x - 9 * y /\ 7 * x - 9 * y <= 4`),
   ("SUNRISE1", Term`!x0:num x:num y0:num y:num.
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
   ("DIV1", Term`!x. 0 <= x = x / 2 <= x`),
   ("DIV2", Term`!x. (x / 2 = x) = (x = 0)`),
   ("10000.9391",
    Term`~(v <
        SUC
          (SUC z + (SUC (SUC (SUC (SUC v)) + (v + (SUC u + v))) + u + y) +
           v)) ==>
      SUC 0 < 0 + (v + x) + SUC (v + v) /\
      (z + z >= 0 + v \/ (z + v = 0) /\ u <= u)`),
   ("10000.2223",
    Term`SUC 0 < (u :num) +
           (0 +
            SUC
              (SUC
                 ((z :num) +
                  (SUC (0 + u) + SUC (v :num) + SUC u + u +
                   (0 + SUC (SUC z + (x :num)) + 0) + 0))) +
            SUC (z + u)) + x + ((y :num) + z + u) + 0`),
   ("NUM1", Term`!n:num m. n + m > 10 ==> n + 2 * m > 10`),
   ("at.ADD", concl arithmeticTheory.ADD),
   ("at.EVEN", concl arithmeticTheory.EVEN),
   ("at.EQ_ADD_LCANCEL", concl arithmeticTheory.EQ_ADD_LCANCEL),
   ("it.INT_DOUBLE", concl integerTheory.INT_DOUBLE),
   ("it.INT_EQ_NEG", concl integerTheory.INT_EQ_NEG),
   ("it.INT_ADD_RID_UNIQ", concl integerTheory.INT_ADD_RID_UNIQ),
   ("BIGINT1", Term`!x. 100i * x > 213 ==> 100 * x > 251`),
   ("BIGINT2", Term`!x. ~213 < 100i * x ==> ~251 < 100 * x`),
   ("MIKE.NUM", Term`!q r:num. (7 = r + q * 3) /\ r < 3 ==> (r = 1)`),
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
                     x <= w /\ w < z`, "pt11")
];

fun print_profile_results (nm, {usr, sys, gc}) = let
  val pl = StringCvt.padLeft #" " 8
  val _ = print (StringCvt.padRight #" " 25 nm)
  val _ = print (pl (Time.toString usr)^" "^pl (Time.toString sys)^" "^
                 pl (Time.toString gc)^"\n")
in
  ()
end

val _ = (map test_term terms_to_test;
         case CommandLine.arguments() of
           [] => ()
         | _ => app print_profile_results (Profile.results()))

