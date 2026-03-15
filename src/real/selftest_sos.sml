open HolKernel Parse boolLib bossLib;
open realSyntax realTheory RealArith RealField SOSLib;
open testutils;

val errc = ref 0
val _ = diemode := Remember errc

(* ================================================================ *)
(* Tests for SOSLib (SOS_CONV, PURE_SOS_TAC, PURE_SOS)             *)
(* ================================================================ *)

(* -- SOS_CONV: decompose polynomial as sum of squares -- *)

fun sos_conv_test (name, tm) =
  let
    fun check res = lhand (concl res) ~~ tm
  in
    tprint ("SOS_CONV " ^ name);
    require_msg (check_result check) (term_to_string o concl) SOS_CONV tm
  end;

val _ = List.app sos_conv_test [
  ("x^2",
   ``x * x:real``),
  ("x^2 + y^2",
   ``x * x + y * y:real``),
  ("(x+y)^2",
   ``x * x + &2 * x * y + y * y:real``),
  ("(x-y)^2",
   ``x * x - &2 * x * y + y * y:real``),
  ("x^2 + y^2 + 1",
   ``x * x + y * y + &1:real``),
  ("x^2 + 1",
   ``x * x + &1:real``),
  ("4*x^2 + 4*x*y + y^2",
   ``&4 * x * x + &4 * x * y + y * y:real``),
  ("x^2 + 4*y^2 + z^2 + 2*x*z",
   ``x * x + &4 * y * y + z * z + &2 * x * z:real``)
];

(* -- PURE_SOS: prove &0 <= polynomial -- *)

fun pure_sos_test (name, tm) =
  let
    fun check res = concl res ~~ tm
  in
    tprint ("PURE_SOS " ^ name);
    require_msg (check_result check) (term_to_string o concl) PURE_SOS tm
  end;

val _ = List.app pure_sos_test [
  ("0 <= x^2",
   ``&0 <= x * x:real``),
  ("0 <= x^2 + y^2",
   ``&0 <= x * x + y * y:real``),
  ("0 <= (x+y)^2",
   ``&0 <= x * x + &2 * x * y + y * y:real``),
  ("0 <= (x-y)^2",
   ``&0 <= x * x - &2 * x * y + y * y:real``),
  ("0 <= x^2 + y^2 + 1",
   ``&0 <= x * x + y * y + &1:real``),
  ("0 <= x^2 + y^2 + z^2",
   ``&0 <= x * x + y * y + z * z:real``)
];

(* -- PURE_SOS_TAC: close goals -- *)

fun tac_test (name, goal_tm) =
  let
    fun check res = concl res ~~ goal_tm
  in
    tprint ("PURE_SOS_TAC " ^ name);
    require_msg (check_result check) (term_to_string o concl)
                (fn t => prove(t, PURE_SOS_TAC)) goal_tm
  end;

val _ = List.app tac_test [
  ("0 <= x^2",
   ``&0 <= x * x:real``),
  ("0 <= x^2 + y^2",
   ``&0 <= x * x + y * y:real``),
  ("0 <= (x+y)^2",
   ``&0 <= x * x + &2 * x * y + y * y:real``)
];

(* -- Higher-degree tests (pure SOS, no CSDP needed) -- *)

val _ = List.app sos_conv_test [
  ("x^4 + y^4",
   ``(x:real) pow 4 + y pow 4``),
  ("x^4 + y^4 + z^4",
   ``(x:real) pow 4 + y pow 4 + z pow 4``),
  ("x^2*y^2",
   ``x * x * y * y:real``),
  ("(x^2 + y^2)^2 expanded",
   ``x * x * x * x + &2 * x * x * y * y + y * y * y * y:real``)
];

val _ = List.app pure_sos_test [
  ("0 <= x^4 + y^4",
   ``&0 <= (x:real) pow 4 + y pow 4``),
  ("0 <= x^2*y^2",
   ``&0 <= x * x * y * y:real``),
  ("0 <= x^4 + y^4 + 1",
   ``&0 <= (x:real) pow 4 + y pow 4 + &1``)
];

(* -- Tests requiring CSDP (non-obvious SOS decompositions) -- *)
(* These only run if CSDP is available *)

val csdp_available =
    OS.Process.isSuccess (OS.Process.system "which csdp > /dev/null 2>&1");

val _ = if csdp_available then
  List.app sos_conv_test [
    ("2*x^4+2*x^3*y-x^2*y^2+5*y^4 (CSDP)",
     ``&2 * (x:real) pow 4 + &2 * x pow 3 * y
       - x pow 2 * y pow 2 + &5 * y pow 4``),
    ("4*x^4+4*x^3*y-7*x^2*y^2-2*x*y^3+10*y^4 (CSDP)",
     ``&4 * (x:real) pow 4 + &4 * x pow 3 * y
       - &7 * x pow 2 * y pow 2 - &2 * x * y pow 3
       + &10 * y pow 4``),
    (* Schur inequality: x^6+y^6+z^6 - 3*x^2*y^2*z^2 *)
    ("x^6+y^6+z^6-3*x^2*y^2*z^2 (CSDP)",
     ``(x:real) pow 6 + y pow 6 + z pow 6
       - &3 * x pow 2 * y pow 2 * z pow 2``),
    (* x^4 + y^4 + z^4 + 1 - 4*x*y*z *)
    ("x^4+y^4+z^4+1-4xyz (CSDP)",
     ``(x:real) pow 4 + y pow 4 + z pow 4 + &1
       - &4 * x * y * z``)
  ]
else
  print "  [CSDP not available — skipping CSDP tests]\n";

val _ = if csdp_available then
  List.app pure_sos_test [
    ("0 <= 2*x^4+2*x^3*y-x^2*y^2+5*y^4 (CSDP)",
     ``&0 <= &2 * (x:real) pow 4 + &2 * x pow 3 * y
            - x pow 2 * y pow 2 + &5 * y pow 4``)
  ]
else ();

(* -- FAIL tests: should raise on non-SOS polynomials -- *)

val _ = shouldfail {
      testfn = SOS_CONV,
      printresult = thm_to_string,
      printarg = fn t => "SOS_CONV fails on " ^ term_to_string t ^
                         " (not a square)",
      checkexn = fn HOL_ERR _ => true | _ => false
    } ``x:real``;

(* -- REAL_SOS tests: universally quantified goals -- *)

fun real_sos_test (name, tm) =
  let
    fun check res = concl res ~~ tm
  in
    tprint ("REAL_SOS " ^ name);
    require_msg (check_result check) (term_to_string o concl) REAL_SOS tm
  end;

val _ = List.app real_sos_test [
  ("!x. 0 <= x^2",
   ``!x:real. &0 <= x * x``),
  ("!x y. 0 <= x^2 + y^2",
   ``!x y:real. &0 <= x * x + y * y``),
  ("!x y. 0 <= (x-y)^2",
   ``!x y:real. &0 <= x * x - &2 * x * y + y * y``),
  ("!x y. x^2 + y^2 >= 2*x*y (AM-GM)",
   ``!x y:real. x * x + y * y >= &2 * x * y``)
];

val _ = if csdp_available then
  List.app real_sos_test [
    ("!x y. 0 <= 2x^4+2x^3y-x^2y^2+5y^4 (CSDP)",
     ``!x y:real. &0 <= &2 * x pow 4 + &2 * x pow 3 * y
                        - x pow 2 * y pow 2 + &5 * y pow 4``)
  ]
else ();

(* -- REAL_SOS_TAC tests -- *)

fun sos_tac_test (name, goal_tm) =
  let
    fun check res = concl res ~~ goal_tm
  in
    tprint ("REAL_SOS_TAC " ^ name);
    require_msg (check_result check) (term_to_string o concl)
                (fn t => prove(t, REAL_SOS_TAC)) goal_tm
  end;

val _ = List.app sos_tac_test [
  ("!x. 0 <= x^2",
   ``!x:real. &0 <= x * x``),
  ("!x y. 0 <= x^2 + y^2",
   ``!x y:real. &0 <= x * x + y * y``),
  ("!x y. x^2 + y^2 >= 2*x*y (AM-GM, tac)",
   ``!x y:real. x * x + y * y >= &2 * x * y``)
];

(* -- REAL_SOS with hypotheses (Positivstellensatz, requires CSDP) -- *)

val _ = if csdp_available then
  List.app real_sos_test [
    ("x>=5 /\\ y>=5 ==> x*y>=25",
     ``!x y:real. x >= &5 /\ y >= &5 ==> x * y >= &25``),
    ("x>=1 ==> x*x>=x",
     ``!x:real. x >= &1 ==> x * x >= x``),
    ("x>=0 /\\ y>=0 ==> x*x+y*y>=0 (hyps)",
     ``!x y:real. x >= &0 /\ y >= &0 ==> x * x + y * y >= &0``)
  ]
else ();

val _ = if csdp_available then
  List.app real_sos_test [
    ("x>=0 /\\ y>=0 /\\ x+y<=1 ==> x*y<=1/4 (CSDP)",
     ``!x y:real. x >= &0 /\ y >= &0 /\ x + y <= &1
                  ==> x * y <= &1 / &4``),
    ("x+y=1 /\\ x>=0 /\\ y>=0 ==> x*y<=1/4 (subst, CSDP)",
     ``!x y:real. x + y = &1 /\ x >= &0 /\ y >= &0
                  ==> x * y <= &1 / &4``)
  ]
else ();

(* -- REAL_SOS_TAC with hypotheses (requires CSDP) -- *)

val _ = if csdp_available then
  List.app sos_tac_test [
    ("x>=5 /\\ y>=5 ==> x*y>=25 (tac)",
     ``!x y:real. x >= &5 /\ y >= &5 ==> x * y >= &25``)
  ]
else ();

(* -- REAL_SOS_ASM_TAC test (requires CSDP) -- *)

val _ = if csdp_available then
  let
    val goal = ``!x:real. x >= &1 ==> x * x >= x``
    fun check res = concl res ~~ goal
  in
    tprint "REAL_SOS_ASM_TAC with assumption";
    require_msg (check_result check) (term_to_string o concl)
                (fn t => prove(t, REAL_SOS_ASM_TAC)) goal
  end
else ();

(* -- REAL_SOS_DIRECT_TAC (requires CSDP) -- *)

val _ = if csdp_available then
  let
    val expected_concl = ``x * y >= &25:real``
    val expected_hyps = HOLset.fromList Term.compare
                          [``x >= &5:real``, ``y >= &5:real``]
    fun check res = concl res ~~ expected_concl andalso
                    HOLset.equal (hypset res, expected_hyps)
  in
    tprint "REAL_SOS_DIRECT_TAC x>=5, y>=5 |- x*y>=25";
    require_msg (check_result check) thm_to_string
      (fn () => prove(``x * y >= &25:real``,
                  MAP_EVERY ASSUME_TAC
                    [ASSUME ``x >= &5:real``, ASSUME ``y >= &5:real``] THEN
                  REAL_SOS_DIRECT_TAC)) ()
  end
else ();

(* ===================================================================== *)
(* A3: INT_SOS, NUM_SOS_RULE, REAL_SOSFIELD                             *)
(* ===================================================================== *)

fun prover_test prover_name prover (name, tm) =
  let
    fun check res = aconv tm (concl res)
  in
    tprint (prover_name ^ " " ^ name);
    require_msg (check_result check) (term_to_string o concl) prover tm
  end;

(* -- INT_SOS tests -- *)

val _ = List.app (prover_test "INT_SOS" INT_SOS) [
  ("!x:int. x*x >= 0",
   Parse.Term `!x:int. x * x >= &0`)
];

(* INT_SOS with hypotheses (requires CSDP) *)
val _ = if csdp_available then
  List.app (prover_test "INT_SOS" INT_SOS) [
    ("x>=5 /\\ y>=5 ==> x*y>=25",
     Parse.Term `!x y:int. x >= &5 /\ y >= &5 ==> x * y >= &25`),
    ("x>=1 ==> x*x>=x",
     Parse.Term `!x:int. x >= &1 ==> x * x >= x`)
  ]
else ();

(* -- NUM_SOS_RULE tests -- *)

val _ = List.app (prover_test "NUM_SOS_RULE" NUM_SOS_RULE) [
  ("num: x*x >= x*x",
   Parse.Term `!x:num. x * x >= x * x`)
];

(* NUM_SOS_RULE with hypotheses (requires CSDP) *)
val _ = if csdp_available then
  List.app (prover_test "NUM_SOS_RULE" NUM_SOS_RULE) [
    ("num: x>=5 /\\ y>=5 ==> x*y>=25",
     Parse.Term `!x y:num. x >= 5 /\ y >= 5 ==> x * y >= 25`)
  ]
else ();

(* -- REAL_SOSFIELD tests -- *)

val _ = List.app (prover_test "REAL_SOSFIELD" REAL_SOSFIELD) [
  ("x*x >= 0 (no div)",
   Parse.Term `!x:real. x * x >= &0`)
];

(* REAL_SOSFIELD with hypotheses (requires CSDP) *)
val _ = if csdp_available then
  List.app (prover_test "REAL_SOSFIELD" REAL_SOSFIELD) [
    ("x>0 ==> x + x/x >= x",
     Parse.Term `!x:real. x > &0 ==> x + x / x >= x`)
  ]
else ();

val _ = print "\n"
val _ = exit_count0 errc
