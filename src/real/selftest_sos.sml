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
      val _ = tprint ("SOS_CONV " ^ name)
      val th = SOS_CONV tm
      val lhs_tm = lhand (concl th)
      val rhs_tm = rand (concl th)
    in
      if lhs_tm ~~ tm then OK()
      else die ("LHS mismatch: " ^ term_to_string lhs_tm)
    end
    handle e => die ("EXCEPTION: " ^ General.exnMessage e);

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
      val _ = tprint ("PURE_SOS " ^ name)
      val th = PURE_SOS tm
    in
      if concl th ~~ tm then OK()
      else die ("conclusion mismatch: " ^ thm_to_string th)
    end
    handle e => die ("EXCEPTION: " ^ General.exnMessage e);

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
      val _ = tprint ("PURE_SOS_TAC " ^ name)
      val th = prove(goal_tm, PURE_SOS_TAC)
    in
      if concl th ~~ goal_tm then OK()
      else die ("conclusion mismatch")
    end
    handle e => die ("EXCEPTION: " ^ General.exnMessage e);

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

val _ = let
  val _ = tprint "SOS_CONV fails on x (not a square)"
in
  (SOS_CONV ``x:real``; die "should have failed")
  handle HOL_ERR _ => OK()
end;

(* -- REAL_SOS tests: universally quantified goals -- *)

fun real_sos_test (name, tm) =
    let
      val _ = tprint ("REAL_SOS " ^ name)
      val th = REAL_SOS tm
    in
      if concl th ~~ tm then OK()
      else die ("conclusion mismatch: " ^ thm_to_string th)
    end
    handle e => die ("EXCEPTION: " ^ General.exnMessage e);

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
      val _ = tprint ("REAL_SOS_TAC " ^ name)
      val th = prove(goal_tm, REAL_SOS_TAC)
    in
      if concl th ~~ goal_tm then OK()
      else die ("conclusion mismatch")
    end
    handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = List.app sos_tac_test [
  ("!x. 0 <= x^2",
   ``!x:real. &0 <= x * x``),
  ("!x y. 0 <= x^2 + y^2",
   ``!x y:real. &0 <= x * x + y * y``),
  ("!x y. x^2 + y^2 >= 2*x*y (AM-GM, tac)",
   ``!x y:real. x * x + y * y >= &2 * x * y``)
];

(* -- REAL_SOS with hypotheses (Positivstellensatz) -- *)

val _ = List.app real_sos_test [
  ("x>=5 /\\ y>=5 ==> x*y>=25",
   ``!x y:real. x >= &5 /\ y >= &5 ==> x * y >= &25``),
  ("x>=1 ==> x*x>=x",
   ``!x:real. x >= &1 ==> x * x >= x``),
  ("x>=0 /\\ y>=0 ==> x*x+y*y>=0 (hyps)",
   ``!x y:real. x >= &0 /\ y >= &0 ==> x * x + y * y >= &0``)
];

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

(* -- REAL_SOS_TAC with hypotheses -- *)

val _ = List.app sos_tac_test [
  ("x>=5 /\\ y>=5 ==> x*y>=25 (tac)",
   ``!x y:real. x >= &5 /\ y >= &5 ==> x * y >= &25``)
];

(* -- REAL_SOS_ASM_TAC test -- *)

val _ = let
  val _ = tprint "REAL_SOS_ASM_TAC with assumption"
  val th = prove(
    ``!x:real. x >= &1 ==> x * x >= x``,
    REAL_SOS_ASM_TAC)
in
  if concl th ~~ ``!x:real. x >= &1 ==> x * x >= x`` then OK()
  else die "conclusion mismatch"
end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

(* ===================================================================== *)
(* A3: INT_SOS, SOS_RULE, REAL_SOSFIELD                                 *)
(* ===================================================================== *)

(* -- INT_SOS tests -- *)

val _ = let
  val _ = tprint "INT_SOS !x:int. x*x >= 0"
  val th = INT_SOS (Parse.Term `!x:int. x * x >= &0`)
in
  if concl th ~~ Parse.Term `!x:int. x * x >= &0` then OK()
  else die "conclusion mismatch"
end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = let
  val _ = tprint "INT_SOS x>=5 /\\ y>=5 ==> x*y>=25"
  val th = INT_SOS (Parse.Term `!x y:int. x >= &5 /\ y >= &5 ==> x * y >= &25`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = let
  val _ = tprint "INT_SOS x>=1 ==> x*x>=x"
  val th = INT_SOS (Parse.Term `!x:int. x >= &1 ==> x * x >= x`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

(* -- SOS_RULE tests -- *)

val _ = let
  val _ = tprint "SOS_RULE num: x>=5 /\\ y>=5 ==> x*y>=25"
  val th = SOS_RULE (Parse.Term `!x y:num. x >= 5 /\ y >= 5 ==> x * y >= 25`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = let
  val _ = tprint "SOS_RULE num: x*x >= x*x"
  val th = SOS_RULE (Parse.Term `!x:num. x * x >= x * x`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

(* -- REAL_SOSFIELD tests -- *)

val _ = let
  val _ = tprint "REAL_SOSFIELD x>0 ==> x + x/x >= x"
  val th = REAL_SOSFIELD (Parse.Term `!x:real. x > &0 ==> x + x / x >= x`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = let
  val _ = tprint "REAL_SOSFIELD x*x >= 0 (no div)"
  val th = REAL_SOSFIELD (Parse.Term `!x:real. x * x >= &0`)
in OK() end
handle e => die ("EXCEPTION: " ^ General.exnMessage e);

val _ = print "\n"
val _ = exit_count0 errc
