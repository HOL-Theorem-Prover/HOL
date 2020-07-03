(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Unit tests for HolSmtLib *)

val _ = print "Testing HolSmtLib\n"

(*****************************************************************************)
(* tracing/pretty-printing options useful for debugging                      *)
(*****************************************************************************)

(*
val _ = Globals.show_tags := true
val _ = Globals.show_assums := true
val _ = Globals.show_types := true
val _ = wordsLib.add_word_cast_printer ()
*)

val _ = Feedback.set_trace "HolSmtLib" 0
(*
val _ = Feedback.set_trace "HolSmtLib" 4
*)

(*****************************************************************************)
(* check whether SMT solvers are installed                                   *)
(*****************************************************************************)

val _ = if Yices.is_configured () then () else
  print "(Yices not configured, some tests will be skipped.)\n"

val _ = if Z3.is_configured () then () else
  print "(Z3 not configured, some tests will be skipped.)\n"

(*****************************************************************************)
(* utility functions                                                         *)
(*****************************************************************************)

local

fun die s =
  if !Globals.interactive then
    raise (Fail s)
  else (
    print ("\n" ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

(* provable terms: theorem expected *)
fun expect_thm name smt_tac t =
  let
    open boolLib
    val thm = Tactical.TAC_PROOF (([], t), smt_tac)
      handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
        die ("Test of solver '" ^ name ^ "' failed on term '" ^
          Hol_pp.term_to_string t ^ "': exception HOL_ERR (in " ^
          origin_structure ^ "." ^ origin_function ^ ", message: " ^ message ^
          ")")
  in
    if null (Thm.hyp thm) andalso Thm.concl thm ~~ t then ()
    else
      die ("Test of solver '" ^ name ^ "' failed on term '" ^
        Hol_pp.term_to_string t ^ "': theorem differs (" ^
        Hol_pp.thm_to_string thm ^ ")")
  end

(* unprovable terms: satisfiability expected *)
fun expect_sat name smt_tac t =
  let
    val _ = Tactical.TAC_PROOF (([], t), smt_tac)
  in
    die ("Test of solver '" ^ name ^ "' failed on term '" ^
      Hol_pp.term_to_string t ^ "': exception expected")
  end handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
    if origin_structure = "HolSmtLib" andalso
       origin_function = "GENERIC_SMT_TAC" andalso
       (message = "solver reports negated term to be 'satisfiable'" orelse
        message = "solver reports negated term to be 'satisfiable' (model returned)")
    then
      ()
    else
      die ("Test of solver '" ^ name ^ "' failed on term '" ^
        Hol_pp.term_to_string t ^
        "': exception HOL_ERR has unexpected argument values (in " ^
        origin_structure ^ "." ^ origin_function ^ ", message: " ^ message ^
        ")")

fun mk_test_fun is_configured expect_fun name smt_tac =
  if is_configured then
    (fn g => (expect_fun name smt_tac g; print "."))
  else
    Lib.K ()

(*****************************************************************************)
(* a built-in automated semi-decision procedure that *very* loosely          *)
(* resembles SMT solvers (in terms of coverage; not so much in terms of      *)
(* performance)                                                              *)
(*****************************************************************************)

fun auto_tac (_, t) =
  let
    val simpset = bossLib.++ (bossLib.srw_ss (), wordsLib.WORD_ss)
    val t_eq_t' = simpLib.SIMP_CONV simpset [integerTheory.INT_ABS,
      integerTheory.INT_MAX, integerTheory.INT_MIN]
      t
      handle Conv.UNCHANGED =>
        Thm.REFL t
    val t' = boolSyntax.rhs (Thm.concl t_eq_t')
    val t'_thm = bossLib.DECIDE t'
      handle Feedback.HOL_ERR _ =>
        bossLib.METIS_PROVE [] t'
      handle Feedback.HOL_ERR _ =>
        intLib.ARITH_PROVE t'
      handle Feedback.HOL_ERR _ =>
        realLib.REAL_ARITH t'
      handle Feedback.HOL_ERR _ =>
        wordsLib.WORD_DECIDE t'
      handle Feedback.HOL_ERR _ =>
        Tactical.prove (t', blastLib.BBLAST_TAC)
    val thm = Thm.EQ_MP (Thm.SYM t_eq_t') t'_thm
  in
    ([], fn _ => thm)
  end

val thm_AUTO =
  mk_test_fun true expect_thm "AUTO" (Tactical.THEN (Library.SET_SIMP_TAC, auto_tac))

fun mk_Yices expect_fun =
  mk_test_fun (Yices.is_configured ()) expect_fun "Yices" HolSmtLib.YICES_TAC

val thm_YO = mk_Yices expect_thm
val sat_YO = mk_Yices expect_sat

fun mk_Z3 expect_fun =
  mk_test_fun (Z3.is_configured ()) expect_fun "Z3" HolSmtLib.Z3_ORACLE_TAC

val thm_Z3 = mk_Z3 expect_thm
val sat_Z3 = mk_Z3 expect_sat

fun mk_Z3p expect_fun =
  mk_test_fun (Z3.is_configured ()) expect_fun "Z3 (proofs)" HolSmtLib.Z3_TAC

val thm_Z3p = mk_Z3p expect_thm
val sat_Z3p = mk_Z3p expect_sat

(*****************************************************************************)
(* HOL definitions (e.g., user-defined data types)                           *)
(*****************************************************************************)

val _ = bossLib.Hol_datatype `dt1 = foo | bar | baz`

val _ = bossLib.Hol_datatype `person = <| employed :bool; age :num |>`

in

(*****************************************************************************)
(* test cases                                                                *)
(*****************************************************************************)

  val tests = [

    (* propositional logic *)
    (``T``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``F``, [sat_YO, sat_Z3, sat_Z3p]),
    (``p = (p:bool)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``p ==> p``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``p \/ ~ p``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``p /\ q ==> q /\ p``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(p ==> q) /\ (q ==> p) ==> (p = q)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(p ==> q) /\ (q ==> p) <=> (p = q)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``p \/ q ==> p /\ q``, [sat_YO, sat_Z3, sat_Z3p]),
    (``if p then (q ==> p) else (p ==> q)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``case p of T => p | F => ~ p``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``case p of T => (q ==> p) | F => (p ==> q)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* numerals *)

    (* FIXME: SMT-LIB 2 does not provide a theory of natural numbers, but only
              integers and reals.  We should add support for naturals (via an
              embedding into integers), but for now, they are treated as
              uninterpreted. *)

    (* num *)

    (``0n = 0n``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``1n = 1n``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0n = 1n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``42n = 42n``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* int *)

    (``0i = 0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``1i = 1i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0i = 1i``, [sat_YO, sat_Z3, sat_Z3p]),
    (``42i = 42i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0i = ~0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~0i = 0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~0i = ~0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~42i = ~42i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* real *)

    (* Z3 2.19 prints reals as integers in its proofs; I see no way to
       reliably distinguish between them. *)

    (``0r = 0r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``1r = 1r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0r = 1r``, [sat_YO, sat_Z3, sat_Z3p]),
    (``42r = 42r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0r = ~0r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~0r = 0r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~0r = ~0r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~42r = ~42r``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~42r = 42r``, [sat_YO, sat_Z3, sat_Z3p]),
    (``42r = ~42r``, [sat_YO, sat_Z3, sat_Z3p]),

    (* arithmetic operators: SUC, +, -, *, /, DIV, MOD, ABS, MIN, MAX *)

    (* num *)

    (``SUC 0 = 1``, [thm_AUTO, thm_YO]),
    (``SUC x = x + 1``, [thm_AUTO, thm_YO]),
    (``x < SUC x``, [thm_AUTO, thm_YO]),
    (``(SUC x = SUC y) = (x = y)``, [thm_AUTO, thm_YO]),
    (``SUC (x + y) = (SUC x + SUC y)``, [sat_YO, sat_Z3, sat_Z3p]),

    (``(x:num) + 0 = x``, [thm_AUTO, thm_YO]),
    (``0 + (x:num) = x``, [thm_AUTO, thm_YO]),
    (``(x:num) + y = y + x``, [thm_AUTO, thm_YO]),
    (``(x:num) + (y + z) = (x + y) + z``, [thm_AUTO, thm_YO]),
    (``((x:num) + y = 0) <=> (x = 0) /\ (y = 0)``, [thm_AUTO, thm_YO]),

    (``(x:num) - 0 = x``, [thm_AUTO, thm_YO]),
    (``(x:num) - y = y - x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) - y - z = x - (y + z)``, [thm_AUTO, thm_YO]),
    (``(x:num) <= y ==> (x - y = 0)``, [thm_AUTO, thm_YO]),
    (``((x:num) - y = 0) \/ (y - x = 0)``, [thm_AUTO, thm_YO]),

    (``(x:num) * 0 = 0``, [thm_AUTO, thm_YO]),
    (``0 * (x:num) = 0``, [thm_AUTO, thm_YO]),
    (``(x:num) * 1 = x``, [thm_AUTO, thm_YO]),
    (``1 * (x:num) = x``, [thm_AUTO, thm_YO]),
    (``(x:num) * 42 = 42 * x``, [thm_AUTO, thm_YO]),

    (``(0:num) DIV 1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:num) DIV 1 = 1``, [thm_AUTO, thm_YO]),
    (``(42:num) DIV 1 = 42``, [thm_AUTO, thm_YO]),
    (``(0:num) DIV 42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:num) DIV 42 = 0``, [thm_AUTO, thm_YO]),
    (``(42:num) DIV 42 = 1``, [thm_AUTO, thm_YO]),
    (``(x:num) DIV 1 = x``, [thm_AUTO, thm_YO]),
    (``(x:num) DIV 42 <= x``, [thm_AUTO, thm_YO]),
    (``((x:num) DIV 42 = x) = (x = 0)``, [thm_AUTO, thm_YO]),
    (``(x:num) DIV 0 = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) DIV 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:num) DIV 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:num) DIV 0 = 1``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) DIV 0 = x DIV 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(0:num) MOD 1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:num) MOD 1 = 0``, [thm_AUTO, thm_YO]),
    (``(42:num) MOD 1 = 0``, [thm_AUTO, thm_YO]),
    (``(0:num) MOD 42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:num) MOD 42 = 1``, [thm_AUTO, thm_YO]),
    (``(42:num) MOD 42 = 0``, [thm_AUTO, thm_YO]),
    (``(x:num) MOD 1 = 0``, [thm_AUTO, thm_YO]),
    (``(x:num) MOD 42 < 42``, [thm_AUTO, thm_YO]),
    (``((x:num) MOD 42 = x) = (x < 42)``, [thm_AUTO, thm_YO]),
    (``(x:num) MOD 0 = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) MOD 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:num) MOD 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:num) MOD 0 = 1``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) MOD 0 = x MOD 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* cf. arithmeticTheory.DIVISION *)
    (``((x:num) = x DIV 1 * 1 + x MOD 1) /\ x MOD 1 < 1``, [thm_AUTO, thm_YO]),
    (``((x:num) = x DIV 42 * 42 + x MOD 42) /\ x MOD 42 < 42``,
      [thm_AUTO, thm_YO]),

    (``MIN (x:num) y <= x``, [thm_AUTO, thm_YO]),
    (``MIN (x:num) y <= y``, [thm_AUTO, thm_YO]),
    (``(z:num) < x /\ z < y ==> z < MIN x y``, [thm_AUTO, thm_YO]),
    (``MIN (x:num) y < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``MIN (x:num) 0 = 0``, [thm_AUTO, thm_YO]),

    (``MAX (x:num) y >= x``, [(*thm_AUTO,*) thm_YO]),
    (``MAX (x:num) y >= y``, [(*thm_AUTO,*) thm_YO]),
    (``(z:num) > x /\ z > y ==> z > MAX x y``, [(*thm_AUTO,*) thm_YO]),
    (``MAX (x:num) y > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``MAX (x:num) 0 = x``, [thm_AUTO, thm_YO]),

    (* int *)

    (``(x:int) + 0 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0 + (x:int) = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) + y = y + x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) + (y + z) = (x + y) + z``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``((x:int) + y = 0) = (x = 0) /\ (y = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:int) + y = 0) = (x = ~y)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(x:int) - 0 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) - y = y - x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) - y - z = x - (y + z)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) <= y ==> (x - y = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:int) - y = 0) \/ (y - x = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) - y = x + ~y``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(x:int) * 0 = 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0 * (x:int) = 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) * 1 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``1 * (x:int) = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) * ~1 = ~x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~1 * (x:int) = ~x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) * 42 = 42 * x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(~42:int) / ~42 = 1``, [thm_AUTO, thm_YO]),
    (``(~1:int) / ~42 = 0``, [thm_AUTO, thm_YO]),
    (``(0:int) / ~42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) / ~42 = ~1``, [thm_AUTO, thm_YO]),
    (``(42:int) / ~42 = ~1``, [thm_AUTO, thm_YO]),
    (``(~42:int) / ~1 = 42``, [thm_AUTO, thm_YO]),
    (``(~1:int) / ~1 = 1``, [thm_AUTO, thm_YO]),
    (``(0:int) / ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) / ~1 = ~1``, [thm_AUTO, thm_YO]),
    (``(42:int) / ~1 = ~42``, [thm_AUTO, thm_YO]),
    (``(~42:int) / 1 = ~42``, [thm_AUTO, thm_YO]),
    (``(~1:int) / 1 = ~1``, [thm_AUTO, thm_YO]),
    (``(0:int) / 1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) / 1 = 1``, [thm_AUTO, thm_YO]),
    (``(42:int) / 1 = 42``, [thm_AUTO, thm_YO]),
    (``(~42:int) / 42 = ~1``, [thm_AUTO, thm_YO]),
    (``(~1:int) / 42 = ~1``, [thm_AUTO, thm_YO]),
    (``(0:int) / 42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) / 42 = 0``, [thm_AUTO, thm_YO]),
    (``(42:int) / 42 = 1``, [thm_AUTO, thm_YO]),
    (``(x:int) / 1 = x``, [thm_AUTO, thm_YO]),
    (``(x:int) / ~1 = ~x``, [thm_AUTO, thm_YO]),
    (``(x:int) / 42 <= x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) / 42 <= ABS x``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``((x:int) / 42 = x) = (x = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:int) / 42 = x) = (x = 0) \/ (x = ~1)``, [thm_AUTO, thm_YO]),
    (``(x:int) / 0 = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) / 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:int) / 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:int) / 0 = 1``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:int) / 0 = 1 / 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) / 0 = x / 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* cf. integerTheory.int_div *)
    (``(x:int) < 0 ==> (x / 1 = ~(~x / 1) + if ~x % 1 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_YO]),
    (``(x:int) < 0 ==> (x / 42 = ~(~x / 42) + if ~x % 42 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_YO]),
    (``0 <= (x:int) ==> (x / ~42 = ~(x / 42) + if x % 42 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_YO]),
    (``0 <= (x:int) ==> (x / ~1 = ~(x / 1) + if x % 1 = 0 then 0 else ~1)``,
      [thm_AUTO, thm_YO]),
    (``(x:int) < 0 ==> (x / ~42 = ~x / 42)``, [thm_AUTO, thm_YO]),
    (``(x:int) < 0 ==> (x / ~1 = ~x / 1)``, [thm_AUTO, thm_YO]),

    (``(~42:int) % ~42 = 0``, [thm_AUTO, thm_YO]),
    (``(~1:int) % ~42 = ~1``, [thm_AUTO, thm_YO]),
    (``(0:int) % ~42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) % ~42 = ~41``, [thm_AUTO, thm_YO]),
    (``(42:int) % ~42 = 0``, [thm_AUTO, thm_YO]),
    (``(~42:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(~1:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(0:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(42:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(~42:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(~1:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(0:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(42:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(~42:int) % 42 = 0``, [thm_AUTO, thm_YO]),
    (``(~1:int) % 42 = 41``, [thm_AUTO, thm_YO]),
    (``(0:int) % 42 = 0``, [thm_AUTO, thm_YO]),
    (``(1:int) % 42 = 1``, [thm_AUTO, thm_YO]),
    (``(42:int) % 42 = 0``, [thm_AUTO, thm_YO]),
    (``(x:int) % 1 = 0``, [thm_AUTO, thm_YO]),
    (``(x:int) % ~1 = 0``, [thm_AUTO, thm_YO]),
    (``(x:int) % 42 < 42``, [thm_AUTO, thm_YO]),
    (``((x:int) % 42 = x) = (x < 42)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:int) % 42 = x) <=> (0 <= x) /\ (x < 42)``, [thm_AUTO, thm_YO]),
    (``(x:int) % 0 = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) % 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:int) % 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(0:int) % 0 = 1``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) % 0 = x % 0``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* cf. integerTheory.int_mod *)
    (``(x:int) % ~42 = x - x / ~42 * ~42``, [thm_AUTO, thm_YO]),
    (``(x:int) % ~1 = x - x / ~1 * ~1``, [thm_AUTO, thm_YO]),
    (``(x:int) % 1 = x - x / 1 * 1``, [thm_AUTO, thm_YO]),
    (``(x:int) % 42 = x - x / 42 * 42``, [thm_AUTO, thm_YO]),

    (``ABS (x:int) >= 0``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``(ABS (x:int) = 0) = (x = 0)``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``(x:int) >= 0 ==> (ABS x = x)``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``(x:int) <= 0 ==> (ABS x = ~x)``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``ABS (ABS (x:int)) = ABS x``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``ABS (x:int) = x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``int_min (x:int) y <= x``, [thm_AUTO, thm_YO]),
    (``int_min (x:int) y <= y``, [thm_AUTO, thm_YO]),
    (``(z:int) < x /\ z < y ==> z < int_min x y``, [thm_AUTO, thm_YO]),
    (``int_min (x:int) y < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``int_min (x:int) 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) >= 0 ==> (int_min x 0 = 0)``, [thm_AUTO, thm_YO]),

    (``int_max (x:int) y >= x``, [thm_AUTO, thm_YO]),
    (``int_max (x:int) y >= y``, [thm_AUTO, thm_YO]),
    (``(z:int) > x /\ z > y ==> z > int_max x y``, [thm_AUTO, thm_YO]),
    (``int_max (x:int) y > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) >= 0 ==> (int_max x 0 = x)``, [thm_AUTO, thm_YO]),

    (* real *)

    (``(x:real) + 0 = x``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0 + (x:real) = x``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:real) + y = y + x``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:real) + (y + z) = (x + y) + z``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``((x:real) + y = 0) = (x = 0) /\ (y = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:real) + y = 0) = (x = ~y)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``(x:real) - 0 = x``, [thm_AUTO, thm_YO]),
    (``(x:real) - y = y - x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) - y - z = x - (y + z)``, [thm_AUTO, thm_YO]),
    (``(x:real) <= y ==> (x - y = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:real) - y = 0) \/ (y - x = 0)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) - y = x + ~y``, [thm_AUTO, thm_YO]),

    (``(x:real) * 0 = 0``, [thm_AUTO, thm_YO]),
    (``0 * (x:real) = 0``, [thm_AUTO, thm_YO]),
    (``(x:real) * 1 = x``, [thm_AUTO, thm_YO]),
    (``1 * (x:real) = x``, [thm_AUTO, thm_YO]),
    (``(x:real) * 42 = 42 * x``, [thm_AUTO, thm_YO]),

    (``(x:real) / 1 = x``, [thm_AUTO, thm_YO]),
    (``x > 0 ==> (x:real) / 42 < x``, [(*thm_AUTO,*) thm_YO]),
    (``x < 0 ==> (x:real) / 42 > x``, [(*thm_AUTO,*) thm_YO]),

    (``abs (x:real) >= 0``, [thm_AUTO, thm_YO]),
    (``(abs (x:real) = 0) = (x = 0)``, [thm_AUTO, thm_YO]),
    (``(x:real) >= 0 ==> (abs x = x)``, [thm_AUTO, thm_YO]),
    (``(x:real) <= 0 ==> (abs x = ~x)``, [thm_AUTO, thm_YO]),
    (``abs (abs (x:real)) = abs x``, [thm_AUTO, thm_YO]),
    (``abs (x:real) = x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``min (x:real) y <= x``, [(*thm_AUTO,*) thm_YO]),
    (``min (x:real) y <= y``, [(*thm_AUTO,*) thm_YO]),
    (``(z:real) < x /\ z < y ==> z < min x y``, [(*thm_AUTO,*) thm_YO]),
    (``min (x:real) y < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``min (x:real) 0 = 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) >= 0 ==> (min x 0 = 0)``, [(*thm_AUTO,*) thm_YO]),

    (``max (x:real) y >= x``, [(*thm_AUTO,*) thm_YO]),
    (``max (x:real) y >= y``, [(*thm_AUTO,*) thm_YO]),
    (``(z:real) > x /\ z > y ==> z > max x y``, [(*thm_AUTO,*) thm_YO]),
    (``max (x:real) y > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) >= 0 ==> (max x 0 = x)``, [(*thm_AUTO,*) thm_YO]),

    (* arithmetic inequalities: <, <=, >, >= *)

    (* num *)

    (``0n < 1n``, [thm_AUTO, thm_YO]),
    (``1n < 0n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) < y ==> 42 * x < 42 * y``, [thm_AUTO, thm_YO]),

    (``0n <= 1n``, [thm_AUTO, thm_YO]),
    (``1n <= 0n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) <= x``, [thm_AUTO, thm_YO]),
    (``(x:num) <= y ==> 42 * x <= 42 * y``, [thm_AUTO, thm_YO]),

    (``1n > 0n``, [thm_AUTO, thm_YO]),
    (``0n > 1n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) > y ==> 42 * x > 42 * y``, [thm_AUTO, thm_YO]),

    (``1n >= 0n``, [thm_AUTO, thm_YO]),
    (``0n >= 1n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) >= x``, [thm_AUTO, thm_YO]),
    (``(x:num) >= y ==> 42 * x >= 42 * y``, [thm_AUTO, thm_YO]),

    (``((x:num) < y) = (y > x)``, [thm_AUTO, thm_YO]),
    (``((x:num) <= y) = (y >= x)``, [thm_AUTO, thm_YO]),
    (``(x:num) < y /\ y <= z ==> x < z``, [thm_AUTO, thm_YO]),
    (``(x:num) <= y /\ y <= z ==> x <= z``, [thm_AUTO, thm_YO]),
    (``(x:num) > y /\ y >= z ==> x > z``, [thm_AUTO, thm_YO]),
    (``(x:num) >= y /\ y >= z ==> x >= z``, [thm_AUTO, thm_YO]),

    (``(x:num) >= 0``, [thm_AUTO, thm_YO]),
    (``0 < (x:num) /\ x <= 1 ==> (x = 1)``, [thm_AUTO, thm_YO]),

    (* int *)

    (``0i < 1i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``1i < 0i``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) < y ==> 42 * x < 42 * y``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``0i <= 1i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``1i <= 0i``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) <= x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) <= y ==> 42 * x <= 42 * y``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1i > 0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0i > 1i``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) > y ==> 42 * x > 42 * y``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1i >= 0i``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0i >= 1i``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:int) >= x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) >= y ==> 42 * x >= 42 * y``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``((x:int) < y) = (y > x)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``((x:int) <= y) = (y >= x)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:int) < y /\ y <= z ==> x < z``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:int) <= y /\ y <= z ==> x <= z``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:int) > y /\ y >= z ==> x > z``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:int) >= y /\ y >= z ==> x >= z``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``(x:int) >= 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``0 < (x:int) /\ x <= 1 ==> (x = 1)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* real *)

    (``0r < 1r``, [thm_AUTO, thm_YO]),
    (``1r < 0r``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) < x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) < y ==> 42 * x < 42 * y``, [thm_AUTO, thm_YO]),

    (``0n <= 1n``, [thm_AUTO, thm_YO]),
    (``1n <= 0n``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:num) <= x``, [thm_AUTO, thm_YO]),
    (``(x:num) <= y ==> 2 * x <= 2 * y``, [thm_AUTO, thm_YO]),

    (``1r > 0r``, [thm_AUTO, thm_YO]),
    (``0r > 1r``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) > x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) > y ==> 42 * x > 42 * y``, [thm_AUTO, thm_YO]),

    (``1r >= 0r``, [thm_AUTO, thm_YO]),
    (``0r >= 1r``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:real) >= x``, [thm_AUTO, thm_YO]),
    (``(x:real) >= y ==> 42 * x >= 42 * y``, [thm_AUTO, thm_YO]),

    (``((x:real) < y) = (y > x)``, [thm_AUTO, thm_YO]),
    (``((x:real) <= y) = (y >= x)``, [thm_AUTO, thm_YO]),
    (``(x:real) < y /\ y <= z ==> x < z``, [thm_AUTO, thm_YO]),
    (``(x:real) <= y /\ y <= z ==> x <= z``, [thm_AUTO, thm_YO]),
    (``(x:real) > y /\ y >= z ==> x > z``, [thm_AUTO, thm_YO]),
    (``(x:real) >= y /\ y >= z ==> x >= z``, [thm_AUTO, thm_YO]),

    (``(x:real) >= 0``, [sat_YO, sat_Z3, sat_Z3p]),
    (``0 < (x:real) /\ x <= 1 ==> (x = 1)``,
      [sat_YO, sat_Z3, sat_Z3p]),

    (* uninterpreted functions *)

    (``(x = y) ==> (f x = f y)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x = y) ==> (f x y = f y x)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(f (f x) = x) /\ (f (f (f (f (f x)))) = x) ==> (f x = x)``,
      [(*thm_AUTO,*) thm_YO, thm_Z3, thm_Z3p]),
    (``(f x = f y) ==> (x = y)``, [sat_YO, sat_Z3, sat_Z3p]),

    (* predicates *)

    (``P x ==> P x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``P x ==> Q x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``P x ==> P y``, [sat_YO, sat_Z3, sat_Z3p]),
    (``P x y ==> P x x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``P x y ==> P y x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``P x y ==> P y y``, [sat_YO, sat_Z3, sat_Z3p]),

    (* quantifiers *)

    (``!x. x = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (* Yices 1.0.28 reports `unknown' for the next goal, while Z3 2.13
       (somewhat surprisingly, as SMT-LIB does not seem to require
       non-empty sorts) can prove it *)
    (``?x. x = x``, [thm_AUTO, thm_Z3(*, thm_Z3p*)]),
    (* Z3 2.13 reports `unknown' for the next goal *)
    (``(?y. !x. P x y) ==> (!x. ?y. P x y)``, [thm_AUTO, thm_YO]),
    (* Yices 1.0.28 and Z3 2.13 report `unknown' for the next goal *)
    (``(!x. ?y. P x y) ==> (?y. !x. P x y)``, []),
    (* Z3 2.13 reports `unknown' for the next goal *)
    (``(?x. P x) ==> !x. P x``, [sat_YO]),
    (* Z3 2.13 reports `unknown' for the next goal *)
    (``?x. P x ==> !x. P x``, [thm_AUTO, thm_YO]),

    (* let binders *)

    (``let x = y in let x = (x /\ z) in x <=> y /\ z``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``let x = u in let x = x in let y = v in x /\ y <=> u /\ v``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* lambda abstractions *)

    (``(\x. x) = (\y. y)``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(\x. \x. x) x x = (\y. \y. y) y x``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(\x. x (\x. x)) = (\y. y (\x. x))``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (* Yices 1.0.29 fails to decide this one *)
    (``(\x. x (\x. x)) = (\y. y x)``, [(*sat_YO,*) sat_Z3, sat_Z3p]),
    (``f x = (\x. f x) x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``f x = (\y. f y) x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* higher-order logic *)

    (* Z3 2.19 unexpectedly replaces certain implications by conjunctions in
       its proof *)

    (``(P (f x) ==> Q f) ==> P (f x) ==> Q f``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(Q f ==> P (f x)) ==> Q f ==> P (f x)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* tuples, FST, SND *)

    (``(x, y) = (x, z)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x, y) = (z, y)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x, y) = (y, x)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x, y) = (y, x)) = (x = y)``, [(*thm_AUTO,*) thm_YO]),
    (``((x, y, z) = (y, z, x)) <=> (x = y) /\ (y = z)``,
      [(*thm_AUTO,*) thm_YO]),
    (``((x, y) = (u, v)) <=> (x = u) /\ (y = v)``, [thm_AUTO, thm_YO]),

    (``y = FST (x, y)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x = FST (x, y)``, [thm_AUTO, thm_YO]),
    (``(FST (x, y, z) = FST (u, v, w)) = (x = u)``, [thm_AUTO, thm_YO]),
    (``(FST (x, y, z) = FST (u, v, w)) <=> (x = u) /\ (y = w)``,
      [sat_YO, sat_Z3, sat_Z3p]),

    (``y = SND (x, y)``, [thm_AUTO, thm_YO]),
    (``x = SND (x, y)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(SND (x, y, z) = SND (u, v, w)) = (y = v)``,
       [sat_YO, sat_Z3, sat_Z3p]),
    (``(SND (x, y, z) = SND (u, v, w)) = (z = w)``,
       [sat_YO, sat_Z3, sat_Z3p]),
    (``(SND (x, y, z) = SND (u, v, w)) <=> (y = v) /\ (z = w)``,
      [thm_AUTO, thm_YO]),

    (``(FST (x, y) = SND (x, y)) = (x = y)``, [thm_AUTO, thm_YO]),
    (``(FST p = SND p) = (p = (SND p, FST p))``, [(*thm_AUTO,*) thm_YO]),
    (``((\p. FST p) (x, y)= (\p. SND p) (x, y)) = (x = y)``,
      [thm_AUTO, thm_YO]),

    (* words (i.e., bit vectors) *)

    (``x:word2 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word3 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word4 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word5 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word6 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word7 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word8 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word12 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word16 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word20 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word24 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word28 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word30 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word64 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x:word32 && x = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 && y = y && x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32 && y) && z = x && (y && z)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 && 0w = 0w``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 && 0w = x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``x:word32 || x = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 || y = y || x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32 || y) || z = x || (y || z)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 || 0w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x:word32 || 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x:word32 ?? x = 0w``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 ?? y = y ?? x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32 ?? y) ?? z = x ?? (y ?? z)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 ?? 0w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x:word32 ?? 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``~ ~ x:word32 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~ 0w = 0w:word32``, [sat_YO, sat_Z3, sat_Z3p]),

    (* Yices does not support bit-vector division *)
    (* Z3 2.19 prints "extract" wrongly in its proofs *)

    (``x:word32 / 4w = x / 2w / 2w``, [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 / 6w = x / 2w / 3w``, [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 / x = 1w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x:word32 <> 0w ==> (x / x = 1w)``, [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``y:word8 <> 0w ==> (x / y = -x / -y)``, [sat_YO, sat_Z3, sat_Z3p]),
    (``y:word8 <> 0w ==> (x / y = -(-x / y))``, [sat_YO, sat_Z3, sat_Z3p]),
    (``y:word8 <> 0w ==> (x / y = -(x / -y))``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -x / -y)``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -(-x / y))``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word8 <> 0x80w /\ y <> 0w ==> (x / y = -(x / -y))``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (``x:word32 // 4w = x // 2w // 2w``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 // 6w = x // 2w // 3w``, [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 // x = 1w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``x:word32 <> 0w ==> (x // x = 1w)``, [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (``y:word8 <> 0w ==> (x = x // y * y + word_mod x y)``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``y:word8 <> 0w ==> word_mod x y <+ y``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (``y:word8 <> 0w ==> (x = x / y * y + word_rem x y)``,
      [(*thm_AUTO, thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (* Z3 2.19 does not handle "bvsrem ... bv0" correctly *)

    (``x:word8 < 0w /\ y < 0w  ==> (word_rem x y = -word_mod (-x) (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_Z3(*, thm_Z3p*)]),
    (``x:word8 < 0w /\ y >= 0w ==> (word_rem x y = -word_mod (-x) y)``,
      [(*thm_AUTO, thm_YO, thm_Z3, thm_Z3p*)]),
    (``x:word8 >= 0w /\ y < 0w ==> (word_rem x y = word_mod x (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_Z3(*, thm_Z3p*)]),
    (``x:word8 >= 0w /\ y >= 0w ==> (word_rem x y = word_mod x y)``,
      [(*thm_AUTO, thm_YO, thm_Z3, thm_Z3p*)]),

    (``x:word8 < 0w /\ y < 0w  ==> (word_smod x y = -word_mod (-x) (-y))``,
      [(*thm_AUTO, thm_YO,*)thm_Z3(*, thm_Z3p*)]),
    (``x:word8 < 0w /\ y >= 0w ==> (word_smod x y = -word_mod (-x) y + y)``,
      [(*thm_AUTO, thm_YO, thm_Z3, thm_Z3p*)]),
(* this is false: consider x = 99, y = 255
    (``x:word8 >= 0w /\ y < 0w ==> (word_smod x y = word_mod x (-y) + y)``,
      [(*thm_AUTO, thm_YO,*)thm_Z3(*, thm_Z3p*)]),
*)
    (``x:word8 >= 0w /\ y >= 0w ==> (word_smod x y = word_mod x y)``,
      [(*thm_AUTO, thm_YO, thm_Z3, thm_Z3p*)]),

    (``x:word32 << 0 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 << 31 = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 << 31 = 0w) \/ (x << 31 = 1w << 31)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* Yices does not support shifting by more than the word length *)

    (``x:word32 << 99 = 0w``, [thm_AUTO, (*thm_YO,*) thm_Z3, thm_Z3p]),

    (* Yices does not support shifting by a non-constant *)

    (``x:word32 << n = x``, [(*sat_YO,*) sat_Z3, sat_Z3p]),

    (``x:word32 <<~ 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 <<~ 31w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 <<~ 31w = 0w) \/ (x <<~ 31w = 1w <<~ 31w)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 <<~ x) && 1w = 0w``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``x:word32 <<~ y = y <<~ x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 <<~ y) <<~ z = x <<~ (y <<~ z)``, [sat_YO, sat_Z3, sat_Z3p]),

    (``x:word32 >>> 0 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 >>> 31 = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 >>> 31 = 0w) \/ (x >>> 31 = 1w)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (* Yices does not support right-shift by a (non-constant) bit-vector
       amount *)

    (``x:word32 >>>~ 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x:word32 >>>~ 31w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 >>>~ 31w = 0w) \/ (x >>>~ 31w = 1w)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 >>>~ x) = 0w``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 >>>~ y = y >>>~ x``, [(*sat_YO,*) sat_Z3, sat_Z3p]),
    (``(x:word32 >>>~ y) >>>~ z = x >>>~ (y >>>~ z)``,
      [(*sat_YO,*) sat_Z3, sat_Z3p]),

    (* Yices does not support arithmetical shift-right *)

    (``x:word32 >> 0 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3, thm_Z3p]),
    (``x:word32 >> 31 = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 >> 31 = 0w) \/ (x >> 31 = 0xFFFFFFFFw)``,
      [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),

    (``x:word32 >>~ 0w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3, thm_Z3p]),
    (``x:word32 >>~ 31w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 >>~ 31w = 0w) \/ (x >>~ 31w = 0xFFFFFFFFw)``,
      [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``(x:word32 >>~ x = 0w)  \/ (x >>~ x = 0xFFFFFFFFw)``,
      [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 >>~ y = y >>~ x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32 >>~ y) >>~ z = x >>~ (y >>~ z)``, [sat_YO, sat_Z3, sat_Z3p]),

    (* Yices does not support bit-vector rotation *)

    (``x:word32 #<< 0 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 32 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 64 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<< 1 <> x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``x:word32 #<<~ 0w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 32w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 64w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #<<~ 1w = x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``x:word32 #>> 0 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 32 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 64 = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>> 1 <> x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``x:word32 #>>~ 0w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 32w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 64w = x``, [thm_AUTO, (*thm_YO,*) thm_Z3(*, thm_Z3p*)]),
    (``x:word32 #>>~ 1w = x``, [sat_YO, sat_Z3, sat_Z3p]),

    (``1w:word2 @@ 1w:word2 = 5w:word4``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``((x @@ y):word32 = y @@ x) = (x:word16 = y)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(31 >< 0) x:word32 = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(1 >< 0) (0w:word32) = 0w:word2``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(32 >< 0) (x:word32) :bool[33] = w2w x``,
      [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``(0 >< 1) (x:word32) = 0w:word32``,
      [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),

    (``(x:word2 = y) <=> (x ' 0 = y ' 0) /\ (x ' 1 = y ' 1)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``0w:word32 = w2w (0w:word16)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = w2w (0w:word32)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = w2w (0w:word64)``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``x:word32 = w2w x``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``0w:word32 = sw2sw (0w:word16)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = sw2sw (0w:word32)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w:word32 = sw2sw (0w:word64)``, [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),
    (``x:word32 = sw2sw x``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),

    (``(x:word32) + x = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) + y = y + x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``((x:word32) + y) + z = x + (y + z)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32) + 0w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) + 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(x:word32) - x = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) - x = 0w``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32) - y = y - x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``((x:word32) - y) - z = x - (y - z)``,
      [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) - 0w = 0w``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) - 0w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``(x:word32) * x = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) * y = y * x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``((x:word32) * y) * z = x * (y * z)``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32) * 0w = 0w``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``(x:word32) * 0w = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``(x:word32) * 1w = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``- (x:word32) = x``, [sat_YO, sat_Z3, sat_Z3p]),
    (``- 0w = 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``- - (x:word32) = x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``0w < 1w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~ 0w < 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``0w <= 1w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x <= y:word32 <=> x < y \/ (x = y)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~ 0w <= 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1w > 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0w > ~ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1w >= 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x >= y:word32 <=> x > y \/ (x = y)``, [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w >= ~ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``0w <+ 1w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``0w <+ ~ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``0w <=+ 1w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x <=+ y:word32 <=> x <+ y \/ (x = y)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``0w <=+ ~ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1w >+ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``~ 0w >+ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``1w >=+ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x >=+ y:word32 <=> x >+ y \/ (x = y)``,
      [thm_AUTO, thm_YO, thm_Z3(*, thm_Z3p*)]),
    (``~ 0w >=+ 0w:word32``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (* from Magnus Myreen *)
    (``!(a:word32) b.
     (((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a)) /\ (a >= b <=> b <= a) /\ (a > b <=> b < a) /\
     (~(a <=+ b) <=> b <+ a) /\ (~(a <+ b) <=> b <=+ a) /\
     (a <+ b \/ (a = b) <=> a <=+ b) /\ (~(a < b) <=> b <= a) /\
     (~(a <= b) <=> b < a) /\ (a < b \/ (a = b) <=> a <= b) /\
     ((a = b) \/ a < b <=> a <= b) /\ (a <+ b \/ (a = b) <=> a <=+ b) /\
     ((a = b) \/ a <+ b <=> a <=+ b) /\
     (b <=+ a /\ a <> b <=> b <+ a) /\ (a <> b /\ b <=+ a <=> b <+ a) /\
     (b <= a /\ a <> b <=> b < a) /\ (a <> b /\ b <= a <=> b < a) /\
     (((v:word32) - w = 0w) <=> (v = w)) /\ (w - 0w = w)``,
      [(*thm_AUTO,*) thm_YO(*, thm_Z3, thm_Z3p*)]),

    (* from Yogesh Mahajan *)
    (``!(w: 18 word). (sw2sw w): 32 word = w2w ((16 >< 0) w: 17 word) +
     0xfffe0000w + ((0 >< 0) (~(17 >< 17) w: bool[unit]) << 17): 32 word``,
      [thm_AUTO, thm_YO(*, thm_Z3, thm_Z3p*)]),

    (* The Yices translation currently rejects polymorphic-width bit
       vectors; the SMT-LIB translation treats their type -- and
       operations on them -- as uninterpreted. *)

    (``x <=+ x``, [thm_AUTO(*, thm_YO, thm_Z3, thm_Z3p*)]),

    (* data types: constructors *)

    (``foo <> bar``, [thm_AUTO, thm_YO]),
    (``foo <> baz``, [thm_AUTO, thm_YO]),
    (``bar <> baz``, [thm_AUTO, thm_YO]),
    (``[] <> x::xs``, [thm_AUTO, thm_YO]),
    (``xs <> x::xs``, [thm_AUTO, thm_YO]),
    (``(x::xs = y::ys) <=> (x = y) /\ (xs = ys)``, [thm_AUTO, thm_YO]),

    (* data types: case constants *)

    (``dt1_CASE foo f b z = f``, [thm_AUTO, thm_YO]),
    (``dt1_CASE bar f b z = b``, [thm_AUTO, thm_YO]),
    (``dt1_CASE baz f b z = z``, [thm_AUTO, thm_YO]),
    (``dt1_CASE x c c c = c``, [(*thm_AUTO,*) thm_YO]),
    (``list_CASE [] n c = n``, [thm_AUTO, thm_YO]),
    (``list_CASE (x::xs) n c = c x xs``, [thm_AUTO, thm_YO]),

    (* records: field selectors *)

    (``(x = y) <=> (x.employed = y.employed) /\ (x.age = y.age)``,
      [(*thm_AUTO,*) thm_YO]),

    (* records: field updates *)

    (``(x with employed := e).employed = e``, [thm_AUTO, thm_YO]),

    (``x with <| employed := e; age := a |> =
     y with <| employed := e; age := a |>``, [thm_AUTO, thm_YO]),

    (* records: literals *)

    (``(<| employed := e1; age := a1 |> = <| employed := e2; age := a2 |>)
     <=> (e1 = e2) /\ (a1 = a2)``, [thm_AUTO, thm_YO]),

    (* sets (as predicates -- every set expression must be applied to an
       argument!) *)

    (``x IN P <=> P x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x IN {x | P x} <=> P x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x NOTIN {}``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN UNIV``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x IN P UNION Q <=> P x \/ Q x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P UNION {} <=> x IN P``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P UNION UNIV``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P UNION Q <=> x IN Q UNION P``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P UNION (Q UNION R) <=> x IN (P UNION Q) UNION R``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),

    (``x IN P INTER Q <=> P x /\ Q x``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x NOTIN P INTER {}``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P INTER UNIV <=> x IN P``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P INTER Q <=> x IN Q INTER P``, [thm_AUTO, thm_YO, thm_Z3, thm_Z3p]),
    (``x IN P INTER (Q INTER R) <=> x IN (P INTER Q) INTER R``,
      [thm_AUTO, thm_YO, thm_Z3, thm_Z3p])

  ]  (* tests *)
end

(*****************************************************************************)
(* actually perform tests                                                    *)
(*****************************************************************************)

val _ = map (fn (term, test_funs) =>
               map (fn test_fun => test_fun term) test_funs) tests

(*****************************************************************************)

val _ = print " done, all tests successful.\n"

val _ = OS.Process.exit OS.Process.success
