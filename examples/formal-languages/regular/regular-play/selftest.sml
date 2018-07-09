
(* examples *)
(* /opt/hol_bir/examples/formal-languages/context-free/selftest.sml *)
(* /opt/hol_bir/examples/separationLogic/src/holfoot/selftest.sml *)

(* also look at: /opt/hol_bir/src/list/src/selftest.sml *)

(* /opt/hol_bir/src/pattern_matches *)


open HolKernel Parse boolLib bossLib;


open regexSemanticsTheory;
open regexExecutableTheory;
open regexMarkedTheory;
open regexCachedMarkedTheory;

open stringTheory;


open testutils;

val hard_fail = true;
val _ = really_die := true;
val quiet = false;




fun test_a_case casename (oresultval, expectedval) =
  let
    val _ = print ("Result of case \"" ^ casename ^ "\":\t");
    val _ = print (if not (isSome oresultval) then "UNKNOWN ERROR" else (if (valOf oresultval) = expectedval then "success" else "ERROR"));
    val _ = print "\n";
  in
    ()
  end;

(* debug switch, enables a complete test even if one case fails *)
val runtoend = false;
fun run_a_case casename testfun expectedval =
  let
    val ores = if runtoend then ((SOME (testfun ())) handle _ => NONE) else (SOME (testfun ()));
  in
    test_a_case casename (ores, expectedval)
  end;

fun evalFun term () = ((snd o dest_eq o concl o EVAL) term);




(* test the definitions in regexExecutableTheory *)
(* ----------------------------------------------------------------------------- *)
run_a_case "simpe parts test"
           (evalFun ``parts "acc"``)
           ``[["acc"]; ["a"; "cc"]; ["ac"; "c"]; ["a"; "c"; "c"]]``;

run_a_case "simpe split test"
           (evalFun ``split "acc"``)
           ``[("","acc"); ("a","cc"); ("ac","c"); ("acc","")]``;


val aObS = ``(Rep (Alt (Sym #"a") (Sym #"b")))``;
val aObSc = ``(Seq ^aObS (Sym #"c"))``;
val regExp = ``Seq (Rep (Seq ^aObSc ^aObSc)) ^aObS``;

run_a_case "simpe test accept acc"
           (evalFun ``accept ^regExp "acc"``)
           ``T``;

run_a_case "simpe test accept accc"
           (evalFun ``accept ^regExp "accc"``)
           ``F``;







(* test the definitions in regexMarkedTheory *)
(* ----------------------------------------------------------------------------- *)
val aObS = ``(Rep (Alt (Sym #"a") (Sym #"b")))``;
val aObSc = ``(Seq ^aObS (Sym #"c"))``;
val regExp = ``Seq (Rep (Seq ^aObSc ^aObSc)) ^aObS``;

run_a_case "simpe test acceptM acc"
           (evalFun ``acceptM (MARK_REG ^regExp) "acc"``)
           ``T``;

run_a_case "simpe test acceptM accc"
           (evalFun ``acceptM (MARK_REG ^regExp) "accc"``)
           ``F``;









(* test the definitions in regexCachedMarkedTheory *)
(* ----------------------------------------------------------------------------- *)
val aObS = ``(Rep (Alt (Sym #"a") (Sym #"b")))``;
val aObSc = ``(Seq ^aObS (Sym #"c"))``;
val regExp = ``Seq (Rep (Seq ^aObSc ^aObSc)) ^aObS``;

run_a_case "simpe test acceptCM acc"
           (evalFun ``acceptCM (CACHE_REG (MARK_REG ^regExp)) "acc"``)
           ``T``;

run_a_case "simpe test acceptCM accc"
           (evalFun ``acceptCM (CACHE_REG (MARK_REG ^regExp)) "accc"``)
           ``F``;






(* testing using the emitted SML code and the test library *)
(* ----------------------------------------------------------------------------- *)
(* make HOL4 load the required libraries *)
local
  open regexEMCML;
  open regex;
  open regexExe;
  open regexExeM;
  open regexExeMC;
  open regexTest;
in
end;
(* retrieve the tests *)
val basicTestcases = regexTest.getTests ();




(* create the test machine for comliance testing *)
exception TestCaseException of (string * int);

functor regexTestCaseRunner (regexM:regex) =
struct

  fun execRegexCase testname (id, b, r, s) () =
    let
      val exeVal = regexExe.match r s;
      val refVal = regexRef.match r s;
    in
      if refVal <> b then
        raise TestCaseException (testname, id)
      else
        exeVal = refVal
    end;


  fun test testname = foldl (fn ((id, b, r, s), ()) =>
                            run_a_case (testname ^ " #" ^ (Int.toString id)) (execRegexCase testname (id, b, r, s)) true
                        ) () basicTestcases;

end;




(* run the tests on all implementations *)
val testname1 = "conformance testing Exe  ";
structure regexTestCaseRunner1 = regexTestCaseRunner (regexExe);
val testname2 = "conformance testing ExeM ";
structure regexTestCaseRunner2 = regexTestCaseRunner (regexExeM);
val testname3 = "conformance testing ExeMC";
structure regexTestCaseRunner3 = regexTestCaseRunner (regexExeMC);

val () = regexTestCaseRunner1.test testname1;
val () = regexTestCaseRunner2.test testname2;
val () = regexTestCaseRunner3.test testname3;






