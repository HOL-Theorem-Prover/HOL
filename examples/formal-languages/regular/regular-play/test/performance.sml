
(* load the neccessary SML libraries *)
Meta.load "../emit/regexEMCML";
Meta.load "../lib/regex";
Meta.load "../lib/regexRef";
Meta.load "../lib/regexExe";
Meta.load "../lib/regexExeM";
Meta.load "../lib/regexExeMC";
Meta.load "regexTest";



(* performance test flag, set to true to run additional tests *)
val runPerformanceTests = true;


exception TestCaseException of (string * int);

(* create a test template as a functor *)    
functor regexTestRunner (regexM:regex) =
struct

  fun test name tests =
       let
         open regexTest;

         fun execTestCase (id, b, r, s) =
                if b = (regexM.match r s) then ()
                else raise TestCaseException (name, id);

         val () = print ("Starting test of \"" ^ name ^ "\"\n");
         val lasttimer = start_time();

         val () = foldl (fn (t, ()) => execTestCase t) () tests;

         val () = end_time lasttimer;
         val () = print "Tests ended all successful.\n\n";

       in
         ()
       end

end;


fun runTestFun testFun name tests =
       (testFun name tests; true)
       handle TestCaseException(_, id) => (
         print ("Test with id '" ^ (Int.toString id) ^ "' failed.\n\n");
         false
       );
         



(* create 4 instances using the functor *)
structure regexTestRunner1 = regexTestRunner (regexRef);
structure regexTestRunner2 = regexTestRunner (regexExe);
structure regexTestRunner3 = regexTestRunner (regexExeM);
structure regexTestRunner4 = regexTestRunner (regexExeMC);


val () = print "\n\n\n";

(* run the test template functor for all 4 instances *)
local
  val tests = regexTest.getTests();
in
  val res1 = runTestFun regexTestRunner1.test "IMPL_ref" tests;
  val res2 = runTestFun regexTestRunner2.test "IMPL_exec" tests;
  val res3 = runTestFun regexTestRunner3.test "IMPL_exec_marked" tests;
  val res4 = runTestFun regexTestRunner4.test "IMPL_exec_mark_cache" tests;
end

(* throw an exception if at least one of the instances fails *)
val () = if (res1 andalso res2 andalso res3 andalso res4) then ()
         else OS.Process.terminate OS.Process.failure;






(* additional performance tests *)
val () = if runPerformanceTests then ()
         else OS.Process.terminate OS.Process.success;

val () = print "\n\n\n";
val () = print "And now the performance tests.\n";




val () = print "\n\n\n";
local
  val () = print "Loading random test data with 6..\n";
  val tests = regexTest.getPerformanceTests "/dev/urandom" (6);
in
  val true = runTestFun regexTestRunner1.test "IMPL_ref_perf" tests;
  val true = runTestFun regexTestRunner2.test "IMPL_exec_perf" tests;
  val true = runTestFun regexTestRunner3.test "IMPL_exec_marked_perf" tests;
  val true = runTestFun regexTestRunner4.test "IMPL_exec_mark_cache_perf" tests;
end


(* test/data/gen.py 10000000 12 > test/data/test12 *)
val () = print "\n\n\n";
local
  val () = print "Loading test data with 100000..\n";
  val tests = regexTest.getPerformanceTests "./test/data/test12" (100000);
in
  val true = runTestFun regexTestRunner1.test "IMPL_ref_perf" tests;
(*  val true = runTestFun regexTestRunner2.test "IMPL_exec_perf" tests;*)
  val true = runTestFun regexTestRunner3.test "IMPL_exec_marked_perf" tests;
  val true = runTestFun regexTestRunner4.test "IMPL_exec_mark_cache_perf" tests;
end


(* test/data/gen.py 10000000 12 > test/data/test12 *)
val () = print "\n\n\n";
local
  val () = print "Loading test data with 10000, regex size 600..\n";
  val tests = regexTest.getPerformanceTestsRegexSize "./test/data/test12" (10000) (600);
in
  val true = runTestFun regexTestRunner1.test "IMPL_ref_perf" tests;
(*  val true = runTestFun regexTestRunner2.test "IMPL_exec_perf" tests;*)
  val true = runTestFun regexTestRunner3.test "IMPL_exec_marked_perf" tests;
  val true = runTestFun regexTestRunner4.test "IMPL_exec_mark_cache_perf" tests;
end


(* test/data/gen.py 10000000 12 > test/data/test12 *)
val () = print "\n\n\n";
local
  val () = print "Loading test data with 100000, regex size 10000..\n";
  val tests = regexTest.getPerformanceTestsRegexSize "./test/data/test12" (100000) (10000);
in
(*  val true = runTestFun regexTestRunner1.test "IMPL_ref_perf" tests;*)
(*  val true = runTestFun regexTestRunner2.test "IMPL_exec_perf" tests;*)
  val true = runTestFun regexTestRunner3.test "IMPL_exec_marked_perf" tests;
  val true = runTestFun regexTestRunner4.test "IMPL_exec_mark_cache_perf" tests;
end



