(* ====================================================== *)
(* examples of symbolic execution using SMT solver        *)
(* this version uses HolSMTlib written by Tjark Weber     *)
(* ====================================================== *)


(* Stuff needed when running interactively *)

val opsemPath = Globals.HOLDIR ^ "/examples/opsemTools/";

loadPath := opsemPath :: opsemPath ^ "java2opsem" ::
opsemPath ^ "verify/solvers/" ::
opsemPath ^ "verify/solvers/SMTSolver" ::
opsemPath ^ "verify/" ::
(!loadPath);

quietdec := true; (* turn off printing *)

app load ["execSymbSMTlib"];
open execSymbSMTlib;

quietdec := false; (* turn printing back on *)


(* to be able to build and load the examples *)
use "java2opsem.ml";
 


(* ====================================================== *)
(* Examples of symbolic execution from test files
   in java2opsem/testFiles *)
(* ====================================================== *)



val name = "AbsMinus";
val spec = loadAndGetSpec name;
time (execSymbSMTlib.execSymbWithSMT name spec 20) "YICES";
time (execSymbSMTlib.execSymbWithSMT name spec 20) "Z3";
time (execSymbSMTlib.execSymbWithSMT name spec 20) "Z3_ORACLE";

(*
Symbolic execution using YICES_TAC
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j /\ i <> j
======================
======================
End of path
    i <= j /\ i <> j
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j /\ (i = j)
======================
======================
End of path
    i <= j /\ (i = j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ~(i <= j)
======================
======================
Condition
(k = 1) /\ i <> j
is FALSE on the current state, taking the other path
======================
End of path
    ~(i <= j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
===============================
PROGRAM IS CORRECT
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
===============================
> val it =
    ``if i <= j then
        if i <> j then
          RESULT
            (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+ ("k",Scalar 1) |+
             ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)))
        else
          RESULT
            (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+ ("k",Scalar 1) |+
             ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j)))
      else
        RESULT
          (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+ ("k",Scalar 0) |+
           ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j)))``
     : term
- - 
*** Time taken: 3.064s

Time taken with Z3:  3.236s
Time taken with Z3_ORACLE: 3.044s
*)


val name = "AbsMinusKO";
val spec = loadAndGetSpec name;
time (execSymbSMTlib.execSymbWithSMT name spec 20) "YICES";
time (execSymbSMTlib.execSymbWithSMT name spec 20) "Z3";
time (execSymbSMTlib.execSymbWithSMT name spec 20) "Z3_ORACLE";

(*
Symbolic execution using YICES_TAC
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j /\ i <> j
======================
======================
End of path
    i <= j /\ i <> j
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path i <= j /\ (i = j)
======================
======================
End of path
    i <= j /\ (i = j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ~(i <= j)
======================
======================
Condition
(k = 1) /\ i <> j
is FALSE on the current state, taking the other path
======================
End of path
    ~(i <= j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
HOL_ERR when calling SMT solver
HolSmtLib.GENERIC_SMT_TAC, message: solver reports negated term to be 'satisfiable'
Term is: !result Result k j i. T /\ ~(i <= j) ==> i >= j ==> (j - i = i - j)
===============================
1 ERROR has been found
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
===============================
runtime: 3.028s,    gctime: 0.360s,     systime: 0.052s.
> val it =
    ``if i <= j then
        if i <> j then
          RESULT
            (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar 1) |+
             ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)))
        else
          RESULT
            (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar 1) |+
             ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)))
      else
        RESULT
          (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar 0) |+
           ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)))``
     : term
- - 
*** Time taken: 3.104s
*)


val name = "Tritype";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec 30) "Z3";
time (execSymbWithSMT name spec 30) "Z3_ORACLE";



(*
Symbolic execution using Z3_TAC
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((i = 0) \/ (j = 0)) \/ (k = 0)
======================
======================
End of path
    ((i = 0) \/ (j = 0)) \/ (k = 0)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ~(((i = 0) \/ (j = 0)) \/ (k = 0))
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\ (j = k)
======================
======================
Condition
trityp = 0
is FALSE on the current state, taking the other path
======================
Condition
3 < trityp
is TRUE on the current state, taking this path
======================
End of path
    ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\ (j = k)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\ j <> kis unfeasable
======================
<<HOL message: Initialising SRW simpset ... done>>
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\ j <> k is impossible
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\ (j = k)is unfeasable
======================
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\ (j = k) is impossible
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\ j <> k
======================
======================
Condition
trityp = 0
is FALSE on the current state, taking the other path
======================
Condition
3 < trityp
is FALSE on the current state, taking the other path
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\
 j <> k) /\ k < i + j
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\
 j <> k) /\ k < i + j
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\
 j <> k) /\ ~(k < i + j)
======================
======================
Condition
(trityp = 2) /\ j < i + k
is FALSE on the current state, taking the other path
======================
Condition
(trityp = 3) /\ i < j + k
is FALSE on the current state, taking the other path
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ i <> k) /\
 j <> k) /\ ~(k < i + j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\ (j = k)is unfeasable
======================
======================
Path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\ (j = k) is impossible
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\ j <> k
======================
======================
Condition
trityp = 0
is FALSE on the current state, taking the other path
======================
Condition
3 < trityp
is FALSE on the current state, taking the other path
======================
Condition
(trityp = 1) /\ k < i + j
is FALSE on the current state, taking the other path
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\
 j <> k) /\ j < i + k
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\
 j <> k) /\ j < i + k
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\
 j <> k) /\ ~(j < i + k)
======================
======================
Condition
(trityp = 3) /\ i < j + k
is FALSE on the current state, taking the other path
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ (i = k)) /\
 j <> k) /\ ~(j < i + k)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\ (j = k)
======================
======================
Condition
trityp = 0
is FALSE on the current state, taking the other path
======================
Condition
3 < trityp
is FALSE on the current state, taking the other path
======================
Condition
(trityp = 1) /\ k < i + j
is FALSE on the current state, taking the other path
======================
Condition
(trityp = 2) /\ j < i + k
is FALSE on the current state, taking the other path
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 (j = k)) /\ i < j + k
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 (j = k)) /\ i < j + k
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 (j = k)) /\ ~(i < j + k)
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 (j = k)) /\ ~(i < j + k)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\ j <> k
======================
======================
Condition
trityp = 0
is TRUE on the current state, taking this path
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 j <> k) /\ (i + j <= k \/ j + k <= i \/ i + k <= j)
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 j <> k) /\ (i + j <= k \/ j + k <= i \/ i + k <= j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 j <> k) /\ ~(i + j <= k \/ j + k <= i \/ i + k <= j)
======================
======================
End of path
    (((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ i <> j) /\ i <> k) /\
 j <> k) /\ ~(i + j <= k \/ j + k <= i \/ i + k <= j)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'z3 -ini:z3.ini -smt input.z3.smt > output.z3'>>
<<HOL message: HolSmtLib: parsing Z3 proof file 'output.z3'>>
<<HOL message: HolSmtLib: checking Z3 proof>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (proof checked)>>
======================
Program is correct on this path
======================
===============================
PROGRAM IS CORRECT
27 conditions have been tested.
15 conditions have been solved by EVAL.
16 conditions have been shown impossible.

10 feasible paths have been explored.
===============================
> val it =
    ``if ((i = 0) \/ (j = 0)) \/ (k = 0) then
        RESULT
          (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 4) |+ ("Result",Scalar 4))
      else
        if i = j then
          if i = k then
            RESULT
              (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
               ("k",Scalar k) |+ ("trityp",Scalar 3) |+ ("Result",Scalar 3))
          else
            if k < i + j then
              RESULT
                (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                 ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                 ("Result",Scalar 2))
            else
              RESULT
                (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                 ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                 ("Result",Scalar 4))
        else
          if i = k then
            if j < i + k then
              RESULT
                (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                 ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                 ("Result",Scalar 2))
            else
              RESULT
                (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                 ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                 ("Result",Scalar 4))
          else
            if j = k then
              if i < j + k then
                RESULT
                  (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                   ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                   ("Result",Scalar 2))
              else
                RESULT
                  (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                   ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                   ("Result",Scalar 4))
            else
              if i + j <= k \/ j + k <= i \/ i + k <= j then
                RESULT
                  (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                   ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                   ("Result",Scalar 4))
              else
                RESULT
                  (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                   ("k",Scalar k) |+ ("trityp",Scalar 1) |+
                   ("Result",Scalar 1))`` : term
- - 
*** Time taken: 22.793s

Time taken with Z3_ORACLE: 18.289s
*)




(* =================================== *)
(* Program with arrays                 *)
(* =================================== *)


(* search of an element in an array *) 
val name = "Search";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30 "YICES"; 
execSymbWithSMT name spec 30 "Z3"; 

(*
===============================
PROGRAM IS CORRECT
10 conditions have been tested.
0 condition has been solved by EVAL.
0 condition has been shown impossible.

11 feasible paths have been explored.
===============================
*)


(* Binary search of an element in an array *)
val name = "Bsearch";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30 "YICES"

(*
Symbolic execution using YICES_TAC
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path a_0 = x
======================
======================
End of path
    a_0 = x
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path a_0 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path a_0 <> x /\ (a_1 = x)
======================
======================
End of path
    a_0 <> x /\ (a_1 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path a_0 <> x /\ a_1 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (a_0 <> x /\ a_1 <> x) /\ (a_2 = x)
======================
======================
End of path
    (a_0 <> x /\ a_1 <> x) /\ (a_2 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (a_0 <> x /\ a_1 <> x) /\ a_2 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ (a_3 = x)
======================
======================
End of path
    ((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ (a_3 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ (a_4 = x)
======================
======================
End of path
    (((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ (a_4 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
(a_5 = x)
======================
======================
End of path
    ((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
(a_5 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
a_5 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
 a_5 <> x) /\ (a_6 = x)
======================
======================
End of path
    (((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
 a_5 <> x) /\ (a_6 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
 a_5 <> x) /\ a_6 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
  a_5 <> x) /\ a_6 <> x) /\ (a_7 = x)
======================
======================
End of path
    ((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
  a_5 <> x) /\ a_6 <> x) /\ (a_7 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
  a_5 <> x) /\ a_6 <> x) /\ a_7 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
   a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ (a_8 = x)
======================
======================
End of path
    (((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
   a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ (a_8 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path (((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
   a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ a_8 <> x
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
    a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ a_8 <> x) /\ (a_9 = x)
======================
======================
End of path
    ((((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
    a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ a_8 <> x) /\ (a_9 = x)
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'satisfiable' (no model given)>>
======================
Yices fails to shows that path is unfeasable
Taking path ((((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
    a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ a_8 <> x) /\ a_9 <> x
======================
======================
End of path
    ((((((((a_0 <> x /\ a_1 <> x) /\ a_2 <> x) /\ a_3 <> x) /\ a_4 <> x) /\
    a_5 <> x) /\ a_6 <> x) /\ a_7 <> x) /\ a_8 <> x) /\ a_9 <> x
======================
======================
Testing correctness
======================
<<HOL message: HolSmtLib: calling external command 'yices -tc input.yices > output.yices'>>
<<HOL message: HolSmtLib: solver returned 'unsatisfiable' (no proof given)>>
======================
Program is correct on this path
======================
===============================
PROGRAM IS CORRECT
10 conditions have been tested.
0 condition has been solved by EVAL.
0 condition has been shown impossible.

11 feasible paths have been explored.
===============================
> val it =
    ``if a_0 = x then
        RESULT
          (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
           ("a",
            Array
              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
               (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
               (9,a_9))) |+ ("left",Scalar 0) |+ ("result",Scalar 0) |+
           ("Result",Scalar 0))
      else
        if a_1 = x then
          RESULT
            (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
             ("a",
              Array
                (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                 (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                 (9,a_9))) |+ ("left",Scalar 1) |+ ("result",Scalar 1) |+
             ("Result",Scalar 1))
        else
          if a_2 = x then
            RESULT
              (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
               ("a",
                Array
                  (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                   (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                   (9,a_9))) |+ ("left",Scalar 2) |+ ("result",Scalar 2) |+
               ("Result",Scalar 2))
          else
            if a_3 = x then
              RESULT
                (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                 ("a",
                  Array
                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                     (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                     (9,a_9))) |+ ("left",Scalar 3) |+
                 ("result",Scalar 3) |+ ("Result",Scalar 3))
            else
              if a_4 = x then
                RESULT
                  (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                   ("a",
                    Array
                      (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                       (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                       (8,a_8) |+ (9,a_9))) |+ ("left",Scalar 4) |+
                   ("result",Scalar 4) |+ ("Result",Scalar 4))
              else
                if a_5 = x then
                  RESULT
                    (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                     ("a",
                      Array
                        (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                         (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                         (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                     ("left",Scalar 5) |+ ("result",Scalar 5) |+
                     ("Result",Scalar 5))
                else
                  if a_6 = x then
                    RESULT
                      (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                       ("a",
                        Array
                          (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                           (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                           (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                       ("left",Scalar 6) |+ ("result",Scalar 6) |+
                       ("Result",Scalar 6))
                  else
                    if a_7 = x then
                      RESULT
                        (FEMPTY |+ ("x",Scalar x) |+
                         ("aLength",Scalar 10) |+
                         ("a",
                          Array
                            (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                             (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                             (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                         ("left",Scalar 7) |+ ("result",Scalar 7) |+
                         ("Result",Scalar 7))
                    else
                      if a_8 = x then
                        RESULT
                          (FEMPTY |+ ("x",Scalar x) |+
                           ("aLength",Scalar 10) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("left",Scalar 8) |+ ("result",Scalar 8) |+
                           ("Result",Scalar 8))
                      else
                        if a_9 = x then
                          RESULT
                            (FEMPTY |+ ("x",Scalar x) |+
                             ("aLength",Scalar 10) |+
                             ("a",
                              Array
                                (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                 (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                                 (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                             ("left",Scalar 9) |+ ("result",Scalar 9) |+
                             ("Result",Scalar 9))
                        else
                          RESULT
                            (FEMPTY |+ ("x",Scalar x) |+
                             ("aLength",Scalar 10) |+
                             ("a",
                              Array
                                (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                 (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                                 (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                             ("result",Scalar (-1)) |+ ("left",Scalar 10) |+
                             ("Result",Scalar (-1)))`` : term
- - 
*** Time taken: 14.169s
*)


(* Binary search of an element in an array *)
val name = "Bsearch";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec 30) "YICES";
time (execSymbWithSMT name spec 30) "Z3";
time (execSymbWithSMT name spec 30) "Z3_ORACLE";




(*
===============================
PROGRAM IS CORRECT
20 conditions have been tested.
0 condition has been solved by EVAL.
0 condition has been shown impossible.

21 feasible paths have been explored.
===============================
*** Time taken with Yices: 36.594s
*** Time taken with Z3: 37.742s
*** Time taken with Z3_ORACLE: 37.366s
*)




