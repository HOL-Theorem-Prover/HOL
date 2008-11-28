(* Examples of verification using bmcStraight
*)

val opsemPath = Globals.HOLDIR ^ "/examples/opsemTools/";

loadPath := opsemPath ::
opsemPath ^ "java2opsem" :: 
opsemPath ^ "java2opsem/testFiles/opsemFiles" :: 
opsemPath ^ "verify" :: 
opsemPath ^ "verify/solvers" :: 
opsemPath ^ "verify/solvers/SMTSolver" ::
opsemPath ^ "verify/solvers/constraintSolver" ::
(!loadPath);

quietdec := true; (* turn off printing *)

(* app load ["PATH_EVAL","newOpsemTheory"];*)

(*load "bmcStraight";*)
open HolKernel Parse boolLib  PATH_EVAL 
     newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory  stringLib 
     stateTools  simpTools  bmcStraight ;

quietdec := false; (* turn printing back on *)

show_types:=true;

(* to be able to build and load the examples *)
use "java2opsem.ml";

val n = "AbsMinus";
val spec = loadAndGetSpec n 
verify spec n;
(* 
 - Verifying program AbsMinus 
building term: runtime: 1.468s,    gctime: 0.160s,     systime: 0.000s.
calling SMT solver: Calling external SMT solver on:
~((i < j ==>
   ((if ((if i <= j then 1 else 0) = 1) /\ ~(i = j) then
       j - i
     else
       i - j) =
    j - i)) /\
  (i >= j ==>
   ((if ((if i <= j then 1 else 0) = 1) /\ ~(i = j) then
       j - i
     else
       i - j) =
    i - j)))
runtime: 0.016s,    gctime: 0.004s,     systime: 0.000s.
Solving time with SMT solver: 0.0s.

==================
Program is correct
==================
*** Time taken: 1.396s
*)

val n = "AbsMinusKO";
val spec = loadAndGetSpec n
verify spec n;
(*
- Verifying program AbsMinusKO 
building term: runtime: 1.352s,    gctime: 0.132s,     systime: 0.000s.
Term to verify is:
?j i. ~(i >= j ==> (j - i = i - j))
calling SMT solver: Calling external SMT solver on:
~(i >= j ==> (j - i = i - j))
runtime: 0.004s,    gctime: 0.000s,     systime: 0.000s.
Solving time with SMT solver: 0.004s.

==================
An error has been found
==================
> val it = [("i", "-4"), ("j", "-5")] : (string * string) list
- - - - - 
*** Time taken: 1.360s
*)


val n = "Tritype";
val spec = loadAndGetSpec n 
verify spec n;
(* 
 - Verifying program Tritype 
building term: runtime: 3.788s,    gctime: 0.516s,     systime: 0.140s.
calling SMT solver: runtime: 0.116s,    gctime: 0.008s,     systime: 0.000s.
Solving time with SMT solver: 0.004s.

==================
Program is correct
==================
*** Time taken: 4.048s

*)


val n = "TritypeKO";
val spec = loadAndGetSpec n 
verify spec n;
(*
 - Verifying program TritypeKO 
building term: runtime: 3.700s,    gctime: 0.616s,     systime: 0.016s.
calling SMT solver: runtime: 0.120s,    gctime: 0.016s,     systime: 0.000s.
Solving time with SMT solver: 0.004s.

==================
An error has been found
==================
> val it = [("i", "2"), ("j", "3"), ("k", "2")] : (string * string) list
- - - - - 
*** Time taken: 3.972s
*)

val n = "GeneratedFlasherManager";
val spec = loadAndGetSpec n 
verify spec n;
(*
- Verifying program GeneratedFlasherManager 
building term: runtime: 223.854s,    gctime: 29.382s,     systime: 0.288s.
Term to verify is:
F
Term to verify has been simplified to a constant

==================
Program is correct
==================
> val it = [] : (string * string) list
- - - - - 
*** Time taken: 223.862s
*)

val n = "F1";
val spec = loadAndGetSpec n 
buildTermToVerify spec
- > val it = ``(T /\ T) /\ ~T`` : term
- - - - 
*** Time taken: 115.455s

val n = "TwoLoopsFlasherManager";
val spec = loadAndGetSpec n 
verify spec n;
(*
- Verifying program TwoLoopsFlasherManager 
building term: runtime: 235.119s,    gctime: 29.770s,     systime: 0.228s.
Term to verify is:
F
Term to verify has been simplified to a constant

==================
Program is correct
==================
> val it = [] : (string * string) list
- - - - - 
*** Time taken: 235.123s
*)


val n = "Sum";
val spec = loadAndGetSpec n 
verify spec n;

(*
Verifying program Sum 
building term: runtime: 2.920s,    gctime: 0.356s,     systime: 0.004s.
Term to verify is:
?n.
  (n >= 0 /\ 0 <= n /\ 1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\
   6 <= n /\ 7 <= n /\ 8 <= n /\ 9 <= n /\ ~(10 <= n)) /\
  ~(45 = n * (n + 1) / 2)
calling SMT solver: Calling external SMT solver on:
(n >= 0 /\ 0 <= n /\ 1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\
 6 <= n /\ 7 <= n /\ 8 <= n /\ 9 <= n /\ ~(10 <= n)) /\
~(45 = n * (n + 1) / 2)
Error: feature not supported: non linear problem.
Compilation error in yices file: SumStraightruntime: 0.016s,    gctime: 0.004s,     systime: 0.000s.
Term contains non linear expressions, calling constraint solver
calling constraint solver: Calling external solver with timeout on:
(n >= 0 /\ 0 <= n /\ 1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\
 6 <= n /\ 7 <= n /\ 8 <= n /\ 9 <= n /\ ~(10 <= n)) /\
~(45 = n * (n + 1) / 2)
ILOG JSolverForVerification, valid until 2009-01-20


Searching solutions for term in /home/helen/Recherche/hol/HOL/examples/opsemTools/verify/solvers/constraintSolver/xmlterm2csp//xml/SumStraight.xml

Constraint system
------------------------
{ 
  n[-128..127] >= 0
  n[-128..127] >= 0
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  not(n[-128..127] >= 10)
  not((n[-128..127] * (1 + n[-128..127] )) / 2 == 45)
} ------------------------
 using JSolver
---------
No solution
Resolution time : 0.0010s
---------

#########################
  Number of solve 1
  Number of fail 1
  Total solving time 0.0010s
#########################
runtime: 0.016s,    gctime: 0.000s,     systime: 0.000s.
Solving time with constraint solver: 0.001s.

==================
Program is correct
==================
> val it = [] : (string * string) list
- - - - - 
*** Time taken: 2.984s
*)



val n = "NestedLoop";
val spec = loadAndGetSpec n 
verify spec n;
(*
- Verifying program NestedLoop 
building term: runtime: 14.441s,    gctime: 2.044s,     systime: 0.024s.
calling SMT solver: Calling external SMT solver on:
(1 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 2 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 3 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 4 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 5 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 6 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 7 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 8 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 9 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 10 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ ~(11 <= n)) /\
~(100 = n * n)
Error: feature not supported: non linear problem.
Compilation error in yices file: NestedLoopStraightruntime: 0.064s,    gctime: 0.008s,     systime: 0.000s.
Term contains non linear expressions, calling constraint solver
calling constraint solver: Calling external solver with timeout on:
(1 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 2 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 3 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 4 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 5 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 6 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 7 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 8 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 9 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ 10 <= n /\
 (1 <= n /\ 2 <= n /\ 3 <= n /\ 4 <= n /\ 5 <= n /\ 6 <= n /\ 7 <= n /\
  8 <= n /\ 9 <= n /\ 10 <= n /\ ~(11 <= n)) /\ ~(11 <= n)) /\
~(100 = n * n)
ILOG JSolverForVerification, valid until 2009-01-20


Searching solutions for term in /home/helen/Recherche/hol/HOL/examples/opsemTools/verify/solvers/constraintSolver/xmlterm2csp//xml/NestedLoopStraight.xml

Constraint system
------------------------
{ 
  n[-128..127] >= 1
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 2
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 3
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 4
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 5
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 6
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 7
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 8
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 9
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  n[-128..127] >= 10
  n[-128..127] >= 1
  n[-128..127] >= 2
  n[-128..127] >= 3
  n[-128..127] >= 4
  n[-128..127] >= 5
  n[-128..127] >= 6
  n[-128..127] >= 7
  n[-128..127] >= 8
  n[-128..127] >= 9
  n[-128..127] >= 10
  not(n[-128..127] >= 11)
  not(n[-128..127] >= 11)
  not(square(n[-128..127]) == 100)
} ------------------------
 using JSolver
---------
No solution
Resolution time : 0.02s
---------

#########################
  Number of solve 1
  Number of fail 1
  Total solving time 0.02s
#########################
runtime: 0.196s,    gctime: 0.040s,     systime: 0.004s.
Solving time with constraint solver: 0.02s.

==================
Program is correct
==================
> val it = [] : (string * string) list
- - - - - 
*** Time taken: 14.781s

*)

(* version where n=6 to verify that loop is unwound only 6 times *)
(* since n is modified, need to change the postcondition, that depends on
the final state of n *)
val n = "FixedNestedLoop";
 val spec =
    ``RSPEC (\state. T)
        ("n" ::= C 6 ;;"s" ::= C 0 ;; "i" ::= C 1 ;;
         While (V "i" <= V "n")
           ("j" ::= C 1 ;;
            While (V "j" <= V "n")
              ("s" ::= V "s" + C 1 ;; "j" ::= V "j" + C 1) ;;
            "i" ::= V "i" + C 1) ;; "Result" ::= V "s")
        (\state1 state2.
           ScalarOf (state2 ' "Result") =
           ScalarOf (state2 ' "n") * ScalarOf (state2 ' "n"))``
verify spec n;

(*
Verifying program FixedNestedLoop 
building term: ======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
j <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
======================
Condition
i <= n
is FALSE on the current state,
 It is not possible to unwind loop one more time
runtime: 6.140s,    gctime: 0.916s,     systime: 0.020s.
Term to verify is:
F
Term to verify has been simplified to a constant

==================
Program is correct
==================
> val it = [] : (string * string) list
- - - - - 
*** Time taken: 6.140s

*)


(* -------------------- *)
(* programs with arrays *)
(* -------------------- *)


(* doesn't work yet *)

(*

(* search of an element in an array *) 
val n = "Search";
val spec = loadAndGetSpec n;
verify spec n;

(* does not scale
impossible to unwind loop 5 times!
interrupted after 324.716s

This is because test on arrays are translated as if then terms

    ``[("left",
        (if
           (if
              Num
                (if
                   (if Num (if a_0 = x then 0 else 1) = 9 then
                      a_9
                    else
                      (if Num (if a_0 = x then 0 else 1) = 8 then
                         a_8
                       else
                         (if Num (if a_0 = x then 0 else 1) = 7 then
                            a_7
                          else
                            (if Num (if a_0 = x then 0 else 1) = 6 then
                               a_6
                             else
                               (if Num (if a_0 = x then 0 else 1) = 5 then
                                  a_5
                                else
                                  (if
                                     Num (if a_0 = x then 0 else 1) = 4
                                   then
                                     a_4
                                   else
                                     (if
                                        Num (if a_0 = x then 0 else 1) = 3
                                      then
                                        a_3
                                      else
                                        (if
                                           Num (if a_0 = x then 0 else 1) =
                                           2
  ...

code for 2 unwindings takes 2500 lines!


*)


(* Binary search of an element in an array *)
val n = "Bsearch";
val spec = loadAndGetSpec n;
verify spec n;

val n = "BsearchKO";
val spec = loadAndGetSpec n;
verify spec n;


(* partition of QuicSort program *)
val n = "Partition";
val spec = loadAndGetSpec n;
verify spec n;


(* Selection sort *)
val n = "SelectionSort";
val spec = loadAndGetSpec n;
verify spec n;

(* Buble sort algorithm taken from a paper of mantovani and all *)
(* a precondition fixes the values of the array to 
   contains values from 0 to a.length given in decreasing
   order 
   i.e if the array is of length 10 it contains values
   9 8 7 6 5 4 3 2 1 0
*)
val n = "BubleSortMantovani";
val spec = loadAndGetSpec n;

*)
