(* ====================================================== *)
(* examples of symbolic execution using HOL, SMT solver
   for cutting and solving paths, and constraint solver when 
   there is a non linear expression   
*)
(* ====================================================== *)


(* Stuff needed when running interactively *)

val opsemPath = Globals.HOLDIR ^ "/examples/opsemTools/";

loadPath := opsemPath :: opsemPath ^ "java2opsem" ::
opsemPath ^ "verify/solvers/" ::
opsemPath ^ "verify/solvers/SMTSolver" ::
opsemPath ^ "verify/solvers/constraintSolver" ::
opsemPath ^ "verify/" ::
(!loadPath);

quietdec := true; (* turn off printing *)

app load ["execSymbHOLandSMT"];
open execSymbHOLandSMT;

quietdec := false; (* turn printing back on *)
 

(* to be able to build and load the examples *)
use "java2opsem.ml";
 

(* ====================================================== *)
(* Examples of symbolic execution from test files
   in java2opsem/testFiles *)
(* ====================================================== *)

val name = "AbsMinus";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 20;


(*
======================
Testing feasability
======================
Calling external SMT solver on:
T /\ i <= j
======================
Taking path i <= j
======================
======================
Testing feasability
======================
Calling external SMT solver on:
T /\ i <= j /\ ~(i = j)
======================
Taking path i <= j /\ ~(i = j)
======================
======================
End of path
    i <= j /\ ~(i = j)
======================

Term to be refuted with METIS ?result Result k i j.
  (T /\ i <= j /\ ~(i = j)) /\ i >= j /\ ~(j - i = i - j)
METIS failed
Trying to simplify with SIMP_CONV and COOPER
<<HOL message: Initialising SRW simpset ... done>>
======================
Program is correct on this path
======================
======================
Testing feasability
======================
Calling external SMT solver on:
T /\ i <= j /\ (i = j)
======================
Taking path i <= j /\ (i = j)
======================
======================
End of path
    i <= j /\ (i = j)
======================

Term to be refuted with METIS ?result Result k i j.
  (T /\ i <= j /\ (i = j)) /\ i < j /\ ~(i - j = j - i)
======================
Program is correct on this path
======================
======================
Testing feasability
======================
Calling external SMT solver on:
T /\ ~(i <= j)
======================
Taking path ~(i <= j)
======================
======================
Condition
(k = 1) /\ ~(i = j)
is FALSE on the current state, taking the other path
======================
End of path
    ~(i <= j)
======================

Term to be refuted with METIS ?result Result k i j. (T /\ ~(i <= j)) /\ i < j /\ ~(i - j = j - i)
METIS failed
Trying to simplify with SIMP_CONV and COOPER
===============================
PROGRAM IS CORRECT
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
All correct paths were verified in HOL.
1 subterm has been solved with refute and METIS.
2 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.008s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 5.184s,    gctime: 0.748s,     systime: 0.044s.
> val it =
    ``(if i <= j then
         (if ~(i = j) then
            RESULT
              (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i)))
          else
            RESULT
              (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+
               ("k",Scalar 1) |+ ("result",Scalar (i - j)) |+
               ("Result",Scalar (i - j))))
       else
         RESULT
           (FEMPTY |+ ("j",Scalar j) |+ ("i",Scalar i) |+ ("k",Scalar 0) |+
            ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j))))`` : term
- - - - - 
*** Time taken: 5.208s

Examples of solutions found by SMT solver when the path is possible:
val t = ``T /\ i <= j``
extSolvSMT name t
sat
(= i 0)
(= j 0)

val t = ``T /\ i <= j /\ ~(i = j)``
extSolvSMT name t
(= i -1)
(= j 0)

val t = ``T /\ i <= j /\ (i = j)``
extSolvSMT name t
sat
(= i 0)
(= j 0)

val t = ``T /\ ~(i <= j)``
extSolvSMT name t
sat
(= i 1)
(= j 0)
*)



val name = "AbsMinusKO";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 20;

(*
===============================
1 ERROR has been found
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
All correct paths were verified in HOL.
1 subterm has been solved with refute and METIS.
2 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.02s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 5.444s,    gctime: 0.696s,     systime: 0.204s.
> val it =
    ``(if i <= j then
         (if ~(i = j) then
            RESULT
              (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i)))
          else
            RESULT
              (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i))))
       else
         ERROR
           (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar 0) |+
            ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)) |+
            ("i",Scalar 1) |+ ("j",Scalar 0)))`` : term
- - - - - 
*** Time taken: 5.720s
*)

val name = "Tritype";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 30;



(*
===============================
PROGRAM IS CORRECT
27 conditions have been tested.
15 conditions have been solved by EVAL.
16 conditions have been shown impossible.

10 feasible paths have been explored.
All correct paths were verified in HOL.
20 subterms have been solved with refute and METIS.
10 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.064s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 88.874s,    gctime: 11.285s,     systime: 0.400s.

> val it =
    ``(if ((i = 0) \/ (j = 0)) \/ (k = 0) then
         RESULT
           (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
            ("trityp",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if i = j then
            (if i = k then
               RESULT
                 (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                  ("k",Scalar k) |+ ("trityp",Scalar 3) |+
                  ("Result",Scalar 3))
             else
               (if k < i + j then
                  RESULT
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                     ("Result",Scalar 2))
                else
                  RESULT
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                     ("Result",Scalar 4))))
          else
            (if i = k then
               (if j < i + k then
                  RESULT
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                     ("Result",Scalar 2))
                else
                  RESULT
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                     ("Result",Scalar 4)))
             else
               (if j = k then
                  (if i < j + k then
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                        ("Result",Scalar 2))
                   else
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                        ("Result",Scalar 4)))
                else
                  (if i + j <= k \/ j + k <= i \/ i + k <= j then
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                        ("Result",Scalar 4))
                   else
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 1) |+
                        ("Result",Scalar 1)))))))`` : term
- - - - - 
*** Time taken: 88.562s
*)


val name = "TritypeKO";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 30 ;

(*
===============================
2 ERRORs have been found
26 conditions have been tested.
14 conditions have been solved by EVAL.
16 conditions have been shown impossible.

9 feasible paths have been explored.
All correct paths were verified in HOL.
18 subterms have been solved with refute and METIS.
9 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.072s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 62.588s,    gctime: 8.269s,     systime: 0.984s.
> val it =
    ``(if ((i = 0) \/ (j = 0)) \/ (k = 0) then
         RESULT
           (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
            ("trityp",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if i = j then
            (if i = k then
               RESULT
                 (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                  ("k",Scalar k) |+ ("trityp",Scalar 3) |+
                  ("Result",Scalar 3))
             else
               (if k < i + j then
                  RESULT
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                     ("Result",Scalar 2))
                else
                  ERROR
                    (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                     ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                     ("Result",Scalar 2) |+ ("i",Scalar 1) |+
                     ("j",Scalar 1) |+ ("k",Scalar 2))))
          else
            (if i = k then
               ERROR
                 (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                  ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                  ("Result",Scalar 4) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
                  ("k",Scalar 2))
             else
               (if j = k then
                  (if i < j + k then
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 2) |+
                        ("Result",Scalar 2))
                   else
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                        ("Result",Scalar 4)))
                else
                  (if (i + j <= k \/ j + k <= i) \/ i + k <= j then
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                        ("Result",Scalar 4))
                   else
                     RESULT
                       (FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j) |+
                        ("k",Scalar k) |+ ("trityp",Scalar 1) |+
                        ("Result",Scalar 1)))))))`` : term
- - - - - 
*** Time taken: 61.464s
*)


val name = "Sum";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 41; (* 10 times into the loop *)

(*
===============================
PROGRAM IS CORRECT
12 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

11 feasible paths have been explored.
0 path has been shown correct with the SMT solver
11 paths have been shown correct with the CSP solver
0 subterm has been solved with refute and METIS.
11 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.052s.

8 bits: Total time spent with the CSP solver: 0.025s.
16 bits: Total time spent with the CSP solver: 0.032s.
31 bits: Total time spent with the CSP solver: 0.027s.
===============================
runtime: 70.352s,    gctime: 8.777s,     systime: 0.492s.
> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               (if 4 <= n then
                  (if 5 <= n then
                     (if 6 <= n then
                        (if 7 <= n then
                           (if 8 <= n then
                              (if 9 <= n then
                                 (if 10 <= n then
                                    (if 11 <= n then
                                       TIMEOUT
                                         (FEMPTY |+ ("n",Scalar n) |+
                                          ("Result",Scalar Result) |+
                                          ("s",Scalar 66) |+
                                          ("i",Scalar 12))
                                     else
                                       RESULT
                                         (FEMPTY |+ ("n",Scalar n) |+
                                          ("s",Scalar 55) |+
                                          ("i",Scalar 11) |+
                                          ("Result",Scalar 55)))
                                  else
                                    RESULT
                                      (FEMPTY |+ ("n",Scalar n) |+
                                       ("s",Scalar 45) |+ ("i",Scalar 10) |+
                                       ("Result",Scalar 45)))
                               else
                                 RESULT
                                   (FEMPTY |+ ("n",Scalar n) |+
                                    ("s",Scalar 36) |+ ("i",Scalar 9) |+
                                    ("Result",Scalar 36)))
                            else
                              RESULT
                                (FEMPTY |+ ("n",Scalar n) |+
                                 ("s",Scalar 28) |+ ("i",Scalar 8) |+
                                 ("Result",Scalar 28)))
                         else
                           RESULT
                             (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 21) |+
                              ("i",Scalar 7) |+ ("Result",Scalar 21)))
                      else
                        RESULT
                          (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 15) |+
                           ("i",Scalar 6) |+ ("Result",Scalar 15)))
                   else
                     RESULT
                       (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 10) |+
                        ("i",Scalar 5) |+ ("Result",Scalar 10)))
                else
                  RESULT
                    (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 6) |+
                     ("i",Scalar 4) |+ ("Result",Scalar 6)))
             else
               RESULT
                 (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 3) |+
                  ("i",Scalar 3) |+ ("Result",Scalar 3)))
          else
            RESULT
              (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 1) |+
               ("i",Scalar 2) |+ ("Result",Scalar 1)))
       else
         RESULT
           (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
            ("Result",Scalar 0)))`` : term
- - - - - 
*** Time taken: 70.544s

*)

(* with a number of steps which is too small -> 
   some of the paths are TIMEOUT *)
val name = "Sum";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 15;

> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               TIMEOUT
                 (FEMPTY |+ ("n",Scalar n) |+ ("Result",Scalar Result) |+
                  ("s",Scalar 3) |+ ("i",Scalar 3))
             else
               RESULT
                 (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 3) |+
                  ("i",Scalar 3) |+ ("Result",Scalar 3)))
          else
            RESULT
              (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 1) |+
               ("i",Scalar 2) |+ ("Result",Scalar 1)))
       else
         RESULT
           (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
            ("Result",Scalar 0)))`` : term



(* Sum of integers from P to N
   Contains a non linear expression, so the CSP solver has been used
   at the end of each path
 *)
val name = "SumFromPtoN";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 41;(* 10 times into the loop *)
(*
===============================
PROGRAM IS CORRECT
12 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

11 feasible paths have been explored.
0 path has been shown correct with the SMT solver
11 paths have been shown correct with the CSP solver
0 subterm has been solved with refute and METIS.
11 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.036s.

8 bits: Total time spent with the CSP solver: 0.541s.
16 bits: Total time spent with the CSP solver: 13.279s.
32 bits: PROBLEM: finds an error!!!

val tm = ``(n:int>=0) /\ (p:int>=0) /\ (p<= n) /\ ((1+p)<=n) /\ ((2+p)<=n)
           /\ ~((3+p)<=n) /\ 
           ~((3+3*p) =((n * (1 + n )) / 2 - ((~1 + p ) * p) / 2 ))``
val (res,solver)  =externalSolvers "nonLinear" tm;
> val res =
    |- n >= 0 /\ p >= 0 /\  p <= n /\ 1 + p <= n /\ 2 + p <= n /\ ~(3 + p <= n) /\
       ~(3 + 3 * p = n * (1 + n) / 2 - (~1 + p) * p / 2) =
       T : thm
Solution: 
(n,46341)
(p,46339)

There are some overflow problems for integer coded on more thant 16 bits
with Jsolver.

===============================
runtime: 352.310s,    gctime: 58.588s,     systime: 1.096s.
> val it =
    ``(if p + 1 <= n then
         (if p + 1 + 1 <= n then
            (if p + 1 + 1 + 1 <= n then
               (if p + 1 + 1 + 1 + 1 <= n then
                  (if p + 1 + 1 + 1 + 1 + 1 <= n then
                     (if p + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                        (if p + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                           (if p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                              (if
                                 p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n
                               then
                                 (if
                                    p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                    1 <= n
                                  then
                                    (if
                                       p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                       1 + 1 + 1 <= n
                                     then
                                       TIMEOUT
                                         (FEMPTY |+ ("p",Scalar p) |+
                                          ("n",Scalar n) |+
                                          ("Result",Scalar Result) |+
                                          ("s",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1 + 1))) |+
                                          ("i",
                                           Scalar
                                             (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                              1 + 1 + 1 + 1 + 1 + 1)))
                                     else
                                       RESULT
                                         (FEMPTY |+ ("p",Scalar p) |+
                                          ("n",Scalar n) |+
                                          ("s",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1))) |+
                                          ("i",
                                           Scalar
                                             (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                              1 + 1 + 1 + 1 + 1)) |+
                                          ("Result",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1)))))
                                  else
                                    RESULT
                                      (FEMPTY |+ ("p",Scalar p) |+
                                       ("n",Scalar n) |+
                                       ("s",
                                        Scalar
                                          (p + (p + 1) + (p + 1 + 1) +
                                           (p + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1 + 1))) |+
                                       ("i",
                                        Scalar
                                          (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                           1 + 1 + 1)) |+
                                       ("Result",
                                        Scalar
                                          (p + (p + 1) + (p + 1 + 1) +
                                           (p + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1 + 1)))))
                               else
                                 RESULT
                                   (FEMPTY |+ ("p",Scalar p) |+
                                    ("n",Scalar n) |+
                                    ("s",
                                     Scalar
                                       (p + (p + 1) + (p + 1 + 1) +
                                        (p + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                         1))) |+
                                    ("i",
                                     Scalar
                                       (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                        1)) |+
                                    ("Result",
                                     Scalar
                                       (p + (p + 1) + (p + 1 + 1) +
                                        (p + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                         1)))))
                            else
                              RESULT
                                (FEMPTY |+ ("p",Scalar p) |+
                                 ("n",Scalar n) |+
                                 ("s",
                                  Scalar
                                    (p + (p + 1) + (p + 1 + 1) +
                                     (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1 + 1))) |+
                                 ("i",
                                  Scalar
                                    (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) |+
                                 ("Result",
                                  Scalar
                                    (p + (p + 1) + (p + 1 + 1) +
                                     (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1 + 1)))))
                         else
                           RESULT
                             (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                              ("s",
                               Scalar
                                 (p + (p + 1) + (p + 1 + 1) +
                                  (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1 + 1))) |+
                              ("i",
                               Scalar (p + 1 + 1 + 1 + 1 + 1 + 1 + 1)) |+
                              ("Result",
                               Scalar
                                 (p + (p + 1) + (p + 1 + 1) +
                                  (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1 + 1)))))
                      else
                        RESULT
                          (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                           ("s",
                            Scalar
                              (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1 + 1))) |+
                           ("i",Scalar (p + 1 + 1 + 1 + 1 + 1 + 1)) |+
                           ("Result",
                            Scalar
                              (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1 + 1)))))
                   else
                     RESULT
                       (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                        ("s",
                         Scalar
                           (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                            (p + 1 + 1 + 1 + 1))) |+
                        ("i",Scalar (p + 1 + 1 + 1 + 1 + 1)) |+
                        ("Result",
                         Scalar
                           (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                            (p + 1 + 1 + 1 + 1)))))
                else
                  RESULT
                    (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                     ("s",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1 + 1)) |+
                     ("Result",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1)))))
             else
               RESULT
                 (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                  ("s",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                  ("i",Scalar (p + 1 + 1 + 1)) |+
                  ("Result",Scalar (p + (p + 1) + (p + 1 + 1)))))
          else
            RESULT
              (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
               ("s",Scalar (p + (p + 1))) |+ ("i",Scalar (p + 1 + 1)) |+
               ("Result",Scalar (p + (p + 1)))))
       else
         RESULT
           (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+ ("s",Scalar p) |+
            ("i",Scalar (p + 1)) |+ ("Result",Scalar p)))`` : term
*)



(* new example: contains an error
   the result must be  n*(n+1)/2 - (p-1)*p/2 
   and here the result is n*(n+1)/2 - p*(p+1)/2
*)
val name = "SumFromPtoNKO";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 41;

(*
===============================
11 ERRORs have been found
12 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

11 feasible paths have been explored.
All correct paths were verified in HOL.
0 subterm has been solved with refute and METIS.
11 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.064s.
Total time spent with the CSP solver: 0.052s.
===============================
runtime: 335.805s,    gctime: 55.315s,     systime: 1.816s.
> val it =
    ``(if p + 1 <= n then
         (if p + 1 + 1 <= n then
            (if p + 1 + 1 + 1 <= n then
               (if p + 1 + 1 + 1 + 1 <= n then
                  (if p + 1 + 1 + 1 + 1 + 1 <= n then
                     (if p + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                        (if p + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                           (if p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n then
                              (if
                                 p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 <= n
                               then
                                 (if
                                    p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                    1 <= n
                                  then
                                    (if
                                       p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                       1 + 1 + 1 <= n
                                     then
                                       TIMEOUT
                                         (FEMPTY |+ ("p",Scalar p) |+
                                          ("n",Scalar n) |+
                                          ("Result",Scalar Result) |+
                                          ("s",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1 + 1))) |+
                                          ("i",
                                           Scalar
                                             (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                              1 + 1 + 1 + 1 + 1 + 1)))
                                     else
                                       ERROR
                                         (FEMPTY |+ ("p",Scalar p) |+
                                          ("n",Scalar n) |+
                                          ("s",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1))) |+
                                          ("i",
                                           Scalar
                                             (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                              1 + 1 + 1 + 1 + 1)) |+
                                          ("Result",
                                           Scalar
                                             (p + (p + 1) + (p + 1 + 1) +
                                              (p + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1) +
                                              (p + 1 + 1 + 1 + 1 + 1 + 1 +
                                               1 + 1 + 1 + 1))) |+
                                          ("n",Scalar 11) |+
                                          ("p",Scalar 1)))
                                  else
                                    ERROR
                                      (FEMPTY |+ ("p",Scalar p) |+
                                       ("n",Scalar n) |+
                                       ("s",
                                        Scalar
                                          (p + (p + 1) + (p + 1 + 1) +
                                           (p + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1 + 1))) |+
                                       ("i",
                                        Scalar
                                          (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                           1 + 1 + 1)) |+
                                       ("Result",
                                        Scalar
                                          (p + (p + 1) + (p + 1 + 1) +
                                           (p + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1) +
                                           (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                            1 + 1))) |+ ("n",Scalar 10) |+
                                       ("p",Scalar 1)))
                               else
                                 ERROR
                                   (FEMPTY |+ ("p",Scalar p) |+
                                    ("n",Scalar n) |+
                                    ("s",
                                     Scalar
                                       (p + (p + 1) + (p + 1 + 1) +
                                        (p + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                         1))) |+
                                    ("i",
                                     Scalar
                                       (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                        1)) |+
                                    ("Result",
                                     Scalar
                                       (p + (p + 1) + (p + 1 + 1) +
                                        (p + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) +
                                        (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
                                         1))) |+ ("n",Scalar 9) |+
                                    ("p",Scalar 1)))
                            else
                              ERROR
                                (FEMPTY |+ ("p",Scalar p) |+
                                 ("n",Scalar n) |+
                                 ("s",
                                  Scalar
                                    (p + (p + 1) + (p + 1 + 1) +
                                     (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1 + 1))) |+
                                 ("i",
                                  Scalar
                                    (p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) |+
                                 ("Result",
                                  Scalar
                                    (p + (p + 1) + (p + 1 + 1) +
                                     (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1) +
                                     (p + 1 + 1 + 1 + 1 + 1 + 1 + 1))) |+
                                 ("n",Scalar 8) |+ ("p",Scalar 1)))
                         else
                           ERROR
                             (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                              ("s",
                               Scalar
                                 (p + (p + 1) + (p + 1 + 1) +
                                  (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1 + 1))) |+
                              ("i",
                               Scalar (p + 1 + 1 + 1 + 1 + 1 + 1 + 1)) |+
                              ("Result",
                               Scalar
                                 (p + (p + 1) + (p + 1 + 1) +
                                  (p + 1 + 1 + 1) + (p + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1) +
                                  (p + 1 + 1 + 1 + 1 + 1 + 1))) |+
                              ("n",Scalar 7) |+ ("p",Scalar 1)))
                      else
                        ERROR
                          (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                           ("s",
                            Scalar
                              (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1 + 1))) |+
                           ("i",Scalar (p + 1 + 1 + 1 + 1 + 1 + 1)) |+
                           ("Result",
                            Scalar
                              (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1) +
                               (p + 1 + 1 + 1 + 1 + 1))) |+
                           ("n",Scalar 6) |+ ("p",Scalar 1)))
                   else
                     ERROR
                       (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                        ("s",
                         Scalar
                           (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                            (p + 1 + 1 + 1 + 1))) |+
                        ("i",Scalar (p + 1 + 1 + 1 + 1 + 1)) |+
                        ("Result",
                         Scalar
                           (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                            (p + 1 + 1 + 1 + 1))) |+ ("n",Scalar 5) |+
                        ("p",Scalar 1)))
                else
                  ERROR
                    (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                     ("s",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1 + 1)) |+
                     ("Result",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1))) |+
                     ("n",Scalar 4) |+ ("p",Scalar 1)))
             else
               ERROR
                 (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                  ("s",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                  ("i",Scalar (p + 1 + 1 + 1)) |+
                  ("Result",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                  ("n",Scalar 3) |+ ("p",Scalar 1)))
          else
            ERROR
              (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
               ("s",Scalar (p + (p + 1))) |+ ("i",Scalar (p + 1 + 1)) |+
               ("Result",Scalar (p + (p + 1))) |+ ("n",Scalar 2) |+
               ("p",Scalar 1)))
       else
         ERROR
           (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+ ("s",Scalar p) |+
            ("i",Scalar (p + 1)) |+ ("Result",Scalar p) |+ ("n",Scalar 1) |+
            ("p",Scalar 1)))`` : term
*)


val n = "NestedLoop";
val spec = loadAndGetSpec n 
time (execSymbWithSMT n spec) 100 ;
(* corresponds to 4 pass through the loop *)

(*
===============================
PROGRAM IS CORRECT
426 conditions have been tested.
0 condition has been solved by EVAL.
395 conditions have been shown impossible.

5 feasible paths have been explored.
0 path has been shown correct with the SMT solver
3 paths have been shown correct with the CSP solver
0 subterm has been solved with refute and METIS.
5 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 2.32s.
Total time spent with the CSP solver: 0.016s.
===============================
runtime: 1977.484s,    gctime: 293.130s,     systime: 20.217s.
> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               (if 4 <= n then
                  (if 5 <= n then
                     (if 6 <= n then
                        (if 7 <= n then
                           (if 8 <= n then
                              (if 9 <= n then
                                 (if 10 <= n then
                                    (if 11 <= n then
                                       (if 12 <= n then
                                          (if 13 <= n then
                                             (if 14 <= n then
                                                (if 15 <= n then
                                                   (if 16 <= n then
                                                      (if 17 <= n then
                                                         (if 18 <= n then
                                                            (if 19 <= n then
                                                               (if
                                                                  20 <= n
                                                                then
                                                                  (if
                                                                     21 <= n
                                                                   then
                                                                     (if
                                                                        22 <=
                                                                        n
                                                                      then
                                                                        (if
                                                                           23 <=
                                                                           n
                                                                         then
                                                                           (if
                                                                              24 <=
                                                                              n
                                                                            then
                                                                              (if
                                                                                 25 <=
                                                                                 n
                                                                               then
                                                                                 (if
                                                                                    26 <=
                                                                                    n
                                                                                  then
                                                                                    (if
                                                                                       27 <=
                                                                                       n
                                                                                     then
                                                                                       (if
                                                                                          28 <=
                                                                                          n
                                                                                        then
                                                                                          (if
                                                                                             29 <=
                                                                                             n
                                                                                           then
                                                                                             (if
                                                                                                30 <=
                                                                                                n
                                                                                              then
                                                                                                (if
                                                                                                   31 <=
                                                                                                   n
                                                                                                 then
                                                                                                   TIMEOUT
                                                                                                     (FEMPTY |+
                                                                                                      ("n",
                                                                                                       Scalar
                                                                                                         n) |+
                                                                                                      ("Result",
                                                                                                       Scalar
                                                                                                         Result) |+
                                                                                                      ("i",
                                                                                                       Scalar
                                                                                                         1) |+
                                                                                                      ("j",
                                                                                                       Scalar
                                                                                                         31) |+
                                                                                                      ("s",
                                                                                                       Scalar
                                                                                                         31))
                                                                                                 else
                                                                                                   TIMEOUT
                                                                                                     (FEMPTY |+
                                                                                                      ("n",
                                                                                                       Scalar
                                                                                                         n) |+
                                                                                                      ("Result",
                                                                                                       Scalar
                                                                                                         Result) |+
                                                                                                      ("s",
                                                                                                       Scalar
                                                                                                         30) |+
                                                                                                      ("j",
                                                                                                       Scalar
                                                                                                         31) |+
                                                                                                      ("i",
                                                                                                       Scalar
                                                                                                         2)))
                                                                                              else
                                                                                                TIMEOUT
                                                                                                  (FEMPTY |+
                                                                                                   ("n",
                                                                                                    Scalar
                                                                                                      n) |+
                                                                                                   ("Result",
                                                                                                    Scalar
                                                                                                      Result) |+
                                                                                                   ("s",
                                                                                                    Scalar
                                                                                                      29) |+
                                                                                                   ("i",
                                                                                                    Scalar
                                                                                                      2) |+
                                                                                                   ("j",
                                                                                                    Scalar
                                                                                                      1)))
                                                                                           else
                                                                                             TIMEOUT
                                                                                               (FEMPTY |+
                                                                                                ("n",
                                                                                                 Scalar
                                                                                                   n) |+
                                                                                                ("Result",
                                                                                                 Scalar
                                                                                                   Result) |+
                                                                                                ("i",
                                                                                                 Scalar
                                                                                                   2) |+
                                                                                                ("s",
                                                                                                 Scalar
                                                                                                   29) |+
                                                                                                ("j",
                                                                                                 Scalar
                                                                                                   2)))
                                                                                        else
                                                                                          TIMEOUT
                                                                                            (FEMPTY |+
                                                                                             ("n",
                                                                                              Scalar
                                                                                                n) |+
                                                                                             ("Result",
                                                                                              Scalar
                                                                                                Result) |+
                                                                                             ("i",
                                                                                              Scalar
                                                                                                2) |+
                                                                                             ("s",
                                                                                              Scalar
                                                                                                29) |+
                                                                                             ("j",
                                                                                              Scalar
                                                                                                3)))
                                                                                     else
                                                                                       TIMEOUT
                                                                                         (FEMPTY |+
                                                                                          ("n",
                                                                                           Scalar
                                                                                             n) |+
                                                                                          ("Result",
                                                                                           Scalar
                                                                                             Result) |+
                                                                                          ("i",
                                                                                           Scalar
                                                                                             2) |+
                                                                                          ("s",
                                                                                           Scalar
                                                                                             29) |+
                                                                                          ("j",
                                                                                           Scalar
                                                                                             4)))
                                                                                  else
                                                                                    TIMEOUT
                                                                                      (FEMPTY |+
                                                                                       ("n",
                                                                                        Scalar
                                                                                          n) |+
                                                                                       ("Result",
                                                                                        Scalar
                                                                                          Result) |+
                                                                                       ("i",
                                                                                        Scalar
                                                                                          2) |+
                                                                                       ("s",
                                                                                        Scalar
                                                                                          29) |+
                                                                                       ("j",
                                                                                        Scalar
                                                                                          5)))
                                                                               else
                                                                                 TIMEOUT
                                                                                   (FEMPTY |+
                                                                                    ("n",
                                                                                     Scalar
                                                                                       n) |+
                                                                                    ("Result",
                                                                                     Scalar
                                                                                       Result) |+
                                                                                    ("i",
                                                                                     Scalar
                                                                                       2) |+
                                                                                    ("s",
                                                                                     Scalar
                                                                                       29) |+
                                                                                    ("j",
                                                                                     Scalar
                                                                                       6)))
                                                                            else
                                                                              TIMEOUT
                                                                                (FEMPTY |+
                                                                                 ("n",
                                                                                  Scalar
                                                                                    n) |+
                                                                                 ("Result",
                                                                                  Scalar
                                                                                    Result) |+
                                                                                 ("i",
                                                                                  Scalar
                                                                                    2) |+
                                                                                 ("s",
                                                                                  Scalar
                                                                                    29) |+
                                                                                 ("j",
                                                                                  Scalar
                                                                                    7)))
                                                                         else
                                                                           TIMEOUT
                                                                             (FEMPTY |+
                                                                              ("n",
                                                                               Scalar
                                                                                 n) |+
                                                                              ("Result",
                                                                               Scalar
                                                                                 Result) |+
                                                                              ("i",
                                                                               Scalar
                                                                                 2) |+
                                                                              ("s",
                                                                               Scalar
                                                                                 29) |+
                                                                              ("j",
                                                                               Scalar
                                                                                 8)))
                                                                      else
                                                                        TIMEOUT
                                                                          (FEMPTY |+
                                                                           ("n",
                                                                            Scalar
                                                                              n) |+
                                                                           ("Result",
                                                                            Scalar
                                                                              Result) |+
                                                                           ("i",
                                                                            Scalar
                                                                              2) |+
                                                                           ("s",
                                                                            Scalar
                                                                              29) |+
                                                                           ("j",
                                                                            Scalar
                                                                              9)))
                                                                   else
                                                                     TIMEOUT
                                                                       (FEMPTY |+
                                                                        ("n",
                                                                         Scalar
                                                                           n) |+
                                                                        ("Result",
                                                                         Scalar
                                                                           Result) |+
                                                                        ("i",
                                                                         Scalar
                                                                           2) |+
                                                                        ("s",
                                                                         Scalar
                                                                           29) |+
                                                                        ("j",
                                                                         Scalar
                                                                           10)))
                                                                else
                                                                  TIMEOUT
                                                                    (FEMPTY |+
                                                                     ("n",
                                                                      Scalar
                                                                        n) |+
                                                                     ("Result",
                                                                      Scalar
                                                                        Result) |+
                                                                     ("i",
                                                                      Scalar
                                                                        2) |+
                                                                     ("s",
                                                                      Scalar
                                                                        29) |+
                                                                     ("j",
                                                                      Scalar
                                                                        11)))
                                                             else
                                                               TIMEOUT
                                                                 (FEMPTY |+
                                                                  ("n",
                                                                   Scalar
                                                                     n) |+
                                                                  ("Result",
                                                                   Scalar
                                                                     Result) |+
                                                                  ("i",
                                                                   Scalar
                                                                     2) |+
                                                                  ("s",
                                                                   Scalar
                                                                     29) |+
                                                                  ("j",
                                                                   Scalar
                                                                     12)))
                                                          else
                                                            TIMEOUT
                                                              (FEMPTY |+
                                                               ("n",
                                                                Scalar n) |+
                                                               ("Result",
                                                                Scalar
                                                                  Result) |+
                                                               ("i",
                                                                Scalar 2) |+
                                                               ("s",
                                                                Scalar
                                                                  29) |+
                                                               ("j",
                                                                Scalar 13)))
                                                       else
                                                         TIMEOUT
                                                           (FEMPTY |+
                                                            ("n",
                                                             Scalar n) |+
                                                            ("Result",
                                                             Scalar
                                                               Result) |+
                                                            ("i",
                                                             Scalar 2) |+
                                                            ("s",
                                                             Scalar 29) |+
                                                            ("j",
                                                             Scalar 14)))
                                                    else
                                                      TIMEOUT
                                                        (FEMPTY |+
                                                         ("n",Scalar n) |+
                                                         ("Result",
                                                          Scalar Result) |+
                                                         ("i",Scalar 2) |+
                                                         ("s",Scalar 29) |+
                                                         ("j",Scalar 15)))
                                                 else
                                                   TIMEOUT
                                                     (FEMPTY |+
                                                      ("n",Scalar n) |+
                                                      ("Result",
                                                       Scalar Result) |+
                                                      ("s",Scalar 28) |+
                                                      ("i",Scalar 3) |+
                                                      ("j",Scalar 1)))
                                              else
                                                TIMEOUT
                                                  (FEMPTY |+
                                                   ("n",Scalar n) |+
                                                   ("Result",
                                                    Scalar Result) |+
                                                   ("i",Scalar 3) |+
                                                   ("s",Scalar 28) |+
                                                   ("j",Scalar 3)))
                                           else
                                             TIMEOUT
                                               (FEMPTY |+ ("n",Scalar n) |+
                                                ("Result",Scalar Result) |+
                                                ("i",Scalar 3) |+
                                                ("s",Scalar 28) |+
                                                ("j",Scalar 5)))
                                        else
                                          TIMEOUT
                                            (FEMPTY |+ ("n",Scalar n) |+
                                             ("Result",Scalar Result) |+
                                             ("i",Scalar 3) |+
                                             ("s",Scalar 28) |+
                                             ("j",Scalar 7)))
                                     else
                                       TIMEOUT
                                         (FEMPTY |+ ("n",Scalar n) |+
                                          ("Result",Scalar Result) |+
                                          ("i",Scalar 3) |+
                                          ("s",Scalar 28) |+
                                          ("j",Scalar 9)))
                                  else
                                    TIMEOUT
                                      (FEMPTY |+ ("n",Scalar n) |+
                                       ("Result",Scalar Result) |+
                                       ("s",Scalar 27) |+ ("i",Scalar 4) |+
                                       ("j",Scalar 1)))
                               else
                                 TIMEOUT
                                   (FEMPTY |+ ("n",Scalar n) |+
                                    ("Result",Scalar Result) |+
                                    ("i",Scalar 4) |+ ("j",Scalar 3) |+
                                    ("s",Scalar 27)))
                            else
                              TIMEOUT
                                (FEMPTY |+ ("n",Scalar n) |+
                                 ("Result",Scalar Result) |+
                                 ("i",Scalar 4) |+ ("j",Scalar 6) |+
                                 ("s",Scalar 27)))
                         else
                           TIMEOUT
                             (FEMPTY |+ ("n",Scalar n) |+
                              ("Result",Scalar Result) |+ ("i",Scalar 5) |+
                              ("s",Scalar 25) |+ ("j",Scalar 2)))
                      else
                        TIMEOUT
                          (FEMPTY |+ ("n",Scalar n) |+
                           ("Result",Scalar Result) |+ ("s",Scalar 25) |+
                           ("j",Scalar 6) |+ ("i",Scalar 6)))
                   else
                     RESULT
                       (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 16) |+
                        ("j",Scalar 5) |+ ("i",Scalar 5) |+
                        ("Result",Scalar 16)))
                else
                  RESULT
                    (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 9) |+
                     ("j",Scalar 4) |+ ("i",Scalar 4) |+
                     ("Result",Scalar 9)))
             else
               RESULT
                 (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 4) |+
                  ("j",Scalar 3) |+ ("i",Scalar 3) |+ ("Result",Scalar 4)))
          else
            RESULT
              (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 1) |+
               ("j",Scalar 2) |+ ("i",Scalar 2) |+ ("Result",Scalar 1)))
       else
         RESULT
           (FEMPTY |+ ("n",Scalar n) |+ ("j",Scalar j) |+ ("s",Scalar 0) |+
            ("i",Scalar 1) |+ ("Result",Scalar 0)))`` : term


*)

val n = "NestedLoop";
val spec = loadAndGetSpec n 
time (execSymbWithSMT n spec) 25 ;

(*
Not linear but proved with HOL

===============================
PROGRAM IS CORRECT
18 conditions have been tested.
0 condition has been solved by EVAL.
12 conditions have been shown impossible.

2 feasible paths have been explored.
All correct paths were verified in HOL.
0 subterm has been solved with refute and METIS.
2 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.1s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 14.553s,    gctime: 2.052s,     systime: 0.424s.
> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               (if 4 <= n then
                  (if 5 <= n then
                     (if 6 <= n then
                        TIMEOUT
                          (FEMPTY |+ ("n",Scalar n) |+
                           ("Result",Scalar Result) |+ ("i",Scalar 1) |+
                           ("j",Scalar 6) |+ ("s",Scalar 6))
                      else
                        TIMEOUT
                          (FEMPTY |+ ("n",Scalar n) |+
                           ("Result",Scalar Result) |+ ("s",Scalar 5) |+
                           ("j",Scalar 6) |+ ("i",Scalar 2)))
                   else
                     TIMEOUT
                       (FEMPTY |+ ("n",Scalar n) |+
                        ("Result",Scalar Result) |+ ("s",Scalar 4) |+
                        ("i",Scalar 2) |+ ("j",Scalar 1)))
                else
                  TIMEOUT
                    (FEMPTY |+ ("n",Scalar n) |+ ("Result",Scalar Result) |+
                     ("i",Scalar 2) |+ ("s",Scalar 4) |+ ("j",Scalar 2)))
             else
               TIMEOUT
                 (FEMPTY |+ ("n",Scalar n) |+ ("Result",Scalar Result) |+
                  ("s",Scalar 4) |+ ("j",Scalar 3) |+ ("i",Scalar 3)))
          else
            RESULT
              (FEMPTY |+ ("n",Scalar n) |+ ("s",Scalar 1) |+
               ("j",Scalar 2) |+ ("i",Scalar 2) |+ ("Result",Scalar 1)))
       else
         RESULT
           (FEMPTY |+ ("n",Scalar n) |+ ("j",Scalar j) |+ ("s",Scalar 0) |+
            ("i",Scalar 1) |+ ("Result",Scalar 0)))`` : term
*)



(* =================================== *)
(* Program with arrays                 *)
(* =================================== *)


(* search of an element in an array *) 
val name = "Search";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 30; 
(*
===============================
PROGRAM IS CORRECT
31 conditions have been tested.
21 conditions have been solved by EVAL.
11 conditions have been shown impossible.

11 feasible paths have been explored.
Total time spent with the SMT solver: 0.06s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 35.466s,    gctime: 5.388s,     systime: 0.404s.
> val it =
    ``(if a_0 = x then
         RESULT
           (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
            ("a",
             Array
               (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                (9,a_9))) |+ ("left",Scalar 0) |+ ("result",Scalar 0) |+
            ("Result",Scalar 0))
       else
         (if a_1 = x then
            RESULT
              (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
               ("a",
                Array
                  (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                   (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                   (9,a_9))) |+ ("left",Scalar 1) |+ ("result",Scalar 1) |+
               ("Result",Scalar 1))
          else
            (if a_2 = x then
               RESULT
                 (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                  ("a",
                   Array
                     (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                      (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                      (9,a_9))) |+ ("left",Scalar 2) |+
                  ("result",Scalar 2) |+ ("Result",Scalar 2))
             else
               (if a_3 = x then
                  RESULT
                    (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                     ("a",
                      Array
                        (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                         (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                         (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                     ("left",Scalar 3) |+ ("result",Scalar 3) |+
                     ("Result",Scalar 3))
                else
                  (if a_4 = x then
                     RESULT
                       (FEMPTY |+ ("x",Scalar x) |+ ("aLength",Scalar 10) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("left",Scalar 4) |+ ("result",Scalar 4) |+
                        ("Result",Scalar 4))
                   else
                     (if a_5 = x then
                        RESULT
                          (FEMPTY |+ ("x",Scalar x) |+
                           ("aLength",Scalar 10) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("left",Scalar 5) |+ ("result",Scalar 5) |+
                           ("Result",Scalar 5))
                      else
                        (if a_6 = x then
                           RESULT
                             (FEMPTY |+ ("x",Scalar x) |+
                              ("aLength",Scalar 10) |+
                              ("a",
                               Array
                                 (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                  (3,a_3) |+ (4,a_4) |+ (5,a_5) |+
                                  (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                                  (9,a_9))) |+ ("left",Scalar 6) |+
                              ("result",Scalar 6) |+ ("Result",Scalar 6))
                         else
                           (if a_7 = x then
                              RESULT
                                (FEMPTY |+ ("x",Scalar x) |+
                                 ("aLength",Scalar 10) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("left",Scalar 7) |+ ("result",Scalar 7) |+
                                 ("Result",Scalar 7))
                            else
                              (if a_8 = x then
                                 RESULT
                                   (FEMPTY |+ ("x",Scalar x) |+
                                    ("aLength",Scalar 10) |+
                                    ("a",
                                     Array
                                       (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                        (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                        (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                        (8,a_8) |+ (9,a_9))) |+
                                    ("left",Scalar 8) |+
                                    ("result",Scalar 8) |+
                                    ("Result",Scalar 8))
                               else
                                 (if a_9 = x then
                                    RESULT
                                      (FEMPTY |+ ("x",Scalar x) |+
                                       ("aLength",Scalar 10) |+
                                       ("a",
                                        Array
                                          (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                           (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                           (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                           (8,a_8) |+ (9,a_9))) |+
                                       ("left",Scalar 9) |+
                                       ("result",Scalar 9) |+
                                       ("Result",Scalar 9))
                                  else
                                    RESULT
                                      (FEMPTY |+ ("x",Scalar x) |+
                                       ("aLength",Scalar 10) |+
                                       ("a",
                                        Array
                                          (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                           (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                           (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                           (8,a_8) |+ (9,a_9))) |+
                                       ("result",Scalar ~1) |+
                                       ("left",Scalar 10) |+
                                       ("Result",Scalar ~1))))))))))))`` : term
- - - - - 
*** Time taken: 14.661s
*)

(* Binary search of an element in an array *)
val name = "Bsearch";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 30;


(*
===============================
PROGRAM IS CORRECT
51 conditions have been tested.
31 conditions have been solved by EVAL.
21 conditions have been shown impossible.

21 feasible paths have been explored.
All correct paths were verified in HOL.
49 subterms have been solved with refute and METIS.
71 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.108s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 537.586s,    gctime: 87.217s,     systime: 2.428s.
(* using results that have been cached with COOPER *)
runtime: 122.428s,    gctime: 18.893s,     systime: 1.092s.

> val it =
    ``(if a_4 = x then
         RESULT
           (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
            ("a",
             Array
               (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                (9,a_9))) |+ ("left",Scalar 0) |+ ("right",Scalar 9) |+
            ("mid",Scalar 4) |+ ("result",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if x < a_4 then
            (if a_1 = x then
               RESULT
                 (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                  ("a",
                   Array
                     (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                      (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                      (9,a_9))) |+ ("left",Scalar 0) |+
                  ("right",Scalar 3) |+ ("mid",Scalar 1) |+
                  ("result",Scalar 1) |+ ("Result",Scalar 1))
             else
               (if x < a_1 then
                  (if a_0 = x then
                     RESULT
                       (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("left",Scalar 0) |+ ("right",Scalar 0) |+
                        ("mid",Scalar 0) |+ ("result",Scalar 0) |+
                        ("Result",Scalar 0))
                   else
                     (if x < a_0 then
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 0) |+
                           ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
                           ("Result",Scalar ~1))
                      else
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("right",Scalar 0) |+
                           ("mid",Scalar 0) |+ ("left",Scalar 1) |+
                           ("Result",Scalar ~1))))
                else
                  (if a_2 = x then
                     RESULT
                       (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("right",Scalar 3) |+ ("left",Scalar 2) |+
                        ("mid",Scalar 2) |+ ("result",Scalar 2) |+
                        ("Result",Scalar 2))
                   else
                     (if x < a_2 then
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 2) |+
                           ("mid",Scalar 2) |+ ("right",Scalar 1) |+
                           ("Result",Scalar ~1))
                      else
                        (if a_3 = x then
                           RESULT
                             (FEMPTY |+ ("aLength",Scalar 10) |+
                              ("x",Scalar x) |+
                              ("a",
                               Array
                                 (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                  (3,a_3) |+ (4,a_4) |+ (5,a_5) |+
                                  (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                                  (9,a_9))) |+ ("right",Scalar 3) |+
                              ("left",Scalar 3) |+ ("mid",Scalar 3) |+
                              ("result",Scalar 3) |+ ("Result",Scalar 3))
                         else
                           (if x < a_3 then
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("left",Scalar 3) |+ ("mid",Scalar 3) |+
                                 ("right",Scalar 2) |+ ("Result",Scalar ~1))
                            else
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("right",Scalar 3) |+ ("mid",Scalar 3) |+
                                 ("left",Scalar 4) |+
                                 ("Result",Scalar ~1))))))))
          else
            (if a_7 = x then
               RESULT
                 (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                  ("a",
                   Array
                     (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                      (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                      (9,a_9))) |+ ("right",Scalar 9) |+
                  ("left",Scalar 5) |+ ("mid",Scalar 7) |+
                  ("result",Scalar 7) |+ ("Result",Scalar 7))
             else
               (if x < a_7 then
                  (if a_5 = x then
                     RESULT
                       (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("left",Scalar 5) |+ ("right",Scalar 6) |+
                        ("mid",Scalar 5) |+ ("result",Scalar 5) |+
                        ("Result",Scalar 5))
                   else
                     (if x < a_5 then
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 5) |+
                           ("mid",Scalar 5) |+ ("right",Scalar 4) |+
                           ("Result",Scalar ~1))
                      else
                        (if a_6 = x then
                           RESULT
                             (FEMPTY |+ ("aLength",Scalar 10) |+
                              ("x",Scalar x) |+
                              ("a",
                               Array
                                 (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                  (3,a_3) |+ (4,a_4) |+ (5,a_5) |+
                                  (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                                  (9,a_9))) |+ ("right",Scalar 6) |+
                              ("left",Scalar 6) |+ ("mid",Scalar 6) |+
                              ("result",Scalar 6) |+ ("Result",Scalar 6))
                         else
                           (if x < a_6 then
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("left",Scalar 6) |+ ("mid",Scalar 6) |+
                                 ("right",Scalar 5) |+ ("Result",Scalar ~1))
                            else
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("right",Scalar 6) |+ ("mid",Scalar 6) |+
                                 ("left",Scalar 7) |+
                                 ("Result",Scalar ~1))))))
                else
                  (if a_8 = x then
                     RESULT
                       (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("right",Scalar 9) |+ ("left",Scalar 8) |+
                        ("mid",Scalar 8) |+ ("result",Scalar 8) |+
                        ("Result",Scalar 8))
                   else
                     (if x < a_8 then
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 8) |+
                           ("mid",Scalar 8) |+ ("right",Scalar 7) |+
                           ("Result",Scalar ~1))
                      else
                        (if a_9 = x then
                           RESULT
                             (FEMPTY |+ ("aLength",Scalar 10) |+
                              ("x",Scalar x) |+
                              ("a",
                               Array
                                 (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                                  (3,a_3) |+ (4,a_4) |+ (5,a_5) |+
                                  (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                                  (9,a_9))) |+ ("right",Scalar 9) |+
                              ("left",Scalar 9) |+ ("mid",Scalar 9) |+
                              ("result",Scalar 9) |+ ("Result",Scalar 9))
                         else
                           (if x < a_9 then
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("left",Scalar 9) |+ ("mid",Scalar 9) |+
                                 ("right",Scalar 8) |+ ("Result",Scalar ~1))
                            else
                              RESULT
                                (FEMPTY |+ ("aLength",Scalar 10) |+
                                 ("x",Scalar x) |+
                                 ("a",
                                  Array
                                    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+
                                     (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
                                     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+
                                     (8,a_8) |+ (9,a_9))) |+
                                 ("result",Scalar ~1) |+
                                 ("right",Scalar 9) |+ ("mid",Scalar 9) |+
                                 ("left",Scalar 10) |+
                                 ("Result",Scalar ~1))))))))))`` : term
- - - - - 
*** Time taken: 40.811s
*)

(* Bsearch with a number of steps to small *)
time (execSymbWithSMT name spec) 10;
(*
===============================
TIMEOUT
1 condition has been tested.
1 condition has been solved by EVAL.
0 condition has been shown impossible.

0 feasible path has been explored.
All correct paths were verified in HOL.
0 subterm has been solved with refute and METIS.
0 subterm has been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.0s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 7.668s,    gctime: 1.340s,     systime: 0.008s.
> val it =
    ``TIMEOUT
        (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
         ("Result",Scalar Result) |+
         ("a",
          Array
            (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
             (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
             (9,a_9))) |+ ("result",Scalar ~1) |+ ("mid",Scalar 0) |+
         ("left",Scalar 0) |+ ("right",Scalar 9))`` : term
- - - - - 
*)


(* Binary search with an error 
when the searched value is greater than the middle, modify the 
rigth bound instead of the left bound
*)
val name = "BsearchKO";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 20;

(*
===============================
2 ERRORs have been found
25 conditions have been tested.
13 conditions have been solved by EVAL.
13 conditions have been shown impossible.

7 feasible paths have been explored.
All correct paths were verified in HOL.
15 subterms have been solved with refute and METIS.
28 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.088s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 276.225s,    gctime: 41.919s,     systime: 1.408s.
> val it =
    ``(if a_4 = x then
         RESULT
           (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
            ("a",
             Array
               (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                (9,a_9))) |+ ("left",Scalar 0) |+ ("right",Scalar 9) |+
            ("mid",Scalar 4) |+ ("result",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if x < a_4 then
            (if a_1 = x then
               RESULT
                 (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                  ("a",
                   Array
                     (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                      (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                      (9,a_9))) |+ ("left",Scalar 0) |+
                  ("right",Scalar 3) |+ ("mid",Scalar 1) |+
                  ("result",Scalar 1) |+ ("Result",Scalar 1))
             else
               (if x < a_1 then
                  (if a_0 = x then
                     RESULT
                       (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                        ("a",
                         Array
                           (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                            (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                            (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                        ("left",Scalar 0) |+ ("right",Scalar 0) |+
                        ("mid",Scalar 0) |+ ("result",Scalar 0) |+
                        ("Result",Scalar 0))
                   else
                     (if x < a_0 then
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 0) |+
                           ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
                           ("Result",Scalar ~1))
                      else
                        RESULT
                          (FEMPTY |+ ("aLength",Scalar 10) |+
                           ("x",Scalar x) |+
                           ("a",
                            Array
                              (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                               (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                               (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                           ("result",Scalar ~1) |+ ("left",Scalar 0) |+
                           ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
                           ("Result",Scalar ~1))))
                else
                  ERROR
                    (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
                     ("a",
                      Array
                        (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+
                         (3,a_3) |+ (4,a_4) |+ (5,a_5) |+ (6,a_6) |+
                         (7,a_7) |+ (8,a_8) |+ (9,a_9))) |+
                     ("result",Scalar ~1) |+ ("left",Scalar 0) |+
                     ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
                     ("Result",Scalar ~1) |+ ("a_9",Scalar 2) |+
                     ("x",Scalar 1) |+ ("a_8",Scalar 2) |+
                     ("a_7",Scalar 2) |+ ("a_6",Scalar 2) |+
                     ("a_5",Scalar 2) |+ ("a_4",Scalar 2) |+
                     ("a_3",Scalar 1) |+ ("a_2",Scalar 0) |+
                     ("a_1",Scalar 0) |+ ("a_0",Scalar 0))))
          else
            ERROR
              (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
               ("a",
                Array
                  (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                   (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                   (9,a_9))) |+ ("result",Scalar ~1) |+ ("left",Scalar 0) |+
               ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
               ("Result",Scalar ~1) |+ ("a_9",Scalar 2) |+ ("x",Scalar 1) |+
               ("a_8",Scalar 2) |+ ("a_7",Scalar 1) |+ ("a_6",Scalar 0) |+
               ("a_5",Scalar 0) |+ ("a_4",Scalar 0) |+ ("a_3",Scalar 0) |+
               ("a_2",Scalar 0) |+ ("a_1",Scalar 0) |+ ("a_0",Scalar 0))))`` :
  term
- - - - - 
*)

(* Partition procedure of the quicksort algorithm *)
val name = "Partition";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 10;

(* TIMEOUT  *)

(* using an array of length 5 and 10 steps *)

val n = 20;

val (_,args) = strip_comb spec;
val (pre,prog,post) = (el 1 args, el 2 args, el 3 args);
val (listVars,s) = makeState prog;

val s =
    ``FEMPTY |++
      [("aLength",Scalar 5); ("k",Scalar k); ("pivot",Scalar pivot);
       ("tmp",Scalar tmp); ("j",Scalar j); ("tmp2",Scalar tmp2);
       ("i",Scalar i); ("Result",Scalar Result); ("p",Scalar p);
       ("a",
        Array
          (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) 
          |+ (3,a_3) |+ (4,a_4)))]`` 


val evalP = evalPre pre s

resetAll(); (* reset global variables *)
setVars(listVars);

val res = 
        time (execSymb name 
                 evalP 
                 (``[^prog]``,s,s,n) 
                 post)
                 ``T``
printStatistics();
resetProgramVars(); (* reset the list of variable used to existentially quantify terms *) 

(* too slow for solving the final term *)

val final = 
  ``((i < j /\ 0 <= i /\ i < 5 /\ 0 <= j /\ j < 5) /\
   (((i + 1 <= j /\
      ~(if Num (i + 1) = 4 then
          (if Num i = 4 then
             a_4 < a_4
           else
             (if Num i = 3 then
                a_4 < a_3
              else
                (if Num i = 2 then
                   a_4 < a_2
                 else
                   (if Num i = 1 then
                      a_4 < a_1
                    else
                      (if Num i = 0 then
                         a_4 < a_0
                       else
                         a_4 < FEMPTY ' (Num i))))))
        else
          (if Num (i + 1) = 3 then
             (if Num i = 4 then
                a_3 < a_4
              else
                (if Num i = 3 then
                   a_3 < a_3
                 else
                   (if Num i = 2 then
                      a_3 < a_2
                    else
                      (if Num i = 1 then
                         a_3 < a_1
                       else
                         (if Num i = 0 then
                            a_3 < a_0
                          else
                            a_3 < FEMPTY ' (Num i))))))
           else
             (if Num (i + 1) = 2 then
                (if Num i = 4 then
                   a_2 < a_4
                 else
                   (if Num i = 3 then
                      a_2 < a_3
                    else
                      (if Num i = 2 then
                         a_2 < a_2
                       else
                         (if Num i = 1 then
                            a_2 < a_1
                          else
                            (if Num i = 0 then
                               a_2 < a_0
                             else
                               a_2 < FEMPTY ' (Num i))))))
              else
                (if Num (i + 1) = 1 then
                   (if Num i = 4 then
                      a_1 < a_4
                    else
                      (if Num i = 3 then
                         a_1 < a_3
                       else
                         (if Num i = 2 then
                            a_1 < a_2
                          else
                            (if Num i = 1 then
                               a_1 < a_1
                             else
                               (if Num i = 0 then
                                  a_1 < a_0
                                else
                                  a_1 < FEMPTY ' (Num i))))))
                 else
                   (if Num (i + 1) = 0 then
                      (if Num i = 4 then
                         a_0 < a_4
                       else
                         (if Num i = 3 then
                            a_0 < a_3
                          else
                            (if Num i = 2 then
                               a_0 < a_2
                             else
                               (if Num i = 1 then
                                  a_0 < a_1
                                else
                                  (if Num i = 0 then
                                     a_0 < a_0
                                   else
                                     a_0 < FEMPTY ' (Num i))))))
                    else
                      (if Num i = 4 then
                         FEMPTY ' (Num (i + 1)) < a_4
                       else
                         (if Num i = 3 then
                            FEMPTY ' (Num (i + 1)) < a_3
                          else
                            (if Num i = 2 then
                               FEMPTY ' (Num (i + 1)) < a_2
                             else
                               (if Num i = 1 then
                                  FEMPTY ' (Num (i + 1)) < a_1
                                else
                                  (if Num i = 0 then
                                     FEMPTY ' (Num (i + 1)) < a_0
                                   else
                                     FEMPTY ' (Num (i + 1)) <
                                     FEMPTY ' (Num i)))))))))))) /\
     i + 1 + 1 <= j) /\
    ~(if Num (i + 1 + 1) = 4 then
        (if Num i = 4 then
           a_4 < a_4
         else
           (if Num i = 3 then
              a_4 < a_3
            else
              (if Num i = 2 then
                 a_4 < a_2
               else
                 (if Num i = 1 then
                    a_4 < a_1
                  else
                    (if Num i = 0 then
                       a_4 < a_0
                     else
                       a_4 < FEMPTY ' (Num i))))))
      else
        (if Num (i + 1 + 1) = 3 then
           (if Num i = 4 then
              a_3 < a_4
            else
              (if Num i = 3 then
                 a_3 < a_3
               else
                 (if Num i = 2 then
                    a_3 < a_2
                  else
                    (if Num i = 1 then
                       a_3 < a_1
                     else
                       (if Num i = 0 then
                          a_3 < a_0
                        else
                          a_3 < FEMPTY ' (Num i))))))
         else
           (if Num (i + 1 + 1) = 2 then
              (if Num i = 4 then
                 a_2 < a_4
               else
                 (if Num i = 3 then
                    a_2 < a_3
                  else
                    (if Num i = 2 then
                       a_2 < a_2
                     else
                       (if Num i = 1 then
                          a_2 < a_1
                        else
                          (if Num i = 0 then
                             a_2 < a_0
                           else
                             a_2 < FEMPTY ' (Num i))))))
            else
              (if Num (i + 1 + 1) = 1 then
                 (if Num i = 4 then
                    a_1 < a_4
                  else
                    (if Num i = 3 then
                       a_1 < a_3
                     else
                       (if Num i = 2 then
                          a_1 < a_2
                        else
                          (if Num i = 1 then
                             a_1 < a_1
                           else
                             (if Num i = 0 then
                                a_1 < a_0
                              else
                                a_1 < FEMPTY ' (Num i))))))
               else
                 (if Num (i + 1 + 1) = 0 then
                    (if Num i = 4 then
                       a_0 < a_4
                     else
                       (if Num i = 3 then
                          a_0 < a_3
                        else
                          (if Num i = 2 then
                             a_0 < a_2
                           else
                             (if Num i = 1 then
                                a_0 < a_1
                              else
                                (if Num i = 0 then
                                   a_0 < a_0
                                 else
                                   a_0 < FEMPTY ' (Num i))))))
                  else
                    (if Num i = 4 then
                       FEMPTY ' (Num (i + 1 + 1)) < a_4
                     else
                       (if Num i = 3 then
                          FEMPTY ' (Num (i + 1 + 1)) < a_3
                        else
                          (if Num i = 2 then
                             FEMPTY ' (Num (i + 1 + 1)) < a_2
                           else
                             (if Num i = 1 then
                                FEMPTY ' (Num (i + 1 + 1)) < a_1
                              else
                                (if Num i = 0 then
                                   FEMPTY ' (Num (i + 1 + 1)) < a_0
                                 else
                                   FEMPTY ' (Num (i + 1 + 1)) <
                                   FEMPTY ' (Num i)))))))))))) /\
   ~(i + 1 + 1 + 1 <= j)) /\
  ~ !i'.
     i' < Num i ==>
     (if i' = Num i then
        (if Num i = 4 then
           (if Num i = 4 then
              a_4 < a_4
            else
              (if Num i = 3 then
                 a_4 < a_3
               else
                 (if Num i = 2 then
                    a_4 < a_2
                  else
                    (if Num i = 1 then
                       a_4 < a_1
                     else
                       (if Num i = 0 then
                          a_4 < a_0
                        else
                          a_4 < FEMPTY ' (Num i))))))
         else
           (if Num i = 3 then
              (if Num i = 4 then
                 a_3 < a_4
               else
                 (if Num i = 3 then
                    a_3 < a_3
                  else
                    (if Num i = 2 then
                       a_3 < a_2
                     else
                       (if Num i = 1 then
                          a_3 < a_1
                        else
                          (if Num i = 0 then
                             a_3 < a_0
                           else
                             a_3 < FEMPTY ' (Num i))))))
            else
              (if Num i = 2 then
                 (if Num i = 4 then
                    a_2 < a_4
                  else
                    (if Num i = 3 then
                       a_2 < a_3
                     else
                       (if Num i = 2 then
                          a_2 < a_2
                        else
                          (if Num i = 1 then
                             a_2 < a_1
                           else
                             (if Num i = 0 then
                                a_2 < a_0
                              else
                                a_2 < FEMPTY ' (Num i))))))
               else
                 (if Num i = 1 then
                    (if Num i = 4 then
                       a_1 < a_4
                     else
                       (if Num i = 3 then
                          a_1 < a_3
                        else
                          (if Num i = 2 then
                             a_1 < a_2
                           else
                             (if Num i = 1 then
                                a_1 < a_1
                              else
                                (if Num i = 0 then
                                   a_1 < a_0
                                 else
                                   a_1 < FEMPTY ' (Num i))))))
                  else
                    (if Num i = 0 then
                       (if Num i = 4 then
                          a_0 < a_4
                        else
                          (if Num i = 3 then
                             a_0 < a_3
                           else
                             (if Num i = 2 then
                                a_0 < a_2
                              else
                                (if Num i = 1 then
                                   a_0 < a_1
                                 else
                                   (if Num i = 0 then
                                      a_0 < a_0
                                    else
                                      a_0 < FEMPTY ' (Num i))))))
                     else
                       (if Num i = 4 then
                          FEMPTY ' (Num i) < a_4
                        else
                          (if Num i = 3 then
                             FEMPTY ' (Num i) < a_3
                           else
                             (if Num i = 2 then
                                FEMPTY ' (Num i) < a_2
                              else
                                (if Num i = 1 then
                                   FEMPTY ' (Num i) < a_1
                                 else
                                   (if Num i = 0 then
                                      FEMPTY ' (Num i) < a_0
                                    else
                                      FEMPTY ' (Num i) <
                                      FEMPTY ' (Num i)))))))))))
      else
        (if Num i = 4 then
           (if 4 = Num i then
              (if 3 = Num i then
                 (if 2 = Num i then
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1))
                  else
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2))
               else
                 (if 2 = Num i then
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1))
                  else
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2)) |+
                 (3,a_3))
            else
              (if 3 = Num i then
                 (if 2 = Num i then
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1))
                  else
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2))
               else
                 (if 2 = Num i then
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1))
                  else
                    (if 1 = Num i then
                       (if 0 = Num i then FEMPTY else FEMPTY |+ (0,a_0))
                     else
                       (if 0 = Num i then
                          FEMPTY
                        else
                          FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2)) |+
                 (3,a_3)) |+ (4,a_4)) ' i' < a_4
         else
           (if Num i = 3 then
              (if 4 = Num i then
                 (if 3 = Num i then
                    (if 2 = Num i then
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1))
                     else
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2))
                  else
                    (if 2 = Num i then
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1))
                     else
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                       (2,a_2)) |+ (3,a_3))
               else
                 (if 3 = Num i then
                    (if 2 = Num i then
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1))
                     else
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+ (2,a_2))
                  else
                    (if 2 = Num i then
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1))
                     else
                       (if 1 = Num i then
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0))
                        else
                          (if 0 = Num i then
                             FEMPTY
                           else
                             FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                       (2,a_2)) |+ (3,a_3)) |+ (4,a_4)) ' i' < a_3
            else
              (if Num i = 2 then
                 (if 4 = Num i then
                    (if 3 = Num i then
                       (if 2 = Num i then
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1))
                        else
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                          (2,a_2))
                     else
                       (if 2 = Num i then
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1))
                        else
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                          (2,a_2)) |+ (3,a_3))
                  else
                    (if 3 = Num i then
                       (if 2 = Num i then
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1))
                        else
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                          (2,a_2))
                     else
                       (if 2 = Num i then
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1))
                        else
                          (if 1 = Num i then
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0))
                           else
                             (if 0 = Num i then
                                FEMPTY
                              else
                                FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                          (2,a_2)) |+ (3,a_3)) |+ (4,a_4)) ' i' < a_2
               else
                 (if Num i = 1 then
                    (if 4 = Num i then
                       (if 3 = Num i then
                          (if 2 = Num i then
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1))
                           else
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                             (2,a_2))
                        else
                          (if 2 = Num i then
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1))
                           else
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                             (2,a_2)) |+ (3,a_3))
                     else
                       (if 3 = Num i then
                          (if 2 = Num i then
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1))
                           else
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                             (2,a_2))
                        else
                          (if 2 = Num i then
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1))
                           else
                             (if 1 = Num i then
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0))
                              else
                                (if 0 = Num i then
                                   FEMPTY
                                 else
                                   FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                             (2,a_2)) |+ (3,a_3)) |+ (4,a_4)) ' i' < a_1
                  else
                    (if Num i = 0 then
                       (if 4 = Num i then
                          (if 3 = Num i then
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2))
                           else
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2)) |+ (3,a_3))
                        else
                          (if 3 = Num i then
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2))
                           else
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2)) |+ (3,a_3)) |+ (4,a_4)) ' i' <
                       a_0
                     else
                       (if 4 = Num i then
                          (if 3 = Num i then
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2))
                           else
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2)) |+ (3,a_3))
                        else
                          (if 3 = Num i then
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2))
                           else
                             (if 2 = Num i then
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1))
                              else
                                (if 1 = Num i then
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0))
                                 else
                                   (if 0 = Num i then
                                      FEMPTY
                                    else
                                      FEMPTY |+ (0,a_0)) |+ (1,a_1)) |+
                                (2,a_2)) |+ (3,a_3)) |+ (4,a_4)) ' i' <
                       FEMPTY ' (Num i)))))))``

externalSolvers name final;

(* problem: ~ !i'.
   i' < Num i ==>
need to translate ~ !i' as a for all statement and to rewrite
it using rewr_bounded_FORALL conversion *)


(* Selection sort *)
val name = "SelectionSort";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 40;

(*
TIMEOUT, need more steps!!!
*)

(* Buble sort algorithm taken from a paper of mantovani and all *)
(* a precondition fixes the values of the array to 
   contains values from 0 to a.length given in decreasing
   order 
   i.e if the array is of length 10 it contains values
   9 8 7 6 5 4 3 2 1 0
*)

val name = "BubleSortMantovani";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 1000;


(*
PROGRAM IS CORRECT
109 conditions have been tested.
64 conditions have been solved by EVAL.
55 conditions have been shown impossible.

1 feasible path has been explored.
1 path has been shown correct with the SMT solver
0 path has been shown correct with the CSP solver
0 subterm has been solved with refute and METIS.
9 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the SMT solver: 0.2s.
Total time spent with the CSP solver: 0.0s.
===============================
runtime: 1102.641s,    gctime: 417.614s,     systime: 5.820s.
> val it =
    ``RESULT
        (FEMPTY |+ ("aLength",Scalar 10) |+ ("aux",Scalar a_8) |+
         ("a",
          Array
            (FEMPTY |+ (9,a_0) |+ (8,a_1) |+ (7,a_2) |+ (6,a_3) |+
             (5,a_4) |+ (4,a_5) |+ (3,a_6) |+ (2,a_7) |+ (0,a_9) |+
             (1,a_8))) |+ ("j",Scalar 1) |+ ("i",Scalar 9))`` : term
- - - - - 
*** Time taken: 1102.649s
*)

val (_,args) = strip_comb spec;
val (pre,prog,post) = (el 1 args, el 2 args, el 3 args);
val s =    ``FEMPTY |+ ("j",Scalar j) |+ ("aux",Scalar aux) |+
      ("aLength",Scalar 10) |+ ("i",Scalar i) |+
      ("a",
       Array
         (FEMPTY |+ (0,9) |+ (1,8) |+ (2,7) |+ (3,6) |+ (4,5) |+
          (5,4) |+ (6,3) |+ (7,2) |+ (8,1) |+ (9,0)))``

resetAll();
time (execSymb name 
              (evalPre pre s) 
              (``[^prog]``,s,s,1000)
               post)
              ``T``;

runtime: 1266.015s,

(* the program is too big! *) 
val name = "GeneratedFlasherManager";
val spec = loadAndGetSpec name;
time (execSymbWithSMT name spec) 1000;

(* too slow
*** Time taken: 643.824s
to execute the 35 first assignements of variables
and there are 112 variables to initialize !!!
 *)






