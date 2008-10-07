(* ====================================================== *)
(* examples of symbolic execution *)
(* ====================================================== *)


(* Stuff needed when running interactively *)

val opsemPath = Globals.HOLDIR ^ "/examples/opsemTools/";

loadPath := opsemPath :: opsemPath ^ "java2opsem" ::
opsemPath ^ "verify/solvers" ::
opsemPath ^ "verify/" ::
(!loadPath);

quietdec := true; (* turn off printing *)

app load ["newOpsemTheory","pairSyntax", "intLib","intSimps",
          "computeLib", "finite_mapTheory",
          "relationTheory", "stringLib",
          "PATH_EVAL",
          "IndDefLib", "IndDefRules",
          "term2xml","execSymb","extSolv"];


open newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory relationTheory stringLib
     PATH_EVAL IndDefLib IndDefRules term2xml execSymb extSolv;

quietdec := false; (* turn printing back on *)



(* to be able to build and load the examples *)
use "java2opsem.ml";

(* ====================================================== *)
(* Examples to test calls to the CSP solver from term2xml *)
(* ====================================================== *)


(* tests to execute a path *)
val ex1 = ``(i=i+1) \/ (~(i=0) /\ (i=3*i)) \/ (i>j)``;
printXML_to_file("ex1",ex1);
execPath "ex1";
getSolutions(ilogPath ^ "results/ex1.res");


(* if example above doesn't work, try to re-compile *)
compile();



(* examples to use the solver with timeout *)
(* --------------------------------------- *)

val fastTerm = ``(i=j) /\ (i:int>=j:int)``;
printXML_to_file("fastTerm",fastTerm);
execPath "fastTerm";
val s1 = getSolutions(ilogPath ^ "results/fastTerm.res");
isSolverTimeout(s1);


(* a term slow to solve
   with a timeout of 100 milli seconds (0.1s) *)
val slowTerm = ``(((((i + j <= k \/ j + k <= i \/ i + k <= j) /\
   ~(((i = 0) \/ (j = 0)) \/ (k = 0))) /\ ~(i = j)) /\ ~(i = k)) /\
 (j = k)) /\ i < j + k``;
printXML_to_file( "slowTerm",slowTerm);

execPath "slowTerm";
val s2 = getSolutions(ilogPath ^ "results/slowTerm.res");
isSolverTimeout(s2);

limitedExecPath "slowTerm" 100;
val s3 = getSolutions(ilogPath ^ "results/slowTerm.res");
isSolverTimeout(s3);



(* ====================================================== *)
(* Examples of symbolic execution from test files
   in java2opsem/testFiles *)
(* ====================================================== *)

val name = "AbsMinus";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 10;


(*
===============================
PROGRAM IS CORRECT
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
All correct paths were verified in HOL.
1 subterm has been solved with refute and METIS.
2 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.018s.
===============================
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
*** Time taken: 3.548s
*)

val name = "AbsMinusKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 10;

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

Total time spent with the constraint solver: 0.024s.
===============================
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
            ("i",Scalar ~32767) |+ ("j",Scalar ~32768)))`` : term
- - - - - 
*** Time taken: 2.952s
*)

val name = "Tritype";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;


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

Total time spent with the constraint solver: 0.481s.
===============================
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
*** Time taken: 39.410s
*)


val name = "TritypeKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

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

Total time spent with the constraint solver: 0.185s.
===============================
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
*** Time taken: 26.722s
*)


val name = "Sum";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

(*
===============================
PROGRAM IS CORRECT
9 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

8 feasible paths have been explored.
All correct paths were verified in HOL.
0 subterm has been solved with refute and METIS.
8 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.067s.
===============================
> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               (if 4 <= n then
                  (if 5 <= n then
                     (if 6 <= n then
                        (if 7 <= n then
                           (if 8 <= n then
                              TIMEOUT
                                (FEMPTY |+ ("n",Scalar n) |+
                                 ("Result",Scalar Result) |+
                                 ("s",Scalar 28) |+ ("i",Scalar 8))
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
*** Time taken: 19.909s
*)


(* Sum of integers from P to N
   Contains a non linear expression, so the CSP solver has been used
   at the end of each path
 *)
val name = "SumFromPtoN";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 20;

(* If we call the CSP solver with integers coded on 32 bits, 
when computing n*(n+1)/2, there is an overflow so the CSP solver finds
an solution which is due to the overflow.

{ 
  n[-1073741824..1073741823] >= 0
  p[-1073741824..1073741823] >= 0
  p[-1073741824..1073741823] <= n[-1073741824..1073741823]
  p[-1073741824..1073741823] <= n[-1073741824..1073741823]
  not((1 + p[-1073741824..1073741823] ) <= n[-1073741824..1073741823])
  not(p[-1073741824..1073741823] == ((n[-1073741824..1073741823] * (1 + n[-1073741824..1073741823] )) / 2 - ((-1 + p[-1073741824..1073741823] ) * p[-1073741824..1073741823]) / 2 ))
} ------------------------
 using JSolver
---------
Solution: 
(n,46341)
(p,46341)


If we use integers coded on 16 bits,  since jsolver works on 
32 bits, there is no overflow and the program is proved correct.

===============================
PROGRAM IS CORRECT
9 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

8 feasible paths have been explored.
8 paths have been shown correct with the constraint solver
0 subterm has been solved with refute and METIS.
8 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.061s.
===============================
> val it =
    ``(if 1 <= n then
         (if 2 <= n then
            (if 3 <= n then
               (if 4 <= n then
                  (if 5 <= n then
                     (if 6 <= n then
                        (if 7 <= n then
                           (if 8 <= n then
                              TIMEOUT
                                (FEMPTY |+ ("n",Scalar n) |+
                                 ("Result",Scalar Result) |+
                                 ("s",Scalar 28) |+ ("i",Scalar 8))
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
*** Time taken: 19.545s
*)


(* new example: contains an error
   the result must be  n*(n+1)/2 - (p-1)*p/2 
   and here the result is n*(n+1)/2 - p*(p+1)/2
*)
val name = "SumFromPtoNKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 20;
(*
===============================
4 ERRORs have been found
5 conditions have been tested.
0 condition has been solved by EVAL.
1 condition has been shown impossible.

4 feasible paths have been explored.
All correct paths were verified in HOL.
0 subterm has been solved with refute and METIS.
4 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.041s.
===============================
> val it =
    ``(if p + 1 <= n then
         (if p + 1 + 1 <= n then
            (if p + 1 + 1 + 1 <= n then
               (if p + 1 + 1 + 1 + 1 <= n then
                  TIMEOUT
                    (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                     ("Result",Scalar Result) |+
                     ("s",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                         (p + 1 + 1 + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1 + 1 + 1)))
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
                     ("n",Scalar 0) |+ ("p",Scalar ~3)))
             else
               ERROR
                 (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
                  ("s",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                  ("i",Scalar (p + 1 + 1 + 1)) |+
                  ("Result",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                  ("n",Scalar 0) |+ ("p",Scalar ~2)))
          else
            ERROR
              (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+
               ("s",Scalar (p + (p + 1))) |+ ("i",Scalar (p + 1 + 1)) |+
               ("Result",Scalar (p + (p + 1))) |+ ("n",Scalar 0) |+
               ("p",Scalar ~1)))
       else
         ERROR
           (FEMPTY |+ ("p",Scalar p) |+ ("n",Scalar n) |+ ("s",Scalar p) |+
            ("i",Scalar (p + 1)) |+ ("Result",Scalar p) |+ ("n",Scalar 1) |+
            ("p",Scalar 1)))`` : term
- - - - - 
*** Time taken: 27.306s
*)


(* =================================== *)
(* Program with arrays                 *)
(* =================================== *)


(* search of an element in an array *) 
val name = "Search";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30; 
(*
===============================
PROGRAM IS CORRECT
31 conditions have been tested.
21 conditions have been solved by EVAL.
11 conditions have been shown impossible.

11 feasible paths have been explored.
All correct paths were verified in HOL.
20 subterms have been solved with refute and METIS.
0 subterm has been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.161s.
===============================
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
execSymbWithCSP name spec 30;


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

Total time spent with the constraint solver: 0.315s.
===============================
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
*** Time taken: 237.071s
*)

(* Bsearch with a number of steps to small *)
execSymbWithCSP name spec 10;
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

Total time spent with the constraint solver: 0.0s.
===============================
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
*** Time taken: 4.016s
*)


(* Binary search with an error 
when the searched value is greater than the middle, modify the 
rigth bound instead of the left bound
*)
val name = "BsearchKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 20;

(*
the solution found by the CSP solver gives a nice counter-example !

Solution: 
(a_8,-32766)
(a_9,-32766)
(a_7,-32766)
(a_6,-32766)
(a_5,-32766)
(a_4,-32766)
(a_3,-32767)
(a_2,-32768)
(a_1,-32768)
(a_0,-32768)
(x,-32767)

Resolution time : 0.011s
---------
===============================
2 ERRORs have been found
25 conditions have been tested.
13 conditions have been solved by EVAL.
13 conditions have been shown impossible.

7 feasible paths have been explored.
All correct paths were verified in HOL.
15 subterms have been solved with refute and METIS.
28 subterms have been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.514s.
===============================
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
                     ("Result",Scalar ~1) |+ ("a_8",Scalar ~32766) |+
                     ("a_9",Scalar ~32766) |+ ("a_7",Scalar ~32766) |+
                     ("a_6",Scalar ~32766) |+ ("a_5",Scalar ~32766) |+
                     ("a_4",Scalar ~32766) |+ ("a_3",Scalar ~32767) |+
                     ("a_2",Scalar ~32768) |+ ("a_1",Scalar ~32768) |+
                     ("a_0",Scalar ~32768))))
          else
            ERROR
              (FEMPTY |+ ("aLength",Scalar 10) |+ ("x",Scalar x) |+
               ("a",
                Array
                  (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+
                   (4,a_4) |+ (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+
                   (9,a_9))) |+ ("result",Scalar ~1) |+ ("left",Scalar 0) |+
               ("mid",Scalar 0) |+ ("right",Scalar ~1) |+
               ("Result",Scalar ~1) |+ ("a_8",Scalar ~32768) |+
               ("a_9",Scalar ~32767) |+ ("a_7",Scalar ~32768) |+
               ("a_6",Scalar ~32768) |+ ("a_5",Scalar ~32768) |+
               ("a_4",Scalar ~32768) |+ ("a_3",Scalar ~32768) |+
               ("a_2",Scalar ~32768) |+ ("a_1",Scalar ~32768) |+
               ("a_0",Scalar ~32768))))`` : term
- - - - - 
*** Time taken: 119.499s

Some paths are impossible and the CSP solver is too slow to show it.
So SIMP_CONV is called and shows quickly that the path is not feasible.

======================
Testing feasability
======================
Calling external solver with timeout on:
(a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\
(((~(a_4 = x) /\ x < a_4) /\ ~(a_1 = x)) /\ ~(x < a_1)) /\ (a_0 = x)
Timeout in solver, testing path with SIMP_CONV
======================
Path (a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\(((~(a_4 = x) /\ x < a_4) /\ ~(a_1 = x)) /\ ~(x < a_1)) /\ (a_0 = x) is impossible


======================
Testing feasability
======================
Calling external solver with timeout on:
(a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\
(~(a_4 = x) /\ ~(x < a_4)) /\ (a_1 = x)
Timeout in solver, testing path with SIMP_CONV
======================
Path (a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\(~(a_4 = x) /\ ~(x < a_4)) /\ (a_1 = x) is impossible

======================
Testing feasability
======================
Calling external solver with timeout on:
(a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\
(((~(a_4 = x) /\ ~(x < a_4)) /\ ~(a_1 = x)) /\ ~(x < a_1)) /\ (a_0 = x)
Timeout in solver, testing path with SIMP_CONV
======================
Path (a_8 <= a_9 /\ a_7 <= a_8 /\ a_6 <= a_7 /\ a_5 <= a_6 /\ a_4 <= a_5 /\
 a_3 <= a_4 /\ a_2 <= a_3 /\ a_1 <= a_2 /\ a_0 <= a_1) /\(((~(a_4 = x) /\ ~(x < a_4)) /\ ~(a_1 = x)) /\ ~(x < a_1)) /\ (a_0 = x) is impossible

*)

(* Partition procedure of the quicksort algorithm *)
val name = "Partition";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

(* doesn't work because there are accesses to indexes which have
   symbolic values. So a if then term is generated and term2xml
   doesn't handle "if then" terms
   It would be easy to modify using meta constraint "ifThen  *)


(* Selection sort *)
val name = "SelectionSort";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 40;

(*
PROBLEM!!!

Timeout in solver, testing path with SIMP_CONV
======================
Path ((((((~(a_1 < a_0) /\ a_2 < a_0) /\ a_3 < a_2) /\ ~(a_4 < a_3)) /\
   a_5 < a_3) /\ a_6 < a_5) /\ ~(a_7 < a_6)) /\ ~(a_8 < a_6) is impossible
======================

Type inference failure: unable to infer a type for the application of

COND ((a_7 :int) < (a_6 :int))
  (if (a_8 :int) < a_7 then
     (if (a_9 :int) < a_8 then
        TIMEOUT
          ((FEMPTY :state) |+ ("aLength",Scalar (10 :int)) |+
           ("a",
            Array
              ((FEMPTY :num |-> int) |+ ((0 :num),(a_0 :int)) |+
               ((1 :num),(a_1 :int)) |+ ((2 :num),(a_2 :int)) |+
               ((3 :num),(a_3 :int)) |+ ((4 :num),(a_4 :int)) |+
               ((5 :num),(a_5 :int)) |+ ((6 :num),a_6) |+
               ((7 :num),a_7) |+ ((8 :num),a_8) |+ ((9 :num),a_9))) |+
           ("i",Scalar (0 :int)) |+ ("aux",Scalar (0 :int)) |+
           ("indMin",Scalar (9 :int)) |+ ("j",Scalar (10 :int)))
      else
        TIMEOUT
          ((FEMPTY :state) |+ ("aLength",Scalar (10 :int)) |+
           ("a",
            Array
              ((FEMPTY :num |-> int) |+ ((0 :num),a_0) |+
               ((1 :num),a_1) |+ ((2 :num),a_2) |+ ((3 :num),a_3) |+
               ((4 :num),a_4) |+ ((5 :num),a_5) |+ ((6 :num),a_6) |+
               ((7 :num),a_7) |+ ((8 :num),a_8) |+ ((9 :num),a_9))) |+
           ("i",Scalar (0 :int)) |+ ("aux",Scalar (0 :int)) |+
           ("indMin",Scalar (8 :int)) |+ ("j",Scalar (10 :int))))
   else
     (if a_9 < a_7 then
        TIMEOUT
          ((FEMPTY :state) |+ ("aLength",Scalar (10 :int)) |+
           ("a",
            Array
              ((FEMPTY :num |-> int) |+ ((0 :num),a_0) |+
               ((1 :num),a_1) |+ ((2 :num),a_2) |+ ((3 :num),a_3) |+
               ((4 :num),a_4) |+ ((5 :num),a_5) |+ ((6 :num),a_6) |+
               ((7 :num),a_7) |+ ((8 :num),a_8) |+ ((9 :num),a_9))) |+
           ("i",Scalar (0 :int)) |+ ("aux",Scalar (0 :int)) |+
           ("indMin",Scalar (9 :int)) |+ ("j",Scalar (10 :int)))
      else
        TIMEOUT
          ((FEMPTY :state) |+ ("aLength",Scalar (10 :int)) |+
           ("a",
            Array
              ((FEMPTY :num |-> int) |+ ((0 :num),a_0) |+
               ((1 :num),a_1) |+ ((2 :num),a_2) |+ ((3 :num),a_3) |+
               ((4 :num),a_4) |+ ((5 :num),a_5) |+ ((6 :num),a_6) |+
               ((7 :num),a_7) |+ ((8 :num),a_8) |+ ((9 :num),a_9))) |+
           ("i",Scalar (0 :int)) |+ ("aux",Scalar (0 :int)) |+
           ("indMin",Scalar (7 :int)) |+ ("j",Scalar (10 :int)))))

on line 1543, characters 9-37

which has type

:outcome -> outcome

to

F :bool

between beginning of frag 5 and end of frag 5

unification failure message: unify failed
! Uncaught exception: 
! HOL_ERR
- - - - - 
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
execSymbWithCSP name spec 1000;


(*
We can assign initial values of the array using  the precondition
(could be done automatically but not yet implemented)

val (_,args) = strip_comb spec;
val (pre,prog,post) = (el 1 args, el 2 args, el 3 args);
val s =    ``FEMPTY |+ ("j",Scalar j) |+ ("aux",Scalar aux) |+
      ("aLength",Scalar 10) |+ ("i",Scalar i) |+
      ("a",
       Array
         (FEMPTY |+ (0,9) |+ (1,8) |+ (2,7) |+ (3,6) |+ (4,5) |+
          (5,4) |+ (6,3) |+ (7,2) |+ (8,1) |+ (9,0)))``

resetAll();
execSymb name 
              (evalPre pre s) 
              (``[^prog]``,s,s,1000)
               post
              ``T``;

===============================
PROGRAM IS CORRECT
109 conditions have been tested.
109 conditions have been solved by EVAL.
10 conditions have been shown impossible.

1 feasible path has been explored.
All correct paths were verified in HOL.
1 subterm has been solved with refute and METIS.
0 subterm has been solved with SIMP_CONV and COOPER.

Total time spent with the constraint solver: 0.0s.
===============================

> val it =
    ``RESULT
        (FEMPTY |+ ("aLength",Scalar 10) |+ ("aux",Scalar 1) |+
         ("a",
          Array
            (FEMPTY |+ (9,9) |+ (8,8) |+ (7,7) |+ (6,6) |+ (5,5) |+ (4,4) |+
             (3,3) |+ (2,2) |+ (0,0) |+ (1,1))) |+ ("j",Scalar 1) |+
         ("i",Scalar 9))`` : term
- - - - - 
*** Time taken: 409.614s

If we don't use the precondition to assign values of the array
in the initial state:

*** Time taken: 526.989s


*)
