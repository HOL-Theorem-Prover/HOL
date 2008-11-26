(* ====================================================== *)
(* examples of symbolic execution usign SMT solver        *)
(* ====================================================== *)


(* Stuff needed when running interactively *)

val opsemPath = Globals.HOLDIR ^ "/examples/opsemTools/";

loadPath := opsemPath :: opsemPath ^ "java2opsem" ::
opsemPath ^ "verify/solvers/" ::
opsemPath ^ "verify/solvers/SMTSolver" ::
opsemPath ^ "verify/" ::
(!loadPath);

quietdec := true; (* turn off printing *)

app load ["execSymbSMT","extSMTSolver"];
open execSymbSMT extSMTSolver;

quietdec := false; (* turn printing back on *)


(* to be able to build and load the examples *)
use "java2opsem.ml";
 
(* ====================================================== *)
(* Examples to test calls to the CSP solver from term2xml *)
(* ====================================================== *)


(* tests to execute a path *)
val ex1 = ``(i=i+1) \/ (~(i=0) /\ (i=3*i)) \/ (i>j)``;
printTerm_to_file("ex1",ex1);
execPath "ex1";
(* *** Time taken: 0.012s *)
getSolutions("ex1");
(* val it = ([("i", "-1"), ("j", "-2")] *)

(* a term slower to solve *)
val slowTerm = ``(((((i + j <= k \/ j + k <= i \/ i + k <= j) /\
   ~(((i = 0) \/ (j = 0)) \/ (k = 0))) /\ ~(i = j)) /\ ~(i = k)) /\
 (j = k)) /\ i < j + k``;
printTerm_to_file( "slowTerm",slowTerm);
execPath "slowTerm";
(* *** Time taken: 0.016s *)
val s2 = getSolutions( "slowTerm");
val s2 = ([("i", "-1"), ("j", "1"), ("k", "1")]


(* ====================================================== *)
(* Examples of symbolic execution from test files
   in java2opsem/testFiles *)
(* ====================================================== *)

val name = "AbsMinus";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 20;


(*
===============================
PROGRAM IS CORRECT
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
Total time spent with the SMT solver: 0.0s.
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
*** Time taken: 2.832s
*)

val name = "AbsMinusKO";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 10;

(*
===============================
1 ERROR has been found
3 conditions have been tested.
1 condition has been solved by EVAL.
1 condition has been shown impossible.

3 feasible paths have been explored.
Total time spent with the SMT solver: 0.012s.
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
            ("i",Scalar 1) |+ ("j",Scalar 0)))`` : term
- - - - - 
*** Time taken: 3.512s
*)

val name = "Tritype";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30;



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

Total time spent with the SMT solver: 0.048s.
*)


val name = "TritypeKO";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30;

(*
===============================
2 ERRORs have been found
26 conditions have been tested.
14 conditions have been solved by EVAL.
16 conditions have been shown impossible.

9 feasible paths have been explored.
Total time spent with the SMT solver: 0.056s.
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
execSymbWithSMT name spec 41; (* 10 times into the loop *)
(* impossible because postcondition is not linear *)
(* Compilation error in yices file: Sum! Uncaught exception: 
! YICES_COMPILEError
- - - - 
*)




(* =================================== *)
(* Program with arrays                 *)
(* =================================== *)


(* search of an element in an array *) 
val name = "Search";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30; 
(*
===============================
PROGRAM IS CORRECT
31 conditions have been tested.
21 conditions have been solved by EVAL.
11 conditions have been shown impossible.

11 feasible paths have been explored.
Total time spent with the SMT solver: 0.06s.
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
execSymbWithSMT name spec 30;


(*
===============================
PROGRAM IS CORRECT
51 conditions have been tested.
31 conditions have been solved by EVAL.
21 conditions have been shown impossible.

21 feasible paths have been explored.
Total time spent with the SMT solver: 0.124s.
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
*** Time taken: 40.811s
*)

(* Bsearch with a number of steps to small *)
execSymbWithSMT name spec 10;
(*
===============================
TIMEOUT
1 condition has been tested.
1 condition has been solved by EVAL.
0 condition has been shown impossible.

0 feasible path has been explored.
Total time spent with the SMT solver: 0.0s.
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
execSymbWithSMT name spec 20;

(*
===============================
2 ERRORs have been found
25 conditions have been tested.
13 conditions have been solved by EVAL.
13 conditions have been shown impossible.

7 feasible paths have been explored.
Total time spent with the SMT solver: 0.048s.
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
*** Time taken: 34.414s
*)

(* Partition procedure of the quicksort algorithm *)
val name = "Partition";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 30;

(* doesn't work because there are accesses to indexes which have
   symbolic values. So a if then term is generated and term2yices
   doesn't yet handle "if then" terms
  *)


(* Selection sort *)
val name = "SelectionSort";
val spec = loadAndGetSpec name;
execSymbWithSMT name spec 40;

(*
TIMEOUT, needs more steps!!!

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
execSymbWithSMT name spec 1000;


(*
===============================
PROGRAM IS CORRECT
109 conditions have been tested.
64 conditions have been solved by EVAL.
55 conditions have been shown impossible.

1 feasible path has been explored.
Total time spent with the SMT solver: 0.184s.
===============================
> val it =
    ``RESULT
        (FEMPTY |+ ("aLength",Scalar 10) |+ ("aux",Scalar a_8) |+
         ("a",
          Array
            (FEMPTY |+ (9,a_0) |+ (8,a_1) |+ (7,a_2) |+ (6,a_3) |+
             (5,a_4) |+ (4,a_5) |+ (3,a_6) |+ (2,a_7) |+ (0,a_9) |+
             (1,a_8))) |+ ("j",Scalar 1) |+ ("i",Scalar 9))`` : term
- - - - - 
*** Time taken: 912.445s
*)



(* the program is too big!
   it is impossible to build the initial state from the program. 
   it is too long to do symbolic execution (updating state is
   too slow because the state is large (112 variables)
*) 
val name = "GeneratedFlasherManager";
val spec = loadAndGetSpec name;
(* need to have loaded the example 
   instruction loadAndGetSpec above has loaded it*)
val vars = getVars name; 
(* *** Time taken: 0.080s *)
execSymbWithSMT_vars name spec 1000 vars; 
(* too slow
*** Time taken: 643.824s
to execute the 35 first assignements of variables
and there are 112 variables to initialize !!!
 *)




