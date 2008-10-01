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

(* 3 paths were explored.
1 condition was resolved by EVAL.
3 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.021s.
> val it =
    ``(if i <= j then
         (if ~(i = j) then
            RESULT
              (FEMPTY |+ ("result",Scalar result) |+
               ("Result",Scalar Result) |+ ("k",Scalar k) |+
               ("i",Scalar i) |+ ("j",Scalar j) |+ ("result",Scalar 0) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i)))
          else
            RESULT
              (FEMPTY |+ ("result",Scalar result) |+
               ("Result",Scalar Result) |+ ("k",Scalar k) |+
               ("i",Scalar i) |+ ("j",Scalar j) |+ ("result",Scalar 0) |+
               ("k",Scalar 1) |+ ("result",Scalar (i - j)) |+
               ("Result",Scalar (i - j))))
       else
         RESULT
           (FEMPTY |+ ("result",Scalar result) |+
            ("Result",Scalar Result) |+ ("k",Scalar k) |+ ("i",Scalar i) |+
            ("j",Scalar j) |+ ("result",Scalar 0) |+ ("k",Scalar 0) |+
            ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j))))`` : term
- - - - - 
*** Time taken: 3.892s
*)

val name = "AbsMinusKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 10;

(*
======================
An ERROR has been found
======================
3 paths were explored.
1 condition was resolved by EVAL.
2 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.035s.
> val it =
    ``(if i <= j then
         (if ~(i = j) then
            RESULT
              (FEMPTY |+ ("result",Scalar result) |+
               ("Result",Scalar Result) |+ ("k",Scalar k) |+
               ("j",Scalar j) |+ ("i",Scalar i) |+ ("result",Scalar 0) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i)))
          else
            RESULT
              (FEMPTY |+ ("result",Scalar result) |+
               ("Result",Scalar Result) |+ ("k",Scalar k) |+
               ("j",Scalar j) |+ ("i",Scalar i) |+ ("result",Scalar 0) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i)) |+
               ("Result",Scalar (j - i))))
       else
         ERROR
           (FEMPTY |+ ("result",Scalar result) |+
            ("Result",Scalar Result) |+ ("k",Scalar k) |+ ("j",Scalar j) |+
            ("i",Scalar i) |+ ("result",Scalar 0) |+ ("k",Scalar 0) |+
            ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)) |+
            ("i",Scalar ~32767) |+ ("j",Scalar ~32768)))`` : term
- - - - - 
*** Time taken: 2.868s
*)

val name = "Tritype";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

(*
10 paths were explored.
15 conditions were resolved by EVAL.
10 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 2.756s.
> val it =
    ``(if ((i = 0) \/ (j = 0)) \/ (k = 0) then
         RESULT
           (FEMPTY |+ ("trityp",Scalar trityp) |+
            ("Result",Scalar Result) |+ ("i",Scalar i) |+ ("j",Scalar j) |+
            ("k",Scalar k) |+ ("trityp",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if i = j then
            (if i = k then
               RESULT
                 (FEMPTY |+ ("trityp",Scalar trityp) |+
                  ("Result",Scalar Result) |+ ("i",Scalar i) |+
                  ("j",Scalar j) |+ ("k",Scalar k) |+ ("trityp",Scalar 3) |+
                  ("Result",Scalar 3))
             else
               (if k < i + j then
                  RESULT
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 2) |+ ("Result",Scalar 2))
                else
                  RESULT
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 4) |+ ("Result",Scalar 4))))
          else
            (if i = k then
               (if j < i + k then
                  RESULT
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 2) |+ ("Result",Scalar 2))
                else
                  RESULT
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 4) |+ ("Result",Scalar 4)))
             else
               (if j = k then
                  (if i < j + k then
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 2) |+ ("Result",Scalar 2))
                   else
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 4) |+ ("Result",Scalar 4)))
                else
                  (if i + j <= k \/ j + k <= i \/ i + k <= j then
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 4) |+ ("Result",Scalar 4))
                   else
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 1) |+ ("Result",Scalar 1)))))))`` :
  term
- - - - - 
*** Time taken: 40.002s
*)


val name = "TritypeKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

(*
9 paths were explored.
14 conditions were resolved by EVAL.
7 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 2.883s.
> val it =
    ``(if ((i = 0) \/ (j = 0)) \/ (k = 0) then
         RESULT
           (FEMPTY |+ ("trityp",Scalar trityp) |+
            ("Result",Scalar Result) |+ ("i",Scalar i) |+ ("j",Scalar j) |+
            ("k",Scalar k) |+ ("trityp",Scalar 4) |+ ("Result",Scalar 4))
       else
         (if i = j then
            (if i = k then
               RESULT
                 (FEMPTY |+ ("trityp",Scalar trityp) |+
                  ("Result",Scalar Result) |+ ("i",Scalar i) |+
                  ("j",Scalar j) |+ ("k",Scalar k) |+ ("trityp",Scalar 3) |+
                  ("Result",Scalar 3))
             else
               (if k < i + j then
                  RESULT
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 2) |+ ("Result",Scalar 2))
                else
                  ERROR
                    (FEMPTY |+ ("trityp",Scalar trityp) |+
                     ("Result",Scalar Result) |+ ("i",Scalar i) |+
                     ("j",Scalar j) |+ ("k",Scalar k) |+
                     ("trityp",Scalar 2) |+ ("Result",Scalar 2) |+
                     ("i",Scalar 1) |+ ("j",Scalar 1) |+ ("k",Scalar 2))))
          else
            (if i = k then
               ERROR
                 (FEMPTY |+ ("trityp",Scalar trityp) |+
                  ("Result",Scalar Result) |+ ("i",Scalar i) |+
                  ("j",Scalar j) |+ ("k",Scalar k) |+ ("trityp",Scalar 4) |+
                  ("Result",Scalar 4) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
                  ("k",Scalar 2))
             else
               (if j = k then
                  (if i < j + k then
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 2) |+ ("Result",Scalar 2))
                   else
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 4) |+ ("Result",Scalar 4)))
                else
                  (if (i + j <= k \/ j + k <= i) \/ i + k <= j then
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 4) |+ ("Result",Scalar 4))
                   else
                     RESULT
                       (FEMPTY |+ ("trityp",Scalar trityp) |+
                        ("Result",Scalar Result) |+ ("i",Scalar i) |+
                        ("j",Scalar j) |+ ("k",Scalar k) |+
                        ("trityp",Scalar 1) |+ ("Result",Scalar 1)))))))`` :
  term
- - - - - 
*** Time taken: 37.530s
*)


val name = "Sum";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;

(*8 paths were explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and OMEGA_CONV.
Total solving time with the constraint solver: 0.058s.
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
                                (FEMPTY |+ ("i",Scalar i) |+
                                 ("n",Scalar n) |+
                                 ("Result",Scalar Result) |+
                                 ("s",Scalar 0) |+ ("i",Scalar 0) |+
                                 ("s",Scalar 0) |+ ("i",Scalar 1) |+
                                 ("s",Scalar 1) |+ ("i",Scalar 2) |+
                                 ("s",Scalar 3) |+ ("i",Scalar 3) |+
                                 ("s",Scalar 6) |+ ("i",Scalar 4) |+
                                 ("s",Scalar 10) |+ ("i",Scalar 5) |+
                                 ("s",Scalar 15) |+ ("i",Scalar 6) |+
                                 ("s",Scalar 21) |+ ("i",Scalar 7) |+
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
*** Time taken: 17.817s
*)


(* Sum of integers from P to N
   Contains a non linear expression, so the CSP solver has been used
   at the end of each path
 *)
val name = "SumFromPtoN";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 20;
(*
4 paths were explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and OMEGA_CONV.
Total solving time with the constraint solver: 1.693s.
> val it =
    ``(if p + 1 <= n then
         (if p + 1 + 1 <= n then
            (if p + 1 + 1 + 1 <= n then
               (if p + 1 + 1 + 1 + 1 <= n then
                  TIMEOUT
                    (FEMPTY |+ ("p",Scalar p) |+ ("i",Scalar i) |+
                     ("n",Scalar n) |+ ("Result",Scalar Result) |+
                     ("s",Scalar s) |+ ("i",Scalar p) |+ ("s",Scalar p) |+
                     ("i",Scalar (p + 1)) |+ ("s",Scalar (p + (p + 1))) |+
                     ("i",Scalar (p + 1 + 1)) |+
                     ("s",Scalar (p + (p + 1) + (p + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1)) |+
                     ("s",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1 + 1)) |+
                     ("s",
                      Scalar
                        (p + (p + 1) + (p + 1 + 1) + (p + 1 + 1 + 1) +
                         (p + 1 + 1 + 1 + 1))) |+
                     ("i",Scalar (p + 1 + 1 + 1 + 1 + 1)))
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
- - - - - 
*** Time taken: 21.213s
*)


(* new example: contains an error
   the result must be  n*(n+1)/2 - (p-1)*p/2 
   and here the result is n*(n+1)/2 - p*(p+1)/2
*)
val name = "SumFromPtoNKO";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 10;
(*
1 path was explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and OMEGA_CONV.
Total solving time with the constraint solver: 0.046s.
> val it =
    ``(if p + 1 <= n then
         TIMEOUT
           (FEMPTY |+ ("p",Scalar p) |+ ("i",Scalar i) |+ ("n",Scalar n) |+
            ("Result",Scalar Result) |+ ("s",Scalar s) |+ ("i",Scalar p) |+
            ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+
            ("s",Scalar (p + (p + 1))))
       else
         ERROR
           (FEMPTY |+ ("p",Scalar p) |+ ("i",Scalar i) |+ ("n",Scalar n) |+
            ("Result",Scalar Result) |+ ("s",Scalar s) |+ ("i",Scalar p) |+
            ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+ ("Result",Scalar p) |+
            ("n",Scalar 1) |+ ("p",Scalar 1)))`` : term
- - - - - 
*** Time taken: 5.784s
*)


(* =================================== *)
(* Program with arrays                 *)
(* =================================== *)


(* search of an element in an array *) 
val name = "Search";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;
(*
11 paths were explored.
21 conditions were resolved by EVAL.
11 paths were resolved by SIMP_CONV and OMEGA_CONV.
Total solving time with the constraint solver: 0.167s.
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
*** Time taken: 13.841s
*)

(* Binary search *)
val name = "Bsearch";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;


(*
21 paths were explored.
31 conditions were resolved by EVAL.
21 paths were resolved by SIMP_CONV and OMEGA_CONV.
Total solving time with the constraint solver: 0.317s.
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
*** Time taken: 49.851s
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

#########################
  Number of solve 1
  Number of fail 0
  Total solving time 0.011s
#########################
======================
An ERROR has been found
======================

but the CSP solver is too slow on some problems!!!
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


(* Buble sort algorithm taken from a paper of mantovani and all *)
(* a precondition fixes the values of the array *)

val name = "BubleSortMantovani";
val spec = loadAndGetSpec name;
execSymbWithCSP name spec 30;


(*TODO:   deal with Num when building the CSP
  ``((Num a_9 = 0) /\ (Num a_8 = 1) /\ (Num a_7 = 2) /\ (Num a_6 = 3) /\
       (Num a_5 = 4) /\ (Num a_4 = 5) /\ (Num a_3 = 6) /\ (Num a_2 = 7) /\
       (Num a_1 = 8) /\ (Num a_0 = 9)) /\ a_1 < a_0`` 
*)
