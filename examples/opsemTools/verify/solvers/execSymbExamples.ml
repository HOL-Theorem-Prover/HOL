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
*** Time taken: 3.772s
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
*** Time taken: 4.352s
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
*** Time taken: 75.321s
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
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.087s
*)


(* java2opsem/testFiles/java has been modified because
   the specification was false *)
val name = "SumFromPtoN";
val spec = buildAndGetSpec name;
execSymbWithCSP name spec 10;
(*
1 path was explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.92s.
> val it =
    ``(if p + 1 <= n then
         TIMEOUT
           (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
            ("n",Scalar n) |+ ("i",Scalar i) |+ ("p",Scalar p) |+
            ("i",Scalar p) |+ ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+
            ("s",Scalar (p + (p + 1))))
       else
         RESULT
           (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
            ("n",Scalar n) |+ ("i",Scalar i) |+ ("p",Scalar p) |+
            ("i",Scalar p) |+ ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+
            ("Result",Scalar p)))`` : term
- - - - - 
*** Time taken: 12.637s

*)


(* new example *)
val name = "SumFromPtoNKO";
val spec = buildAndGetSpec name;
execSymbWithCSP name spec 10;
(*
1 path was explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.119s.
> val it =
    ``(if p + 1 <= n then
         TIMEOUT
           (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
            ("n",Scalar n) |+ ("i",Scalar i) |+ ("p",Scalar p) |+
            ("i",Scalar p) |+ ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+
            ("s",Scalar (p + (p + 1))))
       else
         ERROR
           (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
            ("n",Scalar n) |+ ("i",Scalar i) |+ ("p",Scalar p) |+
            ("i",Scalar p) |+ ("s",Scalar p) |+ ("i",Scalar (p + 1)) |+
            ("Result",Scalar p) |+ ("n",Scalar 1) |+ ("p",Scalar 1)))`` : term
- - - - - 
*** Time taken: 11.293s
*)
