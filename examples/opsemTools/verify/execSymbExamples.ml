(* examples of symbolic execution *)

(* Stuff needed when running interactively *)

loadPath := Globals.HOLDIR ^ "/examples/opsemTools/" :: 
Globals.HOLDIR ^ "/examples/opsemTools/java2opsem" ::
Globals.HOLDIR ^ "/examples/opsemTools/verify/solvers" ::
Globals.HOLDIR ^ "/examples/opsemTools/verify/" ::
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



(* Examples to test calls to CSP solver from term2xml *)


(* tests to execute a path *)
val ex1 = ``(i=i+1) \/ (~(i=0) /\ (i=3*i)) \/ (i>j)``;
printXML_to_file("ex1",ex1);
execPath "ex1";
getSolutions(ilogPath ^ "results/ex1.res");

(* if example above doesn't work, try to re-compile *)
compile();



(* tests to use the solver with timeout *)
(* ------------------------------------ *)


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




(* TODO: examples of symbolic execution from test files
   in java2opsem/testFiles *)
(* requires to move from num to int in tactics used by 
   execSymb.sml *)
