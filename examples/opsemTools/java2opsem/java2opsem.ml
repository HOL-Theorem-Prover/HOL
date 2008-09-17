(* =============== java2opsem ========================== *)

(* =====================================================
   Functions to generate a relational specification
       (RSPEC pre prog post) 
   from a Java file that contains a java method and
   a JML specification.

   pre, prog, post are terms.
     - pre is a lambda expression on state and will be evaluated 
   on the state before execution of the method.
     - post is a lambda expression on two states, the state before 
   and the state after execution of the method. This allows 
   to have relational expressions in postconditions that express
   a relation between state before and after execution.
     - prog is a program that follows the syntax given in
   newOpsemTheory.


* testFiles/javaFiles contain a set of Java programs with their JML 
specifications.
* testFiles/opsemFiles contain the sml scripts for building 
RSPEC terms that correspond to Java files. Files in testFiles/opsem
have been automatically built using buildAndLoadAllSpec().

Do Holmake in testFiles/opsemFiles to compile examples
and then use "loadAndGetSpec name" to get the specification
of example "name".
To build a new example from a Java file "name", use 
"buildAndGetSpec name"

See "How to?" at the end of this comment for more details on 
the use of functions in java2opsem.

=====
NOTA:
=====
- Tools for parsing Java and JML run on any platform with 
  J2SDK 1.4.1 or J2SDK 1.4.2 and later versions.
- You need to recompile the java classes
  the first time you are using this file.
  use "compile();" function at the end of this file.

   ===================================================== *)

(* =====================================================
   This tool takes as input a small subset of Java and 
   JML languages (see JML Home page at 
   http://www.eecs.ucf.edu/~leavens/JML/ for general information
   on JML).
   However, it uses standard tools for parsing Java 
   and jml, and can be extended by implementing
   visitors for new Classes.
     
   It uses JDT (Java Development Tooling, eclipse environment)
   for parsing Java.
   See http://help.eclipse.org/help31/index.jsp?topic=/org.eclipse.jdt.doc.isv/reference/api/index.html
   for description of the API and AST nodes.

   It uses jml-release.jar for parsing JML specifications.
   See http://sourceforge.net/project/showfiles.php?group_id=65346&package_id=62764&release_id=594123
   for downloading JML tools.
   jml-release.jar is part of JML.5.6_rc1.tar.gz, last version 
   May 2008.
   See http://www.cs.ucf.edu/~leavens/JML/ for information on JML

   Translation follows as much as possible explanations given in 
   jml reference manual
   http://www.eecs.ucf.edu/~leavens/JML//OldReleases/jmlrefman.pdf.
   There is also a local copy of the  manual (version 
   august 2008) in directory java2opSem.


   ===================================================== *)

(* =============== Current restrictions ================

Java programs
-------------
Only syntactically correct and well typed programs are accepted.

- Data types: integer variables and arrays of integers 
(no objects).

- Only the following operators are permitted:
  + Integer operators: +, -, *, /
  + Relational operators: >,>=,<,<=,==,!=
  + Logical operators: !(not), || (or); && (and)
(- i++ or i-- statements are not allowed)

- integer expressions must be fully parenthesized otherwise
the HOL term will not be correct
(e.g x+y+z will produce (Plus x y z) which is not
allowed in the opsem syntax of programs)

- Local variables:
   * integer variable declarations will be translated
     into an assignment
     int i = 3; --> (Assign "i" (Const 3))
     int i;     --> (Assign "i" (Const 0)) because O
     is the default value for integers.
   TODO: declare the variable as "Local" in opSem 
   * no array declarations (arrays can only be parameters)

- Array lengths
  The length of an array "arr" is represented as an integer 
  variable "arrLength". 
  Exemple:
    if (a.Length > 8) s=4;
  is translated as
      (Cond
        (Less 
          (Const 8)
          (Var "aLength")
        )
        (Assign "s"
          (Const 4)
        )
        Skip
      )
    
- Control flow instructions
   * in "if statements", then and else blocks must be enclosed 
within {}, even if the block contains only one instruction
(restriction from jmspecs.check).
Example:
  don't use "if (i>3) x=6;" but "if (i>3) {x=6};"
   * no "case" statement
   * only "while loops" ("for loops" are not allowed)

- Javadoc comments are not allowed

- opSem is defined on natural numbers only. So an expression as
-1 will be correctly translated but not allowed in opSem.


JML specifications
------------------

- Specification expressions
  Only normal behaviour of the method, \requires and \ensures 
  clauses (no \also).
  NB: requires clause must precede ensures clause.
  TODO: \assert

- Only the following operators are allowed inside \requires 
  and \ensures expressions:
    * Integer operators: +, -, *, /
    * Relationnal operators: >,>=,<,<=,==,!=
    * Logical operators: !(not), || (or); && (and), ==>
    TODO: <==> and <=!=>
    * \result: represents the value returned by the method.
    A variable "Result" is created in opSem and is evaluated 
    on the final state.
       Example:
         /*@ ensures \result == 8;*/
       Postcondition:
         \state1 state2. (ScalarOf (state2 ' "Result")= 8)
    * \old (see explanations below)
    * JmlSpecQuantifiedExpression \forall and \exists
    (see explanations below)

- Array lengths
  The length of an array "arr" is represented as an integer 
  variable "arrLength". 

   ================= Current restrictions ================ *)

(* ======================= sml files ===================== 
Each example "Foo" is built in a file "FooScript.sml"
which defines the theory "Foo".

This theory contains one definition "MAIN_def"
which defines the RSPEC specification.

Example:
-------
File testFiles/javaFiles/AbsMinus.java

class AbsMinus {
    /*@ ensures
         ((i < j) ==> (\result == j-i))
         && ((i >= j) ==> (\result == i-j));
    @*/
    int absMinus (int i, int j) {
       int result;
       int k = 0;
       if (i <= j) {
            k = k+1;
       }
       if (k == 1 && i != j) {
            result = j-i;
       }
       else {
            result = i-j;
       }
       return result;
    }
}

File testFiles/opsemFiles/AbsMinusScript.sml

(* This file has been generated by java2opSem from testFiles/javaFiles/AbsMinus.java*)

open HolKernel Parse boolLib
stringLib IndDefLib IndDefRules
finite_mapTheory relationTheory
newOpsemTheory
computeLib bossLib;

val _ = new_theory "AbsMinus";

(* Method absMinus*)
val MAIN_def =
  Define `MAIN =
    RSPEC
    (\state.
      T)
      (Seq
        (Assign "result" (Const 0))
        (Seq
          (Assign "k"
            (Const 0)
          )
          (Seq
            (Cond
              (LessEq
                (Var "i")
                (Var "j")
              )
              (Assign "k"
                (Plus
                  (Var "k")
                  (Const 1)
                )
              )
              Skip
            )
            (Seq
              (Cond
                (And
                  (Equal
                    (Var "k")
                    (Const 1)
                  )
                  (Not (Equal
                    (Var "i")
                    (Var "j")
                  ))
                )
                (Assign "result"
                  (Sub
                    (Var "j")
                    (Var "i")
                  )
                )
                (Assign "result"
                  (Sub
                    (Var "i")
                    (Var "j")
                  )
                )
              )
              (Assign "Result"
                (Var "result")
              )
            )
          )
        )
      )
    (\state1 state2.
      ((((ScalarOf (state1 ' "i")<ScalarOf (state1 ' "j")))) ==> (((ScalarOf (state2 ' "Result")=ScalarOf (state1 ' "j")-ScalarOf (state1 ' "i")))))/\((((ScalarOf (state1 ' "i")>=ScalarOf (state1 ' "j")))) ==> (((ScalarOf (state2 ' "Result")=ScalarOf (state1 ' "i")-ScalarOf (state1 ' "j"))))))
    `

  val _ = export_theory();

   ======================= sml files ===================== *)




(* more details on translation *)


(* ======================== state =========================

   In newOpsem, variables are reprented by strings and their 
   values are computed by evaluating a lambda expression on 
   the state.
   Values of variables are either scalars
       ScalarOf (state ' "i")
   or arrays
       ArrayOf (state ' "tab") ' i.

   Precondition (\requires)
   ------------------------
   In precondition, all variables are evaluated on the
   state before execution of the method. So the precondition
   is a lambda expression on state.
   Example
      \requires i>= j;
   will be translated as:
      \state. ScalarOf (state ' "i") <= ScalarOf (state ' "j")

   Postcondition (\ensures)
   ------------------------
   The postcondition can express a relation between variable
   values before and after execution of the method. So the
   postcondition is a lambda expression on state1 and state2
   where state1 represents the state before execution and
   state2 represents the state after execution.

   As mentioned in chapter 9.9.3 (Ensures Clauses, p 73) of the 
   reference manual, the postcondition is evaluated on the 
   state after execution of the method.
   There are two execeptions: parameters and expressions
   inside \old statements are evaluated on the state 
   before execution of the method (see below).

Parameters in Postconditions (Jml reference manual page 77,
chapter 9.9.6)
Parameters of methods are passed by value in Java, meaning that
parameters are local variables in a method body, which are 
initialized when the method is called with the values
of the parameters for the invocation.
This leads us to the following two rules:
  - The parameters of a method or constructor can never be 
listed in its assignable clause.
  - If parameters of a method (or constructor) are used in a 
normal or exceptional postcondition for that method (or 
constructor), i.e., in an ensures or signals clause, then
these always have their value in the pre-state of the method
(or constructor), not the post-state. In other words, there is
an implicit \old() placed around any occurrence
of a formal parameter in a postcondition.

Example:
--------

/*@ requires (n >= 0);
  @ ensures \result == (n*(n+1))/2;
  @*/
static int sum (int n)

Precondition: 
(\state.
  ((ScalarOf (state ' "n")>=0)))
Postcondition
(\state1 state2.
  (ScalarOf (state2 ' "Result")=(ScalarOf (state1 ' "n")*(ScalarOf (state1 ' "n")+1))/2))

Result corresponds to \result JML statement and is evaluated
on the final state (state2). n is a parameter of the
procedure and is evaluated on the initial state state1.

    Arrays
    Since Java implements a call by value parameter passing,
    if "arr" is an array and is a parameter of the method,
    "arr" will be evaluated on the initial state. But "arr[i]"
    is evaluated on the final state.  

Example:
   /*@ ensures a==\old(b) && b==\old(a);
    @*/
    void swap(int[] a, int[] b )
Postcondition:
(\state1 state2.
  (ScalarOf (state1 ' "a")=ScalarOf (state1 ' "b"))
/\(ScalarOf (state1 ' "b")=ScalarOf (state1 ' "a")))
a and b are evaluated 

    Array lengths: since the length of the array can't be
    modified in a method, it is evaluated on the state before
    execution.

   ==================== state ========================= *)


(* ================ \old ===============================

   The \old(Expr) statement refers to the value of Expr
   before execution of the method.   
   So \old(Expr) will return the term which corresponds
   to Expr where all variables are evaluated on state1.

See reference manual p 89 for details on \old (chapter
11.4.2 \old and \pred).

Example:
 
 /*@ requires (i>0 && i < a.length)
  @ && (j>0 && j < a.length);
  @ ensures a[i]==\old(a[j]) && a[j]==\old(a[i]);
  @*/
 void swap(int[] a, int i,int j )

Precondition
(\state.
  ((ScalarOf (state ' "i")>0)/\(ScalarOf (state ' "i")<ScalarOf (state ' "aLength")))
/\((ScalarOf (state ' "j")>0)/\(ScalarOf (state ' "j")<ScalarOf (state ' "aLength"))))
Postcondition
(\state1 state2.
  ((ArrayOf (state2 ' "a") ' (ScalarOf (state1 ' "i")))=
   (ArrayOf (state1 ' "a") ' (ScalarOf (state1 ' "j"))))
/\((ArrayOf (state2 ' "a") ' (ScalarOf (state1 ' "j")))=
   (ArrayOf (state1 ' "a") ' (ScalarOf (state1 ' "i")))))

Here, i and j are evaluated on initial state because they are
parameters but a[i] and a[j] are evaluated on the final state.

   Current restrictions: 
   - \old(Expr,label) is not yet implemented
   - an expression inside \old can't contains a quantified expression 

   ======================== \old ====================== *)

(* ================= \forall \exists ====================

   Only \forall and \exits  spec-quantified-expr are possible.
   TODO: use specific global constraints to translate other
         quantified expressions such as \num_of, \min, \max, ...

    spec-quantified-expr ::= "(" quantifier quantified-var-decl "; [ [ predicate ] ";" ] spec-expression ")"
    is translated as:
      ! v1 v2 ... vn . predicate(v1,...,vn) ==> spec-expression
    when quantifier is \forall
    and as
      ? v1 v2 ... vn . predicate(v1,...,vn) /\ spec-expression
    where v1 v2 ... vn are the variables declared in 
    quantified-var-decl.

Example:
   /*@ ensures
     @	(\forall int i; (i >= 0 && i < a.length-1); a[i] <= a[i+1])
     @ && (\forall int i; (i >= 0 && i < a.length-1);
     @        (\exists int j; (i >= 0 && i < a.length-1);
     @              \old(a[j]) == a[i]));
     @*/
   void bubbleSort (int[] a) {
Postcondition
(\state1 state2.
  (!i . (((i>=0)/\(i<ScalarOf (state1 ' "aLength")-1)))==>
        (((ArrayOf (state2 ' "a") ' (i))<=(ArrayOf (state2 ' "a") ' (i+1)))))
/\(!i . (((i>=0)/\(i<ScalarOf (state1 ' "aLength")-1)))==>
   ((?j . (((i>=0)/\(i<ScalarOf (state1 ' "aLength")-1)))
          /\(((ArrayOf (state1 ' "a") ' (j))=(ArrayOf (state2 ' "a") ' (i))))))))

   ================= \forall \exists ==================== *)


(* ======================= How to ? ========================

Functions below load or build RSPEC specifications.
Specifications can be built from Java files or can be
loaded from examples in testFiles/opsemFiles.


The files in  "testFiles/opsemFiles" define theories.
The specification of an example is stored as a Hol definition 
with name MAIN_def.


Functions in java2opsem
-----------------------

java2opsem can be used in two ways:
 
     1. To generate specifications from .java files.

     2. To load and get specifications that have already
        been generated from a Java file and compiled
        as a theory.

#1 functions call the programs that parse Java and JML
and use "Holmake" to build the theories.
Java files are supposed to be in "testFiles/javaFiles"
and the sml files that are generated are written in 
"testFiles/opsemFiles".
#1 functions can be quite slow.

#2 functions can be used to load specifications that have
already been built in testFiles/opsemFiles. 

The names of #1 functions begin with "build".
They are:
  - buildAndGetSpec name: to build and get the 
    specification from file testFiles/javaFiles/name.java.
    Returns the RSPEC term.
  - buildAndLoadAllSpec(): to build and load theories
    that correspond to all examples in 
    testFiles/javaFiles/
    
The names of #2 functions begin with "load".
They are:
  - loadAndGetSpec name: to load and get the 
    specification from theory "name" that has already
    been built in testFiles/opsemFiles.
    Returns the RSPEC term. 
  - loadAllSpec(): to load all the theories 
    in testFiles/opsemFiles.

When the theory of example "name" has been loaded,
its specification is computed by:
    getSpec name


Standard use of these functions:
--------------------------------

To work on few examples that have already been built:
    loadAndGetSpec("Tritype");
will return the RSPEC term that corresponds to Tritype.

To work on many examples that have already been built;
    loadAllSpec()
And then get the specification of a particular 
example:
    getSpec("AbsMinus");

If you have created a new example file in
"testFiles/javaFiles/Foo.java:
then
    buildAndGetSpec("Foo");
will return the RSPEC term that corresponds to Foo.

To build and load all the examples in "testFiles/javaFiles":
    buildAndLoadAllSpec()
(this can be quite long)

Remark:
Don't care about the warning message which is diplayed
when building the specification from a .java file:
NLS missing message: initializer_error in: org.eclipse.core.internal.runtime.messages
NLS missing message: fileInitializer_fileNotFound in: org.eclipse.core.internal.runtime.messages
NLS missing message: fileInitializer_IOError in: org.eclipse.core.internal.runtime.messages
NLS missing message: fileInitializer_missingFileName in: org.eclipse.core.internal.runtime.messages


======================= How to ? ====================== *)


(* ---------------------------------------------------- *)
(* Functions to load or generate a RSPEC specifications *)
(* ---------------------------------------------------- *)

load "newOpsemTheory";

(* The compiled examples are written in the directory 
   testFiles/opsemFiles so add it into the load path 
*)

loadPath := Globals.HOLDIR ^ "/examples/opsemTools/" :: 
     Globals.HOLDIR ^ "/examples/opsemTools/java2opsem/testFiles/opsemFiles" :: (!loadPath);

local

val path = Globals.HOLDIR ^ "/examples/opsemTools/java2opsem/";

val testPath = path ^ "testFiles/";

in

(* auxiliary function to suppress the extension to a file name *)
fun suppressExtension(s,s') = 
  if s'=""
  then s
  else
    let val fst = String.sub(s',0)
      val newS' = s ^ Char.toString(fst)
    in
      if fst = #"."
      then s
      else suppressExtension(newS', 
                            String.substring(s',1,(size s')-1))
    end;

(* -----------------------------------------------------*)
(* to get specifications from alreay loaded examples    *)
(* -----------------------------------------------------*)

(* Function to get the RSPEC specification of an example that
   has already been loaded 
   PRECOND: theory name has already been loaded  
*)
fun getSpec name = 
   snd(dest_comb(concl(assoc "MAIN_def" (definitions name))));

(* function to get the spec of file "testFiles/opsemFiles/name.sml"
   when the .sml has already been built and compiled. *)
fun loadAndGetSpec name = 
    (load(name ^ "Theory");
     getSpec name
    );

local

(* returns true is name is a file with extension .ui *)
fun isUiFile(s,s') =
  if s'=""
  then false
  else
    let val fst = String.sub(s',0)
      val newS' = s ^ Char.toString(fst)
    in
      if fst = #"."
      then (s' = ".ui")
      else isUiFile(newS',String.substring(s',1,(size s')-1))
    end;

in


(* function to load all the examples that have already
   been built and compiled in "testFiles/opsemFiles" *)
fun loadAllSpec() =
  let val files =  Portable.listDir(testPath ^ "/opsemFiles");
    val uiFiles = List.filter (fn tm => isUiFile("",tm)) files;
  in 
    (print("loading all test examples in " ^ testPath ^ "/opsemFiles\n");
     map (fn tm => load(suppressExtension("",tm)))
          uiFiles
    )
  end;
end;


(* -----------------------------------------------------
   To get specifications from java files.
   Need to generate the .sml file, to compile it and
   to load it.  
   -----------------------------------------------------*)
local

val classPath = ".:" ^ path ^ "bin:" ^ path ^ "lib/jml-release.jar:"
   ^ path ^ "lib/org.eclipse.core.contenttype_3.2.0.v20060603.jar:"
   ^ path ^ "lib/org.eclipse.core.jobs_3.2.0.v20060603.jar:" 
   ^ path ^ "lib/org.eclipse.core.resources_3.2.1.R32x_v20060914.jar:"
   ^ path ^ "lib/org.eclipse.core.runtime_3.2.0.v20060603.jar:"
   ^ path ^ "lib/org.eclipse.equinox.common_3.2.0.v20060603.jar:"
   ^ path ^ "lib/org.eclipse.equinox.preferences_3.2.1.R32x_v20060717.jar:"
   ^ path ^ "lib/org.eclipse.jdt.core_3.2.1.v_677_R32x.jar:"
   ^ path ^ "lib/org.eclipse.osgi_3.2.1.R32x_v20060919.jar"

in

(* Returns the specification of examples in 
   "testFiles/javaFiles/name.java"
   Generates the .sml file, then builds the corresponding 
   theory and returns the specification.
*)

fun buildAndGetSpec name = 
  let val conv = "java  -cp " ^ classPath ^ " java2opSem.Export2opSem "
    ^ testPath ^"javaFiles/"  ^ name ^ ".java";
    val currentDir = Portable.pwd();
   in
     (Portable.system(conv);
      Portable.system("cd " ^ testPath ^ "opsemFiles;Holmake;");
      load(name ^ "Theory");
      Portable.system("cd " ^ currentDir);
      print("Theory " ^ name ^ " has been loaded\n");
      getSpec name
    )
end;


local

(* to generate, build and load the specification from file 
   testFiles/javaFiles/name.java *)
fun buildAndLoadSpec name = 
  let val conv = "java  -cp " ^ classPath ^ " java2opSem.Export2opSem "
    ^ testPath ^ "javaFiles/"  ^ name ^ ".java";
   in
     (Portable.system(conv);
      Portable.system("cd " ^ testPath ^ "opsemFiles;Holmake;cd ../");
      load(name ^ "Theory");
      print("Theory " ^ name ^ " has been loaded\n")
    )
end;

in

(* read all files in testFiles/javaFiles, generate the 
   corresponding .sml files in testFiles/javaFiles, compile
   them using Holmake and load
   the corresponding theories.
*)
fun buildAndLoadAllSpec() =
  let val files =  Portable.listDir(testPath ^ "javaFiles");
  in 
    (print "Building and loading all test examples in testFiles/javaFiles\n";
     map (fn tm => buildAndLoadSpec(suppressExtension("",tm)))
          files
    )
  end;
end;

(* to compile java files of package java2opSem *)
fun compile() = 
  let val comp = "javac -d " ^ path ^ "bin -cp " ^ classPath
                  ^ " " ^ path ^"src/java2opSem/*.java";
   in
     ((*print("class path is:" ^ classPath);*)
      Portable.system(comp);
      print("Java files have been compiled ...\n")
     )
end;

end;

end;


(* ============== examples ========================= 

(* Case 1 of use: building theories in testFiles/opsemFiles from .
                  Java files in testFiles/javaFiles    *)
(* --------------------------------------------------- *)

(* build, load and get the specification of Tritype 
   from  testFiles/javaFiles/Tritype.java *)
val TritypeSpec = buildAndGetSpec "Tritype";

(* build, load and get the specification of AbsMinus 
   from  testFiles/javaFiles/AbsMinus.java *)
val AbsMinusSpec = buildAndGetSpec "AbsMinus";

(* build and load the specification of all files in 
   testFiles/javaFiles *)
(* could be quite slow *)
buildAndLoadAllSpec();

(* to get the specification of "BubleSort" that 
   has already been built and loaded by the call to
   buildAndLoadAllSpec() above *)
val BubleSortSpec = getSpec("BubleSort");


(* Case 2 of use: Examples have already been generated and compiled
                  as theories in testFiles/opsemFiles  *)
(* --------------------------------------------------  *)


(* load theory SumFromPtoN and get its specification *)
val SumFromPtoNSpec = loadAndGetSpec "SumFromPtoN";

(* load all the theories that have already been
   generated and compiled in testFiles/opsemFiles *)

loadAllSpec();

(* get the spec of "ArraySwapElement" that has
   been loaded by loadAllSpec() above *)
val ArraySwapElementSpec = getSpec "ArraySwapElement";


   ============== examples ========================= *)


