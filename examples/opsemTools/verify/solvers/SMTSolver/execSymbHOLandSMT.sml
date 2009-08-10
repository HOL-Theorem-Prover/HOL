
(* ========================= execSymbHOLandSMT.sml =====================

   Version of symbolic execution that uses the SMT solver yices to cut
   paths and to solve the final terms at the end of the paths when
   HOL fails.
   It also calls the constraint solver if the final term to verify
   is non linear.


   Takes a Hoare triple (pre,prog,post) and verifies if
   the program satisfies its specification by
   symbolic execution using a SMT solver.

   The output is a "if then else" term where
     - conditions are conditions that were not reduced to constant
       during symbolic execution
     - values are outcome
        (i.e RESULT, ERROR or TIMEOUT followed by
        the final state value)

   Symbolic execution prints a trace of the calls to the
   SMT solver.
   It also displays some information (stored in global
   variables):
     * nbPath is the number of feasible paths that have
       been explored during symbolic execution
     * nbResolvedCond is the number of conditions that
       have been evaluated to constants by function EVAL
     * SMTtime is the total SMT solving time
     * CSPtime is the total SMT solving time
     * METIStime is the time spent in HOL trying to solve term using
       METIS tactic
     * SIMPtime is the time spent in HOL trying to solve term using
       simplification


   Functions in term2yices.ml generate the yices input syntax for
   a term.
   extSolvSMT in extSMTSolver (resp. extSolv.extSolvTimeoutFormat in extSol)
   call the SMT (resp. constraint) solver.

   Need to have yices intalled on the machine and to have defined
   an environment variable called YICES_EXEC that points to yices
   executable on the computer.

  ========================= execSymbSMT.ml ===================== *)




(* ======================== algorithm ========================

Algorithm for symbolic execution of a
Hoare triple (pre,prog,post)
-------------------------------------

Let (pre, path, state1,state2, post) be Boolean terms that represent:
- the precondition: a lambda expression on state1
- the current path
- state1: the initial state (before program execution)
- state2: the current state  (after execution of the current path)
- the postcondition: a lambda expression on state1 and state2 which expresses
  a relation between state before execution and state after

Let l be a list of terms that represent the instructions
of prog in the opSem syntax.
Let valPre be the precondition evaluated on state1
and valPost be the postcondition evaluated on state1 and state2.

We assume that we have two functions:
  - testPath:bool that tests if a path is feasible
  i.e (valPre /\ path) has a solution
  - verifyPath:outcome that verifies the correctness of the
  path
  i.e if (valPre /\ path /\ ~valPost) has NO solution
  then returns the outcome (RESULT state)
  else returns the outcome (ERROR errorState) where errorState
  contains the errors that have been found.


The symbolic execution is a deep first search algorithm
that covers feasible paths only.
It starts with an initial symbolic state
where all variables in the program have symbolic values,
the list of instructions of prog and an initial empty path
(i.e term ``T``).
Variable n is the allowed number of steps and res is
an initial empty list that will contain the result.


symbExec(pre,path,l,st1,st2,n,post,res) =

- if l=[]
  then the end of a path has been reached so
       add the result (path,verifyPath(pre,path,st1,st2,post))
       to res
- else
    * if n=0
      then this path leads to a timeout so add the result
           (path,(TIMEOUT st)) to res
    * else
       let l = [i1,l']
       - if i1 is not a control instruction
         then call "STEP1" to compute the next state st'
         according to the small step semantics.
         Then call execSymb(pre,path,l',st1,st',n-1,post,res)
       - else
            Let cond be the condition of i1
            * evaluate cond on the current state
              using the semantics of Boolean expressions
              (i.e the HOL definition "beval")
            * if it is a constant (T or F)
              then take the corresponding path
            * else
                - call testPath(pre,st1,path/\cond,state) to know
                  if cond is possible
                - if it is possible, take the corresponding
                  path in the program
                - call testPath(pre,st2,path/\~cond,state) to
                  know if the NEGATION of cond is possible
                - if it is possible, take the corresponding
                  path in the program

Taking a path in the program depends on the type of the
control instruction.

If the control instruction i1 is (Cond c i_if i_else)
then:
  - if c is ``T`` or possible then taking the path
    is a call to
       execSymb(pre,path/\c,[i_if,l'],st1,st2,n,post,res)
  - else a call to
       execSymb(pre,path/\~c,[i_else,l'],st1,st2,n,post,res)

If the control instruction i1 is (While c i)
then:
  - if c is ``T`` or possible then taking the path
    is a call to
       execSymb(pre,path/\c,[i,(While c i1)],st1,st2,n,post,res)
  - else a call to
       execSymb(pre,path/\~c,l',st1,st2,n,post,res)


 ======================== algorithm ===========================
*)


(* ============== Proof at the end of a path ==================
Let valPre be the precondition evaluated on state1
and valPost be the postcondition evaluated on state1 and
state2.
Path is the accumulated path where each condition has been
evaluated on the current state.

At the end of each path we must show that:
   (valPre/\path)==>valPost
This is done by showing that
   (valPre/\path)/\~valPost
is false.

The current version performs this proof as follows:

1. Compute the negation of the postcondition
   by propagating De Morgan's laws at one level using
   the conversion rule:

   NOT_CONJ_IMP_CONV ``~((A1 ==> B1)/\ ... /\(An ==> Bn))``=
      |- (A1 /\ ~B1) \/ ... \/ (An /\ ~Bn)

   Assume we have obtained a disjunction
     np1 \/ np2 \/ ... \/ npi

2. Distribute this disjunction on (path/\pre/\state)
   to get:
           path /\ pre /\ state /\ np1
    \/     path /\ pre /\ state /\ np2
    \/     ...
    \/     path /\ pre /\ state /\ npi

Then for each term dk = (path/\pre/\state/\npk):

3. Try to refute dk using METIS as follows:

   val IMP_F_IS_F =
      METIS_PROVE [] ``!P. (!Q. P ==> Q) ==> (P = F)``;
   fun refute tm =
     let val th = prove(``!Q. ^tm ==> Q``, RW_TAC std_ss [])
   in
     MP (SPEC tm IMP_F_IS_F) th
   end;

4. If METIS fails (i.e raises a HOL_ERR) then try to simplify
   term dk with SIMP_CONV arith_ss and OMEGA_CONV

5. Rebuild the disjunction from terms dk which have been
   simplified in step 3 or 4.
   Eliminate F from this disjunction using rule
      F \/ t = t

6. If the final disjunction is not equal to F then call
   the external solver.
   The external solver successively builds and solves
   a system for each term of the final disjunction.


Remarks:
  - Step 1 is useful if the postcondition is a conjunction
    of specification cases (such as in tritype). It allows
    to avoid disjunctions in the final system.
  - If the program is not correct, then at least one term
    dk doesn't reduce to F. In this case, METIS and SIMP_CONV
    will fail but the constraint solver will be efficient to
    find the error since the constraint system has a solution.

 ================= end of the path =======================
*)

(* simpTools contains some simplification tools to rewrite
             pre and post conditions.
             It also contains primitive functions "nextState"
             "nextInst" and "evalCond" that executes the semantics
   stateTools contains tools to manipulate states built as finite maps
*)

open HolKernel Parse boolLib
     newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory stringLib
     simpTools stateTools extSMTSolver;


(* -------------------------------------------- *)
(* Global variables and functions to build the solution:
   - SMT solving time information
   - number of conditions that have been evaluated as
     constants using EVAL
   - number of feasible paths that have been explored
*)
(* -------------------------------------------- *)

(* global variable to know if there was an error *)
val nbError = ref 0;

fun incNbError() =
   nbError := !nbError + 1;

(* global variable to know if there was a timeout *)
val nbTimeout = ref 0;

fun incNbTimeout() =
   nbTimeout := !nbTimeout + 1;


(* -------------------------------------------- *)
(* global variable and functions to manage
   time of SMT calls *)
(* -------------------------------------------- *)

val SMTtime= ref 0.0;

fun incSMTTime(t) =
   SMTtime := !SMTtime + t;


(* -------------------------------------------- *)
(* global variable and functions to manage
   time of CSP calls *)
(* -------------------------------------------- *)

val CSPtime= ref 0.0;

fun incCSPTime(t) =
   CSPtime := !CSPtime + t;

(* -------------------------------------------- *)
(* global variable and functions to know
   how many paths were verified using the SMT solver *)
(* -------------------------------------------- *)

val SMTSolvedPath= ref 0;

fun incSMTSolvedPath() =
   SMTSolvedPath := !SMTSolvedPath + 1;

(* -------------------------------------------- *)
(* global variable and functions to know
   how many paths were verified using the constraint solver *)
(* -------------------------------------------- *)

val CSPSolvedPath= ref 0;

fun incCSPSolvedPath() =
   CSPSolvedPath := !CSPSolvedPath + 1;


(* global variable and functions to manage
   the number of paths *)
(* -------------------------------------------- *)

val nbPath= ref 0;

fun incPath() =
   nbPath := !nbPath + 1;

(* global variable and functions to manage
   the number of conditions that have been tested *)
(* -------------------------------------------- *)

val nbCond= ref 0;

fun incNbCond() =
   nbCond := !nbCond + 1;

(* global variable and functions to manage
   the number of conditions that have been resolved
   using EVAL *)
(* -------------------------------------------- *)

val nbEvalCond = ref 0;

fun incEvalCond() =
    nbEvalCond:= !nbEvalCond + 1;

(* global variable and functions to manage
   the number of unfeasible paths *)
(* -------------------------------------------- *)

val nbUnfeasiblePath = ref 0;

fun incUnfeasiblePath() =
    nbUnfeasiblePath:= !nbUnfeasiblePath + 1;


(* global variable and functions to manage
   the number of paths that have been proved
   using METIS *)
(* -------------------------------------------- *)

val nbMETISPath = ref 0;

fun incMETISPath() =
  nbMETISPath:= !nbMETISPath + 1;

(* global variable and functions to manage
   the number of paths that have been proved
   using SIMP_CONV and COOPER *)
(* -------------------------------------------- *)

val nbSIMPPath = ref 0;

fun incSIMPPath() =
  nbSIMPPath:= !nbSIMPPath + 1;


(* global variable that contains the variables of the program
   and is used to make existential formula *)
val programVars = ref [];
(* programVars is computed by function setVars taht is defined
   with function makeState *)
fun resetProgramVars() =
     programVars:=[];

(* To set the variables of the program.
    Used to make existential terms
    This function is called in stateTools when making the state
*)
fun setVars vars =
   map
    (fn v =>
      let val s = fromHOLstring v
      in
       if stateTools.isArrayLength v
       then programVars:= [mk_var(s,``:num``)] @ !programVars
       else programVars:= [mk_var(s,``:int``)] @ !programVars
      end
    )
   vars;


(* to reset the global variables at the end of an execution *)
fun resetAll() =
  (SMTtime:=0.0;
   SMTSolvedPath:=0;
   CSPtime:=0.0;
   CSPSolvedPath:=0;
   nbError:=0;
   nbTimeout:=0;
   nbPath:=0;
   nbCond:=0;
   nbEvalCond:=0;
   nbUnfeasiblePath:=0;
   nbMETISPath:=0;
   nbSIMPPath:=0
  );



(*================================================== *)
(* functions to do symbolic simplifications on terms *)
(*================================================== *)

(* Function to existentially quantify a term *)
(* ----------------------------------------- *)
fun existQuantify tm =
  list_mk_exists(!programVars,tm);


(* functions to simplify each sub-term of disjunction *)
(* -------------------------------------------------- *)

(* PRE: l is a list of terms
   POST: the list where each term has been simplified
         using SIMP_CONV std_ss (or arith_ss)*)
fun simplifyDisjunct l =
  map (fn t =>
       (print ("simplify disjunct " ^ term_to_string(t) ^"\n");
        getThm (SIMP_CONV arith_ss  [] t))
       )
      l;

(* PRE: l is a list of simplified terms
   POST: the disjunction (s1\/s2\/...\/sp) where
         si are terms which are not constant *)
fun mkDisjFromList l =
  let val (h,t) = (hd(l) ,tl(l));
   in
     if (length l) = 1
     then h
     else
       if (is_const(h))
       then
	 if (h=``T``)
	 then h
         else mkDisjFromList t
       else mk_disj(h,mkDisjFromList t)
   end;


(* -------------------------------------------------- *)
(* Functions to build the term to be verified
   i.e that will be simplified
   with HOL or passed to the constraint solver.

   Takes the negation of the postcondition using
   NOT_CONJ_IMP_CONV => gives a disjunction
   d = d1 \/ d2 \/ ... \/dn.
   Takes the precondtion, the current path, the term
   that represents the current state: term of the form
   c= c1 /\ c2 /\ ... /\ cp.
   Then distributes d on c and simplifies each
   subterm using SIMP_CONV arith_ss  [] to obtain
    simp(c1 /\ c2 /\ ... /\ cp /\d1) \/
    simp(c1 /\ c2 /\ ... /\ cp /\d2) \/ ... \/
    simp(c1 /\ c2 /\ ... /\ cp /\dn)
   Also simplifies the final disjunction if there is a
   constant T or F.
*)
(* -------------------------------------------------- *)



local

(* function to eliminate  ``F`` from disjunctions. *)
fun simplDisj t =
  let val orthm = EVAL t;
  in
    getThm orthm
end;



(* Use RW_TAC to refute a term *)
fun refute tm =
 let val th = prove(``!Q. ^tm ==> Q``, RW_TAC std_ss [])
 in
  MP (SPEC tm IMP_F_IS_F) th
 end;



(* version that works with integers *)
(* could also try
(SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC]
THENC OMEGA_CONV ) c;
*)
fun distributeAndRefute tm ld =
  map
   (fn t =>
      let val c = mk_conj(tm,t)
          val fc = existQuantify c ;
      in
         (print("\nTerm to be refuted with METIS "
                ^ term_to_string(fc) ^ "\n");
	  refute fc;
          incMETISPath();
          ``F``
         )
         handle HOL_ERR s =>
           (print "METIS failed\n";
            print("Trying to simplify with SIMP_CONV and COOPER\n");
           let
             val res = getThm (SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] fc)
             in
              (incSIMPPath();
               res
              )
             end
            )
      end
      handle UNCHANGED =>
        (print "Term unchanged\n";
        mk_conj(tm,t))
   )
   ld;


in


 (* Verify a term with HOL at the end of a path *)
fun verifyTerm tm post =
  let val np =  takeNegPost post;
    val listDisj = strip_disj(np);
    val disj = mkDisjFromList(distributeAndRefute tm listDisj)
   in
      ((* print "VerifyTerm\n";
       print_term disj;*)
       simplDisj(disj)
      )
   end

   handle HOL_ERR s =>
       (print ("HOL_ERR in makeTermToVerify\n");
	print("tm is " ^ term_to_string(tm));
        print("post is " ^ term_to_string(post));
        ``T``
       )

end;



(* ------------------------------------------------- *)
(* to test if a path is possible                     *)
(* with a current precondition and a current state   *)
(* ------------------------------------------------- *)
(*  test if (pre /\ path) is satisfied for some values of
    the current state

  Use function extSolvTimeout in extSolv.sml
  to call the solver with a timeout of 100ms.

  If there is a timeout or if the solver showed that the
  condition is not possible, try to prove
  the formula using
  SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] t *)

(* --------------------------------------------------- *)
local
fun pathInfo b tm time =
  if b =``T``
  then
    (print "======================\n";
     print( "Taking path " ^ term_to_string(tm) ^ "\n");
     print "======================\n";
     (true,time)
    )
  else
    (print "======================\n";
     print ("Path " ^ term_to_string(tm) ^ " is impossible\n");
     print "======================\n";
     incUnfeasiblePath();
     (false,time)
    );

in


fun testPath name pre path st =
  (* TODO: use mkSimplConj or modify term2xml to handle x /\T *)
 let    val conj = mk_conj(pre,path)
   in
   (print "======================\n";
    print "Testing feasability\n";
    print "======================\n";
    let val (th,time) = extSolvSMT name conj
      val res = getThm th
    in
     if (res = ``F``)
     then
       (* try to show that the condition is impossible
          using SIMP_CONV*)
       let  val existsConj = existQuantify conj
         val thSimp = SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] existsConj
         val resSimp=  getThm thSimp
       in
          pathInfo resSimp path time
       end
       handle UNCHANGED  =>
        (* It was not possible to show the theorem in HOL
            so return the theorem computed with the
            external solver *)
         (print "Path was solved using external solver\n";
          pathInfo res path time
         )
     else
       (print "======================\n";
	print( "Taking path " ^ term_to_string(path) ^ "\n");
	print "======================\n";
	(true,time)
       )
     end
(*     handle ExtSolverTimeout =>
       let val existsConj = existQuantify conj
         val thSimp = SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] existsConj
         val resSimp=  getThm thSimp
       in
         (print "Timeout in solver, testing path with SIMP_CONV\n";
          pathInfo resSimp path ((Real.fromInt timeout)*0.001)
         )
       end
       handle UNCHANGED  =>
        (print "======================\n";
	 print "Path unsolved\n";
         print( "Taking path " ^ term_to_string(path) ^ "\n");
	 print "======================\n";
         (true,((Real.fromInt timeout)*0.001))
        )
*)
   )
   end;
end;


(* ------------------------------------------ *)
(* to verify the program at the end of a branch *)
(* ------------------------------------------ *)

(* pre and post are precondition and postcondition,
   path is the current path ,
   st is the state of the variables i.e the final values
      of the variables computed by symbolic execution
      along the path

Let evalPost be the post condition evaluated on the final state.

returns a RESULT outcome
  if pre /\ path /\ ~evalPost
  has no solution
  which means that (pre /\ path) => evalPost
  is true

returns an ERROR outcome otherwise
*)

(* format of integers with CSP solver *)
val CSP_FORMAT = 17;
(* timeout with CSP solver *)
val CSP_TIMEOUT = 100000;

(* ------------------------------------------ *)
local

fun printCorrect() =
  (print "======================\n";
   print "Program is correct on this path\n";
   print "======================\n"
);

fun printError() =
  (print "======================\n";
   print "An ERROR has been found\n";
   print "======================\n"
);

(* call the SMT solver and the constraint solver if
   there is a non linear expression *)
fun externalSolvers name tm =
  let val (r,t) = extSolvSMT name tm
    val res = getThm(r)
    in
      (incSMTTime(t);
       if res=``F``
          then incSMTSolvedPath()
          else ();
       (r,"SMT")
      )
    end
    handle YICES_COMPILEError =>
      (print "Term contains non linear expressions, calling constraint solver\n";
       let val (r,t) = extSolv.extSolvTimeoutFormat name tm CSP_TIMEOUT CSP_FORMAT
         val res = getThm(r)
         in
           (
            incCSPTime(t);
            if res=``F``
               then incCSPSolvedPath()
               else ();
            (r,"CSP")
           )
         end
       );


(* to get a counter-example when the final term has
been reduced to T. PRECOND: the solution is stored in name.res

  name is the name of the file that contains the result,
  s is the current state where error values must be substituted
  solver is either "SMT" or "CSP" depending on the solver that
    has been used to solve the term
 *)
fun getCounterExample name s solver =
  let val errorState =
          if solver = "SMT"
	  then makeErrorState name s
          else extSolv.makeErrorState name s
  in
      (printError();
       incNbError();
       ``ERROR ^errorState``
      )
  end;


in



(* ---------------------------------------------- *)
(* To verify the system at the end of a path.
   Try first to solve the term with HOL, if it fails
   call external solver: SMT solver and constraint solver when
   there is a non linear expression               *)

(* st1 is initial state (before program execution)
   st2 is final state (after program execution)   *)
(* ---------------------------------------------- *)

fun verifyPath name pre st1 st2 post path =
  let val conj = mk_conj(pre,path);
    val st2' = pruneState(st2);
    val po = evalPost post st1 st2'
    (* verify the term with HOL using specific rule to compute
       the negation of post *)
    val tm = verifyTerm conj po
    in
     (* if tm is a constant and its value is F
        the program is correct *)
     if is_const(tm)
     then
       if tm=``F``
       then
          (printCorrect();
           ``RESULT ^st2'``
        )
       else
         (* there is an error, searching solution with CSP *)
         (print "======================\n";
          print "HOL has shown that path is NOT correct\n";
          print "Searching counter-example with external solver\n";
          let val tmKO = mk_conj(conj,takeNegPost(po))
             val  (th,solver) = externalSolvers name tmKO
             val res = getThm th
	  in
          if res = ``F``
          then
            ( print "PROBLEM: external solver has not find a counter-example\n";
	      ``ERROR ^st2'``
	    )
          else
            (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP
               when solving pre /\ state /\ path /\ ~post *)
            getCounterExample name st2' solver
          end
        )
     else
         (* tm has not been simplified to T nor F so
            calling the external solver *)
         (print "======================\n";
	  print "HOL was unable to verify the path\n";
	  print "======================\n";
	  let val (th,solver) = externalSolvers name tm
             val res = getThm th
	  in
            if res = ``F``
            then
		( printCorrect();
		  ``RESULT ^st2'``
		)
            else
	     (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP
               when solving pre /\ state /\ path /\ ~post *)
	        getCounterExample name st2' solver
          end
         )
    end
end;



(* --------------------------------------------------
   main functions to symbolically execute a program
   using the small step semantics and calling a SMT
   -------------------------------------------------- *)

local

(* to test if the term that represents the first instruction
   is a condition *)
fun is_condition tm =
let val (opr,_) = strip_comb(tm)
  in
   opr=``Cond``
  end;

(* to test if the term that represents the first instruction
   is a while *)
fun is_while tm =
let val (opr,_) = strip_comb(tm)
  in
   opr=``While``
  end;


(* to get the instruction name *)
fun instName tm =
let val (opr,_) = strip_comb(tm)
  in
   opr
  end;




in

(*------------------------------------------
 Main function to verify a Hoare triple
   (pre, prog, post) by symbolic execution
   l: list of instructions in opSem syntax
      that correspond to prog
   st1: initial state
   st2: current state
   n: number of steps that can still be performed

Use functions:
  - STEP1 to compute the next state if the instruction
    is not a control instruction
  - execSymbCond (resp. execSymbWhile) to do the symbolic
    execution when the first instruction is a conditional
    instruction (resp. a while instruction)
  - verifyPath at the end of a path (i.e when the instruction
    list is empty) to verify if
        (pre /\ path) ==> post on the current state
  - testPath to test if a condition is possible on a path
    i.e if
        (pre /\ path /\ cond)
    has a solution
------------------------------------------*)


fun execSymb name pre (l,st1,st2,n) post path=
 if listSyntax.is_nil(l)
 then
     (*end of a path
       test if (pre /\ path) ==> post
       on the current state
     *)
     (print "======================\n";
      print "End of path\n";
      print( "    " ^ term_to_string(path) ^"\n");
      print "======================\n";
      (*print ("st2 " ^ term_to_string(st2));*)
      let val r =  verifyPath name pre st1 st2 post path
        in
          (incPath();
           r
          )
        end
     )
 else
   if n=0
   (* no more steps, so add a TIMEOUT outcome *)
   then let val st2' = pruneState(st2)
        in
          ``TIMEOUT ^st2'``
        end
   else
     (* takes the first instruction *)
     let val inst = snd(dest_comb(fst(dest_comb(l))))
      in
       (* conditional *)
       if is_condition(inst)
       then execSymbCond name pre (l,st1,st2,n) post path
       else
         (* while *)
         if is_while(inst)
	 then execSymbWhile name pre (l,st1,st2,n) post path
         (* instruction is not a conditional *)
         (* call STEP1 to compute the next state and continue *)
         else
(*          (print("instruction: " ^ term_to_string(instName(inst)) ^"\n");*)
          let val (newList,newState) = simpTools.nextStep l st2;
           in
             execSymb name pre (newList,st1,newState,(n-1)) post path
           end
(*) *)
      end
     handle HOL_ERR t  =>
       let val {origin_structure = or,origin_function=f,message=m } = t
       in
       (print("Hol error\n");
        print(or ^ "\n");
        print(f ^ "\n");
        print(m ^ "\n");
        ``F``
        )
       end


(* -----------------------------------------------------
   Function to symbolically execute a "Cond" instruction.

   The first instruction of list l has the form "Cond c i1 i2".
   If c evaluates to a constant (T or F)
   on the current state using function "EVAL", then take
   the corresponding branch
   Else, call the solver to know if the condition is possible
   with the current precondition, current path and current state.
      If it is possible, take the "If" branch
      and then try the "else" branch.
      If the condition is not possible, only try the else branch

Use function testPath to know if the condition is possible
with the current precondition, path and state.
Function testPath calls the SMT.
  ----------------------------------------------------- *)


and execSymbCond name pre (l,st1,st2,n) post path =
 (incNbCond();
  let val (_,comb) = strip_comb(l)
    (* first instruction COND *)
    val instCond = (el 1 comb)
    val listInst = (el 2 comb)
   (* save current state to perform  symbolic execution
      of else part with the state before the conditionnal *)
    val saveState = st2;
    val (_,listCond) = strip_comb(instCond)
    val cond = (el 1 listCond)
    val iftm = (el 2 listCond)
    val elsetm = (el 3 listCond)
    (* evaluate the condition on the current state *)
    val termCond = simpTools.evalCond cond st2;
   in

   (* if the condition has been evaluated to a constant
      by EVAL, then takes the decision according to its value *)
   if (is_const(termCond))
   then
    (incEvalCond();
     if (termCond=``T``)
     then
      let val nextList =  listSyntax.mk_cons(iftm,listInst)
      in
        (print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is TRUE on the current state, ");
	 print ("taking this path\n");
         execSymb name pre (nextList,st1,st2,n) post path
        )
       end
    else
      let val nextList =listSyntax.mk_cons(elsetm,listInst)
       in
       ( incUnfeasiblePath();
         print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is FALSE on the current state, ");
	 print ("taking the other path\n");
         execSymb name pre (nextList,st1,st2,n) post path
        )
     end
     )
   else
   (* the condition has not been simplified by EVAL.
      Use the solver to know if the condition is
      possible on the current path
    *)
   let val newPath = mkSimplConj path termCond;
      val (ok,tIf) = testPath name pre newPath st2;
      val nextListIf = listSyntax.mk_cons(iftm,listInst);
      val nextListElse = listSyntax.mk_cons(elsetm,listInst);
      val resIf=
         if (ok)
         (* Add the condition to the current path
         and do symbolic execution of if part*)
         then execSymb name pre (nextListIf,st1,st2,n) post newPath
         else
           (print "\nPath is impossible, HOL must be called\n";
            ``F``);
      val newPathElse = mkSimplConj path (mk_neg termCond);
      val (elseOk,tElse) = testPath name pre newPathElse saveState;
      val resElse =
          if (elseOk)
         (* do  symbolic execution on else part *)
         (* and add ~cond to the current path *)
          then execSymb name pre (nextListElse,st1,saveState,n) post newPathElse
          else ``F``
       in
           (incSMTTime(tIf);
            incSMTTime(tElse);
	    if ok
	    then
		if elseOk
		then ``if ^termCond then ^resIf else ^resElse``
		else resIf
	     else resElse
           )
        end
end)




(* -----------------------------------------------------
   Function to symbolically execute a "While" instruction.

   The list l has the form [While c i,l'].
   If the condition evaluates to a constant (T or F)
   on the current state using function "EVAL":
      - if c is T then call STEP1 to computes the next state
        s' after execution of i and continue symbolic
        execution with s' and instruction list l
      - if c is false, then continue symbolic execution
        with l'
   Else, call the solver to know if the condition is possible
   with the current precondition, current path and current state.
      - If it is possible, then enter the while
      and then try the exit condition of the loop.
      - If the condition is not possible, only try the
      exit branch.

Use function testPath to know if the condition is possible
with the current precondition, path and state.
Function testPath calls the SMT.
  ----------------------------------------------------- *)

and execSymbWhile name pre (l,st1,st2,n) post path  =
  (incNbCond();
   let val (_,comb) = strip_comb(l)
    (* first instruction: a While *)
    val instCond = (el 1 comb)
    (* other instructions *)
    val tail = (el 2 comb)
   (* save current state to perform  symbolic execution
      of exit part with the state before the while *)
    val saveState = st2;
    val (_,listCond) = strip_comb(instCond)
    (* condition *)
    val cond = (el 1 listCond)
    (* instruction block of the loop *)
    val block = (el 2 listCond)
    (* evaluate the condition on the current state *)
    val termCond = simpTools.evalCond cond st2;
   in
   (* if the condition has been evaluated to a constant
      by EVAL, then takes the decision according to its value *)
   if (is_const(termCond))
   then
    (incEvalCond();
     (* enter the loop: do symbolic execution of list
        [block,l] *)
     if (termCond=``T``)
     then
      let val nextList =  listSyntax.mk_cons(block,l)
      in
        (print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is TRUE on the current state, ");
	 print ("entering the loop\n");
         execSymb name pre (nextList,st1,st2,n) post path
        )
       end
    else
      (* exit the loop: do symbolic execution of
         the tail of instruction list *)
       ( incUnfeasiblePath();
         print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is FALSE on the current state, ");
	 print ("exiting the loop\n");
         execSymb name pre (tail,st1,st2,n) post path
        )
     )
   else
   (* the condition has not been simplified by EVAL.
      Use the solver to know if the condition is
      possible on the current path
    *)
   let  val newPath = mkSimplConj path termCond;
     val (ok,tLoop) = testPath name pre newPath st2;
     val nextListLoop = listSyntax.mk_cons(block,l);
     val resLoop =
       if (ok)
       (* Add the condition to the current path
        and enter the loop: do symbolic execution of [block,l] *)
       then execSymb name pre (nextListLoop,st1,st2,n) post newPath
       else ``F``
     val newPathExit = mkSimplConj path (mk_neg termCond);
     val (elseOk,tExit) = testPath name pre newPathExit saveState;
     (* exit the loop: do  symbolic execution on the tail of
        the list and add ~cond to the current path *)
     val resExit =
         if (elseOk)
         then execSymb name pre (tail,st1,saveState,n) post newPathExit
         else ``F``
       in
         (incSMTTime(tLoop);
          incSMTTime(tExit);
	  if ok
	  then
	      if elseOk
	      then ``if ^termCond then ^resLoop else ^resExit``
	      else resLoop
	  else resExit
	 )
   end

end)

end;


(* --------------------------------------------------
   main function to verify a Hoare triple by symbolic
   execution
   -------------------------------------------------- *)

(* to evaluate pre or post condition on an initial state *)
local


fun plural n =
  if n>1
  then "s have been "
  else " has been ";


(* to print statistics global variables *)
fun printStatistics() =
    (print "===============================\n";
     if not (!nbTimeout=0)
     then print "TIMEOUT\n"
     else
         if !nbError = 0
         then print "PROGRAM IS CORRECT\n"
         else print(int_to_string(!nbError) ^ " ERROR" ^ plural(!nbError)
		    ^ "found\n");
     print (int_to_string(!nbCond) ^ " condition"
            ^ plural(!nbCond) ^ "tested.\n");
     print (int_to_string(!nbEvalCond) ^ " condition"
            ^ plural(!nbEvalCond) ^ "solved" ^ " by EVAL.\n");
     print (int_to_string(!nbUnfeasiblePath) ^ " condition"
            ^ plural(!nbUnfeasiblePath) ^ "shown impossible.\n\n");
     print (int_to_string(!nbPath) ^ " feasible path" ^ plural(!nbPath)
            ^ "explored.\n");
     if !SMTSolvedPath=0 andalso !CSPSolvedPath=0
     then
        print "All correct paths were verified in HOL.\n"
     else
        (print(int_to_string(!SMTSolvedPath)  ^ " path" ^ plural(!SMTSolvedPath)
                ^ "shown correct with the SMT solver\n");
         print(int_to_string(!CSPSolvedPath)  ^ " path" ^ plural(!CSPSolvedPath)
                ^ "shown correct with the CSP solver\n"));
     print (int_to_string(!nbMETISPath) ^ " subterm"
            ^ plural(!nbMETISPath) ^ "solved with refute and METIS.\n");
     print (int_to_string(!nbSIMPPath) ^ " subterm"
            ^ plural(!nbSIMPPath) ^ "solved with SIMP_CONV and COOPER.\n\n");
     print ("Total time spent with the SMT solver: "
	    ^ Real.toString(!SMTtime) ^ "s.\n");
     print ("Total time spent with the CSP solver: "
	    ^ Real.toString(!CSPtime) ^ "s.\n");
     print "===============================\n"
    );


in


(* Do symbolic execution
   The symbolic state is built from variables in the program
 *)
fun execSymbWithSMT name spec n =
  let  val (_,args) = strip_comb spec;
   val (pre,prog,post) = (el 1 args, el 2 args, el 3 args);
   val (listVars,s) = makeState prog;
   val evalP = evalPre pre s
   (* val ss = computeStateFromPre evalP s*)
  in
     (resetAll(); (* reset global variables *)
      setVars(listVars);
      let val res =
        execSymb name
                 evalP
                 (``[^prog]``,s,s,n)
                 post
                 ``T``
      in
        (printStatistics();
         resetProgramVars(); (* reset the list of variable used to existentially quantify terms *)
	 res)
      end
     )
   end
     handle HOL_ERR t  =>
       let val {origin_structure = or,origin_function=f,message=m } = t
       in
       (print("\n Hol error\n");
        print(or ^ "\n");
        print(f ^ "\n");
        print(m ^ "\n");
        ``F``
        )
       end

end;


