
(* ========================= execSymb.sml =====================

   Version of execSymb.ml for compiling.

   Takes a Hoare triple (pre,prog,post) and verifies if
   the program satisfies its specification by 
   symbolic execution using a CSP solver.

   The output is a list of pairs (path,result)
   where 
     - path is a term which corresponds to 
       a path that has been covered into the program 
       during symbolic execution
     - result is an outcome 
        (i.e RESULT, ERROR or TIMEOUT followed by
        the final state value)

   Symbolic execution prints a trace of the calls to the
   CSP solver.
   It also displays some information (stored in global 
   variables): 
     * nbPath is the number of feasible paths that have 
       been explored during symbolic execution
     * nbResolvedCond is the number of conditions that
       have been evaluated to constants by function EVAL
     * CSPtime is the total CSP solving time.
   
   Calls to CSP solvers are decomposed into two steps:
     - Write XML trees that represent the current execution 
       status in xml files (in term2xml/xml).
       This is done by functions in term2xml.
     - Read the XML files to build and then solve the corresponding
       CSP. This is done by Java classes in term2xml/java.
       
   Functions in term2xml.ml generate XML trees which represent 
   a term. 
   XML files are written in term2xml/xml.
   See term2xml/xml/term.dtd for the syntax of XML trees.

   Java classes in term2xml/java take XML files in
   term2xml/xml and build and solve the corresponding
   CSP.
   Let tm be the term that has been written as XML file and
   read by Java classes to build a CSP.
   If there is a solution s to the CSP, then ?s.tm
   is a theorem
   else !s.~tm is a theorem. 
   

Examples of symbolic execution can be found at the end of this file.
Need to load: newOpsemTheory (file loadNewOpsem.ml), the examples
(file loadExamples), term2xml.ml and this file execSymb.ml.
Need to have a java virtual machine.

  ========================= execSymb.ml ===================== *)




(* ======================== algorithm ========================

Algorithm for symbolic execution of a 
Hoare triple (pre,prog,post)
-------------------------------------

Let (pre, path, state, post) be Boolean terms that represent:
- the precondition
- the current path
- the current state: a conjunction of equalities
  (var_i = val_i) where var_i is a variable and 
  val_i a numeral term which gives its current value
- the postcondition
Let l be a list of terms that represent the instructions 
of prog in the opSem syntax.

We assume that we have two functions:
  - testPath:bool that tests is a path is feasible 
  i.e (pre /\ path /\ state) has a solution
  - verifyPath:outcome that verifies the correctness of the
  path
  i.e if (pre /\ path /\ state /\ ~post) has NO solution
  then returns the outcome (RESULT state)
  else returns the outcome (ERROR errorState) where errorState
  contains the errors that have been found.

The symbolic execution returns a list of couples (path,result)
where path is a path covered during symbolic execution and 
result is the outcome along this path (i.e RESULT, ERROR or 
TIMEOUT followed by the final state value).

The symbolic execution is a deep first search algorithm 
that covers feasible paths only.
It starts with an initial symbolic state
where all variables in the program have symbolic values,
the list of instructions of prog and an initial empty path 
(i.e term ``T``).
Variable n is the allowed number of steps and res is
an initial empty list that will contain the result.


symbExec(pre,path,l,st,n,post,res) =

- if l=[] 
  then the end of a path has been reached so
       add the result (path,verifyPath(pre,path,st,post))
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
         Then call execSymb(pre,path,l',st',n-1,post,res)
       - else
            Let cond be the condition of i1 
            * evaluate cond on the current state
              using the semantics of Boolean expressions
              (i.e the HOL definition "beval")
            * if it is a constant (T or F)
              then take the corresponding path
            * else 
                - call testPath(pre,path/\cond,state) to know 
                  if cond is possible
                - if it is possible, take the corresponding 
                  path in the program
                - call testPath(pre,path/\~cond,state) to 
                  know if the NEGATION of cond is possible 
                - if it is possible, take the corresponding 
                  path in the program

Taking a path in the program depends on the type of the
control instruction.

If the control instruction i1 is (Cond c i_if i_else)
then:
  - if c is ``T`` or possible then taking the path 
    is a call to
       execSymb(pre,path/\c,[i_if,l'],st,n,post,res)
  - else a call to
       execSymb(pre,path/\~c,[i_else,l'],st,n,post,res)

If the control instruction i1 is (While c i)
then:
  - if c is ``T`` or possible then taking the path 
    is a call to
       execSymb(pre,path/\c,[i,(While c i1)],st,n,post,res)
  - else a call to 
       execSymb(pre,path/\~c,l',st,n,post,res)


 ======================== algorithm ===========================
*)


(* ============== Proof at the end of a path ==================

At the end of each path we must show that:
   (pre/\path/\state)==>post
This is done by showing that
   (pre/\path/\state)/\~post
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
   term dk with SIMP_CONV arith_ss

5. Rebuild the disjunction from terms dk which have been 
   simplified in step 3 or 4. 
   Eliminate F from this disjunction using rule 
      F \/ t = t

6. If the final disjunction is not equal to F then call
   the constraint solver.
   The constraint solver will successively build and solve 
   a CSP for each term of the final disjunction.    
   

Remarks:
  - Step 1 is useful if the postcondition is a conjunction
    of specification cases (such as in tritype). It allows *
    to avoid disjunctions in the final CSP.
  - If the program is not correct, then at least one term
    dk doesn't reduce to F. In this case, METIS and SIMP_CONV 
    will fail but the constraint solver will be efficient to 
    find the error since the constraint system has a solution.

 ================= end of the path =======================
*)


(* -----------------------------------------------------
   Functions written by Mike Gordon to read a solution 
   computed by a CSP 
   -----------------------------------------------------
*)


open HolKernel Parse boolLib
     newOpsemTheory bossLib pairSyntax intLib
     computeLib finite_mapTheory relationTheory stringLib
     term2xml;  (* added as printXML_to_file needed *)

(* Magnus switched to using integers
val _ = intLib.deprecate_int();
*)


(*
open intSyntax;
*)

(* Read a file into a string *)
fun readFileToString file_name =
 let val instream = TextIO.openIn file_name
     val contents = TextIO.inputAll instream
     val _ = TextIO.closeIn instream
 in
  contents
 end;

(* 
Parse a solutions file -- very ad hoc and no error checking! 

 getSolutions : string -> (string * string) list list * real
 getSolutions file_name = ([[("x1","m1"),...,],...,[("y1","n1"),...]], time)

If the solver returns "No solution" then the first component of the
returned pair (a list of lists) is empty.

*)
local 

(* If p(xi)=false (for 1<=i<=n) and p(x)=true, then:
   splitUntil p [x1,...,xn,x,y1,...ym] = ([x1,...,xn],[y1,...,ym])  
*)
val splitUntil =
  let fun splitUntilAux acc p [] = (rev acc,[])
|  splitUntilAux acc p (x::l) = 
  if p(x) then (rev acc,l) 
  else splitUntilAux (x::acc) p l
  in
  splitUntilAux ([] : string list)
end;


(* dest_string_int_pair "(x,n)" --> ("x","n") *)
fun dest_string_int_pair str =
  let val [x,n] = 
    String.tokens (fn c => mem c [#"(",#")",#","]) str
  in
  (x, n)
end

(* Group each solution into a list, returning a list of lists:
   sol_extract 
   [...,"Solution #2",...,"Solution #3",...,"Solution #4",...]
   -->
   [[...],[...],[...],[...]]
 *)
fun sol_extract [] = []
|  sol_extract l  = let val (l1,l2) = splitUntil (String.isPrefix "Solution: ") l
in 
  l1 :: sol_extract l2
end

in

fun getSolutions file_name =
  let val lines = String.tokens (fn c => c = #"\n") (readFileToString file_name)
val solutions = 
  if hd lines = "No solution"
  then []
  else map (map dest_string_int_pair) (sol_extract(tl(butlast lines)))
val sol_time_str = String.extract(last lines, (String.size "Resolution time: "),
				  NONE)
val SOME sol_time = Real.fromString(implode(butlast(explode sol_time_str)))
  in
  (solutions,sol_time)
end

end;

(* End of functions written by Mike Gordon to read a solution 
   of a CSP solver *)
(* -----------------------------------------------------*)


(* function to transform the list of solutions
   as a finite map that can be used as outcome *)
fun addSol st nt vt = 
  ``^st |+ (^nt,Scalar ^vt)``;

fun finiteMapSol l st =
  if null l 
  then st
  else 
    let val (n,v) = (fst(hd(l)),snd(hd(l)));
      val (nt,vt) = (stringSyntax.fromMLstring(n),
                     numSyntax.mk_numeral(Arbnum.fromString(v)));
      val newSt = addSol st nt vt
      in 
        finiteMapSol (tl l) newSt
    end;

(*----------------------------------------------------- *)



(* functions to generate symbolic states *)
(* ------------------------------------- *)

(* take a term that corresponds to a program in opSem syntax
   and build a symbolic state that represents all 
   its variables *)
(* From functions written by Mike Gordon in verifier.ml *)

(* Get set of string terms in a term *)
(* Written by Mike Gordon in verifier.ml    *)
fun get_strings tm =
 if is_string tm
  then [tm] else
 if is_var tm orelse is_const tm
  then [] else
 if is_comb tm
  then union (get_strings(rator tm)) (get_strings(rand tm)) else
 if is_abs tm
  then get_strings(body tm)
  else (print "error in get_strings"; fail());


(* from fun STATE_ELIM written by Mike Gordon in verifier.ml *)
(* takes a list of term representing symbolic values
   of variables (e.g ``("j",j)``) and returns a finite_Map*)
fun makeStateFromPair l = 
  if ((length l) = 1)
  then ``(FEMPTY |+ ^(hd l)) ``
  else
      let 
        val map = makeStateFromPair (tl l);
      in
         ``^map |+ ^(hd l)``
end;

fun makeState spec = 
 let val (_,args) = strip_comb spec;
     val (_,tm,_) = (el 1 args, el 2 args, el 3 args)
     val var_tms = get_strings tm
     val pairs = map 
                  (fn tm => pairSyntax.mk_pair
                      let val v = mk_var(fromHOLstring tm,``:num``)
                      in 
		      (tm,``Scalar ^v``)
			end
		  )
                  var_tms
 in         
   makeStateFromPair pairs
end;



(* -------------------------------------------- *)
(* Global variable and functions to build the solution:
   - CSP solving time information
   - number of conditions that have been evaluated as 
     constants using EVAL 
   - number of feasible paths that have been explored
   - list of outcome for each path in the program
*) 
(* -------------------------------------------- *)


(* global variable and functions to manage
   time of CSP calls *)
(* -------------------------------------------- *)

val CSPtime= ref 0.0;

fun incCSPTime(t) = 
   CSPtime := !CSPtime + t;

(* global variable and functions to manage
   the number of paths *)
(* -------------------------------------------- *)

val nbPath= ref 0;

fun incPath() = 
   nbPath := !nbPath + 1;

(* global variable and functions to manage
   the number of conditions that have been resolved
   using EVAL *)
(* -------------------------------------------- *)

val nbResolvedCond = ref 0;

fun incResolved() = 
    nbResolvedCond:= !nbResolvedCond + 1;

(* global variable and functions to manage
   the number of paths that have been resolved
   using SIMP_CONV and METIS *)
(* -------------------------------------------- *)

val nbResolvedPath = ref 0;

fun incResolvedPath() = 
  nbResolvedPath:= !nbResolvedPath + 1;


(* global variable and functions to manage
   results on the different paths *)
(* -------------------------------------------- *)

val allPathResult = ref [];(*ref [(``T``,``T``)];*)

fun addPath p r =
   allPathResult := [(p,r)] @ !allPathResult;


(* to reset the global variables at the end of an execution *)
fun resetAll() = 
  (CSPtime:=0.0;
   nbPath:=0;
   nbResolvedCond:=0;
   nbResolvedPath:=0;
   allPathResult:=[]
  );
   

(* -------------------------------------------- *)
(* functions to do symbolic simplifications on terms *)
(* -------------------------------------------------- *)
(* function to eliminate  ``T`` from conjunctions. 
   It is required because the current Java implementation
   that takes a XML tree to build the CSP
   doesn't consider Booleans.
   So if precondition is ``T`` then the XML tag is empty
*)
fun mkSimplConj t1 t2 = 
  let val andthm = EVAL ``^t1 /\ ^t2``;
  in 
    snd(dest_comb(concl(andthm)))
end;


(* functions to put a term in DNF and simplify each sub-term *)
(* -------------------------------------------------------- *)

(* PRE: l is a list of terms 
   POST: the list where each term has been simplified 
         using SIMP_CONV std_ss (or arith_ss)*)
fun simplifyDisjunct l =
  map (fn t => 
       (print ("simplify disjunct " ^ term_to_string(t) ^"\n");
        snd(dest_comb(concl(SIMP_CONV arith_ss  [] t))))
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

(* example of exception handling *)
(* to add to functions that use simplifications *)
(*fun essai tm = 
  let  val si = snd(dest_comb(concl(SIMP_CONV arith_ss [] tm)));
 in 
   si
 end
handle UNCHANGED => tm;*)


(* PRE: tm is in DNF *)
(* POST: DNF where each term has been simplified *)
fun simplifyDNF tm =
  if is_disj(tm)
  then mkDisjFromList(simplifyDisjunct(strip_disj(tm)))
  else tm;
  
(* to put a term into Disjunctive Normal Form *)
(* used to speed up the CSP solving *)
fun dnf tm =
 let val thm = SIMP_CONV (std_ss ++ boolSimps.DNF_ss) [] tm;
  in 
    (print ("DNF " ^ term_to_string(tm) ^"\n");
    simplifyDNF(snd(dest_comb(concl(thm)))))
 handle UNCHANGED => tm
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

(*---------------------------------------------------------
Tool for applying De Morgan's laws at the top level to a 
negated conjunction of implications:

NOT_CONJ_IMP_CONV  ``~((A1 ==> B1) /\ ... /\ (An ==> Bn))`` =
 |- (A1 /\ ~B1) \/ ... \/ (An /\ ~Bn)
---------------------------------------------------------*)
fun NOT_CONJ_IMP_CONV tm =
 let val tm1 = dest_neg tm
 in
  if is_imp tm1
   then let val (tm2,tm3) = dest_imp tm1
        in
         SPECL [tm2,tm3] NOT_IMP
        end
   else let val (tm2,tm3) = dest_conj tm1
            val (tm4,tm5) = dest_imp tm2
        in
         CONV_RULE
          (RAND_CONV(RAND_CONV NOT_CONJ_IMP_CONV))
          (SPECL [tm4,tm5,tm3] NOT_IMP_CONJ)
        end
  end;

local 

(* function to eliminate  ``F`` from disjunctions. *)
fun simplDisj t = 
  let val orthm = EVAL t;
  in 
    snd(dest_comb(concl(orthm)))
end;

(* function to take the negation of the postcondition
   using NOT_CONJ_IMP_CONV *)
fun takeNegPost post =
 let val n = mk_neg(post);
   in
     if is_conj(post) orelse is_imp(post)
     then 
     (* build the negation using De Morgan laws at one level *)
        snd(dest_comb(concl(NOT_CONJ_IMP_CONV n)))
     else
       (* case where post is not an implication *)
       n
   end;

(* function to distribute and simplify 
   pre/\path/\state on the conjunction obtained
   from the negation of the postcondition
   terms are simplified using SIMP_CONV std_ss 
   (or arith_ss) *) 

fun distributeAndSimplify tm ld =
  map 
   (fn t => 
      let val c = mk_conj(tm,t)
       in
         (print("term to be simplified with SIMP_CONV " 
                ^ term_to_string(c) ^ "\n"); 
         snd(dest_comb(concl(SIMP_CONV arith_ss [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC] c)))
         )
       end
       handle UNCHANGED => mk_conj(tm,t)
   )
   ld;


(* function to distribute and simplify 
   pre/\path/\state on the conjunction obtained
   from the negation of the postcondition
   terms are proven using METIS 
 *)
fun distributeAndProve tm ld =
  map 
   (fn t => 
      let val c = mk_conj(tm,t)
       in
         (print("term to be proved False with METIS " 
                ^ term_to_string(c) ^ "\n"); 
         METIS_PROVE [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC,NOT_DISJ] ``^c = F``;
         ``F``
         )
       end
       handle HOL_ERR s => 
          (print "METIS failed\n";
           mk_conj(tm,t)
          )
   )
   ld;

(* to distribute and simplify the term using first METIS and then
   SIMP_CONV arith_ss *)

fun distributeProveSimp tm ld =
  map 
   (fn t => 
      let val c = mk_conj(tm,t)
       in
         (print("term to be proved False with METIS " 
                ^ term_to_string(c) ^ "\n"); 
          METIS_PROVE [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC,NOT_DISJ] ``^c = F``;
          ``F``
         )
         handle HOL_ERR s => 
           (print "METIS failed\n";
            print("Trying to simplify with SIMP_CONV " 
                ^ term_to_string(c) ^ "\n"); 
            snd(dest_comb(concl(SIMP_CONV arith_ss  [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC] c)))
            )
            handle UNCHANGED => 
               mk_conj(tm,t)
       end
   )
   ld;


(* functions written by Mike Gordon to refute a term using
   METIS (cf mail 16/07/08)
val IMP_F_IS_F = METIS_PROVE [] ``!P. (!Q. P ==> Q) ==> (P = F)``;                  
*)                                                             

(* If more convenient, could instead use:
val IMP_F_IS_F = METIS_PROVE [] ``!P. (!Q. P ==> Q) ==> ~P``;
*)

(* Use RW_TAC to refute a term *)
fun refute tm =
 let val th = prove(``!Q. ^tm ==> Q``, RW_TAC std_ss [])
 in
  MP (SPEC tm IMP_F_IS_F) th
 end;

fun distributeAndRefute tm ld =
  map 
   (fn t => 
      let val c = mk_conj(tm,t)
       in
         (print("term to be refuted with METIS " 
                ^ term_to_string(c) ^ "\n"); 
	  refute c;
          ``F``
         )
         handle HOL_ERR s => 
           (print "METIS failed\n";
            print("Trying to simplify with SIMP_CONV " 
                ^ term_to_string(c) ^ "\n"); 
            snd(dest_comb(concl(SIMP_CONV arith_ss  [CONJ_RIGHT_ASSOC,CONJ_LEFT_ASSOC] c)))
            )
            handle UNCHANGED => 
            mk_conj(tm,t)
       end
   )
   ld;

(* function to distribute 
   pre/\path/\state on the conjunction obtained
   from the negation of the postcondition *) 
(* same as distributeAndSimplify but doesn't simplify the
   terms *)
fun distribute tm ld =
  map 
   (fn t => mk_conj(tm,t))
   ld;

in

(* build the term to be verified at the end of a path *) 
fun makeTermToVerify tm post =
  let val np =  takeNegPost post;
    val listDisj = strip_disj(np);
    val disj = mkDisjFromList(distributeAndRefute tm listDisj)
   in 
      (print_term disj;
      simplDisj(disj)
      )
   end
   handle HOL_ERR s => 
       (print ("HOL_ERR in makeTermToVerify\n");
        ``T``
       )

end;


(* =====================================================
(* Functions to perform the symbolic execution of
   the program, using a CSP solver to select the paths
   and verify that the program satisfies its specification
   at the end of the path *)
   ===================================================== *)


(* -------------------------------------------*)
(* function to transform a finite map that represents
   a state as a term.
   Let fm a finite map of pairs (varName_i, value_i).
   mk_term_from_state  builds the conjunction of terms 
       ``varName_i=value_i``
   for each variable i
   NB: only the last values of variables are considered 
  *)
(* ------------------------------------------ *)
local

(* to test if a finite map is empty *)
fun isEmpty fm = 
   is_const(fm) andalso fst(dest_const(fm))="FEMPTY"
;

(* to make a term that is the equality of 
   a pair (var_i,val_i) where var_i is a variable in 
   the program and val_i is its last value 
*)
fun termVarState vst =
 let val (n,v) = pairSyntax.dest_pair vst;
    val thm = EVAL ``ScalarOf ^v``;
    val scal = snd(dest_comb(concl(thm)));
  in
    mk_eq(mk_var(fromHOLstring n,``:num``),scal)
  end;


(* To build the conjunction of equalities var_i=val_i
   from a finite map that contains pairs (var_i,val_i)
Only the last values of variables are added. 

fm: the finite_map 
var: list of variables that have already been 
     found into the map
*)
fun termFromFiniteMap fm var  = 
  if isEmpty fm 
  then ``T``
  else
    let val (_,[mp,varState]) = strip_comb fm;
        val (n,_) = pairSyntax.dest_pair varState
    in 
      (* if var has not already been found in the list
         then add the pair *)
      if (List.find (fn x=> (x=n)) var) = NONE
      then  
         if  isEmpty mp 
         then termVarState varState
         else mkSimplConj (termVarState varState)
                          (termFromFiniteMap mp (var@[n]))
      else ``T``
    end;

in

(* to build a term from the current value of the state *)
fun termFromState fm =
   termFromFiniteMap fm []
end;



(* ------------------------------------------ *)
(* to test if a path is possible *)
(* with a current precondition and a current state *)
(* ------------------------------------------ *)

(*  test if (pre /\ path) is satisfied for some values of
    the current state 

    use functions printXML_to_file and execPath in
    term2xml
 *)
(* ------------------------------------------ *)
fun testPath name pre path st =
 let val sttm = termFromState(st); 
   val conj = mk_conj(pre,mk_conj(path,sttm))
   in
   (printXML_to_file(name,conj);
    print "======================\n";
    print "Calling the solver to test if path\n";
    print ("    " ^ term_to_string(path) ^"\n");
    print "is feasible.\n";
    print "======================\n";
    execPath(name);
    let val (sol,time) = getSolutions (ilogPath ^ "results/" ^ name ^ ".res");
    in
     if (null sol)
     then  
       (print "======================\n";
        print ("Path " ^ term_to_string(path) ^ " is impossible\n");
        print "======================\n";
        (false,time)
       )
     else 
       (print "======================\n";
        print( "Taking path " ^ term_to_string(path) ^ "\n");
        print "======================\n";
        (true,time)
       )
    end
   )
   end;


(* ------------------------------------------ *)
(* to verify the program at the end of a branch *)
(* ------------------------------------------ *)

(* pre and post are precondition and postcondition,
   path is the current path ,
   st is the state of the variables i.e the final values
      of the variables computed by symbolic execution
      along the path 

returns a RESULT outcome 
  if pre /\ state /\ path /\ ~post
  has no solution  
  which means that (pre /\ state /\ path) => post
  is true

returns an ERROR outcome otherwise

use functions printXML_to_file and validate
in term2xml 
*)


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

in

fun verifyPath name pre st post path =
  let val prpa = mk_conj(pre,path);
    val stt = termFromState(st);
    val conj = mk_conj(stt,prpa);
    (* make the term using specific rule to compute 
       the negation of post *) 
    val tm = makeTermToVerify conj post
   (* other possibility: put the term in DNF *)
    (*val tm = dnf(mk_conj(conj,mk_neg(post)))*);
    in 
     (* if tm is a constant and its value is F 
        the program is correct *)
     if (is_const(tm) andalso tm=``F``)
     then 
       (printCorrect();
        incResolvedPath();
        (``RESULT ^st``,0.0)
       )
     else
         (* tm has not been simplified or has been simplified
            to true so need to call the CSP to find 
            the counter-examples *)
         (print "======================\n";
	  print "METIS and SIMP_CONV haved failed to verify the path\n";
          print "Calling the solver\n";
	  print "======================\n";
	  printXML_to_file(name,tm);
	  execute(name);
	  let val (sol,time) = getSolutions (ilogPath ^ "results/" ^ name ^ ".res");
	  in
          if (null sol)
          then 
	    (printCorrect();
             (``RESULT ^st``,time)
	    )
          else 
            (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP 
               when solving pre /\ state /\ path /\ ~post *) 
            let val errorState = finiteMapSol (hd sol) st
            in
              (printError();
               (``ERROR ^errorState``,time)
	      )
            end
          end
         )
      end
end;



(* -------------------------------------------------- 
   main functions to symbolically execute a program 
   using the small step semantics and calling a CSP
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

(* to print a condition in the program as a HOL term *)
fun pretty_string tm =
   let val var_tms = get_strings tm; 
     val pairs = map 
                  (fn tm => pairSyntax.mk_pair
                      let val v = mk_var(fromHOLstring tm,``:num``)
                      in 
		      (tm,``Scalar ^v``)
			end
		  )
                  var_tms;
     val st = makeStateFromPair pairs;
     val (_,res) = strip_comb(concl(EVAL ``beval ^tm ^st``));
     in 
       term_to_string(el 2 res)
     end;


in

(*------------------------------------------
 Main function to verify a Hoare triple 
   (pre, prog, post) by symbolic execution
   l: list of instructions in opSem syntax 
      that correspond to prog
   st: current variable state
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
fun execSymb name pre (l,st,n) post path= 
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
      let val (r,t) = verifyPath name pre st post path
        in 
          (incPath();
           incCSPTime(t);
           addPath path r
          )
        end
     )
 else
   if n=0
   (* no more steps, so add a TIMEOUT outcome *)
   then addPath path ``TIMEOUT ^st``
   else
     (* takes the first instruction *)
     let val inst = snd(dest_comb(fst(dest_comb(l))))
      in
       (* conditional *)
       if is_condition(inst)
       then execSymbCond name pre (l,st,n) post path 
       else 
         (* while *)
         if is_while(inst)
	 then execSymbWhile name pre (l,st,n) post path
         (* instruction is not a conditional *)
         (* call STEP1 to compute the next state and continue *)
         else
          let val step = EVAL ``STEP1 (^l, ^st)``;
            val tm = snd(dest_comb(concl(step)));
            val newState = snd(dest_comb(snd(dest_comb(tm))));
            val newList = snd(dest_comb(fst(dest_comb(tm))))
           in
             execSymb name pre (newList,newState,(n-1)) post path 
           end
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
Function testPath calls the CSP.
  ----------------------------------------------------- *)

and execSymbCond name pre (l,st,n) post path = 
  let val (_,comb) = strip_comb(l)
    (* first instruction COND *)
    val instCond = (el 1 comb)
    val listInst = (el 2 comb)
   (* save current state to perform  symbolic execution 
      of else part with the state before the conditionnal *)
    val saveState = st;
    val (_,listCond) = strip_comb(instCond)
    val cond = (el 1 listCond)
    val iftm = (el 2 listCond)
    val elsetm = (el 3 listCond)
    (* evaluate the condition on the current state *)
    val (_,evalCond) = strip_comb(concl(EVAL ``beval ^cond ^st``))
    val termCond = (el 2 evalCond);      
   in   
   (* if the condition has been evaluated to a constant
      by EVAL, then takes the decision according to its value *)
   if (is_const(termCond))
   then 
    (incResolved();
     if (termCond=``T``)
     then
      let val nextList =  listSyntax.mk_cons(iftm,listInst)
      in
        (print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is TRUE on the current state, ");
	 print ("taking this path\n");
         execSymb name pre (nextList,st,n) post path 
        )
       end
    else 
      let val nextList =listSyntax.mk_cons(elsetm,listInst)
       in 
       (print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is FALSE on the current state, ");
	 print ("taking the other path\n");
         execSymb name pre (nextList,st,n) post path 
        )
     end
     )
   else
   (* the condition has not been simplified by EVAL. 
      Use the solver to know if the condition is
      possible on the current path
    *)
   let val newPath = mkSimplConj path termCond;
      val (ok,t) = testPath name pre newPath st;
   in
    (if (ok) 
     (* Add the condition to the current path
        and do symbolic execution of if part.
        Then try the else part *)
     then 
      let val nextList = listSyntax.mk_cons(iftm,listInst)
        in
           (incCSPTime(t);
            execSymb name pre (nextList,st,n) post newPath 
           )
        end
     else print(""); 
     (* do  symbolic execution on else part *)
     (* and add ~cond to the current path *)
     let val newPathElse = mkSimplConj path (mk_neg termCond);
       val (elseOk,t) = testPath name pre newPathElse saveState;
       in 
         if (elseOk)
         then 
            let val nextList = listSyntax.mk_cons(elsetm,listInst)
            in
              (incCSPTime(t);
               execSymb name pre (nextList,saveState,n) post newPathElse 
              )
            end
         else print("")
       end
    )
  end
end


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
Function testPath calls the CSP.
  ----------------------------------------------------- *)

and execSymbWhile name pre (l,st,n) post path  =
   let val (_,comb) = strip_comb(l)
    (* first instruction: a While *)
    val instCond = (el 1 comb)
    (* other instructions *)
    val tail = (el 2 comb)
   (* save current state to perform  symbolic execution 
      of exit part with the state before the while *)
    val saveState = st;
    val (_,listCond) = strip_comb(instCond)
    (* condition *)
    val cond = (el 1 listCond)
    (* instruction block of the loop *)
    val block = (el 2 listCond)
    (* evaluate the condition on the current state *)
    val (_,evalCond) = strip_comb(concl(EVAL ``beval ^cond ^st``))
    val termCond = (el 2 evalCond);      
   in   
   (* if the condition has been evaluated to a constant
      by EVAL, then takes the decision according to its value *)
   if (is_const(termCond))
   then 
    (incResolved();
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
         execSymb name pre (nextList,st,n) post path
        )
       end
    else 
      (* exit the loop: do symbolic execution of 
         the tail of instruction list *)
       (print "======================\n";
         print ("Condition\n" ^ pretty_string(cond) ^"\n");
         print ("is FALSE on the current state, ");
	 print ("exiting the loop\n");
         execSymb name pre (tail,st,n) post path
        )
     )
   else
   (* the condition has not been simplified by EVAL. 
      Use the solver to know if the condition is
      possible on the current path
    *)
   let  val newPath = mkSimplConj path termCond;
     val (ok,t) = testPath name pre newPath st;
   in
    (if (ok) 
     (* Add the condition to the current path
        and enter the loop: do symbolic execution of [block,l]
        Then try the exit part *)
     then 
      let val nextList = listSyntax.mk_cons(block,l)
        in
           (incCSPTime(t);
            execSymb name pre (nextList,st,n) post newPath
	  ) 
        end
     else print(""); 
     (* exit the loop: do  symbolic execution on the tail of 
        the list and add ~cond to the current path *)
     let val newPathExit = mkSimplConj path (mk_neg termCond);
       val (elseOk,t) = testPath name pre newPathExit saveState;
       in 
         if (elseOk)
         then 
           (incCSPTime(t);
            execSymb name pre (tail,saveState,n) post newPathExit
	   )
         else print("")
       end
    )
  end
end

end;


(* -------------------------------------------------- 
   main function to verify a Hoare triple by symbolic
   execution
   -------------------------------------------------- *)

(* to evaluate pre or post condition on an initial state *)
local

fun evalSpec t st = 
   snd(dest_comb(concl(EVAL ``^t ^st``)));

in

fun execSymbWithCSP name spec n = 
  (* build the symbolic state from variables in the program *)
  let val s = makeState spec;
   val (_,args) = strip_comb spec;
   val (pre,prog,post) = (el 1 args, el 2 args, el 3 args)
  in
     (resetAll(); (* reset global variables *)
      execSymb name 
              (evalSpec pre s) 
              (``[^prog]``,s,n)
              (evalSpec post s)
              ``T``;
      let val plurPath = if (!nbPath>1) then "s were "
                         else " was ";
        val plurCond = if (!nbResolvedCond>1) then "s were "
                          else " was ";
      val plurResolvedPath = if (!nbResolvedPath>1) then "s were "
                         else " was ";
      in
        (print (int_to_string(!nbPath) ^ " path" ^ plurPath 
               ^ "explored.\n");
         print (int_to_string(!nbResolvedCond) ^ " condition" 
               ^ plurCond ^ "resolved" ^ " by EVAL.\n");
         print (int_to_string(!nbResolvedPath) ^ " path" 
               ^ plurResolvedPath ^ "resolved" ^ " by SIMP_CONV and METIS.\n")
        )
      end;
      print ("Total solving time with the constraint solver: " 
              ^ Real.toString(!CSPtime) ^ "s.\n"); 
      !allPathResult)
   end;
end;






(* ============================= examples ==========================

Examples of symbolic execution:
------------------------------

Need to load: newOpsem (file loadNewOpsem.ml), the examples
(file loadExamples), term2xml.ml and this file execSymb.ml.

Need to have a java virtual machine.

In all the examples, the constraint solver handles natural 
numbers in [0..2^16].

AbsMinus
--------
val name = "AbsMinus";
val spec = AbsMinusSpec;
execSymbWithCSP name spec 10;

3 paths were explored.
1 condition was resolved by EVAL.
3 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.037s.
> val it =
    [(``~(i <= j)``,
      ``RESULT
          (FEMPTY |+ ("result",Scalar result) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("i",Scalar i) |+ ("j",Scalar j) |+
           ("result",Scalar 0) |+ ("k",Scalar 0) |+
           ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j)))``),
     (``i <= j /\ (i = j)``,
      ``RESULT
          (FEMPTY |+ ("result",Scalar result) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("i",Scalar i) |+ ("j",Scalar j) |+
           ("result",Scalar 0) |+ ("k",Scalar 0) |+ ("k",Scalar 1) |+
           ("result",Scalar (i - j)) |+ ("Result",Scalar (i - j)))``),
     (``i <= j /\ ~(i = j)``,
      ``RESULT
          (FEMPTY |+ ("result",Scalar result) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("i",Scalar i) |+ ("j",Scalar j) |+
           ("result",Scalar 0) |+ ("k",Scalar 0) |+ ("k",Scalar 1) |+
           ("result",Scalar (j - i)) |+ ("Result",Scalar (j - i)))``)] :
  (term * term) list
- - - - - 
*** Time taken: 3.916s

Tritype
-------
val name = "Tritype";
val spec = TritypeSpec;
execSymbWithCSP name spec 20;

10 paths were explored.
15 conditions were resolved by EVAL.
10 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 1.709s.
> val it =
    [(``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ ~(i + j <= k \/ j + k <= i \/ i + k <= j)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("Result",Scalar 1))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ (i + j <= k \/ j + k <= i \/ i + k <= j)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 4) |+ ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         (j = k)) /\ ~(i < j + k)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 3) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         (j = k)) /\ i < j + k``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 3) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ (i = k)) /\
         ~(j = k)) /\ ~(j < i + k)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 2) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ (i = k)) /\
         ~(j = k)) /\ j < i + k``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 2) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ ~(k < i + j)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ k < i + j``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2))``),
     (``((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\
        (j = k)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 3) |+
           ("trityp",Scalar 6) |+ ("trityp",Scalar 3) |+
           ("Result",Scalar 3))``),
     (``((i = 0) \/ (j = 0)) \/ (k = 0)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``)] : (term * term) list
- - - - - 
*** Time taken: 25.590s


Tritype with a number of step that is too small
-----------------------------------------------
The outcome is RESULT for one path and TIMEOUT
for the other path.

val name = "Tritype";
val spec = TritypeSpec;
execSymbWithCSP name spec 5

1 path was explored.
0 condition was resolved by EVAL.
1 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.018s.
> val it =
    [(``~(((i = 0) \/ (j = 0)) \/ (k = 0))``,
      ``TIMEOUT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0))``),
     (``((i = 0) \/ (j = 0)) \/ (k = 0)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``)] : (term * term) list
- - - - 
*** Time taken: 4.488s


Tritype with an error
---------------------
The outcome is ERROR for some of the paths

val name = "TritypeKO";
val spec = TritypeKOSpec;
execSymbWithCSP name spec 20

9 paths were explored.
14 conditions were resolved by EVAL.
7 paths were resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 1.725s.
> val it =
    [(``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ ~((i + j <= k \/ j + k <= i) \/ i + k <= j)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("Result",Scalar 1))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ ((i + j <= k \/ j + k <= i) \/ i + k <= j)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 4) |+ ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         (j = k)) /\ ~(i < j + k)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 3) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ ~(i = k)) /\
         (j = k)) /\ i < j + k``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 3) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2))``),
     (``((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ ~(i = j)) /\ (i = k)) /\
        ~(j = k)``,
      ``ERROR
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 2) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4) |+ ("Result",Scalar 4) |+
           ("trityp",Scalar 4) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
           ("k",Scalar 2))``),
     (``((((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ ~(i = k)) /\
          ~(j = k)) /\ ~(k < i + j)) /\ j < i + k``,
      ``ERROR
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2) |+ ("Result",Scalar 2) |+
           ("trityp",Scalar 2) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("k",Scalar 2))``),
     (``(((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ ~(i = k)) /\
         ~(j = k)) /\ k < i + j``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 2) |+
           ("Result",Scalar 2))``),
     (``((~(((i = 0) \/ (j = 0)) \/ (k = 0)) /\ (i = j)) /\ (i = k)) /\
        (j = k)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 0) |+
           ("trityp",Scalar 1) |+ ("trityp",Scalar 3) |+
           ("trityp",Scalar 6) |+ ("trityp",Scalar 3) |+
           ("Result",Scalar 3))``),
     (``((i = 0) \/ (j = 0)) \/ (k = 0)``,
      ``RESULT
          (FEMPTY |+ ("trityp",Scalar trityp) |+ ("Result",Scalar Result) |+
           ("i",Scalar i) |+ ("j",Scalar j) |+ ("k",Scalar k) |+
           ("trityp",Scalar 0) |+ ("trityp",Scalar 4) |+
           ("Result",Scalar 4))``)] : (term * term) list
- - - - 
*** Time taken: 24.686s

Sum of the n first integers
---------------------------

20 steps
--------

val name = "Sum";
val spec = SumSpec;
execSymbWithCSP name spec 20

4 paths were explored.
1 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.067s.
> val it =
    [(``~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("Result",Scalar 0))``),
     (``1 <= n /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("Result",Scalar 1))``),
     (``(1 <= n /\ 2 <= n) /\ ~(3 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("Result",Scalar 3))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("Result",Scalar 6))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5))``)] : (term * term) list
- - - - 
*** Time taken: 4.792s

50 steps
--------

execSymbWithCSP name spec 50

14 paths were explored.
1 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.276s.
> val it =
    [(``~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("Result",Scalar 0))``),
     (``1 <= n /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("Result",Scalar 1))``),
     (``(1 <= n /\ 2 <= n) /\ ~(3 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("Result",Scalar 3))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("Result",Scalar 6))``),
     (``(((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ ~(5 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("Result",Scalar 10))``),
     (``((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ ~(6 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("Result",Scalar 15))``),
     (``(((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n) /\
        ~(7 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("Result",Scalar 21))``),
     (``((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n) /\
         7 <= n) /\ ~(8 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("Result",Scalar 28))``),
     (``(((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
           6 <= n) /\ 7 <= n) /\ 8 <= n) /\ ~(9 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("Result",Scalar 36))``),
     (``((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
            6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ ~(10 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("Result",Scalar 45))``),
     (``(((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
             6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
        ~(11 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("s",Scalar 55) |+ ("i",Scalar 11) |+ ("Result",Scalar 55))``),
     (``((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
              6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
         11 <= n) /\ ~(12 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("s",Scalar 55) |+ ("i",Scalar 11) |+ ("s",Scalar 66) |+
           ("i",Scalar 12) |+ ("Result",Scalar 66))``),
     (``(((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
               6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
          11 <= n) /\ 12 <= n) /\ ~(13 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("s",Scalar 55) |+ ("i",Scalar 11) |+ ("s",Scalar 66) |+
           ("i",Scalar 12) |+ ("s",Scalar 78) |+ ("i",Scalar 13) |+
           ("Result",Scalar 78))``),
     (``((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
           11 <= n) /\ 12 <= n) /\ 13 <= n) /\ ~(14 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("s",Scalar 55) |+ ("i",Scalar 11) |+ ("s",Scalar 66) |+
           ("i",Scalar 12) |+ ("s",Scalar 78) |+ ("i",Scalar 13) |+
           ("s",Scalar 91) |+ ("i",Scalar 14) |+ ("Result",Scalar 91))``),
     (``((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
           11 <= n) /\ 12 <= n) /\ 13 <= n) /\ 14 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("s",Scalar 0) |+
           ("i",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 3) |+
           ("i",Scalar 3) |+ ("s",Scalar 6) |+ ("i",Scalar 4) |+
           ("s",Scalar 10) |+ ("i",Scalar 5) |+ ("s",Scalar 15) |+
           ("i",Scalar 6) |+ ("s",Scalar 21) |+ ("i",Scalar 7) |+
           ("s",Scalar 28) |+ ("i",Scalar 8) |+ ("s",Scalar 36) |+
           ("i",Scalar 9) |+ ("s",Scalar 45) |+ ("i",Scalar 10) |+
           ("s",Scalar 55) |+ ("i",Scalar 11) |+ ("s",Scalar 66) |+
           ("i",Scalar 12) |+ ("s",Scalar 78) |+ ("i",Scalar 13) |+
           ("s",Scalar 91) |+ ("i",Scalar 14) |+ ("s",Scalar 105) |+
           ("i",Scalar 15))``)] : (term * term) list
- - - - 
*** Time taken: 24.114s


Condinationnal sum: computes the sum of the n first integers
when n<k else compute n+k
-------------------------------------------------

val name = "ConditionnalSum";
val spec = ConditionnalSumSpec;
execSymbWithCSP name spec 20

5 paths were explored.
1 condition was resolved by EVAL.
1 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.104s.
> val it =
    [(``n < k /\ ~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("s",Scalar 0) |+
           ("i",Scalar 1) |+ ("Result",Scalar 0))``),
     (``(n < k /\ 1 <= n) /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("s",Scalar 0) |+
           ("i",Scalar 1) |+ ("s",Scalar 1) |+ ("i",Scalar 2) |+
           ("Result",Scalar 1))``),
     (``((n < k /\ 1 <= n) /\ 2 <= n) /\ ~(3 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("s",Scalar 0) |+
           ("i",Scalar 1) |+ ("s",Scalar 1) |+ ("i",Scalar 2) |+
           ("s",Scalar 3) |+ ("i",Scalar 3) |+ ("Result",Scalar 3))``),
     (``(((n < k /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("s",Scalar 0) |+
           ("i",Scalar 1) |+ ("s",Scalar 1) |+ ("i",Scalar 2) |+
           ("s",Scalar 3) |+ ("i",Scalar 3) |+ ("s",Scalar 6) |+
           ("i",Scalar 4) |+ ("Result",Scalar 6))``),
     (``(((n < k /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\ 4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("s",Scalar 0) |+
           ("i",Scalar 1) |+ ("s",Scalar 1) |+ ("i",Scalar 2) |+
           ("s",Scalar 3) |+ ("i",Scalar 3) |+ ("s",Scalar 6) |+
           ("i",Scalar 4) |+ ("s",Scalar 10) |+ ("i",Scalar 5))``),
     (``~(n < k)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("k",Scalar k) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("s",Scalar (n + k)) |+
           ("Result",Scalar (n + k)))``)] : (term * term) list
- - - - 
*** Time taken: 6.604s


Nested loops that compute the square of n
------------------------------------------
public class NestedLoop {
	/*@ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=1;
		while (i <= n) {
			int j=1;
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
}

val name = "NestedLoop";
val spec = NestedLoopSpec;
execSymbWithCSP name spec 50

4 paths were explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.913s.
> val it =
    [(``~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("Result",Scalar 0))``),
     (``(1 <= n /\ ~(2 <= n)) /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("i",Scalar 2) |+
           ("Result",Scalar 1))``),
     (``((((((1 <= n /\ 2 <= n) /\ ~(3 <= n)) /\ 2 <= n) /\ 1 <= n) /\
          2 <= n) /\ ~(3 <= n)) /\ ~(3 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
           ("s",Scalar 3) |+ ("j",Scalar 2) |+ ("s",Scalar 4) |+
           ("j",Scalar 3) |+ ("i",Scalar 3) |+ ("Result",Scalar 4))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)) /\ 2 <= n) /\
                 1 <= n) /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)) /\ 3 <= n) /\
            1 <= n) /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)) /\ ~(4 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("i",Scalar 2) |+ ("j",Scalar 1) |+ ("s",Scalar 4) |+
           ("j",Scalar 2) |+ ("s",Scalar 5) |+ ("j",Scalar 3) |+
           ("s",Scalar 6) |+ ("j",Scalar 4) |+ ("i",Scalar 3) |+
           ("j",Scalar 1) |+ ("s",Scalar 7) |+ ("j",Scalar 2) |+
           ("s",Scalar 8) |+ ("j",Scalar 3) |+ ("s",Scalar 9) |+
           ("j",Scalar 4) |+ ("i",Scalar 4) |+ ("Result",Scalar 9))``),
     (``((((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ ~(5 <= n)) /\
                  2 <= n) /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\
             ~(5 <= n)) /\ 3 <= n) /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\
        4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("i",Scalar 2) |+
           ("j",Scalar 1) |+ ("s",Scalar 5) |+ ("j",Scalar 2) |+
           ("s",Scalar 6) |+ ("j",Scalar 3) |+ ("s",Scalar 7) |+
           ("j",Scalar 4) |+ ("s",Scalar 8) |+ ("j",Scalar 5) |+
           ("i",Scalar 3) |+ ("j",Scalar 1) |+ ("s",Scalar 9) |+
           ("j",Scalar 2) |+ ("s",Scalar 10) |+ ("j",Scalar 3) |+
           ("s",Scalar 11) |+ ("j",Scalar 4))``),
     (``((((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                  ~(6 <= n)) /\ 2 <= n) /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\
             4 <= n) /\ 5 <= n) /\ ~(6 <= n)) /\ 3 <= n) /\ 1 <= n) /\
        2 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
           ("s",Scalar 6) |+ ("j",Scalar 2) |+ ("s",Scalar 7) |+
           ("j",Scalar 3) |+ ("s",Scalar 8) |+ ("j",Scalar 4) |+
           ("s",Scalar 9) |+ ("j",Scalar 5) |+ ("s",Scalar 10) |+
           ("j",Scalar 6) |+ ("i",Scalar 3) |+ ("j",Scalar 1) |+
           ("s",Scalar 11) |+ ("j",Scalar 2))``),
     (``((((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                  6 <= n) /\ ~(7 <= n)) /\ 2 <= n) /\ 1 <= n) /\ 2 <= n) /\
             3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n) /\ ~(7 <= n)) /\
        3 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("i",Scalar 2) |+ ("j",Scalar 1) |+ ("s",Scalar 7) |+
           ("j",Scalar 2) |+ ("s",Scalar 8) |+ ("j",Scalar 3) |+
           ("s",Scalar 9) |+ ("j",Scalar 4) |+ ("s",Scalar 10) |+
           ("j",Scalar 5) |+ ("s",Scalar 11) |+ ("j",Scalar 6) |+
           ("s",Scalar 12) |+ ("j",Scalar 7) |+ ("i",Scalar 3))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ ~(8 <= n)) /\ 2 <= n) /\ 1 <= n) /\
            2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("i",Scalar 2) |+
           ("j",Scalar 1) |+ ("s",Scalar 8) |+ ("j",Scalar 2) |+
           ("s",Scalar 9) |+ ("j",Scalar 3) |+ ("s",Scalar 10) |+
           ("j",Scalar 4) |+ ("s",Scalar 11) |+ ("j",Scalar 5) |+
           ("s",Scalar 12) |+ ("j",Scalar 6) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ ~(9 <= n)) /\ 2 <= n) /\
            1 <= n) /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
           ("s",Scalar 9) |+ ("j",Scalar 2) |+ ("s",Scalar 10) |+
           ("j",Scalar 3) |+ ("s",Scalar 11) |+ ("j",Scalar 4) |+
           ("s",Scalar 12) |+ ("j",Scalar 5) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ ~(10 <= n)) /\
            2 <= n) /\ 1 <= n) /\ 2 <= n) /\ 3 <= n) /\ 4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("i",Scalar 2) |+ ("j",Scalar 1) |+ ("s",Scalar 10) |+
           ("j",Scalar 2) |+ ("s",Scalar 11) |+ ("j",Scalar 3) |+
           ("s",Scalar 12) |+ ("j",Scalar 4) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
            ~(11 <= n)) /\ 2 <= n) /\ 1 <= n) /\ 2 <= n) /\ 3 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("s",Scalar 10) |+ ("j",Scalar 11) |+ ("i",Scalar 2) |+
           ("j",Scalar 1) |+ ("s",Scalar 11) |+ ("j",Scalar 2) |+
           ("s",Scalar 12) |+ ("j",Scalar 3) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
            11 <= n) /\ ~(12 <= n)) /\ 2 <= n) /\ 1 <= n) /\ 2 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("s",Scalar 10) |+ ("j",Scalar 11) |+ ("s",Scalar 11) |+
           ("j",Scalar 12) |+ ("i",Scalar 2) |+ ("j",Scalar 1) |+
           ("s",Scalar 12) |+ ("j",Scalar 2) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
            11 <= n) /\ 12 <= n) /\ ~(13 <= n)) /\ 2 <= n) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("s",Scalar 10) |+ ("j",Scalar 11) |+ ("s",Scalar 11) |+
           ("j",Scalar 12) |+ ("s",Scalar 12) |+ ("j",Scalar 13) |+
           ("i",Scalar 2) |+ ("j",Scalar 1) |+ ("s",Scalar 13))``),
     (``(((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                 6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
            11 <= n) /\ 12 <= n) /\ 13 <= n) /\ ~(14 <= n)) /\ 2 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("s",Scalar 10) |+ ("j",Scalar 11) |+ ("s",Scalar 11) |+
           ("j",Scalar 12) |+ ("s",Scalar 12) |+ ("j",Scalar 13) |+
           ("s",Scalar 13) |+ ("j",Scalar 14) |+ ("i",Scalar 2) |+
           ("j",Scalar 1))``),
     (``((((((((((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
                6 <= n) /\ 7 <= n) /\ 8 <= n) /\ 9 <= n) /\ 10 <= n) /\
           11 <= n) /\ 12 <= n) /\ 13 <= n) /\ 14 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5) |+ ("s",Scalar 5) |+
           ("j",Scalar 6) |+ ("s",Scalar 6) |+ ("j",Scalar 7) |+
           ("s",Scalar 7) |+ ("j",Scalar 8) |+ ("s",Scalar 8) |+
           ("j",Scalar 9) |+ ("s",Scalar 9) |+ ("j",Scalar 10) |+
           ("s",Scalar 10) |+ ("j",Scalar 11) |+ ("s",Scalar 11) |+
           ("j",Scalar 12) |+ ("s",Scalar 12) |+ ("j",Scalar 13) |+
           ("s",Scalar 13) |+ ("j",Scalar 14) |+ ("s",Scalar 14) |+
           ("j",Scalar 15))``)] : (term * term) list
- - - - 
*** Time taken: 87.337s

Nested loop with errors
------------------------

public class NestedLoopKO1 {
	/*@ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=0; // 0 instead of 1
		while (i <= n) {
			int j=0; // 0 instead of 1
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
}

val name = "NestedLoopKO1";
val spec = NestedLoopKO1Spec;
execSymbWithCSP name spec 20

1 path was explored.
3 conditions were resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.077s.
> val it =
    [(``~(1 <= n)``,
      ``ERROR
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("i",Scalar 1) |+
           ("Result",Scalar 1) |+ ("Result",Scalar 1) |+ ("i",Scalar 1) |+
           ("j",Scalar 1) |+ ("s",Scalar 1) |+ ("n",Scalar 0))``),
     (``(1 <= n /\ ~(2 <= n)) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("i",Scalar 1) |+ ("j",Scalar 0) |+
           ("s",Scalar 3))``),
     (``((1 <= n /\ 2 <= n) /\ ~(3 <= n)) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("i",Scalar 1) |+ ("j",Scalar 0))``),
     (``(1 <= n /\ 2 <= n) /\ 3 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4))``)] : (term * term) list
- - - - 
*** Time taken: 6.208s

30 steps
--------
execSymbWithCSP name spec 30

2 paths were explored.
6 conditions were resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.513s.
> val it =
    [(``~(1 <= n)``,
      ``ERROR
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("i",Scalar 1) |+
           ("Result",Scalar 1) |+ ("Result",Scalar 1) |+ ("i",Scalar 1) |+
           ("j",Scalar 1) |+ ("s",Scalar 1) |+ ("n",Scalar 0))``),
     (``((((1 <= n /\ ~(2 <= n)) /\ 1 <= n) /\ 1 <= n) /\ ~(2 <= n)) /\
        ~(2 <= n)``,
      ``ERROR
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("i",Scalar 1) |+ ("j",Scalar 0) |+
           ("s",Scalar 3) |+ ("j",Scalar 1) |+ ("s",Scalar 4) |+
           ("j",Scalar 2) |+ ("i",Scalar 2) |+ ("Result",Scalar 4) |+
           ("Result",Scalar 4) |+ ("i",Scalar 2) |+ ("j",Scalar 2) |+
           ("s",Scalar 4) |+ ("n",Scalar 1))``),
     (``((((1 <= n /\ 2 <= n) /\ ~(3 <= n)) /\ 1 <= n) /\ 1 <= n) /\ 2 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("i",Scalar 1) |+ ("j",Scalar 0) |+ ("s",Scalar 4) |+
           ("j",Scalar 1) |+ ("s",Scalar 5) |+ ("j",Scalar 2) |+
           ("s",Scalar 6) |+ ("j",Scalar 3))``),
     (``((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)) /\ 1 <= n) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4) |+ ("i",Scalar 1) |+
           ("j",Scalar 0) |+ ("s",Scalar 5) |+ ("j",Scalar 1) |+
           ("s",Scalar 6) |+ ("j",Scalar 2))``),
     (``((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ ~(5 <= n)) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4) |+ ("s",Scalar 5) |+
           ("j",Scalar 5) |+ ("i",Scalar 1) |+ ("j",Scalar 0) |+
           ("s",Scalar 6) |+ ("j",Scalar 1))``),
     (``(((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\
         ~(6 <= n)) /\ 1 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4) |+ ("s",Scalar 5) |+
           ("j",Scalar 5) |+ ("s",Scalar 6) |+ ("j",Scalar 6) |+
           ("i",Scalar 1) |+ ("j",Scalar 0))``),
     (``(((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n) /\
        ~(7 <= n)``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4) |+ ("s",Scalar 5) |+
           ("j",Scalar 5) |+ ("s",Scalar 6) |+ ("j",Scalar 6) |+
           ("s",Scalar 7) |+ ("j",Scalar 7) |+ ("i",Scalar 1))``),
     (``(((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n) /\ 5 <= n) /\ 6 <= n) /\
        7 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 0) |+ ("j",Scalar 0) |+
           ("s",Scalar 1) |+ ("j",Scalar 1) |+ ("s",Scalar 2) |+
           ("j",Scalar 2) |+ ("s",Scalar 3) |+ ("j",Scalar 3) |+
           ("s",Scalar 4) |+ ("j",Scalar 4) |+ ("s",Scalar 5) |+
           ("j",Scalar 5) |+ ("s",Scalar 6) |+ ("j",Scalar 6) |+
           ("s",Scalar 7) |+ ("j",Scalar 7))``)] : (term * term) list
- - - - 
*** Time taken: 19.401s


Another error: 
-------------
j is not reset in the inner loop
	/*@ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=1;
		int j=1;
		while (i <= n) {
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
}


val name = "NestedLoopKO2";
val spec = NestedLoopKO2Spec;
execSymbWithCSP name spec 20

3 paths were explored.
0 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.129s.
> val it =
    [(``~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("Result",Scalar 0))``),
     (``(1 <= n /\ ~(2 <= n)) /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("i",Scalar 2) |+
           ("Result",Scalar 1))``),
     (``((((1 <= n /\ 2 <= n) /\ ~(3 <= n)) /\ 2 <= n) /\ ~(3 <= n)) /\
        ~(3 <= n)``,
      ``ERROR
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("i",Scalar 2) |+ ("i",Scalar 3) |+
           ("Result",Scalar 2) |+ ("Result",Scalar 2) |+ ("i",Scalar 3) |+
           ("n",Scalar 2))``),
     (``((((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)) /\ 2 <= n) /\
        ~(4 <= n)``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("i",Scalar 2) |+ ("i",Scalar 3))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("j",Scalar j) |+ ("n",Scalar n) |+ ("i",Scalar i) |+
           ("s",Scalar 0) |+ ("i",Scalar 1) |+ ("j",Scalar 1) |+
           ("s",Scalar 1) |+ ("j",Scalar 2) |+ ("s",Scalar 2) |+
           ("j",Scalar 3) |+ ("s",Scalar 3) |+ ("j",Scalar 4) |+
           ("s",Scalar 4) |+ ("j",Scalar 5))``)] : (term * term) list
- - - - 
*** Time taken: 6.904s


Sum of the squares of the n first integers
------------------------------------------

val name = "SquareSum";
val spec = SquareSumSpec;
execSymbWithCSP name spec 20

4 paths were explored.
1 condition was resolved by EVAL.
0 path was resolved by SIMP_CONV and METIS.
Total solving time with the constraint solver: 0.074s.
> val it =
    [(``~(1 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("i",Scalar 0) |+
           ("s",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("Result",Scalar 0))``),
     (``1 <= n /\ ~(2 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("i",Scalar 0) |+
           ("s",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("Result",Scalar 1))``),
     (``(1 <= n /\ 2 <= n) /\ ~(3 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("i",Scalar 0) |+
           ("s",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 5) |+
           ("i",Scalar 3) |+ ("Result",Scalar 5))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ ~(4 <= n)``,
      ``RESULT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("i",Scalar 0) |+
           ("s",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 5) |+
           ("i",Scalar 3) |+ ("s",Scalar 14) |+ ("i",Scalar 4) |+
           ("Result",Scalar 14))``),
     (``((1 <= n /\ 2 <= n) /\ 3 <= n) /\ 4 <= n``,
      ``TIMEOUT
          (FEMPTY |+ ("s",Scalar s) |+ ("Result",Scalar Result) |+
           ("n",Scalar n) |+ ("i",Scalar i) |+ ("i",Scalar 0) |+
           ("s",Scalar 0) |+ ("s",Scalar 0) |+ ("i",Scalar 1) |+
           ("s",Scalar 1) |+ ("i",Scalar 2) |+ ("s",Scalar 5) |+
           ("i",Scalar 3) |+ ("s",Scalar 14) |+ ("i",Scalar 4) |+
           ("s",Scalar 30) |+ ("i",Scalar 5))``)] : (term * term) list
- - - - 
*** Time taken: 5.736s

============================= examples ==========================
*)
