
(* ========================= execSymb.sml =====================

   Version of execSymb.ml for compiling.

   Takes a Hoare triple (pre,prog,post) and verifies if
   the program satisfies its specification by 
   symbolic execution using a CSP solver.

   The output is a "if then else" term where
     - conditions are conditions that were not reduced to constant 
       during symbolic execution
     - values are outcome 
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


(* -------------------------------------------- *)
(* Global variables and functions to build the solution:
   - CSP solving time information
   - number of conditions that have been evaluated as 
     constants using EVAL 
   - number of feasible paths that have been explored
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


(* global variable that contains the variables of the program
   and is used to make existential formula *)
val programVars = ref [];
(* programVars is computed by function setVars taht is defined
   with function makeState *)
fun resetProgramVars() =
     programVars:=[];

(* to reset the global variables at the end of an execution *)
fun resetAll() = 
  (CSPtime:=0.0;
   nbPath:=0;
   nbResolvedCond:=0;
   nbResolvedPath:=0
  );
   


open HolKernel Parse boolLib arithmeticTheory (* to have BOUNDED_FORALL theorem *)
     newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory relationTheory stringLib
     term2xml extSolv;  (* added as printXML_to_file needed *)



(*====================================== *)
(* functions to generate symbolic states *)
(* ===================================== *)


(* take a term that corresponds to a program in opSem syntax
   and build a symbolic state that represents all 
   its variables *)
(* Functions  written by Mike Gordon in PATH_EVAL *)
(* Have been modified to get also array variables *)

(* Functions below return a pair ([var ident], [array ident]) *)
(* ---------------------------------------------------------- *)

(* Get set of variables read in a numerical expression (nexp) *)
fun nexp_vars nex =
 let val (opr,args) = strip_comb nex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Var","Arr","Const","Plus","Times","Div","Sub","Min"])
              then (print name; 
                    print " is not an nexp constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Var"      => ([el 1 args],[])
  | "Arr"      =>  (fst (nexp_vars(el 2 args)),
                    insert (el 1 args) (snd(nexp_vars(el 2 args))))
  | "Const"    => ([],[])
  | "Plus"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Times"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Sub"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Div"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Min"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | _          => (print "BUG in nexp_vars! "; print name; fail())
 end;



(* Get set of variables read in a boolean expression (bexp) *)
fun bexp_vars bex =
 let val (opr,args) = strip_comb bex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Equal","Less","LessEq","And","Or","Not"])
              then (print name; 
                    print " is not a bexp constructor\n"; 
                    fail())
              else ()
 in
  case name of
   "Equal"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "Less"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "LessEq"     => (union (fst (nexp_vars(el 1 args))) (fst (nexp_vars(el 2 args)))
                  , union (snd (nexp_vars(el 1 args))) (snd (nexp_vars(el 2 args))))
  | "And"     => (union (fst (bexp_vars(el 1 args))) (fst (bexp_vars(el 2 args)))
                  , union (snd (bexp_vars(el 1 args))) (snd (bexp_vars(el 2 args))))
  | "Or"     => (union (fst (bexp_vars(el 1 args))) (fst (bexp_vars(el 2 args)))
                  , union (snd (bexp_vars(el 1 args))) (snd (bexp_vars(el 2 args))))
  | "Not"      => bexp_vars(el 1 args)
  | _          => (print "BUG in bexp_vars! "; print name; fail())
 end;


(* Get set of variables read or assigned to in a program *)
fun program_vars c =
 let val (opr,args) = strip_comb c  (* N.B. syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Skip","Assign","ArrayAssign","Dispose","Seq",
                              "Cond","While","Local","Assert"])
              then (print name; 
                    print " is not a program constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Skip"     => ([],[])
  | "Assign"   => (insert (el 1 args) (fst (nexp_vars(el 2 args))),
                   snd (nexp_vars(el 2 args)))
  | "ArrayAssign"   =>  ((union (fst (nexp_vars(el 2 args)))
                              (fst (nexp_vars(el 3 args)))),
			insert (el 1 args) 
                               (union (snd (nexp_vars(el 2 args)))
                                      (snd (nexp_vars(el 3 args)))))
  | "Dispose"  => ([],[])
  | "Seq"      => (union
                   (fst (program_vars(el 1 args))) 
                   (fst (program_vars(el 2 args))),
		   union
                   (snd (program_vars(el 1 args))) 
                   (snd (program_vars(el 2 args))))
  | "Cond"     => (union
                   (fst (bexp_vars(el 1 args)))
                   (union
                     (fst (program_vars(el 2 args)))
                     (fst (program_vars(el 3 args)))),
		   union
                   (snd (bexp_vars(el 1 args)))
                   (union
                     (snd (program_vars(el 2 args)))
                     (snd (program_vars(el 3 args)))))

  | "While"    => (union (fst (bexp_vars(el 1 args))) 
                         (fst (program_vars(el 2 args))),
		   union (snd (bexp_vars(el 1 args))) 
                         (snd (program_vars(el 2 args))))
  | "Local"    => ([],[])
  | "Assert"   => ([],[])
  | _          => (print "BUG in program_vars! "; print name; fail())
 end;


(* ==================================== *)
(* functions to make the initial state *)
val MAX_ARRAY_SIZE = 10;


(* to know if a variable is the length of an array *)
fun isArrayLength tm =
  let val s = fromHOLstring tm
  in  
     if (size s) > 6
     then 
       String.extract (s,(size s) -6, NONE) = "Length"
     else false
  end;

(* compute the set of variable in the program as a list of type
   variables. Used to make existential terms *)
fun setVars vars = 
   map
    (fn v =>
      let val s = fromHOLstring v
      in
       if isArrayLength v
       then programVars:= [mk_var(s,``:num``)] @ !programVars
       else programVars:= [mk_var(s,``:int``)] @ !programVars
      end
    )
   vars;


(* 
Construct: FEMPTY |++ [("v1",v1);...;("vn",vn)]
where v1,...,vn are the integer variables read or written in c

TODO: build the length of the array from preconditions
*)

fun varPairs vars =
  let val maxTerm = term_of_int(Arbint.fromInt(MAX_ARRAY_SIZE))
  in
    map 
      (fn tm => 
         if isArrayLength tm
         then ``(^tm,Scalar ^maxTerm)``
         else
           ``(^tm, Scalar ^(mk_var(fromHOLstring tm,``:int``)))``)
    vars
  end;



(* 
Construct a pair (name,value) where name is the name of an array variable
and (value) is a finite_map that represents symbolic initial value of the array.
assuming that the maximum array size is MAX_ARRAY_SIZE.

FEMPTY |++ [("v1",(FEMPTY |++ (0,v1_0) |+ (1,v1_1) |+ ...
   |+ (MAX_ARRAY_SIZE-1,v1_MAX_ARRAY_SIZE-1));...;("vn",(FEMPTY |++ (0,vn_0) |+ (1,vn_1) |+ ...
   |+ (MAX_ARRAY_SIZE,vn_MAX_ARRAY_SIZE-1))]
where v1,...,vn are the array variables read or written in c.

*)

local

fun generateValues(n,l) =
  let val symbVal = mk_var(n ^ "_"  ^ Int.toString(l),``:int``);
  in
  if (l=0)
  then ``(FEMPTY |+ (0:num,^symbVal))``
  else
    let
        val arr = generateValues(n,l-1);
    in
      ``^arr |+ (^(numSyntax.mk_numeral(Arbnum.fromInt(l))),^symbVal)``
    end
end;


fun generateArray(n) =
  let val values = generateValues(n,MAX_ARRAY_SIZE-1);
      val nt = stringSyntax.fromMLstring(n);
  in
    ``(^nt, Array(^values))``
end;


in

fun arrayPairs vars =
 map 
   (fn tm => generateArray(fromHOLstring(tm)))
 vars

end;



(* main function to create the state *)
(* --------------------------------- *)
(* for each array "arr", add an int variable "arrLength"
   that corresponds to arr.length *)
(* if the length of the array is given in the precondition,
   then it is fixed to this value, else it is fixed to
   MAX_ARRAY_SIZE *)

local

(* add a variable xxxLength for each array xxx 
   in the list of int variables *)
fun addArrLength varNames arrNames =
 if arrNames = []
 then varNames
 else 
   List.concat(
    (map 
      (fn tm => 
        insert 
        (stringSyntax.fromMLstring(fromHOLstring(tm)^ "Length"))
        varNames
      )
      arrNames));

(* TODO 
fun  getArrayLength pre =
    take the precondition and return a list of pairs 
   ("arrLength", val) where val is the length of array arr
   given in the precondition or is MAX_ARRAY_SIZE if no information is
   given in the precondition *)

in


(* the length of the arrays are fixed to MAX_ARRAY_SIZE *)
fun makeState c = 
  let val names = program_vars c;
    val varNames = fst names;
    val arrNames = snd names;
    val varAndLengthNames = addArrLength varNames arrNames;
(*    val lengthValue = getArrayLength pre *)
    val vars = varPairs varAndLengthNames;
    val arrayVars = arrayPairs arrNames
  in
     (setVars varAndLengthNames;
      ``FEMPTY |++ ^(listSyntax.mk_list(vars@arrayVars,``:string#value``))``
     )
  end;
end;


(* end of functions to generate symbolic states *)
(* ============================================ *)



(* functions to simplify finite_maps *)
(* --------------------------------- *)

(* Test if a term is FEMPTY or of the form FEMPTY |+ (x1,y1) .... |+ (xn,yn) *)
fun is_finite_map fm =
 (is_const fm andalso fst(dest_const fm) = "FEMPTY")
 orelse (let val (opr,args) = strip_comb fm
         in
          is_const opr 
          andalso fst(dest_const opr) = "FUPDATE"
          andalso (length args = 2)
          andalso is_finite_map(el 1 args)
          andalso is_pair(el 2 args)
         end);


(* Remove overwritten entries in a finite map *)
fun PRUNE_FINITE_MAP_CONV  fm =
 if not(is_finite_map fm) orelse 
    (is_const fm andalso fst(dest_const fm) = "FEMPTY")
  then REFL fm
  else (REWR_CONV FUPDATE_PRUNE 
         THENC RATOR_CONV(RAND_CONV(EVAL THENC PRUNE_FINITE_MAP_CONV)))
       fm;

fun pruneState st =
   snd(dest_comb(concl(PRUNE_FINITE_MAP_CONV  st)));





(*================================================== *)
(* functions to do symbolic simplifications on terms *)
(*================================================== *)

(* Function to existentially quantify a term *)
(* ----------------------------------------- *)
fun existQuantify tm =
  list_mk_exists(!programVars,tm);


(* Function to get the result of an equational theorem *)
(* --------------------------------------------------- *)
fun getThm thm =
  snd(dest_comb(concl(thm)));


(* functions to transform JML bounded forall statement *)
(* --------------------------------------------------  *)

(* conversion rule to rewrite a bounded for all term
   as a conjunction *) 
fun boundedForALL_ONCE_CONV tm =
 let val (vars,body) = strip_forall tm
     val (ant,con) = dest_imp body
     val (_,[lo,hi]) = strip_comb ant
 in
  if hi = Term(`0:num`)
   then (EVAL THENC SIMP_CONV std_ss []) tm
   else CONV_RULE
         (RHS_CONV EVAL)
         (BETA_RULE
          (SPEC
            (mk_abs(lo,con))
            (Q.GEN `P` (CONV_RULE EVAL (SPEC hi BOUNDED_FORALL_THM)))))
 end;                                                                                                                                    

val boundedForAll_CONV =
 TOP_DEPTH_CONV boundedForALL_ONCE_CONV THENC REWRITE_CONV [];                                                                           

(* take a term t and converts it according to
    boundedForAll_CONV *)
fun rewrBoundedForAll tm =
   getThm (boundedForAll_CONV tm)
   handle UNCHANGED => tm;


(* function to eliminate  ``T`` from conjunctions. 
   It is required because the current Java implementation
   that takes a XML tree to build the CSP
   doesn't consider Booleans.
   So if precondition is ``T`` then the XML tag is empty
*)
fun mkSimplConj t1 t2 = 
  getThm (EVAL ``^t1 /\ ^t2``);



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

(*---------------------------------------------------------
Tool for applying De Morgan's laws at the top level to a 
negated conjunction terms. For each term which is
an implication, apply NOT_IMP_CONJ theorem:

NOT_CONJ_IMP_CONV  ``~((A1 ==> B1) /\ ... /\ (An ==> Bn) /\ TM)`` =
 |- (A1 /\ ~B1) \/ ... \/ (An /\ ~Bn) \/ ~TM

---------------------------------------------------------*)
local

   val DE_MORGAN_AND_THM = METIS_PROVE [] ``!A B. ~(A/\B) = ~A \/ ~B `` 

in

fun NOT_CONJ_IMP_CONV tm =
 let val tm1 = dest_neg tm
 in
  if is_imp_only tm1
   then let val (tm2,tm3) = dest_imp tm1
        in
         SPECL [tm2,tm3] NOT_IMP
        end
   else 
     if is_conj tm1
     then let val (tm2,tm3) = dest_conj tm1
        in
            if is_imp_only tm2
            then let val (tm4,tm5) = dest_imp tm2
              in
                CONV_RULE
                (RAND_CONV(RAND_CONV NOT_CONJ_IMP_CONV))
                (SPECL [tm4,tm5,tm3] NOT_IMP_CONJ)
             end
            else 
               CONV_RULE
                (RAND_CONV(RAND_CONV NOT_CONJ_IMP_CONV))
                (SPECL [tm2,tm3] DE_MORGAN_AND_THM)
        end
      else REFL tm
  end
  handle HOL_ERR t  => 
     (print "HOL_ERR in NOT_CONJ_IMP_CONV";
      REFL tm
     )
end;


(* function to take the negation of the postcondition
   using NOT_CONJ_IMP_CONV *)
fun takeNegPost post =
 let val n = mk_neg(post);
   in
     if is_conj(post) orelse is_imp(post)
     then 
     (* build the negation using De Morgan laws at one level *)
        getThm (NOT_CONJ_IMP_CONV n)
     else
       (* case where post is not an implication *)
       n
     handle HOL_ERR t  => 
       (print "HOL_ERR in takeNegPost";
        n
        )
   end;


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
          ``F``
         )
         handle HOL_ERR s => 
           (print "METIS failed\n";
            print("Trying to simplify with SIMP_CONV and OMEGA_CONV\n"); 
            (*    ^ term_to_string(c) ^ "\n");*) 
         let  
          val res = getThm (SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] fc)
         in 
             res
         end
            )
        handle UNCHANGED => 
        (print "Term unchanged\n";
        mk_conj(tm,t))
       end
   )
   ld;


in

(* Verify a term at the end of a path *) 
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



(* =====================================================
(* Functions to perform the symbolic execution of
   the program, using a CSP solver to select the paths
   and verify that the program satisfies its specification
   at the end of the path *)
   ===================================================== *)
(*
(* to make a term that is the equality of 
   a pair (var_i,val_i) where var_i is a variable in 
   the program and val_i is its last value 
*)
fun termVarState vst =
 let val (n,v) = pairSyntax.dest_pair vst;
    val thm = EVAL ``ScalarOf ^v``;
    val scal = getThm thm;
  in
    mk_eq(mk_var(fromHOLstring n,``:int``),scal)
  end;
*)

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
(* local

(* to test if a finite map is empty *)
fun isEmpty fm = 
   is_const(fm) andalso fst(dest_const(fm))="FEMPTY"
;


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
*)

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
     (false,time)
    );

in 


fun testPath name pre path st =
  (* TODO: use mkSimplConj or modify term2xml to handle x /\T *)
 let val timeout = 100
   val intFormat = 8
   val conj = mk_conj(pre,path)
   in
   (print "======================\n";
    print "Testing feasability\n";
    print "======================\n";
    let val (th,time) = extSolvTimeoutFormat name conj timeout intFormat
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
     handle ExtSolverTimeout =>
       let val existsConj = existQuantify conj
         val thSimp = SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] existsConj
         val resSimp=  getThm thSimp
       in
         (print "Timeout in solver, testing path with SIMP_CONV\n";
          pathInfo resSimp path  ((Real.fromInt timeout)*0.001)  
        )
       end
       handle UNCHANGED  => 
        (print "======================\n";
	 print "Path unsolved\n";
         print( "Taking path " ^ term_to_string(path) ^ "\n");
	 print "======================\n"; 
         (true,((Real.fromInt timeout)*0.001))
        )
   )
   end;
end;

(* old version that doesn't use the external solver *)
(*  test if (pre /\ path) is satisfied for some values of
    the current state 

    use functions printXML_to_file and execPath in
    term2xml
 *)
 (*fun testPath name pre path st =
  (*val sttm = termFromState(pruneState(st)); *)
  (* TODO: use mkSimplConj or modify term2xml to handle x /\T *)
 let  val conj = mk_conj(pre,path)
   val intFormat = 8
   val timeout = 100
   (*val conj = mk_conj(pre,mk_conj(path,sttm))*)
   in
   (printXML_to_file(name,conj);
    print "======================\n";
    print "Calling the solver to test if path\n";
    print ("    " ^ term_to_string(path) ^"\n");
    print "is feasible.\n";
    print "======================\n";
    limitedExecPathFormat name timeout intFormat;
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

end;
*)

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


(* function to evaluate the postcondition.
   st1 is the state before execution of the program
   st2 is the state after execution of the program
*)
fun evalPost t st1 st2 = 
  let val p = getThm (EVAL ``^t ^st1``);
   val pp =  if (is_abs(p))
             then getThm (EVAL ``^p ^st2``)
             else p
   in
     rewrBoundedForAll pp
   end
   handle HOL_ERR s => 
     (print "HOL_ERR in evalPost";
      t
     )
  ;

fun makeErrorState name st = 
   let val (sol,_) =  extSolv.getSolutions (ilogPath ^ "results/" ^ name ^ ".res")
   in 
     extSolv.finiteMapSol (hd sol) st
   end;

in

(* st1 is initial state (before program execution)
   st2 is final state (after program execution) *)

fun verifyPath name pre st1 st2 post path =
  let val timeout = 10000; 
     val f = 16
     val conj = mk_conj(pre,path);
    val st2' = pruneState(st2);
    (* val stt = termFromState(pruneState(st2));
     val conj = mk_conj(stt,prpa);*)
    val po = evalPost post st1 st2'
    (* make the term using specific rule to compute 
       the negation of post *) 
    val tm = verifyTerm conj po
   (* other possibility: put the term in DNF *)
    (*val tm = dnf(mk_conj(conj,mk_neg(post)))*);
    in 
     (* if tm is a constant and its value is F 
        the program is correct *)
     if is_const(tm)
     then 
       if tm=``F``
       then
          (printCorrect();
           incResolvedPath();
          (``RESULT ^st2'``,0.0)
        )
       else 
         (* there is an error, searching solution with CSP *)
         (print "======================\n";
          print "METIS has shown that path is NOT correct\n";
          print "Searching counter-example\n";
          let val tmKO = mk_conj(conj,takeNegPost(po))
             val  (th,time) = extSolvTimeoutFormat name tmKO timeout f
             val res = getThm th
	  in
          if res = ``F``
          then 
            ( print "PROBLEM: solver has not find a counter-example\n";
	      (``ERROR ^st2'``,time)
	    )
          else 
            (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP 
               when solving pre /\ state /\ path /\ ~post *) 
            let val errorState = makeErrorState name st2'
            in
              (printError();
               (``ERROR ^errorState``,time)
	      )
            end
          end
          )
     else
         (* tm has not been simplified to T nor F so 
            calling the CSP *)
         (print "======================\n";
	  print "METIS and SIMP_CONV have failed to verify the path\n";
          print "Testing correctness\n";
	  print "======================\n";
	  let val (th,time) = extSolvTimeoutFormat name tm timeout f
             val res = getThm th
	  in
          if res = ``F``
          then 
	    (printCorrect();
             (``RESULT ^st2'``,time)
	    )
          else 
            (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP 
               when solving pre /\ state /\ path /\ ~post *) 
            let val errorState = makeErrorState name st2'
            in
              (printError();
               (``ERROR ^errorState``,time)
	      )
            end
          end
         )
      end
end;

(*
old version that doen't use the extSolv 
fun verifyPath name pre st1 st2 post path =
  let val conj = mk_conj(pre,path);
    val st2' = pruneState(st2);
    (* val stt = termFromState(pruneState(st2));
     val conj = mk_conj(stt,prpa);*)
    val po = evalPost post st1 st2'
    (* make the term using specific rule to compute 
       the negation of post *) 
    val tm = verifyTerm conj po
   (* other possibility: put the term in DNF *)
    (*val tm = dnf(mk_conj(conj,mk_neg(post)))*);
    in 
     (* if tm is a constant and its value is F 
        the program is correct *)
     if (is_const(tm) andalso tm=``F``)
     then 
       (printCorrect();
        incResolvedPath();
        (``RESULT ^st2'``,0.0)
       )
     else
         (* tm has not been simplified or has been simplified
            to true so need to call the CSP to find 
            the counter-examples *)
         (print "======================\n";
	  print "METIS and SIMP_CONV have failed to verify the path\n";
          print "Calling the solver\n";
          print ("term is: " ^ term_to_string(tm) ^"\n");
	  print "======================\n";
	  printXML_to_file(name,tm);
	  execPath(name);
	  let val (sol,time) = getSolutions (ilogPath ^ "results/" ^ name ^ ".res");
	  in
          if (null sol)
          then 
	    (printCorrect();
             (``RESULT ^st2'``,time)
	    )
          else 
            (* add to the current state the values
               of the variables that correspond to an error
               i.e the values found by the CSP 
               when solving pre /\ state /\ path /\ ~post *) 
            let val errorState = finiteMapSol (hd sol) st2'
            in
              (printError();
               (``ERROR ^errorState``,time)
	      )
            end
          end
         )
      end
end;
*)


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
local

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

fun makeStateFromPair l = 
  if ((length l) = 1)
  then ``(FEMPTY |+ ^(hd l)) ``
  else
      let 
        val map = makeStateFromPair (tl l);
      in
         ``^map |+ ^(hd l)``
end;

in

fun pretty_string tm =
   let val var_tms = get_strings tm; 
     val pairs = map 
                  (fn tm => pairSyntax.mk_pair
                      let val v = mk_var(fromHOLstring tm,``:int``)
                      in 
		      (tm,``Scalar ^v``)
			end
		  )
                  var_tms;
     val st = makeStateFromPair pairs;
     val (_,res) = strip_comb(concl(EVAL ``beval ^tm ^st``));
     in 
       term_to_string(el 2 res)
     end
end;;

(*

(* to make the current precondition
   i.e the conjunction of current precondition 
       with the next assignment in the program *)
(* st is the current state, st' is the new state *)
fun makePre pre st st' =
    if st = st'
    then pre
    else mkSimplConj pre (termVarState (snd (dest_comb st')));
*)

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
      let val (r,t) = verifyPath name pre st1 st2 post path
        in 
          (incPath();
           incCSPTime(t);
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
          let val tm = getThm (EVAL ``STEP1 (^l, ^st2)``);
            val newState = snd(dest_comb(snd(dest_comb(tm))));
            val newList = snd(dest_comb(fst(dest_comb(tm))));
           in
             execSymb name pre (newList,st1,newState,(n-1)) post path 
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

and execSymbCond name pre (l,st1,st2,n) post path = 
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
    val (_,evalCond) = strip_comb(concl(EVAL ``beval ^cond ^st2``))
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
         execSymb name pre (nextList,st1,st2,n) post path 
        )
       end
    else 
      let val nextList =listSyntax.mk_cons(elsetm,listInst)
       in 
       (print "======================\n";
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
         then  execSymb name pre (nextListIf,st1,st2,n) post newPath 
         else ``F``;
      val newPathElse = mkSimplConj path (mk_neg termCond);
      val (elseOk,tElse) = testPath name pre newPathElse saveState;
      val resElse = 
          if (elseOk)
         (* do  symbolic execution on else part *)
         (* and add ~cond to the current path *)
          then execSymb name pre (nextListElse,st1,saveState,n) post newPathElse 
          else ``F`` 
       in
           (incCSPTime(tIf);
            incCSPTime(tElse);
	    if ok
	    then
		if elseOk
		then ``if ^termCond then ^resIf else ^resElse``
		else resIf
	    else resElse
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

and execSymbWhile name pre (l,st1,st2,n) post path  =
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
    val (_,evalCond) = strip_comb(concl(EVAL ``beval ^cond ^st2``))
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
         execSymb name pre (nextList,st1,st2,n) post path
        )
       end
    else 
      (* exit the loop: do symbolic execution of 
         the tail of instruction list *)
       (print "======================\n";
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
         (incCSPTime(tLoop);
          incCSPTime(tExit);
	  if ok
	  then
	      if elseOk
	      then ``if ^termCond then ^resLoop else ^resExit``
	      else resLoop
	  else resExit
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

fun evalPre t st = 
   rewrBoundedForAll(getThm (EVAL ``^t ^st``));

in


fun execSymbWithCSP name spec n = 
  (* build the symbolic state from variables in the program *)
  let  val (_,args) = strip_comb spec;
   val (pre,prog,post) = (el 1 args, el 2 args, el 3 args);
   val s = snd (dest_comb(concl(EVAL (makeState prog))))
  in
     (resetAll(); (* reset global variables *)
      let val res = 
          execSymb name 
              (evalPre pre s) 
              (``[^prog]``,s,s,n)
               post
              ``T``;
       val plurPath = if (!nbPath>1) then "s were "
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
               ^ plurResolvedPath ^ "resolved" ^ " by SIMP_CONV and OMEGA_CONV.\n");
	 print ("Total solving time with the constraint solver: " 
		^ Real.toString(!CSPtime) ^ "s.\n"); 
         resetProgramVars(); (* reset the list of variable used to existentially quantify terms *) 
	 res)
      end
     )
   end
end;

