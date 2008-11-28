(* To verify a relational specification using STRAIGHT_RUN
   a SMT solver and a constraint solver when there is 
   a non-linear expression

Principle:

- Each straight block into the program is executed using STRAIGHT_RUN
- New states are computed after execution of each straight block:
  * execution starts with symbolic intial state s_0
  * state after execution of block b_i is computed by calling
    STRAIGHT_RUN b_i s_i
    This gives a new state s_(i+1)
- if program contains "Local" and "Dispose", then then local variable 
is renamed to become a new global variable (preprocessing that could 
be done during parsing)
After renaming,  "Local" and "Dispose" are removed
- when the current command is a loop (While c body) 
it is unwound MAX_UNWIND times.
  * If current state is state s_i, then we successively call
    STRAIGHT_RUN body s_i which gives state s_(i+1)
    STRAIGHT_RUN body s_(i+1)  which gives state s_(i+2)
    ...
    STRAIGHT_RUN body s_(i+MAX_UNWIND) which gives the final state
  * the loop is unwound on more step only if the entrance condition
    doesn't evaluate to constant ``T``
  * each time the loop is unwound, we add the entrance condition
    into the term to verify: EVAL ``beval ~b s``
    where s is the current state
  * we add the exit condition to the term to be verified.
    The exit condition is EVAL ``beval ~b s_(i+MAX_UNWIND)``
- when the current command is an assertion, it is evaluated on the 
current state
- The term to be verified is:
    ? vars. pre /\ l_0 /\ l_1 /\ ... /\ l_p 
                /\ a_0 /\ a_1 /\ ... /\ a_q 
                /\ ~post
  where l_i are conjunction of entrance and exit conditions of loops 
  and a_i are the assertions

*)


(* TODO
- assert: on the current state
- local and dispose
- compute straight blocks only one time ==> build and use the 
Control Flow Graph of the program
*) 


open HolKernel Parse boolLib  PATH_EVAL
     newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory  stringLib extSMTSolver extSolv
     stateTools  simpTools;

(* maximum number of loop unwinding *)
val MAX_UNWIND = 10;


fun getRes thm =
  snd(dest_comb(concl(thm)));

fun isTrue thm = 
  getRes(thm) = ``T``;

(* prog is a program
   return the first striaght block in prog and the rest of the program
   to be executed
   i.e a pair (str,p) where 
      - str is a straight program,
      - p is either "Skip" or a non stright program
      - and "Seq str p" = prog 
*)
fun getStaightBlock prog =
 let val (opr,args) = strip_comb prog
      val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Skip","Assign","ArrayAssign","GenAssign","Dispose","Seq",
                              "Cond","While","Local","Assert"])
              then (print name; 
                    print " is not a program constructor\n"; 
                    fail())
              else ()
 in
  if name = "Seq"
  then
      let val p1= (el 1 args)
          val p2= (el 2 args)
        in
           if isTrue(EVAL ``STRAIGHT ^p1``)
           then 
             let val gp2 = getStaightBlock p2 
                val p2str = fst gp2
                val rest = snd gp2
                in
		   (``Seq ^p1 ^p2str``,rest)
                end
           else
               (``Skip``,prog)
        end
   else
      if name = "Dispose" orelse name ="Local" orelse name ="Assert" 
      then (print "commands Dispose Local and Assert are not handled"; print name; fail())
      else
         (prog, ``Skip``)
  end;



(* unwind a loop with body b and condition c *)
fun unwindWhile c b s n =
   if n=0
   then 
     let val st = ``FEMPTY |++ ^s``;
        val bev = getRes(EVAL ``beval ^c ^st``);
     in
        (* exit the loop so add the negation of loop 
           entrance condition *)
        (s,mk_neg(bev))
     end
   else 
      let val se = ``FEMPTY |++ ^s``;
          val bev = getRes(EVAL ``beval ^c ^se``);
      in
        if is_const(bev) andalso bev=``F``
	then 
	  (* exit the loop *)
	  (print "======================\n";
           print ("Condition\n" ^ pretty_string(c) ^"\n");
           print ("is FALSE on the current state,\n ");
	   print ("It is not possible to unwind loop one more time\n");
           (s,``T``)
          )
        else
           (* enter the loop so add the entrance condition *)
           let val (st,cond) = finalState b s
             val (stu,condu) = unwindWhile c b st (n-1)
             (* EVAL to simplify terms with T or F *)
              val co = getRes(EVAL ``^(mk_conj(bev,mk_conj(cond,condu)))``)
          in
            (stu,co)
          end
      end
      

and execWhile prog s = 
  let val (opr,args) = strip_comb prog
     val c = el 1 args
     val body = el 2 args
  in 
    unwindWhile c body s MAX_UNWIND
  end



(* Takes a program and the current state (i.e state before current block)
   Computes a pair (s',c) where 
     - s' is the final state
     - c is the conjunction of decisions that have been 
       taken when loops have been unwound
*)
and finalState prog s  =
  let val isStraight = getRes(EVAL ``STRAIGHT(^prog)``)
  in 
    if isStraight=``T``
    then 
       let val straightThm = EVAL ``STRAIGHT_RUN ^prog ^s``;
       in 
          (getRes(straightThm),``T``)
       end
    else
       let val b = getStaightBlock prog
	 val block = fst b
	 val rest = snd b
	 val straightThm = EVAL ``STRAIGHT_RUN ^block ^s``;
	 val stateAfter = getRes(straightThm); 
         val (opr,args) = strip_comb rest
       in
	 if opr = ``Skip`` 
	 then (stateAfter,``T``)
	 else 
	   if opr = ``Seq`` 
	   then
	     let val p1= (el 1 args)
		 val p2= (el 2 args)
		 val (stAfterWhile,listCond) = execWhile p1 stateAfter;
               val (fst,cond) = finalState p2 stAfterWhile 
             in
		 (fst,mk_conj(listCond,cond))
             end
	   else (* it is a while and it is the last block *)
	      execWhile rest stateAfter
        end
   end;

(* val s = s1 *)

(* compute the initial state using makeStateList in ../stateTools.sml
   and the final state using "finalState" and evaluate 
   pre and post conditions using these states.
   The term to be verified is:
      ? vars. valPre /\ valPost /\ cond
   where vars are variables in the program, valPre (resp. valPost) 
   is the value of pre (resp. post) and cond is the conjunction of
   decisions that have been taken during loop unfolding
*)
fun buildTermToVerify spec = 
  let val (_,args) = strip_comb spec;
    val prog =  el 2 args;
    val pre =  el 1 args;
    val post =  el 3 args;
    val s1 = makeStateList prog;
    val (s2,listCond) = finalState prog s1;
    val stateBefore = ``FEMPTY |++ ^s1``;
    val stateAfter = ``FEMPTY |++ ^s2``; 
    val preValue = evalPre pre stateBefore;
    val postValue = evalPost post stateBefore stateAfter; 
    val verif = mk_conj(mk_conj(preValue,listCond),
                        mk_neg(postValue));
    val f = free_vars verif;
 in
    list_mk_exists(f,verif)
 end;



(* to print a message *)
fun printResult res =
   (print "\n==================\n";
    if res=``F``
       then print "Program is correct\n"
       else print "An error has been found\n";
    print "==================\n");


(* ====================== *)
(* verify a specification *)
(* ====================== *)

(* the term to verify is built by evaluating states on successive blocks 
   of the program and unwinding loops MAX_UNWIND times.
   The verification is done first by evaluating the term to 
   remove constants. If this term is not constant T or F then a SMT
   solver is called. If this solver fails because there is a non linear term,
   then the constraint solver is called
*)
    

fun verify spec n =
  (print("Verifying program " ^ n ^ " \n");
  let val verif = (print "building term: "; time buildTermToVerify spec);
      val v = getThm(EVAL verif);
      in 
        (print "Term to verify is:\n";
         print((term_to_string v)^ "\n");
         if is_const(v)
	 then 
	   (print "Term to verify has been simplified to a constant\n";
	    printResult v;
            []
	    )
          else
	    let  val (thm,t) = (print "calling SMT solver: " ; time (extSolvSMT(n^"Straight")) v)
	      val res = getRes thm
            in 
		(print("Solving time with SMT solver: " ^  Real.toString(t) ^ "s.\n");
		 printResult res;
		 if res=``T``
		 then fst(extSMTSolver.getSolutions(n^"Straight"))
		 else []
		)
	    end
	)
        handle YICES_COMPILEError => 
         (print "Term contains non linear expressions, calling constraint solver\n";
	  let  val (thm,t) = (print "calling constraint solver: " ; 
                              time (extSolv.extSolvTimeoutFormat(n^"Straight") v 1000) 8)
	      val res = getRes thm
          in 
             (print("Solving time with constraint solver: " ^  Real.toString(t) ^ "s.\n");
	      printResult res;
	      if res=``T``
	      then hd(fst(extSolv.getSolutions(n^"Straight")))
	      else []
	     )
	  end
         )
      end
    );






(*



(* trying to use lambda expressions to define straight code 
denotational semantics. Passing from one state to another 
is just reducing the lambda abstraction *)

(* seems to be 10 times slower than direct computation of
the state using STRAIGHT_RUN *)

val s = MAKE_STATE_LIST prog;

val res = getRes(EVAL ``STRAIGHT_RUN ^prog ^s``);
*** Time taken: 0.692s

val res = getRes(EVAL ``STRAIGHT_RUN ^prog x``);
val r = subst [(``x:(string # value) list`` |-> s)] res;
getRes(EVAL ``^r``);
*** Time taken: 6.500s

val res = getRes(EVAL ``STRAIGHT_RUN ^prog x``);
val l = mk_abs(``x:(string # value) list``,res);
EVAL ``^l ^s``
*** Time taken: 6.664s


*)
