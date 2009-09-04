(* To verify a relational specification using STRAIGHT_RUN
   a SMT solver and a constraint solver when there is
   a non-linear expression.

Principle:

- Each straight block into the program is executed using STRAIGHT_RUN
- New states are computed after execution of straight blocks:
  * execution starts with symbolic intial state s_0
  * state after execution of block b_i is computed by calling
    STRAIGHT_RUN b_i s_i
    This gives a new state s_(i+1)
- (TODO)if program contains "Local" and "Dispose", then then local variable
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
  * the loop is unwound one more step only if the entrance condition
    doesn't evaluate to constant ``T``
  * each time the loop is unwound, we add the entrance condition
    into the term to verify: EVAL ``beval b s``
    where s is the current state
  * we add the exit condition to the term to be verified.
    The exit condition is EVAL ``beval ~b s_(i+MAX_UNWIND)``
- (TODO)when the current command is an assertion, it is evaluated on the
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
     stateTools  simpTools ;

(* maximum number of loop unwinding *)
val MAX_UNWIND = 10;


(* functions to handle results of theorems *)

fun getRes thm =
  snd(dest_comb(concl(thm)));

fun isTrue thm =
  getRes(thm) = ``T``;


(* ===================================================== *)
(* conversions and simplifications on states to simplify
   conditional terms when a decision has been taken
   when entering a loop *)
(* ===================================================== *)


(* ------------------------------------------------------*)
(* Conversion to transform an equality between a conditional
   term and a value into a conditional term on equalities

   Apply theorem condEq:
    ``!b:bool c1:int c2:int x:int.
               ((if b then c1 else c2) = x) =
               if b then c1=x else c2=x``
*)

local
val condEq =
   prove(``!b:bool c1:int c2:int x:int.
               ((if b then c1 else c2) = x) =
               if b then c1=x else c2=x``,
         METIS_TAC [])
in

fun cond_EQ_CONV tm =
    let val (_,args) = strip_comb tm;
      val iff = (el 1 args);
      val x = (el 2 args);
      val (_,argsIf) = strip_comb  iff;
      val b = (el 1 argsIf);
      val c1 = (el 2 argsIf);
      val c2 = (el 3 argsIf);
    in
        SPECL [b,c1,c2,x] condEq
    end
end;

(* ----------------------------------------------------- *)
(* same conversion as above but for a conditional expression
   that contains Num *)
local
val condEqNum =
   prove(``!b:bool c1:int c2:int x:num.
               (Num (if b then c1 else c2) = x) =
               if b then Num(c1)=x else Num(c2)=x``,
         METIS_TAC [])
in

fun cond_EQ_CONV_NUM tm =
    let val (_,args) = strip_comb tm;
      val num = (el 1 args);
      val (opr,iff) = dest_comb num;
    in
      if opr = ``Num``
      then
        let val x = (el 2 args);
	  val (_,argsIf) = strip_comb  iff;
	  val b = (el 1 argsIf);
          val c1 = (el 2 argsIf);
          val c2 = (el 3 argsIf);
        in
          SPECL [b,c1,c2,x] condEqNum
        end
      else raise HOL_ERR {message="term doesn't match condEqNum",
		       origin_function ="cond_EQ_CONV_NUM",
		       origin_structure ="bmcStraight"}
    end
end;


(* -------------------------------------------------------- *)
(* conversion functions to simplify a conditional term when
   if and else parts are constants T and F *)
local
val condConstantT =
   prove(``!b. (if b then T else F) = b``,
         METIS_TAC [])

in

fun cond_CONSTANT_T_CONV tm =
    let val (_,args) = strip_comb tm;
      val b = (el 1 args);
      val c1 = (el 2 args);
      val c2 = (el 3 args);
    in
      if c1=``T`` andalso c2 = ``F``
      then SPECL [b] condConstantT
      else raise HOL_ERR {message="term doesn't match condConstantT",
		       origin_function ="cond_CONSTANT_T_CONV",
		       origin_structure ="bmcStraight"}
    end
end;


local
 val condConstantF =
   prove(``!b. (if b then F else T) = ~b``,
         METIS_TAC [])

in

fun cond_CONSTANT_F_CONV tm =
    let val (_,args) = strip_comb tm;
      val b = (el 1 args);
      val c1 = (el 2 args);
      val c2 = (el 3 args);
    in
      if c1=``F`` andalso c2 = ``T``
      then SPECL [b] condConstantF
      else raise HOL_ERR {message="term doesn't match condConstantF",
		       origin_function ="cond_CONSTANT_F_CONV",
		       origin_structure ="bmcStraight"}
    end
end;


(*
local
val cond_neg =
   prove(``!b c1 c2. ~(if b then c1 else c2) =
                      (if b then ~c1 else ~c2)``,
         METIS_TAC [])
in

fun cond_NEGATION_CONV tm =
    let val (_,args) = strip_comb tm;
      val b = (el 1 args);
      val c1 = (el 2 args);
      val c2 = (el 3 args);
    in
      SPECL [b,c1,c2] condNeg
    end
end
*)

fun COND_CONV tm =
  (TOP_DEPTH_CONV cond_EQ_CONV THENC REWRITE_CONV []
   (* THENC TOP_DEPTH_CONV cond_CONSTANT_T_CONV
   THENC TOP_DEPTH_CONV cond_CONSTANT_F_CONV
   THENC REWRITE_CONV [] *)
  )
  tm;

(* To simplify conditional terms using conversion functions above

   The objective is to simplify a term of the form:
      ``(if a_0 = x then 0 = ~1 else T) /\ (if a_1 = x then 1 = ~1 else T) /\
      (if a_2 = x then 2 = ~1 else T) /\ (if a_3 = x then 3 = ~1 else T) /\
      (if a_4 = x then 4 = ~1 else T) /\ (if a_5 = x then 5 = ~1 else T) /\
      (if a_6 = x then 6 = ~1 else T) /\ (if a_7 = x then 7 = ~1 else T) /\
      (if a_8 = x then 8 = ~1 else T) /\
      ~((if a_9 = x then 9 = ~1 else T) /\ (if a_9 = x then T else F))`` : term
   into term
        ~(a_0 = x) /\ ~(a_1 = x) /\ ~(a_2 = x) /\ ~(a_3 = x) /\ ~(a_4 = x) /\
       ~(a_5 = x) /\ ~(a_6 = x) /\ ~(a_7 = x) /\ ~(a_8 = x) /\ (a_9 = x) : thm
*)
fun simplifyConditional cond =
      (* transform equalities of conditionals into
         conditional of equalities *)
  let val c1 = getRes((COND_CONV THENC REWRITE_CONV []) cond)
      (* simplify trivial equalities *)
      val c2 = getRes(EVAL c1)
  in
    (* simplify conditional with constants *)
    getRes((TOP_DEPTH_CONV cond_CONSTANT_F_CONV THENC REWRITE_CONV []) c2)
    handle UNCHANGED =>
      getRes((TOP_DEPTH_CONV cond_CONSTANT_T_CONV THENC REWRITE_CONV []) c2)
      handle UNCHANGED =>
      c2
  end
  handle UNCHANGED =>
    getRes((TOP_DEPTH_CONV cond_CONSTANT_F_CONV THENC REWRITE_CONV []) cond)
    handle UNCHANGED =>
      getRes((TOP_DEPTH_CONV cond_CONSTANT_T_CONV THENC REWRITE_CONV []) cond)
      handle UNCHANGED =>
      cond;


(* end of conversion functions *)


(* ============================================================= *)
(* to simplify states according to decisions that have been taken
   during loop unwinding *)

(* ----------------------------------------------------- *)
(* For a conditional term iftm = "if c then p1 else p2",
   if decision c has been taken during loop unwinding,
   if "c==>cond" is true then iftm is replaced with p1, if
   "~c==>cond" is true then iftm is replaced with p2
   else simplification is recursively done in c p1 and p2.
*)

fun decide c iftm =
 if term2yices.is_conditional iftm
 then
   let val (_,args) = strip_comb iftm
     val cond = (el 1 args)
     val p1 = (el 2 args)
     val p2 = (el 3 args)
     val impCond = ``^c ==> ^cond``
     val resCond = getRes(EVAL impCond)
   in
     if resCond = ``T``
     then p1
     else
       let val impNotCond = ``(^c) ==> ~(^cond)``
         val resNotCond = getRes(EVAL impNotCond)
       in
        if resNotCond = ``T``
        then p2
        else  ``if ^(decide c cond)
                then ^(decide c p1)
                else ^(decide c p2)``
       end
   end
 else iftm;


(* ----------------------------------------------------- *)
(* Simplify state s using decision d
   by applying "decide d" to all values in state s.
   s is a list of terms ``("name",value)`` *)
fun decideState d s =
  map
    (fn p =>
       let val (name,vall) = dest_comb(p)
          in
            mk_comb(name, decide d vall)
          end
     )
  s;


(* ----------------------------------------------------- *)
(* compute the value of the state after that decision c has
   been taken during loop unwinding
*)
fun stateForDecision c s =
   let val (l,t) = listSyntax.dest_list(s)
   in
     let val ec =  (print "\nCOND_conv in stateForDecision: "; getRes(time COND_CONV c))
       val cc = (print "\nsimp_conv : "; getRes(time (SIMP_CONV (srw_ss()) []) ec))
     in
       listSyntax.mk_list((decideState cc l),t)
     end
     handle UNCHANGED =>
       listSyntax.mk_list((decideState c l),t)
   end;




(* ===================================================== *)
(* Functions to execute a program block by block.
   Compute successive states s0 s1 ... sn
   where s0 is symbolic initial state built from program variables,
   and for each i, si+1 is state obtained after executing
   block bi+1 on state si.
   Blocks are straight. *)
(* ===================================================== *)

(* ------------------------------------------------------------------*)
(* to decompose a program as 2 subparts (s,p) where s is straight and
   p is the rest of the program to analyze *)
(* prog is a program
   return the first striaght block in prog and the rest of the program
   to be executed
   i.e a pair (str,p) where
      - str is a straight program,
      - p is either "Skip" or a non straight program
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


(* ------------------------------------------*)
(* unwind a loop with body b and condition c *)

(* return a pair (s',c) where s' is the state after n unwinding
   and c is a list of decisions taken when unwinding the loop.
   Conditional terms in states are simplified by propagating the
   decisions that have been taken so far (using "stateForDecision"
   function).
*)


(* TODO:
- build the term for all possible numbers of unwinding
  between 0 and MAX_UNWIND
- consider cases where bev is constant when n=0
*)

fun unwindWhile c b s n =
   if n=0
   then
     let val st = ``FEMPTY |++ ^s``;
        val bev = getRes(EVAL ``beval ^c ^st``);
        val notBev = mk_neg(bev)
        val ss = stateForDecision notBev s
     in
        (* exit the loop so add the negation of loop
           entrance condition *)
        (print "\nend of loop\n";
         print("neg of bev " ^ term_to_string(notBev));
         print(term_to_string(ss));
        (ss,notBev)
        )
     end
   else
      let val se = ``FEMPTY |++ ^s``;
          val bev = getRes(EVAL ``beval ^c ^se``);
      in
        (print("\nbev: " ^ term_to_string(bev)  ^"\n");
         print("current state: " ^term_to_string(s));

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
           let  (* simplify s assuming decision c has been taken *)
             val ss =
               if bev = ``T``
               then s
               else stateForDecision bev s
             val (st,cond) = finalState b ss
             val (stu,condu) = unwindWhile c b st (n-1)
             (* EVAL to simplify terms with T or F *)
              val co = getRes(EVAL ``^(mk_conj(bev,mk_conj(cond,condu)))``)
          in
            (print("\nenter loop for step " ^ int_to_string(n) ^"\n");
             print(term_to_string(stu));
	     (stu,co)
	    )
          end
)
      end


and execWhile prog s =
  let val (opr,args) = strip_comb prog
     val c = el 1 args
     val body = el 2 args
  in
    (print "\nstate before loop\n";
     print(term_to_string(s));
     unwindWhile c body s MAX_UNWIND
)
  end



(* ---------------------------------------------------------------------*)
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




(* ------------------------------------------------------------------*)
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
(*    val simpListCond = simplifyConditional listCond
    val simpPostValue = simplifyConditional postValue
    val verif = mk_conj(mk_conj(preValue,simpListCond),
                        mk_neg(simpPostValue));*)
    val verif = mk_conj(mk_conj(preValue,listCond),
                        mk_neg(postValue));
(*    val v = getRes(SIMP_CONV (srw_ss()) [] verif)*)
    val f = free_vars verif;
 in
    list_mk_exists(f,verif)
end;

(*
simplifyConditional simpListCond

val cond = `` ~(if a_9 = x then F else T)``
simplifyCondition

simplifyCondition postValue

evalPost post stateBefore stateBefore
val stateBefore =  ``(FEMPTY :state) |++
      [("left",Scalar (left :int)); ("x",Scalar (x :int));
       ("aLength",Scalar (10 :int)); ("Result",Scalar (5 :int));
       ("result",Scalar (result :int));
       ("a",
        Array
          ((FEMPTY :num |-> int) |+ ((0 :num),(a_0 :int)) |+
           ((1 :num),(a_1 :int)) |+ ((2 :num),(a_2 :int)) |+
           ((3 :num),(a_3 :int)) |+ ((4 :num),(a_4 :int)) |+
           ((5 :num),(a_5 :int)) |+ ((6 :num),(a_6 :int)) |+
           ((7 :num),(a_7 :int)) |+ ((8 :num),(a_8 :int)) |+
           ((9 :num),(a_9 :int)) |+ ((10 :num),(a_10 :int))))]``

evalPost post ``FEMPTY |++ ^s1`` ``FEMPTY |++ ^s2``

val s2 = ``[("left",(if a_9 = x then Scalar 9 else Scalar 10)); ("x",Scalar x);
 ("aLength",Scalar 10); ("Result",Scalar Result);
 ("result",(if a_9 = x then Scalar 9 else Scalar ~1));
 ("a",
  Array
    (FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8)  |+ (9,a_9)))]``

val listCond =      ``((if a_0 = x then 0 else ~1) = ~1) /\
       ((if a_1 = x then 1 else ~1) = ~1) /\
       ((if a_2 = x then 2 else ~1) = ~1) /\
       ((if a_3 = x then 3 else ~1) = ~1) /\
       ((if a_4 = x then 4 else ~1) = ~1) /\
       ((if a_5 = x then 5 else ~1) = ~1) /\
       ((if a_6 = x then 6 else ~1) = ~1) /\
       ((if a_7 = x then 7 else ~1) = ~1) /\
       ((if a_8 = x then 8 else ~1) = ~1) /\
       ~(((if a_9 = x then 9 else ~1) = ~1) /\ (if a_9 = x then T else F))``

EVAL listCond

val l1 = getRes((COND_CONV THENC REWRITE_CONV []) listCond)
val l1' = getRes(EVAL l1)

val ll = ``if a_0:int = x:int then F else T``
TOP_DEPTH_CONV cond_CONSTANT_F_CONV ll

(TOP_DEPTH_CONV cond_CONSTANT_F_CONV THENC REWRITE_CONV []) l1'
(TOP_DEPTH_CONV cond_CONSTANT_T_CONV THENC REWRITE_CONV []) l1'



val l = ``(if a_0 = x then F else T) /\ (if a_1 = x then F else T) /\
      (if a_2 = x then F else T) /\ (if a_3 = x then F else T) /\
      (if a_4 = x then F else T) /\ (if a_5 = x then F else T) /\
      (if a_6 = x then F else T) /\ (if a_7 = x then F else T) /\
      (if a_8 = x then F else T)``

TOP_DEPTH_CONV cond_CONSTANT_F_CONV l1
     handle HOL_ERR t  =>
       let val {origin_structure = or,origin_function=f,message=m } = t
       in
       (print(or ^ "\n");
        print(f ^ "\n");
        print(m ^ "\n");
        ``F``
        )
       end



val t = ``(~(a_0 = x) /\ ~(a_1 = x) /\ ~(a_2 = x) /\ ~(a_3 = x) /\ ~(a_4 = x) /\
 ~(a_5 = x) /\ ~(a_6 = x) /\ ~(a_7 = x) /\ ~(a_8 = x) /\
 ~(~(a_9 = x) /\ (if a_9 = x then T else F))) /\
~((~(a_9 = x) ==>
   ~(a_9 = x) /\ ~(a_8 = x) /\ ~(a_7 = x) /\ ~(a_6 = x) /\ ~(a_5 = x) /\
   ~(a_4 = x) /\ ~(a_3 = x) /\ ~(a_2 = x) /\ ~(a_1 = x) /\
   ~(a_0 = x)) /\
  ((a_9 = x) ==>
   (if Num (if a_9 = x then 9 else ~1) = 9 then
      a_9 = x
    else
      (if Num (if a_9 = x then 9 else ~1) = 8 then
         a_8 = x
       else
         (if Num (if a_9 = x then 9 else ~1) = 7 then
            a_7 = x
          else
            (if Num (if a_9 = x then 9 else ~1) = 6 then
               a_6 = x
             else
               (if Num (if a_9 = x then 9 else ~1) = 5 then
                  a_5 = x
                else
                  (if Num (if a_9 = x then 9 else ~1) = 4 then
                     a_4 = x
                   else
                     (if Num (if a_9 = x then 9 else ~1) = 3 then
                        a_3 = x
                      else
                        (if Num (if a_9 = x then 9 else ~1) = 2 then
                           a_2 = x
                         else
                           (if Num (if a_9 = x then 9 else ~1) = 1 then
                              a_1 = x
                            else
                              (if
                                 Num (if a_9 = x then 9 else ~1) = 0
                               then
                                 a_0 = x
                               else
                                 FEMPTY '
                                 (Num (if a_9 = x then 9 else ~1)) =
                                 x))))))))))))``

simplifyConditional t
(TOP_DEPTH_CONV COND_CONV THENC REWRITE_CONV []) t
(TOP_DEPTH_CONV cond_CONSTANT_T_CONV THENC REWRITE_CONV []) t

val t = ``if Num (if a_9 = x then 9 else ~1) = 9 then
             a_9 = x
          else a_8 = x``

val t = ``if  ((if a_9 = x then 9 else ~1) = 9) then
             a_9 = x
          else a_8 = x``

val t = ``(a_9 = x) ==>
   (if Num (if a_9 = x then 9 else ~1) = 9 then
      a_9 = x
    else
      (if Num (if a_9 = x then 9 else ~1) = 8 then
         a_8 = x
       else
         (if Num (if a_9 = x then 9 else ~1) = 7 then
            a_7 = x
          else
            (if Num (if a_9 = x then 9 else ~1) = 6 then
               a_6 = x
             else
               (if Num (if a_9 = x then 9 else ~1) = 5 then
                  a_5 = x
                else
                  (if Num (if a_9 = x then 9 else ~1) = 4 then
                     a_4 = x
                   else
                     (if Num (if a_9 = x then 9 else ~1) = 3 then
                        a_3 = x
                      else
                        (if Num (if a_9 = x then 9 else ~1) = 2 then
                           a_2 = x
                         else
                           (if Num (if a_9 = x then 9 else ~1) = 1 then
                              a_1 = x
                            else
                              (if
                                 Num (if a_9 = x then 9 else ~1) = 0
                               then
                                 a_0 = x
                               else
                                 FEMPTY '
                                 (Num (if a_9 = x then 9 else ~1)) =
                                 x))))))))))``

val th = ``!c:bool x1:int x2:int.
       c ==> ((if c then x1 else x2) = x1)``
prove(th,METIS_TAC [])

val

*)

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


(* lre problème est quand on accède à un lément de tableau d'indice
inconnu, on se retrouve avec FEMPTY!!!

val st = ``[("left",(if a_9 = x then Scalar 9 else Scalar 10)); ("x",Scalar x);
 ("aLength",Scalar 10); ("Result",Scalar Result);
 ("result",(if a_9 = x then Scalar 9 else Scalar ~1));
 ("a",
  Array
    ( FEMPTY |+ (0,a_0) |+ (1,a_1) |+ (2,a_2) |+ (3,a_3) |+ (4,a_4) |+
     (5,a_5) |+ (6,a_6) |+ (7,a_7) |+ (8,a_8) |+ (9,a_9) |+ (i,a_i)))]``

val s = ``FEMPTY |++ ^st``

val cond = ``\state1:state state2. ArrayOf (state2 ' "a") ' (Num (ScalarOf (state2 ' "Result")))=
ScalarOf (state1 ' "aLength")``

EVAL ``^cond ^s ^s``

>       ((if Num Result = i then
           a_i
         else
           (if Num Result = 9 then
              a_9
            else
              (if Num Result = 8 then
                 a_8
               else
                 (if Num Result = 7 then
                    a_7
                  else
                    (if Num Result = 6 then
                       a_6
                     else
                       (if Num Result = 5 then
                          a_5
                        else
                          (if Num Result = 4 then
                             a_4
                           else
                             (if Num Result = 3 then
                                a_3
                              else
                                (if Num Result = 2 then
                                   a_2
                                 else
                                   (if Num Result = 1 then
                                      a_1
                                    else
                                      (if Num Result = 0 then
                                         a_0
                                       else
                                         FEMPTY ' (Num Result)))))))))))) =
        10)

val t = ``if Num Result = 2 then
              a_2
          else
              (if Num Result = 1 then
                   a_1
               else
                   (if Num Result = 0 then
                        a_0
                    else
                        FEMPTY ' (Num Result))) =
        10``

val th = ``((Num Result =2) \/ (Num Result =0)\/ (Num Result =1))
   ==> (t = ((if Num Result = 2 then
              a_2:int
          else
              if Num Result = 1 then
                   a_1
               else a_0) = 10))``

val th = ``(Num Result =2)
   ==> (t = (a_2:int = 10))``

   prove(th,METIS_TAC [])



val th = ``!c:bool x1:int x2:int.
       c ==> ((if c then x1 else x2) = x1)``
prove(th,METIS_TAC [])
OK

val th = ``!c1:bool c2:bool x1:int x2:int.
       (c1 \/ c2)  ==>
         ~((if c1 then (if c2 then x1 else x2) else x3) = x3)``
prove(th,METIS_TAC [])

SIMP_CONV (srw_ss()++intSimps.COOPER_ss++ARITH_ss) [] th


DB.match [] ``if c then x1 else x2``

val t = `` FEMPTY '
     (Num
          (if a_9 = x then
               9
           else
               ~1))``



*)
