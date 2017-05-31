(* selftest.sml \lstset{language=ML,upquote=true}\begin{comment} % *)
(* %
\end{comment} % (*
*)
\begin{comment}==LITERATE PROGRAM FILE HEADER =======================================================\end{comment}

\section{HOL Preliminaries}

The HOL logic system provides a proof manager which manages the derivation of an proof.  It does so using a 
structure which represents a list of assumptions, a desired conclusion, and a list of theorems from which justify the 
conclusion as drawn from the assumptions.  A goal is a similar structure, without the theorems: that is, the goal consists
of a list of assumptions and a conclusion for which a proof is desired. The derivation of a proof is a tree structure
and can be represented using a fractional notation, where the numerator represents the goal, and the denominator represents
a set of sub-goals which result from a mechanical application of a rule of logic.  

Another way of looking at a deriviation is to treat the top-most goal as the root of a tree; the sub goals sprout out 
from the root, and whenever the outermost sub-goals evaluates to true or false, it is a leaf.  
Once we have evalauted sub-goal in such a manner, the corresponding terms from the trunk can be substituted.

There are a number of libraries in HOL which make this possible.  One library in particular,  known as `bossLib', 
provides a suite of basic automated proving tools.  A number of other libraries provide type syntaxes which make it
possible to extends HOLs native data types to include numbers, strings and lists.
We first load these libraries and open them to make them public.    

Once the internal features of the bossLib structure are exposed to the HOL session, terms can now consist of expressions on strings, numbers and lists. 
As per HOL recommendations, other libraries required by the test case should be open at the front of the file befor any other commands.

Following this, flags can be set to tailor the environment to the users liking.  In the case of this file, to get feedback about data types and proofs,
we enable the HOL system to display all assumptions and data types currently in use.

\begin{lstlisting} % *)

(* load "stringTheory"; *)
(* val _ = load "imperativeTheory"; *)
open HolKernel Parse boolLib bossLib numSyntax listSyntax stringTheory arithmeticTheory;
open ptopTheory imperativeLib imperativeTheory ;

val _ = set_trace "Unicode" 0;

val _ = show_types:=true;
val _ = show_assums:=true;

val OK = testutils.OK
val die = testutils.die
val tprint = testutils.tprint;


(* \end{lstlisting}


\section{Theory of Imperative Programming by Example}

The language of program refinement is that of logic: truth and falsehood. Truth, however, is a much loftier goal than the more practical
problems faced by software engineers; to mistake program correctness for truth is philosophically invalid.  Rather, when we speak of truth 
in a programming context, it is intended to reflect whether a final state meets a logical specification given an initial state. 
The ptopTheory defines two specifications $abort$ and $magic$, which we use when it is important to stress this interpretation of truth.  
Given any initial state and any final state, $abort$ always returns true, while $magic$  always returns false.  
Always returning true means there's no point going further -- the program has reached it's accepted limit.   
Always returning false means that you have to continue, knowing that no matter what else you do, it won't be enough to satisfy the requirements. 

section{Definition of Assignment }

The ptopTheory defines assignment as guaranteeing that the value of a state-variable x in the next state $s'$ is equal to an expression evauated in the current state $s$.
The following provides a test of this definition.
 
\begin{lstlisting} % *)

val _ = let	val	
		xForyImplies_sx_Is_es = 
		(
				EVAL_RULE (SPEC ``x:'a`` (EVAL_RULE (ASSUME ``assign x e s s'``)))
						(*	[
								assign x e s s'	
							]	|-
								s' x  = e s  : thm
						*)
		)

	in
		prove (
			``(\ (s :'a -> 'b) (s' :'a -> 'b).((s'(x:'a)) = ((e:('a->'b)->'b) s))) [=. (assign x e)``,
			(
				(REFINEMENT_TAC)	
						(*	[
							]	|-
								 assign x e s s'	
								 ==>
								 s' x = e s	
						*)
			THEN
				(DISCH_TAC)	
						(* 	[ 	
								assign x e s s'	
							]	|- 
								s' x = e s	
						*)
			THEN 
				(ACCEPT_TAC xForyImplies_sx_Is_es)
			)
		)
	end
;

(* \end{lstlisting} 

For novice users of HOL, the above code demonstrates seven commonly used tactics of the HOL proving system, namely:

\begin{enumerate}
\item{ASSUME, ASSUME_TAC}

Given a theorem whose assumptions are a subset of the current goal, adds the theorems conclusion to goal's assumptions.

\item{EVAL_RULE}

Creates an equality between the theorems conclusion and the result of evaluating its terms and functions.
\item{SPEC,SPECL}

Allows a general theorem to be specialized to a particular instance. 
SPECL allows parallel execution of multiple SPEC tactics using a list of instances.
\item{SUBST_TAC}

Given an equality, if the left-hand side is a term in the goal, then it is replaced by the right-hand side.
\item{DISCH_TAC}

Given an implications, moves the left-hand side of the implication into the list of assumptions.
\item{ACCEPT_TAC}

Once a sub-goal has been converted into the form of an existing theorem, this tactic promotes the sub-goal to a theorem.
\end{enumerate}

\section{Sequential Composition}

Sequential composition is made possible in ptopTheory by using an existential specification.  
Specifically, we assert that there exists an intermediate state, $s''$,  such that initial specification $f$ provides a path from $s$ to $s''$, 
and the final specification $g$ provides a path from $s''$ to $s'$.  As an example of how to use this, consider how the specification

\[ s' x = 1 \and s' y = 1\]

is satisfied by $y:=1;x:=y$. (here the semicolon is used to indicate sequential composition of two instructions).
 
\begin{lstlisting} % *)

fun testRefinement rhsProgLhsSpec = let	val	
		lemma = 
	 		(UNDISCH_ALL (#1 (EQ_IMP_RULE (EVAL (mk_comb(mk_comb ((rand rhsProgLhsSpec),``s:'a->num``),``s':'a->num``))))))
						(*	[
								sc (assign y (\s. 1)) (assign x (\s. s y)) s s'
							]	|-
								    ?s''. 
										(!y'. if y = y' then s'' y' = 1 else s'' y' = s y') 
										/\
										(!y'. if x = y' then s' y' = s'' y else s' y' = s'' y')
						*)
	in
		prove 
		(
			rhsProgLhsSpec,
			(
				(REFINEMENT_TAC)
						(*	[
							]	|-
									sc (assign y (\s. 1)) (assign x (\s. s y)) s s' ==> (s' x = 1) /\ (s' y = 1)
						*)
			THEN
				(STRIP_TAC)	
						(* 	[ 	
								sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s' x = 1) /\ (s' y = 1)
						*)
			THEN 
				(STRIP_ASSUME_TAC lemma)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s' x = 1) /\ (s' y = 1)
						*)
			THEN
				(SUBST_TAC
					[(
						EVAL_RULE 												
							(
								(SPECL [``x:'a``]	(ASSUME ( #2(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
							)
					)]
				)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s'' y = 1) /\ (s' y = 1)
						*)
			THEN
				(SUBST_TAC
					[(
						EVAL_RULE 												
							(
								(SPECL [``y:'a``]	(ASSUME ( #2(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
							)
					)]
				)
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y (\s. 1)) (assign x (\s. s y)) s s' 
							]	|- 
									(s'' y = 1) /\ (s'' y = 1 )
						*)
			THEN
				(CONJ_TAC THENL
					[(
						(* 	[ 	
								 !y'. if x = y' then s' y' = s'' y else s' y' = s'' y'
							,
								 !y'. if y = y' then s'' y' = 1 else s'' y' = s y'
							,
								 sc (assign y ( \s. 1)) (assign x ( \s. s y)) s s' 
							]	|- 
									(s'' y = (1 :num))
						*)				
						(ACCEPT_TAC
							(
								EVAL_RULE 
								(
									(SPECL [``y:'a``]	(ASSUME (#1(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
								)
							)
						)
					),(
						(ACCEPT_TAC
							(
								EVAL_RULE 
									(
										(SPECL [``y:'a``]	(ASSUME (#1(dest_conj (beta_conv(mk_comb((rand (concl  lemma)),``s'':'a->num``)))))))
									)
							)
						)
					)]
				)
			)
		)
	end

val rhsProgRefinesLhsSpec = ``(\ (s:'a->num) (s':'a->num). (((s' (x:'a)) = 1 ) /\ ((s' (y:'a)) = 1))) [=. (sc (assign y (\ (s:'a->num).1)) (assign x (\ (s:'a->num).(s y))))``; 

val _ = tprint ("some implementation refines given specification: " );
val _ = testRefinement(rhsProgRefinesLhsSpec) handle HOL_ERR _ => die "rhsProgRefinesLhsSpec FAILED";
val _ = OK();


(* \end{lstlisting} % 

The example above introduces the following tactics and rules:

\begin{enumerate}
\item{UNDISCH_ALL}

Given a list of assumptions, converts them into a chain of refinements.

\item{EQ_IMP_RULE}

Swaps the left-hand and right-hand side of an equation, as required to apply the SUBST_TAC.
\item{STRIP_TAC,STRIP_ASSUME_TAC}

Similar to DISCH_TAC, but decomposes assumptions to remove quantifiers and conjunctions so that they can be more readily used.
\item{CONJ_TAC, EQ_TAC}

If a theorem is in the form a conjunction, this breaks the goal into two sub-goals, one for the left-hand side,
the other for the right-hand side.  EQ_TAC was not used in the example, but does the same for equations.

\item{rand,rator,dest_conj,beta_conv,mk_comb, concl, etc}

These are a variety of routines defined in the Term structure which are useful for extracting and transforming specific 
terms into the form needed to prove a goal.
\end{enumerate}

\section{Swapping Algorithms}

The final exercise is to demonstrate the use of the theory on some sample programs.

A useful function on state spaces is the swap command which is defined as:

(s' x = s y /\ s' y = s x) 

where s is free provided that s x and s y exist and are of the same type.  
Without reducing the generality of the proofs, from this point on the examples use strings (variable names) to instantiate variables $x$ and $y$ of type $'a$ 

We wish to show that provided $s x$, $s' x$, $s y$ and $s' y$ are the same type, the following are valid implementatons:

\begin{enumerate}
\item{in the general case }
\item{using an algebraic method in the case where s x and s y are numeric}
\end{enumerate}

The proof benefits from a function EVAL_FOR_STATEVARS defined in imperativeLib that allows EVAL_TAC to be applied for every variable name.

In the general case, we create a temporary variable and assign to it the value of one of the values to be swapped.  
The first variable is then assigned the value of the other variable, and then the other variable in turn is assigned the value of the temporary variable.

\begin{lstlisting} % *)

val _ = tprint ("swap is possible with introduction of temporary variable: " );
val GeneralSwap = let val
	conversion =	
			PURE_ONCE_REWRITE_RULE [PREDICATIVE_SPEC_EQ_THM] 
			(
				SPECL 
					[
						``"t"``,
						``(assign "x" (\ (s:string->'b). s "y"))``,
						``(\ (s:string->'b).s "x")``
					]   
					(INST_TYPE 
						[	alpha |-> ``:string``, 
							gamma |-> ``:string->'b``
						] 
						(	REFINEMENT_RULE 
							(	
								SPECL 
									[
										``f:('a->'b)->'c->bool``,
										``e:('a->'b)->'b``,
										``x:'a``
									] 
									FORWARD_SUB
							)	
						)
					)
			)
	in
		prove
		(
			``	( 
					(
						\ (s:string->'b) (s':string->'b) . ((s' "x") = (s "y")) /\ ((s' "y") = (s "x"))
					) 
					[=. 
					( 
						sc 
						(
							sc	(assign ("t") (\ (s:string->'b).s "x")) (assign "x" (\ (s:string->'b). s "y"))
						)
						(assign "y" (\ (s:string->'b).s "t")) 
					)
				)
			``
			,
			(SUBST_TAC [conversion])
				(*	[				
					]	|- 
							 (\s s'. (s' "x" = s "y") /\ (s' "y" = s "x")) [=. sc (subs (assign "x" (\s. s "y")) "t" (\s. s "x")) (assign "y" (\s. s "t"))					
				*)
		THEN
			(REP_EVAL_TAC)
				(*	[
					]	|-
							!s s'.  
								(?s''. 
										(!y.if "x" = y then  s'' y = s "y"  else s' y = if "t" = y then s "x" else s y) 
												/\
										(!y. if "y" = y then s' y = s'' "t" else s' y = s'' y) 
								)
								==>
									(s' "x" = s "y") /\ (s' "y" = s "x")
				*)
				
		THEN
			(REPEAT STRIP_TAC)	
		THEN
			(EVAL_FOR_STATEVARS [``"t"``,``"x"``,``"y"``])
		THEN
			REP_EVAL_TAC
		)
	end
handle HOL_ERR _ => die "general swap FAILED";
val _ = OK();

(* \end{lstlisting}

In the special case where both variables are numbers, an algebraic method can be used to swap the values without the use of a temporary variable.

\begin{lstlisting} % *)

(*
	need this for LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0, and ADD_0
	
*)

val _ = tprint ("swap is possible for num type without need for temporary variable: " );
val NumericSwap = let val
		conversion =	
			PURE_ONCE_REWRITE_RULE [PREDICATIVE_SPEC_EQ_THM] 
			(
				SPECL 
					[
						``"x"``, 
						``(assign "y" (\ (s:string->num). ((s "x") - (s "y"))))``, 
						``(\ (s:string->num).((s "x") + (s "y")))``
					] 
					(INST_TYPE 
						[	
							alpha |-> ``:string``, 
							beta |-> ``:num``, 
							gamma |-> ``:string->num``
						] 
						(	REFINEMENT_RULE
							(
								SPECL 
									[
										``f:('a->'b)->'c->bool``,
										``e:('a->'b)->'b``,
										``x:'a``
									] FORWARD_SUB
							)
						)
					)
			)
	and
		lemma = prove (``!(a:num) (b:num). (a + b -(a + b -b)) = (b + a - a)``,(PROVE_TAC [LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0,ADD_0,ADD_SYM]))
	in
		prove
		(
			``	
				( 
					\ (s:string->num) (s':string->num). ((s' "x") = (s "y")) /\ ((s' "y") = (s "x"))
				) 
				[=. 
				( 
					sc 
						(
							(	sc
									(assign "x" (\ (s:string->num).((s "x") + (s "y")))) 
									(assign "y" (\ (s:string->num). ((s "x") - (s "y"))))
							)
						)
						(
								assign "x" (\ (s:string->num).((s "x") - (s "y")))
						)
				)
			``
			,
			(SUBST_TAC [conversion])
				(*	[
					]	|-
							(\(s :string -> num) (s' :string -> num). (s' "x" = s "y") /\ (s' "y" = s "x")) 
							[=.
								 sc
								   (subs (assign "y" (\(s :string -> num). s "x" - s "y")) "x"
									  (\(s :string -> num). s "x" + s "y"))
								   (assign "x" (\(s :string -> num). s "x" - s "y"))
				*)
		THEN
			(REP_EVAL_TAC)
		THEN
			(REPEAT STRIP_TAC)	
		THEN
			(EVAL_FOR_STATEVARS [``"x"``,``"y"``])
		THEN
			(PROVE_TAC [LESS_EQ_REFL, LESS_EQ_ADD_SUB, SUB_EQ_0,ADD_0,lemma])
		)
	end
handle HOL_ERR _ => die "numeric swap FAILED";
val _ = OK();

(* \end{lstlisting}


This concludes the demonstration.

\begin{comment}===LITERATE PROGRAM FILE TRAILER =======================================================\end{comment}
 \begin{lstlisting} 
(* 
   Last updated April 3, 2017
*) 
\end{lstlisting}  %
% *)
