(* Interactive mode: 
load "tautLib";
load "stringTheory";
load "numTheory";
load "ptopTheory";
load "imperativeLib";
load "imperativeTheory";
*)
open HolKernel Parse boolLib bossLib numSyntax listSyntax stringTheory arithmeticTheory;
open tautLib ptopTheory imperativeLib imperativeTheory ;

val _ = set_trace "Unicode" 0;

val _ = show_types:=true;
val _ = show_assums:=true;

val OK = testutils.OK
val die = testutils.die
val tprint = testutils.tprint;

(* 
The examples created in this folder were produced interactively without the assistance of heavy-duty solvers such as HOLyHAMMER.
Producing proofs interactively helps a novice learner to see HOL in action, but it is time-consuming.  On occasion, 
the presence of quantifiers or non-boolean types can cause obvious transformations to be overlooked.  In these case, the
use of the built-in provers is a great time-saver.  By restating these in terms of BOOLEAN data-types, HOLs database of theorems 
can be summoned by form alone to direct the progress of the proof. The resuting theorems can be tailored to one's one purposes
using INST_TYPE, SPECL and REWRITEs
*)
val simpleTruthForgettableName1 = TAUT_PROVE (``!(a:bool) (b:bool). (  (~ (a       ==> b) ) <=> (   a  /\  ~ b  ) )``);
val simpleTruthForgettableName2 = TAUT_PROVE (``!(a:bool) (b:bool). (  (~ ( a       /\ b) ) <=> ( (~a) \/ (~ b) ) )``);
val simpleTruthForgettableName3 = prove(
	``!(z:num)(z':num)(x:'a)(x':'a).(
		((if x = x' then ((if x = x' then 1 else 0) = z) else ((if x = x' then 1 else 0) = z'))
	<=>
		(if x = x' then (1 = z) else (0 = z'))))
	``,(METIS_TAC [])
);
val simpleTruthForgettableName4 = prove(
	``!(z:num) (z':num)(v:bool).( 
		((~v) ==> ( (if v then z else z' ) <> z) )
	<=> 
		( (~v) ==>(z' <> z ) ))
	``,(METIS_TAC [])
);

(* 
Here the program is defined.  We introduce as many variables/contants of type ``:'a`` as we need. 
The logic assumes that the free-variables named explicity here are distinct from one another.
*)
val statevars = [``x``,``y``,``t``];

(* 
Another axiom of the logic is that for any free statespace variables of type ```:'a`` above, there are at least as 
many state-spaces are there are constants of type ``:b``. 

The left-hand spec pairs these states up and returns true if either the input state does not apply, or the output
state exhibits a correct response for the input.
*)
val theSpec = ``(\ (s:'a->num) (s':'a->num). (((s' (x:'a)) = 1 ) /\ ((s' (y:'a)) = 1)))``;

(* 
A program is written using commands defined in ptopScript.sml.  
Each of these commands is associated with a behavioral specification.
A good implementation is one in which the behaviours result in the correct final response.
*)
val goodImplementation = ``(sc (assign y (\ (s:'a->num).1)) (assign x (\ (s:'a->num).(s y ))))``; 

(* 
The following tactic is a good starting point for proving refinement when the main operations are 
assignment and sequential composition.
*)

val simpleRewrites = [
	simpleTruthForgettableName1,
	simpleTruthForgettableName2
];

fun theTac statevars = (	
	(REPEAT STRIP_TAC)
THEN
	(REFINEMENT_TAC)
THEN
	(REWRITE_TAC simpleRewrites)
THEN
	(REWRITE_TAC [FORWARD_SUB])
THEN
	(REP_EVAL_TAC)
THEN
	(REPEAT STRIP_TAC)
THEN
	(EVAL_FOR_STATEVARS statevars ) 
THEN 
	REP_EVAL_TAC
);

(* 
Given a good specification, a good implementation, a successful set of tactics, and an interactive
theorem prover by which to inspect the progress of the proof, we can provide examples where the 
prover verifies a program to meet its specification.
*)

fun assumeAensureH (A:term list) (H:term) = mk_imp ( list_mk_conj(A), (H) ) 
fun LHSrefinedbyRHS (lhsSpec:term)  (rhsProg:term) = mk_icomb(mk_icomb(REFINEMENT_RATOR,lhsSpec),rhsProg)

val _ = tprint ("some implementation refines given specification: " );

val _ = let val proveSo = (
		prove(
			assumeAensureH( 
				(DECL_STATEVARS ``v:'a`` statevars), 
				(LHSrefinedbyRHS (theSpec)  (goodImplementation) )
			),
			theTac (statevars)
		);
		NONE
	)
	handle 
		HOL_ERR _ => SOME "refinement not proven"
in case proveSo of
      NONE => OK()
     | SOME s => die s
 end;

(* 
If we made it here, then there is no more work to be done.
But what if we didn't.  If the proof fails, we cannot be certain that we have disproved refinement.
Can we provide an certainty to the user that the result is because their program has a bug, and not 
that our test was flawed?
*)

val _ = tprint ("sometimes refinement is not proven: " );

val disputedImplementation = ``(sc (assign y (\ (s:'a->num).(s x))) (assign x (\ (s:'a->num).1 )))``;

fun LHSnotrefinedbyRHS (lhsSpec:term)  (rhsProg:term) = mk_icomb(mk_icomb(REFINEMENT_NOT_RATOR,lhsSpec),rhsProg)

(* 
Refinement is proven above by demonstrating that the laws of programming theory ensure the spec holds for all states.
Nonrefinement is an existental proof.  Often existential proofs are handled by SAT solvers, but an automated theorem
prover can help by suggesting where the laws may allow witnesses to occur.
Alternate tactics are required to extract these suggestions from the prover.
*)

val altTac1 = ( 
	fn goal:((term list) * term) => (
		(let val
			Px =(#2 (strip_forall( rand( rator( #2(strip_exists(#2(goal))) ) ) ) ) )
		in (let val
			P = mk_abs(``v:'a``,Px)
		 in (let val
			Q= ( rand (#2(strip_exists(#2(goal))) ))
		  in 
			(REWRITE_TAC [BETA_RULE (SPECL [P,Q] LEFT_AND_FORALL_THM) ] goal)
		  end)
		 end)
		end)
	)
);

val altTac2 = ( 
	fn goal:((term list) * term) => (
		(let val
				Px =( strip_exists(#2(goal)) )
	 	in 
			(let val
				P = mk_abs( hd(#1(Px)), mk_abs( hd (tl(#1(Px))), (#2(Px)) ) )
			in 
				(REWRITE_TAC	[BETA_RULE (SPEC P (INST_TYPE [alpha |-> ``:'a->num``,beta |-> ``:'a->num``] 
								SWAP_EXISTS_THM))] 
						goal
				)
		  	end)
		end)
	)
);

fun altTac statevars = (
	altTac1
THEN
	(EVAL_FOR_STATEVARS statevars ) 
THEN 
	REP_EVAL_TAC
THEN
	altTac2
);
	
(*
testIt (DECL_STATEVARS ``v:'a`` statevars) false;

e (theTac statevars);

(* e ((EVAL_FOR_STATEVARS statevars) THEN REP_EVAL_TAC); *)

e  (EXISTS_TAC ``\(v:'a). ( if (x:'a)=v then 1 else ( ( \(v':'a).0) (v) ) )``);
e  (EXISTS_TAC ``\(v':'a).0``);

e (GEN_TAC THEN (REPEAT STRIP_TAC) THEN REP_EVAL_TAC);

e (REWRITE_TAC [SPECL [``1``,``0``] simpleTruthForgettableName3]);

e (CHANGED_TAC REP_EVAL_TAC);

e (UNDISCH_TAC ``  (x :'a) <> (y :'a)``);
e ((REWRITE_TAC [SPECL [``1``,``0``] simpleTruthForgettableName4]) THEN DISCH_TAC THEN EVAL_TAC);
*)
(*val matchMeToo = (let val gl = ( strip_exists (#2(top_goal())) ) in 
	mk_abs ( (hd(#1(gl))), (mk_abs ( hd(tl(#1(gl))), (#2(gl)) ) )
*)
(* val _ = let 
	val asl = (DECL_STATEVARS ``v:'a`` statevars)
in
	prove(
		mk_imp( list_mk_conj(asl), 
			mk_icomb(mk_icomb(REFINEMENT_RATOR,lhsSpec),goodImplementation)
		),
		(theTac statevars)
	)
end;
*)


val _ = let val proveSo = (
		prove(
			assumeAensureH( 
				(DECL_STATEVARS ``v:'a`` statevars), 
				(LHSrefinedbyRHS (theSpec)  (disputedmplementation) )
			),
			theTac (statevars)
		);
		NONE
	)
	handle 
		HOL_ERR _ => SOME "refinement not proven"
in case proveSo of
      NONE => OK()
     | SOME s => ( 
     		tprint s;		
		let val proveOtherwise = (
			prove(
				assumeAensureH( 
					(DECL_STATEVARS ``v:'a`` statevars), 
					(LHSnotrefinedbyRHS (theSpec)  (disputedmplementation) )
				),
				altTac (statevars)
			);
			NONE	
		)
		handle 
			HOL_ERR _ => SOME "refinement not disproven"
	in case proveOtherwise of
      		NONE => OK()
     		| SOME s => (
			tprint s(* die s *);	
			tprint "still a work in progress"
		)
	end
	)
 end;


