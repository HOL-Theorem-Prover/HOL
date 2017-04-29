load "tautLib";
load "stringTheory";
load "numTheory";
load "ptopTheory";
load "imperativeLib";
load "imperativeTheory";
open tautLib ptopTheory imperativeLib imperativeTheory;

val _ = set_trace "Unicode" 0;

val _ = show_types:=true;
val _ = show_assums:=true;

val simpleTruthForgettableName1 = TAUT_PROVE (``!(a:bool) (b:bool). (  (~ (a       ==> b) ) <=> (   a  /\  ~ b  ) )``);
val simpleTruthForgettableName2 = TAUT_PROVE (``!(a:bool) (b:bool). (  (~ ( a       /\ b) ) <=> ( (~a) \/ (~ b) ) )``);

val simpleTruths = [
	simpleTruthForgettableName1,
	simpleTruthForgettableName2
];

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

val statevars = [``x``,``y``,``t``];

val lhsSpec = ``(\ (s:'a->num) (s':'a->num). (((s' (x:'a)) = 1 ) /\ ((s' (y:'a)) = 1)))``;
val goodImplementation = ``(sc (assign y (\ (s:'a->num).1)) (assign x (\ (s:'a->num).(s y ))))``; 
val badImplementation = ``(sc (assign y (\ (s:'a->num).(s x))) (assign x (\ (s:'a->num).1 )))``;


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
				(REWRITE_TAC [BETA_RULE (SPEC P (INST_TYPE [alpha |-> ``:'a->num``,beta |-> ``:'a->num``] SWAP_EXISTS_THM))] goal)
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

(*val matchMeToo = (let val gl = ( strip_exists (#2(top_goal())) ) in 
	mk_abs ( (hd(#1(gl))), (mk_abs ( hd(tl(#1(gl))), (#2(gl)) ) )
*)

fun theTac statevars = (	
	(REPEAT STRIP_TAC)
THEN
	(REFINEMENT_TAC)
THEN
	(REWRITE_TAC simpleTruths)
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


fun rhsProgLhsNotSpec rhsProg = mk_icomb(mk_icomb(REFINEMENT_NOT_RATOR,lhsSpec),rhsProg);

fun rhsProgLhsSpec rhsProg = mk_icomb(mk_icomb(REFINEMENT_RATOR,lhsSpec),rhsProg);

fun testIt asl b = if b then 
	set_goal([], mk_imp ( list_mk_conj(asl), (rhsProgLhsSpec goodImplementation ) ) ) 
else 
	set_goal([], mk_imp ( list_mk_conj(asl), (rhsProgLhsNotSpec badImplementation) ) ) 
;


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

testIt (DECL_STATEVARS ``v:'a`` statevars) true;
testIt (DECL_STATEVARS ``v:'a`` statevars) false;

(*
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
