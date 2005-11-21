(***************************************************************************
 *
 *  jbUtils. sml
 *
 *  useful conversions, tactics, and ML functions
 *  Jens Brandt
 *
 ***************************************************************************)

structure jbUtils :> jbUtils =
struct

(* interactive mode
app load ["schneiderUtils"];
*)

open HolKernel boolLib Parse bossLib schneiderUtils;

val AND_IMP_RULE = REWRITE_RULE[AND_IMP_INTRO];
val IMP_AND_RULE = REWRITE_RULE[GSYM AND_IMP_INTRO];

(*==========================================================================
 *  tactics
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  REWRITE1_TAC, PROVE1_TAC
 *--------------------------------------------------------------------------*)

fun ONCE_REWRITE1_TAC(thm1:thm) = ONCE_REWRITE_TAC [thm1];
fun REWRITE1_TAC(thm1:thm) = REWRITE_TAC [thm1];
fun PROVE1_TAC (thm1:thm) = PROVE_TAC[thm1];

(*--------------------------------------------------------------------------
 *  REMAINS_TO_PROVE term -> tactic
 *
 *  construct new subgoal that solves the current one
 *--------------------------------------------------------------------------*)

fun REMAINS_TO_PROVE (t:term) = SUBGOAL_THEN t PROVE1_TAC;

(*--------------------------------------------------------------------------
 *  NEW_GOAL_TAC term -> tactic
 *
 *  replace current goal by another one (checked by PROVE_TAC)
 *--------------------------------------------------------------------------*)

fun NEW_GOAL_TAC (t:term) =
	SUBGOAL_THEN t MATCH_MP_TAC THEN1 PROVE_TAC[];

(*--------------------------------------------------------------------------
 *  ASSUME_X_TAC thm -> tactic
 *
 *  put a new assumption in front of the goal
 *--------------------------------------------------------------------------*)

fun ASSUME_X_TAC (thm1:thm) = ASSUME_TAC thm1 THEN UNDISCH_HD_TAC;

(*--------------------------------------------------------------------------
 *  DISJ_LIST_CASES_TAC thm -> tactic
 *
 *  apply DISJ_CASES_TAC repeatedly for a theorem
 *--------------------------------------------------------------------------*)

fun DISJ_LIST_CASES_TAC (thm1:thm) (asm_list, goal) =
let
	val cases_thm = GEN ``P:bool`` (prove(mk_imp (list_mk_conj (map (fn x => ``^x ==> P:bool``) (strip_disj (concl thm1))), ``P:bool``), PROVE_TAC[thm1]))
in
	(MATCH_MP_TAC (SPEC goal cases_thm) THEN REPEAT CONJ_TAC THEN STRIP_TAC) (asm_list, goal)
end

(*--------------------------------------------------------------------------
 *  NESTED_ASM_CASES_TAC term list -> tactic
 *
 *  [a,b,c]  ->  a \/ ~a /\ (b \/ ~b /\ (c \/ ~c)
 *--------------------------------------------------------------------------*)

fun NESTED_ASM_CASES_TAC nil = ALL_TAC
	| NESTED_ASM_CASES_TAC (h::t) = ASM_CASES_TAC (h) THENL [ALL_TAC,(NESTED_ASM_CASES_TAC t)];


(*==========================================================================
 *  ML functions
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  print a message before proving the theorem (for debugging purposes)
 *--------------------------------------------------------------------------*)

fun store_thm_verbose (s:string, t:term, tac:tactic) =
	let
		val _ = print ("Proving " ^ s ^ "...\n")
	in
		store_thm(s,t,tac)
	end;

(*--------------------------------------------------------------------------
 *  in_list : ''a list -> ''a -> bool
 *--------------------------------------------------------------------------*)

fun in_list l1 p1 =
	(exists  (fn (x) => (x = p1)) l1);

(*--------------------------------------------------------------------------
 *  list_merge : ''a list -> ''a list -> ''a list
 *--------------------------------------------------------------------------*)

fun list_merge l1 l2 =
	l1 @ filter (fn x => not (in_list l1 x)) l2;

(*--------------------------------------------------------------------------
 *  list_xmerge : ''a list list -> ''a list
 *--------------------------------------------------------------------------*)

fun	  list_xmerge (nil) = []
	| list_xmerge (first::nil) = first
	| list_xmerge (first::rest) = list_merge first (list_xmerge rest);

(* ---------- test cases ---------- *
	list_xmerge [[``f1:frac``]];
	list_xmerge [[``f1:frac``,``f2:frac``],[``f2:frac``,``f3:frac``]];
 * ---------- test cases ---------- *)

(*--------------------------------------------------------------------------
 *  extract_terms_of_type : hol_type -> term -> term list
 *--------------------------------------------------------------------------*)

fun extract_terms_of_type (typ1:hol_type) (t1:term) =
	if type_of t1 = typ1 then
		[t1]
	else
		if is_comb t1 then
			let
				val (top_rator, top_rand) = dest_comb t1;
			in
				list_merge (extract_terms_of_type typ1 top_rator) (extract_terms_of_type typ1 top_rand)
			end
		else
			[];

(*--------------------------------------------------------------------------
 *  dest_binop_triple : term -> term * term * term
 *--------------------------------------------------------------------------*)

fun dest_binop_triple tm =
	let val (Rator,rhs) = Term.dest_comb tm
		val (opr,lhs) = Term.dest_comb Rator
	in
		(opr,lhs,rhs)
	end;

end; (* of struct *)
