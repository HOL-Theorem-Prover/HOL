(* =====================================================================*)
(* FILE		: elsaUtils (formerly utilsLib.sml and before that,     *)
(*                   functions.sml and before that, start_groups.ml)    *)
(* DESCRIPTION	: defines a collection of general purpose functions,	*)
(*                rules, and tactics which are used throughout the	*)
(*                group library entry and the integer library entry.	*)
(*									*)
(* AUTHOR       : Elsa Gunter, Bell Labs                                *)
(* DATE		: 89.3.20						*)
(* TRANSLATOR   : Elsa Gunter,                                          *)
(* TRANSLATED   : 91.22.12						*)
(* =====================================================================*)

(* Copyright 1991 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure elsaUtils :> elsaUtils =
struct

open HolKernel Parse Drule Tactical Tactic Conv;

infix THENL THEN ORELSE;


type hol_type = Type.hol_type;
type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic
type conv = Abbrev.conv
type thm_tactic = Abbrev.thm_tactic;


fun UTILSLIB_ERR{function,message} =
    HOL_ERR{origin_structure = "elsaUtils",
            origin_function = function,
            message = message};

(* Some general-purpose functions *)

fun is_contained_in {subset, superset} =
    itlist
      (fn x => fn y => x andalso y)
      (map (fn x => exists (fn y => (aconv x y)) superset) subset)
      true

(* find_match was in the original system *)

(* try to match PATTERN against a subterm of TERM, return the term
   & hol_type substitutions that make PATTERN match the subterm *)

fun find_match {pattern, term} =
    let 
	fun find_match_aux term =
	    match_term pattern term
	    handle HOL_ERR _ =>
		find_match_aux (#Body(dest_abs term))
		handle HOL_ERR _ =>
		    find_match_aux (rator term)
		    handle HOL_ERR _ =>
			find_match_aux (rand term)
			handle HOL_ERR _ =>
			    raise UTILSLIB_ERR
                                    {function = "find_match",
				     message = "no match"}
    in
	find_match_aux term
    end

(*
  mapshape applies the functions in functions to argument lists obtained by
  splitting the list unionlist into sublists of lengths given by partition.
*)

fun mapshape {partition = [],functions = [], unionlist = []} = []
  | mapshape {partition = (n1::rem_lengths),
	      functions = (f::rem_funs),
	      unionlist} =
      let
	  val (first_list,rem_lists) = split_after n1 unionlist
      in 
	  (f first_list) ::
	  (mapshape
	   {partition = rem_lengths,
	    functions = rem_funs,
	    unionlist = rem_lists})
      end
  | mapshape _ = raise UTILSLIB_ERR{function = "mapshape",
                                                 message = "bad fit"}



(*
   The following are derived proof rules and tactics which I found useful
   in developing group theory and the integers.
*)

(* Proof Rules *)


(*
  STRONG_INST, STRONG_INST_TY_TERM and STRONG_INST are like INST, INST_TY_TERM
  and INST, except that they instantiate free variables in the hypotheses,
  rather than failing.  I have also changed the type of their arguments to
  use records to state more explictly which piece of the substitution
  information is the variable bieng substituted for and which piece is the
  expression being substituted.
*)

local
    fun COUNT_UNDISCH 0 thm = thm
      | COUNT_UNDISCH n thm = COUNT_UNDISCH (n -1) (UNDISCH thm)
    fun split_subst [] = ([], [])
      | split_subst ({redex, residue}::rest) =
	let val (vals, vars) = split_subst rest
	in
	    (residue::vals, redex::vars)
	end
in
    fun STRONG_INST_TYPE {type_substitution, theorem} =
	  COUNT_UNDISCH
	    (length (hyp theorem))
	    (INST_TYPE type_substitution (DISCH_ALL theorem))

    fun STRONG_INST_TY_TERM {type_substitution, term_substitution, theorem} =
	let
	    val inst_ty_thm = INST_TYPE type_substitution (DISCH_ALL theorem)
	    val (values,variables) = split_subst term_substitution
	in
	    COUNT_UNDISCH
	      (length (hyp theorem))
	      (SPECL values (GENL variables inst_ty_thm))
	end

    fun STRONG_INST {term_substitution, theorem} =
	let
	    val (values,variables) = split_subst term_substitution
	in
	    COUNT_UNDISCH
	      (length (hyp theorem))
	      (SPECL values (GENL variables (DISCH_ALL theorem)))
	end
end


(*
   AUTO_SPEC : {specialization_term:term, generalized_theorem:thm} -> thm

   (specialization_term = t)
   (Automatically tries to instantiate the type of x to that of t, applying
    the type substitution to the hypotheses as needed.)

       A |- !x.u
   ------------------  
       A |- u[t/x]
*)

fun AUTO_SPEC {specialization_term, generalized_theorem} =
    let
	val type_substitution =
	      match_type
	        (type_of(#Bvar(dest_forall(concl generalized_theorem))))
		(type_of specialization_term)
    in
	SPEC
	  specialization_term
	  (STRONG_INST_TYPE
	     {type_substitution = type_substitution,
	      theorem = generalized_theorem})
    end


(*
   AUTO_SPECL : {specialization_list:term list,
                 generalized_theorem:thm} -> thm

  (specialization_list = [t1;...;tn])

      A |- !x1 ... xn. t(x1,...,xn)
   -----------------------------------
        A |- t(t1,...,tn)

*)

fun AUTO_SPECL {specialization_list, generalized_theorem} =
    rev_itlist
      (fn specialization_term => fn gen_thm =>
         AUTO_SPEC {specialization_term = specialization_term,
		    generalized_theorem = gen_thm})
      specialization_list
      generalized_theorem

(* Are these needed?  
(*
   EQF_INTRO : thm -> thm

     A |- ~t
   ------------
    A |- t = F
*)

fun EQF_INTRO neg_thm =
      EQ_MP
        (SYM(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC
					    (dest_neg(concl neg_thm))
					    EQ_CLAUSES)))))
	neg_thm


(*
   FALSITY_INTRO : {theorem:thm, negated_theorem:thm} -> thm

    A1 |- t  A2 |- ~t
   --------------------
      A1 u A2 |- F

*)

local
    val neg_type = (==`:bool -> bool`==)
in
    fun FALSITY_INTRO {theorem, negated_theorem} =
	let
	    val neg_var =
		 variant
	           (all_varsl ((concl negated_theorem)::(hyp negated_theorem)))
		   (mk_var {Name="neg", Ty=neg_type})
	in
	    if aconv (concl negated_theorem) (mk_neg (concl theorem))
		then
		    MP
		      (BETA_RULE
		       (SUBST[{thm=NOT_DEF, var=neg_var}]
			      (mk_comb {Rator=neg_var, Rand=(concl theorem)})
			      negated_theorem))
		      theorem
	    else raise UTILSLIB_ERR
			   {function = "FALSITY_INTRO",
			    message = "negated_theorem is not the "^
			               "negation of theorem"}
	end
end

fun NORMALIZE rewrite_list thm = REWRITE_RULE rewrite_list (BETA_RULE thm)
*)

(* This should be recordized!! *)

fun MATCH_TERM_SUBS_RULE thm tm =
    let
	val strip_thm = hd (IMP_CANON thm)
	val (term_substitution,type_substitution)=
	      match_term (lhs(concl strip_thm)) tm
    in
	SUBS
	  [(STRONG_INST_TY_TERM
	      {term_substitution=term_substitution,
	       type_substitution=type_substitution,
	       theorem = strip_thm})]
    end
 

(* Tactics *)

(*
   SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A,t] t1    [A] t
*)

local
    val bool = (==`:bool`==)
in
    fun SUPPOSE_TAC new_claim current_goal =
	if type_of new_claim = bool
	    then
		([(new_claim::(fst current_goal),snd current_goal),
		  (fst current_goal, new_claim)],
		 fn [goalthm,claimthm] =>
		   MP (DISCH new_claim goalthm) claimthm
		  | _ => raise UTILSLIB_ERR
				  {function = "SUPPOSE_TAC",
				   message = "invalid application"})
	else raise UTILSLIB_ERR
		       {function = "SUPPOSE_TAC",
			message = "The claim doesn't have type :bool"}
end


(*
   REV_SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A] t    [A,t] t1
*)

local
    val bool = (==`:bool`==)
in
    fun REV_SUPPOSE_TAC new_claim current_goal =
	if type_of new_claim = bool
	    then
		([(fst current_goal, new_claim),
		  (new_claim::(fst current_goal),snd current_goal)],
		 fn [claimthm,goalthm] =>
		   MP (DISCH new_claim goalthm) claimthm
		  | _ => raise UTILSLIB_ERR
				 {function = "REV_SUPPOSE_TAC",
				  message = "invalid application"})
	else raise UTILSLIB_ERR
		{function = "REV_SUPPOSE_TAC",
                 message = "The claim doesn't have type :bool"}
end


(*
  ADD_ASSUMS_THEN : {new_assumptions:term list, tactic:tactic} -> tactic

  For adding assumptions to the goal to be used by the given tactic.
  Returns the result of applying the tactic to the augmented goal,
  together with a new subgoal for each new assumption added.
*)

fun ADD_ASSUMS_THEN {new_assumptions = [], tactic} (asms,goal) =
      tactic (asms,goal)
  | ADD_ASSUMS_THEN {new_assumptions = (claim::rest), tactic} (asms,goal) =
      if exists (aconv claim) asms
	  then ADD_ASSUMS_THEN
	        {new_assumptions = rest,
		 tactic = tactic}
		(asms,goal)
      else (SUPPOSE_TAC claim THENL
	    [(ADD_ASSUMS_THEN {new_assumptions = rest, tactic = tactic}),
	     ALL_TAC])
	   (asms,goal)

(*
  ADD_STRIP_ASSUMS_THEN : {new_assumptions:term list, tactic:tactic} -> tactic

  Like ADD_ASSUMS_THEN except it strips the new assumptions before
  adding them to the assumptions.
*)

fun ADD_STRIP_ASSUMS_THEN {new_assumptions = [], tactic} (asms,goal) =
      tactic (asms,goal)
  | ADD_STRIP_ASSUMS_THEN {new_assumptions = (claim::rest), tactic}
                          (asms,goal) =
      if exists (aconv claim) asms
	  then ADD_STRIP_ASSUMS_THEN
	        {new_assumptions = rest,
		 tactic = tactic}
		(asms,goal)
      else (SUPPOSE_TAC claim THENL
	    [((POP_ASSUM STRIP_ASSUME_TAC) THEN
	      (ADD_STRIP_ASSUMS_THEN {new_assumptions=rest,tactic=tactic})),
	     ALL_TAC])
	   (asms,goal)

(*
   use_thm : {theorem:thm, thm_tactic:(thm -> tactic)} -> tactic

  For adding the hypotheses of a theorem to the assumptions of a goal
  before applying the tactic resulting from applying thm_tactic to
  the given theorem.
*)

fun use_thm {theorem, thm_tactic} =
    ADD_STRIP_ASSUMS_THEN{new_assumptions = hyp theorem,
			  tactic = thm_tactic theorem}


fun NEW_SUBST1_TAC thm = use_thm {theorem = thm, thm_tactic = SUBST1_TAC}


fun SUBST_MATCH_TAC thm (asms,goal) =
    let
	val strip_thm = hd (IMP_CANON thm)
	val (term_substitution,type_substitution)=
	    find_match {pattern = (lhs(concl strip_thm)), term = goal}
	val subst_thm = STRONG_INST_TY_TERM
			  {term_substitution=term_substitution,
			   type_substitution=type_substitution,
			   theorem = strip_thm}
    in
	NEW_SUBST1_TAC subst_thm (asms,goal)
    end



fun ASSUME_LIST_TAC thms (asms,goal) =
    let
	val new_assums = flatten (map hyp thms)
	val tactic = 
	      itlist
	       (fn thm => fn tac =>
	         if exists (aconv (concl thm)) asms orelse
		    exists (aconv (concl thm)) new_assums
		     then ALL_TAC
		 else (ASSUME_TAC thm) THEN tac)
	       thms
	       ALL_TAC
    in
	ADD_ASSUMS_THEN
	{new_assumptions=new_assums,
	 tactic = tactic}
	(asms,goal)
    end



(*
   ASM_CONJ1_TAC : tactic

        [A] T1 /\ T2
   ======================
     [A] T1   [A;T1] T2
*)

fun ASM_CONJ1_TAC (asms,goal) =
    if is_conj goal
	then
	    (REV_SUPPOSE_TAC (rand(rator goal)) THENL
	     [ALL_TAC,
	      CONJ_TAC THENL
	      [ACCEPT_TAC(ASSUME (rand(rator goal))),
	       ALL_TAC]])
	    (asms,goal)
    else raise UTILSLIB_ERR
		    {function = "ASM_CONJ1_TAC",
		     message = "goal not a conjuct"}


(*
   ASM_CONJ2_TAC : tactic

        [A] T1 /\ T2
   ======================
     [A;T2] T1   [A] T2
*)

fun ASM_CONJ2_TAC (asms,goal) =
    if is_conj goal
	then
	    (SUPPOSE_TAC (rand goal) THENL
	     [CONJ_TAC THENL
	      [ALL_TAC,
	       ACCEPT_TAC(ASSUME (rand goal))],
	       ALL_TAC])
	    (asms,goal)
    else raise UTILSLIB_ERR
		    {function = "ASM_CONJ2_TAC",
		     message = "goal not a conjuct"}


(*
   MP_IMP_TAC : thm -> tactic  ( thm = [A1] |- t2 ==> t1 )

      [A] t1
    ==========
      [A] t2
*)

fun MP_IMP_TAC imp_thm (thisgoal as (asms,goal)) =
    if is_imp (concl imp_thm)
	then
	    if aconv (#conseq (dest_imp (concl imp_thm))) goal
		then
		    use_thm
		      {theorem = imp_thm,
		       thm_tactic =
		         fn imp_thm => fn (asms,goal) =>
			   ([(asms,#ant(dest_imp(concl imp_thm)))],
			    fn [thm] => MP imp_thm thm
			     | _ => raise UTILSLIB_ERR
				            {function = "MP_IMP_TAC",
				             message = "invalid application"})}
		      thisgoal
	    else raise UTILSLIB_ERR
			    {function = "MP_IMP_TAC",
			     message = "theorem doesn't imply goal"}
    else raise UTILSLIB_ERR
		    {function = "MP_IMP_TAC",
		     message = "theorem is not an implication"}

(*
   MATCH_THM_TAC : {pattern_function:(term -> term),
		    thm_tactic:thm_tactic} -> thm_tactic

   Used to create a version of a theorem tactic that will do matching
   against the given theorem.
*)

fun MATCH_THM_TAC {pattern_function, thm_tactic} =
    let
	fun sub_tac thm (asms,goal) =
	    let
		val (term_substitution,type_substitution) =
		      match_term (pattern_function (concl thm)) goal
		val inst_thm =
		      STRONG_INST_TY_TERM
		        {term_substitution=term_substitution,
			 type_substitution=type_substitution,
			 theorem=thm}
	    in
		((thm_tactic inst_thm) ORELSE
		 (thm_tactic (BETA_RULE inst_thm)))
		(asms,goal)
	    end
    in
	fn thm => (REPEAT GEN_TAC) THEN (sub_tac (SPEC_ALL thm))
    end



(*
   NEW_MATCH_ACCEPT_TAC : thm -> tactic

   Same as MATCH_ACCEPT_TAC, except that if the instantiated version of
   the theorem has hypotheses that are not among the goal assumptions,
   then it creates new subgoals for these, rather than failing.
*)

val NEW_MATCH_ACCEPT_TAC =
      MATCH_THM_TAC
        {pattern_function = (fn x => x), 
	 thm_tactic = (fn thm => use_thm {theorem = thm,
					  thm_tactic = ACCEPT_TAC})}


(*
   MATCH_MP_IMP_TAC : thm -> tactic  ( thm = [A1] |- t2 ==> t1 )


      [A] t1'
    ==========
      [A] t2'

   where t2' ==> t1' is an instance of t2 ==> t1
*)


val MATCH_MP_IMP_TAC =
      MATCH_THM_TAC
        {pattern_function = fn tm => #conseq(dest_imp tm),
	 thm_tactic = MP_IMP_TAC}


(*
   REDUCE_TAC : thm_list -> tactic
   Reduces a goal by stripping and using modus ponens and any theorem
   which is an implication and whose implication conclusion matches the
   goal statement.  It also solves those subgoals which match any of the
   given theorems, or which are included among the assumptions.
*)

local
    fun tryfind f [] = 
	  raise UTILSLIB_ERR{function = "REDUCE_TAC-tryfind",
					  message ="impossible to see this"}
      | tryfind f (x::rest) = f x handle (HOL_ERR _) => tryfind f rest
in
    fun REDUCE_TAC reduction_thms =
	let
	    val new_reduction_thms =
		map UNDISCH_ALL (flatten (map IMP_CANON reduction_thms))
	    val tac_list =
		map
	        (fn thm => (NEW_MATCH_ACCEPT_TAC thm) ORELSE
		 (MATCH_MP_IMP_TAC thm))
		new_reduction_thms
	    fun core_reduce_tac goal =
		((FIRST_ASSUM ACCEPT_TAC) ORELSE
		 ((REPEAT STRIP_TAC) THEN
		  ((FIRST_ASSUM ACCEPT_TAC) ORELSE
		   ((fn gl => tryfind (fn f => f gl) tac_list) THEN
		    core_reduce_tac) ORELSE
		   ALL_TAC))) goal
	in
	    core_reduce_tac
	end
end


(*  Replace by CONV_TAC FUN_EQ_CONV
  EXT_TAC : term -> tactic  ( term = x )

         [A] t1 = t2
    =======================
      [A] !x. t1 x = t2 x

   x should not be free in t1, t2, or [A].
*)

end (* structure utilsLib *)
