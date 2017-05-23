open HolKernel Parse boolLib bossLib ptopTheory imperativeLib

val _ = new_theory "imperative";

val _ = set_trace "Unicode" 0;

val _ = show_types:=true;
val _ = show_assums:=true;

val _ = store_thm 
	(
		"MAGIC_REFINES_ALL",
		``  f [=. magic ``,
		imperativeLib.REFINEMENT_TAC
			(* 
				[
				] |-
					magic s s' ==> f s s'
			*)	
	THEN
		EVAL_TAC
			(* |- f [=. magic : thm *)
	)
;
	
val _ = store_thm
	(
		"ALL_REFINE_ABORT",
		``  abort [=. f ``,
		imperativeLib.REFINEMENT_TAC
			(* 
				[
				] |-
					f s s' ==> abort s s'
			*)	
	THEN
		EVAL_TAC
			(* |- abort [=. f : thm *)
	)
;


val	thmAbstractFunction =	
	store_thm
	(	
		"IMPERATIVE_FN_ABSTRACTION",
		``!(t :'a -> 'b) (f :'a -> 'b).(t = (\(y :'a). f y)) <=> (!(y:'a).(t (y :'a) = f y)) ``,
		(
			(EVAL_TAC)
				(* 	[ 	
					]	|- 
							!t f. (t = f) <=> !y. t y = f y
				*)
		THEN
			(REPEAT STRIP_TAC)
				(* 	[ 	
					]	|- 
							 (t = f) <=> !y. t y = f y
				*)
		THEN
			(ACCEPT_TAC (SPECL [``t:'a->'b``,``f:'a->'b``] FUN_EQ_THM))
				(*  [] |- !t f. (t = (\y. f y)) <=> !y. t y = f y : thm *) 
		)
	)
;

val	thmConditionalFunction =	
	let val
		goal =	``!(t :'a -> 'b) (a :'a -> bool) (b :'a -> 'b) (c :'a -> 'b). (!(y :'a). 
				if a y then t y = b y else t y = c y) 
					<=>
				(t = (\(y :'a). if a y then b y else c y))``
	and
		specializedTerm0 = [
			``t:'a->'b``,
			``\(y:'a).(if (a:'a->bool) y then (b:'a->'b) y else (c:'a->'b) y)``
		]
	and
		specializedTerm1 = [
			``\rhs.((((t:'a->'b) (y:'a)) = rhs )) ``,
			``(a:'a -> bool) (y: 'a)``,
			``((b:'a->'b) (y:'a))``, 
			``((c:'a->'b)(y:'a))``
		]
	in
		store_thm
		(	
			"IMPERATIVE_IFTHENELSE_FN",
			goal,
			(
				(*	[
					]	|-
							!t a b c. (!y. if a y then t y = b y else t y = c y) <=>  
								(t = (\y. if a y then b y else c y))
				*)
				(REPEAT STRIP_TAC)
					(* 	[ 	
						]	|- 
							(!y. if a y then t y = b y else t y = c y) <=>  
								(t = (\y. if a y then b y else c y))
					*)
			THEN
				(EQ_TAC	THENL
					[(
						(* 	[ 	
							]	|- 
									(!y. if a y then t y = b y else t y = c y) 
										==>  (t = (\y. if a y then b y else c y))
						*)
						(REPEAT STRIP_TAC)
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								]	|- 
										(t = (\y. if a y then b y else c y))
							*)
					THEN
						(SUBST_TAC [(BETA_RULE (SPECL specializedTerm0 thmAbstractFunction))])
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										!y. t y = if a y then b y else c y
							*)
					THEN
						(REPEAT STRIP_TAC)
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										t y = if a y then b y else c y							*)
					THEN
						(SUBST_TAC [
							(BETA_RULE(SPECL  specializedTerm1 (
								INST_TYPE [
									alpha |-> ``:'b ``, beta |->``:bool``
								] COND_RAND))
							)
						])
							(* 	[ 	
									(!y. if a y then t y = b y else t y = c y) 
								  ]	|- 
										 if a y then t y = b y else t y = c y
							*)
					THEN 
						(FIRST_ASSUM (ACCEPT_TAC o (SPEC ``y:'a``)))
					),(
						(* 	[ 	
							]	|- 
									(t = (\y. if a y then b y else c y)) 
										==>  (!y. if a y then t y = b y else t y = c y)
						*)
						(REPEAT STRIP_TAC)
							(* 	[ 	
									t = (\y. if a y then b y else c y)								  
								]	|- 
										if a y then t y = b y else t y = c y
							*)
					THEN
						(SUBST_TAC [(
							imperativeLib.SWAPLR_RULE 
								(
									BETA_RULE
									(
										SPECL specializedTerm1 (INST_TYPE [
											alpha |-> ``:'b ``, beta |->``:bool``
										] COND_RAND)
									)
								)
							)]
						)
							(* 	[ 	
									t = (\y. if a y then b y else c y)								  
								]	|- 
										t y = if a y then b y else c y
							*)
					THEN
						(ASSUME_TAC 
							(
								UNDISCH (#1(EQ_IMP_RULE 				
										(
											BETA_RULE 
											(
												SPECL specializedTerm0 thmAbstractFunction
											)
										)
									))
							)
							(* 	[ 
									!y. t y = if a y then b y else c y
								,
									t = (\y. if a y then b y else c y)								  
								]	|- 
										t y = if a y then b y else c y
							*)
						)
					THEN
						(FIRST_ASSUM (ACCEPT_TAC o (SPEC ``y:'a``)))
					)]				
					(* 	[
						]	|- 
								!t a b c.  (!y. if a y then t y = b y else t y = c y) <=> 
									(t = (\y. if a y then b y else c y)) : thm 
					*)
				)
			)
		)
	end
;

val	SPEC_EQ_THM = 
	store_thm
	(
		"IMPERATIVE_SPEC_EQ_THM",
		``(!(s :'a) (s' :'b).(f :'a -> 'b -> 'c) s s' = (g :'a -> 'b -> 'c) s s') <=> (f = g)``,
		(
			(EQ_TAC THENL
				[(
					(* 	[ 	
						]	|- 
								(!s s'. f s s' = g s s') ==> (f = g)
					*)
					(DISCH_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									(f = g)
						*)
				THEN
					(SUBST_TAC [(INST_TYPE [beta |-> ``:'b->'c``] (SPEC_ALL FUN_EQ_THM))])
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									!x. f x = g x
						*)
				THEN
					(GEN_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									f x = g x
						*)
				THEN
					(SUBST_TAC [(SPECL [``(f:'a->'b->'c) (x:'a)``,``(g:'a->'b->'c) (x:'a)``] (
						INST_TYPE [alpha |-> ``:'b``, beta |-> gamma] FUN_EQ_THM))]
					)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									 !x'. f x x' = g x x'
						*)
				THEN
					(GEN_TAC)
						(* 	[ 	
									(!s s'. f s s' = g s s')
							]	|- 
									 f x x' = g x x'
						*)
				THEN
					(FIRST_ASSUM (ACCEPT_TAC o (SPECL [``x:'a``,``x':'b``])))
				),(
					(* 	[ 	
						]	|- 
								(f = g) ==> !s s'. f s s' = g s s'
					*)
					(REPEAT STRIP_TAC)
						(* 	[ 	
									(f = g) 
							]	|- 
									!s s'. f s s' = g s s'
						*)
				THEN
					(REPEAT AP_THM_TAC)
						(* 	[ 	
									(f = g) 
							]	|- 
									f = g 
						*)
				THEN
					(FIRST_ASSUM ACCEPT_TAC)
				)]
			)
		)	
			(* 
				[] |- (!s s'. f s s' = g s s') <=> (f = g) : proof
			*) 
	)
;

val thmAbstractSpecification = 
		INST_TYPE [
			alpha |-> ``:'a -> 'b``, beta |-> ``:'a -> 'b``, gamma |-> ``:bool``
		] SPEC_EQ_THM
			(* 	
				[] |- (!s s'. f s s' <=> g s s') <=> (f = g)   : thm 			
			*)
;

val _ = save_thm("PREDICATIVE_SPEC_EQ_THM",thmAbstractSpecification);

val thmOnePointLemma=
	store_thm
	(
		"ONE_POINT_LEMMA",
		`` (x = x) /\ (f x t ) <=> f x t``,
		(
			(EQ_TAC	THENL
				[(
					(* 	[ 	
						]	|- 
								((x  = x) /\ (f  x t )) ==> f x t
					*)
						(ASSUME_TAC (REFL ``x``))
						(* 	[ 	(x = x) 
							]	|- 
									((x = x) /\ (f x t)) ==> f x t
						*)
					THEN
						(FIRST_ASSUM  imperativeLib.MAKE_IT_SO)
				),(
					(* 	[ 	
						]	|- 
								(f x t) ==> (x = x) /\ f x t
					*)
						(DISCH_TAC)
						(* 	[ 	
								(f x t)
							]	|- 
									(x = x) /\ f x t
						*)
					THEN
						(FIRST_ASSUM  imperativeLib.MAKE_IT_SO)
				)]
			)					
		)
	)
;

		
val thmForwardSubstitution =
	let	val	
		conversion0 = BETA_RULE
						(
							imperativeLib.SWAPLR_RULE 
							(
								SPECL 
									[
										``s'':'a->'b``,
										``\(y:'a).((x:'a) = y)``,
										``\(y:'a).((e:('a->'b)->'b) (s:'a->'b))``,
										``s:'a->'b``
									] 
										thmConditionalFunction
							)
						)
	and
		conversion1 = imperativeLib.SWAPLR_RULE 						
						(
							BETA_RULE
							(
								SPECL 
									[
										``s'':'a->'b``,
										``\ (y:'a).if (x:'a) = y then (e:('a->'b)->'b) (s:'a->'b) else s y``
									] 
										thmAbstractFunction
							)
						)
	and
		lemma0 = BETA_RULE
						(
							SPECL 
								[
									``s'':'a->'b``,
									``\(y:'a).if (x:'a) = y then (e:('a->'b)->'b) (s:'a->'b) else s y``
								] 
									thmAbstractFunction
						)
	and 
		lemma1	=	imperativeLib.VSUB ``t:'c`` ``s':'c`` 
						(
							imperativeLib.VSUB ``x:'a->'b`` ``\(y:'a).if(x = y) 	then (e:('a->'b)->'b) (s:'a->'b) 
														else s y`` 
								(INST_TYPE [
									alpha |-> ``:('a->'b)`` , beta |-> ``:'c``
								] thmOnePointLemma)
						)
	in
		store_thm
		(
			"FORWARD_SUB",
			``!f e x s s'. sc (assign x e) f s s' = subs f x e s s' ``,
			(
				(REPEAT STRIP_TAC) 
					(* 	[ 	
						]	|- 
								 sc (assign x e) f s s' <=> subs f x e s s'
					*)
			THEN
				(EVAL_TAC)
					(* 	[ 	
						]	|- 
								(?s''. 
									(!y. if x = y then s'' y = e s else s'' y = s y) /\ f s'' s') 
								<=>
									f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(REWRITE_TAC [(REWRITE_RULE [conversion0] lemma0),conversion1])
					(* 	[ 	
						]	|- 
								(?s''. 
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								<=>
									f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(SUBST_TAC [(imperativeLib.SWAPLR_RULE lemma1)])
					(* 	[ 	
						]	|- 
								 (?s''. 
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								<=>
										((\y. if x = y then e s else s y) = 
											(\y. if x = y then e s else s y)) 	
									/\	
										f (\y. if x = y then e s else s y) s'
					*)
			THEN
				(EQ_TAC THENL
					[(
						(* 	[ 	
							]	|- 
									 (?s''. 
										(s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
									==>
											((\y. if x = y then e s else s y) = 
												(\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'

						*)
						(DISCH_TAC)
							(* 	[ 	
									(?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								]	|- 
											((\y. if x = y then e s else s y) = 
												(\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM CHOOSE_TAC)
							(* 	[ 	
									(s'' = (\y. if x = y then e s else s y)) /\ f s'' s'
								,
									(?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
								]	|- 
											((\y. if x = y then e s else s y) = 
												(\y. if x = y then e s else s y)) 
										 /\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM (fn th =>  (TRY(REWRITE_TAC [(imperativeLib.SWAPLR_RULE th)]))))
					),(
						(* 	[ 	
							]	|- 
									((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
									f (\y. if x = y then e s else s y) s'
									==>
									(?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
						*)
						(DISCH_TAC)
							(* 	[ 	
									((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
									f (\y. if x = y then e s else s y) s'
								]	|-
									 (?s''. (s'' = (\y. if x = y then e s else s y)) /\ f s'' s') 
							*)
					THEN
						(FIRST_ASSUM (fn th =>  (TRY (
								EXISTS_TAC ((#1(dest_eq(#1(dest_conj(concl th))))))))
							)
						)
							(* 	[ 	
									((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
									f (\y. if x = y then e s else s y) s'
								]	|- 
											((\y. if x = y then e s else s y) = (\y. if x = y then e s else s y)) 
										/\
											f (\y. if x = y then e s else s y) s'
							*)
					THEN
						(FIRST_ASSUM imperativeLib.MAKE_IT_SO)
					)]
				)
			)
		)
	end
;


val _ = export_theory();
