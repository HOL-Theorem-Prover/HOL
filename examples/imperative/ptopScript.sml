open HolKernel Parse boolLib bossLib;

val _ = new_theory "ptop";

val tautAcceptInPlace = store_thm ("V_IMP_V_EQ_TRUE",``(v:bool) ==> (v <=> T)``,(REPEAT (CHANGED_TAC EVAL_TAC)));
val _ = save_thm("PTOP_ACCEPT_IN_PLACE",UNDISCH (tautAcceptInPlace));

val tautRejectInPlace = store_thm("NOTV_IMP_V_EQ_FALSE",``(~(v:bool)) ==> (v <=> F)``,(REPEAT (CHANGED_TAC EVAL_TAC)));
val _ = save_thm("PTOP_REJECT_IN_PLACE",UNDISCH (tautRejectInPlace));

val _ = set_fixity "[=." (Infixl 500);

val _ = set_fixity "[<>." (Infixl 500);

val _ = xDefine "bRefinement" 
	`( v [=. u ) = ( !(s:'a) (s':'b).( (u s s') ==> (v s s') ))`
;

val _ = xDefine "bRefinementNot" 
	`(v [<>. u ) = ( ?(s:'a) (s':'b).( ~((u s s') ==> (v s s')) ) )`
;

val _ = xDefine "ptopABORT" `abort = \(s:'a) (s':'b). T`;
val _ = xDefine "ptopMAGIC" `magic = \(s:'a) (s':'b). F`;
 
val _ = xDefine "ptopASSIGN" `assign (x:'a) (e:('a->'b)->'b)  = 
			\(s:'a->'b) (s':'a->'b) . !(v:'a). 
				if (x = v) then ( 
					(s' v) = (e s)
                                ) else ( 
					(s' v) = (s v) 
				)
		` 
;

val _ = xDefine "ptopSC" `sc f g s s' = (? s'' . ( (f s s'') /\ (g s'' s') ) ) ` ;

val _ = xDefine "ptopSUBS" `subs f x e s s'
              = (let s'' = \y. if ( x = y) then (e s) else (s y)
                  in (f s'' s') ) `;

val _ = export_theory();

