Theory ptop

(* tautAcceptInPlace *)
Theorem V_IMP_V_EQ_TRUE:  (v:bool) ==> (v <=> T)
Proof(REPEAT (CHANGED_TAC EVAL_TAC))
QED
val _ = save_thm("PTOP_ACCEPT_IN_PLACE",UNDISCH (V_IMP_V_EQ_TRUE));

(* tautRejectInPlace *)
Theorem NOTV_IMP_V_EQ_FALSE:  (~(v:bool)) ==> (v <=> F)
Proof(REPEAT (CHANGED_TAC EVAL_TAC))
QED
val _ = save_thm("PTOP_REJECT_IN_PLACE",UNDISCH (NOTV_IMP_V_EQ_FALSE));

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
