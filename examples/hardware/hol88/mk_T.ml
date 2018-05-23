
% The System T (Hughes and Cresswell Chapter 2) %

new_theory`T`;;

new_type 0 `world`;;

% Accessibility relation %

new_curried_infix(`R`, ":world->world->bool");;

new_axiom(`R_REFL`, "!w. w R w");;

new_definition      (`VALID` , "VALID p = !w:world. p w");;

new_definition      (`L_AX`  , "L p = \w. !w'. (w R w') ==> p w'");;

new_infix_definition(`or_AX` , "or p1 p2 = \w. (p1 w) \/ (p2 w)");;

new_definition      (`not_AX`, "not p = \w. ~(p w)");;

new_definition      (`M_AX`  , "M p = not(L(not p))");;

new_infix_definition(`imp_AX`, "imp p1 p2 = ((not p1) or p2)");;

new_infix_definition(`and_AX`, "and p1 p2 = not((not p1) or (not p2))");;

new_infix_definition(`L_IMP`, "--> p1 p2 = L(p1 imp p2)");;

new_infix_definition(`L_EQ`  , "== p1 p2 = ((p1 imp p2) and (p2 imp p1))");;

close_theory();;

load_theory`T`;;

let R_REFL = axiom `T` `R_REFL`
and L_AX   = axiom `T` `L_AX`
and or_AX  = axiom `T` `or_AX`
and not_AX = axiom `T` `not_AX`
and M_AX   = axiom `T` `M_AX`
and imp_AX = axiom `T` `imp_AX`
and and_AX = axiom `T` `and_AX`
and L_IMP  = axiom `T` `L_IMP`
and L_EQ   = axiom `T` `L_EQ`;;

% |- VALID((L p) imp p) %

% need a derived rule: ((not p1) or p2)w --> ~(p1 w) \/ (p2 w) etc.%

let A5 =
 let p = "p:world->bool"
 and w = "w:world"
 in
 let th1 = EQ_MP (RIGHT_BETA(AP_THM(SPEC p L_AX )w)) (ASSUME "L ^p ^w")
 in
 let th2 = GEN w (DISCH "L ^p ^w" (MP (SPEC w th1) (SPEC w R_REFL)))
 in
 let th3 = AP_THM (SPEC "L ^p" (SPEC p imp_AX)) w
 and th4 = RIGHT_BETA(AP_THM(SPEC "L ^p" (SPEC "not ^p" or_AX))w)
 in
 let th5 = th3 TRANS th4 % unfinished ... %
