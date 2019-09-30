
new_theory `Modal`;;

new_type 0 `world`;;

% Accessibility relation %

new_constant(`R`, ":world#world->bool");;

new_definition(`VALID` , "VALID p = !w:world. p w");;

new_definition(`Nec`  , "Nec p = \w. !w'. R(w,w')  ==>  p w'");;

new_definition(`Pos`  , "Pos p = \w. ?w'. R(w,w')  /\   p w'");;

new_infix_definition(`-->`, "--> p1 p2 = \w. p1 w  ==>  p2 w");;

new_definition
 (`Euclidean`, 
  "Euclidean = !w1 w2 w3. R(w1,w2) /\ R(w1,w3) ==> R(w2,w3)");;

load_definitions `Modal`;;

let Euclidean_Thm =
 prove_thm
  (`Euclidean_Thm`,
   "Euclidean ==> !p. VALID (Pos p --> Nec(Pos p))",
   REWRITE_TAC[VALID;Pos;Nec;-->]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "w':world"
    THEN ASM_REWRITE_TAC[]
    THEN ASSUM_LIST(IMP_RES_TAC o (EQ_MP Euclidean) o (el 4)));;
