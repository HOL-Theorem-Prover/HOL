% Tentative definitions of groups in HOL %

new_theory `Group`;;

new_definition
 (`Arb`,
  "Arb = @x:*.T");;

new_infix_definition
 (`-->`,
  "--> (p1:*->bool) (p2:**->bool) = 
   \f. !x. (p1 x ==> p2(f x)) /\ (~p1 x ==> (f x = Arb))");;

new_infix_definition
 (`::`,
  ":: x p = p x");;

new_definition
 (`Restrict`,
  "Restrict (dom:*->bool) f =
    \x. (dom x => f x | Arb)");;

new_definition
 (`Restrict2`,
  "Restrict2 (dom:*->bool) op =
    \x y. ((dom x /\ dom y) => op x y | Arb)");;

new_definition
 (`Group`,
  "Group(dom:*->bool,op,inv,id) =
    (op :: dom-->(dom-->dom)) /\
    (inv :: dom->dom)         /\
    (id :: dom)               /\
    (!x y z. op(op x y)z = op x (op y z))  /\   %op is associative%
    (!x. op x (inv x) = id)                /\   %inv is an inverse%
    (!x. op x id = x)"                          %id is an identity%
 );;

new_definition
 (`Sub_Group`,
  "Sub_Group((dom1,op1,inv1,id1),(dom2,op2,inv2,id2)) =
    Include dom1 dom2           /\ 
    (op1  = Restrict2 dom1 op2) /\
    (inv1 = Restrict dom1 inv2) /\
    (dom1 id2)"
 );;

