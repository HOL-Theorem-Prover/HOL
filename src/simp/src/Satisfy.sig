(*------------------------------------------------------------------------
 * Satisfy
 *
 * depth-1 prolog unification for finding existential variables.
 * Still needs a little more work.
 *
 * Try to satisfy a set of goals by unifying against a set of facts.
 * 
 * EXAMPLES
 *
 * val tac = VALID (SATISFY_THEN ALL_TAC);
 * tac ([`3 + 1 = 6`], --`?a b. a + 1 = b` ;
 * tac ([`!x. x + 1 = 6`], --`?a b. a + 1 = b` ;
 * tac ([`!P:'b. P = b`], --`?a b. Q (a:'a) = (b:'b)` ;
 * tac ([`!P. P`], --`?a b. a + 1 = b` ;
 * new_constant {Name="KKK",Ty=(==`:'a->'a->bool`==)} handle _ => (); 
 * tac ([`!a:'a. KKK a a`], --`?(x:'a). KKK x x` ;
 * tac ([`!a:'a. KKK a a`,`(Q:'a -> 'a -> bool) n m`], 
 *        --`?x y. KKK x x /\ (Q:'a->'a->bool) x y` ;
 * tac ([`(P1:num->num->bool) e f`,
 `(P2:num->num->bool) f g`,
 `!g. (P3:num->num->bool) e g`], 
 --`?a b c. (P1:num->num->bool) a b /\
 (P2:num->num->bool) b c /\
 (P3:num->num->bool) a b`;
 * 
 * SATISFY_PROVE [ASSUME `(T /\ F) = T`] `?a b. (a /\ F) = b` ;
 * SATISFY_PROVE [`!x. x + 1 = 6`] `?a b. a + 1 = b` ;
 * SATISFY_PROVE [`!P:'b. P = b`] `?a b. Q (a:'a) = (b:'b)` ;
 * SATISFY_PROVE [`!P. P`] `?a b. a + 1 = b` ;
 * SATISFY_PROVE [`!a:num. KKK a a`] `?(x:num). KKK x x` ;
 * SATISFY_PROVE [`!a:'a. KKK a a`,`(Q:'a -> 'a -> bool) n m`]
 *              `?x y. KKK x x /\ (Q:'a->'a->bool) x y` ;
 * SATISFY_PROVE (map ASSUME [--`KKK 3 4`--]) `?y. KKK 3 y` ;
 * SATISFY_CONV (map ASSUME [--`KKK 3 4`--]) `?y. KKK 3 y` ;
 * ASM_SIMP_RULE SATISFY_ss (mk_thm([--`KKK 3 4`--],--`?y. KKK 3 y`);
 *
 *--------------------------------------------------------------------*)

signature Satisfy = sig
  type term = Term.term
  type thm = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic
  type factdb = term list * thm list
               (* this may be hidden in the future *)
   val SATISFY : factdb -> term -> thm
   val SATISFY_CONV : factdb -> conv
   val SATISFY_TAC : tactic
   val add_facts : factdb -> thm list -> factdb
end (* sig *)

