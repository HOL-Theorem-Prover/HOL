(* ========================================================================= *)
(* BASIC TEST 2: PARSING AND PRINTING                                        *)
(* ========================================================================= *)

val t1 = ``v``;
val _ = print (term_to_string t1 ^ "\n");

val t2 = ``!f s a b. (!x. f x = a) /\ b IN IMAGE f s ==> (a = b)``;
val _ = print (term_to_string t2 ^ "\n");
