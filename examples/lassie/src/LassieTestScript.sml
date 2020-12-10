open BasicProvers Defn HolKernel Parse SatisfySimps Tactic monadsyntax boolTheory bossLib;
open LassieLib;

val _ = new_theory "LassieTest";

val this_can_never_be_a_thm = Q.store_thm ("test", `∀ (n:num). T`, fs[]);

val tg:(term list * term) = ([], “∀ (n:num). T”);

val t = LassieLib.nltac ‘cheat. cheat. cheat. cheat.’ tg;

val t = LassieLib.nltac ‘Cases.’ tg;

val t = LassieLib.nltac ‘Cases_on ' n '.’ tg;

val t = LassieLib.nltac ‘fs [ arithmeticTheory.ADD_ASSOC ].’ tg;

val t = LassieLib.def `test123` `cheat`;

val t = LassieLib.nltac ‘test123.’ tg;

val t = LassieLib.nltac ‘imp_res_tac test.’ tg;

val t = LassieLib.nltac ‘(qspec_then ' x ' irule test).’ tg;

val t = LassieLib.def `resolve_with test` `imp_res_tac test`;

val t = LassieLib.nltac ‘resolve_with CONJ_COMM.’ tg;

val t = LassieLib.nltac ‘fs [ test , test ].’ tg;

val t = LassieLib.nltac ‘cheat THEN cheat.’ tg;

val t = LassieLib.nltac ‘' T ' by cheat.’ tg;

val t = LassieLib.nltac ‘Goal 1. cheat.’ tg;

val _ = export_theory();
