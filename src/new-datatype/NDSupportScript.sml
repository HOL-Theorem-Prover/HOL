open HolKernel Parse boolLib bossLib;

val _ = new_theory "NDSupport";

val J_def = Define`J = \x (u:one). NONE`;
val KT_def = Define`KT = \x. T`;

val    fun_map_def = Define`   fun_map = combin$o         `;
val    sum_map_def = Define`   sum_map =    sum$++        `;
val   prod_map_def = Define`  prod_map =   pair$##        `;
val   list_map_def = Define`  list_map =   list$MAP       `;
val option_map_def = Define`option_map = option$OPTION_MAP`;

val list_retrieve_def = Define`
   (list_retrieve f [    ]          _ = NONE                    )
/\ (list_retrieve f (h::_) (    0, c) = f h c                   )
/\ (list_retrieve f (h::t) (SUC n, c) = list_retrieve f t (n, c))
`;

val sum_retrieve_def = Define`
   (sum_retrieve f1 _ (INL a1) (b1, _) = f1 a1 b1)
/\ (sum_retrieve _ f2 (INR a2) (_, b2) = f2 a2 b2)`;

val prod_retrieve_def = Define`
   (prod_retrieve f1 _ (a1, _) (INL b1) = f1 a1 b1)
/\ (prod_retrieve _ f2 (_, a2) (INR b2) = f2 a2 b2)`;

val fun_retrieve_def = Define`
    fun_retrieve f g (a, b) = f (g a) b`;
(*  fun_retrieve = $o ($o UNCURRY) $o *)

val option_retrieve_def = Define`
   (option_retrieve f  NONE    _ = NONE )
/\ (option_retrieve f (SOME c) p = f c p)
`;



val INJ_def = Define`INJ f = !x y. (f x = f y) ==> (x = y)`;

val inj_pair_def = Define`
    inj_pair f g = !x y. (f x = f y) /\ (!z. g x z = g y z) ==> (x = y)
`;

val sum_all_def = Define`
   (sum_all P Q (INL x) = P x)
/\ (sum_all P Q (INR y) = Q y)`;

val prod_all_def = Define`
    prod_all P Q (x,y) = P x /\ Q y`;

(* list_all = EVERY *)
val list_all_def = Define`
   (list_all P [    ] = T)
/\ (list_all P (h::t) = P h /\ list_all P t)`;

val option_all_def = Define`
   (option_all P  NONE    = T  )
/\ (option_all P (SOME x) = P x)`;

val fun_all_def = Define`
    fun_all P f = !x. P (f x)
`;

val _ = export_theory();

