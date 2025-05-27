open HolKernel Parse boolLib bossLib testutils countable_typesLib;

val Datatype = quietly Datatype
val mk_countable = quietly mk_countable

val _ = Datatype `rose_tricky = RT_Empty | RT_List (num list) ((rose_tricky) list)`;

val _ = tprint "Testing mk_countable on rose-type datatype rose_tricky.";
val _ = require (check_result (fn thm => not (is_imp (concl thm))))
    mk_countable ``: rose_tricky``;

val _ = Datatype `
  rose_awful = RA_Empty | RA_List ((rose_awful_aux) list)
  ;
  rose_awful_aux = RAA_Empty | RAA (rose_awful) num 'a num (rose_awful)
`

val _ = Datatype `
  tier2 = T2_Empty ('a -> num) | T2_Loop (tier2 list) (num list rose_awful)
`

val _ = Datatype `
  tier3 = T3_Empty | T3_x ('a tier2) num
`;

val _ = tprint "Testing mk_countable on compound datatype tier3."
val _ = require is_result mk_countable ``: 'a tier3``
