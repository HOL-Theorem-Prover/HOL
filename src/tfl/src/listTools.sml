(*---------------------------------------------------------------------------
 * Proof support for the theory of lists.
 *---------------------------------------------------------------------------*)
structure listTools :> listTools = 
struct

type thm = Thm.thm

val std_thms = [listTheory.LENGTH,
                listTheory.TL,
                listTheory.HD,
                listTheory.CONS_ACYCLIC,
                listTheory.LENGTH_APPEND,
                listTheory.APPEND, listTheory.APPEND_NIL,
                listTheory.LENGTH_NIL,
                listTheory.CONS_11,
                listTheory.NOT_NIL_CONS, 
                listTheory.NOT_CONS_NIL];

end;
