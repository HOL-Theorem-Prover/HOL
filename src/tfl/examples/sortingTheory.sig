signature sortingTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val performs_sorting_def : thm
    val sorted_def : thm
    val tupled_sorted_def : thm
  
  (*  Theorems  *)
    val sorted_append : thm
    val sorted_def_thm : thm
    val sorted_eq : thm
    val sorted_eqns : thm
    val sorted_induction : thm
(*
   [perm] Parent theory of "sorting"
   
   [performs_sorting_def]
   Definition
   [oracles: ] [axioms: ] []
   |- !f R. performs_sorting f R = (!l. perm l (f R l) /\ sorted R (f R l))
   
   [sorted_def]
   Definition
   [oracles: ] [axioms: ] [] |- !x x'. sorted x x' = tupled_sorted (x,x')
   
   [tupled_sorted_def]
   Definition
   [oracles: ] [axioms: ] []
   |- tupled_sorted =
      WFREC
        (@R'.
          WF R' /\ (!R y rst x. R' (R,CONS y rst) (R,CONS x (CONS y rst))))
        (\tupled_sorted a.
          pair_case
            (\v v1.
              list_case T
                (\v2 v3.
                  list_case T
                    (\v4 v5. v v2 v4 /\ tupled_sorted (v,CONS v4 v5))
                    v3)
                v1)
            a)
   
   [sorted_append]
   Theorem
   [oracles: ] [axioms: ] []
   |- !R L1 L2.
        transitive R /\
        sorted R L1 /\
        sorted R L2 /\
        (!x y. mem x L1 /\ mem y L2 ==> R x y) ==>
        sorted R (APPEND L1 L2)
   
   [sorted_def_thm]
   Theorem
   [oracles: ] [axioms: ] []
   |- ((sorted R [] = T) /\
       (sorted R [x] = T) /\
       (sorted R (CONS x (CONS y rst)) = R x y /\ sorted R (CONS y rst))) /\
      (!P.
        (!R. P R []) /\
        (!R x. P R [x]) /\
        (!R x y rst. P R (CONS y rst) ==> P R (CONS x (CONS y rst))) ==>
        (!v v1. P v v1))
   
   [sorted_eq]
   Theorem
   [oracles: ] [axioms: ] []
   |- !R L x.
        transitive R ==>
        (sorted R (CONS x L) = sorted R L /\ (!y. mem y L ==> R x y))
   
   [sorted_eqns]
   Theorem
   [oracles: ] [axioms: ] []
   |- (sorted R [] = T) /\
      (sorted R [x] = T) /\
      (sorted R (CONS x (CONS y rst)) = R x y /\ sorted R (CONS y rst))
   
   [sorted_induction]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P.
        (!R. P R []) /\
        (!R x. P R [x]) /\
        (!R x y rst. P R (CONS y rst) ==> P R (CONS x (CONS y rst))) ==>
        (!v v1. P v v1)
   
   
*)
end
