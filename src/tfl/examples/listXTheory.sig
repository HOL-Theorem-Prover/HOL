signature listXTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val filter_def : thm
    val mem_def : thm
  
  (*  Theorems  *)
    val APPEND : thm
    val filter_append_distrib : thm
    val filters_commute : thm
    val filters_compose : thm
    val length_append_comm : thm
    val length_append_distrib : thm
    val length_append_filter : thm
    val length_filter : thm
    val length_filter_stable : thm
    val length_filter_subset : thm
    val mem_filter : thm
    val mem_filter_lemma : thm
    val mem_of_append : thm
(*
   [WF] Parent theory of "listX"
   
   [option] Parent theory of "listX"
   
   [rec_type] Parent theory of "listX"
   
   [filter_def]
   Definition
   [oracles: ] [axioms: ] []
   |- (!P. filter P [] = []) /\
      (!P L x.
        filter P (CONS x L) = ((P x) => (CONS x (filter P L)) | (filter P L)))
   
   [mem_def]
   Definition
   [oracles: ] [axioms: ] []
   |- (!x. mem x [] = F) /\ (!x L y. mem x (CONS y L) = (x = y) \/ mem x L)
   
   [APPEND]
   Theorem
   [oracles: ] [axioms: ] []
   |- (!L. APPEND L [] = L) /\
      (!l. APPEND [] l = l) /\
      (!l1 l2 h. APPEND (CONS h l1) l2 = CONS h (APPEND l1 l2))
   
   [filter_append_distrib]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L M. filter P (APPEND L M) = APPEND (filter P L) (filter P M)
   
   [filters_commute]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P Q L. filter P (filter Q L) = filter Q (filter P L)
   
   [filters_compose]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P Q L. filter P (filter Q L) = filter (\x. P x /\ Q x) L
   
   [length_append_comm]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L M. LENGTH (APPEND L M) = LENGTH (APPEND M L)
   
   [length_append_distrib]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L M. LENGTH (APPEND L M) = LENGTH L + LENGTH M
   
   [length_append_filter]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L. LENGTH L = LENGTH (APPEND (filter P L) (filter (~ o P) L))
   
   [length_filter]
   Theorem
   [oracles: ] [axioms: ] [] |- !L P. LENGTH (filter P L) <= LENGTH L
   
   [length_filter_stable]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L P. (LENGTH (filter P L) = LENGTH L) ==> (filter P L = L)
   
   [length_filter_subset]
   Theorem
   [oracles: ] [axioms: ] []
   |- (!y. P y ==> Q y) ==> (!L. LENGTH (filter P L) <= LENGTH (filter Q L))
   
   [mem_filter]
   Theorem
   [oracles: ] [axioms: ] [] |- !P L x. mem x (filter P L) = P x /\ mem x L
   
   [mem_filter_lemma]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L x. mem x L = mem x (filter P L) \/ mem x (filter (~ o P) L)
   
   [mem_of_append]
   Theorem
   [oracles: ] [axioms: ] []
   |- !y L M. mem y (APPEND L M) = mem y L \/ mem y M
   
   
*)
end
