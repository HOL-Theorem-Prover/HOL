signature permTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val perm_def : thm
  
  (*  Theorems  *)
    val append_perm_sym : thm
    val cons_perm : thm
    val perm_append : thm
    val perm_cong : thm
    val perm_cons_iff : thm
    val perm_intro : thm
    val perm_length : thm
    val perm_mono : thm
    val perm_nil : thm
    val perm_refl : thm
    val perm_split : thm
    val perm_sym : thm
    val perm_trans : thm
    val trans_permute : thm
(*
   [listX] Parent theory of "perm"
   
   [perm_def]
   Definition
   [oracles: ] [axioms: ] []
   |- !L1 L2. perm L1 L2 = (!x. filter ($= x) L1 = filter ($= x) L2)
   
   [append_perm_sym]
   Theorem
   [oracles: ] [axioms: ] []
   |- !A B C. perm (APPEND A B) C ==> perm (APPEND B A) C
   
   [cons_perm]
   Theorem
   [oracles: ] [axioms: ] []
   |- !x L M N. perm L (APPEND M N) ==> perm (CONS x L) (APPEND M (CONS x N))
   
   [perm_append]
   Theorem
   [oracles: ] [axioms: ] [] |- !l1 l2. perm (APPEND l1 l2) (APPEND l2 l1)
   
   [perm_cong]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L1 L2 L3 L4.
        perm L1 L3 /\ perm L2 L4 ==> perm (APPEND L1 L2) (APPEND L3 L4)
   
   [perm_cons_iff]
   Theorem
   [oracles: ] [axioms: ] []
   |- !l2 l1 x. perm (CONS x l1) (CONS x l2) = perm l1 l2
   
   [perm_intro]
   Theorem
   [oracles: ] [axioms: ] [] |- !x y. (x = y) ==> perm x y
   
   [perm_length]
   Theorem
   [oracles: ] [axioms: ] [] |- !l1 l2. perm l1 l2 ==> (LENGTH l1 = LENGTH l2)
   
   [perm_mono]
   Theorem
   [oracles: ] [axioms: ] []
   |- !l1 l2 x. perm l1 l2 ==> perm (CONS x l1) (CONS x l2)
   
   [perm_nil]
   Theorem
   [oracles: ] [axioms: ] []
   |- !L. (perm L [] = L = []) /\ (perm [] L = L = [])
   
   [perm_refl]  Theorem  [oracles: ] [axioms: ] [] |- !L. perm L L
   
   [perm_split]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P l. perm l (APPEND (filter P l) (filter (~ o P) l))
   
   [perm_sym]
   Theorem
   [oracles: ] [axioms: ] [] |- !l1 l2. perm l1 l2 = perm l2 l1
   
   [perm_trans]  Theorem  [oracles: ] [axioms: ] [] |- transitive perm
   
   [trans_permute]
   Theorem
   [oracles: ] [axioms: ] [] |- !x y z. perm x y /\ perm y z ==> perm x z
   
   
*)
end
