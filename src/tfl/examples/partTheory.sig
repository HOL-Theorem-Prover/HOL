signature partTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val part_def : thm
    val partition_def : thm
  
  (*  Theorems  *)
    val part_length : thm
    val part_length_lem : thm
    val part_mem : thm
    val part_perm_lem : thm
    val parts_have_prop : thm
(*
   [perm] Parent theory of "part"
   
   [part_def]
   Definition
   [oracles: ] [axioms: ] []
   |- (!P l1 l2. part P [] l1 l2 = (l1,l2)) /\
      (!P h rst l1 l2.
        part P (CONS h rst) l1 l2 =
        ((P h) => (part P rst (CONS h l1) l2) | (part P rst l1 (CONS h l2))))
   
   [partition_def]
   Definition
   [oracles: ] [axioms: ] [] |- !P L. partition P L = part P L [] []
   
   [part_length]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L l1 l2 p q.
        ((p,q) = part P L l1 l2) ==>
        (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)
   
   [part_length_lem]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L l1 l2 p q.
        ((p,q) = part P L l1 l2) ==>
        LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
        LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2
   
   [part_mem]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L a1 a2 l1 l2.
        ((a1,a2) = part P L l1 l2) ==>
        (!x. mem x (APPEND L (APPEND l1 l2)) = mem x (APPEND a1 a2))
   
   [part_perm_lem]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L a1 a2 l1 l2.
        ((a1,a2) = part P L l1 l2) ==>
        perm (APPEND L (APPEND l1 l2)) (APPEND a1 a2)
   
   [parts_have_prop]
   Theorem
   [oracles: ] [axioms: ] []
   |- !P L A B l1 l2.
        ((A,B) = part P L l1 l2) /\
        (!x. mem x l1 ==> P x) /\
        (!x. mem x l2 ==> ~(P x)) ==>
        (!z. mem z A ==> P z) /\ (!z. mem z B ==> ~(P z))
   
   
*)
end
