Theory ramana20261012
Ancestors
  hol

Definition final_leaf_def:
  final_leaf (n:num) = 2n ** n
End

Definition final_list_def:
  final_list (ns : num list) = FOLDL $- 0 ns
End

Datatype:
  rlp = RLPB num | RLPL (rlp list)
End

Definition rlp_it_def:
  rlp_it (RLPB n) = final_leaf n ∧
  rlp_it (RLPL rps) = rlp_acc [] rps ∧
  rlp_acc acc [] = final_list acc ∧
  rlp_acc acc (x::xs) = rlp_acc (rlp_it x :: acc) xs
End

(* will fail if the induction principle is of wrong shape, e.g., just T *)
val (th1,th2) = rlp_it_ind |> SPEC_ALL |> UNDISCH |> CONJ_PAIR

Definition rlp_alt_def:
  rlp_alt (RLPB n) = final_leaf n ∧
  rlp_alt (RLPL rlps) = final_list (MAP rlp_alt rlps)
End
