open HolKernel Parse boolLib bossLib;

open boolListsTheory numsAsCompStatesTheory

val _ = new_theory "busyBeaver";

(* longest it takes machines of size n to terminate *)
Definition tmax_def:
  tmax n =
  MAX_SET {t |
           ∃m. terminated (steps t (mk_initial_state m 0)) ∧
               (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
               ℓ m = n }
End

(* the machine of size n, that takes that longest time to terminate,
   the "busy beaver" if you will
*)
Definition BB_def:
  BB n = @m. terminated (steps (tmax n) (mk_initial_state m 0)) ∧ (ℓ m = n)
End

Definition HALT_def:
  HALT = {(M,x)| ∃t. terminated (steps t (mk_initial_state M x)) }
End




val _ = export_theory();
