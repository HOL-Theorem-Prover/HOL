open HolKernel boolLib bossLib
open arm8_commonTheory

val () = new_theory "arm8_ev"

(* -------------------------------------------------------------------------
   External visibility
   ------------------------------------------------------------------------- *)

(* External visibility requirement *)
Definition external:
  external G = acyclic (obs G ⨾ si G RUNION lob G)
End

Definition arm_ev:
  arm_ev G <=> arm_common G /\ external G
End

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
