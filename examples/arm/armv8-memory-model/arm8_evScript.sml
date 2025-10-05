Theory arm8_ev
Ancestors
  arm8_common

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

