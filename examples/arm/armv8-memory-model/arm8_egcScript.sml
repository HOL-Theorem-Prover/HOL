open HolKernel boolLib bossLib
open arm8_commonTheory

val () = new_theory "arm8_egc"

(* -------------------------------------------------------------------------
   External Global Completion
   ------------------------------------------------------------------------- *)

Definition gc_req:
  gc_req G <=>
         (W G RCROSS UNIV)
  RUNION ((R G RCROSS UNIV) RINTER (RRANGE (rfe G) RCROSS UNIV))
  RUNION (inv (rfi G) ⨾ lob G)
End

Definition preorder_gcb:
  preorder_gcb G <=> im0 G RUNION lob G RINTER gc_req G RUNION scaob G
End

Definition preorder_gcb_lift:
  preorder_gcb_lift G <=> lift (erln G) (preorder_gcb G)
End

Definition dgcbl:
  dgcbl G gcb = delift (erln G) gcb RINTER same_loc G
End

Definition rf_gcb:
  rf_gcb G gcb <=>
  ((W G RCROSS R G) RINTER dgcbl G gcb) RMINUS intervening_write G (dgcbl G gcb)
End

Definition co_gcb:
  co_gcb G gcb <=> (W G RCROSS W G) RINTER dgcbl G gcb
End

(* External Global Completion requirement *)
Definition external_global:
  external_global G =
  ?gcb. linearization_of G (preorder_gcb_lift G) gcb /\
        (G.rf = rf_gcb G gcb) /\
        (G.co = co_gcb G gcb)
End

Definition arm_egc:
  arm_egc G <=> arm_common G /\ external_global G
End

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
