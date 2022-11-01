open HolKernel boolLib bossLib
open arm8_commonTheory

val () = new_theory "arm8_ec"

(* -------------------------------------------------------------------------
   External Completion
   ------------------------------------------------------------------------- *)

Definition preorder_cb:
  preorder_cb G <=> im0 G RUNION lob G RUNION scaob G
End

Definition preorder_cb_lift:
  preorder_cb_lift G <=> lift (erln G) (preorder_cb G)
End

Definition dcbl:
  dcbl G cb = delift (erln G) cb RINTER same_loc G
End

Definition rf_fwd:
  rf_fwd G cb <=>
  ((W G RCROSS R G) RINTER po_loc G RINTER inv (dcbl G cb))
  RMINUS intervening_write G (po_loc G)
End

Definition rf_nfwd:
  rf_nfwd G cb <=>
  ((W G RCROSS R G) RINTER dcbl G cb)
  RMINUS intervening_write G (dcbl G cb RUNION po_loc G)
End

Definition rf_cb:
  rf_cb G cb <=> rf_fwd G cb RUNION rf_nfwd G cb
End

Definition co_cb:
  co_cb G cb <=> dcbl G cb RINTER (W G RCROSS W G)
End

(* External Completion requirement *)
Definition external_completion:
  external_completion G =
  ?cb. linearization_of G (preorder_cb_lift G) cb /\
       (G.rf = rf_cb G cb) /\
       (G.co = co_cb G cb)
End

Definition arm_ec:
  arm_ec G <=> arm_common G /\ external_completion G
End

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
