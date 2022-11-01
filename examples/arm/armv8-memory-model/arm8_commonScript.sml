open HolKernel boolLib bossLib
open mmTheory

val () = new_theory "arm8_common"

(* -------------------------------------------------------------------------
   Common Armv8 Memory Model Definitions
   ------------------------------------------------------------------------- *)

Definition po_loc:
  po_loc G = po G RINTER same_loc G
End

Definition intervening_write:
  intervening_write G r = r ⨾ diag (W G) ⨾ r
End

(* Initial memory order *)
Definition im0:
  im0 G <=>
  (E G RCROSS E G) RINTER
  ((is_init RCROSS (W G DIFF is_init)) RINTER same_loc G)
End

(* Coherence-after *)
Definition ca:
  ca G <=> fr G RUNION G.co
End

(* Local read successor *)
Definition lrs:
  lrs G <=>
  diag (W G) ⨾ (po_loc G RMINUS intervening_write G (po_loc G)) ⨾ diag (R G)
End

(* Local write successor *)
Definition lws:
  lws G <=> diag (RW G) ⨾ po_loc G ⨾ diag (W G)
End
(* RW added as a sanity condition, as po_loc does not make sense otherwise *)

(* Observed-by *)
Definition obs:
  obs G <=> rfe G RUNION fre G RUNION coe G
End

(* Dependency-ordered-before *)
Definition dob:
  dob G <=>
         G.addr
  RUNION G.data
  RUNION G.ctrl ⨾ diag (W G)
  RUNION ((G.ctrl RUNION (G.addr ⨾ po G)) ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G))
  RUNION G.addr ⨾ po G ⨾ diag (W G)
  RUNION (G.addr RUNION G.data) ⨾ lrs G
End

(* Atomic-ordered-before *)
Definition aob:
  aob G <=> rmw G RUNION diag (RRANGE (rmw G)) ⨾ lrs G ⨾ diag (A G UNION Q G)
End

(* Barrier-ordered-before *)
Definition bob:
  bob G <=>
         po G ⨾ diag (F_dmbsy G) ⨾ po G
  RUNION po G ⨾ (diag (A G) ⨾ G.amo ⨾ diag (L G)) ⨾ po G
  RUNION diag (L G) ⨾ po G ⨾ diag (A G)
  RUNION diag (R G) ⨾ po G ⨾ diag (F_dmbld G) ⨾ po G
  RUNION diag (A G UNION Q G) ⨾ po G
  RUNION diag (W G) ⨾ po G ⨾ diag (F_dmbst G) ⨾ po G ⨾ diag (W G)
  RUNION po G ⨾ diag (L G)
End

(* Tag-ordered-before is missing from Vafeiadis's fromalisation *)

(* Local-ordered-before *)
Definition lob:
  lob G <=>
  TC (lws G ⨾ si G
      RUNION dob G
      RUNION aob G
      RUNION bob G)
End

(* -------------------------------------------------------------------------
   Armv8 Single-copy-atomic-ordered-before
   ------------------------------------------------------------------------- *)

Definition ER:
  ER G = RRANGE (rfe G)
End

Definition IR:
  IR G = RRANGE (rfi G)
End

Definition rfisw:
  rfisw G <=> inv (rfi G) ⨾ si G ⨾ rfi G
End

Definition erln:
  erln G <=>
         si G RINTER (W G RCROSS W G)
  RUNION si G RINTER (ER G RCROSS ER G)
  RUNION si G RINTER (R G RCROSS R G) RINTER rfisw G
  RUNION diag (E G)
End
(* E G is added to ensure "every event is erln-equal to itself" *)

Definition MC:
  MC G = classes (erln G)
End

(* Single-copy-atomic-ordered-before *)
Definition scaob:
  scaob G <=> si G RINTER (ER G RCROSS IR G)
End

Definition linearization_of:
  linearization_of G r cb <=>
  r RSUBSET cb /\
  strict_total_order (MC G) cb /\
  cb RSUBSET (MC G) RCROSS (MC G)
End

(* -------------------------------------------------------------------------
   Universal requirements
   ------------------------------------------------------------------------- *)

(* Internal visibility requirement *)
Definition internal:
  internal G = acyclic (po_loc G RUNION ca G RUNION G.rf)
End

(* Atomic: Basic LDXR/STXR constraint to forbid intervening writes *)
Definition atomic:
  atomic G <=> rmw G RINTER (fre G ⨾ coe G) RSUBSET REMPTY
End

Definition arm_common:
  arm_common G <=> WellFormed G /\ complete G /\ internal G /\ atomic G
End

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
