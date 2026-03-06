
(* Definitions for AMBA APB bus. See AMBA Specification v2.0 from ARM for details  *)
Theory amba_apb
Ancestors
  mod16
Libs
  pairSyntax commonTools amba_common


Definition I1p:   INIT_APB (paddr:bool,pwrite:bool,psel:bool,psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool,penable:bool,pdata:bool,mdata:bool,maddr:bool,sdata_0:bool,saddr_0:bool,sdata_1:bool,saddr_1:bool) = ~psel /\ ~penable
End
val INIT_APB_def = I1p;

(* FIXME: transitions for pdata of the form pdata_0' = ... , so we can use pdata in the defs of m' and s' *)
(* FIXME: scale, separate read/write buses *)
(* note: psel_x is a family signals, where x identifies the slave, so the x is not bits e.g. psel_2 is a valid signal *)

Definition PSEL_def:   PSEL x (psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool) = MOD16_N2B x (psel_3,psel_2,psel_1,psel_0)
End

(*these are temporary, pending implementation of DI, at which point SDATA will lose the second argument and these can be removed
  or at the very least they will be removed by DI. however, the saddr_x, sdata_x vars will definitely go  *)
Definition SDATA_def:   SDATA x b = if (x=0) then FST b else SND b
End
Definition SADDR_def:   SADDR x b = if (x=0) then FST b else SND b
End

Definition Rm:   TRANS_APB_M (^Rpm_state,^Rpm_state') =
  (penable' = psel /\ ~penable) /\
  (psel ==> (pwrite' = pwrite)) /\
  ((psel /\ ~penable) ==> ((psel'=psel) /\ (psel_3'=psel_3) /\ (psel_2'=psel_2) /\ (psel_1'=psel_1) /\ (psel_0'=psel_0)))  /\
  (penable ==> (mdata' = if pwrite then mdata else pdata)) /\
  (penable ==> (maddr' = if pwrite then maddr else paddr))
End
val TRANS_APB_M_def = Rm;

(* the saddr and sdata vars will go away once we have DI *)
Definition Rs:   TRANS_APB_S x (^Rps_state,^Rps_state') =
    (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ penable ==>
        (SDATA x (sdata_0',sdata_1') = if pwrite then pdata else SDATA x (sdata_0,sdata_1))) /\
    (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ penable ==>
        (SADDR x (saddr_0',saddr_1') = if pwrite then paddr else SADDR x (saddr_0,saddr_1)))
End
val TRANS_APB_S_def = Rs;

Definition Rb:   TRANS_BUS x (^Rp_state,^Rp_state') =
  (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ ~penable ==>
                                                (paddr' = if pwrite then maddr else SADDR x (saddr_0,saddr_1))) /\
  (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ ~penable ==>
                                                (pdata' = if pwrite then mdata else SDATA x (sdata_0,sdata_1)))
End
val TRANS_BUS_def = Rb;

Definition R1p:   TRANS_APB (^Rp_state,^Rp_state') =
^(lhs(concl(Drule.SPEC_ALL Rm)))  /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rs))))))  /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rb))))))
End
val TRANS_APB_def = R1p;

