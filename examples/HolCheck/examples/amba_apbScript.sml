
(* Definitions for AMBA APB bus. See AMBA Specification v2.0 from ARM for details  *)

open HolKernel Parse boolLib bossLib 

val _ = new_theory("amba_apb")

open HolKernel Parse boolLib bossLib pairSyntax
open mod16Theory commonTools amba_common
 
val I1p = Define `INIT_APB (paddr:bool,pwrite:bool,psel:bool,psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool,penable:bool,pdata:bool,mdata:bool,maddr:bool,sdata_0:bool,saddr_0:bool,sdata_1:bool,saddr_1:bool) = ~psel /\ ~penable`;
val INIT_APB_def = I1p;

(* FIXME: transitions for pdata of the form pdata_0' = ... , so we can use pdata in the defs of m' and s' *)
(* FIXME: scale, separate read/write buses *)
(* note: psel_x is a family signals, where x identifies the slave, so the x is not bits e.g. psel_2 is a valid signal *)

val PSEL_def = Define `PSEL x (psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool) = MOD16_N2B x (psel_3,psel_2,psel_1,psel_0)`; 

(*these are temporary, pending implementation of DI, at which point SDATA will lose the second argument and these can be removed
  or at the very least they will be removed by DI. however, the saddr_x, sdata_x vars will definitely go  *)
val SDATA_def = Define `SDATA x b = if (x=0) then FST b else SND b`
val SADDR_def = Define `SADDR x b = if (x=0) then FST b else SND b`

val Rm = Define `TRANS_APB_M (^Rpm_state,^Rpm_state') = 
  (penable' = psel /\ ~penable) /\
  (psel ==> (pwrite' = pwrite)) /\
  ((psel /\ ~penable) ==> ((psel'=psel) /\ (psel_3'=psel_3) /\ (psel_2'=psel_2) /\ (psel_1'=psel_1) /\ (psel_0'=psel_0)))  /\
  (penable ==> (mdata' = if pwrite then mdata else pdata)) /\
  (penable ==> (maddr' = if pwrite then maddr else paddr))
`;
val TRANS_APB_M_def = Rm;

(* the saddr and sdata vars will go away once we have DI *)
val Rs = Define `TRANS_APB_S x (^Rps_state,^Rps_state') = 
    (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ penable ==> 
	(SDATA x (sdata_0',sdata_1') = if pwrite then pdata else SDATA x (sdata_0,sdata_1))) /\  
    (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ penable ==> 
	(SADDR x (saddr_0',saddr_1') = if pwrite then paddr else SADDR x (saddr_0,saddr_1))) 
`;
val TRANS_APB_S_def = Rs;

val Rb = Define `TRANS_BUS x (^Rp_state,^Rp_state') = 
  (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ ~penable ==> 
						(paddr' = if pwrite then maddr else SADDR x (saddr_0,saddr_1))) /\
  (psel /\ PSEL x (psel_3,psel_2,psel_1,psel_0) /\ ~penable ==> 
						(pdata' = if pwrite then mdata else SDATA x (sdata_0,sdata_1)))
`;
val TRANS_BUS_def = Rb;

val R1p = Define `TRANS_APB (^Rp_state,^Rp_state') = 
^(lhs(concl(Drule.SPEC_ALL Rm)))  /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rs))))))  /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rb))))))  
`;
val TRANS_APB_def = R1p;

val _ = export_theory()
