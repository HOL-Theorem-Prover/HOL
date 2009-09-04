structure amba_common =
struct

local

open HolKernel Parse boolLib bossLib

open bossLib pairSyntax boolSyntax
open mod16Theory commonTools

in

(* APB *)

val num_apb_slaves = 2; (* this is not completely general yet: PSEL definition only allows upto 16 slaves *)

val Rpm_state = ``(paddr:bool,pwrite:bool,psel:bool,psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool,penable:bool,pdata:bool,mdata:bool,maddr:bool)``
val Rpm_state' = ksTools.mk_primed_state Rpm_state;

val Rps_state = ``(paddr:bool,pwrite:bool,psel:bool,psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool,penable:bool,pdata:bool,sdata_0:bool,saddr_0:bool,sdata_1:bool,saddr_1:bool)``
val Rps_state' = ksTools.mk_primed_state Rps_state;

val Rp_state = list_mk_pair((strip_pair Rpm_state)@[``sdata_0:bool``,``saddr_0:bool``,``sdata_1:bool``,``saddr_1:bool``])
val Rp_state' = ksTools.mk_primed_state Rp_state

(* AHB *)

val nm = 8; (*  2..16 *)
val nb = 16; (* 4 or 16 *)
val ns = 16; (* 1..16 *)
val nw = 16; (* 4 or 16 *)

val mk_bool_pair = pairSyntax.list_mk_pair o (List.map mk_bool_var)

val bbv = mk_bool_pair ["bb3","bb2","bb1","bb0"]

val hwsv = mk_bool_pair ["hws3","hws2","hws1","hws0"]

val burstm_vars = mk_bool_pair ["hburstm_15_0","hburstm_14_0","hburstm_13_0","hburstm_12_0","hburstm_11_0","hburstm_10_0","hburstm_9_0","hburstm_8_0","hburstm_7_0","hburstm_6_0","hburstm_5_0","hburstm_4_0","hburstm_3_0","hburstm_2_0","hburstm_1_0","hburstm_0_0"]
val burstm_vars' = ksTools.mk_primed_state burstm_vars

val transm_vars = mk_bool_pair ["htransm_15_0","htransm_14_0","htransm_13_0","htransm_12_0","htransm_11_0","htransm_10_0","htransm_9_0","htransm_8_0","htransm_7_0","htransm_6_0","htransm_5_0","htransm_4_0","htransm_3_0","htransm_2_0","htransm_1_0","htransm_0_0","htransm_15_1","htransm_14_1","htransm_13_1","htransm_12_1","htransm_11_1","htransm_10_1","htransm_9_1","htransm_8_1","htransm_7_1","htransm_6_1","htransm_5_1","htransm_4_1","htransm_3_1","htransm_2_1","htransm_1_1","htransm_0_1"];
val transm_vars' = ksTools.mk_primed_state transm_vars

val split_varsl = List.map mk_bool_var ["hsplit_15","hsplit_14","hsplit_13","hsplit_12","hsplit_11","hsplit_10","hsplit_9","hsplit_8","hsplit_7","hsplit_6","hsplit_5","hsplit_4","hsplit_3","hsplit_2","hsplit_1","hsplit_0"];
val split_vars = list_mk_pair split_varsl

val mask_varsl = List.map mk_bool_var ["hmask_15","hmask_14","hmask_13","hmask_12","hmask_11","hmask_10","hmask_9","hmask_8","hmask_7","hmask_6","hmask_5","hmask_4","hmask_3","hmask_2","hmask_1","hmask_0"];
val mask_vars = list_mk_pair mask_varsl

val busreq_varsl = List.map mk_bool_var ["hbusreq_15","hbusreq_14","hbusreq_13","hbusreq_12","hbusreq_11","hbusreq_10","hbusreq_9","hbusreq_8","hbusreq_7","hbusreq_6","hbusreq_5","hbusreq_4","hbusreq_3","hbusreq_2","hbusreq_1","hbusreq_0"];
val busreq_vars = list_mk_pair busreq_varsl

val split_vars' = ksTools.mk_primed_state split_vars
val mask_vars' = ksTools.mk_primed_state mask_vars
val busreq_vars' = ksTools.mk_primed_state busreq_vars

val nbrr = list_mk_conj(List.map mk_neg (List.drop(busreq_varsl,16-nm)))

val nhsr = list_mk_conj(List.map mk_neg (List.drop(split_varsl,16-nm)))

val nmr = list_mk_conj(List.map mk_neg (List.drop(mask_varsl,16-nm)))

val grant_vars = mk_bool_pair ["hgrant_3","hgrant_2","hgrant_1","hgrant_0"];
val grant_vars' = ksTools.mk_primed_state grant_vars

val master_vars = mk_bool_pair ["hmaster_3","hmaster_2","hmaster_1","hmaster_0"];
val master_vars' = ksTools.mk_primed_state master_vars

val hselvl = ["hsel_3","hsel_2","hsel_1","hsel_0"];
val hselv = mk_bool_pair hselvl
val hselv' = ksTools.mk_primed_state hselv

(* need 4 vars since slave 0 who is split capable can split on any one of 16 masters
   at the moment we allow slaves to split on only one master at most. otherwise we need 16 vars here *)
val slvsplt_varsl = List.map (fn l => "hslvsplt_"^(int_to_string (hd l))^"_"^(int_to_string (last l))) (cartprod [List.tabulate(ns,I),rev (List.tabulate(4,I))])
val slvsplt_vars = mk_bool_pair slvsplt_varsl
val slvsplt_vars' = ksTools.mk_primed_state slvsplt_vars
val ssv = fromMLlist (List.map list_mk_pair (multi_part ((length slvsplt_varsl) div ns) (List.map mk_bool_var slvsplt_varsl)))

val nss =  list_mk_conj(List.map (mk_neg o mk_bool_var) slvsplt_varsl);

val bbv' = ksTools.mk_primed_state bbv
val htransv = mk_bool_pair ["htrans_0","htrans_1"]
val hrespv = mk_bool_pair ["hresp_0","hresp_1"]
val hwsv' = ksTools.mk_primed_state hwsv

val Im_state = list_mk_pair(List.concat (List.map strip_pair [htransv,busreq_vars]))

val Is_state = list_mk_pair(List.concat (List.map strip_pair [``(haddr_0:bool,hreadyout:bool)``,
							      hrespv,split_vars,hselv]))

val Ia_state = list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,master_vars,busreq_vars]))

val Ra_state = list_mk_pair(List.concat
				(List.map strip_pair [``hreadyout:bool``,grant_vars,master_vars,
						      mask_vars,busreq_vars,htransv]))
val Ra_state2 = list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,master_vars,
							       busreq_vars,htransv]))
val Ra_state' = ksTools.mk_primed_state Ra_state

val Rm_state =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,transm_vars,busreq_vars,
							       hrespv,burstm_vars,bbv,mask_vars,split_vars,master_vars]))
val Rm_state2 =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,busreq_vars,hrespv,
								split_vars,master_vars]))
val Rm_state' = ksTools.mk_primed_state Rm_state

val Rs_state = list_mk_pair(List.concat (List.map strip_pair  [``hreadyout:bool``,hselv,hrespv,hwsv,htransv,
							       ``hburst_0:bool``,slvsplt_vars,split_vars,grant_vars,master_vars]))
val Rs_state2 = list_mk_pair(List.concat (List.map strip_pair  [``hreadyout:bool``,hselv,hrespv,htransv,
							       ``hburst_0:bool``,split_vars,grant_vars,master_vars]))
val Rs_state' = ksTools.mk_primed_state Rs_state


val Rx_state =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,transm_vars,burstm_vars,
							       htransv,``hburst_0:bool``]))
val Rx_state2 =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,grant_vars,htransv,``hburst_0:bool``]))
val Rx_state' = ksTools.mk_primed_state Rx_state

val Rd_state =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,hselv,``haddr_0:bool``]))
val Rd_state' = ksTools.mk_primed_state Rd_state


val RCn_state =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,htransv,bbv,hwsv]))
val RCn_state2 =  list_mk_pair(List.concat (List.map strip_pair [``hreadyout:bool``,htransv]))
val RCn_state' = ksTools.mk_primed_state RCn_state

val I1h_state =  list_mk_pair(undup Term.var_compare
				    (List.concat (List.map strip_pair [Im_state,Is_state,Ia_state,Ra_state2,RCn_state2,
								       Rm_state2,Rx_state2,(*Rd_state,*)Rs_state2])))
val R1h_state = I1h_state
val R1h_state' = ksTools.mk_primed_state R1h_state

val mod16defs = [MOD16_ZERO_def,MOD16_ONE_def,MOD16_IS_ZERO_def,MOD16_IS_ONE_def,MOD16_INC_def,MOD16_HOLD_def,dest_mod16,
		 dest_mod16r,dest_mod16_tup,FST_COND,SND_COND,MOD16_IS_16_def,xor_def,MOD16_N2B_def,MOD16_N2B'_def,
		 MOD16_PROJ_def]
val m16b = [MOD16_ZERO_def,MOD16_ONE_def,MOD16_IS_ZERO_def,MOD16_IS_ONE_def,MOD16_INC_def,
	    MOD16_INC4_def,MOD16_HOLD_def,FST_COND,SND_COND, MOD16_IS_16_def,xor_def]
val m16n2b = [MOD16_N2B_15,MOD16_N2B_14,MOD16_N2B_13,MOD16_N2B_12,MOD16_N2B_11,MOD16_N2B_10,MOD16_N2B_9,MOD16_N2B_8,
	      MOD16_N2B_7,MOD16_N2B_6,MOD16_N2B_5,MOD16_N2B_4,MOD16_N2B_3,MOD16_N2B_2,MOD16_N2B_1,MOD16_N2B_0]
val m16exp = [MOD16_FORALL_EXPAND16,MOD16_FORALL_EXPAND4,MOD16_FORALL_EXPAND8]

(* unroll abstract model into purely boolean model *)
fun unroll_ahb_CONV maindefs Adef abbrev_defs t =
	    (PURE_ONCE_REWRITE_CONV maindefs
             THENC NCONV nm (PURE_ONCE_REWRITE_CONV [Adef])
             THENC UNCHANGED_CONV (REWRITE_CONV abbrev_defs)
              THENC UNCHANGED_CONV (SIMP_CONV (pure_ss++BETA_ss) m16exp)
               THENC UNCHANGED_CONV (SIMP_CONV (pure_ss++numSimps.REDUCE_ss) ([COND_CLAUSES]))
               THENC UNCHANGED_CONV (SIMP_CONV (pure_ss++EL_ss) (m16n2b))
	       THENC UNCHANGED_CONV (SIMP_CONV (pure_ss++pairSimps.PAIR_ss) ([dest_mod16r2,dest_mod16_tup]@m16b))) t


end
end
