(*load "bossLib"; 
load "pairSyntax";
load "boolSyntax";
 *)

structure amba_apb =
struct

local 

open Globals HolKernel Parse goalstackLib;

open boolSyntax;
open bossLib;
open ctl2muTheory;
open cearTools;
open Ho_Rewrite;
open amba_apbTheory;
open Tactical;
open Tactic;
open PairRules;
open commonTools
open bddTools
open ctlTheory
open ctlSyntax
open ksTools
open modelTools

in

val R1rp = REWRITE_RULE [TRANS_M_def,TRANS_S_def] TRANS_APB_def
	
local

    val state = ``(paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool)``
    val T1rp = [(".",rhs (concl(Drule.SPEC_ALL R1rp)))]    
    val bvmp = ["paddr_0","paddr_0'","pwrite","pwrite'","psel_0","psel_0'","penable","penable'",
		"pdata_0","pdata_0'","m_0_0","m_0_0'","s_0_0_0","s_0_0_0'"] (* APB vars *)

    (* initial states *)
    infixr 5 C_AND infixr 5 C_OR infixr 2 C_IMP infix C_IFF

    fun apb_AP s = C_AP state (mk_bool_var s)

    val ctl_initp = (C_NOT(apb_AP "psel_0")) C_AND (C_NOT(apb_AP "penable"))

    (* AG (~penable /\ psel /\ pwrite /\ ~paddr_0 ==> AX AX s_0_0_0 = m_0_0) coherence + latency in write cycle *)
    val ctl_latw = C_AG ((list_C_AND [C_NOT(apb_AP "penable"),apb_AP "psel_0",apb_AP "pwrite",C_NOT(apb_AP("paddr_0"))]) 
			     C_IMP ((C_AX (C_AX (apb_AP "s_0_0_0"))) C_IFF (apb_AP "m_0_0")))

    (* AG (~penable /\ psel /\ ~pwrite /\ ~paddr_0 ==> s_0_0_0 = AX AX m_0_0) coherence + latency in read cycle *)
    val ctl_latr = C_AG ((list_C_AND [C_NOT(apb_AP "penable"),apb_AP "psel_0",C_NOT(apb_AP "pwrite"),C_NOT(apb_AP("paddr_0"))]) 
			     C_IMP ((C_AX (C_AX (apb_AP "m_0_0")) C_IFF (apb_AP "s_0_0_0"))))

    (* AG (AF (psel ==> AX penable)) (the imp is there (rather than conj) because psel may never assert but that is not deadlock) *)
    val ctl_dlp = C_AG (C_AF ((apb_AP "psel_0") C_IMP (C_AX (apb_AP "penable"))))

in 

fun mk_apb() =  ((set_init (rhs (concl(Drule.SPEC_ALL INIT_APB_def)))) o (set_trans T1rp) o (set_ric true) o (set_name "apb") o 
		 (set_vord bvmp)o (set_state state) o 
		 (set_props[("ctl_initp",ctl_initp),("ctl_latw", ctl_latw),("ctl_latr", ctl_latr),("ctl_dlp", ctl_dlp)])) empty_model


(* interactive usage example
app load ["holCheck","amba_apb"];
val apb1 = amba_apb.mk_apb();  (* init the defs *)
val apb2 = holCheck.holCheck apb1 handle ex => Raise ex;
*) 

end

(* additional vars used by bridge (not sure if I really need this since not doing any model checking *)
val bvmb = ["hsel_1","hsel_1'","haddr_0","haddr_0'","hreadyout","hreadyout'","hresp_0","hresp_0'","hresp_1","hresp_1'","hws0","hws0'","hws1","hws1'","hws2","hws2'","hws3","hws3'","htrans_0","htrans_0'","htrans_1","htrans_1'","hburst_0","hburst_0'","bb2","bb2'"];


end 
end






