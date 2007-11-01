(*load "bossLib"; load "pairSyntax"; load "boolSyntax"; *)

(* 
once this has been compiled, model checking can be done interactively as follows: 

app load ["holCheck","amba_apb"];
val apb1 = amba_apb.mk_apb();  (* init the defs *)
val apb2 = holCheck.holCheck apb1 handle ex => Raise ex;
List.map (isSome o #2) (valOf (modelTools.get_results apb2)); (* should be all true *)

model checking is delibrately not part of the compile because it takes too long and this is a demo
*) 
structure amba_apb =
struct

local 

open Globals HolKernel Parse goalstackLib

open boolSyntax bossLib Ho_Rewrite Tactical Tactic PairRules pairTheory
open ctl2muTheory cearTools amba_apbTheory commonTools bddTools ctlTheory ctlSyntax ksTools modelTools mod16Theory amba_common

in

val R1rp = SIMP_RULE arith_ss ([FST,SND,TRANS_APB_M_def,TRANS_APB_S_def,TRANS_BUS_def,PSEL_def,SDATA_def,SADDR_def]@mod16defs) TRANS_APB_def;

local

    val state = ``(paddr:bool,pwrite:bool,psel:bool,psel_3:bool,psel_2:bool,psel_1:bool,psel_0:bool,penable:bool,pdata:bool,mdata:bool,maddr:bool,sdata_0:bool,saddr_0:bool,sdata_1:bool,saddr_1:bool)`` 
    val T1rp = [(".",rhs (concl(Drule.SPEC_ALL R1rp)))]    
    val bvmp = List.map (with_flag (show_types,false) term_to_string) ((pairSyntax.strip_pair state)@(pairSyntax.strip_pair (mk_primed_state state))) 

    (* initial states *)
    infixr 5 C_AND infixr 5 C_OR infixr 2 C_IMP infix C_IFF

    fun apb_AP s = C_AP state (mk_bool_var s)

    val ctl_initp = (C_NOT(apb_AP "psel")) C_AND (C_NOT(apb_AP "penable"))

    fun intpow x y = Real.trunc(Math.pow(Real.fromInt x,Real.fromInt y))

    fun apb_PSEL_proj i = if i<4 then apb_AP ("psel_"^(int_to_string i)) else failwith ("apb_PSEL_proj arg out of range")
    
    fun apb_PSEL' n k = 
	if k=0 then 
	    if n=1 then apb_AP "psel_0" else C_NOT(apb_AP "psel_0")
	else if n >= intpow 2 k then apb_PSEL_proj k 
	     else C_NOT(apb_PSEL_proj k) C_AND (apb_PSEL' (if n >= intpow 2 k then n-(intpow 2 k) else n) (k-1)) 

    fun apb_PSEL x = apb_PSEL' x 3
 
    fun apb_SADDR x = if x<2 then (apb_AP ("saddr_"^(int_to_string x))) else failwith ("apb_SADDR arg out of range")
    fun apb_SDATA x = if x<2 then (apb_AP ("sdata_"^(int_to_string x))) else failwith ("apb_SDATA arg out of range")

    (* AG (~penable /\ psel /\ pwrite /\ PSEL x ==> AX AX sdata x = mdata) coherence + latency in write cycle *)
    fun ctl_latw n = C_AG ((list_C_AND [C_NOT(apb_AP "penable"),apb_AP "psel",apb_AP "pwrite",apb_PSEL n]) 
			     C_IMP ((C_AX (C_AX (apb_SDATA n))) C_IFF (apb_AP "mdata")))

    (* AG (~penable /\ psel /\ ~pwrite /\ PSEL x ==> AX AX mdata  = sdata x) coherence + latency in read cycle *)
    fun ctl_latr n = C_AG ((list_C_AND [C_NOT(apb_AP "penable"),apb_AP "psel",C_NOT(apb_AP "pwrite"),apb_PSEL n]) 
			     C_IMP ((C_AX (C_AX (apb_AP "mdata")) C_IFF (apb_SDATA n))))

    (* AG (AF (psel ==> AX penable)) (the imp is there (not conj) because psel may never assert but that's not deadlock)*)
    val ctl_dlp = C_AG (C_AF ((apb_AP "psel") C_IMP (C_AX (apb_AP "penable"))))

    val ctl_latr_list = List.tabulate(2,fn n => ("ctl_latr"^(int_to_string n),ctl_latr n))
    val ctl_latw_list = List.tabulate(2,fn n => ("ctl_latw"^(int_to_string n),ctl_latw n))
in 

fun mk_apb() =  ((set_init (rhs (concl(Drule.SPEC_ALL INIT_APB_def)))) o (set_trans T1rp) o (set_flag_ric true) o 
		 (set_name "apb") o (set_vord bvmp)o (set_state state) o 
		 (set_props ([("ctl_initp",ctl_initp),("ctl_dlp", ctl_dlp)]@ctl_latr_list@ctl_latw_list))) empty_model

end

(* additional vars used by bridge (not sure if I really need this since not doing any model checking *)
val bvmb = ["hsel_1","hsel_1'","haddr_0","haddr_0'","hreadyout","hreadyout'","hresp_0","hresp_0'","hresp_1","hresp_1'","hws0","hws0'","hws1","hws1'","hws2","hws2'","hws3","hws3'","htrans_0","htrans_0'","htrans_1","htrans_1'","hburst_0","hburst_0'","bb2","bb2'"];


end 
end






