(*load "bossLib"; 
load "pairSyntax";
load "boolSyntax";
load "muLib";
load "CTL" *)

structure amba_ahb =
struct

local 

open Globals HolKernel Parse goalstackLib;

open boolSyntax;
open bossLib;
open ctl2muTheory;
open cearTools;
open Ho_Rewrite;
open Tactical;
open Tactic;
open PairRules;
open holCheckTools
open bddTools
open ctlTheory
open ctlSyntax
open ksTools
open amba_ahbTheory;

in

val abbrev_defs = [IDLE_def,BUSY_def,NOSEQ_def,SEQ_def,OKAY_def,ERROR_def,RETRY_def,SPLIT_def,SINGLE_def,INC4_def]

val I1rh = PURE_REWRITE_RULE ([INIT_M_def,INIT_S_def,INIT_A_def]@abbrev_defs) INIT_AHB_def

val R1rh = PURE_REWRITE_RULE ([TRANS_A_def,TRANS_M_0_def,TRANS_M_1_def,TRANS_M_2_def,TRANS_X_def,TRANS_D_def,TRANS_CNT_def,TRANS_S_0_def,TRANS_S_1_def]@abbrev_defs) TRANS_AHB_def

local 

    val state = rand(lhs(concl(Drule.SPEC_ALL INIT_AHB_def)))

    val T1rh = [(".",snd(dest_eq (concl(Drule.SPEC_ALL R1rh))))]
	       
    (* CTL properties *)
    infixr 5 C_AND infixr 5 C_OR infixr 2 C_IMP infix C_IFF infixr 1 C_AU

    fun ahb_AP s = C_AP state (mk_bool_var s)

    (* abbrevs *)
	       
    val NSQ  = (ahb_AP "htrans_1") C_AND (C_NOT(ahb_AP "htrans_0"))
    val RDY = (ahb_AP "hreadyout")
    val OK = (C_NOT(ahb_AP "hresp_0")) C_AND (C_NOT(ahb_AP "hresp_1"))
    val RETRY = (C_NOT(ahb_AP "hresp_0")) C_AND (ahb_AP "hresp_1")
    val ERROR = (ahb_AP "hresp_0") C_AND (C_NOT(ahb_AP "hresp_1"))
    val SPLIT = (ahb_AP "hresp_0") C_AND (ahb_AP "hresp_1")

    (* initial states *)
    val ctl_inith =  (C_NOT(ahb_AP "hbusreq_0")) C_AND (C_NOT(ahb_AP "htrans_0")) C_AND (C_NOT(ahb_AP "htrans_1")) C_AND 
		     (C_NOT(ahb_AP "htrans_m1_0")) C_AND (C_NOT(ahb_AP "htrans_m1_1")) C_AND (C_NOT(ahb_AP "htrans_m2_0")) C_AND 
		     (C_NOT(ahb_AP "htrans_m2_1")) C_AND (C_NOT(ahb_AP "hbusreq_1")) C_AND (C_NOT(ahb_AP "hbusreq_2")) C_AND 
		     (ahb_AP "hreadyout") C_AND (C_NOT(ahb_AP "hresp_0")) C_AND (C_NOT(ahb_AP "hresp_1")) C_AND 
		     (C_NOT(ahb_AP "hws0")) C_AND (C_NOT(ahb_AP "hws1")) C_AND (C_NOT(ahb_AP "hws2")) C_AND (C_NOT(ahb_AP "hws3")) C_AND
		     (C_NOT(ahb_AP "hgrant_0")) C_AND (ahb_AP "hgrant_1") C_AND (C_NOT(ahb_AP "hgrant_2")) C_AND 
		     (C_NOT(ahb_AP "bb0")) C_AND (C_NOT(ahb_AP "bb1")) C_AND (C_NOT(ahb_AP "bb2")) C_AND (C_NOT(ahb_AP "bb3")) C_AND 
 		     (C_NOT(ahb_AP "hmaster_0")) C_AND (C_NOT(ahb_AP "hslv0splt_0")) C_AND (C_NOT(ahb_AP "hslv0splt_1")) C_AND 
		     (C_NOT(ahb_AP "hsplit_0")) C_AND (C_NOT(ahb_AP "hsplit_1")) C_AND (C_NOT(ahb_AP "hmask_0")) C_AND 
		     (C_NOT(ahb_AP "hmask_1"));

    (* the properties are framed so that if the initial states are contained in the satisfying set then we are okay *)

    (* one and only one master always has the grant *)
    val ctl_grant_always = C_AG ((((ahb_AP "hgrant_0") C_OR (ahb_AP "hgrant_1") C_OR (ahb_AP"hgrant_2"))) C_AND
				 (((ahb_AP "hgrant_0") C_IMP ((C_NOT ((ahb_AP "hgrant_1"))) C_AND (C_NOT((ahb_AP "hgrant_2"))))) C_AND 
				 (((ahb_AP "hgrant_1")) C_IMP ((C_NOT ((ahb_AP "hgrant_0"))) C_AND (C_NOT((ahb_AP "hgrant_2"))))) C_AND 
				 (((ahb_AP "hgrant_2")) C_IMP ((C_NOT ((ahb_AP "hgrant_0"))) C_AND (C_NOT((ahb_AP "hgrant_1")))))));

    (* everyone gets the bus *)
    (* AG (hbusreq_x /\ ~hmask_x ==> AF hgrant_x) *)
    val ctl_grant = C_AG (((ahb_AP "hbusreq_1") C_AND (C_NOT(ahb_AP "hmask_0"))) C_IMP (C_AF (ahb_AP "hgrant_1")))

    (* for low priority guy we can't guarantee the bus but the possibility should exist *)
    val ctl_grant2 = C_AG (((ahb_AP "hbusreq_2") C_AND (C_NOT(ahb_AP "hmask_1"))) C_IMP (C_EF (ahb_AP "hgrant_2")))

    (* transfer completes within two cycles from transfer start (this is for without waitstates so now obsolete) *)
    (* AG (init ==> AX AX hreadyout)  
    val ctl_lat = ``C_AG (C_IMP((^ctl_init), C_AX (C_AX (C_BOOL ((ahb_AP "hreadyout")))))``;*)

    (* all transfers complete eventually.. this is only for sanity checking, subsumed by transfer latency checks *)
    (* AG (no_seq ==> AX(A(~no_seq U ((READY /\ OK) \/ RETRY \/ ERROR \/ SPLIT)))))*)
    val ctl_latf = C_AG (NSQ C_IMP (C_AX((C_NOT(NSQ)) C_AU (SPLIT C_OR RETRY C_OR ERROR C_OR (RDY C_AND OK)))))
 
    (* to make it easier to type (as in keyboard) various latency properties *)
    val lat_rec_def = Define `(lat_rec f 0       = f) /\
                              (lat_rec f (SUC n) = C_OR(f,C_AX (lat_rec f n)))`; 

    (* bus latency is at most four (four waitstates ) cycles*) 
    (* AG (lat_rec 4 hreadyout) *)  
    val ctl_bus_lat = C_AG (rhs(concl(SIMP_CONV std_ss [lat_rec_def] ``lat_rec (^(ahb_AP "hreadyout")) (SUC (SUC (SUC (SUC 0))))``)));

    (* transfer completes at most ten (two overhead + four waitstates + four beat burst) cycles from transfer start *)
    (* AG ((no_seq /\ single ==> lat_rec 2  (hreadyout /\ OK)) /\ 
           (no_seq /\ inc4   ==> lat_Rec 10 (hreadyout /\ OK))) *)  
    val ctl_trans_lat = 
    C_AG ((NSQ C_AND (C_NOT (ahb_AP "hburst_0")) C_IMP 
			((rhs(concl(SIMP_CONV std_ss [lat_rec_def] 
			  ``lat_rec (^RDY /\ ^OK) (SUC (SUC 0))``))))) 
	      C_AND 
	  ((NSQ C_AND (ahb_AP "hburst_0")) C_IMP 
			(((C_AX((C_NOT(NSQ)) C_AU (SPLIT C_OR RETRY C_OR ERROR C_OR (RDY C_AND OK))))) C_AND 
			(rhs(concl(SIMP_CONV std_ss [lat_rec_def] 
		          ``lat_rec (^RDY /\ ^OK) (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))``))))))

    (* no deadlock (this is conducted using the non-totalised R) *)
    val ctl_dlh = ``C_AG (C_EX (C_BOOL(B_TRUE)))``;
  

    val bvmh = ["hreadyout","hreadyout'","htrans_m2_0","htrans_m2_0'","htrans_m2_1","htrans_m2_1'","htrans_m1_0","htrans_m1_0'",
		"htrans_m1_1","htrans_m1_1'","htrans_m0_0","htrans_m0_0'","htrans_m0_1","htrans_m0_1'","htrans_0","htrans_0'",
		"htrans_1","htrans_1'","hresp_0","hresp_0'","hresp_1","hresp_1'","hmask_0","hmask_0'","hmask_1","hmask_1'","hbusreq_0",
		"hbusreq_0'","hbusreq_1","hbusreq_1'","hbusreq_2","hbusreq_2'","hgrant_0","hgrant_0'","hgrant_1","hgrant_1'","hgrant_2",
		"hgrant_2'","hsel_0","hsel_0'","hsel_1","hsel_1'","haddr_0","haddr_0'","hws0","hws0'","hws1","hws1'","hws2","hws2'",
		"hws3","hws3'","hmaster_0","hmaster_0'","bb0","bb0'","bb1","bb1'","bb2","bb2'","bb3","bb3'","hburst_m2_0","hburst_m2_0'",
		"hburst_m1_0","hburst_m1_0'","hburst_0","hburst_0'","hslv0splt_0","hslv0splt_0'","hslv0splt_1","hslv0splt_1'","hsplit_0",
		"hsplit_0'","hsplit_1","hsplit_1'"];

in 

fun mk_ahb() = ((rhs(concl(Drule.SPEC_ALL I1rh)),T1rh,true,SOME "ahb",SOME bvmh, SOME state),
		[ctl_inith,ctl_grant_always,ctl_grant,ctl_grant2,ctl_latf,ctl_trans_lat])

(* interactive usage example
app load ["bdd","holCheck","amba_ahb"];
bdd.init 100000 10000; 
val ahb = amba_ahb.mk_ahb();  (* init the defs *)
val ((S0,T1,Ric,nm,vars,state),fl) = ahb;
val dtb = PrimitiveBddRules.dest_term_bdd; 
val _ = set_trace "metis" 0; val _ = set_trace "meson" 0; val _ = set_trace "notify type variable guesses" 0; 
val (res,ksd,ic) = holCheck.holCheck (fst ahb) (snd ahb) NONE NONE handle ex => Raise ex;
*) 

end

end 
end





