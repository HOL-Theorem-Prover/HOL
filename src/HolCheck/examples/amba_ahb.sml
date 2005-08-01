
(* app load ["boolSyntax","bossLib","PairRules","Ho_Rewrite","Tactical","Tactic","ctl2muTheory","cearTools","commonTools",
	     "bddTools","ctlTheory","ctlSyntax","ksTools","amba_ahbTheory","modelTools","mod16Theory","listTheory"] *)

(*
once this has been compiled, model checking can be done interactively as follows:

app load ["holCheck","amba_ahb"];
val ahb1 = amba_ahb.mk_ahb();  (* init the defs *)
val ahb1 = modelTools.set_flag_abs false ahb1; (* turn off abstraction -- see below *)
val ahb2 = holCheck.holCheck ahb1 handle ex => Raise ex;
List.map (isSome o #2) (valOf (modelTools.get_results ahb2)); (* should be all true *)

model checking is delibrately not part of the compile because it takes too long and this is a demo
*) 

(* FIXME: WARNING! WARNING! Ever since a change to the way I do abstractions, 
          this example pretty much dies in the refinement 
          stage. Run with abstraction off and it goes through eventually. 
          This is under investigation. *)
structure amba_ahb =
struct

local 

open Globals HolKernel Parse goalstackLib;

open boolSyntax bossLib PairRules Ho_Rewrite Tactical Tactic Drule Conv boolTheory listTheory
open ctl2muTheory cearTools commonTools bddTools ctlTheory ctlSyntax ksTools amba_ahbTheory modelTools mod16Theory amba_common

val nm = 8;
val nb = 16;
val ns = 16;
val nw = 16;

 (* create var ordering *)
    val burstmv =  ["hburstm_15_0","hburstm_14_0","hburstm_13_0","hburstm_12_0","hburstm_11_0","hburstm_10_0",
		    "hburstm_9_0","hburstm_8_0","hburstm_7_0","hburstm_6_0","hburstm_5_0","hburstm_4_0","hburstm_3_0",
		    "hburstm_2_0","hburstm_1_0","hburstm_0_0"]
    val burstmv' = List.map prm burstmv
    val burstmvl = interleave burstmv' burstmv
    val transmv =  ["htransm_15_0","htransm_14_0","htransm_13_0","htransm_12_0","htransm_11_0","htransm_10_0",
		    "htransm_9_0", "htransm_8_0","htransm_7_0","htransm_6_0","htransm_5_0","htransm_4_0","htransm_3_0",
		    "htransm_2_0","htransm_1_0","htransm_0_0","htransm_15_1","htransm_14_1","htransm_13_1","htransm_12_1",
		    "htransm_11_1","htransm_10_1","htransm_9_1","htransm_8_1","htransm_7_1","htransm_6_1","htransm_5_1",
		    "htransm_4_1","htransm_3_1","htransm_2_1","htransm_1_1","htransm_0_1"];
    val transmv' = List.map prm transmv
    val transmvl = interleave transmv' transmv
    val maskv =  ["hmask_15","hmask_14","hmask_13","hmask_12","hmask_11","hmask_10","hmask_9","hmask_8","hmask_7",
		  "hmask_6","hmask_5", "hmask_4","hmask_3","hmask_2","hmask_1","hmask_0"];  
    val maskv' = List.map prm maskv
    val maskvl = interleave maskv' maskv
    val splitv =  ["hsplit_15","hsplit_14","hsplit_13","hsplit_12","hsplit_11","hsplit_10","hsplit_9","hsplit_8",
		   "hsplit_7","hsplit_6", "hsplit_5","hsplit_4","hsplit_3","hsplit_2","hsplit_1","hsplit_0"];
    val splitv' = List.map prm splitv
    val splitvl = interleave splitv' splitv
    val busreqv =  ["hbusreq_15","hbusreq_14","hbusreq_13","hbusreq_12","hbusreq_11","hbusreq_10","hbusreq_9",
		    "hbusreq_8","hbusreq_7","hbusreq_6","hbusreq_5","hbusreq_4","hbusreq_3","hbusreq_2","hbusreq_1",
		    "hbusreq_0"];
    val busreqv' = List.map prm busreqv
    val busreqvl = interleave busreqv' busreqv
    val grantv =  ["hgrant_3","hgrant_2","hgrant_1","hgrant_0"];
    val grantv' = List.map prm grantv
    val grantvl = interleave grantv' grantv
    val masterv =  ["hmaster_3","hmaster_2","hmaster_1","hmaster_0"];
    val masterv' = List.map prm masterv
    val mastervl = interleave masterv' masterv
    val slvspltv = List.map (fn l => "hslvsplt_"^(int_to_string (hd l))^"_"^(int_to_string (last l))) 
			    (cartprod [List.tabulate(ns,I),List.tabulate(nm,I)])
    val slvspltv' = List.map prm slvspltv
    val slvspltvl = interleave slvspltv' slvspltv
    val bbv =  ["bb3","bb2","bb1","bb0"]
    val bbv' = List.map prm bbv
    val bbvl = interleave bbv' bbv
    val htransv =  ["htrans_0","htrans_1","hburst_0"]
    val htransv' = List.map prm htransv
    val htransvl = interleave htransv' htransv
    val hrespv =  ["hresp_0","hresp_1"]
    val hrespv' = List.map prm hrespv
    val hrespvl = interleave hrespv' hrespv
    val hselv = ["hsel_3","hsel_2","hsel_1","hsel_0"];
    val hselv' = List.map prm hselv
    val hselvl = interleave hselv' hselv
    val hwsv =  ["hws3","hws2","hws1","hws0"]
    val hwsv' = List.map prm hwsv
    val hwsvl = interleave hwsv' hwsv

    val bvmh = (["hreadyout","hreadyout'"]@busreqvl@maskvl@grantvl@mastervl@transmvl@burstmvl@htransvl@
	        bbvl@hwsvl@["haddr_0","haddr_0'"]@hselvl@hrespvl@splitvl@slvspltvl)

in

local 

    val mk_bool_pair = pairSyntax.list_mk_pair o (List.map mk_bool_var)

    val state = rand(lhs(concl(SPEC_ALL INIT_AHB_def)))

    fun ahb2ctl t =  (bool2ctl state ((type_of state)-->bool) 
		      (rhs(concl(UNCHANGED_CONV (SIMP_CONV (pure_ss++BETA_ss++numSimps.REDUCE_ss) 
					   ([RETRY_def,ERROR_def,GRANT_def,COND_CLAUSES,SPLIT_def,HSPLIT_def,MASTER_def]
					    @m16n2b@m16exp)) t))))

    val T1rh = [(".",rhs(concl(SPEC_ALL amba_ahb_R1rh)))]
	       
    (* CTL properties *)

    (* stupid ML requires redoing fixity decls *)
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
    val ctl_inith =  bool2ctl state  (type_of state --> bool) (rhs (concl(SPEC_ALL amba_ahb_I1rh)))

    (* the properties are framed so that if the initial states are contained in the satisfying set then we are okay *)

    (* default master always the bus upon request (either right away, or if masked then after demasking via hsplit) *)
    (* AG (hbusreq_x /\ ~hmask_x ==> AF hgrant_x) *)
    val dmn = (nm-1) (* default master number*)
    val ctl_hsplit_follows_split = 
	ahb2ctl ``!m.m<16 ==> (SPLIT (hresp_0:bool,hresp_1:bool) /\ GRANT m (^(mk_bool_pair masterv)))
	    ==> (BC_AF (HSPLIT m (^(mk_bool_pair splitv))))``

    val ctl_grant = C_AG (ahb2ctl ``(hbusreq_7:bool) ==> ((BC_AX (GRANT ^(fromMLnum dmn) (^(mk_bool_pair grantv)))) \/
			  (BC_AF ((HSPLIT ^(fromMLnum dmn) (^(mk_bool_pair splitv))) ==> 
							BC_AX (GRANT ^(fromMLnum dmn) (^(mk_bool_pair grantv))))))``)

    (* for low priority guy we can't guarantee the bus but the possibility should exist *)
    (*val ctl_grant2 = C_EF (((ahb_AP "hbusreq_2") C_AND (C_NOT(ahb_AP "hmask_1"))) C_IMP (C_EF (ahb_AP "hgrant_2")))*)
    val ctl_grant2 = C_AG (ahb2ctl ``(hbusreq_5:bool) ==> ((BC_EX (GRANT 5 (^(mk_bool_pair grantv)))) \/
			  (BC_AF ((HSPLIT 5 (^(mk_bool_pair splitv))) ==> BC_EX (GRANT 5 (^(mk_bool_pair grantv))))))``)
    
    (* quick sanity checks *)
    val ch1 = C_AG (ahb2ctl ``^(rhs(concl(SPEC_ALL amba_ahb_I1rh))) ==> 
			    ~SPLIT(hresp_0,hresp_1) /\ ~RETRY(hresp_0,hresp_1) /\ 
										    ~ERROR(hresp_0,hresp_1)``)
    val ch2 = C_AG (ahb2ctl ``~SPLIT(hresp_0,hresp_1) /\ ~RETRY(hresp_0,hresp_1) /\ ~ERROR(hresp_0,hresp_1)``)

    (* all transfers complete eventually.. this is only for sanity checking, subsumed by transfer latency checks *)
    (* AG (no_seq ==> AX(A(~no_seq U ((READY /\ OK) \/ RETRY \/ ERROR \/ SPLIT)))))*)
    (*SPLIT C_OR RETRY C_OR ERROR C_OR*)
    val ctl_latf = C_AG (NSQ C_IMP (C_AX((C_NOT(NSQ)) C_AU ((RDY C_AND OK)))))
 
    (* to make it easier to type (as in keyboard) various latency properties *)
    val lat_rec_def = Define `(lat_rec f 0       = f) /\
                              (lat_rec f (SUC n) = C_OR(f,C_AX (lat_rec f n)))`; 

    (* bus latency is at most four (four waitstates ) cycles*) 
    (* AG (lat_rec 4 hreadyout) *)  
    val ctl_bus_lat = C_AG (rhs(concl(SIMP_CONV std_ss [lat_rec_def] ``lat_rec (^(ahb_AP "hreadyout")) 
						(SUC (SUC (SUC (SUC 0))))``)));

    (*SPLIT C_OR RETRY C_OR ERROR C_OR*)
    (* transfer completes at most ten (two overhead + four waitstates + four beat burst) cycles from transfer start *)
    (* FIXME: actually this does not properly detect burst termination, since slave says rdy+ok after every transfer *)
    (* FIXME: replace ugly SUCs with numerals *)
    (* AG ((no_seq /\ single ==> lat_rec 2  (hreadyout /\ OK)) /\ 
           (no_seq /\ inc4   ==> lat_rec 10 (hreadyout /\ OK))) *)  
    val ctl_trans_lat = 
    C_AG ((NSQ C_AND (C_NOT (ahb_AP "hburst_0")) C_IMP 
			((rhs(concl(SIMP_CONV std_ss [lat_rec_def] 
			  ``lat_rec (^RDY /\ ^OK) (SUC (SUC 0))``))))) 
	      C_AND 
	  ((NSQ C_AND (ahb_AP "hburst_0")) C_IMP 
			(((C_AX((C_NOT(NSQ)) C_AU ( (RDY C_AND OK))))) C_AND 
			(rhs(concl(SIMP_CONV std_ss [lat_rec_def] 
		          ``lat_rec (^RDY /\ ^OK) (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))``))))))

    (* no deadlock (this is conducted using the non-totalised R) *)
    val ctl_dlh = inst [alpha|->((type_of state-->bool))] ``C_AG (C_EX (C_BOOL(B_TRUE)))``;
   
in 

fun mk_ahb() = ((set_init (rhs (concl(SPEC_ALL amba_ahb_I1rh)))) o (set_trans T1rh) o (set_flag_ric true) o 
		(set_name "ahb") o (set_vord bvmh)o (set_state state) o 
		 (set_props[("ctl_inith",ctl_inith),(*("ctl_dlh",ctl_dlh)*)("ctl_grant",ctl_grant),
			    ("ctl_grant2",ctl_grant2),("ctl_latf",ctl_latf),("ctl_trans_lat",ctl_trans_lat)])) empty_model

end

end 
end
