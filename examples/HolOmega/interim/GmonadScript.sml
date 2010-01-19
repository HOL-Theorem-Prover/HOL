(* $Id$ *)

structure GmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory pairTheory categoryTheory monadTheory KmonadTheory ;
open auxLib ;
(*
load "auxLib" ;
load "GmonadTheory" ; open GmonadTheory ;
fun sge tm = set_goal ([], tm) ;
fun eev tacs = e (EVERY tacs) ;
fun eall [] = () 
  | eall (t :: ts) = (e t ; eall ts) ;
*)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "Gmonad";

(*---------------------------------------------------------------------------
  Monad predicate, based on unit, map and join term operators,
  generalised to general arrow types and also generalised to be relevant
  to compound monads 
 ---------------------------------------------------------------------------*)

val _ = type_abbrev ("dunit", Type `: \'A 'N 'M. !'a. ('a 'M, 'a 'N 'M) 'A`);
val _ = type_abbrev ("dmap",
   Type `: \'A 'N 'M. !'a 'b. ('a, 'b 'M) 'A -> ('a 'N 'M, 'b 'N 'M) 'A`);
val _ = type_abbrev ("djoin",
   Type `: \'A 'N 'M. !'a. ('a 'N 'N 'M, 'a 'N 'M) 'A`);

val EXTD_def = Define 
  `(EXTD ((id, comp) : 'A category) 
  (dmap : ('A, 'N, 'M) dmap, djoin: ('A, 'N, 'M) djoin) : ('A, 'N o 'M) ext) = 
    \:'a 'b. \f. comp djoin (dmap [:'a, 'b 'N:] f)` ;

   (* Gmonad ((id, comp) : 'A category) = \: 'N 'M.  *)
val Gmonad_def = Define 
   `Gmonad = \: 'A. \ ((id, comp) : 'A category). \: 'N 'M. 
     \ (dunit: ('A, 'N, 'M) dunit,
                dmap : ('A, 'N, 'M) dmap ,
                djoin: ('A, 'N, 'M) djoin) 
	       (unitNM: ('A, 'N o 'M) gunit,
                mapNM : ('A, 'N o 'M) gmap ,
                joinNM: ('A, 'N o 'M) gjoin)
   (unitM: ('A, 'M) gunit).
     (* map_I *)         (!:'a. dmap (unitM [:'a:]) = id) /\
     (* map_o *)         (!:'a 'b 'c. !(f: ('a, 'b) 'A) (g: ('b, 'c 'M) 'A).
			      dmap (comp g f) = comp (dmap g) (mapNM f)) /\
     (* map_unit *)      (!:'a 'b. !f: ('a, 'b 'M) 'A.
			      comp (dmap f) unitNM = comp dunit f) /\
     (* map_join *) (!:'a 'b. !f: ('a, 'b 'M) 'A.
             comp (dmap f) joinNM = comp djoin (dmap (dmap f))) /\
     (* join_unit *)     (!:'a. comp djoin dunit = id [:'a 'N 'M:]) /\
     (* join_map_unit *) (!:'a. comp djoin (dmap (unitNM [:'a:])) = id) /\
     (* join_map_join *) (!:'a. 
	  comp (djoin [:'a:]) (dmap djoin) = comp djoin joinNM) ` ;

(* check that these typecheck - 
  what you get when either 'N or 'M is the identity monad  *)
val _ = 
``Gmonad (id, comp) [:'N, I:] (unitN, mapN, joinN) (unitN, mapN, joinN) id `` ;
val _ = ``Gmonad (id, comp) [:I, 'M:] 
  ((\:'a. id [:'a 'M:]), EXT (id, comp) (mapM, joinM), (\:'a. id [:'a 'M:])) 
  (unitM, mapM, joinM) unitM `` ;

(* why does this require more type annotations than Gmonad_def ?? *)
val Gmonad_thm = store_thm ("Gmonad_thm", 
  ``Gmonad [:'A:] (id,comp) [:'N,'M:] 
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM =
     (* map_I *)  (!:'a. dmap [:'a, 'a:] (unitM [:'a:]) = id [:'a 'N 'M:]) /\ 
     (* map_o *) (!:'a 'b 'c. !(f :('a, 'b) 'A) (g :('b, 'c 'M) 'A).
                    dmap [:'a, 'c:] (comp [:'a, 'b, 'c 'M:] g f) =
                    comp (dmap [:'b, 'c:] g) (mapNM [:'a, 'b:] f)) /\
     (* map_unit *)      (!:'a 'b. !f: ('a, 'b 'M) 'A.
			      comp (dmap f) unitNM = comp dunit f) /\
     (* map_join *) (!:'a 'b. !f: ('a, 'b 'M) 'A.
             comp (dmap f) joinNM = comp djoin (dmap (dmap f))) /\
     (* join_unit *)     (!:'a. comp djoin dunit = id [:'a 'N 'M:]) /\
     (* join_map_unit *) (!:'a. comp djoin (dmap (unitNM [:'a:])) = id) /\
     (* join_map_join *) (!:'a. 
	  comp (djoin [:'a:]) (dmap djoin) = comp djoin joinNM)``,
  SRW_TAC [] [Gmonad_def]) ;

val (GmonadD, _) = EQ_IMP_RULE Gmonad_thm ;
val [GmD1, GmD2, GmD3, GmD4, GmD5, GmD6, GmD7] = 
  map DISCH_ALL (CONJUNCTS (UNDISCH GmonadD)) ;

val g_umj_monad_def = Define `g_umj_monad = 
  \: 'A 'N. \ (id, comp) (unitN, mapN, joinN).
  Gmonad [:'A:] (id, comp) [:'N, I:] 
    (unitN, mapN, joinN) (unitN, mapN, joinN) id` ;

val g_umj_monad_thm = store_thm ("g_umj_monad_thm",
  ``g_umj_monad [:'A, 'M:] (id, comp) (unit, map, join) =
    Gmonad [:'A:] (id, comp) [:'M, I:] (unit,map,join) (unit,map,join) id``,
  SRW_TAC [] [g_umj_monad_def]) ;

val g_umj_monad_exp = save_thm ("g_umj_monad_exp",
  REWRITE_RULE [Gmonad_thm] g_umj_monad_thm) ;

val (g_umj_monadD, g_umj_monadI) = EQ_IMP_RULE g_umj_monad_exp ;
val [g_umjD1, g_umjD2, g_umjD3, g_umjD4, g_umjD5, g_umjD6, g_umjD7] = 
  map DISCH_ALL (CONJUNCTS (UNDISCH g_umj_monadD)) ;
val _ = ListPair.map save_thm (["g_umjD1",
    "g_umjD2", "g_umjD3", "g_umjD4", "g_umjD5", "g_umjD6", "g_umjD7"],
  [g_umjD1, g_umjD2, g_umjD3, g_umjD4, g_umjD5, g_umjD6, g_umjD7]) ;

val tmj = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (joinNM = \:'a. extNM [:'a 'N 'M, 'a:] (id [:'a 'N 'M:]))`` ;

val Gmonad_join = store_thm ("Gmonad_join", tmj,
   EVERY [ (SRW_TAC [] [EXTD_def]), 
     farwmmp (GSYM GmD1), farwmmp (GSYM GmD4),
     farwmmp GmD1, farwmmp catDLU,
     (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;
  
val tmdj = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:]))`` ;

val Gmonad_djoin = store_thm ("Gmonad_djoin", tmdj,
   EVERY [ (SRW_TAC [] [EXTD_def]), 
     farwmmp GmD1, farwmmp catDRU,
     (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmm = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (mapNM = MAPE (id, comp) (unitNM, extNM))`` ;

val Gmonad_map = store_thm ("Gmonad_map", tmm,
  EVERY [ (SRW_TAC [] [EXTD_def, MAPE_def]), 
    farwmmp GmD2, farwmmp catDAss, farwmmp GmD6, farwmmp catDLU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmu = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==> 
   (unitNM = \:'a. comp [:'a, 'a 'M, 'a 'N 'M:]
     (dunit [:'a:]) (unitM [:'a:]))`` ;
   
val Gmonad_unit = store_thm ("Gmonad_unit", tmu,
  EVERY [ (SRW_TAC [] []),
    farwmmp (GSYM GmD3), farwmmp GmD1, farwmmp catDLU,
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmmd = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==> 
   (mapNM = \:'a 'b. \ (f : ('a, 'b) 'A).
     dmap [:'a, 'b:] (comp [:'a, 'b, 'b 'M:] (unitM [:'b:]) f))`` ;

val Gmonad_map_d = store_thm ("Gmonad_map_d", tmmd,
  EVERY [ (SRW_TAC [] []),
    farwmmp GmD2, farwmmp GmD1, farwmmp catDLU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tmeo = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (extNM (comp g f) = comp (extNM g) (mapNM f))`` ;
  
val Gmonad_ext_o = store_thm ("Gmonad_ext_o", tmeo,
  EVERY [ (SRW_TAC [] [EXTD_def]), 
    farwmmp GmD2, farwmmp catDAss ]) ;

val tmee = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (extNM = EXT (id, comp) (mapNM, joinNM))`` ;

val Gmonad_ext_jm = store_thm ("Gmonad_ext_jm", tmee,
  EVERY [ DISCH_TAC, farwmmp Gmonad_join,
    (SRW_TAC [] [EXTD_def, EXT_def]), 
    farwmmp catDRAss, farwmmp (GSYM GmD2), farwmmp catDLU ]) ;

val tmgc = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   Kmonad (id, comp) (unitNM, extNM)`` ;

val Gmonad_IMP_Kmonad = store_thm ("Gmonad_IMP_Kmonad", tmgc,
  EVERY [ DISCH_TAC,
    (FIRST_ASSUM (ASSUME_TAC o SYM o MATCH_MP Gmonad_ext_jm)),
    (SRW_TAC [] [Kmonad_def, EXTD_def]) ] 
  THENL [ 
    EVERY (map farwmmp [GSYM catDAss, GmD3, catDAss, GmD5, catDLU]),
    farwmmp GmD6, 
    EVERY (map farwmmp [GSYM catDAss, GmD2, catDAss, GmD7, GSYM catDAss])
    THEN EVERY [
     (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq [EXT_def]))),
     (ASM_REWRITE_TAC []), farwmmp GmD2,
     (FIRST_ASSUM (fn th => 
       CONV_TAC (DEPTH_CONV (REWR_CONV (MATCH_MP catDAss th))))),
     farwmmp (GSYM GmD4), farwmmp catDRAss,
     (ASM_REWRITE_TAC []) ]]) ;

val tmdm = ``category (id, comp) /\ Gmonad (id,comp) [:'N,'M:]
      (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\ 
   (extNM = EXTD (id, comp) (dmap, djoin)) ==> 
   (dmap = \:'a 'b. \ (f : ('a, 'b 'M) 'A).
     extNM [:'a, 'b:] (comp [:'a, 'b 'M, 'b 'N 'M:] (dunit [:'b:]) f))`` ;

val Gmonad_dmap = store_thm ("Gmonad_dmap", tmdm,
  EVERY [ DISCH_TAC, 
    (FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP Gmonad_ext_jm)),
    (FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [Kmonad_thm] o
      MATCH_MP Gmonad_IMP_Kmonad)),
    (POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o
      List.concat o map CONJUNCTS)),
    farwmmp (GSYM GmD3),
    (ASM_REWRITE_TAC [EXTD_def]), TY_BETA_TAC, BETA_TAC,
    farwmmp GmD2, farwmmp catDAss,
    farwmmp (GSYM GmD4), farwmmp catDRAss, 
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq [EXT_def]))),
    (ASM_REWRITE_TAC []), farwmmp catDRU,
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

(* inverse - compound monad gives Gmonad conditions *)

(* presumably there's a left-to-right element in parsing,
  deleting the first instance of Gmonad ... makes parsing fail,
  and I couldn't work out which annotations were needed to fix it *)

val tmginvx8 = ``
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==>
  category (id,comp) /\ Kmonad (id,comp) (unitNM,extNM) /\
  (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\ 
  (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
  (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) ==>
  (extNM = EXTD (id, comp) (dmap, djoin)) `` ;

val (_, tmginv8) = dest_imp tmginvx8 ;

val Kmonad_extD = store_thm ("Kmonad_extD", tmginv8,
  EVERY [ STRIP_TAC,
    (ASM_REWRITE_TAC [FUN_EQ_THM, TY_FUN_EQ_THM, EXTD_def]),
    TY_BETA_TAC, BETA_TAC, (REPEAT STRIP_TAC),
    (farwmmp KmonDAss), (farwmmp catDAss),
    (FIRST_X_ASSUM (fn th => 
      POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o TY_BETA_RULE o 
	REWRITE_RULE [test_lhs_head_var "djoin" th])))),
    (ASM_REWRITE_TAC []), (farwmmp catDLU)]) ;

val tmginvx = ``
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM ==>
  category (id,comp) /\ Kdmonad (id,comp) (unitNM,extNM,mapNM,joinNM) /\
  (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\ 
  (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
  (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
  (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) ==>
  Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM`` ;

val (_, tmginv) = dest_imp tmginvx ;

val Kmonad_IMP_Gmonad = store_thm ("Kmonad_IMP_Gmonad", tmginv,
  EVERY [ REWRITE_TAC [Kdmonad_thm], STRIP_TAC,
    (USE_LIM_RES_TAC (fn th => 
      REWRITE_TAC [Gmonad_thm, GSYM (fix_abs_eq [EXTD_def] th)]) Kmonad_extD),
    (REPEAT CONJ_TAC THEN REPEAT STRIP_TAC) ]
  THENL [
    EVERY [ (FIRST_ASSUM (fn th => MP_TAC (MATCH_MP KmonDLU th))), 
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      STRIP_TAC, (ASM_REWRITE_TAC [])],
    EVERY [ (FIRST_ASSUM (fn th => REWRITE_TAC [test_lhs_head_var "dmap" th])), 
      TY_BETA_TAC, BETA_TAC, (farwmmp catDAss),
      (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_extomap)],
    EVERY [ (FIRST_ASSUM (fn th => MP_TAC (MATCH_MP KmonDRU th))), 
      (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
      STRIP_TAC, (ASM_REWRITE_TAC [])],
    EVERY [ (ASM_REWRITE_TAC [JOINE_def]),
      TY_BETA_TAC, BETA_TAC, (farwmmp KmonDAss), (farwmmp catDRU)],
    (FIRST_ASSUM MATCH_ACCEPT_TAC),
    (farwmmp KmonDLU),
    EVERY [ (ASM_REWRITE_TAC [JOINE_def]),
      TY_BETA_TAC, (farwmmp KmonDAss), (farwmmp catDRU)]]) ;

val Kmonad_IMP_Gmonad' = REWRITE_RULE [Kdmonad_thm] Kmonad_IMP_Gmonad ;

val tmgiffk = ``category (id,comp) ==> 
  (Gmonad (id,comp) (dunit,dmap,djoin) (unitNM,mapNM,joinNM) unitM /\
    (extNM = EXTD (id,comp) (dmap,djoin)) = 
  Kdmonad (id,comp) (unitNM,extNM,mapNM,joinNM) /\ 
    (djoin = \:'a. extNM [:'a 'N, 'a:] (unitM [:'a 'N:])) /\
    (dmap = \:'a 'b. \ f. extNM [:'a, 'b:] (comp (dunit [:'b:]) f)) /\
    (unitNM = \:'a. comp (dunit [:'a:]) (unitM [:'a:])) /\
    (!:'a. comp (djoin [:'a:]) (dunit [:'a 'N:]) = id [:'a 'N 'M:]) )`` ;

val Gmonad_iff_Kmonad = store_thm ("Gmonad_iff_Kmonad", tmgiffk,
  EVERY [ REWRITE_TAC [Kdmonad_thm], STRIP_TAC,
    EQ_TAC, STRIP_TAC, (REPEAT CONJ_TAC) ] 
  THENL [ (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_IMP_Kmonad),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_map),
    (REWRITE_TAC [JOINE_def]) THEN 
      (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_join),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_djoin),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_dmap),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Gmonad_unit),
    (USE_LIM_RES_TAC ACCEPT_TAC GmD5), (* MATCH_ACCEPT_TAC fails !! *)
    (* inverse direction *)
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_IMP_Gmonad'),
    (USE_LIM_RES_TAC MATCH_ACCEPT_TAC Kmonad_extD) ]) ;

val tmgfn = 
  ``((id, comp) = (((\:'a. I), (\:'a 'b 'c. combin$o)) : fun category)) ==> 
  (umj_monad (unitN, mapN, joinN) = 
  Gmonad (id, comp) [:'N, I:] (unitN, mapN, joinN) (unitN, mapN, joinN) id)`` ;

val Gmonad_N_umj = store_thm ("Gmonad_N_umj", tmgfn,
  SRW_TAC [] [Gmonad_def, umj_monad_def]) ;

(* reverse implication *)
(* these don't work 
Q.INST [`extNM` |-> `dmap`] Kmonad_IMP_Gmonad ;
Q.INST_TYPE [`:'N` |-> `:I`] Kmonad_IMP_Gmonad ;
val th = Q.GEN `extNM` Kmonad_IMP_Gmonad ;
REWRITE_RULE [GSYM LEFT_EXISTS_IMP_THM] th ;
val thae = (snd o EQ_IMP_RULE o SPEC_ALL) LEFT_EXISTS_IMP_THM ;
HO_MATCH_MP thae th ;
*)

val gen_KG = GEN_ALL Kmonad_IMP_Gmonad' ;
val kgtacs = [ (MATCH_MP_TAC gen_KG),
  (Q.EXISTS_TAC `extM`), TY_BETA_TAC, 
  (FIRST_ASSUM (ASSUME_TAC o MATCH_MP KmonDLU)),
  (FIRST_ASSUM (ASSUME_TAC o MATCH_MP KmonDRU)),
  (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), 
  (ASM_REWRITE_TAC []),
  (* same problem here regarding eta-reduction of types,
  so require following two lines *)
  (REWRITE_TAC [Kmonad_thm]),
  (FIRST_X_ASSUM (ACCEPT_TAC o REWRITE_RULE [Kmonad_thm])) ] ;

val gktacsK = [
  (USE_LIM_RES_TAC MP_TAC (inst_eqs Gmonad_IMP_Kmonad)),
  (REWRITE_TAC [EXTD_def]),
  TY_BETA_TAC,
  (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)),
  STRIP_TAC,
  (* (ASM_REWRITE_TAC []) should work here, but problem with 
    recognising eta-equivalent types
    val (_, goal) = top_goal () ;
    val (lhs, rhs) = dest_eq goal ;
    val (rator, ty) = dest_tycomb lhs ;
    val ty1 = eta_conv_ty ty ;
    val ty2 = deep_eta_ty ty ;
    val ty3 = deep_beta_eta_ty ty ;
    *)
  (REWRITE_TAC [Kmonad_thm]),
  (FIRST_X_ASSUM (ACCEPT_TAC o REWRITE_RULE [Kmonad_thm])) ] ; 

val gktacsM = [ 
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th, EXTD_def])
    (inst_eqs Gmonad_map)),
  TY_BETA_TAC, (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ;

val gktacsJ = [
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th, JOINE_def, EXTD_def])
    (inst_eqs Gmonad_join)),
  TY_BETA_TAC, (ASM_REWRITE_TAC []),
  (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)), REFL_TAC ] ;

val tmgfm = ``category (id, comp) ==> 
  (Kdmonad (id, comp) (unitM, extM, mapM, joinM) =
    Gmonad (id, comp) [:I, 'M:] 
     ((\:'a. id [:'a 'M:]), extM, (\:'a. id [:'a 'M:])) 
      (unitM, mapM, joinM) unitM)`` ;

val Gmonad_M_Kdmonad = store_thm ("Gmonad_M_Kdmonad", tmgfm, 
  EVERY [ REWRITE_TAC [Kdmonad_thm], STRIP_TAC,
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDLU)),
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP catDRU)),
    EQ_TAC, STRIP_TAC ]
  THENL [ EVERY kgtacs, 
    (REPEAT CONJ_TAC) THENL [
      EVERY gktacsK, EVERY gktacsM, EVERY gktacsJ ] ]) ;

val _ = MATCH_MP Gmonad_iff_Kmonad categoryTheory.category_fun ;
val Gmonad_ext_jm' = inst_eqs Gmonad_ext_jm ;

val tmumjiffk = ``category (id,comp) ==> 
  (g_umj_monad (id,comp) (unit,map,join) /\ (ext = EXT (id,comp) (map,join)) = 
  Kdmonad (id,comp) (unit,ext,map,join))`` ;

val g_umj_iff_Kmonad = store_thm ("g_umj_iff_Kmonad", tmumjiffk,
  EVERY [ (REWRITE_TAC [g_umj_monad_thm, EXT_def]), STRIP_TAC,
    (* note how EXTD_def and EXT_def become the same here *)
    (FIRST_ASSUM ((fn th => REWRITE_TAC [REWRITE_RULE [EXTD_def] th]) o 
      MATCH_MP Gmonad_iff_Kmonad)),
    EQ_TAC, STRIP_TAC, REPEAT CONJ_TAC] 
  THENL [ (FIRST_ASSUM ACCEPT_TAC),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [TY_FUN_EQ_THM,
      MATCH_MP KdmonadD_JOINe th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [TY_FUN_EQ_THM, FUN_EQ_THM,
      MATCH_MP KdmonadD_MAPe th])),
    EVERY [(farwmmp catDRU),
      (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC],
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) Kdmonad_umj5) ]
  THEN EVERY [ TY_BETA_TAC, BETA_TAC, (REPEAT STRIP_TAC), REFL_TAC]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "Gmonad";

val _ = export_theory();

end; (* structure GmonadScript *)

