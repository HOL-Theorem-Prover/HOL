
(* $Id$ *)

(* proof of various results in Barr & Wells about distributive law for monads,
  and in Jones & Duponcheel re prod, dorp, swap constructions *)

structure dist_monadsScript =
struct

open HolKernel Parse boolLib
     bossLib

open categoryTheory KmonadTheory GmonadTheory ;
open auxLib ; infix RS RSN ;
(*
load "auxLib" ;
load "dist_monadsTheory" ; open dist_monadsTheory ;
fun sge tm = set_goal ([], tm) ;
fun eev tacs = e (EVERY tacs) ;
fun eall [] = () 
  | eall (t :: ts) = (e t ; eall ts) ;
*)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "dist_monads";

(* given monad N in the Kleisli category of monad M,
  prove Jones & Duponcheel results about prod, where prod = pext id *)

val tm_Kcm_P2 = ``category (id, comp) /\ 
  Kmonad [:'A:] (id,comp) (unitM, extM : ('A, 'M) ext) ==> 
  Kmonad [: ('A, 'M) Kleisli, 'N :] 
    (unitM, Kcomp (id,comp) extM) (unitNM, pext) ==>
  (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==>
  (comp (pext id) unitN = id)`` ;

val Kcm_P2 = store_thm ("Kcm_P2", tm_Kcm_P2,
  EVERY [ (REWRITE_TAC [Kcomp_def]), (REPEAT STRIP_TAC),
   (FIRST_ASSUM (MP_TAC o MATCH_MP KmonDRU)),
   (ASM_REWRITE_TAC []), TY_BETA_TAC, BETA_TAC,
   (farwmmp catDAss), (frrc_rewr KmonDRU),
   STRIP_TAC, (FIRST_ASSUM MATCH_ACCEPT_TAC)]) ;
    
val Kcm_P3 = store_thm ("Kcm_P3",
  ``Kmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext) ==>
    (pext (unitNM [:'a:]) = unitM [:'a 'N:])``,
  EVERY [ (REWRITE_TAC [Kcomp_def]), STRIP_TAC,
   (FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP KmonDLU)),
   (ASM_REWRITE_TAC []) ]) ;

val tm_Kom_P14e = 
  ``category (id, comp) ==> Komonad (id,comp) (unitM,extM,kcomp) ==>
    Komonad [: ('A, 'M) Kleisli, 'N :] (unitM, kcomp) (unitNM, pext, oNM) ==>
    (extNM = (\:'a 'b. (\f. extM (pext [:'a, 'b:] f)))) ==>
    (pext (comp (extNM f) g) = comp (extNM f) (pext g))`` ;

val Kom_P14e = store_thm ("Kom_P14e", tm_Kom_P14e,
  EVERY [ REPEAT STRIP_TAC, (frrc_rewr Ko_cmD_pext),
    TY_BETA_TAC, BETA_TAC,
    (USE_LIM_RES_TAC ASSUME_TAC Ko_cmD_cm),
    (farwmmp catDAss), (frrc_rewr (KomonadDK RS KmonDAss)) ]) ;

(* note, KomonadI RSN (3, Kom_P14e) fails because 
   Komonad (unitM, kcomp) (unitNM, pext, oNM)
   has the type of the Kleisli category, and so types of KomonadI
   would need to be instantiated *)

(* note, to get Jones & Duponcheel P1 to P4,
  have yet to show / assume (these are equivalent)
  mapNM = mapM o mapN
  pext (comp g f) = comp (pext g) (mapN f) 
  kmap (comp g f) = comp (kmap g) (mapN f) 
  *)
  
val Kdmonad_umj1' = TY_GEN_ALL (GEN_ALL Kdmonad_umj1) ;
val Kdmonad_umj1'' = DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH Kdmonad_umj1))) ;
val Kdmonad_umj1_r = reo_prems rev Kdmonad_umj1 ;
val Kdmonad_umj2_r = reo_prems rev Kdmonad_umj2 ;
val Kdmonad_umj3_r = reo_prems rev Kdmonad_umj3 ;

(* given monad N in the Kleisli category of monad M,
  prove Jones & Duponcheel results about swap, where swap = kmap id,
  and similar Barr & Wells results *)

(* JD S3 is also BW D1 *)
val tm_Kcm_S3 = 
  ``category (id, comp) /\ Kmonad [:'A, 'M:] (id,comp) (unitM, extM) ==> 
    Kdmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (kmap (unitM [:'a:]) = unitM [:'a 'N:])`` ;

val Kcm_S3 = store_thm ("Kcm_S3", tm_Kcm_S3,
  EVERY [ (REPEAT STRIP_TAC),
    (USE_LIM_RES_TAC ASSUME_TAC Kmonad_IMP_Kcat),
    (*
      (frrc_rewr Kdmonad_umj1') fails - BUG ?
      (frrc_rewr Kdmonad_umj1) fails - BUG ?
      also (frrc_rewr Kdmonad_umj1_r) works
      *)
    (frrc_rewr Kdmonad_umj1'') ]) ;

(* before the last tactic, ie, before (frrc_rewr Kdmonad_umj1''), do:
e (POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)) ;
e (POP_ASSUM (fn _ => ALL_TAC)) ;
val (sgs, goal) = top_goal () ;
val [_, _, cat] = map ASSUME sgs ;
val A = MATCH_MP Kdmonad_umj1'' cat ; 
val B = MATCH_MP Kdmonad_umj1' cat ; 
val C = MATCH_MP Kdmonad_umj1 cat ; 
shouldn't B have two type quantifiers, as does A ?
If removing the quantifiers is intended, still the types seem wrong,
because in A there are distinct types 'M and 'N,
which have become identified in A -
see, eg, the type argument of Kdmonad,
which is [:λα β. (α, β 'M) 'A, 'N:]in A,
but is [:λα β. (α, β 'M) 'A, 'M:] in B
Also look at C - similar to B ;
note that TY_GEN_ALL (GEN_ALL C) has one type quantifier
*)

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

(* JD S2 is also BW D2 *)
val tm_Kcm_S2 = ``category (id, comp) /\
    Kdmonad [:'A, 'M:] (id,comp) (unitM, extM, mapM, joinM) ==> 
    Kdmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==> 
    (comp (kmap (id [:'a 'M:])) (unitN [:'a 'M:]) = mapM unitN)`` ;

val Kdmonad_IMP_Kcat = (KdmonadDK RSN (2, Kmonad_IMP_Kcat)) ;
val Kcomp_thm' = SPEC_ALL (TY_SPEC_ALL (SPEC_ALL Kcomp_thm)) ;
val Kcomp_thm'' = (TY_GEN_ALL (GEN_ALL Kcomp_thm')) ; 

val Kcm_S2 = store_thm ("Kcm_S2", tm_Kcm_S2,
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kdmonad_IMP_Kcat),
    (FIRST_REP_RES (MP_TAC o TY_GEN_ALL o REWRITE_RULE [Kcomp_thm'])
      Kdmonad_umj3_r),
    (ASM_REWRITE_TAC []), TY_BETA_TAC, (farwmmp catDAss),
    (POP_ASSUM (fn _ => ALL_TAC)),
    (POP_ASSUM (fn _ => ALL_TAC)),
    (POP_ASSUM (fn _ => ALL_TAC)),
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP KdmonadDK)),
    (farwmmp KmonDRU), STRIP_TAC, (ASM_REWRITE_TAC []),
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) Kdmonad_extomap),
    (farwmmp KmonDLU), (farwmmp catDLU), (farwmmp catDRU) ]) ; 

val tm_Kcm_BWD3 = ``category (id, comp) /\
    Kdmonad [:'A, 'M:] (id,comp) (unitM, extM, mapM, joinM) ==> 
    Kdmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (kmap joinM = comp (extM (kmap id)) (kmap id))`` ;

val Kcm_BWD3 = store_thm ("Kcm_BWD3", tm_Kcm_BWD3,
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kdmonad_IMP_Kcat),
    (FIRST_REP_RES (ASSUME_TAC o TY_GEN_ALL o 
      GSYM o REWRITE_RULE [Kcomp_thm']) Kdmonad_umj2_r),
    (ASM_REWRITE_TAC []), (farwmmp catDRU),
    (frrc_rewr KdmonadD_JOINe) ]) ;

(* with f = id, this is pext dorp = swap o_NM swap *)
val tm_Kcm_S4_ss = ``category (id, comp) /\
    Kmonad [:'A, 'M:] (id,comp) (unitM, extM) ==>
    Kdmonad [: ('A, 'M) Kleisli, 'N :]
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (pext (extM (kmap f)) = comp (extM (pext (kmap f))) (kmap id))`` ;

val Kcm_S4_ss = store_thm ("Kcm_S4_ss", tm_Kcm_S4_ss,
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kmonad_IMP_Kcat),
   (USE_LIM_RES_TAC (fn th => REWRITE_TAC 
     [REWRITE_RULE [Kcomp_thm'] (GSYM th)]) Kdmonad_extomap),
   (farwmmp catDRU) ]) ;

(* with f = g = id, this is swap o_NM swap = dorp o prod *)
val tm_Kcm_S4_ss' = ``category (id, comp) /\
    Kmonad [:'A, 'M:] (id,comp) (unitM, extM) ==>
    Kdmonad [: ('A, 'M) Kleisli, 'N :]
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (comp (extM (pext (kmap f))) (kmap g) =
      comp (extM (kmap f)) (pext g))`` ;

val Kcm_S4_ss' = store_thm ("Kcm_S4_ss'", tm_Kcm_S4_ss',
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kmonad_IMP_Kcat),
    (USE_LIM_RES_TAC (fn th => REWRITE_TAC [Kcomp_thm', th]) Kdmonad_umj4),
    (farwmmp KmonDRAss), (farwmmp catDRAss),
    AP_TERM_TAC, (farwmmp KdmonadD_JOIN_SYM), 
    (USE_LIM_RES_TAC ((fn th => REWRITE_TAC [REWRITE_RULE [Kcomp_thm'] th]))
      KdmonadD_EXT_SYM) ]) ;

(* with g = id, this is swap o_M kjoin = kjoin o_M kmap swap *)
val tm_Kcm_BWD4_alt = ``category (id, comp) /\
    Kmonad [:'A, 'M:] (id,comp) (unitM, extM) ==> 
    Kdmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (comp (extM (kmap g)) kjoin = comp (extM kjoin) (kmap (kmap g)))`` ;

val Kcm_BWD4_alt = store_thm ("Kcm_BWD4_alt", tm_Kcm_BWD4_alt,
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kmonad_IMP_Kcat),
    (USE_LIM_RES_TAC ((fn th => REWRITE_TAC [th]) o
      REWRITE_RULE [Kcomp_thm']) KdmonadD_EXT_SYM),
    (frrc_rewr Kdmonad_umj4), (frrc_rewr KdmonadD_JOINe),
    (REWRITE_TAC [Kcomp_thm]), (* fails - why ? - BUG ? *)
    (REWRITE_TAC [Kcomp_thm']) (* succeeds *)
    (* Note, (REWRITE_TAC [Kcomp_thm'']) also succeeds *)
    ]) ;

val tm_Kcm_S1 = ``category (id, comp) /\
    Kdmonad [:'A, 'M:] (id,comp) (unitM, extM, mapM, joinM) ==> 
    Kdmonad [: ('A, 'M) Kleisli, 'N :] 
      (unitM, Kcomp (id,comp) extM) (unitNM, pext, kmap, kjoin) ==>
    (extNM = (\:'a 'b. (\f. extM (pext [:'a, 'b:] f)))) ==>
    (kmap (mapM f) = comp (extNM (comp unitNM f)) (kmap id))`` ;

val Kcm_S1 = store_thm ("Kcm_S1", tm_Kcm_S1,
  EVERY [ (REPEAT STRIP_TAC), (USE_LIM_RES_TAC ASSUME_TAC Kdmonad_IMP_Kcat),
    (FIRST_REP_RES (fn th => ASM_REWRITE_TAC 
      [MAPE_def, test_lhs_head_var "mapM" th]) KdmonadD_MAPe),
    TY_BETA_TAC, BETA_TAC, 
    (POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)),
    (FIRST_ASSUM (fn th => 
      (CONV_TAC o RATOR_CONV o RAND_CONV o RAND_CONV o REWR_CONV) 
      (MATCH_MP (GSYM catDRU) th))),
    (FIRST_REP_RES (fn th => CHANGED_TAC 
      (REWRITE_TAC [REWRITE_RULE [Kcomp_thm'] th])) Kdmonad_umj2_r),
    AP_THM_TAC, AP_TERM_TAC, AP_TERM_TAC,
    (farwmmp KdmonadD_MAPe), (REWRITE_TAC [Kcomp_thm']), 
    (farwmmp catDAss), (farwmmp (KdmonadDK RS KmonDRU)) ]) ;

val KdmonDRU = (KdmonadDK RS KmonDRU) ; 
val Kdo_mon = (KdomonadDKd RS KdmonadDK) ;
val KdomonDRU = (Kdo_omonadD RS KomonDRU) ;
  
(* showing how JD S1 to S4 give the BW D1 to D4 and swap is nt ;
  have that S2 is BWD2, S3 is BWD1, S1 is swap is nt ;
  need to show 
*)

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

(* conditions S1 to S4 for monads, as in Jones & Duponcheel *)

val S1to4_def = Define `S1to4 = 
    (\: 'A 'N 'M. \ ((id, comp) : 'A category)
    ((unitM, extM, mapM, joinM) : ('A, 'M) Kdmonad)
    ((unitN, mapN, joinN) : ('A, 'N) g_umj_monad)
    (swap : (! 'a. ('a 'M 'N, 'a 'N 'M) 'A)).
    
    (* S1 ; swap nt *) (!: 'a 'b. ! (f : ('a, 'b) 'A).
      comp ((swap : (! 'a. ('a 'M 'N, 'a 'N 'M) 'A)) [:'b:]) (mapN (mapM f)) =
      comp (mapM (mapN f)) (swap [:'a:])) /\
    (* S2 ; BWD2 *) (!: 'a. comp (swap [:'a:]) unitN = mapM unitN) /\
    (* S3 ; BWD1 *) (!: 'a. comp (swap [:'a:]) (mapN unitM) = unitM) /\
    (* S4 *) (let (prod : (! 'a. ('a 'N 'M 'N, 'a 'N 'M) 'A)) =
        \:'a. comp (mapM (joinN [:'a:])) (swap [:'a 'N:]) in
      (!: 'a. comp (prod [:'a:]) (mapN (extM (swap [:'a:]))) = 
        comp (extM (swap [:'a:])) (prod [:'a 'M:]))))` ;

val S1to4_thm = save_thm ("S1to4_thm",
  SPEC_ALL (TY_SPEC_ALL (mk_exp_thm'' S1to4_def))) ; 
val (S1to4D, S1to4I) = EQ_IMP_RULE S1to4_thm ;
val [S_1, S_2, S_3, S_4] = map DISCH_ALL (CONJUNCTS (UNDISCH S1to4D)) ;
val _ = ListPair.map save_thm (["S_1","S_2","S_3","S_4"], [S_1,S_2,S_3,S_4]) ;

(* distributive law for monads, as in Barr & Wells *)

val dist_law_def = Define `dist_law = 
    (\: 'A 'N 'M. \ ((id, comp) : 'A category)
    ((unitM, extM, mapM, joinM) : ('A, 'M) Kdmonad)
    ((unitN, mapN, joinN) : ('A, 'N) g_umj_monad)
    (swap : (! 'a. ('a 'M 'N, 'a 'N 'M) 'A)).
    (* S1 ; swap nt *) (!: 'a 'b. ! (f : ('a, 'b) 'A).
      comp ((swap : (! 'a. ('a 'M 'N, 'a 'N 'M) 'A)) [:'b:]) (mapN (mapM f)) =
      comp (mapM (mapN f)) (swap [:'a:])) /\
    (* S2 ; BWD2 *) (!: 'a. comp (swap [:'a:]) unitN = mapM unitN) /\
    (* S3 ; BWD1 *) (!: 'a. comp (swap [:'a:]) (mapN unitM) = unitM) /\
    (* BWD3 *) (!: 'a. comp (swap [:'a:]) (mapN joinM) =
      comp (extM (swap [:'a:])) (swap [:'a 'M:])) /\
    (* BWD4 *) (!: 'a. comp (swap [:'a:]) joinN = 
      comp (mapM joinN) (comp (swap [:'a 'N:]) (mapN (swap [:'a:])))))` ;

val dist_law_thm = save_thm ("dist_law_thm",
  SPEC_ALL (TY_SPEC_ALL (mk_exp_thm'' dist_law_def))) ; 
val (dist_lawD, dist_lawI) = EQ_IMP_RULE dist_law_thm ;
val [dlDnt, dlD1, dlD2, dlD3, dlD4] = 
  map DISCH_ALL (CONJUNCTS (UNDISCH dist_lawD)) ;
val _ = ListPair.map save_thm (["dlDnt", "dlD1", "dlD2", "dlD3", "dlD4"],
  [dlDnt, dlD1, dlD2, dlD3, dlD4]) ;

(* converse - assume swap is nt, and BW D1 to D4, show how to 
  define a compound monad satisfying J1 and J2 *)
val tmBWD_cm' = ``category (id, comp) ==>
    Kdmonad [:'A, 'M:] (id,comp) (unitM, extM, mapM, joinM) ==> 
    Kdomonad [:'A, 'M:] (id,comp) (unitM, extM, kcomp, mapM, joinM) ==> 
    g_umj_monad [:'A, 'N:] (id,comp) (unitN, mapN, joinN) ==> 
    dist_law (id,comp) (unitM,extM,mapM,joinM) (unitN,mapN,joinN) swap ==>
    (kjoin = \:'a. comp unitM (joinN [:'a:])) ==>
    (kmap = \:'a 'b. \f. comp swap (mapN [:'a, 'b 'M:] f)) ==>
    (unitNM = \:'a. comp (unitM [:'a 'N:]) (unitN [:'a:])) ==>
    (pext = \:'a 'b. \f. kcomp kjoin (kmap [:'a, 'b 'N:] f)) ==>
    (pext [:'a,'c:] (comp g f) = 
      comp (pext [:'b,'c:] g) (mapN [:'a,'b:] f)) ==>
    (!: 'a 'b 'c. !g f. pext [:'a,'c:] (comp g f) = 
      comp (pext [:'b,'c:] g) (mapN [:'a,'b:] f)) ==>
  g_umj_monad [:('A,'M) Kleisli, 'N:] (unitM, kcomp) (unitNM, kmap, kjoin) ==>
  S1to4 (id,comp) (unitM,extM,mapM,joinM) (unitN,mapN,joinN) swap ==> 
  Kdmonad [:('A,'M) Kleisli, 'N:] (unitM,kcomp) (unitNM,pext,kmap,kjoin) ==>
  (extM (pext unitM) = mapM joinN) ==> 
  (extM (pext (comp unitNM f)) = mapM (mapN f)) ==> 
    (* S4 o extra *) (let (prod : (! 'a. ('a 'N 'M 'N, 'a 'N 'M) 'A)) =
        \:'a. comp (mapM (joinN [:'a:])) (swap [:'a 'N:]) in
      (!: 'a. comp (comp (prod [:'a:]) (mapN (extM (swap [:'a:])))) 
	  (mapN (unitM [:'a 'M 'N:])) = 
        comp (comp (extM (swap [:'a:])) (prod [:'a 'M:]))
	  (mapN (unitM [:'a 'M 'N:]))) /\
      (!: 'a. comp (comp (prod [:'a:]) (mapN (extM (swap [:'a:])))) 
	  (mapN (mapM (unitN [:'a 'M:]))) = 
        comp (comp (extM (swap [:'a:])) (prod [:'a 'M:]))
	  (mapN (mapM (unitN [:'a 'M:])))) )`` ;
  
val ([cic, KdmonM, KdomonM, umjN, dl, kjoin, kmap, unitNM,
  pext, pc', pc, umjK, S14, KdK, J2, meq], S4os) = strip_imp tmBWD_cm' ;

val tm_S_IMP_DL = list_mk_imp ([cic, KdmonM, umjN, S14], dl) ;
val tm_DL_IMP_S = list_mk_imp ([cic, KdmonM, umjN, dl], S14) ;
val tm_S_IFF_DL = list_mk_imp ([cic, KdmonM, umjN], mk_eq (S14, dl)) ;
(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val S_IMP_DL = store_thm ("S_IMP_DL", tm_S_IMP_DL,
  EVERY [ (REWRITE_TAC [S1to4_thm, dist_law_thm, LET_THM]),
    BETA_TAC, TY_BETA_TAC, 
    (REPEAT (DISCH_THEN STRIP_ASSUME_TAC)),
    (SUBGOAL_THEN S4os MP_TAC) ]

  THENL [
    EVERY [ (REWRITE_TAC [LET_THM]),
      BETA_TAC, TY_BETA_TAC, (ASM_REWRITE_TAC []) ],

    EVERY [ (POP_ASSUM (fn _ => ALL_TAC)),
      (ASM_REWRITE_TAC [LET_THM]), BETA_TAC, TY_BETA_TAC,

      (* first one ie BWD4 *)
      (farwmmp catDRAss), (farwmmp (GSYM g_umjD2)),
      (farwmmp KdmonDRU), (ASM_REWRITE_TAC []),
      (frrc_rewr Kdmonad_umj3_r), (farwmmp catDAss), (farwmmp KdmonDRU),
      (* second one ie BWD3, some already done *)
      (FIRST_ASSUM (CONV_TAC o CHANGED_CONV o
	DEPTH_CONV o REWR_CONV o MATCH_MP catDRAss)),
      (frrc_rewr (GSYM Kdmonad_umj2_r)), (farwmmp g_umjD6),
      (frrc_rewr Kdmonad_umj1_r), (farwmmp catDLU),
      (frrc_rewr (GSYM Kdmonad_extomap)), (ASM_REWRITE_TAC []),
      (frrc_rewr Kdmonad_umj4), (farwmmp g_umjD2),
      (FIRST_ASSUM (CONV_TAC o CHANGED_CONV o
	DEPTH_CONV o REWR_CONV o MATCH_MP catDAss)),
      (ASM_REWRITE_TAC []), (farwmmp catDAss),
      (frrc_rewr (GSYM Kdmonad_umj2_r)), (farwmmp g_umjD6),
      (frrc_rewr Kdmonad_umj1_r), (farwmmp catDLU),
      (farwmmp KdmonadD_JOINe), (SRW_TAC [] []) ] ]) ;

(* lemma to help rewriting deep inside a term *)
val tmrl' = ``category (id,comp) ==> 
  ((comp [:'b,'c,'d:] x y = w) = 
  (!: 'a. !z. comp [:'a,'c,'d:] x (comp [:'a,'b,'c:] y z) = comp w z)) ==>
  (comp [:'b,'c,'d:] x (comp y (id [:'b:])) = comp w (id [:'b:]))`` ;

val ([cat, eq], xyiwi) = strip_imp tmrl' ;

val rewr_o_lem = store_thm ("rewr_o_lem", (mk_imp (cat, eq)),
  STRIP_TAC THEN EQ_TAC
  THENL [ (farwmmp catDAss) THEN (SRW_TAC [] []),
    DISCH_TAC THEN (SUBGOAL_THEN xyiwi MP_TAC)
    THENL [ (FIRST_ASSUM MATCH_ACCEPT_TAC), (farwmmp catDRU) ] ]) ;

val rewr_o_lem_gen = DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH rewr_o_lem))) ;

val KdmonadD_EXTe = (fix_abs_eq [EXT_def] KdmonadD_EXT) ;

fun userl rl = 
  let val conv = ONCE_DEPTH_CONV (REWR_CONV rl) ;
  in ASSUM_LIST (MAP_EVERY (ASSUME_TAC o CONV_RULE conv)) end ;

fun userl2 rl = 
  let 
    val conv = ONCE_DEPTH_CONV (REWR_CONV rl) ;
    val g2 = CONV_RULE conv (GSYM Kdmonad_umj2) ;
    (* shouldn't need this for rewriting to work - BUG! *)
    val g2' = ufd (TY_GEN_ALL o GEN_ALL o SPEC_ALL o
      TY_SPEC_ALL o SPEC_ALL) g2 ;
  in (frrc_rewr g2') end ;

val DL_IMP_S = prove (tm_DL_IMP_S,
  EVERY [ (REWRITE_TAC [S1to4_thm, dist_law_thm, LET_THM]),
    BETA_TAC, TY_BETA_TAC, 
    (REPEAT (DISCH_THEN STRIP_ASSUME_TAC)),
    (REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC)),
    (* now only S(4) remains to be proved *)
    (frrc_rewr KdmonadD_EXTe), (farwmmp g_umjD2), 
    (* convert all equalities in the assumptions *)
    (FIRST_ASSUM (userl o MATCH_MP rewr_o_lem)),
    (farwmmp catDRAss),
    (* substitute for BWD3 *)
    (FIRST_X_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [th]))),
    (* deal with (mapM swap) o (mapM joinN) *)
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP rewr_o_lem_gen)),
    (POP_ASSUM userl2),
    (* substitute for BWD4 *)
    (FIRST_X_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [th]))),
    (frrc_rewr Kdmonad_umj2), (frrc_rewr KdmonadD_EXTe), (farwmmp catDAss),
    (FIRST_REP_RES (fn umj4 => 
      (FIRST_REP_RES (fn ext => REWRITE_TAC [REWRITE_RULE [ext] umj4]) 
        KdmonadD_EXTe)) Kdmonad_umj4),
    (frrc_rewr Kdmonad_umj1), (farwmmp catDRU), (farwmmp catDRAss),
    STRIP_TAC, REPEAT AP_TERM_TAC, (FIRST_ASSUM MATCH_ACCEPT_TAC) ]) ;
      
val S_IFF_DL = store_thm ("S_IFF_DL", tm_S_IFF_DL,
  EVERY [REPEAT STRIP_TAC, EQ_TAC, STRIP_TAC]
  THENL [ FIRST_REP_RES ACCEPT_TAC S_IMP_DL,
    FIRST_REP_RES ACCEPT_TAC DL_IMP_S]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val tmBWD_cm = list_mk_imp
  ([cic, KdomonM, umjN, dl, kjoin, kmap, unitNM], umjK) ;
val tmBWD_cmK = list_mk_imp
  ([cic, KdomonM, umjN, dl, kjoin, kmap, unitNM, pext], KdK) ;
val tmBWD_cmKJ = list_mk_imp
  ([cic, KdomonM, umjN, dl, kjoin, kmap, unitNM, pext],
    mk_conj (KdK, J2)) ;
val tmBWD_cmKM = list_mk_imp
  ([cic, KdomonM, umjN, kmap, unitNM, pext, KdK], meq) ;
val tmBWD_cmKJM = list_mk_imp
  ([cic, KdomonM, umjN, kjoin, kmap, unitNM, pext, KdK], 
    mk_conj (J2, meq)) ;

(* note also, extM kjoin = mapM joinN, ie, J2 holds,
   def'n of pext, and Kdmonad result omitted above is 
    (pext = \:'a 'b. \f. kcomp kjoin (kmap [:'a, 'b 'N:] f)) ==>
  Kdmonad [:('A,'M) Kleisli, 'N:] (unitM, kcomp) (unitNM, pext, kmap, kjoin)`` ;
*)

val ktacs2 = [
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KdmonadD_EXTe),
  (farwmmp g_umjD2), (farwmmp catDAss), (farwmmp dlD3),
  (REPEAT STRIP_TAC), AP_THM_TAC, AP_TERM_TAC,
  (farwmmp catDRAss), (farwmmp dlDnt), (farwmmp catDAss),
  AP_THM_TAC, AP_TERM_TAC,
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) Kdmonad_umj2),
  (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) KdmonadD_EXTe),
  (farwmmp catDAss)] ;

val ktacs3 = [ 
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (farwmmp catDAss), (farwmmp KdomonDRU), 
  (farwmmp catDRAss), (farwmmp g_umjD3),
  (farwmmp catDAss), (farwmmp dlD1), (farwmmp KdmonadD_MAPe)] ;

val ktacs4 = [ 
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (farwmmp catDAss), (farwmmp KdomonDRU),
  (farwmmp catDRAss), (farwmmp g_umjD4),
  (farwmmp catDAss), (farwmmp dlD4),
  (farwmmp g_umjD2), (farwmmp catDAss), (farwmmp KdmonadD_MAPe)] ;

val ktacs5 = [ 
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (farwmmp catDAss), (farwmmp KdomonDRU),
  (farwmmp catDRAss), (farwmmp g_umjD5), (farwmmp catDRU)] ;

val ktacs6 = [ (farwmmp g_umjD2), (farwmmp catDAss), (farwmmp dlD2),
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (farwmmp catDAss), (farwmmp KdomonDRU),
  (farwmmp catDRAss), (farwmmp g_umjD6), (farwmmp catDRU)] ;

val ktacs7 = [ (farwmmp g_umjD2), (farwmmp catDAss), (farwmmp dlD2),
  (FIRST_REP_RES (fn th => REWRITE_TAC [Kcomp_thm', th]) KdomonadD_Kcomp),
  (farwmmp catDAss), (farwmmp KdomonDRU),
  (farwmmp catDRAss), (farwmmp g_umjD7)] ;

val BWD_cm = store_thm ("BWD_cm", tmBWD_cm, 
  EVERY [ REPEAT STRIP_TAC,
    (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o fix_abs_eq []))),
    ASM_REWRITE_TAC [g_umj_monad_exp], 
    (FIRST_REP_RES ASSUME_TAC KdomonadDKd),
    REPEAT CONJ_TAC]
  THENL (farwmmp dlD2 :: map EVERY 
    [ ktacs2, ktacs3, ktacs4, ktacs5, ktacs6, ktacs7]) ) ;

val g_umj_imp_Kdomonad = ufd (fst o EQ_IMP_RULE) g_umj_iff_Kdomonad ;
val gkd1 = (g_umj_imp_Kdomonad RSN (2, KdomonadDKd)) ;

val gkd2 = (REWRITE_RULE [GSYM AND_IMP_INTRO] (reo_prems tl gkd1)) ; 
val [es, kcs] = eq_subs gkd2 ;
val gkd3 = REWRITE_RULE [] (INST [kcs] gkd2) ;
val g_umj_imp_Kdmonad = fix_abs_eq [EXT_def] gkd3 ;

val BWD_cmK = store_thm ("BWD_cmK", tmBWD_cmK, 
  EVERY [ REPEAT STRIP_TAC,
    (USE_LIM_RES_TAC ASSUME_TAC BWD_cm),
    (USE_LIM_RES_TAC ASSUME_TAC (Kdo_omonadD RSN (2, Komonad_IMP_Kcat))),
    (USE_LIM_RES_TAC MATCH_MP_TAC g_umj_imp_Kdmonad),
    (ASM_REWRITE_TAC []), (CONV_TAC (fix_abs_eq_conv [])),
    REPEAT STRIP_TAC, REFL_TAC ]) ;

val BWD_cmKJM = store_thm ("BWD_cmKJM", tmBWD_cmKJM,
  REPEAT STRIP_TAC 
  THENL [
    EVERY [ (farwmmp KdmonadD_JOIN_SYM), (ASM_REWRITE_TAC []), TY_BETA_TAC, 
    (FIRST_REP_RES MATCH_ACCEPT_TAC (KdomonadDKd RS KdmonadD_MAP_SYM))],
    (SUBGOAL_THEN pc (fn th => REWRITE_TAC [th]))
    THENL [
      EVERY [ (ASM_REWRITE_TAC []),
	(frrc_rewr KdomonadD_Kcomp), (REWRITE_TAC [Kcomp_def]),
	TY_BETA_TAC, BETA_TAC, (farwmmp g_umjD2), (farwmmp catDAss) ],
      (farwmmp (KdmonadDK RS KmonDLU)) THEN
	(frrc_rewr (KdomonadDKd RS KdmonadD_MAP_SYM)) ] ]) ;

(* now need to combine this with Ko_pext_cm to get that NM is a monad *)

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
  val _ = html_theory "dist_monads";

val _ = export_theory();

end; (* structure dist_monadsScript *)

