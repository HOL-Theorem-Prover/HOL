
(* proof of various results in Barr & Wells about distributive law for monads,
  and in Jones & Duponcheel re prod, dorp, swap constructions *)

structure dist_monadsScript =
struct

open HolKernel Parse boolLib
     bossLib

open categoryTheory KmonadTheory ;
open auxLib ;
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

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

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

