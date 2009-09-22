
structure xmonadScript =
struct

open HolKernel Parse boolLib
     bossLib

open combinTheory functorTheory

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "xmonad";


(*
val _ = loadPath := "/home/users/jeremy/myholw/gen" :: !loadPath ;
val _ = loadPath := 
  "/home/users/jeremy/hol-omega/examples/HolOmega" :: !loadPath ;
load "functorTheory" ; 
load "monadTheory" ; 
*)

open HolKernel Parse boolLib
     bossLib ;

open combinTheory functorTheory monadTheory ;

val BIND_THM_alt = TAC_PROOF(([],
   ``(!(unit:'M unit) (bind:'M bind).
      monad(unit, bind) ==>
      !:'a 'b. !(m:'a 'M) (k:'a -> 'b 'M).
      bind [:'a,'b:] m k = JOIN (unit,bind) (MMAP (unit,bind) k m))``),
   SRW_TAC[][monad_def,FUN_EQ_THM,JOIN_def,MMAP_def,ETA_AX]
  );

val umj_monad_IMP_map_eq = store_thm ("umj_monad_IMP_map_eq",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==> (map = MMAP (unit, BIND (map, join)))``,
  EVERY [
    (REWRITE_TAC [MMAP_def, BIND_def, umj_monad_def, o_DEF, FUN_EQ_THM]),
    (CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)),
    (SRW_TAC [] []),
    (CONV_TAC (TOP_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (TOP_DEPTH_CONV TY_ETA_CONV)),
    REFL_TAC]) ;

val umj_monad_IMP_join_eq = store_thm ("umj_monad_IMP_join_eq",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==>
     (join = JOIN (unit, BIND (map, join)))``,
  EVERY [
    (REWRITE_TAC [JOIN_def, BIND_def, umj_monad_def, o_DEF, FUN_EQ_THM]),
    (SRW_TAC [] []),
    (CONV_TAC (TOP_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (TOP_DEPTH_CONV TY_ETA_CONV)),
    REFL_TAC]) ;

val umj_monad_IMP_monad_full = store_thm ("umj_monad_IMP_monad_full",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
     umj_monad(unit,map,join) ==>
     monad (unit,BIND (map,join)) /\ 
     (map = MMAP (unit, BIND (map, join))) /\ 
     (join = JOIN (unit, BIND (map, join)))``, 
  ((SRW_TAC [] []) THENL [
      (MATCH_MP_TAC umj_monad_IMP_monad),
      (MATCH_MP_TAC umj_monad_IMP_map_eq),
      (MATCH_MP_TAC umj_monad_IMP_join_eq)] 
    THEN (POP_ASSUM ACCEPT_TAC))) ;

val (monad_IMP_umj_monad', _) = EQ_IMP_RULE
  (SPEC_ALL (TY_SPEC_ALL monad_EQ_umj_monad)) ;

val monad_IMP_umj_monad = save_thm
  ("monad_IMP_umj_monad", TY_GEN_ALL (GEN_ALL monad_IMP_umj_monad')) ;

(* both umj_monad_IMP_monad_full and monad_IMP_umj_monad can be made 
  equivalences, by each other *)

(* inverse direction of monad_EQ_umj_monad from umj_monad_IMP_monad_full *)
fun ma th = SYM th handle _ => MATCH_MP umj_monad_IMP_monad_full th ; 

val monad_EQ_umj_monad_bis = store_thm ("monad_EQ_umj_monad_bis",
  ``!:'M:ar 1. !unit bind. monad (unit,bind) <=>
    umj_monad (unit,MMAP (unit,bind),JOIN (unit,bind)) /\
    (bind = BIND (MMAP (unit,bind),JOIN (unit,bind)))``,
  (EVERY [(SRW_TAC [] []), EQ_TAC] THENL 
    [ (MATCH_ACCEPT_TAC monad_IMP_umj_monad),
      EVERY [ (SRW_TAC [] []), (RULE_ASSUM_TAC ma),
      (FIRST_ASSUM (fn th => (SYM th ; SUBST_ALL_TAC th))),
      (SRW_TAC [] [])] ])) ;

(* prove inverse direction of umj_monad_EQ_monad from monad_IMP_umj_monad *)
fun mb th = SYM th handle _ => MATCH_MP monad_IMP_umj_monad th ; 

val umj_monad_EQ_monad = store_thm ("umj_monad_EQ_monad",
  ``!:'M:ar 1. !unit map join. umj_monad (unit,map,join) <=>
    monad (unit,BIND (map,join)) /\ (map = MMAP (unit,BIND (map,join)))
      /\ (join = JOIN (unit,BIND (map,join)))``,
  (EVERY [(SRW_TAC [] []), EQ_TAC] THENL 
    [ (MATCH_ACCEPT_TAC umj_monad_IMP_monad_full),
      (EVERY [ (SRW_TAC [] []), (RULE_ASSUM_TAC mb),
      (FIRST_ASSUM (fn th => (SYM th ; CHANGED_TAC (SUBST_ALL_TAC th)))),
      (FIRST_ASSUM (fn th => (SYM th ; CHANGED_TAC (SUBST_ALL_TAC th)))),
      (SRW_TAC [] []) ])]) ) ;

val (umj_monadD, _) = EQ_IMP_RULE (SPEC_ALL umj_monad_def) ;
val [umjD1, umjD2, umjD3, umjD4, umjD5, umjD6, umjD7] =
  CONJUNCTS (UNDISCH umj_monadD) ;

val umj_monad_IMP_monad_bis = store_thm ("umj_monad_IMP_monad_bis",
  ``!:'M. !(unit:'M unit) (map:'M map) (join:'M join).
    umj_monad(unit,map,join) ==> monad(unit, BIND(map,join))``,
  SRW_TAC [] [monad_def, BIND_def]
    THENL [
      MAP_EVERY MP_TAC [umjD3, umjD5],
      MP_TAC umjD6,
      MAP_EVERY MP_TAC [umjD4, GSYM umjD7, GSYM umjD2]]
    THEN EVERY [
      (REWRITE_TAC [o_DEF, FUN_EQ_THM, I_THM]),
      (CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)),
      (REPEAT DISCH_TAC),
      (ASM_REWRITE_TAC []),
      (CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)), REFL_TAC]) ;

val laws_IMP_monad_alt = store_thm ("laws_IMP_monad_alt",
  ``!:'M:ar 1. !unit bind.
    umj_monad (unit, MMAP (unit,bind), JOIN (unit,bind)) /\
    (bind = BIND (MMAP (unit,bind),JOIN (unit,bind))) ==> monad (unit,bind)``,
  EVERY [ (REPEAT STRIP_TAC),
    (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP umj_monad_IMP_monad_full)),
    (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)), (ASM_REWRITE_TAC [])]) ;

val laws_IMP_monad_alt' = TY_GEN_ALL 
  (REWRITE_RULE [umj_monad_def] laws_IMP_monad_alt) ;

(*
show_types := true ;
show_types := false ;
*)

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "xmonad";

val _ = export_theory();

end; (* structure xmonadScript *)

