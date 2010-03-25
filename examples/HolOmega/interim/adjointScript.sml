
(* $Id$ *)

structure adjointScript =
struct

open HolKernel Parse boolLib bossLib

open combinTheory pairTheory functorTheory monadTheory

open auxLib ; (* for tsfg, sfg *)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "adjoint";

val _ = type_abbrev ("sharp",
  Type `: \'F 'G. !'a 'b. ('a -> 'b 'G) -> ('a 'F -> 'b)`) ;
val _ = type_abbrev ("flatt",
  Type `: \'G 'F. !'b 'a. ('a 'F -> 'b) -> ('a -> 'b 'G)`) ;

val adjf1_def = new_definition("adjf1_def",
  ``adjf1 (G : 'G functor) (eta : (I, 'F o 'G) nattransf) 
      (sharp : ('F, 'G) sharp) =
    (!: 'a 'b. (! (f : 'a -> 'b 'G) g. (G g o eta = f) = (sharp f = g)))``) ;

val adjf2_def = new_definition("adjf2_def",
  ``adjf2 (F' : 'F functor) (eps : ('G o 'F, I) nattransf) 
      (flatt : ('G, 'F) flatt) = 
    (!: 'b 'a. (! g (f : 'a -> 'b 'G). (eps o F' f = g) = (flatt g = f)))``) ;

val adjf3_def = new_definition("adjf3_def",
  ``adjf3 (F' : 'F functor) (G : 'G functor)
    (eta : (I, 'F o 'G) nattransf) (eps : ('G o 'F, I) nattransf) =
    (!: 'a 'b. ! (f : 'a -> 'b 'G) g. (G g o eta = f) = (eps o F' f = g))``);

val adjf1DGh' = prove (``adjf1 G eta sharp ==> (G (sharp f) o eta = f)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC adjf1_def), (ASM_REWRITE_TAC []) ]) ;

val adjf1DGh = save_thm ("adjf1DGh",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH adjf1DGh')))) ;

val tmhe = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta sharp ==> (sharp I o F' f = sharp f)`` ;

val adjf1_sharp_eq' = prove (tmhe, EVERY [
  STRIP_TAC, (IMP_RES_THEN (ASSUME_TAC o GSYM) adjf1_def),
  (MATCH_MP_TAC EQ_SYM),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [GSYM o_ASSOC]),
  (IMP_RES_THEN MP_TAC nattransf_def),
  (REWRITE_TAC [oo_def]),
  (TY_BETA_TAC),
  (REWRITE_TAC [o_THM]),
  (DISCH_TAC),
  (ASM_REWRITE_TAC [I_THM]), (ASM_REWRITE_TAC [o_ASSOC]),
  (IMP_RES_TAC adjf1DGh), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

val adjf1_sharp_eq = save_thm ("adjf1_sharp_eq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH adjf1_sharp_eq')))) ;

val EPS_def = new_definition ("EPS_def", 
  ``(EPS (sharp : ('F,'G) sharp) : ('G o 'F, I) nattransf) =
    (\:'e. sharp [:'e 'G, 'e:] I)``) ;

val FLATT_def = new_definition ("FLATT_def", 
  ``(FLATT (G : 'G functor) (eta : (I, 'F o 'G) nattransf) : ('G,'F) flatt) =
    ((\:'b 'a. \g : 'a 'F -> 'b. G g o eta))``) ;

val ETA_def = new_definition ("ETA_def", 
  ``(ETA (flatt : ('G,'F) flatt) : (I, 'F o 'G) nattransf) = 
    (\:'e. flatt [:'e 'F, 'e:] I)``) ;

val SHARP_def = new_definition ("SHARP_def", 
  ``(SHARP (F' : 'F functor) (eps : ('G o 'F, I) nattransf) : ('F,'G) sharp) =
    ((\:'a 'b. \f : 'a -> 'b 'G. eps o F' f))``) ;

val tmd = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta sharp ==> 
  (SHARP F' (EPS sharp) = sharp) /\ (ETA (FLATT G eta) = eta)`` ;

val sharp_tacs = [ (POP_ASSUM (ASSUME_TAC o MATCH_MP adjf1_sharp_eq)),
  (ASM_REWRITE_TAC []), (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)), 
  (REPEAT STRIP_TAC), REFL_TAC] ;

val eta_tacs = [ (POP_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ] ;

val adjf1_IMP_defs = store_thm ("adjf1_IMP_defs", tmd, 
  EVERY [ (REWRITE_TAC [SHARP_def, ETA_def, FLATT_def, EPS_def]),
    TY_BETA_TAC, BETA_TAC, (REWRITE_TAC [TY_FUN_EQ_THM]),
    TY_BETA_TAC, DISCH_TAC, CONJ_TAC ] THENL [
  EVERY sharp_tacs, EVERY eta_tacs ]) ;

val tment = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta sharp ==> nattransf (EPS sharp) (F' oo G) (\:'a 'b. I)`` ;

val adjf1_eta_nt = store_thm ("adjf1_eta_nt", tment, 
  EVERY [DISCH_TAC, (REWRITE_TAC [nattransf_def, EPS_def, oo_def]),
    TY_BETA_TAC, (FIRST_ASSUM (ASSUME_TAC o MATCH_MP adjf1_sharp_eq)),
    (ASM_REWRITE_TAC [o_THM, I_THM]),
    (FIRST_X_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS o CONJUNCT2)) ,
    (IMP_RES_THEN (ASSUME_TAC o GSYM) adjf1_def),
    (REPEAT STRIP_TAC), (MATCH_MP_TAC EQ_SYM),
    (IMP_RES_TAC functor_def),
    (IMP_RES_TAC adjf1DGh), (ASM_REWRITE_TAC [GSYM o_ASSOC, I_o_ID]) ]) ;

val tm13 = ``nattransf eta (\:'a 'b. I) (G o F') /\ functor G /\
       adjf1 G eta sharp ==> adjf3 F' G eta (EPS sharp)`` ;

val adjf1_3 = store_thm ("adjf1_3", tm13,
  EVERY [ (REWRITE_TAC [adjf3_def, EPS_def]), DISCH_TAC,
    (FIRST_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)) ,
    (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP adjf1_sharp_eq)) ,
    TY_BETA_TAC, (IMP_RES_TAC adjf1_def), (ASM_REWRITE_TAC []) ]) ; 

val adjf3_1 = store_thm ("adjf3_1",
  ``adjf3 F' G eta eps = adjf1 G eta (SHARP F' eps)``,
  EVERY [ (REWRITE_TAC [adjf3_def, adjf1_def, SHARP_def]),
    TY_BETA_TAC, BETA_TAC, REFL_TAC] ) ;

val adjf3_2 = store_thm ("adjf3_2",
  ``adjf3 F' G eta eps = adjf2 F' eps (FLATT G eta)``,
  EVERY [ (REWRITE_TAC [adjf3_def, adjf2_def, FLATT_def]),
    TY_BETA_TAC, BETA_TAC, EQ_TAC, DISCH_TAC, ASM_REWRITE_TAC [] ] ) ;

val adjf1_2 = save_thm ("adjf1_2", REWRITE_RULE [adjf3_2] adjf1_3) ;

val sharp_flatt_inv_defs = store_thm ("sharp_flatt_inv_defs",
  ``(functor F' ==> (EPS (SHARP F' eps) = eps)) /\ 
    (functor G ==> (ETA (FLATT G eta) = eta))``,
  EVERY [ (REWRITE_TAC [SHARP_def, FLATT_def, EPS_def, ETA_def, functor_def]),
    (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC, 
    (ASM_REWRITE_TAC [I_o_ID]),
    (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ) ;

val adjf3D = (UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL adjf3_def)))) ;
(* want to instantiate this but need Q.TY_SPECL *)
(* need Q_TAC for types *)

val SHARP_eta_I = store_thm ("SHARP_eta_I", 
  ``functor G /\ adjf3 F' G eta eps ==> (eps o F' eta = I)``,
  EVERY [ STRIP_TAC, (IMP_RES_THEN (ASSUME_TAC o GSYM) adjf3_def),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

val FLATT_eps_I = store_thm ("FLATT_eps_I", 
  ``functor F' /\ adjf3 F' G eta eps ==> (G eps o eta = I)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC adjf3_def),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

(* following for functorTheory *)
val oo_ASSOC = store_thm ("oo_ASSOC", 
  ``!F' G H. F' oo G oo H = (F' oo G) oo H``,
  EVERY [(REWRITE_TAC [oo_def]), TY_BETA_TAC, (REWRITE_TAC [o_ASSOC]) ]) ;

val I_oo_ID = store_thm ("I_oo_ID", 
  ``!H. ((\:'a 'b. I) oo H = H) /\ (H oo (\:'a 'b. I) = H)``,
  EVERY [(REWRITE_TAC [oo_def]), TY_BETA_TAC, (REWRITE_TAC [I_o_ID]),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REWRITE_TAC [] ]) ;

(* why won't oo_ASSOC do this ? *) (* PVH: now it does *)
val oo_assoc_lem = prove (
  ``((G oo F') oo G oo F') = (((G oo F') oo G) oo F')``,
  EVERY [(REWRITE_TAC [oo_ASSOC]) ]) ;

(* note - RES_CANON doesn't deal with ty-foralls properly *) (* PVH: now it does *)
val seith = DISCH_ALL (TY_GEN_ALL (UNDISCH FLATT_eps_I)) ;
val heith = DISCH_ALL (TY_GEN_ALL (UNDISCH SHARP_eta_I)) ;

val adjf3_jmj_lem = store_thm ("adjf3_jmj_lem",
  ``functor F' /\ functor G /\ adjf3 F' G eta eps ==>
    (eps o (F' (G eps)) = eps o eps)``,
  EVERY [STRIP_TAC, (IMP_RES_THEN (ASSUME_TAC o GSYM) adjf3_def),
  (IMP_RES_TAC functor_def), 
  (IMP_RES_TAC FLATT_eps_I), (* this should work but types wrong *) (* PVH: now it does *)
  (* PVH: was: (IMP_RES_TAC seith), *) (ASM_REWRITE_TAC [GSYM o_ASSOC, I_o_ID ]) ]) ;

val jmjth = DISCH_ALL (TY_GEN_ALL (UNDISCH adjf3_jmj_lem)) ;

val tmam = ``functor F' /\ functor G /\
  nattransf eta (\:'a 'b. I) (G oo F') /\
  nattransf eps (F' oo G) (\:'a 'b. I) /\
  adjf3 F' G eta eps ==> cat_monad (G oo F', G foo eps oof F', eta)`` ;

fun ctacs th = [ (REWRITE_TAC [ooo_def, oof_def, foo_def, oo_def]),
  TY_BETA_TAC, (REWRITE_TAC [o_THM]), (IMP_RES_TAC functor_def),
  (FIRST_X_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [GSYM th]))),
  (IMP_RES_TAC th), (ASM_REWRITE_TAC []) ] ;

val adjf_monad = store_thm ("adjf_monad", tmam,
  (REWRITE_TAC [cat_monad_def]) THEN 
  (REPEAT STRIP_TAC) (* which solves first goal *) THENL [
    (MATCH_MP_TAC functor_oo) THEN (ASM_REWRITE_TAC []),
    (* e (PURE_ONCE_REWRITE_TAC [oo_ASSOC]) ; hangs *) (* PVH: no longer *)
    (EVERY [ (REWRITE_TAC [oo_ASSOC]), 
    (* PVH: was: (REWRITE_TAC [oo_assoc_lem]), *)
      (MATCH_MP_TAC nattransf_functor_comp),
      (REWRITE_TAC [GSYM oo_ASSOC]), 
      (REVERSE CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC),
      (Q.SUBGOAL_THEN `nattransf (G foo eps) 
	  (G oo F' oo G) (G oo (\:'a 'b. I))` MP_TAC) THENL [
	(MATCH_MP_TAC functor_nattransf_comp) THEN (ASM_REWRITE_TAC []), 
	(REWRITE_TAC [I_oo_ID]) ]]),
    (FIRST_ASSUM ACCEPT_TAC),
    EVERY (ctacs jmjth),
    EVERY (ctacs heith),
    EVERY [ (REWRITE_TAC [ooo_def, oof_def, foo_def, oo_def]),
      TY_BETA_TAC, (IMP_RES_TAC FLATT_eps_I (*PVH: was: seith*)), (ASM_REWRITE_TAC [])]]) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "adjoint";

val _ = export_theory();

end; (* structure adjointScript *)

