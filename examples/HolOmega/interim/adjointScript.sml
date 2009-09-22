
structure adjointScript =
struct

open HolKernel Parse boolLib bossLib

open combinTheory pairTheory functorTheory monadTheory

open auxLib ; (* for tsfg, sfg *)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "adjoint";

(* when using Holmake 
Holmake -I /home/users/jeremy/hol-omega/examples/HolOmega
*)

val _ = type_abbrev ("hash",
  Type `: \'F 'G. !'a 'b. ('a -> 'b 'G) -> ('a 'F -> 'b)`) ;
val _ = type_abbrev ("star",
  Type `: \'G 'F. !'b 'a. ('a 'F -> 'b) -> ('a -> 'b 'G)`) ;

val adjf1_def = new_definition("adjf1_def",
  ``adjf1 (G : 'G functor) (eta : (I, 'F o 'G) nattransf) 
      (hash : ('F, 'G) hash) =
    (!: 'a 'b. (! (f : 'a -> 'b 'G) g. ((G g o eta = f) = (hash f = g))))``) ;

val adjf2_def = new_definition("adjf2_def",
  ``adjf2 (F' : 'F functor) (eps : ('G o 'F, I) nattransf) 
      (star : ('G, 'F) star) = 
    (!: 'b 'a. (! g (f : 'a -> 'b 'G). ((eps o F' f = g) = (star g = f))))``) ;

val adjf3_def = new_definition("adjf3_def",
  ``adjf3 (F' : 'F functor) (G : 'G functor)
    (eta : (I, 'F o 'G) nattransf) (eps : ('G o 'F, I) nattransf) =
    (!: 'a 'b. ! (f : 'a -> 'b 'G) g. ((G g o eta = f) = (eps o F' f = g)))``);

val adjf1DGh' = prove (``adjf1 G eta hash ==> (G (hash f) o eta = f)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC adjf1_def), (ASM_REWRITE_TAC []) ]) ;

val adjf1DGh = save_thm ("adjf1DGh",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH adjf1DGh')))) ;

val tmhe = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta hash ==> (hash I o F' f = hash f)`` ;

val adjf1_hash_eq' = prove (tmhe, EVERY [
  STRIP_TAC, (IMP_RES_TAC adjf1_def), 
  (POP_ASSUM (ASSUME_TAC o tsfg (sfg (fst o EQ_IMP_RULE)))),
  (MATCH_MP_TAC EQ_SYM), (POP_ASSUM MATCH_MP_TAC),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [GSYM o_ASSOC]),
  (IMP_RES_TAC nattransf_def),
  (POP_ASSUM (ASSUME_TAC o REWRITE_RULE [oo_def])),
  (POP_ASSUM (ASSUME_TAC o CONV_RULE (DEPTH_CONV TY_BETA_CONV))),
  (POP_ASSUM (ASSUME_TAC o REWRITE_RULE [o_THM])),
  (ASM_REWRITE_TAC [I_THM]), (ASM_REWRITE_TAC [o_ASSOC]),
  (IMP_RES_TAC adjf1DGh), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

val adjf1_hash_eq = save_thm ("adjf1_hash_eq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH adjf1_hash_eq')))) ;

val EPS_def = new_definition ("EPS_def", 
  ``(EPS (hash : ('F,'G) hash) : ('G o 'F, I) nattransf) =
    (\:'e. hash [:'e 'G, 'e:] I)``) ;

val STAR_def = new_definition ("STAR_def", 
  ``(STAR (G : 'G functor) (eta : (I, 'F o 'G) nattransf) : ('G,'F) star) =
    ((\:'b 'a. \g : 'a 'F -> 'b. G g o eta))``) ;

val ETA_def = new_definition ("ETA_def", 
  ``(ETA (star : ('G,'F) star) : (I, 'F o 'G) nattransf) = 
    (\:'e. star [:'e 'F, 'e:] I)``) ;

val HASH_def = new_definition ("HASH_def", 
  ``(HASH (F' : 'F functor) (eps : ('G o 'F, I) nattransf) : ('F,'G) hash) =
    ((\:'a 'b. \f : 'a -> 'b 'G. eps o F' f))``) ;

val tm12 = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta hash ==> (adjf2 F' (EPS hash) (STAR G eta : ('G,'F) star))`` ;
  
(* better, get adjf1_2 as REWRITE_RULE [adjf3_2] adjf1_3 *)
val adjf1_2 = store_thm ("adjf1_2", tm12,
  EVERY [ (REWRITE_TAC [adjf2_def, STAR_def, EPS_def]),
    (REPEAT STRIP_TAC), TY_BETA_TAC,
    BETA_TAC, EQ_TAC, STRIP_TAC,
    POP_ASSUM (fn th => REWRITE_TAC [SYM th]), 
    (IMP_RES_TAC adjf1_hash_eq),
    (IMP_RES_TAC adjf1_def), (ASM_REWRITE_TAC []), 
    (POP_ASSUM (MATCH_MP_TAC o tsfg (sfg (fst o EQ_IMP_RULE)))),
    REFL_TAC ] ) ;

val tmd = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta hash ==> 
  (HASH F' (EPS hash) = hash) /\ (ETA (STAR G eta) = eta)`` ;

val hash_tacs = [ (POP_ASSUM (ASSUME_TAC o MATCH_MP adjf1_hash_eq)),
  (ASM_REWRITE_TAC []), (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)), 
  (REPEAT STRIP_TAC), REFL_TAC] ;

val eta_tacs = [ (POP_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ] ;

val adjf1_IMP_defs = store_thm ("adjf1_IMP_defs", tmd, 
  EVERY [ (REWRITE_TAC [HASH_def, ETA_def, STAR_def, EPS_def]),
    TY_BETA_TAC, BETA_TAC, (REWRITE_TAC [TY_FUN_EQ_THM]),
    TY_BETA_TAC, DISCH_TAC, CONJ_TAC ] THENL [
  EVERY hash_tacs, EVERY eta_tacs ]) ;

val tment = ``nattransf eta (\:'a 'b. I) (G oo F') /\ functor G /\
  adjf1 G eta hash ==> nattransf (EPS hash) (F' oo G) (\:'a 'b. I)`` ;

val adjf1_eta_nt = store_thm ("adjf1_eta_nt", tment, 
  EVERY [DISCH_TAC, (REWRITE_TAC [nattransf_def, EPS_def, oo_def]),
    TY_BETA_TAC, (FIRST_ASSUM (ASSUME_TAC o MATCH_MP adjf1_hash_eq)),
    (ASM_REWRITE_TAC [o_THM, I_THM]),
    (FIRST_X_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS o CONJUNCT2)) ,
    (IMP_RES_TAC adjf1_def),
    (POP_ASSUM (ASSUME_TAC o tsfg (sfg (fst o EQ_IMP_RULE)))),
    (REPEAT STRIP_TAC), (MATCH_MP_TAC EQ_SYM),
    (POP_ASSUM MATCH_MP_TAC), (IMP_RES_TAC functor_def),
    (IMP_RES_TAC adjf1DGh), (ASM_REWRITE_TAC [GSYM o_ASSOC, I_o_ID]) ]) ;

val tm13 = ``nattransf eta (\:'a 'b. I) (G o F') /\ functor G /\
       adjf1 G eta hash ==> adjf3 F' G eta (EPS hash)`` ;

val adjf1_3 = store_thm ("adjf1_3", tm13,
  EVERY [ (REWRITE_TAC [adjf3_def, EPS_def]), DISCH_TAC,
    (FIRST_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)) ,
    (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP adjf1_hash_eq)) ,
    TY_BETA_TAC, (IMP_RES_TAC adjf1_def), (ASM_REWRITE_TAC []) ]) ; 

val adjf3_1 = store_thm ("adjf3_1",
  ``adjf3 F' G eta eps = adjf1 G eta (HASH F' eps)``,
  EVERY [ (REWRITE_TAC [adjf3_def, adjf1_def, HASH_def]),
    TY_BETA_TAC, BETA_TAC, REFL_TAC] ) ;

val adjf3_2 = store_thm ("adjf3_2",
  ``adjf3 F' G eta eps = adjf2 F' eps (STAR G eta)``,
  EVERY [ (REWRITE_TAC [adjf3_def, adjf2_def, STAR_def]),
    TY_BETA_TAC, BETA_TAC, EQ_TAC, DISCH_TAC, ASM_REWRITE_TAC [] ] ) ;

val hash_star_inv_defs = store_thm ("hash_star_inv_defs",
  ``(functor F' ==> (EPS (HASH F' eps) = eps)) /\ 
    (functor G ==> (ETA (STAR G eta) = eta))``,
  EVERY [ (REWRITE_TAC [HASH_def, STAR_def, EPS_def, ETA_def, functor_def]),
    (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC, 
    (ASM_REWRITE_TAC [I_o_ID]),
    (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ) ;

val adjf3D = (UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL adjf3_def)))) ;
(* want to instantiate this but need Q.TY_SPECL *)
(* need Q_TAC for types *)

val HASH_eta_I = store_thm ("HASH_eta_I", 
  ``functor G /\ adjf3 F' G eta eps ==> (eps o F' eta = I)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC adjf3_def),
  (POP_ASSUM (MATCH_MP_TAC o tsfg (sfg (fst o EQ_IMP_RULE)))),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

val STAR_eps_I = store_thm ("STAR_eps_I", 
  ``functor F' /\ adjf3 F' G eta eps ==> (G eps o eta = I)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC adjf3_def),
  (POP_ASSUM (MATCH_MP_TAC o tsfg (sfg (snd o EQ_IMP_RULE)))),
  (IMP_RES_TAC functor_def), (ASM_REWRITE_TAC [I_o_ID]) ]) ;

(* following for functorTheory *)
val oo_ASSOC = store_thm ("oo_ASSOC", 
  ``!F' G H. F' oo G oo H = (F' oo G) oo H``,
  EVERY [(REWRITE_TAC [oo_def]), TY_BETA_TAC, (REWRITE_TAC [o_ASSOC]) ]) ;

val I_oo_ID = store_thm ("I_oo_ID", 
  ``!H. ((\:'a 'b. I) oo H = H) /\ (H oo (\:'a 'b. I) = H)``,
  EVERY [(REWRITE_TAC [oo_def]), TY_BETA_TAC, (REWRITE_TAC [I_o_ID]),
    (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REWRITE_TAC [] ]) ;

(* why won't oo_ASSOC do this ? *)
val oo_assoc_lem = prove (
  ``((G oo F') oo G oo F') = (((G oo F') oo G) oo F')``,
  EVERY [(REWRITE_TAC [oo_def]), TY_BETA_TAC, (REWRITE_TAC [o_ASSOC]) ]) ;

(* note - RES_CANON doesn't deal with ty-foralls properly *)
val seith = DISCH_ALL (TY_GEN_ALL (UNDISCH STAR_eps_I)) ;
val heith = DISCH_ALL (TY_GEN_ALL (UNDISCH HASH_eta_I)) ;

val adjf3_jmj_lem = store_thm ("adjf3_jmj_lem",
  ``functor F' /\ functor G /\ adjf3 F' G eta eps ==>
    (eps o (F' (G eps)) = eps o eps)``,
  EVERY [STRIP_TAC, (IMP_RES_TAC adjf3_def),
  (POP_ASSUM (MATCH_MP_TAC o tsfg (sfg (fst o EQ_IMP_RULE)))),
  (IMP_RES_TAC functor_def), 
  (* (IMP_RES_TAC STAR_eps_I), this should work but types wrong *)
  (IMP_RES_TAC seith), (ASM_REWRITE_TAC [GSYM o_ASSOC, I_o_ID ]) ]) ;

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
    (* e (PURE_ONCE_REWRITE_TAC [oo_ASSOC]) ; hangs *)
    (EVERY [ (REWRITE_TAC [oo_assoc_lem]), 
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
      TY_BETA_TAC, (IMP_RES_TAC seith), (ASM_REWRITE_TAC [])]]) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "adjoint";

val _ = export_theory();

end; (* structure adjointScript *)

