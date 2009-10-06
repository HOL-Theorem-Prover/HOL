structure g_adjointScript =
struct

open HolKernel Parse boolLib bossLib

open combinTheory pairTheory ;
open categoryTheory KmonadTheory ;
(*
load "auxLib" ;
load "g_adjointTheory" ; open g_adjointTheory ;
fun sge tm = set_goal ([], tm) ;
*)
(*
open monadTheory ;
*)

open auxLib ; (* for tsfg, sfg *)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "g_adjoint";

(* 
show_types := false ;
show_types := true ;
handle e => Raise e ;
*)

val _ = type_abbrev ("g_hash",
  Type `: \'C 'D 'F 'G. !'a 'b. ('a, 'b 'G) 'C -> ('a 'F, 'b) 'D`) ;
val _ = type_abbrev ("g_star",
  Type `: \'D 'C 'G 'F. !'b 'a. ('a 'F, 'b) 'D -> ('a, 'b 'G) 'C`) ;

(* thus this term typechecks *)
val _ = ``(x : ('C, 'D, 'F, 'G) g_hash) = (y : ('C C, 'D C, 'F, 'G) g_star)`` ;

val g_adjf1_def = new_definition("g_adjf1_def",
  ``g_adjf1 = \: 'C 'D. 
    \ (idC : 'C id, compC : 'C o_arrow) (G : ('D, 'C, 'G) g_functor)
      (eta : ('C, I, 'F o 'G) g_nattransf) (hash : ('C, 'D, 'F, 'G) g_hash).
    (!: 'a 'b. (! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (hash f = g)))`` ) ;

val g_adjf2_def = new_definition("g_adjf2_def",
  ``g_adjf2 = \: 'D 'C.
    \ (idD : 'D id, compD : 'D o_arrow) (F' : ('C, 'D, 'F) g_functor)
      (eps : ('D, 'G o 'F, I) g_nattransf) (star : ('D, 'C, 'G, 'F) g_star). 
    (!: 'b 'a. (! g (f : ('a, 'b 'G) 'C). 
      (compD eps (F' f) = g) = (star g = f)))``) ;

val g_adjf3_def = new_definition("g_adjf3_def",
  ``g_adjf3 = \: 'C 'D. 
    \ (idC : 'C id, compC : 'C o_arrow) (idD : 'D id, compD : 'D o_arrow)
    (F' : ('C, 'D, 'F) g_functor) (G : ('D, 'C, 'G) g_functor)
    (eta : ('C, I, 'F o 'G) g_nattransf) (eps : ('D, 'G o 'F, I) g_nattransf).
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (compD eps (F' f) = g))``);

(* note, [:'b,'a:] required in g_adjf2_thm,
  [:'a,'b:] not required in g_adjf1_thm *)
val g_adjf1_thm = store_thm ("g_adjf1_thm",
  ``g_adjf1 [:'C,'D:] (idC,compC) G eta hash =
    (!: 'a 'b. (! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (hash [:'a,'b:] f = g)))``,
  SRW_TAC [] [g_adjf1_def]) ;
				      
val g_adjf2_thm = store_thm ("g_adjf2_thm",
  ``g_adjf2 [:'D,'C:] (idD,compD) F' eps star =
    (!: 'b 'a. (! g (f : ('a, 'b 'G) 'C). 
      (compD eps (F' f) = g) = (star [:'b,'a:] g = f)))``, 
  SRW_TAC [] [g_adjf2_def]) ;
				      
val g_adjf3_thm = store_thm ("g_adjf3_thm",
  ``g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps =
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (compD eps (F' f) = g))``,
  SRW_TAC [] [g_adjf3_def]) ;
				      
(* duality - g_adjf3 is self-dual and g_adjf2 is dual of g_adjf1 *)

val g_adjf3_dual = store_thm ("g_adjf3_dual",
  ``g_adjf3 [:'C, 'D:] (idC,compC) (idD,compD) F' G eta eps = 
    g_adjf3 [:'D C, 'C C:] (idD, dual_comp compD) (idC, dual_comp compC) 
      (g_dual_functor G) (g_dual_functor F') eps eta``,
  EVERY [ (REWRITE_TAC [dual_comp_def, g_dual_functor_def, g_adjf3_thm]),
    TY_BETA_TAC, BETA_TAC, EQ_TAC, STRIP_TAC, (ASM_REWRITE_TAC []) ]) ;
      
val g_adjf12_dual = store_thm ("g_adjf12_dual",
  ``g_adjf2 [:'D,'C:] (idD,compD) F' eps star = 
    g_adjf1 [:'D C,'C C:] (idD, dual_comp compD) (g_dual_functor F') eps star``,
  EVERY [ 
    (REWRITE_TAC [dual_comp_def, g_dual_functor_def, g_adjf1_thm, g_adjf2_thm]),
    TY_BETA_TAC, BETA_TAC, REFL_TAC]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val g_adjf1DGh' = prove (``g_adjf1 (idC, compC : 'C o_arrow) G eta hash ==>
    (compC (G (hash f)) eta = f)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC g_adjf1_thm), (ASM_REWRITE_TAC []) ]) ;

val g_adjf1DGh = save_thm ("g_adjf1DGh",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1DGh')))) ;

val adjf1_conds_def = Define `adjf1_conds = \:'C 'D. 
  \ (idC, compC) (idD,compD) eta F' G. 
  g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
  category [:'C:] (idC, compC) /\ 
  g_functor [:'D, 'C:] (idD,compD) (idC,compC) G` ;

val adjf1_conds_thm = store_thm ("adjf1_conds_thm", 
  ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G =
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
    category [:'C:] (idC, compC) /\ 
    g_functor [:'D, 'C:] (idD,compD) (idC,compC) G``,
  EVERY [ REWRITE_TAC [adjf1_conds_def],
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC ]) ;
(*
set_goal ([], tmhe) ;
val (sgs, goal) = top_goal () ;
*) 

val g_adjf1D = tsfg (sfg (fst o EQ_IMP_RULE)) g_adjf1_thm ;
val g_adjf1D1 = DISCH_ALL (tsfg (sfg (fst o EQ_IMP_RULE)) (UNDISCH g_adjf1D)) ; 
val g_adjf2D = tsfg (sfg (fst o EQ_IMP_RULE)) g_adjf2_thm ;
val g_adjf3D = tsfg (sfg (fst o EQ_IMP_RULE)) g_adjf3_thm ;
val g_adjf3D1 = DISCH_ALL (tsfg (sfg (fst o EQ_IMP_RULE)) (UNDISCH g_adjf3D)) ; 
val g_adjf3D2 = DISCH_ALL (tsfg (sfg (snd o EQ_IMP_RULE)) (UNDISCH g_adjf3D)) ; 
val (g_functorD, _) = EQ_IMP_RULE g_functor_thm ; 
val (categoryD, _) = EQ_IMP_RULE category_thm ; 
val (g_nattransfD, _) = EQ_IMP_RULE g_nattransf_thm ; 
val [categoryD_idL, categoryD_idR, categoryD_assoc] = RES_CANON categoryD ;

val tmhc = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC, compC) G eta hash ==> 
  (hash (compC g f) = compD (hash g) (F' f))`` ;

val g_adjf1_hash_comp' = prove (tmhc,
  EVERY [
    (REWRITE_TAC [adjf1_conds_thm]), STRIP_TAC, 
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP (GSYM categoryD_assoc) th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC
      [(REWRITE_RULE [o_THM, I_THM] o TY_BETA_RULE o REWRITE_RULE
      [g_oo_def, g_I_def] o MATCH_MP g_nattransfD) th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP categoryD th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]) ;

val g_adjf1_hash_comp = save_thm ("g_adjf1_hash_comp",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_hash_comp')))) ;

val tmhe = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC, compC) G eta hash ==> (compD (hash idC) (F' f) = hash f)`` ;

val g_adjf1_hash_eq' = prove (tmhe,
  EVERY [ DISCH_TAC,
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP (GSYM g_adjf1_hash_comp) th])),
    (POP_ASSUM (ASSUME_TAC o CONJUNCT1)),
    (IMP_RES_TAC adjf1_conds_thm),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP categoryD_idL th])) ]) ;

val g_adjf1_hash_eq = save_thm ("g_adjf1_hash_eq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_hash_eq')))) ;

val g_adjf1_hash_eta' = prove (
  ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
    g_adjf1 (idC, compC) G eta hash ==> 
    (hash [:'a, 'a 'F:] (eta [:'a:]) = idD [:'a 'F:])``,
  EVERY [ STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP categoryD_idL)) ]) ;

val g_adjf1_hash_eta = save_thm ("g_adjf1_hash_eta",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_hash_eta')))) ;

val tmfc = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  category (idD, compD) /\ 
  g_adjf1 (idC, compC) G eta hash ==> (F' f = hash (compC eta f))`` ;
  
val g_adjf1_Feq' = prove (tmfc, 
  EVERY [ STRIP_TAC,
    (IMP_RES_TAC g_adjf1_hash_comp),
    (* (IMP_RES_TAC g_adjf1_hash_comp') doesn't generalise over types *)
    (IMP_RES_TAC adjf1_conds_thm),
    (IMP_RES_TAC g_adjf1_hash_eta),
    (* (IMP_RES_TAC g_adjf1_hash_eta') doesn't generalise over types *)
    (ASM_REWRITE_TAC []),
    (REPEAT (FIRST_X_ASSUM
      (fn th => REWRITE_TAC [MATCH_MP categoryD_idL th]))) ]) ;

val g_adjf1_Feq = save_thm ("g_adjf1_Feq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_Feq')))) ;

val g_adjf1_Feq_exp = (CONV_RULE (REDEPTH_CONV
    (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV)))
  (REWRITE_RULE [adjf1_conds_def] g_adjf1_Feq) ;
val g_adjf1_Feq_exp' = 
    (DISCH_ALL o SPEC_ALL o TY_SPEC_ALL o UNDISCH) g_adjf1_Feq_exp ;

val tmfee = ``category (idC,compC) /\ category (idD,compD) /\
  g_functor (idD,compD) (idC,compC) G /\
  g_adjf1 [:'C,'D:] (idC,compC) G eta hash ==>
    ((F' = \: 'a 'b. \ f. hash (compC eta f)) = 
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F'))`` ;

val g_adjf1_Feq_nt = store_thm ("g_adjf1_Feq_nt", tmfee, 
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC] 
  THENL [
    EVERY [
      (ASM_REWRITE_TAC [g_nattransf_thm, g_oo_def, g_I_def]),
      TY_BETA_TAC, (REWRITE_TAC [o_THM, I_THM]), BETA_TAC,
      (REPEAT STRIP_TAC),
      (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP g_adjf1DGh)) ],
    EVERY [
      (REWRITE_TAC [TY_FUN_EQ_THM, FUN_EQ_THM]),
      (REPEAT STRIP_TAC), TY_BETA_TAC, BETA_TAC,
      (MATCH_MP_TAC g_adjf1_Feq_exp'),
      (ASM_REWRITE_TAC []) ]]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val tmff  = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  category (idD, compD) /\ g_adjf1 (idC, compC) G eta hash ==> 
  g_functor (idC,compC) (idD,compD) F'`` ;

val g_adjf1_F_fun = store_thm ("g_adjf1_F_fun", tmff,
  EVERY [ DISCH_TAC,
    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP g_adjf1_Feq)),
    (ASM_REWRITE_TAC [g_functor_thm]),
    (POP_ASSUM_LIST (MAP_EVERY (MAP_EVERY ASSUME_TAC o CONJUNCTS))),
    (* delete category (idD,compD) *)
    (FIRST_X_ASSUM (fn th => (MATCH_MP categoryD th ; ALL_TAC))),
    CONJ_TAC, (REPEAT STRIP_TAC),
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (IMP_RES_TAC adjf1_conds_thm),
    (FIRST_ASSUM (fn th => ASM_REWRITE_TAC [MATCH_MP g_functorD th])) ]
  THENL [ (IMP_RES_TAC category_thm) THEN ASM_REWRITE_TAC [],
    EVERY [ 
      (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP categoryD_assoc th)])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP categoryD_assoc th])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]] ) ;

val EPS_def = Define
  `EPS = \: 'C 'D. \ ((idC, compC) : 'C category) 
      (hash : ('C,'D, 'F,'G) g_hash).
    (\:'e. hash [:'e 'G, 'e:] idC) : ('D, 'G o 'F, I) g_nattransf` ;

val ETA_def = Define 
  `ETA = \: 'D 'C. \ ((idD, compD) : 'D category)
      (star : ('D,'C, 'G,'F) g_star).
    (\:'e. star [:'e 'F, 'e:] idD) : ('C, I, 'F o 'G) g_nattransf` ;

val EPS_thm = store_thm ("EPS_thm",
  ``EPS [:'C, 'D:] (idC, compC) hash = (\:'e. hash [:'e 'G, 'e:] idC)``,
  SRW_TAC [] [EPS_def]) ;

val ETA_thm = store_thm ("ETA_thm",
  ``ETA [:'D, 'C:] (idD, compD) star = (\:'e. star [:'e 'F, 'e:] idD)``,
  SRW_TAC [] [ETA_def]) ;

val STAR_def = Define 
  `STAR = \: 'D 'C. \ ((idC, compC) : 'C category)
      (G : ('D, 'C, 'G) g_functor) (eta : ('C, I, 'F o 'G) g_nattransf).
    (\:'b 'a. \g : ('a 'F, 'b) 'D. compC (G g) eta) : ('D,'C, 'G,'F) g_star`;

val HASH_def = Define 
  `HASH = \: 'C 'D. \ ((idD, compD) : 'D category)
      (F' : ('C, 'D, 'F) g_functor) (eps : ('D, 'G o 'F, I) g_nattransf).
    (\:'a 'b. \f : ('a, 'b 'G) 'C. compD eps (F' f)) : ('C,'D, 'F,'G) g_hash`;

val STAR_thm = store_thm ("STAR_thm", 
  ``STAR [:'D, 'C:] (idC, compC) G eta =
    (\:'b 'a. \g : ('a 'F, 'b) 'D. compC (G g) eta)``,
  SRW_TAC [] [STAR_def]) ;

val HASH_thm = store_thm ("HASH_thm",  
  ``HASH [:'C, 'D:] (idD, compD) F' eps =
    (\:'a 'b. \f : ('a, 'b 'G) 'C. compD eps (F' f))``,
  SRW_TAC [] [HASH_def]) ;

(* parsing ETA_EPS_dual and HASH_STAR_dual requires _both_ type arguments *)

val ETA_EPS_dual = store_thm ("ETA_EPS_dual",
  ``(ETA [:'D, 'C:] ((idD, compD) : 'D category) star =
    (EPS [:'D C, 'C C:] (idD, dual_comp compD) star))``,
  EVERY [ (REWRITE_TAC [ETA_thm, EPS_def]), TY_BETA_TAC,
    (REWRITE_TAC [UNCURRY_DEF]), BETA_TAC, REFL_TAC ]) ;

val HASH_STAR_dual = store_thm ("HASH_STAR_dual",
  ``HASH [:'C, 'D:] (idD,compD) F' eps =
    STAR [:'C C, 'D C:] (idD, dual_comp compD) (g_dual_functor F') eps``,
  EVERY [
    (REWRITE_TAC [HASH_thm, STAR_def, dual_comp_def, g_dual_functor_def]), 
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val hash_star_inv_defs = store_thm ("hash_star_inv_defs",
  ``(category (idD,compD) /\ g_functor (idC,compC) (idD,compD) F' ==> 
      (eps = EPS (idC,compC) (HASH (idD,compD) F' eps))) /\ 
    (category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G ==> 
      (eta = ETA (idD,compD) (STAR (idC,compC) G eta)))``,
  EVERY [ (REWRITE_TAC [HASH_def, STAR_def, EPS_thm, ETA_thm, 
      g_functor_def, category_def]), 
    (CONV_TAC (REDEPTH_CONV 
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []),
    (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ) ;

val tmd = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta hash ==> 
  (hash = HASH (idD,compD) F' (EPS (idC,compC) hash))`` ;

val g_adjf1_IMP_defs = store_thm ("g_adjf1_IMP_defs", tmd, 
  EVERY [ DISCH_TAC, MATCH_MP_TAC EQ_SYM,
    (POP_ASSUM (ASSUME_TAC o MATCH_MP g_adjf1_hash_eq)),
    (SRW_TAC [] [HASH_def, EPS_thm]),
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (TOP_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tment = ``g_nattransf (idC,compC) eta (g_I [:'C:]) (G g_oo F') /\ 
  category [:'C:] (idC, compC) /\ g_functor (idD,compD) (idC,compC) G /\
  g_adjf1 (idC,compC) G eta hash ==> 
  g_nattransf (idD,compD) (EPS (idC,compC) hash) (F' g_oo G) (g_I [:'D:])`` ;

val tment = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta hash ==> 
  g_nattransf (idD,compD) (EPS (idC,compC) hash) (F' g_oo G) (g_I [:'D:])`` ;

val g_adjf1_eta_nt = store_thm ("g_adjf1_eta_nt", tment, 
  EVERY [DISCH_TAC,
    (REWRITE_TAC [g_nattransf_def, EPS_thm, g_oo_def, g_I_def, o_DEF]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    (FIRST_ASSUM (fn th => 
      ASM_REWRITE_TAC [I_THM, MATCH_MP g_adjf1_hash_eq th])),
    (POP_ASSUM (MAP_EVERY ASSUME_TAC o
      CONJUNCTS o REWRITE_RULE [adjf1_conds_thm])),

    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP g_adjf1D1)),
    (REPEAT STRIP_TAC), (MATCH_MP_TAC EQ_SYM),
    (FIRST_X_ASSUM MATCH_MP_TAC),
    
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP categoryD_assoc th)])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP categoryD_idR th])) ]) ;

val tm13 = ``adjf1_conds [:'C:] (idC, compC) (idD,compD) eta F' G /\
       g_adjf1 (idC, compC) G eta hash ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G eta (EPS (idC, compC) hash)`` ;

val g_adjf1_3 = store_thm ("g_adjf1_3", tm13,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, EPS_thm]), DISCH_TAC, TY_BETA_TAC,
    (FIRST_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1_hash_eq th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1D th])) ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

(*
val tm23 = ``g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) /\
       category (idD,compD) /\ g_functor (idC,compC) (idD,compD) F' /\
       g_adjf2 (idD, compD) F' eps star ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G (ETA (idD, compD) star) eps`` ;

set_goal ([], tm23) ;
e (REWRITE_TAC [g_adjf12_dual]) ;
e (STRIP_TAC) ;
e (CONV_TAC (REWR_CONV g_adjf3_dual)) ;
e (REWRITE_TAC [ETA_EPS_dual]) ;
e (MATCH_MP_TAC g_adjf1_3) ; (* hangs - why ? *)

val (sgs, goal) = top_goal () ;
PART_MATCH (snd o dest_imp) g_adjf1_3 goal ; (* also hangs *)
PART_MATCH I (REFL ``x``) goal handle e => Raise e ;
 
*)

val g_adjf3_1 = store_thm ("g_adjf3_1",
  ``g_adjf3 (idC, compC) (idD,compD) F' G eta eps =
    g_adjf1 (idC, compC) G eta (HASH (idD,compD) F' eps)``,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, g_adjf1_thm, HASH_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC] ) ;

val g_adjf3_2 = store_thm ("g_adjf3_2",
  ``g_adjf3 (idC, compC) (idD,compD) F' G eta eps =
    g_adjf2 (idD,compD) F' eps (STAR (idC, compC) G eta)``,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, g_adjf2_thm, STAR_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    EQ_TAC, DISCH_TAC, ASM_REWRITE_TAC [] ] ) ;

val g_adjf1_2 = save_thm ("g_adjf1_2", REWRITE_RULE [g_adjf3_2] g_adjf1_3) ;

val HASH_eta_I = store_thm ("HASH_eta_I", 
  ``category (idC, compC) /\ g_functor (idD,compD) (idC,compC) G /\
    g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
      (eps : ('D, 'G o 'F, I) g_nattransf) ==> (compD eps (F' eta) = idD)``,
  EVERY [ STRIP_TAC,
    (FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP categoryD_idL)) ]) ;

val STAR_eps_I = store_thm ("STAR_eps_I", 
  ``category (idD, compD) /\ g_functor (idC,compC) (idD,compD) F' /\
    g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
      (eps : ('D, 'G o 'F, I) g_nattransf) ==> (compC (G eps) eta = idC)``,
  EVERY [ STRIP_TAC,
    (FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D2)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP categoryD_idR)) ]) ;

(* this is the actual formulation of the equivalence of two
  characterisations of adjoint functors *)

val tm13e = ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
    category (idD,compD) ==>
  (g_adjf1 [:'C,'D:] (idC,compC) G eta hash /\
    g_nattransf (idC,compC) eta (g_I [:'C:]) (G g_oo F') /\
    (eps = EPS (idC,compC) hash) = 
  g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps /\ 
    g_functor (idC,compC) (idD,compD) F' /\
    g_nattransf (idC,compC) eta (g_I [:'C:]) (G g_oo F') /\
    g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) /\
    (hash = HASH (idD,compD) F' eps))`` ;

val g_adjf13_equiv = store_thm ("g_adjf13_equiv", tm13e,
  (STRIP_TAC THEN EQ_TAC THEN STRIP_TAC) THENL [
    (EVERY [ (REPEAT CONJ_TAC), (ASM_REWRITE_TAC []),
      (FIRST (map (MATCH_MP_TAC o REWRITE_RULE [adjf1_conds_def]) 
	[ g_adjf1_3, g_adjf1_F_fun, g_adjf1_eta_nt, g_adjf1_IMP_defs ])),
      (CONV_TAC (REDEPTH_CONV
	  (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
      (ASM_REWRITE_TAC []) ] ),
    (EVERY [ (REPEAT CONJ_TAC), (ASM_REWRITE_TAC []),
      (MATCH_MP_TAC (fst (EQ_IMP_RULE g_adjf3_1)) ORELSE
	MATCH_MP_TAC (CONJUNCT1 hash_star_inv_defs)),
      (ASM_REWRITE_TAC []) ]) ]) ;

(* note - RES_CANON doesn't deal with ty-foralls properly *)
val seith = DISCH_ALL (TY_GEN_ALL (UNDISCH STAR_eps_I)) ;
val heith = DISCH_ALL (TY_GEN_ALL (UNDISCH HASH_eta_I)) ;

val tgs = TY_GEN_ALL (GEN_ALL STAR_eps_I) ;
val rctgs = RES_CANON tgs ; 
(* takes off the ty-foralls (recent change ?), but doesn't put them back *)
(* so still need to use seith *)

val tmjmj = 
``category (idC, compC) /\ g_functor (idD,compD) (idC,compC) G /\
  category (idD, compD) /\ g_functor (idC,compC) (idD,compD) F' /\
  g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
    (eps : ('D, 'G o 'F, I) g_nattransf) ==> 
  (compD eps (F' (G eps)) = compD eps eps)`` ;

val g_adjf3_jmj_lem = store_thm ("g_adjf3_jmj_lem", tmjmj, 
  EVERY [STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D1)),
    (ASSUME_TAC seith), RES_TAC, 
    (* can't here use (ASSUME_TAC tgs), RES_TAC, *) 
    REPEAT (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    REPEAT (FIRST_X_ASSUM (fn th => 
      ASSUME_TAC (MATCH_MP categoryD_idR th) THEN
      ASM_REWRITE_TAC [GSYM (MATCH_MP categoryD_assoc th)])) ]) ;

val jmjth = DISCH_ALL (TY_GEN_ALL (UNDISCH g_adjf3_jmj_lem)) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*) 

(* given adjoint functors, you have a monad *)
(* NOTE - where do we assume that eta is a natural transformation *)

val tmass = ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
  g_adjf1 (idC,compC) G eta hash ==> 
  (hash (compC (G (hash h)) k) = compD (hash h) (hash k))`` ;

val g_adjf1_monad_lem = store_thm ("g_adjf1_monad_lem", tmass,
  EVERY [ STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP categoryD_assoc th)])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]) ;

val gahe = DISCH_ALL (TY_GEN_ALL (UNDISCH g_adjf1_hash_eta)) ;
val gaml = DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_monad_lem))) ;

val tmmon = ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
  g_adjf1 (idC,compC) G eta hash ==> 
  Kmonad (idC,compC) (eta, \: 'a 'b. G o hash [:'a,'b 'F:])`` ;

val g_adjf1_IMP_Kmonad = store_thm ("g_adjf1_IMP_Kmonad", tmmon,
  EVERY [ (REWRITE_TAC [Kmonad_def]),
    (CONV_TAC (REDEPTH_CONV 
      (REWR_CONV o_THM ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    STRIP_TAC, (REPEAT CONJ_TAC)]
  THENL [(FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1D th])),
    (IMP_RES_TAC gahe) THEN
      (FIRST_X_ASSUM (fn th => ASM_REWRITE_TAC [MATCH_MP g_functorD th])), 
    (IMP_RES_TAC gaml) THEN
      (FIRST_X_ASSUM (fn th => ASM_REWRITE_TAC [MATCH_MP g_functorD th]))] ) ;

(* given g_adjf1, we get a monad without assuming that eta is a natural
  transformation, but then from the monad, we get that the unit is a natural
  transformation - see how this works - question is, what is the functor F' ? *)
val adjf_gives_nt = 
  DISCH_ALL (MATCH_MP Kmonad_IMP_unit_nt (UNDISCH g_adjf1_IMP_Kmonad)) ;

(* yet to be adapted to general setting 

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

val tmam = ``functor F' /\ functor G /\
  nattransf eta (\:'a 'b. I) (G oo F') /\
  nattransf eps (F' oo G) (\:'a 'b. I) /\
  g_adjf3 F' G eta eps ==> cat_monad (G oo F', G foo eps oof F', eta)`` ;

fun ctacs th = [ (REWRITE_TAC [ooo_def, oof_def, foo_def, oo_def]),
  TY_BETA_TAC, (REWRITE_TAC [o_THM]), (IMP_RES_TAC functor_def),
  (FIRST_X_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [GSYM th]))),
  (IMP_RES_TAC th), (ASM_REWRITE_TAC []) ] ;

val g_adjf_monad = store_thm ("g_adjf_monad", tmam,
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
*)

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
(* given a monad, you have adjoint functors ;
  results in KmonadTheory show that a monad gives:
  the Kleisli category is a category (Kmonad_IMP_Kcat)
  ext is a functor from the Kleisli category (Kmonad_IMP_ext_f)
  unit o _ is a functor into the Kleisli category (Kmonad_IMP_uof) 
  unit is a natural transformation (Kmonad_IMP_unit_nt)
  *)
val Kmonad_IMP_adjf = store_thm ("Kmonad_IMP_adjf",
  ``Kmonad (id,comp) (unit,ext) ==> 
    g_adjf1 [: 'A, ('A, 'M) Kleisli :] (id,comp) ext unit (\: 'a 'b. I)``,
  EVERY [ (REWRITE_TAC [g_adjf1_def, Kmonad_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REPEAT STRIP_TAC, (ASM_REWRITE_TAC [I_THM]),
    EQ_TAC, (MATCH_ACCEPT_TAC EQ_SYM) ]) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "g_adjoint";

val _ = export_theory();

end; (* structure g_adjointScript *)

