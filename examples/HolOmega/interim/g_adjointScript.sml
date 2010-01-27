(* $Id$ *)
structure g_adjointScript =
struct

open HolKernel Parse boolLib bossLib

open categoryTheory KmonadTheory auxLib ; infix RS RSN ;
val UNCURRY_DEF = pairTheory.UNCURRY_DEF ;
val o_THM = combinTheory.o_THM ;
val o_DEF = combinTheory.o_DEF ;
val I_THM = combinTheory.I_THM ;

(*
load "auxLib" ;
load "g_adjointTheory" ; open g_adjointTheory ;
fun sge tm = set_goal ([], tm) ;
fun eev tacs = e (EVERY tacs) ;
fun eall [] = () 
  | eall (t :: ts) = (e t ; eall ts) ;
*)

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "g_adjoint";

(* 
show_types := false ;
show_types := true ;
handle e => Raise e ;
*)

val _ = type_abbrev ("g_sharp",
  Type `: \'C 'D 'F 'G. !'a 'b. ('a, 'b 'G) 'C -> ('a 'F, 'b) 'D`) ;
val _ = type_abbrev ("g_flatt",
  Type `: \'D 'C 'G 'F. !'b 'a. ('a 'F, 'b) 'D -> ('a, 'b 'G) 'C`) ;

(* thus this term typechecks *)
val _ = ``(x : ('C, 'D, 'F, 'G) g_sharp) = (y : ('C C, 'D C, 'F, 'G) g_flatt)`` ;

val g_adjf1_def = new_definition("g_adjf1_def",
  ``g_adjf1 = \: 'C 'D 'F 'G. 
    \ (idC : 'C id, compC : 'C o_arrow) (G : ('D, 'C, 'G) g_functor)
      (eta : ('C, I, 'F o 'G) g_nattransf) (sharp : ('C, 'D, 'F, 'G) g_sharp).
    (!: 'a 'b. (! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (sharp f = g)))`` ) ;

val g_adjf2_def = new_definition("g_adjf2_def",
  ``g_adjf2 = \: 'D 'C 'G 'F.
    \ (idD : 'D id, compD : 'D o_arrow) (F' : ('C, 'D, 'F) g_functor)
      (eps : ('D, 'G o 'F, I) g_nattransf) (flatt : ('D, 'C, 'G, 'F) g_flatt). 
    (!: 'b 'a. (! g (f : ('a, 'b 'G) 'C). 
      (compD eps (F' f) = g) = (flatt g = f)))``) ;

val g_adjf3_def = new_definition("g_adjf3_def",
  ``g_adjf3 = \: 'C 'D 'F 'G. 
    \ (idC : 'C id, compC : 'C o_arrow) (idD : 'D id, compD : 'D o_arrow)
    (F' : ('C, 'D, 'F) g_functor) (G : ('D, 'C, 'G) g_functor)
    (eta : ('C, I, 'F o 'G) g_nattransf) (eps : ('D, 'G o 'F, I) g_nattransf).
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (compD eps (F' f) = g))``);

val g_adjf4_def = new_definition("g_adjf4_def",
  ``g_adjf4 = \: 'C 'D 'F 'G. 
    \ (idC : 'C id, compC : 'C o_arrow) (idD : 'D id, compD : 'D o_arrow)
      (sharp : ('C, 'D, 'F, 'G) g_sharp) (flatt : ('D, 'C, 'G, 'F) g_flatt). 
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. (flatt g = f) = (sharp f = g)) /\
    (!: 'a 'c 'b. ! h f. sharp (compC [:'a, 'c, 'b 'G :] f h) = 
        compD (sharp f) (sharp (compC (flatt idD) h))) /\
    (!: 'a 'c 'b. ! h g. flatt (compD [:'a 'F, 'b,'c :] h g) = 
        compC (flatt (compD h (sharp idC))) (flatt g)) ``);

val g_adjf5_def = new_definition("g_adjf5_def",
  ``g_adjf5 = \: 'C 'D 'F 'G. 
    \ (idC : 'C id, compC : 'C o_arrow) (idD : 'D id, compD : 'D o_arrow)
    (F' : ('C, 'D, 'F) g_functor) (G : ('D, 'C, 'G) g_functor)
    (eta : ('C, I, 'F o 'G) g_nattransf) (eps : ('D, 'G o 'F, I) g_nattransf).
    (!: 'b. (compC (G eps) eta = idC [:'b 'G:])) /\
    (!: 'a. (compD eps (F' eta) = idD [:'a 'F:]))``);

(* note, [:'b,'a:] required in g_adjf2_thm,
  [:'a,'b:] not required in g_adjf1_thm *)
val g_adjf1_thm = store_thm ("g_adjf1_thm",
  ``g_adjf1 [:'C,'D:] (idC,compC) G eta sharp =
    (!: 'a 'b. (! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (sharp [:'a,'b:] f = g)))``,
  SRW_TAC [] [g_adjf1_def]) ;
				      
val g_adjf2_thm = store_thm ("g_adjf2_thm",
  ``g_adjf2 [:'D,'C:] (idD,compD) F' eps flatt =
    (!: 'b 'a. (! g (f : ('a, 'b 'G) 'C). 
      (compD eps (F' f) = g) = (flatt [:'b,'a:] g = f)))``, 
  SRW_TAC [] [g_adjf2_def]) ;
				      
val g_adjf3_thm = store_thm ("g_adjf3_thm",
  ``g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps =
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (compD eps (F' f) = g))``,
  SRW_TAC [] [g_adjf3_def]) ;
				      
val exp_convs = [ TY_BETA_CONV, BETA_CONV,
  HO_REWR_CONV pairTheory.FORALL_PROD, REWR_CONV UNCURRY_DEF,
  REWR_CONV TY_FUN_EQ_THM, REWR_CONV FUN_EQ_THM ] ; 

val mk_exp_thm = CONV_RULE (REDEPTH_CONV (FIRST_CONV exp_convs)) ;

val g_adjf4_thm = save_thm ("g_adjf4_thm",
  SPEC_ALL (TY_SPEC_ALL (mk_exp_thm g_adjf4_def))) ;

val g_adjf5_thm = store_thm ("g_adjf5_thm",
  ``g_adjf5 [:'C, 'D, 'F, 'G:] (idC : 'C id, compC : 'C o_arrow)
    (idD : 'D id, compD : 'D o_arrow)
    (F' : ('C, 'D, 'F) g_functor) (G : ('D, 'C, 'G) g_functor)
    (eta : ('C, I, 'F o 'G) g_nattransf) (eps : ('D, 'G o 'F, I) g_nattransf) =
    ((!: 'b. (compC (G eps) eta = idC [:'b 'G:])) /\
    (!: 'a. (compD eps (F' eta) = idD [:'a 'F:])))``,
   SRW_TAC [] [g_adjf5_def]);

(* duality - g_adjf3 is self-dual and g_adjf2 is dual of g_adjf1 *)

val g_adjf3_dual = store_thm ("g_adjf3_dual",
  ``g_adjf3 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) F' G eta eps = 
    g_adjf3 [:'D C,'C C,'G,'F:] (idD, dual_comp compD) (idC, dual_comp compC) 
      (g_dual_functor G) (g_dual_functor F') eps eta``,
  EVERY [ (REWRITE_TAC [dual_comp_def, g_dual_functor_def, g_adjf3_thm]),
    TY_BETA_TAC, BETA_TAC, EQ_TAC, STRIP_TAC, (ASM_REWRITE_TAC []) ]) ;
      
val g_adjf12_dual = store_thm ("g_adjf12_dual",
  ``g_adjf2 [:'D,'C, 'G, 'F:] (idD,compD) F' eps flatt = 
    g_adjf1 [:'D C,'C C, 'G, 'F:] 
      (idD, dual_comp compD) (g_dual_functor F') eps flatt``,
  EVERY [ 
    (REWRITE_TAC [dual_comp_def, g_dual_functor_def, g_adjf1_thm, g_adjf2_thm]),
    TY_BETA_TAC, BETA_TAC, REFL_TAC]) ;

val g_adjf4_dual = store_thm ("g_adjf4_dual",
  ``g_adjf4 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) sharp flatt = 
    g_adjf4 [:'D C, 'C C, 'G, 'F:] 
      (idD, dual_comp compD) (idC, dual_comp compC) flatt sharp``,
  EVERY [ (REWRITE_TAC [dual_comp_def, g_adjf4_thm]),
    TY_BETA_TAC, BETA_TAC, EQ_TAC, STRIP_TAC, 
    CONJ_TAC, REPEAT STRIP_TAC, 
    TRY (FIRST_ASSUM MATCH_ACCEPT_TAC),
    ASM_REWRITE_TAC [] ]) ;
      
(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val g_adjf1DGh' = prove (``g_adjf1 (idC, compC : 'C o_arrow) G eta sharp ==>
    (compC (G (sharp f)) eta = f)``,
  EVERY [ STRIP_TAC, (IMP_RES_TAC g_adjf1_thm), (ASM_REWRITE_TAC []) ]) ;

val g_adjf1DGh = save_thm ("g_adjf1DGh",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1DGh')))) ;

val adjf1_conds_def = Define `adjf1_conds = \:'C 'D 'F 'G. 
  \ (idC, compC) (idD,compD) eta F' G. 
  g_nattransf [:'C:] (idC, compC) (eta :!'a. ('a, 'a 'F 'G) 'C)
    (g_I [:'C:]) (G g_oo F') /\ 
  category [:'C:] (idC, compC) /\ 
  g_functor [:'D, 'C, 'G:] (idD,compD) (idC,compC) G` ;

val adjf1_conds_thm = store_thm ("adjf1_conds_thm", 
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G =
    g_nattransf [:'C:] (idC, compC) 
      (eta :!'a. ('a, 'a 'F 'G) 'C) (g_I [:'C:]) (G g_oo F') /\ 
    category [:'C:] (idC, compC) /\ 
    g_functor [:'D, 'C, 'G:] (idD,compD) (idC,compC) G``,
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
val g_adjf4D = (fst o EQ_IMP_RULE) g_adjf4_thm ;
val [g_adjf4D_eqv, g_adjf4D_sharp, g_adjf4D_flatt] = 
  map DISCH_ALL (CONJUNCTS (UNDISCH g_adjf4D)) ;
val g_adjf4D_eqv1 =
  DISCH_ALL (tsfg (sfg (fst o EQ_IMP_RULE)) (UNDISCH g_adjf4D_eqv)) ; 
val g_adjf4D_eqv2 =
  DISCH_ALL (tsfg (sfg (snd o EQ_IMP_RULE)) (UNDISCH g_adjf4D_eqv)) ; 
val (g_functorD, _) = EQ_IMP_RULE g_functor_thm ; 
val (categoryD, _) = EQ_IMP_RULE category_thm ; 
val (g_nattransfD, _) = EQ_IMP_RULE g_nattransf_thm ; 

val EPS_def = Define
  `EPS = \: 'C 'D. \ ((idC, compC) : 'C category) 
      (sharp : ('C,'D, 'F,'G) g_sharp).
    (\:'e. sharp [:'e 'G, 'e:] idC) : ('D, 'G o 'F, I) g_nattransf` ;

val ETA_def = Define 
  `ETA = \: 'D 'C. \ ((idD, compD) : 'D category)
      (flatt : ('D,'C, 'G,'F) g_flatt).
    (\:'e. flatt [:'e 'F, 'e:] idD) : ('C, I, 'F o 'G) g_nattransf` ;

val EPS_thm = store_thm ("EPS_thm",
  ``EPS [:'C, 'D:] (idC, compC) sharp = (\:'e. sharp [:'e 'G, 'e:] idC)``,
  SRW_TAC [] [EPS_def]) ;

val ETA_thm = store_thm ("ETA_thm",
  ``ETA [:'D, 'C:] (idD, compD) flatt = (\:'e. flatt [:'e 'F, 'e:] idD)``,
  SRW_TAC [] [ETA_def]) ;

val FLATT_def = Define 
  `FLATT = \: 'D 'C. \ ((idC, compC) : 'C category)
      (G : ('D, 'C, 'G) g_functor) (eta : ('C, I, 'F o 'G) g_nattransf).
    (\:'b 'a. \g : ('a 'F, 'b) 'D. compC (G g) eta) : ('D,'C, 'G,'F) g_flatt`;

val SHARP_def = Define 
  `SHARP = \: 'C 'D. \ ((idD, compD) : 'D category)
      (F' : ('C, 'D, 'F) g_functor) (eps : ('D, 'G o 'F, I) g_nattransf).
    (\:'a 'b. \f : ('a, 'b 'G) 'C. compD eps (F' f)) : ('C,'D, 'F,'G) g_sharp`;

val FLATT_thm = store_thm ("FLATT_thm", 
  ``FLATT [:'D, 'C:] (idC, compC) G eta =
    (\:'b 'a. \g : ('a 'F, 'b) 'D. compC (G g) eta)``,
  SRW_TAC [] [FLATT_def]) ;

val SHARP_thm = store_thm ("SHARP_thm",  
  ``SHARP [:'C, 'D:] (idD, compD) F' eps =
    (\:'a 'b. \f : ('a, 'b 'G) 'C. compD eps (F' f))``,
  SRW_TAC [] [SHARP_def]) ;

(* parsing ETA_EPS_dual and SHARP_FLATT_dual requires _both_ type arguments *)

val ETA_EPS_dual = store_thm ("ETA_EPS_dual",
  ``(ETA [:'D, 'C:] ((idD, compD) : 'D category) flatt =
    (EPS [:'D C, 'C C:] (idD, dual_comp compD) flatt))``,
  EVERY [ (REWRITE_TAC [ETA_thm, EPS_def]), TY_BETA_TAC,
    (REWRITE_TAC [UNCURRY_DEF]), BETA_TAC, REFL_TAC ]) ;

val EPS_ETA_dual = store_thm ("EPS_ETA_dual",
  ``(EPS [:'C, 'D:] ((idC, compC) : 'C category) sharp =
    (ETA [:'C C, 'D C:] (idC, dual_comp compC) sharp))``,
  EVERY [ (REWRITE_TAC [ETA_def, EPS_thm]), TY_BETA_TAC,
    (REWRITE_TAC [UNCURRY_DEF]), BETA_TAC, REFL_TAC ]) ;

val SHARP_FLATT_dual = store_thm ("SHARP_FLATT_dual",
  ``SHARP [:'C, 'D:] (idD,compD) F' eps =
    FLATT [:'C C, 'D C:] (idD, dual_comp compD) (g_dual_functor F') eps``,
  EVERY [
    (REWRITE_TAC [SHARP_thm, FLATT_def, dual_comp_def, g_dual_functor_def]), 
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC ]) ;

val FLATT_SHARP_dual = store_thm ("FLATT_SHARP_dual",
  ``FLATT [:'D, 'C:] (idC,compC) G eta =
    SHARP [:'D C, 'C C:] (idC, dual_comp compC) (g_dual_functor G) eta``,
  EVERY [
    (REWRITE_TAC [SHARP_def, FLATT_thm, dual_comp_def, g_dual_functor_def]), 
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC ]) ;

val gatm =
``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G ==>
  category [:'C:] (idC, compC) ==> category [:'D:] (idD, compD) ==> 
  g_adjf1 [:'C, 'D, 'F, 'G:] (idC,compC) G eta sharp ==>
  g_adjf2 [:'D, 'C, 'G, 'F:] (idD,compD) F' eps flatt ==> 
  g_adjf3 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) F' G eta eps ==>
  g_adjf4 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) sharp flatt ==>
  (!:'a 'b. !f g. (flatt [:'b,'a:] g = f) <=> (sharp [:'a,'b:] f = g)) ==>
  (!:'a 'c 'b. !h f. sharp [:'a,'b:] (compC f h) =
    compD (sharp [:'c,'b:] f) (sharp (compC (flatt idD) h))) ==>
  (!:'a 'c 'b. !h g. flatt [:'c,'a:] (compD h g) =
    compC (flatt (compD h (sharp idC))) (flatt [:'b,'a:] g)) ==>
  g_adjf5 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) F' G eta eps ==>
  g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G ==>
  g_functor [:'C,'D,'F:] (idC,compC) (idD,compD) F' ==>
  g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') ==> 
  g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) ==>
  (eps = EPS (idC,compC) sharp) ==> (flatt = FLATT (idC,compC) G eta) ==>
  (eta = ETA (idD,compD) flatt) ==> (sharp = SHARP (idD,compD) F' eps) ==>
  (G = \:'a 'b. \g. flatt (compD g eps)) ==>
  (F' = \:'a 'b. \f. sharp (compC eta f)) ==> T `` ;

val ([a1cs, catC, catD, adjf1, adjf2, adjf3, adjf4,
  adjf4a, adjf4b, adjf4c, adjf5, funG, funF,
  nteta, nteps, eps, flatt, eta, sharp, Geq, Feq], _) = strip_imp gatm ;

val cats = mk_conj (catC, catD) ;
val cats' = mk_conj (catD, catC) ;

val tmhc =
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
    g_adjf1 (idC, compC) G eta sharp ==> 
    (sharp (compC g f) = compD (sharp g) (F' f))`` ;

val g_adjf1_sharp_comp' = prove (tmhc,
  EVERY [
    (REWRITE_TAC [adjf1_conds_thm]), STRIP_TAC, 
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDRAss th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC
      [(REWRITE_RULE [o_THM, I_THM] o TY_BETA_RULE o REWRITE_RULE
      [g_oo_thm, g_I_def] o MATCH_MP g_nattransfD) th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP categoryD th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]) ;

val g_adjf1_sharp_comp = save_thm ("g_adjf1_sharp_comp",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_sharp_comp')))) ;

val tmhe =
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
    g_adjf1 (idC, compC) G eta sharp ==> (compD (sharp idC) (F' f) = sharp f)`` ;

val g_adjf1_sharp_eq' = prove (tmhe,
  EVERY [ DISCH_TAC,
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP (GSYM g_adjf1_sharp_comp) th])),
    (POP_ASSUM (ASSUME_TAC o CONJUNCT1)),
    (IMP_RES_TAC adjf1_conds_thm),
    (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDLU th])) ]) ;

val g_adjf1_sharp_eq = save_thm ("g_adjf1_sharp_eq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_sharp_eq')))) ;

val g_adjf1_sharp_eta' = prove (
  ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
    g_adjf1 (idC, compC) G eta sharp ==> 
    (sharp [:'a, 'a 'F:] (eta [:'a:]) = idD [:'a 'F:])``,
  EVERY [ STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP catDLU)) ]) ;

val g_adjf1_sharp_eta = save_thm ("g_adjf1_sharp_eta",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_sharp_eta')))) ;

val tmfc = 
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
    category (idD, compD) /\ g_adjf1 (idC, compC) G eta sharp ==>
    (F' f = sharp (compC eta f))`` ;
  
val g_adjf1_Feq' = prove (tmfc, 
  EVERY [ STRIP_TAC,
    (IMP_RES_TAC g_adjf1_sharp_comp),
    (* (IMP_RES_TAC g_adjf1_sharp_comp') doesn't generalise over types *)
    (IMP_RES_TAC adjf1_conds_thm),
    (IMP_RES_TAC g_adjf1_sharp_eta),
    (* (IMP_RES_TAC g_adjf1_sharp_eta') doesn't generalise over types *)
    (ASM_REWRITE_TAC []),
    (REPEAT (FIRST_X_ASSUM
      (fn th => REWRITE_TAC [MATCH_MP catDLU th]))) ]) ;

val g_adjf1_Feq = save_thm ("g_adjf1_Feq",
  DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_Feq')))) ;

val g_adjf1_Feq_exp = (CONV_RULE (REDEPTH_CONV
    (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV)))
  (REWRITE_RULE [adjf1_conds_def] g_adjf1_Feq) ;
val g_adjf1_Feq_exp' = 
    (DISCH_ALL o SPEC_ALL o TY_SPEC_ALL o UNDISCH) g_adjf1_Feq_exp ;

val tmfee = mk_imp 
  (list_mk_conj [catC, catD, funG, adjf1], mk_eq (Feq, nteta)) ;

val g_adjf1_Feq_nt = store_thm ("g_adjf1_Feq_nt", tmfee, 
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC] 
  THENL [
    EVERY [
      (ASM_REWRITE_TAC [g_nattransf_thm, g_oo_thm, g_I_def]),
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

val tmff  =
``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  category (idD, compD) /\ g_adjf1 (idC, compC) G eta sharp ==> 
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
      (FIRST_ASSUM (fn th => REWRITE_TAC [(MATCH_MP catDRAss th)])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDAss th])),
      (FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]] ) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

val sharp_flatt_inv_defs = store_thm ("sharp_flatt_inv_defs",
  ``(category (idD,compD) /\ g_functor (idC,compC) (idD,compD) F' ==> 
      (eps = EPS (idC,compC) (SHARP (idD,compD) F' eps))) /\ 
    (category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G ==> 
      (eta = ETA (idD,compD) (FLATT (idC,compC) G eta)))``,
  EVERY [ (REWRITE_TAC [SHARP_def, FLATT_def, EPS_thm, ETA_thm, 
      g_functor_def, category_def]), 
    (CONV_TAC (REDEPTH_CONV 
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    (REPEAT STRIP_TAC), (ASM_REWRITE_TAC []),
    (CONV_TAC (ONCE_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ] ) ;

val [sharp_inv_def, flatt_inv_def] = CONJUNCTS sharp_flatt_inv_defs ;

val tmd = ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta sharp ==> 
  (sharp = SHARP (idD,compD) F' (EPS (idC,compC) sharp))`` ;

val g_adjf1_IMP_defs = store_thm ("g_adjf1_IMP_defs", tmd, 
  EVERY [ DISCH_TAC, MATCH_MP_TAC EQ_SYM,
    (POP_ASSUM (ASSUME_TAC o MATCH_MP g_adjf1_sharp_eq)),
    (SRW_TAC [] [SHARP_def, EPS_thm]),
    (CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)),
    (CONV_TAC (TOP_DEPTH_CONV TY_ETA_CONV)), REFL_TAC ]) ;

val tment =
``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta sharp ==> 
  g_nattransf (idD,compD) (EPS (idC,compC) sharp) (F' g_oo G) (g_I [:'D:])`` ;

val g_adjf1_eta_nt = store_thm ("g_adjf1_eta_nt", tment, 
  EVERY [DISCH_TAC,
    (REWRITE_TAC [g_nattransf_def, EPS_thm, g_oo_thm, g_I_def, o_DEF]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    (FIRST_ASSUM (fn th => 
      ASM_REWRITE_TAC [I_THM, MATCH_MP g_adjf1_sharp_eq th])),
    (POP_ASSUM (MAP_EVERY ASSUME_TAC o
      CONJUNCTS o REWRITE_RULE [adjf1_conds_thm])),

    (FIRST_ASSUM (ASSUME_TAC o MATCH_MP g_adjf1D1)),
    (REPEAT STRIP_TAC), (MATCH_MP_TAC EQ_SYM),
    (FIRST_X_ASSUM MATCH_MP_TAC),
    
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_ASSUM (fn th => REWRITE_TAC [(MATCH_MP catDRAss th)])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDRU th])) ]) ;

val tm13 = ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
       g_adjf1 (idC, compC) G eta sharp ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G eta (EPS (idC, compC) sharp)`` ;

val g_adjf1_3 = store_thm ("g_adjf1_3", tm13,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, EPS_thm]), DISCH_TAC, TY_BETA_TAC,
    (FIRST_ASSUM (MAP_EVERY ASSUME_TAC o CONJUNCTS)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1_sharp_eq th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1D th])) ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)

(* prove g_adjf2_3 by duality from g_adjf1_3 *)
val tm23 = ``g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) /\
       category (idD,compD) /\ g_functor (idC,compC) (idD,compD) F' /\
       g_adjf2 (idD, compD) F' eps flatt ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G (ETA (idD, compD) flatt) eps`` ;

val g_adjf2_3 = store_thm ("g_adjf2_3", tm23,
  EVERY [ (REWRITE_TAC [g_adjf12_dual]), (STRIP_TAC),
    (CONV_TAC (REWR_CONV g_adjf3_dual)),
    (REWRITE_TAC [ETA_EPS_dual]),
    (MATCH_MP_TAC g_adjf1_3), 
    (REWRITE_TAC [adjf1_conds_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    (ASM_REWRITE_TAC (map GSYM [g_functor_dual, category_dual])),
    (FIRST_X_ASSUM (ASSUME_TAC o 
      MATCH_MP (fst (EQ_IMP_RULE g_nattransf_dual)))),
    (FIRST_ASSUM (ACCEPT_TAC o REWRITE_RULE [g_I_dual, g_oo_dual])) ]) ;

val g_adjf3_1 = store_thm ("g_adjf3_1",
  ``g_adjf3 (idC, compC) (idD,compD) F' G eta eps =
    g_adjf1 (idC, compC) G eta (SHARP (idD,compD) F' eps)``,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, g_adjf1_thm, SHARP_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REFL_TAC] ) ;

val g_adjf3_2 = store_thm ("g_adjf3_2",
  ``g_adjf3 (idC, compC) (idD,compD) F' G eta eps =
    g_adjf2 (idD,compD) F' eps (FLATT (idC, compC) G eta)``,
  EVERY [ (REWRITE_TAC [g_adjf3_thm, g_adjf2_thm, FLATT_def]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    EQ_TAC, DISCH_TAC, ASM_REWRITE_TAC [] ] ) ;

val g_adjf1_2 = save_thm ("g_adjf1_2", REWRITE_RULE [g_adjf3_2] g_adjf1_3) ;

val SHARP_eta_I = store_thm ("SHARP_eta_I", 
  ``g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
      (eps : ('D, 'G o 'F, I) g_nattransf) /\
    category (idC, compC) /\ g_functor (idD,compD) (idC,compC) G ==> 
    (compD eps (F' eta) = idD)``,
  EVERY [ STRIP_TAC,
    (FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP catDLU)) ]) ;

val FLATT_eps_I = store_thm ("FLATT_eps_I", 
  ``g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
      (eps : ('D, 'G o 'F, I) g_nattransf) /\
    category (idD, compD) /\ g_functor (idC,compC) (idD,compD) F' ==>
    (compC (G eps) eta = idC)``,
  EVERY [ STRIP_TAC,
    (FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D2)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP catDRU)) ]) ;

(* this is the actual formulation of the equivalence of two
  characterisations of adjoint functors *)

(* problem with using this first one, the type constructor variable
  of functor G does not match, and in g_adjf1_F_fun there is a free
  variable in the premises, not in the conclusion, and when this happens,
  MATCH_MP_TAC produces existential goal for terms, but not for types *)

val tm13e = mk_imp (list_mk_conj [catC, catD, funG, nteta],
  mk_eq (mk_conj (adjf1, eps), list_mk_conj [adjf3, funF, nteps, sharp])) ;

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
	MATCH_MP_TAC (CONJUNCT1 sharp_flatt_inv_defs)),
      (ASM_REWRITE_TAC []) ]) ]) ;

(* get directly from g_adjf3 /\ F',G functors that eps and eta are nts *)
val tm3nt = mk_imp (list_mk_conj [adjf3, catC, catD, funF, funG],
  mk_conj (nteta, nteps)) ;

val g_adjf3_nt = store_thm ("g_adjf3_nt", tm3nt, 
  EVERY [ STRIP_TAC, (IMP_RES_TAC g_functorD),
    (IMP_RES_TAC catDLU), (IMP_RES_TAC catDRU),
    (SRW_TAC [] [g_nattransf_def, g_oo_def, g_I_def]) ]
  THENL [
    EVERY [
      (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf3D2)),
      (ASM_REWRITE_TAC []),
      (FIRST_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [MATCH_MP catDAss th]))),
      (USE_LIM_RES_TAC (fn th => ASM_REWRITE_TAC [th]) (SHARP_eta_I))],
    EVERY [
      (FIRST_ASSUM (MATCH_MP_TAC o GSYM o MATCH_MP g_adjf3D1)),
      (ASM_REWRITE_TAC []),
      (FIRST_ASSUM (fn th => CHANGED_TAC 
	(REWRITE_TAC [MATCH_MP catDRAss th]))),
      (USE_LIM_RES_TAC (fn th => ASM_REWRITE_TAC [th]) ( FLATT_eps_I))]] ) ;
     
val dual_convs = 
  [g_adjf3_dual, g_adjf12_dual, ETA_EPS_dual, EPS_ETA_dual, 
     FLATT_SHARP_dual, SHARP_FLATT_dual,
     g_functor_dual, g_nattransf_dual, category_dual] ;

(* get link between g_adjf2 and g_adjf3 by duality *)

val tm23e = mk_imp (list_mk_conj [catD, catC, funF, nteps],
  mk_eq (mk_conj (adjf2, eta), list_mk_conj [adjf3, funG, nteta, flatt])) ;

val g_adjf23_equiv = store_thm ("g_adjf23_equiv", tm23e,
  EVERY [
    (CONV_TAC (ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV dual_convs)))),
    (REWRITE_TAC [g_oo_dual, g_I_dual]),
    (MATCH_ACCEPT_TAC g_adjf13_equiv) ]) ;

val tm12e = mk_imp (mk_conj (catC, catD),
  mk_eq (list_mk_conj [adjf1, funG, nteta, eps, flatt],
    list_mk_conj [adjf2, funF, nteps, eta, sharp])) ;

(* note, e (IMP_RES_TAC g_adjf13_equiv) takes forever,
  partly because RES_CANON g_adjf13_equiv produces a list of length 200,
  and partly because there are multiple instantiations for category ... *)

val (ga13, ga31) = EQ_IMP_RULE (UNDISCH g_adjf13_equiv) ;
val (ga23, ga32) = EQ_IMP_RULE (UNDISCH g_adjf23_equiv) ;

val [ga13', ga31', ga23', ga32'] = 
  map (reo_prems rev o DISCH_ALL) [ga13, ga31, ga23, ga32] ;

fun usega th = (CHANGED_TAC (REWRITE_TAC [th]) THEN
  MAP_EVERY ASSUME_TAC (CONJUNCTS th)) ;

val g_adjf12_equiv = store_thm ("g_adjf12_equiv", tm12e,
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC ]
  THENL [ FIRST_REP_RES_MKI usega ga13' THEN FIRST_REP_RES_MKI usega ga32',
    FIRST_REP_RES_MKI usega ga23' THEN FIRST_REP_RES_MKI usega ga31' ]) ;

val seith = DISCH_ALL (TY_GEN_ALL (UNDISCH FLATT_eps_I)) ;
val heith = DISCH_ALL (TY_GEN_ALL (UNDISCH SHARP_eta_I)) ;

val tm43 = mk_imp (list_mk_conj [adjf4, catC, catD, eta, eps, Feq, Geq],
  list_mk_conj [funF, funG, nteta, nteps, adjf3, sharp, flatt]) ;

val g_adjf4_3 = store_thm ("g_adjf4_3", tm43,
  EVERY [ STRIP_TAC, (IMP_RES_TAC catDLU), (IMP_RES_TAC catDRU),
    (SRW_TAC [] [g_adjf3_thm, ETA_thm, EPS_thm, SHARP_thm, FLATT_thm,
      g_functor_thm, g_nattransf_thm]) ]
  THENL [
    (* F' and G functors *)
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf4D_eqv1)) THEN REFL_TAC,

    (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_sharp th)])) 
      THEN (REPEAT 
        (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDAss th]))),

    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf4D_eqv2)) THEN REFL_TAC,

    (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_flatt th)]))
      THEN (REPEAT
        (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP catDAss th]))),

    (* eta and eps are natural transformations *)
    (*
    e (REWRITE_TAC [g_oo_def, o_DEF]) ; (* does nothing - why ?? *)
    *)
    EVERY [ (REWRITE_TAC [g_oo_def]), (* has an effect *)
      (SRW_TAC [] [o_THM, g_I_def]),
      (FIRST_ASSUM (fn th => 
	ASM_REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_flatt th)])),
      (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf4D_eqv2)), REFL_TAC],

    EVERY [ (REWRITE_TAC [g_oo_def, g_I_def]), (* has an effect *)
      (SRW_TAC [] [o_THM]),
      (FIRST_ASSUM (fn th => 
	ASM_REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_sharp th)])),
      (FIRST_ASSUM (MATCH_MP_TAC o GSYM o MATCH_MP g_adjf4D_eqv1)), REFL_TAC],

    (* finally, the equivalence condition, g_adjf3 *)
    EVERY [
      (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_flatt th)])),
      (FIRST_ASSUM (fn th => 
	ASM_REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_sharp th)])),
      (FIRST_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP g_adjf4D_eqv))],

    EVERY [ (FIRST_ASSUM
        (fn th => ASM_REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_sharp th)])),
      (CONV_TAC (DEPTH_CONV ETA_CONV)),
      (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC],

    EVERY [ (FIRST_ASSUM
        (fn th => ASM_REWRITE_TAC [GSYM (MATCH_MP g_adjf4D_flatt th)])),
      (CONV_TAC (DEPTH_CONV ETA_CONV)),
      (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC] ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
val tm34 = ``g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps /\
  category (idC,compC) /\ category (idD,compD) /\ 
       g_functor (idC,compC) (idD,compD) F' /\
       g_functor (idD,compD) (idC,compC) G ==>
  g_adjf4 [:'C, 'D:] (idC,compC) (idD,compD) 
    (SHARP (idD,compD) F' eps) (FLATT (idC, compC) G eta)`` ;

val g_adjf3_4 = store_thm ("g_adjf3_4", tm34, 
  EVERY [ STRIP_TAC,
    (USE_LIM_RES_TAC ASSUME_TAC ( heith)),
    (USE_LIM_RES_TAC ASSUME_TAC ( seith)),
    (SRW_TAC [] [g_adjf4_thm, SHARP_thm, FLATT_thm]),
    (IMP_RES_TAC g_functor_thm),
    (IMP_RES_TAC catDLU), (IMP_RES_TAC catDRU) ] 
  THENL [
    (FIRST_X_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP g_adjf3D)),
    EVERY [ (ASM_REWRITE_TAC []),
      (FIRST_ASSUM (fn th => 
	CHANGED_TAC (REWRITE_TAC [MATCH_MP catDRAss th]))),
      (REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC)),
      (FIRST_ASSUM (fn th => 
	CHANGED_TAC (ASM_REWRITE_TAC [MATCH_MP catDAss th]))) ],
    EVERY [ (ASM_REWRITE_TAC []),
      (FIRST_ASSUM (fn th => 
	CHANGED_TAC (REWRITE_TAC [MATCH_MP catDAss th]))),
      (REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC)),
      (FIRST_ASSUM (fn th => 
	CHANGED_TAC (ASM_REWRITE_TAC [MATCH_MP catDRAss th]))) ]]) ;

val tm34e = ``category (idC,compC) /\ category (idD,compD) ==> 
  (g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps /\
    g_functor (idC,compC) (idD,compD) F' /\
    g_functor (idD,compD) (idC,compC) G /\
    (sharp = SHARP (idD,compD) F' eps) /\ (flatt = FLATT (idC, compC) G eta) =
  g_adjf4 [:'C, 'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ (eps = EPS (idC,compC) sharp) /\
    (F' = (\:'a 'b. (\f. sharp (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt (compD g eps))))) `` ; 

val g_adjf34_equiv = store_thm ("g_adjf34_equiv", tm34e, 
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC ] 
    THENL [
      EVERY [
	(USE_LIM_RES_TAC ASSUME_TAC ( g_adjf3_4)),
	(ASM_REWRITE_TAC []), (IMP_RES_TAC g_functorD),
	(IMP_RES_TAC catDLU), (IMP_RES_TAC catDRU),
	(REPEAT CONJ_TAC) ]
      THENL [ (MATCH_MP_TAC flatt_inv_def) THEN (ASM_REWRITE_TAC []),
	(MATCH_MP_TAC sharp_inv_def) THEN (ASM_REWRITE_TAC []),

	EVERY [ (SRW_TAC [] [SHARP_thm]),
	  (FIRST_ASSUM (fn th =>
	    CHANGED_TAC (REWRITE_TAC [MATCH_MP catDAss th]))),
	  (USE_LIM_RES_TAC (fn th => ASM_REWRITE_TAC [th]) ( SHARP_eta_I)),
	  (CONV_TAC (DEPTH_CONV ETA_CONV)),
	  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC],
	
	EVERY [ (SRW_TAC [] [FLATT_thm]),
	  (FIRST_ASSUM (fn th =>
	    CHANGED_TAC (REWRITE_TAC [MATCH_MP catDRAss th]))),
	  (USE_LIM_RES_TAC (fn th => ASM_REWRITE_TAC [th]) ( FLATT_eps_I)),
	  (CONV_TAC (DEPTH_CONV ETA_CONV)),
	  (CONV_TAC (DEPTH_CONV TY_ETA_CONV)), REFL_TAC] ],

      (USE_LIM_RES_TAC (fn th => REWRITE_TAC [th]) ( g_adjf4_3)) ]) ;
	
(* observe that from g_adjf4 we prove that eta and eps are nts,
  but we don't use this to get back to g_adjf4 from g_adjf3 ;
  thus it follows that g_adjf3 implies that eta and eps are nts,
  which is proved directly in g_adjf3nt *) 

(* type-checking this fails, with a very strange message, namely 
Type inference failure: unable to infer a type for the application of

$= (F' :∀α β. (α, β) ('C: ar 2) -> (α ('F: ar 1), β 'F) ('D: ar 2))

on line 56, characters 5-58

which has type

:(∀α β. (α, β) ('C: ar 2) -> (α ('F: ar 1), β 'F) ('D: ar 2)) -> bool

to

...

which has type

:∀α β. (α, β) ('C: ar 2) -> (α ('F: ar 1), β 'F) ('D: ar 2)

(ie, the types look exactly right for a function application )


val tm14e = ``category (idC,compC) ∧ category (idD,compD) ==>
  (g_adjf1 [:'C,'D:] (idC,compC) G eta sharp /\
    g_functor (idD,compD) (idC,compC) G /\
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
    (flatt = FLATT (idC, compC) G eta) = 
  g_adjf4 [:'C,'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ (eps = EPS (idC,compC) sharp) /\
    (F' = (\:'a 'b. (\f. sharp [:'a, 'b 'F:] (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt [:'b, 'a 'G:] (compD g eps)))))``  ;

*)

(* there must be an easier way than this !! *)
local val (th0, _) = EQ_IMP_RULE (UNDISCH g_adjf13_equiv) ;
val th1 = REWRITE_RULE [GSYM AND_IMP_INTRO] th0 ;
val (eps, EPS) = dest_eq (lhand (concl (UNDISCH th1))) ;
in val g_adjf1_eq3 = REWRITE_RULE [] (INST [eps |-> EPS] g_adjf13_equiv) end ;


local 
val th1 = REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf4_3 ;
val th2 = UNDISCH_ALL th1 ;
val hys = hyp th2 ;
val eqhys = filter is_eq hys ;
val subs = map (fn hy => (lhand hy |-> rand hy)) eqhys ;
in val g43 = REWRITE_RULE [] (INST subs (INST subs th1)) end ;


val (a1, th0) = (UNDISCH_TERM g_adjf1_eq3) ;
val (g13D, _) = EQ_IMP_RULE th0 ;
val g_adjf1_eq3' = REWRITE_RULE [GSYM AND_IMP_INTRO]
  (DISCH_ALL (DISCH a1 (UNDISCH g13D))) ;

val (a1, th0) = (UNDISCH_TERM g_adjf34_equiv) ;
val (g34D, _) = EQ_IMP_RULE th0 ;
val g_adjf3_eq4' = REWRITE_RULE [GSYM AND_IMP_INTRO]
  (DISCH_ALL (DISCH a1 (UNDISCH g34D))) ;

val (a1, th0) = (UNDISCH_TERM g_adjf13_equiv) ;
val (_, g31D) = EQ_IMP_RULE th0 ;
val g_adjf3_eq1 = REWRITE_RULE [GSYM AND_IMP_INTRO]
  (DISCH_ALL (DISCH a1 (UNDISCH g31D))) ;


val tm14e = ``category (idC,compC) /\ category (idD,compD) ==>
  (g_adjf1 [:'C,'D:] (idC,compC) G eta sharp /\
    g_functor (idD,compD) (idC,compC) G /\
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
    (flatt = FLATT (idC, compC) G eta) = 
  g_adjf4 [:'C,'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ 
    (F' = (\:'a 'b. (\f. sharp (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt (compD g (EPS (idC,compC) sharp))))))`` ;

(* note that the second and third conditions in g_adjf4 are equivalent,
  in the presence of the first condition - TO BE PROVED *)
val g_adjf14_equiv = store_thm ("g_adjf14_equiv", tm14e,
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC 
  THENL [
    EVERY [
      (USE_LIM_RES_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS) ( g_adjf1_eq3')),
      (USE_LIM_RES_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS) ( g_adjf3_eq4')),
      (REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)],
    EVERY [
      (USE_LIM_RES_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS) ( g43)),
      (POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o GSYM))),
      (FULL_SIMP_TAC simpLib.empty_ss []),
      (USE_LIM_RES_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS) 
        ( (GSYM g_adjf3_eq1))),
      (REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC))] ]) ;
      
(* assumptions of this theorem are the definition of adjoint pair
  currently (Jan 2010) on Wikipedia, under the heading
  Definition via counit-unit adjunction *)
val tm53 = mk_imp (
  list_mk_conj [adjf5, catC, catD, funF, funG, nteta, nteps], adjf3) ;

(*
val tm53 = ``g_adjf5 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps /\
  category (idC,compC) /\ category (idD,compD) /\ 
  g_functor (idC,compC) (idD,compD) F' /\
  g_functor (idD,compD) (idC,compC) G /\
  g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
  g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) ==>
  g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps `` ;
*)

val g_adjf5_3 = store_thm ("g_adjf5_3", tm53,
  EVERY [ (REWRITE_TAC [g_adjf5_thm, g_adjf3_thm]),
    (REPEAT STRIP_TAC), EQ_TAC,
    (DISCH_THEN (fn th => REWRITE_TAC [GSYM th])), (farwmmp g_functorD) ]
  THENL [
    EVERY [ (farwmmp catDAss),
      (FIRST_X_ASSUM (CHANGED_TAC o 
        (fn th => REWRITE_TAC [g_I_thm, I_THM, th]) o REWRITE_RULE [o_THM] o
	  TY_BETA_RULE o REWRITE_RULE [g_oo_thm] o 
	  MATCH_MP (GSYM g_nattransfD))),
      (farwmmp catDRAss)],
    EVERY [ (farwmmp catDRAss),
      (FIRST_X_ASSUM (CHANGED_TAC o 
        (fn th => REWRITE_TAC [g_I_thm, I_THM, th]) o REWRITE_RULE [o_THM] o
	  TY_BETA_RULE o REWRITE_RULE [g_oo_thm] o MATCH_MP g_nattransfD)),
      (farwmmp catDAss)] ]
  THEN (ASM_REWRITE_TAC []) THEN (farwmmp categoryD) ) ;

val tm35 = list_mk_imp ([catC, catD, funF, funG, adjf3], adjf5) ;

val g_adjf3_5= store_thm ("g_adjf3_5", tm35,
  EVERY [ (REWRITE_TAC [g_adjf5_thm, g_adjf3_thm]),
    (REPEAT STRIP_TAC) THENL [ (ASM_REWRITE_TAC []), 
      (FIRST_ASSUM (fn th => CHANGED_TAC (REWRITE_TAC [GSYM th]))) ],
    (farwmmp g_functorD), (farwmmp categoryD) ]) ;

(* now to set out our adjoint functor results in the form in the paper *)
(* first, that the second and third parts of g_adjf4 are equivalent *)
(* check that adjf4a/b/c are right *)
val g_adjf4_chk = prove (mk_eq (adjf4, list_mk_conj [adjf4a, adjf4b, adjf4c]),
  REWRITE_TAC [g_adjf4_thm]) ;

fun usehs th = 
  let val (a1,a2) = EQ_IMP_RULE (SPEC_ALL (TY_SPEC_ALL th)) ;
    fun mk2 ti = DISCH_ALL (TY_GEN_ALL (GEN_ALL (GSYM (inst_eqs (GSYM ti))))) ;
    fun tac ui = FIRST_ASSUM (ASSUME_TAC o MATCH_MP ui) ;
  in MAP_EVERY (tac o mk2) [a1, a2] end ;

val g_adjf4_eqv = store_thm ("g_adjf4_eqv",
  list_mk_imp ([cats, adjf4a], mk_eq (adjf4b, adjf4c)),
  EVERY [REPEAT STRIP_TAC, (FIRST_ASSUM usehs), EQ_TAC, REPEAT STRIP_TAC]
  THENL [
    EVERY [ (ONCE_ASM_REWRITE_TAC []),
      (FIRST_X_ASSUM (fn th => EVERY [CHANGED_TAC (ONCE_REWRITE_TAC [th]),
	(ASM_REWRITE_TAC []), ASSUME_TAC (GSYM th)])),
      (farwmmp catDRAss), (ASM_REWRITE_TAC []),
      (farwmmp catDLU), (ASM_REWRITE_TAC []) ], 
    EVERY [ 
      (FIRST_X_ASSUM (fn th => MATCH_MP_TAC 
        ((fst o EQ_IMP_RULE o SPEC_ALL o TY_SPEC_ALL) th))),
      (FIRST_X_ASSUM (fn th => EVERY [CHANGED_TAC (ONCE_REWRITE_TAC [th]),
	(ASM_REWRITE_TAC []), ASSUME_TAC (GSYM th)])),
      (farwmmp catDAss), (ASM_REWRITE_TAC []),
      (farwmmp catDRU), (ASM_REWRITE_TAC []) ] ]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
val taf1 = list_mk_conj [funG, nteta, adjf1, eps, flatt, Feq] ;
val taf2 = list_mk_conj [funF, nteps, adjf2, eta, sharp, Geq] ;
val taf3 = list_mk_conj [funF, funG, adjf3, flatt, sharp] ;
val taf3' = list_mk_conj [funG, funF, adjf3, sharp, flatt] ;
val taf4 = list_mk_conj [adjf4, eta, eps, Feq, Geq] ;
val taf5 = list_mk_conj [funF, funG, nteta, nteps, adjf5, flatt, sharp] ;

val [g_adjf1e3, g_adjf3e1] = map (REWRITE_RULE [GSYM AND_IMP_INTRO])
  (ufdl ((fn (x,y) => [x,y]) o EQ_IMP_RULE) g_adjf13_equiv) ;
val [g_adjf2e3, g_adjf3e2] = map (REWRITE_RULE [GSYM AND_IMP_INTRO])
  (ufdl ((fn (x,y) => [x,y]) o EQ_IMP_RULE) g_adjf23_equiv) ;
val [g_adjf3e4, g_adjf4e3] = map (REWRITE_RULE [GSYM AND_IMP_INTRO])
  (ufdl ((fn (x,y) => [x,y]) o EQ_IMP_RULE) g_adjf34_equiv) ;

val adjf_thm_1_eq_3 = store_thm ("adjf_thm_1_eq_3",
  mk_imp (cats, mk_eq (taf1, taf3)),
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC ]
  THENL [
    EVERY [ REPEAT CONJ_TAC, TRY (FIRST_ASSUM ACCEPT_TAC),
      (frrc_rewr g_adjf1e3) ],
    EVERY [ 
      (FIRST_REP_RES (MAP_EVERY ASSUME_TAC o CONJUNCTS)
	(REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf3_nt)),
      REPEAT CONJ_TAC, TRY (FIRST_ASSUM ACCEPT_TAC),
      TRY (frrc_rewr g_adjf3e1), (* just one subgoal now *)
      (FIRST_REP_RES (ASSUME_TAC o CONJUNCT1) g_adjf3e1),
      (FIRST_REP_RES ASSUME_TAC 
	(REWRITE_RULE [adjf1_conds_thm, GSYM AND_IMP_INTRO] g_adjf1_Feq)),
      (CONV_TAC mk_exp_conv''),
      (FIRST_ASSUM MATCH_ACCEPT_TAC) ] ]) ;

val adjf_thm_2_eq_3 = store_thm ("adjf_thm_2_eq_3",
  mk_imp (cats', mk_eq (taf2, taf3')),
  EVERY [
    (CONV_TAC (ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV dual_convs)))),
    (REWRITE_TAC [g_oo_dual, g_I_dual]), DISCH_TAC,
    (FIRST_ASSUM (fn th => REWRITE_TAC [GSYM (MATCH_MP adjf_thm_1_eq_3 th)])),
    EQ_TAC, STRIP_TAC, ASM_REWRITE_TAC []]
  THENL [ (REWRITE_TAC [g_dual_functor_def, dual_comp_def]),
    (FIRST_X_ASSUM (fn th => MP_TAC th THEN CHANGED_TAC 
      (REWRITE_TAC [g_dual_functor_def, dual_comp_def]))) ]
  THEN EVERY [ POP_ASSUM_LIST (fn _ => ALL_TAC), TY_BETA_TAC, BETA_TAC]
  THENL [ REFL_TAC,
    (CONV_TAC mk_exp_conv'') THEN (SRW_TAC [] []) ]) ;

val adjf_thm_3_eq_4 = store_thm ("adjf_thm_3_eq_4",
  mk_imp (cats, mk_eq (taf3, taf4)),
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC ]
  THENL [
    EVERY [ REPEAT CONJ_TAC, TRY (FIRST_ASSUM ACCEPT_TAC),
      (frrc_rewr g_adjf3e4) ],
    EVERY [ REPEAT CONJ_TAC, TRY (FIRST_ASSUM ACCEPT_TAC),
      (frrc_rewr g_adjf4e3) ] ]) ;

val adjf_thm_3_eq_5 = store_thm ("adjf_thm_3_eq_5",
  mk_imp (cats, mk_eq (taf3, taf5)),
  EVERY [ STRIP_TAC, EQ_TAC, STRIP_TAC ]
  THENL [
    EVERY [ 
      (FIRST_REP_RES (MAP_EVERY ASSUME_TAC o CONJUNCTS)
	(REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf3_nt)),
      (frrc_rewr g_adjf3_5),
      REPEAT CONJ_TAC, (FIRST_X_ASSUM ACCEPT_TAC) ],
    EVERY [
      (FIRST_REP_RES ASSUME_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf5_3)),
      REPEAT CONJ_TAC, (FIRST_X_ASSUM ACCEPT_TAC) ]]) ;

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*) 

(* note - RES_CANON doesn't deal with ty-foralls properly *)

val tgs = TY_GEN_ALL (GEN_ALL FLATT_eps_I) ;
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
      ASSUME_TAC (MATCH_MP catDRU th) THEN
      ASM_REWRITE_TAC [(MATCH_MP catDRAss th)])) ]) ;

val jmjth = DISCH_ALL (TY_GEN_ALL (UNDISCH g_adjf3_jmj_lem)) ;

(* given adjoint functors, you have a monad *)
(* NOTE - where do we assume that eta is a natural transformation *)

val tmass = ``category (idC,compC) /\ g_functor (idD,compD) (idC,compC) G /\
  g_adjf1 (idC,compC) G eta sharp ==> 
  (sharp (compC (G (sharp h)) k) = compD (sharp h) (sharp k))`` ;

val g_adjf1_monad_lem = store_thm ("g_adjf1_monad_lem", tmass,
  EVERY [ STRIP_TAC,
    (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP g_adjf1D1)),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_functorD th])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [(MATCH_MP catDRAss th)])),
    (FIRST_X_ASSUM (fn th => REWRITE_TAC [MATCH_MP g_adjf1DGh th])) ]) ;

val gahe = DISCH_ALL (TY_GEN_ALL (UNDISCH g_adjf1_sharp_eta)) ;
val gaml = DISCH_ALL (TY_GEN_ALL (GEN_ALL (UNDISCH g_adjf1_monad_lem))) ;

val tmmon = ``category (idC,compC) /\ 
  g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G /\
  g_adjf1 [:'C,'D,'F,'G:] (idC,compC) G eta sharp ==> 
  Kmonad [:'C, 'F o 'G:] (idC,compC) (eta, \: 'a 'b. G o sharp)`` ;

val g_adjf1_IMP_Kmonad = store_thm ("g_adjf1_IMP_Kmonad", tmmon,
  EVERY [ (REWRITE_TAC [Kmonad_thm]),
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

(* note, in adjointScript.sml there is a proof that adjoint functors
  give a monad, in terms of the 7 rule definition of a monad,
  using g_adjf3_jmj_lem *)

(*
show_types := true ;
show_types := false ;
handle e => Raise e ;
set_goal ([], it) ;
val (sgs, goal) = top_goal () ;
*)
(* given a monad, you have adjoint functors ;
  results in KmonadTheory show that a monad gives:
  the Kleisli category is a category (Komonad_IMP_Kcat)
  ext is a functor from the Kleisli category (Komonad_IMP_ext_f)
  unit o _ is a functor into the Kleisli category (Komonad_IMP_uof) 
  unit is a natural transformation (Kmonad_IMP_unit_nt)
  *)
val Kmonad_IMP_adjf = store_thm ("Kmonad_IMP_adjf",
  ``Kmonad [:'A, 'M:] (id,comp) (unit,ext) ==> 
    g_adjf1 [:'A, ('A, 'M) Kleisli, I,'M :] (id,comp) ext unit (\: 'a 'b. I)``,
  EVERY [ (REWRITE_TAC [g_adjf1_def, Kmonad_thm]),
    (CONV_TAC (REDEPTH_CONV
      (REWR_CONV UNCURRY_DEF ORELSEC TY_BETA_CONV ORELSEC BETA_CONV))),
    REPEAT STRIP_TAC, (ASM_REWRITE_TAC [I_THM]),
    EQ_TAC, (MATCH_ACCEPT_TAC EQ_SYM) ]) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "g_adjoint";

val _ = export_theory();

end; (* structure g_adjointScript *)

