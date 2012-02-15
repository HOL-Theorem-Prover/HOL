(* $Id$ *)
(* Modified to show the improve rewriting and resolution tactics,
   and to provide type annotations for variables with universal types, by PVH *)
structure g_adjointScript =
struct

open HolKernel Parse boolLib bossLib

open categoryTheory KmonadTheory auxLib boolSimps ;
infix RS RSN ;
val UNCURRY_DEF = pairTheory.UNCURRY_DEF ;
val o_THM = combinTheory.o_THM ;
val o_DEF = combinTheory.o_DEF ;
val I_THM = combinTheory.I_THM ;

val combin_ss  = bool_ss ++ combinSimps.COMBIN_ss
val satisfy_ss = bool_ss ++ SatisfySimps.SATISFY_ss

val _ = set_trace "Unicode" 1;
val _ = set_trace "kinds" 0;

val _ = new_theory "g_adjoint";

(* 
load "g_adjointTheory" ; open g_adjointTheory ; 
load "auxLib" ; open auxLib ;
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
  ``g_adjf1 [:'C,'D, 'F, 'G:] (idC,compC) G eta sharp =
    (!: 'a 'b. (! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (sharp [:'a,'b:] f = g)))``,
  SRW_TAC [] [g_adjf1_def]) ;

val g_adjf2_thm = store_thm ("g_adjf2_thm",
  ``g_adjf2 [:'D,'C, 'G,'F:] (idD,compD) F' eps flatt =
    (!: 'b 'a. (! g (f : ('a, 'b 'G) 'C). 
      (compD eps (F' f) = g) = (flatt [:'b,'a:] g = f)))``, 
  SRW_TAC [] [g_adjf2_def]) ;

val g_adjf3_thm = store_thm ("g_adjf3_thm",
  ``g_adjf3 [:'C,'D, 'F,'G:] (idC,compC) (idD,compD) F' G eta eps =
    (!: 'a 'b. ! (f : ('a, 'b 'G) 'C) g. 
      (compC (G g) eta = f) = (compD eps (F' f) = g))``,
  SRW_TAC [] [g_adjf3_def]) ;

val exp_convs = [ TY_BETA_CONV, BETA_CONV,
  HO_REWR_CONV pairTheory.FORALL_PROD, REWR_CONV UNCURRY_DEF,
  REWR_CONV TY_FUN_EQ_THM, REWR_CONV FUN_EQ_THM ] ; 

val mk_exp_thm = CONV_RULE (REDEPTH_CONV (FIRST_CONV exp_convs)) ;

val g_adjf4_thm = save_thm ("g_adjf4_thm",
  TY_TM_SPEC_ALL (mk_exp_thm g_adjf4_def)) ;

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
  SIMP_TAC bool_ss [dual_comp_def, g_dual_functor_def, g_adjf3_thm]
  THEN EQ_TAC THEN ASM_SIMP_TAC bool_ss []) ;

val g_adjf12_dual = store_thm ("g_adjf12_dual",
  ``g_adjf2 [:'D,'C, 'G, 'F:] (idD,compD) F' eps flatt = 
    g_adjf1 [:'D C,'C C, 'G, 'F:] 
      (idD, dual_comp compD) (g_dual_functor F') eps flatt``,
  SIMP_TAC bool_ss [dual_comp_def, g_dual_functor_def, g_adjf1_thm, g_adjf2_thm]) ;

val g_adjf4_dual = store_thm ("g_adjf4_dual",
  ``g_adjf4 [:'C, 'D, 'F, 'G:] (idC,compC) (idD,compD) sharp flatt = 
    g_adjf4 [:'D C, 'C C, 'G, 'F:] 
      (idD, dual_comp compD) (idC, dual_comp compC) flatt sharp``,
  SIMP_TAC bool_ss [dual_comp_def, g_adjf4_thm]
  THEN EQ_TAC THEN REPEAT STRIP_TAC
  THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC)
  THEN ASM_REWRITE_TAC[]
) ;

val g_adjf1DGh = store_thm ("g_adjf1DGh", 
  ``g_adjf1 [:'C,'D, 'F,'G:] (idC, compC : 'C o_arrow) G
            (eta : ('C, I, 'F o 'G) g_nattransf) sharp ==>
    (!:'a 'b. !f. compC (G (sharp [:'a,'b:] f)) eta = f)``,
  STRIP_TAC
  THEN IMP_RES_TAC g_adjf1_thm
  THEN ASM_REWRITE_TAC []
) ;

val adjf1_conds_def = Define `adjf1_conds = \:'C 'D 'F 'G. 
  \ (idC, compC) (idD,compD) eta (F': ('C,'D,'F) g_functor) 
    (G : ('D,'C,'G) g_functor). 
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
  SRW_TAC [] [adjf1_conds_def]) ;

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
  ``EPS [:'C, 'D:] (idC, compC) (sharp : ('C,'D, 'F,'G) g_sharp) =
    (\:'e. sharp [:'e 'G, 'e:] idC)``,
  SRW_TAC [] [EPS_def]) ;

val ETA_thm = store_thm ("ETA_thm",
  ``ETA [:'D, 'C:] (idD, compD) (flatt : ('D,'C, 'G,'F) g_flatt) =
    (\:'e. flatt [:'e 'F, 'e:] idD)``,
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
  ``FLATT [:'D, 'C:] (idC, compC)
          (G : ('D, 'C, 'G) g_functor) (eta : ('C, I, 'F o 'G) g_nattransf) =
    (\:'b 'a. \g : ('a 'F, 'b) 'D. compC (G g) eta)``,
  SRW_TAC [] [FLATT_def]) ;

val SHARP_thm = store_thm ("SHARP_thm",  
  ``SHARP [:'C, 'D:] (idD, compD)
          (F' : ('C, 'D, 'F) g_functor) (eps : ('D, 'G o 'F, I) g_nattransf) =
    (\:'a 'b. \f : ('a, 'b 'G) 'C. compD eps (F' f))``,
  SRW_TAC [] [SHARP_def]) ;

(* parsing ETA_EPS_dual and SHARP_FLATT_dual requires _both_ type arguments *)

val ETA_EPS_dual = store_thm ("ETA_EPS_dual",
  ``(ETA [:'D, 'C:] ((idD, compD) : 'D category)
         (flatt : ('D,'C, 'G,'F) g_flatt) =
    (EPS [:'D C, 'C C:] (idD, dual_comp compD) flatt))``,
  SIMP_TAC bool_ss [ETA_thm, EPS_def, UNCURRY_DEF]) ;

val EPS_ETA_dual = store_thm ("EPS_ETA_dual",
  ``(EPS [:'C, 'D:] ((idC, compC) : 'C category)
         (sharp : ('C,'D, 'F,'G) g_sharp) =
    (ETA [:'C C, 'D C:] (idC, dual_comp compC) sharp))``,
  SIMP_TAC bool_ss [ETA_def, EPS_thm, UNCURRY_DEF]) ;

val SHARP_FLATT_dual = store_thm ("SHARP_FLATT_dual",
  ``SHARP [:'C, 'D:] (idD,compD)
          (F' : ('C, 'D, 'F) g_functor) (eps : ('D, 'G o 'F, I) g_nattransf) =
    FLATT [:'C C, 'D C:] (idD, dual_comp compD) (g_dual_functor F') eps``,
  SIMP_TAC bool_ss [SHARP_thm, FLATT_def, dual_comp_def, g_dual_functor_def, UNCURRY_DEF]) ;

val FLATT_SHARP_dual = store_thm ("FLATT_SHARP_dual",
  ``FLATT [:'D, 'C:] (idC,compC)
          (G : ('D, 'C, 'G) g_functor) (eta : ('C, I, 'F o 'G) g_nattransf) =
    SHARP [:'D C, 'C C:] (idC, dual_comp compC) (g_dual_functor G) eta``,
  SIMP_TAC bool_ss [SHARP_def, FLATT_thm, dual_comp_def, g_dual_functor_def, UNCURRY_DEF]) ;

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

val g_adjf1_sharp_comp = store_thm ("g_adjf1_sharp_comp", tmhc,
  REWRITE_TAC [adjf1_conds_thm]
  THEN STRIP_TAC
  THEN FIRST_REP_RES MATCH_MP_TAC g_adjf1D1
  THEN FIRST_REP_RES REWRITE_THM g_functorD
  THEN FIRST_REP_RES REWRITE_THM catDRAss
  THEN FIRST_REP_RES MP_TAC g_nattransfD
  THEN SIMP_TAC combin_ss [g_oo_thm, g_I_def]
  THEN DISCH_TAC
  THEN FIRST_REP_RES REWRITE_THM categoryD
  THEN FIRST_REP_RES REWRITE_THM g_adjf1DGh
) ;


val tmhe =
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
    g_adjf1 (idC, compC) G eta sharp ==> (compD (sharp idC) (F' f) = sharp f)`` ;

val g_adjf1_sharp_eq = store_thm ("g_adjf1_sharp_eq", tmhe,
  STRIP_TAC
  THEN IMP_RES_TAC (GSYM g_adjf1_sharp_comp)
  THEN ASM_REWRITE_TAC []
  THEN IMP_RES_TAC adjf1_conds_thm
  THEN IMP_RES_THEN REWRITE_THM catDLU
) ;


val g_adjf1_sharp_eta = store_thm ("g_adjf1_sharp_eta", 
  ``category (idC,compC) /\
    g_functor (idD,compD) (idC,compC) (G : ('D, 'C, 'G) g_functor) /\
    g_adjf1 (idC, compC) G
            (eta : ('C, I, 'F o 'G) g_nattransf)
            (sharp : ('C, 'D, 'F, 'G) g_sharp) ==> 
    (sharp [:'a, 'a 'F:] (eta [:'a:]) = idD [:'a 'F:])``,
  STRIP_TAC
  THEN FIRST_REP_RES MATCH_MP_TAC g_adjf1D1
  THEN FIRST_REP_RES REWRITE_THM g_functorD
  THEN FIRST_REP_RES MATCH_ACCEPT_TAC catDLU
) ;


val tmfc = 
  ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
    category (idD, compD) /\ g_adjf1 (idC, compC) G eta sharp ==>
    (!:'a 'b. !f. F' [:'a,'b:] f = sharp (compC eta f))`` ;

val g_adjf1_Feq = store_thm ("g_adjf1_Feq", tmfc, 
  STRIP_TAC
  THEN IMP_RES_TAC g_adjf1_sharp_comp
  THEN IMP_RES_TAC adjf1_conds_thm
  THEN IMP_RES_TAC g_adjf1_sharp_eta
  THEN ASM_REWRITE_TAC []
  THEN IMP_RES_THEN REWRITE_THM catDLU
) ;


val g_adjf1_Feq_exp = SIMP_RULE bool_ss [UNCURRY_DEF,adjf1_conds_def] g_adjf1_Feq ;

val tmfee = mk_imp 
  (list_mk_conj [catC, catD, funG, adjf1], mk_eq (Feq, nteta)) ;

val g_adjf1_Feq_nt = store_thm ("g_adjf1_Feq_nt", tmfee,
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
  THEN ASM_SIMP_TAC combin_ss [g_nattransf_thm, g_oo_thm, g_I_def]
  THENL
    [ IMP_RES_THEN MATCH_ACCEPT_TAC g_adjf1DGh,
      SIMP_TAC bool_ss [TY_FUN_EQ_THM, FUN_EQ_THM]
      THEN MATCH_MP_TAC g_adjf1_Feq_exp
      THEN ASM_REWRITE_TAC []
    ]
) ;

val tmff  =
``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  category (idD, compD) /\ g_adjf1 (idC, compC) G eta sharp ==> 
  g_functor (idC,compC) (idD,compD) F'`` ;

val g_adjf1_F_fun = store_thm ("g_adjf1_F_fun", tmff,
  STRIP_TAC
  THEN IMP_RES_TAC g_adjf1_Feq
  THEN ASM_REWRITE_TAC [g_functor_thm]
    (* delete category (idD,compD) *)
  THEN FIRST_X_ASSUM (fn th => (MATCH_MP categoryD th ; ALL_TAC))
  THEN REPEAT STRIP_TAC
  THEN IMP_RES_THEN MATCH_MP_TAC g_adjf1D1
  THEN MAP_EVERY IMP_RES_TAC [adjf1_conds_thm, g_functorD, category_thm]
  THEN ASM_REWRITE_TAC []
  THEN MAP_EVERY (FIRST_REP_RES REWRITE_THM)
    [catDRAss,g_adjf1DGh,catDAss,g_adjf1DGh]
);

val sharp_flatt_inv_defs = store_thm ("sharp_flatt_inv_defs",
  ``(category (idD,compD) /\ g_functor [:'C,'D,'F:] (idC,compC) (idD,compD) F' ==> 
      ((eps : ('D, 'G o 'F, I) g_nattransf) = EPS (idC,compC) (SHARP (idD,compD) F' eps))) /\ 
    (category (idC,compC) /\ g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G ==> 
      ((eta : ('C, I, 'F o 'G) g_nattransf) = ETA (idD,compD) (FLATT (idC,compC) G eta)))``,
  SIMP_TAC (bool_ss ++ ETA_ss)
           [SHARP_def, FLATT_def, EPS_thm, ETA_thm, 
            g_functor_def, category_def, UNCURRY_DEF] ) ;

val [sharp_inv_def, flatt_inv_def] = CONJUNCTS sharp_flatt_inv_defs ;

val tmd = ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta sharp ==> 
  (sharp = SHARP (idD,compD) F' (EPS (idC,compC) sharp))`` ;

val g_adjf1_IMP_defs = store_thm ("g_adjf1_IMP_defs", tmd,
  STRIP_TAC
  THEN MATCH_MP_TAC EQ_SYM
  THEN IMP_RES_TAC g_adjf1_sharp_eq
  THEN SRW_TAC [] [SHARP_def, EPS_thm]
  THEN CONV_TAC (TOP_DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
  THEN REFL_TAC
) ;

val tment =
``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
  g_adjf1 (idC,compC) G eta sharp ==> 
  g_nattransf (idD,compD) (EPS (idC,compC) sharp) (F' g_oo G) (g_I [:'D:])`` ;

val g_adjf1_eta_nt = store_thm ("g_adjf1_eta_nt", tment, 
  SRW_TAC [] [g_nattransf_def, EPS_thm, g_oo_thm, g_I_def, o_DEF]
  THEN IMP_RES_TAC g_adjf1_sharp_eq
  THEN ASM_REWRITE_TAC []
  THEN IMP_RES_TAC adjf1_conds_thm
  THEN FIRST_REP_RES (MATCH_MP_TAC o GSYM) g_adjf1D1
  THEN MAP_EVERY (FIRST_REP_RES REWRITE_THM) 
    [g_functorD,catDRAss,g_adjf1DGh,catDRU]
) ;

val tm13 = ``adjf1_conds [:'C, 'D, 'F, 'G:] (idC, compC) (idD,compD) eta F' G /\
       g_adjf1 (idC, compC) G eta sharp ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G eta (EPS (idC, compC) sharp)`` ;

val g_adjf1_3 = store_thm ("g_adjf1_3", tm13,
  SIMP_TAC satisfy_ss [g_adjf3_thm, EPS_thm, g_adjf1_sharp_eq, g_adjf1D]) ;

(* prove g_adjf2_3 by duality from g_adjf1_3 *)
val tm23 = ``g_nattransf (idD,compD) (eps : ('D, 'G o 'F, I) g_nattransf)
                         ((F':('C, 'D, 'F) g_functor) g_oo (G:('D, 'C, 'G) g_functor))
                         (g_I [:'D:]) /\
       category (idD,compD) /\ g_functor (idC,compC) (idD,compD) F' /\
       g_adjf2 (idD, compD) F' eps flatt ==> 
       g_adjf3 (idC, compC) (idD,compD) F' G (ETA (idD, compD) flatt) eps`` ;

val g_adjf2_3 = store_thm ("g_adjf2_3", tm23,
  REWRITE_TAC [g_adjf12_dual]
  THEN STRIP_TAC
  THEN CONV_TAC (REWR_CONV g_adjf3_dual)
  THEN REWRITE_TAC [ETA_EPS_dual]
  THEN MATCH_MP_TAC g_adjf1_3
  THEN ASM_SIMP_TAC bool_ss [adjf1_conds_def,UNCURRY_DEF,
                             GSYM g_functor_dual,GSYM category_dual]
  THEN IMP_RES_THEN MP_TAC g_nattransf_dual
  THEN REWRITE_TAC [g_I_dual, g_oo_dual]
) ;

val g_adjf3_1 = store_thm ("g_adjf3_1",
  ``g_adjf3 [:'C,'D, 'F,'G:] (idC, compC) (idD,compD) F' G eta eps =
    g_adjf1 (idC, compC) G eta (SHARP (idD,compD) F' eps)``,
  SIMP_TAC bool_ss [g_adjf3_thm, g_adjf1_thm, SHARP_def, UNCURRY_DEF]
) ;

val g_adjf3_2 = store_thm ("g_adjf3_2",
  ``g_adjf3 (idC, compC) (idD,compD)
            (F':('C, 'D, 'F) g_functor) (G:('D, 'C, 'G) g_functor) eta eps =
    g_adjf2 (idD,compD) F' eps (FLATT (idC, compC) G eta)``,
  SIMP_TAC bool_ss [g_adjf3_thm, g_adjf2_thm, FLATT_def, UNCURRY_DEF]
  THEN EQ_TAC THEN DISCH_THEN REWRITE_THM
) ;

val g_adjf1_2 = save_thm ("g_adjf1_2", REWRITE_RULE [g_adjf3_2] g_adjf1_3) ;

val SHARP_eta_I = store_thm ("SHARP_eta_I", 
  ``g_adjf3 (idC,compC) (idD,compD)
            (F':('C, 'D, 'F) g_functor) (G:('D, 'C, 'G) g_functor)
            (eta : ('C, I, 'F o 'G) g_nattransf)
            (eps : ('D, 'G o 'F, I) g_nattransf) /\
    category (idC, compC) /\ g_functor (idD,compD) (idC,compC) G ==> 
    (compD eps (F' eta) = idD)``,
  STRIP_TAC
  THEN FIRST_REP_RES MATCH_MP_TAC g_adjf3D1
  THEN MAP_EVERY (FIRST_REP_RES REWRITE_THM) [g_functorD,catDLU]
) ;

val FLATT_eps_I = store_thm ("FLATT_eps_I", 
  ``g_adjf3 (idC,compC) (idD,compD)
            (F':('C, 'D, 'F) g_functor) (G:('D, 'C, 'G) g_functor)
            (eta : ('C, I, 'F o 'G) g_nattransf)
            (eps : ('D, 'G o 'F, I) g_nattransf) /\
    category (idD, compD) /\ g_functor (idC,compC) (idD,compD) F' ==>
    (compC (G eps) eta = idC)``,
  STRIP_TAC
  THEN FIRST_REP_RES MATCH_MP_TAC g_adjf3D2
  THEN MAP_EVERY (FIRST_REP_RES REWRITE_THM) [g_functorD,catDRU]
) ;

(* this is the actual formulation of the equivalence of two
  characterisations of adjoint functors *)

(* problem with using this first one, the type constructor variable
  of functor G does not match, and in g_adjf1_F_fun there is a free
  variable in the premises, not in the conclusion, and when this happens,
  MATCH_MP_TAC produces existential goal for terms, but not for types *)

val tm13e = mk_imp (list_mk_conj [catC, catD, funG, nteta],
  mk_eq (mk_conj (adjf1, eps), list_mk_conj [adjf3, funF, nteps, sharp])) ;

val g_adjf13_equiv = store_thm ("g_adjf13_equiv", tm13e,
  STRIP_TAC
  THEN EQ_TAC
  THEN STRIP_TAC
  THENL
    [ REPEAT CONJ_TAC
      THEN ASM_REWRITE_TAC []
      THENL
        [ MATCH_MP_TAC g_adjf1_3,
          MATCH_MP_TAC g_adjf1_F_fun,
          MATCH_MP_TAC g_adjf1_eta_nt,
          MATCH_MP_TAC g_adjf1_IMP_defs
        ]
      THEN ASM_SIMP_TAC bool_ss [UNCURRY_DEF,adjf1_conds_def],

      REPEAT CONJ_TAC
      THEN ASM_REWRITE_TAC []
      THENL
        [ ASM_REWRITE_TAC [GSYM g_adjf3_1],
          IMP_RES_TAC (GSYM sharp_flatt_inv_defs)
          THEN ASM_REWRITE_TAC []
        ]
    ]
) ;

(* get directly from g_adjf3 /\ F',G functors that eps and eta are nts *)
val tm3nt = mk_imp (list_mk_conj [adjf3, catC, catD, funF, funG],
  mk_conj (nteta, nteps)) ;

val g_adjf3_nt = store_thm ("g_adjf3_nt", tm3nt,
  STRIP_TAC
  THEN MAP_EVERY IMP_RES_TAC [g_functorD, catDLU, catDRU]
  THEN SRW_TAC [] [g_nattransf_def, g_oo_def, g_I_def]
  THENL
    [ FIRST_REP_RES MATCH_MP_TAC g_adjf3D2
      THEN ASM_REWRITE_TAC []
      THEN IMP_RES_THEN REWRITE_THM catDAss
      THEN FIRST_REP_RES_MKI ASM_REWRITE_THM SHARP_eta_I,

      FIRST_REP_RES MATCH_MP_TAC (GSYM g_adjf3D1)
      THEN ASM_REWRITE_TAC []
      THEN IMP_RES_THEN REWRITE_THM catDRAss
      THEN FIRST_REP_RES_MKI ASM_REWRITE_THM FLATT_eps_I
    ]
) ;
     
val dual_convs = 
  [g_adjf3_dual, g_adjf12_dual, ETA_EPS_dual, EPS_ETA_dual, 
     FLATT_SHARP_dual, SHARP_FLATT_dual,
     g_functor_dual, g_nattransf_dual, category_dual] ;

(* get link between g_adjf2 and g_adjf3 by duality *)

val tm23e = mk_imp (list_mk_conj [catD, catC, funF, nteps],
  mk_eq (mk_conj (adjf2, eta), list_mk_conj [adjf3, funG, nteta, flatt])) ;

val g_adjf23_equiv = store_thm ("g_adjf23_equiv", tm23e,
  ONCE_REWRITE_TAC dual_convs
  THEN SIMP_TAC bool_ss [g_oo_dual, g_I_dual, g_adjf13_equiv]) ;

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

fun usega th = (CHANGED_TAC (REWRITE_TAC [th]) THEN
  STRIP_ASSUME_TAC th) ;

val g_adjf12_equiv = store_thm ("g_adjf12_equiv", tm12e,
  STRIP_TAC
  THEN EQ_TAC
  THEN STRIP_TAC
  THENL
    [ FIRST_REP_RES_MKI usega ga13' THEN FIRST_REP_RES_MKI usega ga32',
      FIRST_REP_RES_MKI usega ga23' THEN FIRST_REP_RES_MKI usega ga31' ]) ;

val tm43 = mk_imp (list_mk_conj [adjf4, catC, catD, eta, eps, Feq, Geq],
  list_mk_conj [funF, funG, nteta, nteps, adjf3, sharp, flatt]) ;

val g_adjf4_3 = store_thm ("g_adjf4_3", tm43,
  STRIP_TAC
  THEN MAP_EVERY IMP_RES_TAC [catDLU,catDRU]
  THEN SRW_TAC [] [g_adjf3_thm, ETA_thm, EPS_thm, SHARP_thm, FLATT_thm,
                   g_functor_thm, g_nattransf_thm]
  THENL [
    (* F' and G functors *)
    IMP_RES_THEN MATCH_MP_TAC g_adjf4D_eqv1 THEN REFL_TAC,

    IMP_RES_THEN (REWRITE_THM o GSYM) g_adjf4D_sharp
    THEN IMP_RES_THEN REWRITE_THM catDAss,

    IMP_RES_THEN MATCH_MP_TAC g_adjf4D_eqv2 THEN REFL_TAC,

    IMP_RES_THEN (REWRITE_THM o GSYM) g_adjf4D_flatt
    THEN IMP_RES_THEN REWRITE_THM catDAss,

    (* eta and eps are natural transformations *)
    (*
    e (REWRITE_TAC [g_oo_def, o_DEF]) ; (* does nothing - why ?? *) (* PVH: Now it does *)
    *)
    ASM_SIMP_TAC combin_ss [g_oo_def, g_I_def]
    THEN IMP_RES_THEN (fn th => ASM_REWRITE_TAC[GSYM th]) g_adjf4D_flatt
    THEN IMP_RES_THEN MATCH_MP_TAC g_adjf4D_eqv2 THEN REFL_TAC,

    ASM_SIMP_TAC combin_ss [g_oo_def, g_I_def]
    THEN IMP_RES_THEN (fn th => ASM_REWRITE_TAC[GSYM th]) g_adjf4D_sharp
    THEN IMP_RES_THEN (MATCH_MP_TAC o GSYM) g_adjf4D_eqv1 THEN REFL_TAC,

    (* finally, the equivalence condition, g_adjf3 *)
    IMP_RES_THEN (REWRITE_THM o GSYM) g_adjf4D_flatt
    THEN IMP_RES_THEN (fn th => ASM_REWRITE_TAC[GSYM th]) g_adjf4D_sharp
    THEN IMP_RES_THEN MATCH_ACCEPT_TAC g_adjf4D_eqv,

    IMP_RES_THEN (fn th => ASM_REWRITE_TAC[GSYM th]) g_adjf4D_sharp
    THEN CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
    THEN REFL_TAC,

    IMP_RES_THEN (fn th => ASM_REWRITE_TAC[GSYM th]) g_adjf4D_flatt
    THEN CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
    THEN REFL_TAC ]) ;

val tm34 =
``g_adjf3 [:'C,'D:] (idC,compC) (idD,compD)
                     (F':('C, 'D, 'F) g_functor) (G:('D, 'C, 'G) g_functor)
                     eta eps /\
       category (idC,compC) /\ category (idD,compD) /\ 
       g_functor (idC,compC) (idD,compD) F' /\
       g_functor (idD,compD) (idC,compC) G ==>
  g_adjf4 [:'C, 'D:] (idC,compC) (idD,compD) 
    (SHARP (idD,compD) F' eps) (FLATT (idC, compC) G eta)`` ;

val g_adjf3_4 = store_thm ("g_adjf3_4", tm34,
  STRIP_TAC
  THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SHARP_eta_I)
  THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] FLATT_eps_I)
  THEN MAP_EVERY IMP_RES_TAC [g_functor_thm,catDLU,catDRU]
  THEN SRW_TAC [] [g_adjf4_thm, SHARP_thm, FLATT_thm]
  THENL (* 3 subgoals *)
    [ IMP_RES_THEN MATCH_ACCEPT_TAC g_adjf3D,

      IMP_RES_THEN REWRITE_THM catDRAss
      THEN REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC)
      THEN IMP_RES_THEN ASM_REWRITE_THM catDAss,

      IMP_RES_THEN REWRITE_THM catDAss
      THEN REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC)
      THEN IMP_RES_THEN ASM_REWRITE_THM catDRAss
    ]) ;

val tm34e = ``category (idC,compC) /\ category (idD,compD) ==> 
  (g_adjf3 [:'C,'D:] (idC,compC) (idD,compD)
                     (F':('C, 'D, 'F) g_functor) (G:('D, 'C, 'G) g_functor)
           eta eps /\
    g_functor (idC,compC) (idD,compD) F' /\
    g_functor (idD,compD) (idC,compC) G /\
    (sharp = SHARP (idD,compD) F' eps) /\ (flatt = FLATT (idC, compC) G eta) =
  g_adjf4 [:'C, 'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ (eps = EPS (idC,compC) sharp) /\
    (F' = (\:'a 'b. (\f. sharp (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt (compD g eps))))) `` ;

val g_adjf34_equiv = store_thm ("g_adjf34_equiv", tm34e,
  STRIP_TAC
  THEN EQ_TAC
  THEN STRIP_TAC
  THENL
    [ IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] g_adjf3_4)
      THEN ASM_REWRITE_TAC []
      THEN MAP_EVERY IMP_RES_TAC [g_functorD,catDLU,catDRU]
      THEN REPEAT CONJ_TAC
      THENL (* 4 subgoals *)
        [ MATCH_MP_TAC flatt_inv_def THEN ASM_REWRITE_TAC [],

          MATCH_MP_TAC sharp_inv_def THEN ASM_REWRITE_TAC [],

          SRW_TAC [] [SHARP_thm]
          THEN IMP_RES_THEN REWRITE_THM catDAss
          THEN USE_LIM_RES_TAC ASM_REWRITE_THM SHARP_eta_I
          THEN CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
          THEN REFL_TAC,

          SRW_TAC [] [FLATT_thm]
          THEN IMP_RES_THEN REWRITE_THM catDRAss
          THEN USE_LIM_RES_TAC ASM_REWRITE_THM FLATT_eps_I
          THEN CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
          THEN REFL_TAC
        ],

      USE_LIM_RES_TAC REWRITE_THM g_adjf4_3
    ]) ;

(* observe that from g_adjf4 we prove that eta and eps are nts,
  but we don't use this to get back to g_adjf4 from g_adjf3 ;
  thus it follows that g_adjf3 implies that eta and eps are nts,
  which is proved directly in g_adjf3nt *) 

(* type-checking this fails (* PVH: now it works *), with a very strange message, namely 
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
  (g_adjf1 [:'C,'D, 'F,'G:] (idC,compC) G
                     (eta : ('C, I, 'F o 'G) g_nattransf) sharp /\
    g_functor (idD,compD) (idC,compC) G /\
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:])
                       (G g_oo (F' : ('C, 'D, 'F) g_functor)) /\ 
    (flatt = FLATT (idC, compC) G eta) = 
  g_adjf4 [:'C,'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ (eps = EPS (idC,compC) sharp) /\
    (F' = (\:'a 'b. (\f. sharp [:'a, 'b 'F:] (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt [:'b, 'a 'G:] (compD g eps)))))``  ;

*)

(* there must be an easier way than this !! *) (* PVH: trying another way after this *)
(*
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
*)

val tm14e = ``category (idC,compC) /\ category (idD,compD) ==>
  (g_adjf1 [:'C,'D:] (idC,compC) (G:('D, 'C, 'G) g_functor)
                     (eta : ('C, I, 'F o 'G) g_nattransf) sharp /\
    g_functor (idD,compD) (idC,compC) G /\
    g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:])
                       (G g_oo (F' : ('C, 'D, 'F) g_functor)) /\ 
    (flatt = FLATT (idC, compC) G eta) = 
  g_adjf4 [:'C,'D:] (idC,compC) (idD,compD) sharp flatt /\
    (eta = ETA (idD,compD) flatt) /\ 
    (F' = (\:'a 'b. (\f. sharp (compC eta f)))) /\
    (G = (\:'a 'b. (\g. flatt (compD g (EPS (idC,compC) sharp))))))`` ;

val EPS = ``EPS [:'C, 'D:] (idC,compC) (sharp: ('C,'D, 'F,'G)g_sharp)``
val ETA = ``ETA [:'D, 'C:] (idC,compC) (flatt: ('D,'C, 'G,'F)g_flatt)``
val g_adjf1_eq3'' = REWRITE_RULE[GSYM AND_IMP_INTRO]
                     (MATCH_MP (DECIDE ``(a ==> (b /\ c = d)) ==> (b ==> a ==> c ==> d)``)
                               g_adjf13_equiv)
val g_adjf3_eq4'' = REWRITE_RULE[GSYM AND_IMP_INTRO]
                     (MATCH_MP (DECIDE ``(a ==> (b /\ c = d)) ==> (b ==> c ==> a ==> d)``)
                               g_adjf34_equiv)

val hyps = strip_conj (fst (dest_imp (concl g_adjf4_3)))
val theta = foldl (fn (e,tht) => (lhs e |-> subst tht (rhs e)) :: tht
                                 handle HOL_ERR _ => tht) [] hyps
val g43' = REWRITE_RULE[GSYM AND_IMP_INTRO] (INST theta g_adjf4_3)

val g_adjf3_eq1' = REWRITE_RULE[GSYM AND_IMP_INTRO]
                     (MATCH_MP (DECIDE ``(a ==> (b = d)) ==> (b ==> a ==> d)``)
                               (GSYM g_adjf13_equiv))

(* note that the second and third conditions in g_adjf4 are equivalent,
  in the presence of the first condition - TO BE PROVED *)
val g_adjf14_equiv = store_thm ("g_adjf14_equiv", tm14e,
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL
    [ ASSUME_TAC (REFL EPS)
      THEN USE_LIM_RES_TAC STRIP_ASSUME_TAC g_adjf1_eq3''
      THEN USE_LIM_RES_TAC STRIP_ASSUME_TAC g_adjf3_eq4''
      THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,

      USE_LIM_RES_TAC (STRIP_ASSUME_TAC o GSYM) g43'
      THEN FULL_SIMP_TAC simpLib.empty_ss []
      THEN USE_LIM_RES_TAC STRIP_ASSUME_TAC (GSYM g_adjf3_eq1')
      THEN REPEAT CONJ_TAC
      THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC)
    ]) ;

(* assumptions of this theorem are the definition of adjoint pair
  currently (Jan 2010) on Wikipedia, under the heading
  Definition via counit-unit adjunction *)
val tm53 = mk_imp (
  list_mk_conj [adjf5, catC, catD, funF, funG, nteta, nteps], adjf3) ;

(*
val tm53 =
``g_adjf5 [:'C,'D, 'F,'G:] (idC,compC) (idD,compD) F' G eta eps /\
  category (idC,compC) /\ category (idD,compD) /\ 
  g_functor (idC,compC) (idD,compD) F' /\
  g_functor (idD,compD) (idC,compC) G /\
  g_nattransf [:'C:] (idC, compC) eta (g_I [:'C:]) (G g_oo F') /\ 
  g_nattransf (idD,compD) eps (F' g_oo G) (g_I [:'D:]) ==>
  g_adjf3 [:'C,'D:] (idC,compC) (idD,compD) F' G eta eps `` ;
*)

val g_adjf5_3 = store_thm ("g_adjf5_3", tm53,
  REWRITE_TAC [g_adjf5_thm, g_adjf3_thm]
  THEN REPEAT STRIP_TAC
  THEN EQ_TAC
  THEN DISCH_THEN (REWRITE_THM o GSYM)
  THEN farwmmp g_functorD
  THENL
    [ farwmmp catDAss
      THEN IMP_RES_THEN (REWRITE_THM o SIMP_RULE combin_ss [g_oo_thm,g_I_def])
                        (GSYM g_nattransfD)
      (* PVH: why doesn't the simplifier do g_I_thm? *)
      THEN farwmmp catDRAss,

      farwmmp catDRAss
      THEN IMP_RES_THEN (REWRITE_THM o SIMP_RULE combin_ss [g_oo_thm,g_I_def])
                        g_nattransfD
      THEN farwmmp catDAss
    ]
  THEN ASM_REWRITE_TAC []
  THEN farwmmp categoryD
) ;

val tm35 = list_mk_imp ([catC, catD, funF, funG, adjf3], adjf5) ;

val g_adjf3_5= store_thm ("g_adjf3_5", tm35,
  SRW_TAC [] [g_adjf5_thm, g_adjf3_thm]
  THENL [ ALL_TAC, FIRST_ASSUM (REWRITE_THM o GSYM) ]
  THEN farwmmp g_functorD
  THEN farwmmp categoryD
) ;

(* now to set out our adjoint functor results in the form in the paper *)
(* first, that the second and third parts of g_adjf4 are equivalent *)
(* check that adjf4a/b/c are right *)
val g_adjf4_chk = prove (mk_eq (adjf4, list_mk_conj [adjf4a, adjf4b, adjf4c]),
  REWRITE_TAC [g_adjf4_thm]) ;

fun usehs th = 
  let val (a1,a2) = EQ_IMP_RULE (TY_TM_SPEC_ALL th) ;
    fun mk2 ti = DISCH_ALL (TY_TM_GEN_ALL (GSYM (inst_eqs (GSYM ti)))) ;
    fun tac ui = FIRST_ASSUM (ASSUME_TAC o MATCH_MP ui) ;
  in MAP_EVERY (tac o mk2) [a1, a2] end ;

val g_adjf4_eqv = store_thm ("g_adjf4_eqv",
  list_mk_imp ([cats, adjf4a], mk_eq (adjf4b, adjf4c)),
  REPEAT STRIP_TAC
  THEN FIRST_ASSUM usehs
  THEN EQ_TAC
  THEN REPEAT STRIP_TAC
  THENL
    [ ONCE_ASM_REWRITE_TAC []
      THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]
                               THEN ASM_REWRITE_TAC []
                               THEN ASSUME_TAC (GSYM th))
      THEN farwmmp catDRAss
      THEN ASM_REWRITE_TAC []
      THEN farwmmp catDLU
      THEN ASM_REWRITE_TAC [],

      FIRST_X_ASSUM (MATCH_MP_TAC o fst o EQ_IMP_RULE o TY_TM_SPEC_ALL)
      THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]
                               THEN ASM_REWRITE_TAC []
                               THEN ASSUME_TAC (GSYM th))
      THEN farwmmp catDAss
      THEN ASM_REWRITE_TAC []
      THEN farwmmp catDRU
      THEN ASM_REWRITE_TAC []
    ]
) ;

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
  STRIP_TAC
  THEN EQ_TAC
  THEN STRIP_TAC
  THENL
    [ REPEAT CONJ_TAC
      THEN TRY (FIRST_ASSUM ACCEPT_TAC)
      THEN frrc_rewr g_adjf1e3,

      IMP_RES_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf3_nt)
      THEN REPEAT CONJ_TAC
      THEN TRY (FIRST_ASSUM ACCEPT_TAC)
      THEN TRY (frrc_rewr g_adjf3e1) (* just one subgoal now *)
      THEN FIRST_REP_RES (ASSUME_TAC o CONJUNCT1) g_adjf3e1
      THEN IMP_RES_TAC (REWRITE_RULE [adjf1_conds_thm, GSYM AND_IMP_INTRO] g_adjf1_Feq)
      THEN POP_ASSUM (REWRITE_THM o GSYM)
      THEN CONV_TAC (TOP_DEPTH_CONV (ETA_CONV ORELSEC TY_ETA_CONV))
      THEN REFL_TAC
    ]
) ;

val adjf_thm_2_eq_3 = store_thm ("adjf_thm_2_eq_3",
  mk_imp (cats', mk_eq (taf2, taf3')),
  ONCE_REWRITE_TAC dual_convs
  THEN REWRITE_TAC [g_oo_dual, g_I_dual]
  THEN DISCH_TAC
  THEN FIRST_ASSUM (REWRITE_THM o GSYM o MATCH_MP adjf_thm_1_eq_3)
  THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
  THENL [ ALL_TAC, POP_ASSUM MP_TAC ]
  THEN REWRITE_TAC [g_dual_functor_def, dual_comp_def]
  THEN SIMP_TAC bool_ss []
  THEN CONV_TAC mk_exp_conv''
  THEN SIMP_TAC bool_ss []
) ;

val adjf_thm_3_eq_4 = store_thm ("adjf_thm_3_eq_4",
  mk_imp (cats, mk_eq (taf3, taf4)),
  STRIP_TAC
  THEN EQ_TAC
  THEN REPEAT STRIP_TAC
  THEN TRY (FIRST_ASSUM ACCEPT_TAC)
  THEN (frrc_rewr g_adjf3e4 ORELSE frrc_rewr g_adjf4e3)
) ;

val adjf_thm_3_eq_5 = store_thm ("adjf_thm_3_eq_5",
  mk_imp (cats, mk_eq (taf3, taf5)),
  STRIP_TAC
  THEN EQ_TAC
  THEN STRIP_TAC
  THENL
    [ IMP_RES_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf3_nt)
      THEN frrc_rewr g_adjf3_5
      THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,

      IMP_RES_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] g_adjf5_3)
      THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC
    ]
) ;

(* note - RES_CANON doesn't deal with ty-foralls properly *) (* PVH: now it does *)

val tmjmj = 
``category (idC, compC) /\ g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G  /\
  category (idD, compD) /\ g_functor [:'C,'D,'F:] (idC,compC) (idD,compD) F' /\
  g_adjf3 (idC,compC) (idD,compD) F' G (eta : ('C, I, 'F o 'G) g_nattransf)
                                       (eps : ('D, 'G o 'F, I) g_nattransf) ==> 
  (compD (eps [:'a:]) (F' (G eps)) = compD eps eps)`` ;

val g_adjf3_jmj_lem = store_thm ("g_adjf3_jmj_lem", tmjmj,
  STRIP_TAC
  THEN IMP_RES_THEN MATCH_MP_TAC g_adjf3D1
  THEN IMP_RES_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] FLATT_eps_I)
  THEN IMP_RES_THEN REWRITE_THM g_functorD
  THEN IMP_RES_TAC catDRU
  THEN IMP_RES_THEN ASM_REWRITE_THM catDRAss
) ;

(* given adjoint functors, you have a monad *)
(* NOTE - where do we assume that eta is a natural transformation *)

val tmass = ``category (idC,compC) /\ g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G /\
  g_adjf1 (idC,compC) G (eta : ('C, I, 'F o 'G) g_nattransf) sharp ==> 
  (sharp [:'a,'b:] (compC (G (sharp [:'c,'b:] h)) k) = compD (sharp h) (sharp k))`` ;

val g_adjf1_monad_lem = store_thm ("g_adjf1_monad_lem", tmass,
  STRIP_TAC
  THEN FIRST_REP_RES MATCH_MP_TAC g_adjf1D1
  THEN FIRST_REP_RES REWRITE_THM g_functorD
  THEN FIRST_REP_RES REWRITE_THM catDRAss
  THEN FIRST_REP_RES REWRITE_THM g_adjf1DGh
) ;

val tmmon = ``category (idC,compC) /\ 
  g_functor [:'D,'C,'G:] (idD,compD) (idC,compC) G /\
  g_adjf1 [:'C,'D,'F,'G:] (idC,compC) G eta sharp ==> 
  Kmonad [:'C, 'F o 'G:] (idC,compC) (eta, \: 'a 'b. G o sharp)`` ;

val g_adjf1_IMP_Kmonad = store_thm ("g_adjf1_IMP_Kmonad", tmmon,
  SIMP_TAC combin_ss [Kmonad_thm]
  THEN STRIP_TAC
  THEN REPEAT CONJ_TAC
  THENL
    [ IMP_RES_THEN REWRITE_THM g_adjf1D,

      IMP_RES_TAC g_adjf1_sharp_eta
      THEN IMP_RES_THEN ASM_REWRITE_THM g_functorD,

      IMP_RES_TAC g_adjf1_monad_lem
      THEN IMP_RES_THEN ASM_REWRITE_THM g_functorD
    ]
) ;

(* given g_adjf1, we get a monad without assuming that eta is a natural
  transformation, but then from the monad, we get that the unit is a natural
  transformation - see how this works - question is, what is the functor F' ? *)
val adjf_gives_nt = 
  DISCH_ALL (MATCH_MP Kmonad_IMP_unit_nt (UNDISCH g_adjf1_IMP_Kmonad)) ;

(* note, in adjointScript.sml there is a proof that adjoint functors
  give a monad, in terms of the 7 rule definition of a monad,
  using g_adjf3_jmj_lem *)

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
  SIMP_TAC combin_ss [g_adjf1_def, Kmonad_thm, UNCURRY_DEF]
  THEN STRIP_TAC
  THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
) ;

val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "g_adjoint";

val _ = export_theory();

end; (* structure g_adjointScript *)

