(* ===================================================================== *)
(* FILE          : llistScript.sml                                       *)
(* DESCRIPTION   : Possibly infinite sequences (llist)                   *)
(* ===================================================================== *)

open HolKernel boolLib Parse bossLib

open BasicProvers boolSimps markerLib optionTheory hurdUtils;

val _ = new_theory "llist";

val _ = temp_delsimps ["NORMEQ_CONV"]

val NOT_SUC = numTheory.NOT_SUC ;
val SUC_SUB1 = arithmeticTheory.SUC_SUB1 ;
val FUNPOW = arithmeticTheory.FUNPOW ;
val pair_CASE_def = pairTheory.pair_CASE_def ;
val UNCURRY_VAR = pairTheory.UNCURRY_VAR ;
val VAR_EQ_TAC = BasicProvers.VAR_EQ_TAC ;

(* ----------------------------------------------------------------------
    The representing type is :num -> 'a option
   ---------------------------------------------------------------------- *)

CoInductive lrep_ok:
   (lrep_ok (λn. NONE))
/\ (lrep_ok t ==> lrep_ok (λn. if n = 0 then SOME h else t(n - 1)))
End

Theorem lrep_ok_alt'[local]:
  !n f. lrep_ok f ==> IS_SOME (f (SUC n)) ==> IS_SOME (f n)
Proof
  let open arithmeticTheory in
  Induct THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC lrep_ok_cases THEN
  FULL_SIMP_TAC bool_ss [NOT_SUC, optionTheory.IS_SOME_DEF,
    ONE, SUB_EQUAL_0, SUB_MONO_EQ, SUB_0] end
QED

Theorem lrep_ok_alt:
  lrep_ok f = (!n. IS_SOME (f (SUC n)) ==> IS_SOME (f n))
Proof
  EQ_TAC THEN REPEAT STRIP_TAC
  >- (irule lrep_ok_alt' >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) THEN
  irule lrep_ok_coind THEN
  Q.EXISTS_TAC ‘λf. !n. IS_SOME (f (SUC n)) ==> IS_SOME (f n)’ THEN
  ASM_SIMP_TAC bool_ss [] THEN
  REPEAT STRIP_TAC THEN
  Cases_on ‘a0 0’
  >- (DISJ1_TAC THEN
      SIMP_TAC bool_ss [FUN_EQ_THM] THEN
      Induct THEN1 POP_ASSUM ACCEPT_TAC THEN
      FULL_SIMP_TAC bool_ss [GSYM optionTheory.NOT_IS_SOME_EQ_NONE] THEN
      PROVE_TAC []) >>
  DISJ2_TAC THEN
  Q.EXISTS_TAC ‘x’ THEN Q.EXISTS_TAC ‘a0 o SUC’ THEN
  ASM_SIMP_TAC std_ss [FUN_EQ_THM] THEN
  GEN_TAC THEN Cases_on ‘n’ THEN
  ASM_SIMP_TAC bool_ss [NOT_SUC, SUC_SUB1]
QED

Theorem type_inhabited[local]:
  ?f. lrep_ok f
Proof Q.EXISTS_TAC `λn. NONE` THEN ACCEPT_TAC(CONJUNCT1 lrep_ok_rules)
QED

val llist_tydef = new_type_definition ("llist", type_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "llist_absrep",
  ABS = "llist_abs",
  REP = "llist_rep",
  tyax = llist_tydef};

val llist_absrep = CONJUNCT1 repabs_fns
val llist_repabs = CONJUNCT2 repabs_fns

Theorem lrep_ok_llist_rep[local,simp]:
  lrep_ok (llist_rep f)
Proof
  SRW_TAC [][llist_repabs, llist_absrep]
QED

Theorem llist_abs_11[local]:
  lrep_ok r1 /\ lrep_ok r2 ==> ((llist_abs r1 = llist_abs r2) = (r1 = r2))
Proof SRW_TAC [][llist_repabs, EQ_IMP_THM] THEN METIS_TAC []
QED

Theorem llist_rep_11[local]:
  (llist_rep t1 = llist_rep t2) = (t1 = t2)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``llist_abs``) THEN SRW_TAC [][llist_absrep]
QED

val llist_repabs' = #1 (EQ_IMP_RULE (SPEC_ALL llist_repabs))

Theorem llist_if_rep_abs[local]: (f = llist_rep a) ==> (a = llist_abs f)
Proof DISCH_TAC THEN ASM_REWRITE_TAC [repabs_fns]
QED

Theorem FUNPOW_BIND_NONE[local]:
  !n. FUNPOW (λm. OPTION_BIND m g) n NONE = NONE
Proof Induct THEN ASM_SIMP_TAC bool_ss [FUNPOW, OPTION_BIND_def]
QED

Theorem lrep_ok_MAP:
  lrep_ok (λn. OPTION_MAP f (g n)) = lrep_ok g
Proof SIMP_TAC bool_ss [lrep_ok_alt, IS_SOME_MAP]
QED

Theorem lrep_ok_FUNPOW_BIND:
  lrep_ok (λn. FUNPOW (λm. OPTION_BIND m g) n fz)
Proof
  SIMP_TAC bool_ss [lrep_ok_alt, arithmeticTheory.FUNPOW_SUC] THEN
  GEN_TAC THEN MATCH_ACCEPT_TAC IS_SOME_BIND
QED

Theorem lrep_ok_MAP_FUNPOW_BIND[local]:
  lrep_ok (λn. OPTION_MAP f (FUNPOW (λm. OPTION_BIND m g) n fz))
Proof SIMP_TAC bool_ss [lrep_ok_MAP] THEN irule lrep_ok_FUNPOW_BIND
QED

val LNIL = new_definition("LNIL", ``LNIL = llist_abs (λn. NONE)``);
val LCONS = new_definition(
  "LCONS",
  ``LCONS h t = llist_abs (λn. if n = 0 then SOME h else llist_rep t (n - 1))``
);

Theorem llist_rep_LCONS:
  llist_rep (LCONS h t) =
  λn. if n = 0 then SOME h else llist_rep t (n - 1)
Proof
  SRW_TAC [][LCONS, GSYM llist_repabs] THEN
  MATCH_MP_TAC (CONJUNCT2 lrep_ok_rules) THEN SRW_TAC [][]
QED

Theorem llist_rep_LNIL: llist_rep LNIL = \n. NONE
Proof SIMP_TAC std_ss [LNIL, lrep_ok_rules, llist_repabs']
QED

Definition LTL_HD_def[nocompute]:
  LTL_HD ll = case llist_rep ll 0 of
                NONE => NONE
              | SOME h => SOME (llist_abs (llist_rep ll o SUC), h)
End

Theorem LTL_HD_LNIL[compute,simp]:
  LTL_HD LNIL = NONE
Proof
  SIMP_TAC std_ss [LTL_HD_def, llist_rep_LNIL]
QED

Theorem lr_eta[local]: (\n. llist_rep t n) = llist_rep t
Proof irule ETA_AX
QED

Theorem LTL_HD_LCONS[compute,simp]: LTL_HD (LCONS h t) = SOME (t, h)
Proof
  SIMP_TAC std_ss [LTL_HD_def, llist_rep_LCONS, combinTheory.o_ABS_L,
                   NOT_SUC, lr_eta, llist_absrep]
QED

val LHD = new_definition("LHD", ``LHD ll = llist_rep ll 0``);
val LTL = new_definition(
  "LTL",
  ``LTL ll = case LHD ll of
               NONE => NONE
             | SOME _ => SOME (llist_abs (\n. llist_rep ll (n + 1)))``
);

Theorem LTL_HD_HD: LHD ll = OPTION_MAP SND (LTL_HD ll)
Proof
  Cases_on `llist_rep ll 0` THEN ASM_SIMP_TAC std_ss [LTL_HD_def, LHD]
QED

Theorem LTL_HD_TL: LTL ll = OPTION_MAP FST (LTL_HD ll)
Proof
  Cases_on `llist_rep ll 0` THEN
  ASM_SIMP_TAC std_ss [LTL_HD_def, LTL, LHD] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [FUN_EQ_THM, arithmeticTheory.ADD1]
QED

Theorem LHD_LCONS: LHD (LCONS h t) = SOME h
Proof SRW_TAC [][LHD, llist_rep_LCONS]
QED

Theorem LTL_LCONS: LTL (LCONS h t) = SOME t
Proof SRW_TAC [ETA_ss][LTL, llist_rep_LCONS, llist_absrep, LHD_LCONS]
QED

(*---------------------------------------------------------------------------*)
(* Syntax for lazy lists, similar to lists                                   *)
(*---------------------------------------------------------------------------*)

val _ = add_rule {term_name = "LCONS", fixity = Infixr 490,
                  pp_elements = [TOK ":::", BreakSpace(0,2)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 2))};

val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "[|"], rightdelim = [TOK "|]"],
                      cons = "LCONS", nilstr = "LNIL",
                      block_info = (PP.INCONSISTENT, 2)};
val _ = TeX_notation {hol = "[|", TeX = ("\\HOLTokenLeftDenote{}", 1)}
val _ = TeX_notation {hol = "|]", TeX = ("\\HOLTokenRightDenote{}", 1)}

Theorem LHDTL_CONS_THM = Q.GENL [‘h’, ‘t’] $ CONJ LHD_LCONS LTL_LCONS

Theorem lrep_inversion[local]:
  lrep_ok f ==> (f = \n. NONE) \/
                (?h t. (f = \n. if n = 0 then SOME h else t (n - 1)) /\
                       lrep_ok t)
Proof
  MATCH_ACCEPT_TAC (fst (EQ_IMP_RULE (SPEC_ALL lrep_ok_cases)))
QED

Theorem forall_llist[local]:
  (!l. P l) = (!r. lrep_ok r ==> P (llist_abs r))
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  ONCE_REWRITE_TAC [GSYM llist_absrep] THEN
  SRW_TAC [][]
QED

Theorem llist_CASES:
  !l. (l = LNIL) \/ (?h t. l = LCONS h t)
Proof
  SIMP_TAC (srw_ss() ++ ETA_ss) [LNIL,LCONS,forall_llist,llist_abs_11,
                                 lrep_ok_rules] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC lrep_inversion THENL [
    SRW_TAC [][],
    DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h`, `llist_abs t`] THEN
    SRW_TAC [][llist_repabs']
  ]
QED

fun llist_CASE_TAC tm = STRUCT_CASES_TAC (ISPEC tm llist_CASES) ;

Theorem LCONS_NOT_NIL[simp]:
  !h t. ~(LCONS h t = LNIL) /\ ~(LNIL = LCONS h t)
Proof
  SRW_TAC [][LCONS, LNIL, FUN_EQ_THM] THEN STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [llist_repabs', lrep_ok_rules] THEN
  POP_ASSUM (ASSUME_TAC o C AP_THM ``0``) THEN
  FULL_SIMP_TAC (srw_ss()) []
QED

Theorem LCONS_11[simp]:
  !h1 t1 h2 t2. (LCONS h1 t1 = LCONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)
Proof
  SRW_TAC [][EQ_IMP_THM, LCONS] THEN
  POP_ASSUM (ASSUME_TAC o Q.AP_TERM `llist_rep`) THEN
  FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [llist_repabs', lrep_ok_rules] THENL [
    POP_ASSUM (MP_TAC o C AP_THM ``0``) THEN SRW_TAC [][],
    ALL_TAC
  ] THEN
  POP_ASSUM (MP_TAC o GEN ``n:num`` o SIMP_RULE (srw_ss()) [] o
             C AP_THM ``SUC n:num``) THEN
  SRW_TAC [ETA_ss][GSYM FUN_EQ_THM, llist_rep_11]
QED

Theorem LTL_HD_11[simp]:
  LTL_HD ll1 = LTL_HD ll2 <=> ll1 = ll2
Proof
  llist_CASE_TAC ``ll1 : 'a llist`` THEN
  llist_CASE_TAC ``ll2 : 'a llist`` THEN
  simp[EQ_IMP_THM]
QED

Theorem LHD_THM[simp,compute]:
  (LHD LNIL = NONE) /\ (!h t. LHD (LCONS h t) = SOME h)
Proof
  SRW_TAC [][LHDTL_CONS_THM] THEN
  SRW_TAC [][LHD, LNIL, llist_repabs', lrep_ok_rules]
QED

Theorem LTL_THM[simp,compute]:
  (LTL LNIL = NONE) /\ (!h t. LTL (LCONS h t) = SOME t)
Proof
  SRW_TAC [][LHDTL_CONS_THM] THEN
  SRW_TAC [][LTL, LNIL, llist_repabs', lrep_ok_rules, LHD]
QED

val LTL_HD_iff = Q.store_thm ("LTL_HD_iff",
  `((LTL_HD x = SOME (t, h)) = (x = LCONS h t)) /\
    ((LTL_HD x = NONE) = (x = LNIL))`,
  llist_CASE_TAC ``x :'a llist`` THEN
  SIMP_TAC std_ss [LTL_HD_LCONS, LTL_HD_LNIL, LCONS_NOT_NIL, LCONS_11] THEN
  DECIDE_TAC) ;

val LHD_EQ_NONE = store_thm(
  "LHD_EQ_NONE",
  ``!ll. ((LHD ll = NONE) = (ll = LNIL)) /\ ((NONE = LHD ll) = (ll = LNIL))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["LHD_EQ_NONE"]

val LTL_EQ_NONE = store_thm(
  "LTL_EQ_NONE",
  ``!ll. ((LTL ll = NONE) = (ll = LNIL)) /\ ((NONE = LTL ll) = (ll = LNIL))``,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][LTL_THM]);
val _ = export_rewrites ["LTL_EQ_NONE"]

val LHDTL_EQ_SOME = store_thm(
  "LHDTL_EQ_SOME",
  ``!h t ll. (ll = LCONS h t) <=> (LHD ll = SOME h) /\ (LTL ll = SOME t)``,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SRW_TAC [][LHD_THM, LTL_THM]);


(* ----------------------------------------------------------------------
    indexing into lazy lists

    LNTH : num -> 'a llist -> 'a option
   ---------------------------------------------------------------------- *)

val LNTH = new_recursive_definition{
  name = "LNTH",
  rec_axiom = prim_recTheory.num_Axiom,
  def = ``(LNTH 0 ll = LHD ll) /\
          (LNTH (SUC n) ll = OPTION_JOIN (OPTION_MAP (LNTH n) (LTL ll)))``};

val LNTH_THM = store_thm(
  "LNTH_THM",
  ``(!n. LNTH n LNIL = NONE) /\
    (!h t. LNTH 0 (LCONS h t) = SOME h) /\
    (!n h t. LNTH (SUC n) (LCONS h t) = LNTH n t)``,
  SRW_TAC [][LNTH] THEN Induct_on `n` THEN
  SRW_TAC [][LNTH]);
val _ = export_rewrites ["LNTH_THM"]

(* ----------------------------------------------------------------------
    LNTH is just llist_rep with arguments swapped
   ---------------------------------------------------------------------- *)

val LNTH_rep = Q.store_thm ("LNTH_rep",
  `!i ll. LNTH i ll = llist_rep ll i`,
  Induct THEN GEN_TAC THEN llist_CASE_TAC ``ll : 'a llist`` THEN
  ASM_SIMP_TAC std_ss [LNTH_THM, llist_rep_LCONS, llist_rep_LNIL, NOT_SUC]) ;

(* can also prove that two lists are equal "extensionally", by showing
   that LNTH is everywhere the same over them *)
val LNTH_llist_rep = prove(
  ``!n r. lrep_ok r ==> (LNTH n (llist_abs r) = r n)``,
  SIMP_TAC bool_ss [LNTH_rep, llist_repabs']) ;

val LNTH_EQ = store_thm(
  "LNTH_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LNTH n ll1 = LNTH n ll2)``,
  SIMP_TAC (srw_ss()) [forall_llist, LNTH_llist_rep, llist_abs_11,
                       FUN_EQ_THM]);

(*---------------------------------------------------------------------------*)
(* LUNFOLD by definition                                                     *)
(*                                                                           *)
(* Formerly we got LUNFOLD by Skolemization using llist_Axiom_1              *)
(* which was proved independently                                            *)
(*---------------------------------------------------------------------------*)

val LUNFOLD_def = zDefine `LUNFOLD f z = llist_abs (\n. OPTION_MAP SND
  (FUNPOW (\m. OPTION_BIND m (UNCURRY (K o f))) n (f z)))` ;

(* would be somewhat ok to add this presentation to compset if you'd
   applied set_skip to option_CASE, as in:
     computeLib.set_skip computeLib.the_compset ``option_CASE`` (SOME 1)
   and you never had a concrete function f that actually wanted to generate
   an infinite list.
*)
val LUNFOLD = Q.store_thm (
  "LUNFOLD",
  `!f x.
     LUNFOLD f x =
       case f x of NONE => [||] | SOME (v1,v2) => v2 ::: LUNFOLD f v1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [LUNFOLD_def] THEN
  irule (GSYM llist_if_rep_abs) THEN
  Cases_on `f x` THEN
  ASM_SIMP_TAC std_ss [llist_rep_LCONS, llist_rep_LNIL, pair_CASE_def,
    FUNPOW_BIND_NONE, OPTION_MAP_DEF, FUN_EQ_THM] THEN
  GEN_TAC THEN Cases_on `n` THEN
  SIMP_TAC std_ss [FUNPOW, OPTION_MAP_DEF, NOT_SUC, UNCURRY_VAR,
    SUC_SUB1, OPTION_BIND_def, llist_repabs', lrep_ok_MAP_FUNPOW_BIND]) ;

(* this is the uniqueness in the definition of llist as final coalgebra *)
Theorem LUNFOLD_UNIQUE:
   !f g. (!x. g x = case f x of NONE => [||]
                             | SOME (v1,v2) => v2:::g v1) ==>
         (!y. g y = LUNFOLD f y)
Proof
  REWRITE_TAC [LNTH_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  Induct_on `n` THEN GEN_TAC THEN
  ONCE_ASM_REWRITE_TAC [LUNFOLD] THEN
  Cases_on `f y` THEN SIMP_TAC std_ss [pair_CASE_def, LNTH_THM] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC
QED

(* LUNFOLD is a sort of inverse to LTL_HD *)
val lu1 = BETA_RULE
  (ISPECL [``LTL_HD``, ``(\x. x) : 'a llist -> 'a llist``] LUNFOLD_UNIQUE) ;

Theorem LUNFOLD_LTL_HD: LUNFOLD LTL_HD ll = ll:'a llist
Proof
  irule EQ_SYM THEN irule lu1 THEN
  qx_gen_tac ‘x’ >> llist_CASE_TAC “x:'a llist” >> simp[]
QED

Theorem LTL_HD_LUNFOLD[simp,compute]:
  LTL_HD (LUNFOLD f x) = OPTION_MAP (LUNFOLD f ## I) (f x)
Proof
  ONCE_REWRITE_TAC [LUNFOLD] THEN CASE_TAC THEN
  SIMP_TAC std_ss [OPTION_MAP_DEF, pair_CASE_def, LTL_HD_LNIL,
    LTL_HD_LCONS, pairTheory.PAIR_MAP]
QED

Theorem LNTH_LUNFOLD[simp]:
  (LNTH 0 (LUNFOLD f x) = OPTION_MAP SND (f x)) /\
  (LNTH (SUC n) (LUNFOLD f x) =
    case f x of NONE => NONE
      | SOME (tx, hx) => LNTH n (LUNFOLD f tx))
Proof
  CONV_TAC (ONCE_DEPTH_CONV (LHS_CONV (ONCE_DEPTH_CONV (REWR_CONV LUNFOLD))))
  THEN Cases_on `f x` THEN
  REWRITE_TAC [LNTH, option_case_def, pair_CASE_def] THEN BETA_TAC THEN
  REWRITE_TAC [LHD_THM, LTL_THM, OPTION_MAP_DEF, OPTION_JOIN_DEF]
QED

Theorem LNTH_LUNFOLD_compute[compute] =
  CONJ (CONJUNCT1 LNTH_LUNFOLD)
       (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
                  (LNTH_LUNFOLD |> CONJUNCT2 |> Q.GEN `n`))

Theorem LHD_LUNFOLD[compute,simp]:
  LHD (LUNFOLD f x) = OPTION_MAP SND (f x)
Proof
  REWRITE_TAC [GSYM LNTH, LNTH_LUNFOLD]
QED

Theorem LTL_LUNFOLD[compute,simp]:
  LTL (LUNFOLD f x) = OPTION_MAP (LUNFOLD f o FST) (f x)
Proof
  REWRITE_TAC [LTL_HD_TL, LTL_HD_LUNFOLD, OPTION_MAP_COMPOSE] THEN
  REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  SIMP_TAC std_ss [FUN_EQ_THM, pairTheory.FST_PAIR_MAP]
QED

(*---------------------------------------------------------------------------*)
(* Co-recursion theorem for lazy lists                                       *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Alternative version of llist_Axiom (more understandable)                  *)
(*---------------------------------------------------------------------------*)

Theorem llist_Axiom_1:
  !f :'a -> ('a#'b)option.
    ?g:'a -> 'b llist.
      !x. g x =
          case f x of
            NONE => LNIL
          | SOME (a,b) => LCONS b (g a)
Proof
  GEN_TAC THEN Q.EXISTS_TAC `LUNFOLD f` THEN
  GEN_TAC THEN MATCH_ACCEPT_TAC LUNFOLD
QED

Theorem llist_Axiom_1ue:
  !f. ?!g. !x. g x = case f x of NONE => LNIL
                              | SOME (a,b) => b ::: g a
Proof
  SIMP_TAC bool_ss [EXISTS_UNIQUE_THM] THEN REPEAT STRIP_TAC
  THENL [
    Q.EXISTS_TAC `LUNFOLD f` THEN GEN_TAC THEN MATCH_ACCEPT_TAC LUNFOLD,
    IMP_RES_TAC LUNFOLD_UNIQUE THEN ASM_SIMP_TAC bool_ss [FUN_EQ_THM]
  ]
QED

val eq_imp_lem = Q.prove (`(p = q) ==> p ==> q`, DECIDE_TAC)  ;

val llist_ue_Axiom = store_thm(
  "llist_ue_Axiom",
  ``!f : 'a -> ('a # 'b) option.
      ?!g : 'a -> 'b llist.
        (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
        (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))``,
  MP_TAC llist_Axiom_1ue THEN
  MATCH_MP_TAC eq_imp_lem THEN
  AP_TERM_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM, GSYM FORALL_AND_THM] THEN
    Q.X_GEN_TAC `f` THEN
  AP_TERM_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM] THEN Q.X_GEN_TAC `g` THEN
  AP_TERM_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM] THEN GEN_TAC THEN
  Cases_on `f x` THEN llist_CASE_TAC ``(g : 'a -> 'b llist) x`` THEN
  SIMP_TAC std_ss [OPTION_MAP_DEF, LHD_THM, LTL_THM, pair_CASE_def,
    LCONS_NOT_NIL, LCONS_11]) ;

val llist_Axiom = store_thm(
  "llist_Axiom",
  ``!f : 'a -> ('a # 'b) option.
      ?g.
         (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
         (!x. LTL (g x) = OPTION_MAP (g o FST) (f x))``,
  MATCH_ACCEPT_TAC
    (CONJUNCT1
      (SIMP_RULE bool_ss [EXISTS_UNIQUE_THM, FORALL_AND_THM] llist_ue_Axiom)));

(* ----------------------------------------------------------------------
    Another consequence of the finality theorem is the principle of
    bisimulation, including for lists unfolded from different generators
   ---------------------------------------------------------------------- *)

val LUNFOLD_BISIMULATION = store_thm(
  "LUNFOLD_BISIMULATION",
  ``!f1 f2 x1 x2. (LUNFOLD f1 x1 = LUNFOLD f2 x2) =
      ?R. R x1 x2 /\
        !y1 y2.  R y1 y2 ==>
           (f1 y1 = NONE) /\ (f2 y2 = NONE) \/
           ?h t1 t2.
             (f1 y1 = SOME (t1, h)) /\ (f2 y2 = SOME (t2, h)) /\ R t1 t2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN (fn th =>
      Q.EXISTS_TAC `\x1 x2. LUNFOLD f1 x1 = LUNFOLD f2 x2` THEN
      SIMP_TAC std_ss [th]) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [LUNFOLD]) THEN
    REPEAT CASE_TAC THEN SIMP_TAC std_ss [LCONS_NOT_NIL, LCONS_11],
    STRIP_TAC THEN POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) THEN
    POP_ASSUM MP_TAC THEN
    Q.SPEC_TAC (`x1`, `x1`) THEN Q.SPEC_TAC (`x2`, `x2`) THEN
    Ho_Rewrite.REWRITE_TAC [LNTH_EQ, PULL_FORALL] THEN
    Induct_on `n` THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [LUNFOLD] THEN RES_TAC THEN
    ASM_SIMP_TAC std_ss [pair_CASE_def, LNTH_THM] ]) ;

val LLIST_BISIMULATION0 = store_thm(
  "LLIST_BISIMULATION0",
  ``!ll1 ll2. (ll1 = ll2) =
              ?R. R ll1 ll2 /\
                  !ll3 ll4.  R ll3 ll4 ==>
                             (ll3 = LNIL) /\ (ll4 = LNIL) \/
                             ?h t1 t2.
                                 (ll3 = h:::t1) /\ (ll4 = h:::t2) /\
                                 R t1 t2``,
  REPEAT GEN_TAC THEN
  CONV_TAC (LHS_CONV (ONCE_DEPTH_CONV (REWR_CONV (SYM LUNFOLD_LTL_HD)))) THEN
  REWRITE_TAC [LUNFOLD_BISIMULATION] THEN
  REPEAT (FIRST [AP_TERM_TAC, ABS_TAC, AP_THM_TAC]) THEN
  SIMP_TAC std_ss [LTL_HD_iff]) ;

val LLIST_BISIMULATION = store_thm(
  "LLIST_BISIMULATION",
  ``!ll1 ll2.
       (ll1 = ll2) =
       ?R. R ll1 ll2 /\
           !ll3 ll4.
              R ll3 ll4 ==>
              (ll3 = [||]) /\ (ll4 = [||]) \/
              (LHD ll3 = LHD ll4) /\ R (THE (LTL ll3)) (THE (LTL ll4))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
    Q.EXISTS_TAC `R` THEN SRW_TAC [][] THEN
    `(ll3 = [||]) /\ (ll4 = [||]) \/
     (LHD ll3 = LHD ll4) /\ R (THE (LTL ll3)) (THE (LTL ll4))`
        by METIS_TAC [] THEN
    SRW_TAC [][] THEN
    Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.SPEC_THEN `ll4` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val LLIST_STRONG_BISIMULATION = store_thm(
  "LLIST_STRONG_BISIMULATION",
  ``!ll1 ll2.
       (ll1 = ll2) =
       ?R. R ll1 ll2 /\
           !ll3 ll4.
              R ll3 ll4 ==>
              (ll3 = ll4) \/
              ?h t1 t2. (ll3 = h ::: t1) /\ (ll4 = h ::: t2) /\
                        R t1 t2``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST_ALL_TAC THEN Q.EXISTS_TAC `(=)` THEN SRW_TAC [][],
    STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
    Q.EXISTS_TAC `\l1 l2. R l1 l2 \/ (l1 = l2)` THEN
    SRW_TAC [][] THENL [
      `(ll3 = ll4) \/
       ?h t1 t2. (ll3 = h:::t1) /\ (ll4 = h:::t2) /\ R t1 t2`
          by METIS_TAC [] THEN
      Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],
      Q.SPEC_THEN `ll3` FULL_STRUCT_CASES_TAC llist_CASES THEN
      SRW_TAC [][]
    ]
  ]);

(* ----------------------------------------------------------------------
    LTAKE : num -> 'a llist -> 'a list option

    returns the prefix of the given length, if the input list is at least
    that long
   ---------------------------------------------------------------------- *)

val LTAKE = new_recursive_definition {
  def = ``(LTAKE 0 ll = SOME []) /\
          (LTAKE (SUC n) ll =
             case LHD ll of
                 NONE => NONE
               | SOME hd =>
                   case LTAKE n (THE (LTL ll)) of
                       NONE => NONE
                     | SOME tl => SOME (hd::tl))``,
  name = "LTAKE",
  rec_axiom = prim_recTheory.num_Axiom};

val LTAKE_LUNFOLD = Q.store_thm ("LTAKE_LUNFOLD",
  `(LTAKE 0 (LUNFOLD f x) = SOME []) /\
  (LTAKE (SUC n) (LUNFOLD f x) =
    case f x of NONE => NONE
      | SOME (tx, hx) => OPTION_MAP (CONS hx) (LTAKE n (LUNFOLD f tx)))`,
  CONJ_TAC THEN REWRITE_TAC [LTAKE, LHD_LUNFOLD, LTL_LUNFOLD] THEN
  Cases_on `f x` THEN
  Ho_Rewrite.REWRITE_TAC [BETA_THM, THE_DEF,
    OPTION_MAP_DEF, option_case_def, pair_CASE_def,
    combinTheory.o_DEF, OPTION_MAP_CASE]) ;

val LTAKE_THM = store_thm(
  "LTAKE_THM",
  ``(!l. LTAKE 0 l = SOME []) /\
    (!n. LTAKE (SUC n) LNIL = NONE) /\
    (!n h t. LTAKE (SUC n) (LCONS h t) = OPTION_MAP (CONS h) (LTAKE n t))``,
  SRW_TAC [][LTAKE, LHD_THM, LTL_THM] THEN REPEAT GEN_TAC THEN
  Cases_on `LTAKE n t` THEN SRW_TAC [][]);
val _ = export_rewrites ["LTAKE_THM"]

(* can also prove llist equality by proving all prefixes are the same *)
val LTAKE_SNOC_LNTH = store_thm(
  "LTAKE_SNOC_LNTH",
  ``!n ll. LTAKE (SUC n) ll =
             case LTAKE n ll of
               NONE => NONE
             | SOME l => (case LNTH n ll of
                             NONE => NONE
                           | SOME e => SOME (l ++ [e]))``,
  Induct THENL [
    SRW_TAC [][LTAKE,LNTH],
    GEN_TAC THEN
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LTAKE])) THEN
    Q.SPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THENL [
      POP_ASSUM (K ALL_TAC) THEN SRW_TAC [][LHD_THM, LTAKE_THM],
      SIMP_TAC (srw_ss()) [LHD_THM,LTL_THM,LTAKE_THM,LNTH_THM] THEN
      SRW_TAC [][] THEN Cases_on `LTAKE n t` THENL [
        SRW_TAC [][],
        SRW_TAC [][] THEN Cases_on `LNTH n t` THEN SRW_TAC [][]
      ]
    ]
  ]);

val LTAKE_EQ_NONE_LNTH = store_thm(
  "LTAKE_EQ_NONE_LNTH",
  ``!n ll. (LTAKE n ll = NONE) ==> (LNTH n ll = NONE)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [LTAKE,LNTH] THEN
  Q.X_GEN_TAC `ll` THEN
  Q.SPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  ASM_SIMP_TAC (srw_ss()) [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE n t` THEN SRW_TAC [][]);

Theorem LTAKE_NIL_EQ_SOME[simp]:
  !l m. (LTAKE m LNIL = SOME l) <=> (m = 0) /\ (l = [])
Proof
  REPEAT GEN_TAC >> Cases_on `m` >> SIMP_TAC (srw_ss()) [LTAKE, LHD_THM] >>
  PROVE_TAC []
QED

val LTAKE_NIL_EQ_NONE = store_thm(
  "LTAKE_NIL_EQ_NONE",
  ``!m. (LTAKE m LNIL = NONE) = (0 < m)``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC (srw_ss()) [LTAKE, LHD_THM]);
val _ = export_rewrites ["LTAKE_NIL_EQ_NONE"]

val SNOC_11 = prove(
  ``!l1 l2 x y. (l1 ++ [x] = l2 ++ [y]) <=> (l1 = l2) /\ (x = y)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THEN
  Induct THEN REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  Cases_on `l2` THEN SRW_TAC [][] THEN METIS_TAC []);

val LTAKE_EQ = store_thm(
  "LTAKE_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LTAKE n ll1 = LTAKE n ll2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  SRW_TAC [][LNTH_EQ] THEN
  POP_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
  SIMP_TAC (srw_ss())[LTAKE_SNOC_LNTH] THEN
  Cases_on `LTAKE n ll1` THEN Cases_on `LTAKE n ll2` THEN
  ASM_SIMP_TAC (srw_ss()) [] THENL [
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll2` THEN SRW_TAC [][] THEN
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll1` THEN SRW_TAC [][] THEN
    METIS_TAC [LTAKE_EQ_NONE_LNTH],
    Cases_on `LNTH n ll1` THEN Cases_on `LNTH n ll2` THEN
    SRW_TAC [][SNOC_11]
  ]);

(* more random facts about LTAKE *)
val LTAKE_CONS_EQ_NONE = store_thm(
  "LTAKE_CONS_EQ_NONE",
  ``!m h t. (LTAKE m (LCONS h t) = NONE) =
            (?n. (m = SUC n) /\ (LTAKE n t = NONE))``,
  GEN_TAC THEN Cases_on `m` THEN SIMP_TAC (srw_ss()) []);

Theorem LTAKE_CONS_EQ_SOME:
  !m h t l.
       (LTAKE m (LCONS h t) = SOME l) <=>
       (m = 0) /\ (l = []) \/
       ?n l'. (m = SUC n) /\ (LTAKE n t = SOME l') /\  (l = h::l')
Proof
  GEN_TAC THEN Cases_on `m` THEN
  SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []
QED

val LTAKE_EQ_SOME_CONS = store_thm(
  "LTAKE_EQ_SOME_CONS",
  ``!n l x. (LTAKE n l = SOME x) ==> !h. ?y. LTAKE n (LCONS h l) = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LTAKE, LHD_THM, LTL_THM] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `l` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LHD_THM, LTL_THM] THEN
  Cases_on `LTAKE n t` THEN SIMP_TAC (srw_ss()) [] THEN RES_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `h`) THEN
  ASM_SIMP_TAC (srw_ss()) []);

(* ----------------------------------------------------------------------
    Finality allows us to  define MAP
   ---------------------------------------------------------------------- *)

val LMAP = new_specification
("LMAP", ["LMAP"],
  prove(
    ``?LMAP. (!f. LMAP f LNIL = LNIL) /\
             (!f h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\l. if l = LNIL then NONE
                     else SOME (THE (LTL l), f (THE (LHD l)))`
                llist_Axiom_1)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN
    REPEAT STRIP_TAC THEN
    POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
    SRW_TAC [][LHD_THM, LTL_THM]));
val _ = export_rewrites ["LMAP"]
val _ = computeLib.add_persistent_funs ["LMAP"]

(* and append *)

val LAPPEND = new_specification
 ("LAPPEND", ["LAPPEND"],
  prove(
    ``?LAPPEND. (!x. LAPPEND LNIL x = x) /\
               (!h t x. LAPPEND (LCONS h t) x = LCONS h (LAPPEND t x))``,
    STRIP_ASSUME_TAC
       (Q.ISPEC `\(l1,l2).
                     if l1 = LNIL then
                        if l2 = LNIL then NONE
                        else SOME ((l1, THE (LTL l2)), THE (LHD l2))
                     else SOME ((THE (LTL l1), l2), THE (LHD l1))`
                llist_Axiom) THEN
    Q.EXISTS_TAC `\l1 l2. g (l1, l2)` THEN SIMP_TAC (srw_ss()) [] THEN
    REPEAT STRIP_TAC THENL [
      ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
      Q.EXISTS_TAC `\ll1 ll2. ll1 = g (LNIL, ll2)` THEN
      SIMP_TAC (srw_ss()) [] THEN Q.X_GEN_TAC `x` THEN
      STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THENL [
        DISJ1_TAC THEN
        ASM_SIMP_TAC std_ss [GSYM LHD_EQ_NONE, LHD_THM],
        SRW_TAC [][]
      ],
      SRW_TAC [][LHDTL_EQ_SOME]
    ]));
val _ = export_rewrites ["LAPPEND"]
val _ = computeLib.add_persistent_funs ["LAPPEND"]

(* NOTE: The last char is Latin Subscript Small Letter L (U+2097) *)
val _ = set_mapped_fixity{fixity = Infixl 480, term_name = "LAPPEND",
                          tok = "++ₗ"};                               (* UOK *)

val _ = TeX_notation { hol = "LAPPEND",
                       TeX = ("\\HOLTokenDoublePlusL", 1) };

(* properties of map and append *)

Theorem LMAP_APPEND:
  !f ll1 ll2.
    LMAP f (LAPPEND ll1 ll2) = LAPPEND (LMAP f ll1) (LMAP f ll2)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION0] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?x y. (ll1 = LMAP f (LAPPEND x y)) /\
                                (ll2 = LAPPEND (LMAP f x) (LMAP f y))` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    ALL_TAC
  ] THEN
  STRUCT_CASES_TAC (Q.SPEC `x` llist_CASES) THEN SRW_TAC [][] THENL [
    STRUCT_CASES_TAC (Q.SPEC `y` llist_CASES) THEN
    SRW_TAC [][] THEN
    PROVE_TAC [LAPPEND, LMAP],
    PROVE_TAC []
  ]
QED

Theorem LAPPEND_EQ_LNIL[simp]:
  (LAPPEND l1 l2 = [||]) <=> (l1 = [||]) /\ (l2 = [||])
Proof SRW_TAC [][EQ_IMP_THM] THEN
      Q.SPEC_THEN `l1` FULL_STRUCT_CASES_TAC llist_CASES THEN
      FULL_SIMP_TAC (srw_ss()) []
QED

val LAPPEND_ASSOC = store_thm(
  "LAPPEND_ASSOC",
  ``!ll1 ll2 ll3. LAPPEND (LAPPEND ll1 ll2) ll3 =
                  LAPPEND ll1 (LAPPEND ll2 ll3)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_STRONG_BISIMULATION] THEN
  Q.EXISTS_TAC `\l1 l2. ?u. (l1 = LAPPEND (LAPPEND u ll2) ll3) /\
                            (l2 = LAPPEND u (LAPPEND ll2 ll3))` THEN
  SRW_TAC [][] THENL [
    PROVE_TAC [],
    STRUCT_CASES_TAC (Q.SPEC `u` llist_CASES) THEN SRW_TAC [][] THEN
    PROVE_TAC []
  ]);

val LMAP_MAP = store_thm(
  "LMAP_MAP",
  ``!(f:'a -> 'b) (g:'c -> 'a) (ll:'c llist).
        LMAP f (LMAP g ll) = LMAP (f o g) ll``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `λll1 ll2. ?ll0. (ll1 = LMAP f (LMAP g ll0)) /\
                                (ll2 = LMAP (f o g) ll0)` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
      (Q.ISPEC `ll0:'c llist` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LMAP, LTL_THM, LHD_THM] THEN
    PROVE_TAC []
  ]);

val LAPPEND_NIL_2ND = store_thm(
  "LAPPEND_NIL_2ND",
  ``!ll. LAPPEND ll LNIL = ll``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LAPPEND ll2 LNIL` THEN
  SIMP_TAC (srw_ss()) [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC (srw_ss()) []);

val LHD_LAPPEND = Q.store_thm("LHD_LAPPEND",
  `LHD (LAPPEND l1 l2) = if l1 = LNIL then LHD l2 else LHD l1`,
  qspec_then`l1`FULL_STRUCT_CASES_TAC llist_CASES >> rw[])

val LTL_LAPPEND = Q.store_thm("LTL_LAPPEND",
  `LTL (LAPPEND l1 l2) = if l1 = LNIL then LTL l2
                         else SOME (LAPPEND (THE (LTL l1)) l2)`,
  qspec_then`l1`FULL_STRUCT_CASES_TAC llist_CASES >> rw[]);


val LTAKE_LAPPEND1 = Q.store_thm("LTAKE_LAPPEND1",
  `!n l1 l2. IS_SOME (LTAKE n l1) ==> (LTAKE n (LAPPEND l1 l2) = LTAKE n l1)`,
  Induct >> rw[LTAKE_THM] >>
  qspec_then`l1`FULL_STRUCT_CASES_TAC llist_CASES >> fs[] >>
  Cases_on`LTAKE n t`>>fs[])

Theorem LTAKE_LMAP:
  !n f ll. LTAKE n (LMAP f ll) =
   OPTION_MAP (MAP f) (LTAKE n ll)
Proof
  Induct_on `n` >> rw[] >>
  qspec_then ‘ll’ strip_assume_tac llist_CASES >>
  pop_assum SUBST_ALL_TAC >>
  fs[OPTION_MAP_COMPOSE,combinTheory.o_DEF]
QED

(* ----------------------------------------------------------------------
    finiteness and list length
   ---------------------------------------------------------------------- *)

val (LFINITE_rules,LFINITE_ind,LFINITE_cases) = Hol_reln`
  LFINITE [||] /\
  (!h t. LFINITE t ==> LFINITE (h:::t))
`;

val LFINITE_THM = store_thm(
  "LFINITE_THM",
  ``(LFINITE LNIL = T) /\
    (!h t. LFINITE (LCONS h t) = LFINITE t)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LFINITE_cases])) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["LFINITE_THM"]

val LFINITE = store_thm(
  "LFINITE",
  ``LFINITE ll = ?n. LTAKE n ll = NONE``,
  EQ_TAC THENL [
    Q.ID_SPEC_TAC `ll` THEN HO_MATCH_MP_TAC LFINITE_ind THEN
    SRW_TAC [][] THEN Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][],
    Q_TAC SUFF_TAC `!n ll. (LTAKE n ll = NONE) ==> LFINITE ll` THEN1
          METIS_TAC [] THEN
    Induct THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val (llength_rel_rules,llength_rel_ind,llength_rel_cases) = Hol_reln`
  llength_rel [||] 0  /\
  (!h n t. llength_rel t n ==> llength_rel (h:::t) (SUC n))
`;

val llength_lfinite = prove(
 ``!t n. llength_rel t n ==> LFINITE t``,
  HO_MATCH_MP_TAC llength_rel_ind THEN SRW_TAC [][]);
val lfinite_llength = prove(
  ``!t. LFINITE t ==> ?n. llength_rel t n``,
  HO_MATCH_MP_TAC LFINITE_ind THEN SRW_TAC [][] THEN
  METIS_TAC [llength_rel_rules]);

val llength_unique = prove(
  ``!t m n. llength_rel t n /\ llength_rel t m ==> (m = n)``,
  Q_TAC SUFF_TAC `!t n. llength_rel t n ==> !m. llength_rel t m ==> (m = n)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC llength_rel_ind THEN SRW_TAC [][] THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [llength_rel_cases]) THEN
  FULL_SIMP_TAC (srw_ss()) []);

val llength_rel_nil = prove(
  ``llength_rel [||] n = (n = 0)``,
  ONCE_REWRITE_TAC [llength_rel_cases] THEN SRW_TAC [][]);
val _ = augment_srw_ss [rewrites [llength_rel_nil]]

val LLENGTH = new_definition(
  "LLENGTH",
  ``LLENGTH ll = if LFINITE ll then SOME (@n. llength_rel ll n) else NONE``);

val LLENGTH_THM = store_thm(
  "LLENGTH_THM",
  ``(LLENGTH LNIL = SOME 0) /\
    (!h t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t))``,
  SRW_TAC [][LLENGTH] THEN
  `?n. llength_rel t n` by METIS_TAC [lfinite_llength] THEN
  `!m. llength_rel t m = (m = n)` by METIS_TAC [llength_unique] THEN
  SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [llength_rel_cases] THEN SRW_TAC [][]);
val _ = export_rewrites ["LLENGTH_THM"]

val LLENGTH_0 = Q.store_thm("LLENGTH_0[simp]",
  `(LLENGTH x = SOME 0) <=> (x = [||])`,
  llist_CASE_TAC ``x : 'a llist`` THEN
  SIMP_TAC bool_ss [LLENGTH_THM, LCONS_NOT_NIL] THEN
  Cases_on `LLENGTH t` THEN
  SIMP_TAC std_ss [OPTION_MAP_DEF, NOT_SUC]) ;

val LFINITE_HAS_LENGTH = store_thm(
  "LFINITE_HAS_LENGTH",
  ``!ll. LFINITE ll ==> ?n. LLENGTH ll = SOME n``,
  SRW_TAC [][LLENGTH]);

val NOT_LFINITE_NO_LENGTH = store_thm(
  "NOT_LFINITE_NO_LENGTH",
  ``!ll. ~LFINITE ll ==> (LLENGTH ll = NONE)``,
  SIMP_TAC (srw_ss()) [LLENGTH]);

val LFINITE_LLENGTH = Q.store_thm("LFINITE_LLENGTH",
  `LFINITE ll <=> ?n. LLENGTH ll = SOME n`,
  rw[EQ_IMP_THM,LFINITE_HAS_LENGTH] >>
  spose_not_then strip_assume_tac >>
  imp_res_tac NOT_LFINITE_NO_LENGTH >>
  fs[])

val LFINITE_INDUCTION = save_thm(
  "LFINITE_INDUCTION",
  CONV_RULE (RENAME_VARS_CONV ["P"]) LFINITE_ind);

val LFINITE_STRONG_INDUCTION = save_thm(
  "LFINITE_STRONG_INDUCTION",
  SIMP_RULE (srw_ss()) [LFINITE_THM]
  (Q.SPEC `\ll. LFINITE ll /\ P ll` LFINITE_INDUCTION))

Theorem LFINITE_MAP[simp]:
  !f (ll:'a llist). LFINITE (LMAP f ll) = LFINITE ll
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    Q_TAC SUFF_TAC `!ll1. LFINITE ll1 ==>
                          !ll. (ll1 = LMAP f ll) ==> LFINITE ll`
          THEN1 SRW_TAC [][] THEN
    HO_MATCH_MP_TAC LFINITE_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LMAP, LFINITE_THM],
    Q.ID_SPEC_TAC `ll` THEN HO_MATCH_MP_TAC LFINITE_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LFINITE_THM, LMAP]
  ]
QED

Theorem LFINITE_APPEND[simp]:
  !ll1 ll2. LFINITE (LAPPEND ll1 ll2) <=> LFINITE ll1 /\ LFINITE ll2
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    Q_TAC SUFF_TAC `!ll0. LFINITE ll0 ==>
                          !ll1 ll2. (LAPPEND ll1 ll2 = ll0) ==>
                                    LFINITE ll1 /\ LFINITE ll2`
          THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN REPEAT STRIP_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll1` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND] THEN
    PROVE_TAC [],
    REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
    Q.ID_SPEC_TAC `ll1` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND]
  ]
QED

val LTAKE_LNTH_EL = Q.store_thm ("LTAKE_LNTH_EL",
  `!n ll m l.
    (LTAKE n ll = SOME l) /\
    m < n
    ==>
    (LNTH m ll = SOME (EL m l))`,
  Induct>>simp[]>>
  (* "Cases" *)
  (fn (g as(_,w)) => (gen_tac >>
    FULL_STRUCT_CASES_TAC(ISPEC(#1(dest_forall w))llist_CASES))g) >>
  simp[PULL_EXISTS] >> Cases>>simp[]);

val NOT_LFINITE_APPEND = store_thm(
  "NOT_LFINITE_APPEND",
  ``!ll1 ll2. ~LFINITE ll1 ==> (LAPPEND ll1 ll2 = ll1)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ~LFINITE ll2 /\  ?ll3. ll1 = LAPPEND ll2 ll3` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `ll4` llist_CASES) THEN
    FULL_SIMP_TAC (srw_ss()) [LFINITE_THM, LAPPEND, LHD_THM, LTL_THM] THEN
    PROVE_TAC []
  ]);

val LFINITE_LAPPEND_IMP_NIL = Q.store_thm("LFINITE_LAPPEND_IMP_NIL",
  `!ll. LFINITE ll ==> !l2. (LAPPEND ll l2 = ll) ==> (l2 = [||])`,
  ho_match_mp_tac LFINITE_INDUCTION >> simp[])

val LLENGTH_MAP = store_thm(
  "LLENGTH_MAP",
  ``!ll f. LLENGTH (LMAP f ll) = LLENGTH ll``,
  REPEAT GEN_TAC THEN Cases_on `LFINITE ll` THENL [
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [LLENGTH_THM, LMAP],
    PROVE_TAC [NOT_LFINITE_NO_LENGTH, LFINITE_MAP]
  ]);

val LLENGTH_APPEND = store_thm(
  "LLENGTH_APPEND",
  ``!ll1 ll2.
       LLENGTH (LAPPEND ll1 ll2) =
         if LFINITE ll1 /\ LFINITE ll2 then
           SOME (THE (LLENGTH ll1) + THE (LLENGTH ll2))
         else
           NONE``,
  REPEAT GEN_TAC THEN
  Cases_on `LFINITE (LAPPEND ll1 ll2)` THENL [
    POP_ASSUM (fn th => `LFINITE ll1 /\ LFINITE ll2` by
                        PROVE_TAC [th, LFINITE_APPEND]) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll2` THEN
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
    HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
    SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN
    ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_CLAUSES],
    `LLENGTH (LAPPEND ll1 ll2) = NONE`
      by PROVE_TAC [NOT_LFINITE_NO_LENGTH] THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

(* ----------------------------------------------------------------------
    mapping in and out of ordinary (finite) lists
   ---------------------------------------------------------------------- *)

val toList = new_definition(
  "toList",
  ``toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE``);

val toList_THM = store_thm(
  "toList_THM",
  ``(toList LNIL = SOME []) /\
    (!h t. toList (LCONS h t) = OPTION_MAP (CONS h) (toList t))``,
  SIMP_TAC (srw_ss()) [toList, LFINITE_THM, LLENGTH_THM, LTAKE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  ASM_SIMP_TAC (srw_ss()) [LTAKE_THM, LHD_THM, LTL_THM]);

val fromList_def = Define`
  (fromList [] = LNIL) /\ (fromList (h::t) = LCONS h (fromList t))
`;
val _ = export_rewrites ["fromList_def"]

val fromList_EQ_LNIL = Q.store_thm(
  "fromList_EQ_LNIL[simp]",
  `(fromList l = LNIL) <=> (l = [])`,
  Cases_on `l` >> simp[]);

val LHD_fromList = Q.store_thm(
  "LHD_fromList",
  `LHD (fromList l) = if NULL l then NONE else SOME (HD l)`,
  Cases_on `l` >> simp[]);

val LTL_fromList = Q.store_thm(
  "LTL_fromList",
  `LTL (fromList l) = if NULL l then NONE else SOME (fromList (TL l))`,
  Cases_on `l` >> simp[]);

val LFINITE_fromList = store_thm(
  "LFINITE_fromList",
  ``!l. LFINITE (fromList l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val LLENGTH_fromList = store_thm(
  "LLENGTH_fromList[simp]",
  ``!l. LLENGTH (fromList l) = SOME (LENGTH l)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val LTAKE_fromList = store_thm(
  "LTAKE_fromList",
  ``!l. LTAKE (LENGTH l) (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) []);

val from_toList = store_thm(
  "from_toList",
  ``!l. toList (fromList l) = SOME l``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [toList_THM]);

val LFINITE_toList = store_thm(
  "LFINITE_toList",
  ``!ll. LFINITE ll ==> ?l. toList ll = SOME l``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [toList_THM]);

val LFINITE_toList_SOME = Q.store_thm("LFINITE_toList_SOME",
  `LFINITE ll <=> IS_SOME (toList ll)`,
  EQ_TAC >> simp[optionTheory.IS_SOME_EXISTS,LFINITE_toList] >>
  rw[] >> fs[toList])

val to_fromList = store_thm(
  "to_fromList",
  ``!ll. LFINITE ll ==> (fromList (THE (toList ll)) = ll)``,
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC (srw_ss()) [toList_THM] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LFINITE_toList THEN FULL_SIMP_TAC (srw_ss()) []);

Theorem LTAKE_LAPPEND2:
  !n l1 l2.
    LTAKE n l1 = NONE ==>
    LTAKE n (LAPPEND l1 l2) =
    OPTION_MAP (APPEND (THE(toList l1))) (LTAKE (n - THE(LLENGTH l1)) l2)
Proof
  rpt gen_tac >> strip_tac >>
  `LFINITE l1` by metis_tac[LFINITE] >>
  qpat_x_assum`_ = _`mp_tac >>
  map_every qid_spec_tac[`l2`,`n`] >>
  pop_assum mp_tac >>
  qid_spec_tac`l1` >>
  ho_match_mp_tac LFINITE_INDUCTION >>
  rw[toList_THM] >- (
    Cases_on`LTAKE n l2`>>simp[] ) >>
  Cases_on`n`>>fs[] >>
  simp[optionTheory.OPTION_MAP_COMPOSE] >>
  `LFINITE l1` by metis_tac[LFINITE] >>
  imp_res_tac LFINITE_toList >> simp[] >>
  imp_res_tac LFINITE_HAS_LENGTH >> simp[] >>
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >> simp[FUN_EQ_THM]
QED

Theorem LNTH_fromList:
  LNTH n (fromList l) = if n < LENGTH l then SOME (EL n l) else NONE
Proof
  ‘!l. LFINITE l ==>
       !n. LNTH n l = if n < THE(LLENGTH l) then SOME (EL n (THE(toList l)))
                      else NONE’
    by (Induct_on ‘LFINITE’ >> rw[] >>
        imp_res_tac LFINITE_HAS_LENGTH >> simp[] >>
        Cases_on`n`>>simp[toList_THM] >- (
         imp_res_tac LFINITE_toList >> simp[] ) >>
        rw[] >>
        imp_res_tac LFINITE_toList >> simp[] ) >>
  metis_tac[LFINITE_fromList,LLENGTH_fromList,THE_DEF,LFINITE_toList,
            from_toList]
QED

val lnth_fromList_some = Q.store_thm ("lnth_fromList_some",
  `!n l. n < LENGTH l <=> (LNTH n (fromList l) = SOME (EL n l))`,
  Induct_on `l` >> rw [] >>
  Cases_on `n` >> rw [LNTH_THM] >> fs []);

(* ----------------------------------------------------------------------
    LDROP : num -> 'a llist -> 'a llist option

    drops a prefix of given length, if there are that many items to be
    dropped
   ---------------------------------------------------------------------- *)

val LDROP = new_recursive_definition {
  def = ``(LDROP 0 ll = SOME ll) /\
          (LDROP (SUC n) ll = OPTION_JOIN (OPTION_MAP (LDROP n) (LTL ll)))``,
  rec_axiom = prim_recTheory.num_Axiom,
  name = "LDROP"};

val FUNPOW_BIND_NONE = Q.prove (
  `!n. FUNPOW (\m. OPTION_BIND m g) n NONE = NONE`,
  Induct THEN ASM_SIMP_TAC bool_ss [FUNPOW, OPTION_BIND_def]) ;

val LDROP_FUNPOW = Q.store_thm ("LDROP_FUNPOW",
  `!n ll. LDROP n ll = FUNPOW (\m. OPTION_BIND m LTL) n (SOME ll)`,
  Induct THEN RULE_ASSUM_TAC GSYM THEN
  SIMP_TAC std_ss [LDROP, FUNPOW, FUNPOW_BIND_NONE] THEN
  GEN_TAC THEN Cases_on `LTL ll` THEN
  ASM_SIMP_TAC std_ss [FUNPOW_BIND_NONE]) ;

val LDROP_THM = store_thm(
  "LDROP_THM",
  ``(!ll. LDROP 0 ll = SOME ll) /\
    (!n. LDROP (SUC n) LNIL = NONE) /\
    (!n h t. LDROP (SUC n) (LCONS h t) = LDROP n t)``,
  SIMP_TAC (srw_ss()) [LDROP, LTL_THM]);
val _ = export_rewrites ["LDROP_THM"]

val LDROP1_THM = store_thm(
  "LDROP1_THM",
  ``LDROP 1 = LTL``,
  SIMP_TAC bool_ss [DECIDE ``1 = SUC 0``,
    LDROP_FUNPOW, FUN_EQ_THM, FUNPOW, OPTION_BIND_def]);

val LNTH_HD_LDROP = Q.store_thm ("LNTH_HD_LDROP",
  `!n ll. LNTH n ll = OPTION_BIND (LDROP n ll) LHD`,
  REWRITE_TAC [LDROP_FUNPOW] THEN
  Induct THEN RULE_ASSUM_TAC GSYM THEN
  SIMP_TAC std_ss [LNTH, FUNPOW, FUNPOW_BIND_NONE] THEN
  GEN_TAC THEN Cases_on `LTL ll` THEN
  ASM_SIMP_TAC std_ss [FUNPOW_BIND_NONE]) ;

val NOT_LFINITE_TAKE = store_thm(
  "NOT_LFINITE_TAKE",
  ``!ll. ~LFINITE ll ==> !n. ?y. LTAKE n ll = SOME y``,
  SIMP_TAC (srw_ss()) [LFINITE] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Q.SPEC `n`) THEN
  Cases_on `LTAKE n ll` THEN FULL_SIMP_TAC (srw_ss()) []);

val LFINITE_TAKE = store_thm(
  "LFINITE_TAKE",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LTAKE n ll = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LTAKE_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (srw_ss()) []);

val NOT_LFINITE_DROP = store_thm(
  "NOT_LFINITE_DROP",
  ``!ll. ~LFINITE ll ==> !n. ?y. LDROP n ll = SOME y``,
  CONV_TAC (BINDER_CONV RIGHT_IMP_FORALL_CONV THENC
            SWAP_VARS_CONV) THEN
  Induct THEN SIMP_TAC (srw_ss()) [LDROP] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val LFINITE_DROP = store_thm(
  "LFINITE_DROP",
  ``!n ll. LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           ?y. LDROP n ll = SOME y``,
  Induct THEN SIMP_TAC (srw_ss()) [LDROP_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LLENGTH_THM, LFINITE_THM, LDROP_THM] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC LFINITE_HAS_LENGTH THEN
  FULL_SIMP_TAC (srw_ss()) []);

val option_case_NONE = prove(
  ``!f x y. (option_CASE x NONE f = SOME y) =
            (?z. (x = SOME z) /\ (f z = SOME y))``,
  REPEAT GEN_TAC THEN Cases_on `x` THEN SIMP_TAC (srw_ss()) []);

val LTAKE_DROP = store_thm(
  "LTAKE_DROP",
  ``(!n ll:'a llist.
        ~LFINITE ll ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll)) /\
    (!n ll:'a llist.
        LFINITE ll /\ n <= THE (LLENGTH ll) ==>
        (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll))``,
  CONJ_TAC THEN Induct THEN SRW_TAC [][] THENL [
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC NOT_LFINITE_TAKE THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `y` ASSUME_TAC o Q.SPEC `n`) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    Q_TAC SUFF_TAC `y = THE (LTAKE n t)` THEN1 METIS_TAC [] THEN
    ASM_SIMP_TAC (srw_ss()) [],
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC LFINITE_HAS_LENGTH THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `?z. LTAKE n t = SOME z` by ASM_SIMP_TAC (srw_ss()) [LFINITE_TAKE] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `z = THE (LTAKE n t)` by ASM_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
  ]);

val LDROP_ADD = store_thm("LDROP_ADD",
  ``!k1 k2 x.
      LDROP (k1 + k2) x = case LDROP k1 x of
                          | NONE => NONE
                          | SOME ll => LDROP k2 ll``,
  ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] THEN
  REWRITE_TAC [LDROP_FUNPOW, arithmeticTheory.FUNPOW_ADD] THEN
  REPEAT GEN_TAC THEN CASE_TAC THEN
  REWRITE_TAC [FUNPOW_BIND_NONE]) ;

val LDROP_SOME_LLENGTH = Q.store_thm("LDROP_SOME_LLENGTH",
  `(LDROP n ll = SOME l) /\ (LLENGTH ll = SOME m) ==>
     n <= m /\ (LLENGTH l = SOME (m - n))`,
  `!ll. LFINITE ll ==>
     !n m l.
       (LDROP n ll = SOME l) /\ (LLENGTH ll = SOME m) ==>
         n <= m /\ (LLENGTH l = SOME (m - n))`
  suffices_by (
    ntac 2 strip_tac >>
    first_assum (match_mp_tac o MP_CANON) >>
    qexists_tac`ll`>>simp[] >>
    metis_tac[NOT_LFINITE_NO_LENGTH,optionTheory.NOT_NONE_SOME] ) >>
  ho_match_mp_tac LFINITE_INDUCTION >>
  strip_tac >- ( Cases >> simp[] ) >>
  ntac 3 strip_tac >> Cases >> simp[PULL_EXISTS] )

val LFINITE_LNTH_NONE = Q.store_thm("LFINITE_LNTH_NONE",
  `LFINITE ll <=> ?n. LNTH n ll = NONE`,
  EQ_TAC >- (
    qid_spec_tac`ll` >>
    ho_match_mp_tac LFINITE_INDUCTION >>
    rw[] >> qexists_tac`SUC n` >> simp[] ) >>
  metis_tac[NOT_LFINITE_TAKE,LTAKE_LNTH_EL,
            optionTheory.NOT_SOME_NONE,
            prim_recTheory.LESS_SUC_REFL]);

val infinite_lnth_some = Q.store_thm ("infinite_lnth_some",
  `!ll. ~LFINITE ll <=> !n. ?x. LNTH n ll = SOME x`,
  rw [LFINITE_LNTH_NONE] >>
  metis_tac [optionTheory.NOT_SOME_NONE, optionTheory.option_nchotomy]);

val LNTH_LAPPEND = Q.store_thm("LNTH_LAPPEND",
  `LNTH n (LAPPEND l1 l2) =
   case LLENGTH l1 of NONE => LNTH n l1
   | SOME m => if n < m then LNTH n l1 else LNTH (n-m) l2`,
  Cases_on`LFINITE l1` >- (
    map_every qid_spec_tac[`l2`,`n`] >>
    pop_assum mp_tac >> qid_spec_tac`l1` >>
    ho_match_mp_tac LFINITE_STRONG_INDUCTION >> rw[] >>
    imp_res_tac LFINITE_HAS_LENGTH >> fs[] >>
    Cases_on`n`>>fs[] ) >>
  BasicProvers.CASE_TAC >>
  fs[LFINITE_LLENGTH] >>
  `!n. ?x. LNTH n l1 = SOME x` by (
    metis_tac[LFINITE_LNTH_NONE,LFINITE_LLENGTH,
              optionTheory.option_CASES,optionTheory.NOT_SOME_NONE] ) >>
  Cases_on`LTAKE (SUC n) l1` >- (
    metis_tac[optionTheory.NOT_SOME_NONE,LTAKE_EQ_NONE_LNTH] ) >>
  qspecl_then[`SUC n`,`l1`,`l2`]mp_tac LTAKE_LAPPEND1 >>
  simp[] >> strip_tac >>
  imp_res_tac LTAKE_LNTH_EL >>
  rpt(pop_assum(qspec_then`n`mp_tac)) >> simp[])

val LNTH_ADD = Q.store_thm("LNTH_ADD",
  `!a b ll. LNTH (a + b) ll = OPTION_BIND (LDROP a ll) (LNTH b)`,
  Induct >> simp[] >> rpt gen_tac >>
  `b + SUC a = SUC (a + b)` by simp[] >>
  pop_assum SUBST1_TAC >>
  qspec_then`ll`FULL_STRUCT_CASES_TAC llist_CASES >>
  simp[])

val lnth_some_down_closed = Q.store_thm ("lnth_some_down_closed",
  `!ll x n1 n2.
    (LNTH n1 ll = SOME x) /\ n2 <= n1
   ==>
    ?y. (LNTH n2 ll = SOME y)`,
  Induct_on `n1` >> rw [] >>
  Q.ISPEC_THEN`ll`FULL_STRUCT_CASES_TAC llist_CASES >>
  fs [] >> Cases_on `n2` >> fs []);

(* ----------------------------------------------------------------------
    exists : ('a -> bool) -> 'a llist -> bool

    defined inductively
   ---------------------------------------------------------------------- *)

Inductive exists:
  (!h t. P h ==> exists P (h ::: t)) /\
  (!h t. exists P t ==> exists P (h ::: t))
End

Theorem exists_thm[simp]:
    (exists P [||] = F) /\
    (exists P (h:::t) <=> P h \/ exists P t)
Proof
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exists_cases])) THEN
  SRW_TAC [][]
QED

val exists_LNTH = store_thm(
  "exists_LNTH",
  ``!l. exists P l = ?n e. (SOME e = LNTH n l) /\ P e``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC exists_ind THEN SRW_TAC [][] THENL [
      MAP_EVERY Q.EXISTS_TAC [`0`, `h`] THEN SRW_TAC [][],
      MAP_EVERY Q.EXISTS_TAC [`SUC n`, `e`] THEN SRW_TAC [][]
    ],
    Q_TAC SUFF_TAC `!n l e. (SOME e = LNTH n l) /\ P e ==> exists P l`
          THEN1 METIS_TAC [] THEN
    Induct THEN REPEAT GEN_TAC THEN
    Q.SPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val MONO_exists = store_thm(
  "MONO_exists",
  ``(!x. P x ==> Q x) ==> (exists P l ==> exists Q l)``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `l` THEN HO_MATCH_MP_TAC exists_ind THEN
  SRW_TAC [][]);
val _ = IndDefLib.export_mono "MONO_exists"

val exists_strong_ind = save_thm(
  "exists_strong_ind",
  exists_ind |> Q.SPECL [`P`, `\ll. Q ll /\ exists P ll`]
             |> SIMP_RULE (srw_ss()) []
             |> Q.GEN `Q` |> Q.GEN `P`);

val exists_LDROP = store_thm(
  "exists_LDROP",
  ``exists P ll <=> ?n a t. (LDROP n ll = SOME (a:::t)) /\ P a``,
  EQ_TAC THENL [
    Q_TAC SUFF_TAC
       `!ll. exists P ll ==> ?n a t. (LDROP n ll = SOME (a:::t)) /\ P a`
       THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC exists_strong_ind THEN SRW_TAC [][] THENL [
      Q.EXISTS_TAC `0` THEN SRW_TAC [][],
      Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][]
    ],
    Q_TAC SUFF_TAC
       `!n ll a t. (LDROP n ll = SOME (a:::t)) /\ P a ==> exists P ll`
       THEN1 METIS_TAC [] THEN
    Induct THEN SRW_TAC [][] THEN
    Q.SPEC_THEN `ll` FULL_STRUCT_CASES_TAC llist_CASES THEN
    FULL_SIMP_TAC (srw_ss()) [LDROP]
  ]);

Theorem exists_thm_strong:
  exists P ll <=> ?n a t l. LDROP n ll = SOME (a:::t) /\ P a /\
                            LTAKE n ll = SOME l /\ EVERY ($~ o P) l
Proof
  simp[exists_LDROP,EQ_IMP_THM] >>
  reverse conj_tac >- metis_tac[] >>
  simp[whileTheory.LEAST_EXISTS, SimpL “$==>”] >> strip_tac >>
  goal_assum drule >>
  rw[] >>
  rpt(pop_assum mp_tac) >>
  rename1`LDROP n ll = SOME (a:::t)`>>
  MAP_EVERY qid_spec_tac [`a`,`t`,`ll`,`n`] >>
  Induct >- rw[] >>
  gen_tac >>
  qspec_then`ll`FULL_STRUCT_CASES_TAC llist_CASES>>
  rw[] >>
  rename1`LDROP _ (h:::_)`>>
  `~P h`
    by(first_x_assum(qspec_then `0` mp_tac) >>
       impl_tac >- simp[] >>
       rename1`h:::t`>>
       disch_then(qspecl_then [`h`,`t`] mp_tac) >> simp[]) >>
  first_x_assum (drule_then drule) >>
  impl_tac
  >- (rw[] >> rename1`n' < n` >> first_x_assum(qspec_then `SUC n'` mp_tac) >>
      rw[]) >>
  rw[PULL_EXISTS]
QED

(* ----------------------------------------------------------------------
    companion LL_ALL/every (has a coinduction principle)
   ---------------------------------------------------------------------- *)

val every_def = Define`every P ll = ~exists ((~) o P) ll`
val _ = overload_on ("LL_ALL", ``every``)
val _ = overload_on ("every", ``every``)

val every_coind = store_thm(
  "every_coind",
  ``!P Q.
       (!h t. Q (h:::t) ==> P h /\ Q t) ==>
       !ll. Q ll ==> every P ll``,
  SIMP_TAC (srw_ss()) [every_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!ll. exists ($~ o P) ll ==> ~Q ll` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC exists_ind THEN
  SRW_TAC [][DECIDE ``(~p ==> ~q) = (q ==> p)``] THEN METIS_TAC []);

Theorem every_thm[simp]:
    (every P [||] = T) /\
    (every P (h:::t) <=> P h /\ every P t)
Proof SRW_TAC [][every_def]
QED
val LL_ALL_THM = save_thm("LL_ALL_THM", every_thm)

val MONO_every = store_thm(
  "MONO_every",
  ``(!x. P x ==> Q x) ==> (every P l ==> every Q l)``,
  STRIP_TAC THEN Q.ID_SPEC_TAC `l` THEN HO_MATCH_MP_TAC every_coind THEN
  SRW_TAC [][]);
val _ = export_mono "MONO_every"

val every_strong_coind = save_thm(
  "every_strong_coind",
  every_coind |> Q.SPECL [`P`, `\ll. Q ll \/ every P ll`]
              |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, IMP_CONJ_THM,
                                       FORALL_AND_THM]
              |> Q.GEN `Q` |> Q.GEN `P`);

Theorem every_LNTH:
  !P ll. every P ll <=> !n e. LNTH n ll = SOME e ==> P e
Proof
  fs [every_def,exists_LNTH] \\
  CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(PURE_ONCE_REWRITE_CONV[EQ_SYM_EQ]))) \\
  simp[IMP_DISJ_THM]
QED

Theorem every_LDROP:
  !f i ll1 ll2.
  every f ll1 /\
  LDROP i ll1 = SOME ll2
  ==> every f ll2
Proof
  Induct_on ‘i’ >> rpt GEN_TAC >>
  qspec_then ‘ll1’ strip_assume_tac llist_CASES >> pop_assum SUBST_ALL_TAC >>
  rw[] >> rw[] >> res_tac
QED

(*
  could alternatively take contrapositives of the exists induction principle:

  exists_strong_ind |> Q.SPECL [`(~) o P`, `(~) o Q`]
                     |> CONV_RULE (BINOP_CONV (ONCE_REWRITE_CONV [MONO_NOT_EQ]))
                     |> SIMP_RULE (srw_ss()) [GSYM every_def]
*)

(* ----------------------------------------------------------------------
    can now define LFILTER and LFLATTEN
   ---------------------------------------------------------------------- *)

val least_lemma = prove(
  ``(?n. P n) ==> ((LEAST) P = if P 0 then 0 else SUC ((LEAST) (P o SUC)))``,
  SRW_TAC [][] THENL [
    Q_TAC SUFF_TAC `(\n. n = 0) ($LEAST P)` THEN1 SRW_TAC [][] THEN
    MATCH_MP_TAC whileTheory.LEAST_ELIM THEN SRW_TAC [][] THENL [
      PROVE_TAC [],
      SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
      `0 < n'` by DECIDE_TAC THEN METIS_TAC []
    ],
    Q_TAC SUFF_TAC `(\n. n = SUC ($LEAST (P o SUC))) ((LEAST) P)` THEN1
          SRW_TAC [][] THEN
    MATCH_MP_TAC whileTheory.LEAST_ELIM THEN CONJ_TAC THENL [
      PROVE_TAC [],
      Q.X_GEN_TAC `p` THEN SRW_TAC [][] THEN
      Q_TAC SUFF_TAC `(\k. p = SUC k) ($LEAST (P o SUC))` THEN1
            SRW_TAC [][] THEN
      MATCH_MP_TAC whileTheory.LEAST_ELIM THEN CONJ_TAC THENL [
        SRW_TAC [][] THEN Cases_on `n` THEN PROVE_TAC [],
        SRW_TAC [][] THEN
        `~(SUC n' < p)` by PROVE_TAC [] THEN
        `(p = SUC n') \/ (p < SUC n')` by DECIDE_TAC THEN
        `?p0. p = SUC p0` by METIS_TAC [arithmeticTheory.num_CASES] THEN
        FULL_SIMP_TAC (srw_ss()) []
      ]
    ]
  ]);

val LFILTER = new_specification
 ("LFILTER", ["LFILTER"],
  prove(
    ``?LFILTER.
        !P ll. LFILTER P ll = if ~ exists P ll then LNIL
                              else
                                if P (THE (LHD ll)) then
                                    LCONS (THE (LHD ll))
                                          (LFILTER P (THE (LTL ll)))
                                else
                                    LFILTER P (THE (LTL ll))``,
    ASSUME_TAC (GEN_ALL
       (Q.ISPEC `\ll. if exists P ll then
                        let n = LEAST n. ?e. (SOME e = LNTH n ll) /\ P e in
                          SOME (THE (LDROP (SUC n) ll),
                                THE (LNTH n ll))
                      else NONE` llist_Axiom_1)) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o CONV_RULE SKOLEM_CONV) THEN
    Q.EXISTS_TAC `g` THEN REPEAT GEN_TAC THEN
    POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `P`) THEN
    Cases_on `exists P ll` THENL [
      POP_ASSUM MP_TAC THEN
      POP_ASSUM
        (fn th => CONV_TAC
                    (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
                  ASSUME_TAC (GSYM th)) THEN
      SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      `?h t. ll = h:::t` by METIS_TAC [llist_CASES, exists_thm] THENL [
        Q.PAT_X_ASSUM `exists P ll` (K ALL_TAC) THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        Q_TAC SUFF_TAC `n = 0` THEN1 SRW_TAC [][] THEN
        CONV_TAC (UNBETA_CONV ``n:num``) THEN UNABBREV_ALL_TAC THEN
        MATCH_MP_TAC whileTheory.LEAST_ELIM THEN SRW_TAC [][] THENL [
          Q.EXISTS_TAC `0` THEN SRW_TAC [][],
          SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
          `0 < n` by DECIDE_TAC THEN
          METIS_TAC [optionTheory.SOME_11, LNTH_THM]
        ],
        FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        `n = SUC (LEAST m. ?e. (SOME e = LNTH m t) /\ P e)`
           by (Q.UNABBREV_TAC `n` THEN
               Q.HO_MATCH_ABBREV_TAC `(LEAST) Q1 = SUC ((LEAST) Q2)` THEN
               `Q2 = Q1 o SUC`
                  by (UNABBREV_ALL_TAC THEN SRW_TAC [][FUN_EQ_THM]) THEN
               POP_ASSUM SUBST1_TAC THEN
               Q.MATCH_ABBREV_TAC `LHS = RHS` THEN
               Q.UNABBREV_TAC `LHS` THEN
               `RHS = if Q1 0 then 0 else RHS` by SRW_TAC [][Abbr`Q1`] THEN
               POP_ASSUM SUBST1_TAC THEN
               Q.UNABBREV_TAC `RHS` THEN
               MATCH_MP_TAC least_lemma THEN
               UNABBREV_ALL_TAC  THEN
               SRW_TAC [][] THEN
               `?m e. (SOME e = LNTH m t) /\ P e`
                   by METIS_TAC [exists_LNTH] THEN
               MAP_EVERY Q.EXISTS_TAC [`SUC m`, `e`] THEN
               SRW_TAC [][]) THEN
        RM_ALL_ABBREVS_TAC THEN SRW_TAC [][] THEN
        FIRST_X_ASSUM
          ((fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) o
           assert (is_forall o concl)) THEN
        SRW_TAC [][] THEN SRW_TAC [][Abbr`n`]
      ],
      POP_ASSUM MP_TAC THEN
      POP_ASSUM
        (fn th => CONV_TAC
                    (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [th])))) THEN
      SRW_TAC [][]
    ]));

val LFILTER_THM = store_thm(
  "LFILTER_THM",
  ``(!P. LFILTER P LNIL = LNIL) /\
    (!P h t. LFILTER P (LCONS h t) = if P h then LCONS h (LFILTER P t)
                                     else LFILTER P t)``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFILTER)) THEN
  SIMP_TAC (srw_ss()) [] THEN
  Cases_on `P h` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `exists P t` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  ONCE_REWRITE_TAC [LFILTER] THEN ASM_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LFILTER_THM"]

val LFILTER_NIL = store_thm(
  "LFILTER_NIL",
  ``!P ll. LL_ALL ($~ o P) ll ==> (LFILTER P ll = LNIL)``,
  ONCE_REWRITE_TAC [LFILTER, every_def] THEN
  `!P. $~ o $~ o P = P` by (GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
                            SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) []);

val LFILTER_EQ_NIL = store_thm(
  "LFILTER_EQ_NIL",
  ``!ll. (LFILTER P ll = LNIL) = every ((~) o P) ll``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, LFILTER_NIL] THEN
  HO_MATCH_MP_TAC every_coind THEN
  SRW_TAC [][]);

val LFILTER_APPEND = store_thm(
  "LFILTER_APPEND",
  ``!P ll1 ll2. LFINITE ll1 ==>
                (LFILTER P (LAPPEND ll1 ll2) =
                 LAPPEND (LFILTER P ll1) (LFILTER P ll2))``,
  REPEAT GEN_TAC THEN Q.ID_SPEC_TAC `ll1` THEN
  HO_MATCH_MP_TAC LFINITE_STRONG_INDUCTION THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC (srw_ss()) []);

Theorem LFILTER_fromList[simp]:
  !p l. LFILTER p (fromList l) = fromList (FILTER p l)
Proof
  Induct_on ‘l’ \\ rw[]
QED

Theorem LFILTER_EQ_CONS:
  LFILTER P ll = h:::t
  ==> ?l ll'. ll = LAPPEND (fromList l) (h:::ll') /\
              EVERY ($~ o P) l /\ P h /\
              LFILTER P ll' = t
Proof
  strip_tac >>
  rename1‘LFILTER P ll’>>
  ‘exists P ll’ by(fs[Once LFILTER,CaseEq "bool"]) >>
  fs[exists_thm_strong] >>
  rename1‘LDROP n ll = SOME (a:::t')’>>
  rename1‘LTAKE n ll = SOME l’>>
  ‘ll = LAPPEND (fromList l) (a:::t')’
    by(reverse(Cases_on ‘LFINITE ll’)
       >- (drule_then
           (qspec_then ‘n’ (fn thm => PURE_ONCE_REWRITE_TAC[GSYM thm]))
           (CONJUNCT1 LTAKE_DROP) >>
           simp[]) >>
       ‘n <= THE(LLENGTH ll)’
         by(fs[LFINITE_LLENGTH] >> metis_tac[LDROP_SOME_LLENGTH]) >>
       drule_all_then (fn thm => PURE_ONCE_REWRITE_TAC[GSYM thm])
                      (cj 2 LTAKE_DROP) >>
       simp[]) >>
  BasicProvers.VAR_EQ_TAC >>
  fs[LFINITE_fromList,LFILTER_APPEND,LFILTER_fromList] >>
  ‘FILTER P l = []’ by(fs[listTheory.FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  fs[] >> rpt(BasicProvers.VAR_EQ_TAC) >>
  metis_tac[]
QED

Theorem every_LFILTER:
  !ll P. every P (LFILTER P ll)
Proof
  rpt strip_tac >>
  rename1`every P (LFILTER P ll)`>>
  `!ll. (?ll'. ll = LFILTER P ll') ==> every P ll
  ` by(ho_match_mp_tac every_coind >>
       rw[] >> first_x_assum(ASSUME_TAC o GSYM) >>
       drule_then strip_assume_tac LFILTER_EQ_CONS >>
       fs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem every_LAPPEND1:
  !P ll1 ll2. every P (LAPPEND ll1 ll2) ==> every P ll1
Proof
  strip_tac
  >> fs[Once (GSYM PULL_EXISTS)]
  >> ho_match_mp_tac every_coind
  >> rw[PULL_EXISTS]
  >> goal_assum drule
QED

Theorem every_fromList_EVERY:
  !l P. every P (fromList l) = EVERY P l
Proof
  Induct >> rw[]
QED

Theorem every_LAPPEND2_LFINITE:
  !l P ll. LFINITE l /\ every P (LAPPEND l ll) ==> every P ll
Proof
  Ho_Rewrite.REWRITE_TAC[GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac LFINITE_ind
  >> fs[]
QED

Theorem every_LFILTER_imp:
  !Q P ll. every Q ll ==> every Q (LFILTER P ll)
Proof
  rpt strip_tac >>
  rename1`every Q (LFILTER P ll)`
  >> `!ll. (?ll'. ll = LFILTER P ll' /\ every Q ll') ==> every Q ll` by (
    ho_match_mp_tac every_coind
    >> rw[] >> qpat_x_assum `_:::_ = _`(ASSUME_TAC o GSYM)
    >> drule_then strip_assume_tac LFILTER_EQ_CONS
    >> BasicProvers.VAR_EQ_TAC
    >> rename1 `LAPPEND (fromList l) (h:::llll)`
    >> qspec_then `l` assume_tac LFINITE_fromList
    >> BasicProvers.VAR_EQ_TAC
    >> drule_all every_LAPPEND2_LFINITE
    >> rw[every_thm,AC CONJ_ASSOC CONJ_COMM]
    >> goal_assum drule
    >> REFL_TAC
  )
  >> metis_tac[]
QED

val LFLATTEN = new_specification
 ("LFLATTEN", ["LFLATTEN"],
  prove(
    ``?LFLATTEN.
      !ll. LFLATTEN (ll:'a llist llist) =
             if LL_ALL ($= LNIL) ll then LNIL
             else
                if THE (LHD ll) = LNIL then
                   LFLATTEN (THE (LTL ll))
                else
                   LCONS (THE (LHD (THE (LHD ll))))
                         (LFLATTEN (LCONS (THE (LTL (THE (LHD ll))))
                                          (THE (LTL ll))))``,
    ASSUME_TAC (
      Q.ISPEC `\ll. if LL_ALL ($= LNIL) ll then NONE
                   else
                     let n = LEAST n. ?e. (SOME e = LNTH n ll) /\ ~(e = [||])
                     in
                        let nlist = THE (LNTH n ll)
                        in
                            SOME(LCONS (THE (LTL nlist))
                                       (THE (LDROP (SUC n) ll)),
                                 THE (LHD nlist))` llist_Axiom) THEN
    POP_ASSUM (Q.X_CHOOSE_THEN `g` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `g` THEN GEN_TAC THEN
    Cases_on `LL_ALL ($= LNIL) ll` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      `LTL (g ll) = NONE` by ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC (srw_ss()) [],
      ALL_TAC
    ] THEN
    `?h t. ll = LCONS h t` by METIS_TAC [llist_CASES,every_thm] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC (srw_ss()) [] THEN
    Cases_on `h = LNIL` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      FULL_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      REPEAT (FIRST_X_ASSUM (fn th =>
                             MP_TAC (Q.SPEC `LCONS LNIL t` th) THEN
                             MP_TAC (Q.SPEC `t` th))) THEN
      ASM_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      `?n e. (SOME e = LNTH n t) /\ ~(e = [||])`
           by (FULL_SIMP_TAC (srw_ss()) [every_def, exists_LNTH] THEN
               METIS_TAC []) THEN
      `(LEAST n. ?e. (SOME e = LNTH n ([||]:::t)) /\ ~(e = [||])) =
       SUC (LEAST n. ?e. (SOME e = LNTH n t) /\ ~(e = [||]))`
         by (Q.MATCH_ABBREV_TAC `(LEAST) Q1 = SUC ((LEAST) Q2)` THEN
             `Q2 = Q1 o SUC` by SRW_TAC [][Abbr`Q1`, Abbr`Q2`, FUN_EQ_THM] THEN
             POP_ASSUM SUBST1_TAC THEN Q.UNABBREV_TAC `Q2` THEN
             Q.MATCH_ABBREV_TAC `(LEAST)Q1 = RHS` THEN
             `RHS = if Q1 0 then 0 else RHS` by SRW_TAC [][Abbr`Q1`] THEN
             POP_ASSUM SUBST1_TAC THEN Q.UNABBREV_TAC `RHS` THEN
             MATCH_MP_TAC least_lemma THEN
             Q.UNABBREV_TAC `Q1` THEN
             Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][] THEN METIS_TAC []) THEN
      POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][LET_THM] THEN
      `?h1 t1. g t = h1 ::: t1`
         by METIS_TAC [LHD_EQ_NONE, llist_CASES,
                       optionTheory.NOT_SOME_NONE] THEN
      POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][LHDTL_EQ_SOME],

      (* ~(h = LNIL) *)
      FULL_SIMP_TAC (srw_ss()) [LL_ALL_THM] THEN
      ASM_SIMP_TAC (srw_ss()) [LHDTL_EQ_SOME] THEN
      Q.SUBGOAL_THEN
        `(LEAST n. ?e. (SOME e = LNTH n (h:::t)) /\ ~(e = [||])) = 0`
      SUBST_ALL_TAC THENL [
        SRW_TAC [][whileTheory.LEAST_DEF] THEN
        ONCE_REWRITE_TAC [whileTheory.WHILE] THEN SRW_TAC [][],
        ALL_TAC
      ] THEN SRW_TAC [][LET_THM]
    ]));

val LFLATTEN_THM = store_thm(
  "LFLATTEN_THM",
  ``(LFLATTEN LNIL = LNIL) /\
    (!tl. LFLATTEN (LCONS LNIL t) = LFLATTEN t) /\
    (!h t tl. LFLATTEN (LCONS (LCONS h t) tl) =
              LCONS h (LFLATTEN (LCONS t tl)))``,
  REPEAT STRIP_TAC THEN CONV_TAC (LHS_CONV (REWR_CONV LFLATTEN)) THEN
  SIMP_TAC (srw_ss()) [LL_ALL_THM, LHD_THM, LTL_THM] THEN
  COND_CASES_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  ONCE_REWRITE_TAC [LFLATTEN] THEN ASM_SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LFLATTEN_THM"]

val LFLATTEN_APPEND = store_thm(
  "LFLATTEN_APPEND",
  ``!h t. LFLATTEN (LCONS h t) = LAPPEND h (LFLATTEN t)``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_STRONG_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ?h t. (ll1 = LFLATTEN (LCONS h t)) /\
                                (ll2 = LAPPEND h (LFLATTEN t))` THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    Cases_on `h = LNIL` THENL [
      SRW_TAC [][],

      (* ~(h = LNIL) *)
      POP_ASSUM (fn th =>
        `?h0 t0. h = LCONS h0 t0` by PROVE_TAC [llist_CASES, th]) THEN
      SRW_TAC [][] THEN PROVE_TAC []
    ]
  ]);
val _ = export_rewrites ["LFLATTEN_APPEND"]


val LFLATTEN_EQ_NIL = store_thm(
  "LFLATTEN_EQ_NIL",
  ``!ll. (LFLATTEN ll = LNIL) = LL_ALL ($= LNIL) ll``,
  GEN_TAC THEN EQ_TAC THENL [
    Q.ID_SPEC_TAC `ll` THEN
    HO_MATCH_MP_TAC every_coind THEN
    SRW_TAC [][],
    ONCE_REWRITE_TAC [LFLATTEN] THEN SIMP_TAC (srw_ss()) []
 ]);

val LFLATTEN_SINGLETON = store_thm(
  "LFLATTEN_SINGLETON",
  ``!h. LFLATTEN (LCONS h LNIL) = h``,
  GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_BISIMULATION] THEN
  Q.EXISTS_TAC `\ll1 ll2. ll1 = LFLATTEN (LCONS ll2 LNIL)` THEN
  SIMP_TAC (srw_ss()) [] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `ll4` llist_CASES) THEN
  SIMP_TAC (srw_ss()) [LFLATTEN_THM, LHD_THM, LTL_THM]);

Theorem LFINITE_LFLATTEN_EQN:
  !lll:'a llist llist.
    every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
    LFINITE (LFLATTEN lll) = LFINITE lll
Proof
  ‘!lll.
     LFINITE lll ==> llist$every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
     LFINITE (LFLATTEN lll)’
    by (ho_match_mp_tac LFINITE_ind \\ fs [])
  \\ qsuff_tac ‘!x.
      LFINITE x ==>
      !lll.
        x = LFLATTEN lll /\ llist$every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
        LFINITE lll’ THEN1 (metis_tac [])
  \\ ho_match_mp_tac LFINITE_ind
  \\ fs [PULL_FORALL] \\ rw []
  THEN1 (qspec_then‘lll’FULL_STRUCT_CASES_TAC llist_CASES \\ fs [])
  \\ rename [‘_ = LFLATTEN lll2’]
  \\ qspec_then‘lll2’FULL_STRUCT_CASES_TAC llist_CASES \\ fs []
  \\ rename [‘h2 <> _’]
  \\ qspec_then‘h2’FULL_STRUCT_CASES_TAC llist_CASES \\ fs [] \\ rw []
  \\ rename [‘LAPPEND t2’]
  \\ qspec_then‘t2’FULL_STRUCT_CASES_TAC llist_CASES \\ fs []
  \\ rename [‘LAPPEND t1’]
  \\ first_x_assum (qspec_then ‘(h:::t1) ::: t’ mp_tac) \\ fs []
QED

(*---------------------------------------------------------------------------*)
(* ZIP two streams together, returning LNIL as soon as possible.             *)
(*                                                                           *)
(* LZIP_THM                                                                  *)
(*    |- (!l2. LZIP LNIL l2 = LNIL) /\                                       *)
(*       (!l1. LZIP l1 LNIL = LNIL) /\                                       *)
(*       (!h1 h2 t1 t2.                                                      *)
(*          LZIP (LCONS h1 t1) (LCONS h2 t2) = LCONS (h1,h2) (LZIP t1 t2))   *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

open pairTheory
val LZIP_THM = new_specification
 ("LZIP_THM", ["LZIP"],
  Q.prove
   (`?LZIP:'a llist # 'b llist -> ('a#'b) llist.
    (!l1. LZIP (l1,[||]) = [||]) /\
    (!l2. LZIP ([||],l2) = [||]) /\
    (!h1 h2 t1 t2. LZIP (h1:::t1, h2:::t2) = (h1,h2) ::: LZIP (t1,t2))`,
    let val ax =
       ISPEC
        ``λ(l1,l2).
             if (l1:'a llist = LNIL) \/ (l2:'b llist = LNIL)
              then NONE
              else SOME ((THE(LTL l1),THE(LTL l2)),
                         (THE(LHD l1),THE(LHD l2)))``
         llist_Axiom_1
    in
     STRIP_ASSUME_TAC (SIMP_RULE (srw_ss()) [FORALL_PROD] ax)
       THEN Q.EXISTS_TAC `g`
       THEN REPEAT CONJ_TAC THENL
      [ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
         THEN RW_TAC (srw_ss()) [],
       ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
         THEN RW_TAC (srw_ss()) [],
       REPEAT GEN_TAC THEN
       POP_ASSUM (fn th => GEN_REWRITE_TAC LHS_CONV bool_rewrites [th])
         THEN RW_TAC (srw_ss()) [LTL_THM,LHD_THM]]
    end));
val _ = export_rewrites ["LZIP_THM"]


(*---------------------------------------------------------------------------*)
(* LUNZIP_THM                                                                *)
(*  |- (LUNZIP [||] = ([||],[||])) /\                                        *)
(*     !x y t. LUNZIP ((x,y):::t) =                                          *)
(*                let (ll1,ll2) = LUNZIP t in (x:::ll1,y:::ll2)              *)
(*---------------------------------------------------------------------------*)

Theorem LUNZIP_exists[local]:
  ?LUNZIP. (LUNZIP [||] = ([||]:'a llist, [||]:'b llist)) /\
           (!x y t. LUNZIP ((x:'a, y:'b):::t) =
                    let (ll1, ll2) = LUNZIP t in (x:::ll1, y:::ll2))
Proof
  qspec_then ‘λll. if (LHD ll = NONE) then NONE
                   else SOME (THE (LTL ll), SND (THE (LHD ll)))’
             strip_assume_tac llist_Axiom_1 >>
  qspec_then ‘λll. if (LHD ll = NONE) then NONE
                   else SOME (THE (LTL ll), FST (THE (LHD ll)))’
             strip_assume_tac llist_Axiom_1 >>
  Q.EXISTS_TAC ‘λll. (g' ll, g ll)’ THEN SIMP_TAC list_ss [] THEN
  REPEAT STRIP_TAC THENL [
    POP_ASSUM (ASSUME_TAC o Q.SPEC `[||]`) THEN
    FULL_SIMP_TAC list_ss [LHD_THM],
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `[||]`) THEN
    FULL_SIMP_TAC list_ss [LHD_THM],
    NTAC 2 (POP_ASSUM (MP_TAC o Q.SPEC ‘(x,y):::t’)) THEN
    RW_TAC list_ss [LHD_THM, LTL_THM, LET_THM]
  ]
QED
val LUNZIP_THM = new_specification ("LUNZIP_THM", ["LUNZIP"], LUNZIP_exists);
val _ = export_rewrites ["LUNZIP_THM"]

val LZIP_LUNZIP = Q.store_thm
("LZIP_LUNZIP",
 `!ll: ('a # 'b) llist. LZIP(LUNZIP ll) = ll`,
 REWRITE_TAC [Once LLIST_STRONG_BISIMULATION] THEN
 GEN_TAC THEN
 Q.EXISTS_TAC `λl1 l2. l1 = LZIP (LUNZIP l2)` THEN
 SRW_TAC [][] THEN
 Q.ISPEC_THEN `ll4` STRUCT_CASES_TAC llist_CASES THEN
 SRW_TAC [][] THEN
 Cases_on `h` THEN SRW_TAC [][] THEN SRW_TAC [][]);
val _ = export_rewrites ["LZIP_LUNZIP"]

val LUNFOLD_THM = Q.store_thm
("LUNFOLD_THM",
  `!f x v1 v2.
     ((f x = NONE) ==> (LUNFOLD f x = [||])) /\
     ((f x = SOME (v1,v2)) ==> (LUNFOLD f x = v2:::LUNFOLD f v1))`,
 SRW_TAC [] [] THEN1
 SRW_TAC [] [Once LUNFOLD] THEN
 SRW_TAC [] [Once LUNFOLD]);

val LLIST_EQ = Q.store_thm
("LLIST_EQ",
 `!f g.
   (!x. ((f x = [||]) /\ (g x = [||])) \/
        (?h y. (f x = h:::f y) /\ (g x = h:::g y)))
   ==>
   (!x. f x = g x)`,
 SRW_TAC [] [] THEN
 SRW_TAC [] [Once LLIST_BISIMULATION0] THEN
 Q.EXISTS_TAC `λll1 ll2. ?x. (ll1 = f x) /\ (ll2 = g x)` THEN
 SRW_TAC [] [] THEN
 METIS_TAC []);

val LUNFOLD_EQ = Q.store_thm
("LUNFOLD_EQ",
 `!R f s ll.
    R s ll /\
    (!s ll.
       R s ll
       ==>
       ((f s = NONE) /\ (ll = [||])) \/
       ?s' x ll'.
         (f s = SOME (s',x)) /\ (LHD ll = SOME x) /\ (LTL ll = SOME ll') /\
         R s' ll')
    ==>
    (LUNFOLD f s = ll)`,
 SRW_TAC [] [] THEN
 SRW_TAC [] [Once LLIST_BISIMULATION] THEN
 Q.EXISTS_TAC `λll1 ll2. ?s. (ll1 = LUNFOLD f s) /\ R s ll2` THEN
 SRW_TAC [] [] THEN1
 METIS_TAC [] THEN
 RES_TAC THEN
 SRW_TAC [] [LUNFOLD_THM] THEN
 IMP_RES_TAC LUNFOLD_THM THEN
 SRW_TAC [] [] THEN
 METIS_TAC []);

val LMAP_LUNFOLD = Q.store_thm
("LMAP_LUNFOLD",
 `!f g s.
   LMAP f (LUNFOLD g s) = LUNFOLD (λs. OPTION_MAP (λ(x, y). (x, f y)) (g s)) s`,
 SRW_TAC [] [] THEN
 MATCH_MP_TAC (GSYM LUNFOLD_EQ) THEN
 SRW_TAC [] [] THEN
 Q.EXISTS_TAC `\s ll. ll = LMAP f (LUNFOLD g s)` THEN
 SRW_TAC [] [] THEN
 Cases_on `g s` THEN
 SRW_TAC [] [LUNFOLD_THM] THEN
 Cases_on `x` THEN
 IMP_RES_TAC LUNFOLD_THM THEN
 SRW_TAC [] []);

val LNTH_LDROP = Q.store_thm
("LNTH_LDROP",
 `!n l x. (LNTH n l = SOME x) ==> (LHD (THE (LDROP n l)) = SOME x)`,
 Induct THEN
 SRW_TAC [] [LNTH, LDROP] THEN
 Cases_on `LTL l` THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) []);

val LAPPEND_fromList = Q.store_thm
("LAPPEND_fromList",
 `!l1 l2. LAPPEND (fromList l1) (fromList l2) = fromList (l1 ++ l2)`,
 Induct THEN
 SRW_TAC [] []);

Theorem LFLATTEN_fromList: !l.
  LFLATTEN(fromList(MAP fromList l)) = fromList(FLAT l)
Proof
  Induct >> rw[LAPPEND_fromList]
QED

val LTAKE_LENGTH = Q.store_thm ("LTAKE_LENGTH",
`!n ll l. (LTAKE n ll = SOME l) ==> (n = LENGTH l)`,
Induct THEN
SRW_TAC [] [] THEN
SRW_TAC [] [] THEN
`(ll = [||]) \/ ?h t. ll = h:::t` by METIS_TAC [llist_CASES] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val LTAKE_TAKE_LESS = Q.store_thm("LTAKE_TAKE_LESS",
  `(LTAKE n ll = SOME l) /\ m <= n ==>
   (LTAKE m ll = SOME (TAKE m l))`,
  rw[] >> Cases_on`n=m`>>fs[] >>
  imp_res_tac LTAKE_LENGTH >> rw[] >>
  Cases_on`LTAKE m ll` >- (
    imp_res_tac LTAKE_EQ_NONE_LNTH >>
    `m < LENGTH l` by fsrw_tac[ARITH_ss][] >>
    imp_res_tac LTAKE_LNTH_EL >> fs[] ) >>
  imp_res_tac LTAKE_LENGTH >> simp[] >>
  simp[listTheory.LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
  qmatch_assum_rename_tac`n < LENGTH x` >>
  `n < LENGTH l` by decide_tac >>
  imp_res_tac LTAKE_LNTH_EL >> fs[]);

val LTAKE_LLENGTH_NONE = Q.store_thm("LTAKE_LLENGTH_NONE",
  `(LLENGTH ll = SOME n) /\ n < m ==> (LTAKE m ll = NONE)`,
  rw[] >> `LFINITE ll` by metis_tac[LFINITE_LLENGTH] >>
  `!ll. LFINITE ll ==> !m n. (LLENGTH ll = SOME n) /\ n < m
    ==> (LTAKE m ll = NONE)` suffices_by metis_tac[] >>
  rpt (pop_assum kall_tac) >>
  ho_match_mp_tac LFINITE_INDUCTION >> rw[] >>
  simp[LTAKE_CONS_EQ_NONE] >>
  Cases_on`m`>>fs[])

Theorem LTAKE_LLENGTH_SOME:
  LLENGTH ll = SOME n ==> ?l. LTAKE n ll = SOME l /\ toList ll = SOME l
Proof metis_tac[LFINITE_LLENGTH,to_fromList,from_toList,THE_DEF,toList]
QED

val toList_LAPPEND_APPEND = Q.store_thm("toList_LAPPEND_APPEND",
  `(toList (LAPPEND l1 l2) = SOME x) ==>
    (x = (THE(toList l1)++THE(toList l2)))`,
  Cases_on`l2=[||]`>>simp[toList_THM,LAPPEND_NIL_2ND] >>
  strip_tac >> fs[toList] >>
  rfs[LLENGTH_APPEND] >>
  qmatch_assum_abbrev_tac`LTAKE n (LAPPEND l1 l2) = SOME x` >>
  `LTAKE n l1 = NONE` by (
    match_mp_tac (GEN_ALL LTAKE_LLENGTH_NONE) >>
    imp_res_tac LTAKE_LENGTH >>
    imp_res_tac LFINITE_HAS_LENGTH >>
    fs[Abbr`n`] >>
    qspec_then`l2`FULL_STRUCT_CASES_TAC llist_CASES >> fs[] >>
    decide_tac ) >>
  fs[LTAKE_LAPPEND2,Abbr`n`] >>
  simp[toList]);

val LNTH_LLENGTH_NONE = Q.store_thm("LNTH_LLENGTH_NONE",
  `(LLENGTH l = SOME x) /\ x <= n ==> (LNTH n l = NONE)`,
  rw[arithmeticTheory.LESS_OR_EQ] >- (
    metis_tac[LTAKE_LLENGTH_NONE,LTAKE_EQ_NONE_LNTH] ) >>
  `LFINITE l` by metis_tac[NOT_LFINITE_NO_LENGTH,optionTheory.NOT_NONE_SOME] >>
  `n < SUC n` by simp[] >>
  `LTAKE (SUC n) l = NONE` by metis_tac[LTAKE_LLENGTH_NONE] >>
  qspecl_then[`n`,`l`]mp_tac LTAKE_SNOC_LNTH >>
  simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  metis_tac[LTAKE_EQ_NONE_LNTH,optionTheory.NOT_NONE_SOME])

val LNTH_NONE_MONO = Q.store_thm ("LNTH_NONE_MONO",
  `!m n l.
    (LNTH m l = NONE) /\ m <= n
   ==>
    (LNTH n l = NONE)`,
  rw[] >> match_mp_tac(GEN_ALL LNTH_LLENGTH_NONE) >>
  `LFINITE l` by metis_tac[LFINITE_LNTH_NONE] >>
  `?z. LLENGTH l = SOME z` by metis_tac[LFINITE_HAS_LENGTH] >>
  imp_res_tac LTAKE_LLENGTH_SOME >>
  imp_res_tac LTAKE_LENGTH >>
  `~(m < z)` by metis_tac[LTAKE_LNTH_EL,optionTheory.NOT_SOME_NONE] >>
  rw[] >> decide_tac);

(* cf. This is just another version of lnth_some_down_closed *)
Theorem LNTH_IS_SOME_MONO :
   !m n l.
     IS_SOME (LNTH n l) /\ m <= n
   ==>
     IS_SOME (LNTH m l)
Proof
    rw [IS_SOME_EXISTS]
 >> MATCH_MP_TAC lnth_some_down_closed
 >> qexistsl_tac [‘x’, ‘n’] >> rw []
QED

(* ------------------------------------------------------------------------ *)
(* Turning a stream-like linear order into a lazy list                      *)
(* ------------------------------------------------------------------------ *)

open pred_setTheory set_relationTheory arithmeticTheory

val linear_order_to_list_f_def = Define `
  linear_order_to_list_f lo =
    let min = minimal_elements (domain lo UNION range lo) lo in
      if min = {} then
        NONE
      else
        SOME (rrestrict lo ((domain lo UNION range lo) DIFF min), CHOICE min)`;

val SUC_EX = Q.prove (`(?x. P (SUC x)) ==> $? P`,
  REWRITE_TAC [EXISTS_DEF] THEN BETA_TAC THEN MATCH_ACCEPT_TAC SELECT_AX) ;

val PRED_SET_ss = pred_setSimps.PRED_SET_ss ;
val set_ss = std_ss ++ pred_setSimps.PRED_SET_ss ;

val MIN_LO_IN = Q.prove (
  `(minimal_elements X lo = {y}) ==> x IN X ==> linear_order lo X ==>
     (y, x) IN lo`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC IN_MIN_LO THEN
  POP_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]) ;

val fploum = REWRITE_RULE [SUBSET_REFL, GSYM AND_IMP_INTRO]
(Q.SPECL [`r`, `s`, `s`] finite_prefix_linear_order_has_unique_minimal) ;

val idlem = Q.prove (`X INTER (X DIFF Y) = X DIFF Y`,
  SIMP_TAC set_ss [INTER_SUBSET_EQN]) ;

fun vstac th = VALIDATE (CONV_TAC (DEPTH_CONV (REWR_CONV_A
  (UNDISCH_ALL (SPEC_ALL th))))) ;

val CARD_SUC_DELETE = Q.prove (
  `x IN s ==> FINITE s ==> (CARD s = SUC (CARD (s DELETE x)))`,
  REPEAT DISCH_TAC THEN IMP_RES_TAC INSERT_DELETE THEN
  POP_ASSUM (fn th => REWRITE_TAC [Once (SYM th)]) THEN
  ASM_SIMP_TAC set_ss []) ;

val pssp = Q.prove (`0 < m ==> (PRE (SUC m) = SUC (PRE m))`,
  SIMP_TAC arith_ss [SUC_PRE]) ;

val csd_gt0 = Q.prove (
  `FINITE s ==> x IN s ==> ~ (y = x) ==> 0 < CARD (s DELETE y)`,
  REPEAT DISCH_TAC THEN
  Q.SUBGOAL_THEN `x IN s DELETE y`
    (ASSUME_TAC o MATCH_MP CARD_SUC_DELETE) THEN1
  ASM_SIMP_TAC set_ss [] THEN
  VALIDATE (POP_ASSUM (ASSUME_TAC o UNDISCH)) THEN1
  ASM_REWRITE_TAC [FINITE_DELETE] THEN
  ASM_REWRITE_TAC [prim_recTheory.LESS_0] ) ;

val set_o_CONS = Q.prove (`set o CONS h = $INSERT h o set`,
  REWRITE_TAC [FUN_EQ_THM, combinTheory.o_THM, listTheory.LIST_TO_SET]) ;

val lo_single_min_prefix = Q.prove (
  `linear_order lo X ==> (minimal_elements X lo = {x}) ==>
  ({y | (y,x) IN lo} = {x})`,
  Ho_Rewrite.REWRITE_TAC [minimal_elements_def,
      EXTENSION, IN_GSPEC_IFF, IN_SING] THEN
  REPEAT STRIP_TAC THEN EQ_TAC
  THENL [
    POP_ASSUM (ASSUME_TAC o Q.SPEC `x`) THEN
      RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE []) THEN
      POP_ASSUM (ASSUME_TAC o Q.SPEC `x'`) THEN
      DISCH_TAC THEN IMP_RES_TAC linear_order_in_set THEN
      RES_TAC THEN ASM_REWRITE_TAC [],
    DISCH_TAC THEN VAR_EQ_TAC THEN
      POP_ASSUM (ASSUME_TAC o Q.SPEC `x`) THEN
      RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [linear_order_def]) THEN
      FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL [`x`, `x`]) THEN RES_TAC]) ;

(* we don't actually use the second clause of the conclusion of this,
  but it didn't take much extra effort to prove *)
val linear_order_to_list_lem1a = Q.prove (
`!s. FINITE s ==>
  !lo X x.
    x IN X /\
    ({ y | (y,x) IN lo } = s) /\
    linear_order lo X /\
    finite_prefixes lo X
    ==>
    (LNTH (PRE (CARD s)) (LUNFOLD linear_order_to_list_f lo) = SOME x) /\
    (OPTION_MAP set (LTAKE (CARD s) (LUNFOLD linear_order_to_list_f lo)) =
      SOME s)`,
  HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION THEN
  REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
  RULE_L_ASSUM_TAC CONJUNCTS THEN
  `SING (minimal_elements X lo)`
    by EVERY [IMP_RES_THEN (IMP_RES_THEN irule) fploum,
              Q.EXISTS_TAC `x`,
              FIRST_ASSUM ACCEPT_TAC ] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SING_DEF]) THEN POP_ASSUM CHOOSE_TAC THEN
  IMP_RES_TAC linear_order_dom_rg THEN Cases_on `x' = x` THEN1
    (* where x is minimum of X *)
    (IMP_RES_TAC lo_single_min_prefix THEN
    REPEAT VAR_EQ_TAC THEN
    ASM_SIMP_TAC (arith_ss ++ PRED_SET_ss) [LNTH_LUNFOLD] THEN
    SIMP_TAC (bool_ss ++ PRED_SET_ss)
      [arithmeticTheory.ONE, LTAKE_LUNFOLD] THEN
    ASM_SIMP_TAC (list_ss ++ PRED_SET_ss) [LET_DEF,
      pair_CASE_def, linear_order_to_list_f_def, option_CLAUSES]) THEN
  (* where x is not minimum of X *)
  Ho_Rewrite.ASM_REWRITE_TAC [BETA_THM, LNTH_LUNFOLD, NOT_INSERT_EMPTY,
     OPTION_MAP_DEF, SND, option_case_def, pair_CASE_def, FST,
      linear_order_to_list_f_def, LET_DEF] THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `s DELETE x'`) THEN
  Q.SUBGOAL_THEN `x IN s` ASSUME_TAC THEN1
    (POP_ASSUM (K ALL_TAC) THEN
    IMP_RES_TAC linear_order_refl THEN
    REPEAT VAR_EQ_TAC THEN
    ASM_SIMP_TAC std_ss [IN_GSPEC_IFF]) THEN
  Q.SUBGOAL_THEN `x' IN s` ASSUME_TAC THEN1
    (REPEAT VAR_EQ_TAC THEN
    Ho_Rewrite.REWRITE_TAC [IN_GSPEC_IFF] THEN
    IMP_RES_TAC MIN_LO_IN) THEN
  VALIDATE (FIRST_X_ASSUM (ASSUME_TAC o UNDISCH)) THEN1
    (SIMP_TAC set_ss [PSUBSET_DEF, SUBSET_DEF, EXTENSION] THEN
    Q.EXISTS_TAC `x'` THEN ASM_REWRITE_TAC []) THEN
  POP_ASSUM (ASSUME_TAC o Q.SPECL [`rrestrict lo (X DELETE x')`,
    `X INTER (X DELETE x')`, `x`]) THEN
  VALIDATE (POP_ASSUM (ASSUME_TAC o UNDISCH)) THEN1
    (POP_ASSUM (K ALL_TAC) THEN REPEAT CONJ_TAC THENL [
      ASM_SIMP_TAC set_ss [],
      ASM_SIMP_TAC set_ss [rrestrict_def, EXTENSION] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      REPEAT VAR_EQ_TAC THEN
      FULL_SIMP_TAC set_ss [] THEN
      IMP_RES_TAC in_dom_rg THEN ASM_REWRITE_TAC [],
      irule linear_order_restrict >> simp[],
      IMP_RES_THEN irule finite_prefixes_subset_rs >> simp[] >>
      irule rrestrict_SUBSET ]) THEN
  Q.SUBGOAL_THEN `CARD s = SUC (CARD (s DELETE x'))` ASSUME_TAC THEN1
    (irule CARD_SUC_DELETE THEN ASM_REWRITE_TAC []) THEN
    IMP_RES_TAC csd_gt0 THEN IMP_RES_TAC pssp THEN ASM_REWRITE_TAC [] THEN
  Ho_Rewrite.REWRITE_TAC [LNTH_LUNFOLD, LTAKE_LUNFOLD,
    linear_order_to_list_f_def, LET_DEF, BETA_THM] THEN
  COND_CASES_TAC THEN1 REV_FULL_SIMP_TAC set_ss [] THEN
  Ho_Rewrite.ASM_REWRITE_TAC
    [option_CLAUSES, pair_CASE_def, BETA_THM, SND, FST,
    GSYM DELETE_DEF, OPTION_MAP_COMPOSE, set_o_CONS] THEN
  ASM_REWRITE_TAC [GSYM OPTION_MAP_COMPOSE, SOME_11,
    OPTION_MAP_DEF, CHOICE_SING, INSERT_DELETE] THEN
  irule INSERT_DELETE THEN ASM_REWRITE_TAC []) ;

val linear_order_to_list_lem2a = Q.prove (
`!i lo X x.
  linear_order lo X /\
  (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x)
  ==>
  x IN X /\ !j. j < i ==>
    ?y. (LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME y) /\
    (y, x) IN lo /\ ~ (y = x)`,
  Induct THEN
  Ho_Rewrite.REWRITE_TAC [LNTH_LUNFOLD,
    linear_order_to_list_f_def, LET_DEF, BETA_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC [OPTION_MAP_DEF, option_CLAUSES] THEN1
    (IMP_RES_TAC CHOICE_DEF THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC linear_order_dom_rg THEN
    FULL_SIMP_TAC std_ss [] THEN
    IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] minimal_elements_subset)) THEN
  Ho_Rewrite.REWRITE_TAC [ BETA_THM, pair_case_def] THEN STRIP_TAC THEN
  IMP_RES_THEN (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN
    ASSUME_TAC th) linear_order_dom_rg THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ONCE_REWRITE_RULE [CONJ_COMM]
    (GSYM AND_IMP_INTRO)]) THEN
  RES_TAC THEN IMP_RES_TAC linear_order_restrict THEN
  POP_ASSUM (ASSUME_TAC o Q.SPEC `X DIFF minimal_elements X lo`) THEN
  RES_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER]) THEN
  ASM_REWRITE_TAC [] THEN
  (* now the second conjunct of the conclusion *)
  Cases THEN Ho_Rewrite.ASM_REWRITE_TAC [LNTH_LUNFOLD,
      linear_order_to_list_f_def, LET_DEF, BETA_THM,
      option_CLAUSES, FST, SND, pair_CASE_def, LESS_MONO_EQ]
  THENL [
    (* j = 0, y is a minimal element *)
    SIMP_TAC arith_ss [] THEN
    IMP_RES_TAC CHOICE_DEF THEN
    RULE_L_ASSUM_TAC (CONJUNCTS o REWRITE_RULE [IN_DIFF]) THEN
    CONJ_TAC THEN1 IMP_RES_TAC IN_MIN_LO THEN
    DISCH_THEN (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN
    IMP_RES_TAC F_IMP,
    (* why doesn't DISCH_THEN IMP_RES_TAC ?? work *)
    DISCH_TAC THEN RES_TAC THEN Q.EXISTS_TAC `y''` THEN
    ASM_REWRITE_TAC [] THEN
    IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] rrestrict_SUBSET) ]) ;

Theorem linear_order_to_list_lem1d[local]:
  linear_order lo X ==> finite_prefixes lo X ==> x IN X ==>
  LNTH (PRE (CARD {y | (y,x) IN lo})) (LUNFOLD linear_order_to_list_f lo) =
  SOME x
Proof
  REPEAT DISCH_TAC THEN
  irule (cj 1 linear_order_to_list_lem1a) >> rpt conj_tac THENL [
    RULE_ASSUM_TAC (REWRITE_RULE [finite_prefixes_def]) THEN RES_TAC,
    REFL_TAC,
    Q.EXISTS_TAC `X` THEN ASM_REWRITE_TAC []
  ]
QED

val linear_order_to_llist_eq = Q.store_thm ("linear_order_to_llist_eq",
  `!lo X.
  linear_order lo X /\
  finite_prefixes lo X
  ==>
  ?ll.
    (X = { x | ?i. LNTH i ll = SOME x }) /\
    (lo = { (x,y) | ?i j. i <= j /\ (LNTH i ll = SOME x) /\
                              (LNTH j ll = SOME y) }) /\
    (!i j x. (LNTH i ll = SOME x) /\ (LNTH j ll = SOME x) ==> (i = j))`,
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `LUNFOLD linear_order_to_list_f lo` THEN
  Ho_Rewrite.REWRITE_TAC [EXTENSION, IN_GSPEC_IFF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC)
  THENL [
    IMP_RES_TAC linear_order_to_list_lem1d THEN
    Q.EXISTS_TAC `PRE (CARD {y | (y,x) IN lo})` THEN
    ASM_REWRITE_TAC [],
    IMP_RES_TAC linear_order_to_list_lem2a,
    Cases_on `x` THEN Ho_Rewrite.REWRITE_TAC [PAIR_IN_GSPEC_IFF] THEN
    Q.EXISTS_TAC `PRE (CARD {y | (y,q) IN lo})` THEN
    Q.EXISTS_TAC `PRE (CARD {y | (y,r) IN lo})` THEN
    IMP_RES_TAC in_dom_rg THEN IMP_RES_TAC linear_order_dom_rg THEN
    IMP_RES_TAC linear_order_to_list_lem1d THEN
    Q.SUBGOAL_THEN `q IN X /\ r IN X`
      (EVERY o map ASSUME_TAC o CONJUNCTS) THEN1
    (VAR_EQ_TAC THEN ASM_REWRITE_TAC [IN_UNION]) THEN
    RES_TAC THEN ASM_REWRITE_TAC [] THEN
    irule PRE_LESS_EQ THEN irule CARD_SUBSET >> conj_tac THEN1
    (RULE_ASSUM_TAC (REWRITE_RULE [finite_prefixes_def]) THEN RES_TAC) THEN
    Ho_Rewrite.REWRITE_TAC [SUBSET_DEF, IN_GSPEC_IFF] THEN
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [linear_order_def, transitive_def]) THEN
    RES_TAC,
    Cases_on `x` THEN
    RULE_ASSUM_TAC (Ho_Rewrite.REWRITE_RULE [PAIR_IN_GSPEC_IFF]) THEN
    REPEAT (POP_ASSUM CHOOSE_TAC) THEN
    RULE_L_ASSUM_TAC CONJUNCTS THEN
    IMP_RES_TAC linear_order_to_list_lem2a THEN
    RULE_ASSUM_TAC (REWRITE_RULE [LESS_OR_EQ]) THEN
    REVERSE (FIRST_X_ASSUM DISJ_CASES_TAC) THEN1
    (FULL_SIMP_TAC bool_ss [SOME_11] THEN IMP_RES_TAC linear_order_refl) THEN
    RES_TAC THEN REV_FULL_SIMP_TAC bool_ss [SOME_11],
    DISJ_CASES_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) THEN1
    FIRST_ASSUM ACCEPT_TAC THEN
    POP_ASSUM DISJ_CASES_TAC THEN
    IMP_RES_TAC linear_order_to_list_lem2a THEN
    REV_FULL_SIMP_TAC bool_ss [SOME_11]]) ;

val linear_order_to_llist = Q.store_thm ("linear_order_to_llist",
`!lo X.
  linear_order lo X /\
  finite_prefixes lo X
  ==>
  ?ll.
    (X = { x | ?i. LNTH i ll = SOME x }) /\
    lo SUBSET { (x,y) | ?i j. i <= j /\ (LNTH i ll = SOME x) /\
                              (LNTH j ll = SOME y) } /\
    (!i j x. (LNTH i ll = SOME x) /\ (LNTH j ll = SOME x) ==> (i = j))`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC linear_order_to_llist_eq THEN
  Q.EXISTS_TAC `ll'` THEN ASM_REWRITE_TAC [SUBSET_REFL]) ;

val LPREFIX_def = Define `
  LPREFIX l1 l2 =
    case toList l1 of
    | NONE => (l1 = l2)
    | SOME xs =>
        case toList l2 of
        | NONE => LTAKE (LENGTH xs) l2 = SOME xs
        | SOME ys => isPREFIX xs ys`

val LPREFIX_LNIL = Q.store_thm("LPREFIX_LNIL[simp]",
  `LPREFIX [||] ll /\
   (LPREFIX ll [||] <=> (ll = [||]))`,
  rw[LPREFIX_def,toList_THM] >>
  BasicProvers.CASE_TAC >>
  simp[rich_listTheory.IS_PREFIX_NIL] >>
  rw[EQ_IMP_THM] >> fs[toList_THM] >>
  (* "Cases_on `ll`" *)
  Q.ISPEC_THEN`ll`FULL_STRUCT_CASES_TAC llist_CASES >>
  fs[toList_THM]);

val LPREFIX_LCONS = Q.store_thm("LPREFIX_LCONS",
  `(!ll h t.
     LPREFIX ll (h:::t) <=>
      ((ll = [||]) \/ ?l. (ll = h:::l) /\ LPREFIX l t)) /\
   (!h t ll.
     LPREFIX (h:::t) ll <=>
      ?l. (ll = h:::l) /\ LPREFIX t l)`,
  rw[] >>
  Q.ISPEC_THEN`ll`FULL_STRUCT_CASES_TAC llist_CASES >>
  simp[LPREFIX_def,toList_THM] >>
  every_case_tac >> fs[] >> rw[EQ_IMP_THM]);

val LPREFIX_LUNFOLD = Q.store_thm("LPREFIX_LUNFOLD",
  `LPREFIX ll (LUNFOLD f n) <=>
   case f n of NONE => (ll = LNIL)
   | SOME (n,x) => !h t. (ll = h:::t) ==> (h = x) /\ LPREFIX t (LUNFOLD f n)`,
  BasicProvers.CASE_TAC >- (
    simp[LUNFOLD_THM,LPREFIX_LNIL] ) >>
  BasicProvers.CASE_TAC >>
  imp_res_tac LUNFOLD_THM >>
  simp[LPREFIX_LCONS] >>
  (* "Cases_on `ll`" *)
  Q.ISPEC_THEN`ll`FULL_STRUCT_CASES_TAC llist_CASES >>
  simp[]);

val LPREFIX_REFL = Q.store_thm("LPREFIX_REFL[simp]",
  `LPREFIX ll ll`,
  rw[LPREFIX_def] >> BasicProvers.CASE_TAC >> simp[]);

Theorem LPREFIX_ANTISYM:
  LPREFIX l1 l2 /\ LPREFIX l2 l1 ==> l1 = l2
Proof
  rw[LPREFIX_def] >>
  every_case_tac >> fs[] >>
  imp_res_tac rich_listTheory.IS_PREFIX_ANTISYM >> rw[] >>
  metis_tac[to_fromList,THE_DEF,toList,NOT_SOME_NONE]
QED

val LPREFIX_TRANS = Q.store_thm("LPREFIX_TRANS",
  `LPREFIX l1 l2 /\ LPREFIX l2 l3 ==> LPREFIX l1 l3`,
  rw[LPREFIX_def] >>
  every_case_tac >> fs[] >>
  TRY(imp_res_tac rich_listTheory.IS_PREFIX_TRANS >> NO_TAC) >>
  imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
  imp_res_tac LTAKE_TAKE_LESS >> simp[] >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  simp[listTheory.TAKE_APPEND1]);

val LPREFIX_fromList = Q.store_thm ("LPREFIX_fromList",
  `!l ll.
    LPREFIX (fromList l) ll <=>
      case toList ll of
      | NONE => LTAKE (LENGTH l) ll = SOME l
      | SOME ys => isPREFIX l ys`,
  rw [LPREFIX_def, from_toList]);

val prefixes_lprefix_total = Q.store_thm("prefixes_lprefix_total",
  `!ll. !l1 l2. LPREFIX l1 ll /\ LPREFIX l2 ll ==>
    LPREFIX l1 l2 \/ LPREFIX l2 l1`,
  rw[LPREFIX_def] >> reverse every_case_tac >> fs[]
  >- metis_tac[rich_listTheory.prefixes_is_prefix_total] >>
  rpt(pop_assum mp_tac) >>
  qho_match_abbrev_tac`P l1 l2 x x'` >>
  `P l1 l2 x x' <=> P l2 l1 x' x` by (
    simp[Abbr`P`] >> metis_tac[] ) >>
  `!ll1 ll2 l1 l2. LENGTH l1 <= LENGTH l2 ==> P ll1 ll2 l1 l2` suffices_by (
    rw[] >> metis_tac[arithmeticTheory.LESS_EQ_CASES] ) >>
  pop_assum kall_tac >> unabbrev_all_tac >> rw[] >>
  `l1 = (TAKE (LENGTH l1) l2)` by (
    metis_tac[LTAKE_TAKE_LESS,optionTheory.SOME_11] ) >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >>
  metis_tac[listTheory.TAKE_DROP])

Theorem LPREFIX_LAPPEND1[local]:
  LPREFIX ll (LAPPEND ll l2)
Proof
  rw[LPREFIX_def] >> every_case_tac >>
  metis_tac[LFINITE_toList,NOT_LFINITE_APPEND,NOT_SOME_NONE,
            IS_SOME_EXISTS,to_fromList,THE_DEF,LTAKE_LAPPEND1,
            LTAKE_fromList,toList_LAPPEND_APPEND,
            rich_listTheory.IS_PREFIX_APPEND]
QED

val LTAKE_IMP_LDROP = Q.store_thm("LTAKE_IMP_LDROP",
  `!n ll l1.
    (LTAKE n ll = SOME l1) ==>
     ?l2. (LDROP n ll = SOME l2) /\
          (LAPPEND (fromList l1) l2 = ll)`,
  Induct >> simp[] >>
  gen_tac >> qspec_then`ll`FULL_STRUCT_CASES_TAC llist_CASES >> rw[] >>
  first_x_assum(fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
  rw[])

val LDROP_EQ_LNIL' = Q.prove (
  `!n ll. (LDROP n ll = SOME LNIL) <=> (LLENGTH ll = SOME n)`,
  Induct THEN
  FULL_SIMP_TAC std_ss [LDROP_FUNPOW, FUNPOW, LLENGTH_0] THEN GEN_TAC THEN
  llist_CASE_TAC ``ll : 'a llist`` THEN
  ASM_SIMP_TAC std_ss [LTL_THM, LLENGTH_THM, FUNPOW_BIND_NONE,
    arithmeticTheory.SUC_NOT]) ;

val LDROP_EQ_LNIL = save_thm("LDROP_EQ_LNIL", SPEC_ALL LDROP_EQ_LNIL') ;

val LPREFIX_APPEND = Q.store_thm("LPREFIX_APPEND",
  `LPREFIX l1 l2 <=> ?ll. l2 = LAPPEND l1 ll`,
  reverse EQ_TAC >- metis_tac[LPREFIX_LAPPEND1] >>
  simp[LPREFIX_def] >>
  Cases_on`toList l1`>>fs[]
  >- metis_tac[LAPPEND_NIL_2ND] >>
  `LFINITE l1` by fs[toList] >>
  imp_res_tac LFINITE_HAS_LENGTH >>
  `LTAKE n l1 = SOME x` by fs[toList] >>
  imp_res_tac LTAKE_LENGTH >> rw[] >>
  qexists_tac`THE(LDROP (LENGTH x) l2)` >>
  rw[LNTH_EQ] >>
  simp[LNTH_LAPPEND] >>
  rw[] >>
  every_case_tac >> fs[toList] >>
  imp_res_tac LTAKE_LNTH_EL >> simp[] >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >> rw[] >>
  imp_res_tac LTAKE_LENGTH >> fs[] >>
  TRY (
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[rich_listTheory.EL_APPEND1] >> NO_TAC) >>
  TRY (
    imp_res_tac LTAKE_IMP_LDROP >> rw[] >>
    simp[LNTH_LAPPEND] >>
    NO_TAC) >>
  `LTAKE (LENGTH x) l2 = SOME x` by (
    imp_res_tac LTAKE_TAKE_LESS >>
    rpt(first_x_assum(qspec_then`LENGTH x`mp_tac)) >>
    simp[rich_listTheory.TAKE_APPEND1] ) >>
  pop_assum(strip_assume_tac o MATCH_MP LTAKE_IMP_LDROP) >>
  rw[LNTH_LAPPEND]);

val LFINITE_LDROP_APPEND1 = Q.prove(
  `!l. LFINITE l ==>
      !n z. (LDROP n l = SOME z) ==>
              !l2. LDROP n (LAPPEND l l2) = SOME (LAPPEND z l2)`,
  ho_match_mp_tac LFINITE_INDUCTION >> simp[] >>
  conj_tac >- ( Cases >> simp[] ) >>
  ntac 3 strip_tac >> Cases >> simp[] )

val NOT_LFINITE_DROP_LFINITE = Q.store_thm("NOT_LFINITE_DROP_LFINITE",
  `!n l t. ~LFINITE l /\ (LDROP n l = SOME t) ==> ~LFINITE t`,
  Induct >> simp[] >> gen_tac >>
  qspec_then`l`FULL_STRUCT_CASES_TAC llist_CASES >>
  simp[] >> metis_tac[])

val LDROP_APPEND1 = Q.store_thm("LDROP_APPEND1",
  `(LDROP n l1 = SOME l) ==>
   (LDROP n (LAPPEND l1 l2) = SOME (LAPPEND l l2))`,
  rw[] >>
  Cases_on`LFINITE l1` >- (
    metis_tac[LFINITE_LDROP_APPEND1] ) >>
  imp_res_tac NOT_LFINITE_DROP_LFINITE >>
  simp[NOT_LFINITE_APPEND])

val LDROP_fromList = Q.store_thm("LDROP_fromList",
  `!ls n.
    LDROP n (fromList ls) =
    if n <= LENGTH ls then SOME (fromList (DROP n ls)) else NONE`,
  Induct >- ( Cases >> simp[] ) >>
  gen_tac >> Cases >> simp[])

val LDROP_SUC = Q.store_thm("LDROP_SUC",
  `LDROP (SUC n) ls = OPTION_BIND (LDROP n ls) LTL`,
  SIMP_TAC std_ss [LDROP_FUNPOW, arithmeticTheory.FUNPOW_SUC]) ;

Theorem LDROP_1[simp]:
  LDROP (1: num) (h:::t) = SOME t
Proof `LDROP (SUC 0) (h:::t) = SOME t` by fs[LDROP] >>
      metis_tac[arithmeticTheory.ONE]
QED

Theorem LDROP_NONE_LFINITE:
  (LDROP k l = NONE) ==> LFINITE l
Proof
  metis_tac[NOT_LFINITE_DROP,NOT_SOME_NONE]
QED

Theorem LDROP_LDROP:
  !ll k1 k2. ~ LFINITE ll ==>
             (THE (LDROP k2 (THE (LDROP k1 ll))) =
              THE (LDROP k1 (THE (LDROP k2 ll))))
Proof
  rw[] >>
  `LDROP (k1+k2) ll = LDROP (k2 + k1) ll` by fs[] >>
  fs[LDROP_ADD] >>
  NTAC 2 (full_case_tac >- imp_res_tac LDROP_NONE_LFINITE) >> fs[]
QED

(* ----------------------------------------------------------------------
    LGENLIST : (num -> 'a) -> num option -> 'a llist
   ---------------------------------------------------------------------- *)

val LGENLIST_def = zDefine`
  (LGENLIST f NONE = LUNFOLD (\n. SOME (n + 1, f n)) 0) /\
  (LGENLIST f (SOME lim) = LUNFOLD (\n. if n < lim then SOME (n + 1, f n)
                                        else NONE) 0)
`;

val LHD_LGENLIST = Q.store_thm(
  "LHD_LGENLIST[simp,compute]",
  `LHD (LGENLIST f limopt) =
    if limopt = SOME 0 then NONE else SOME (f 0)`,
  Cases_on `limopt` >> simp[LGENLIST_def] >> rw[] >> simp[EXISTS_PROD]);

val LTL_LGENLIST = Q.store_thm(
  "LTL_LGENLIST[simp,compute]",
  `LTL (LGENLIST f limopt) =
    if limopt = SOME 0 then NONE
    else SOME (LGENLIST (f o SUC) (OPTION_MAP PRE limopt))`,
  Cases_on `limopt` >> simp[LGENLIST_def]
  >- (`!m. LUNFOLD (\n. SOME (n + 1, f n)) (m + 1) =
           LUNFOLD (\n. SOME (n + 1, f (SUC n))) m`
        suffices_by metis_tac[DECIDE ``0 + 1 = 1``] >>
      simp[LNTH_EQ] >> Induct_on `n` >> simp[LNTH_LUNFOLD] >>
      simp[arithmeticTheory.ADD1]) >>
  reverse (rw[]) >- fs[] >>
  `!m l. 0 < l ==>
         (LUNFOLD (\n. if n < PRE l then SOME (n + 1, f (SUC n)) else NONE) m =
          LUNFOLD (\n. if n < l then SOME (n + 1, f n) else NONE) (m + 1))`
     suffices_by metis_tac[DECIDE ``0 + 1 = 1``] >>
  dsimp[LNTH_EQ] >> Induct_on `n` >>
  simp[LNTH_LUNFOLD, DECIDE ``0 < x ==> (y < PRE x <=> y + 1 < x)``,
       arithmeticTheory.ADD1] >> rw[]);

(* maybe useful? *)
val numopt_BISIMULATION = Q.store_thm(
  "numopt_BISIMULATION",
  `!mopt nopt.
     (mopt = nopt) <=>
     ?R. R mopt nopt /\
         !m n. R m n ==>
               (m = SOME 0) /\ (n = SOME 0) \/
               m <> SOME 0 /\ n <> SOME 0 /\
               R (OPTION_MAP PRE m) (OPTION_MAP PRE n)`,
  simp[EQ_IMP_THM, FORALL_AND_THM] >> conj_tac
  >- (gen_tac >> qexists_tac `(=)` >> simp[]) >>
  rpt strip_tac >>
  Cases_on `mopt`
  >- (Cases_on `nopt` >> simp[] >> rename1 `R NONE (SOME n)` >>
      Induct_on `n` >> strip_tac >> res_tac >> fs[]) >>
  Cases_on `nopt` >> simp[]
  >- (rename1 `R (SOME m) NONE` >> Induct_on `m` >> strip_tac >>
      res_tac >> fs[]) >>
  rename1 `R (SOME m) (SOME n)` >>
  `!m n. R (SOME m) (SOME n) ==> (m = n)` suffices_by metis_tac[] >>
  Induct >> rpt strip_tac >- (res_tac >> fs[]) >>
  rename1 `R (SOME (SUC m0)) (SOME n0)` >>
  `n0 <> 0 /\ R (SOME m0) (SOME (PRE n0))` by (res_tac >> fs[]) >>
  `m0 = PRE n0` by res_tac >> simp[])

val LGENLIST_EQ_LNIL = Q.store_thm(
  "LGENLIST_EQ_LNIL[simp]",
  `((LGENLIST f n = LNIL) <=> (n = SOME 0)) /\
   ((LNIL = LGENLIST f n) <=> (n = SOME 0))`,
  Cases_on `n` >> simp[LGENLIST_def] >> rpt conj_tac >>
  simp[Once LUNFOLD] >> rename [`0 < limit`] >> Cases_on `limit` >> simp[]);

val LFINITE_LGENLIST = Q.store_thm(
  "LFINITE_LGENLIST[simp]",
  `LFINITE (LGENLIST f n) <=> n <> NONE`,
  Cases_on `n` >> simp[]
  >- (`!l. LFINITE l ==> !f. l <> LGENLIST f NONE` suffices_by metis_tac[] >>
      simp[LGENLIST_def] >>
      `!l. LFINITE l ==> !f n. l <> LUNFOLD (\n. SOME (n + 1, f n)) n`
         suffices_by metis_tac[] >>
      ho_match_mp_tac LFINITE_STRONG_INDUCTION >> conj_tac
      >- simp[Once LUNFOLD] >>
      rpt gen_tac >> strip_tac >> simp[Once LUNFOLD]) >>
  rename [`LFINITE (LGENLIST f (SOME n))`] >> simp[LGENLIST_def] >>
  `!m. m <= n ==>
       LFINITE (LUNFOLD (\x. if x < n then SOME (x + 1, f x) else NONE) m)`
    suffices_by metis_tac[DECIDE ``0 <= x``] >>
  Induct_on `n - m` >> simp[Once LUNFOLD])

val LTL_HD_LTL_LHD = Q.store_thm(
  "LTL_HD_LTL_LHD",
  `LTL_HD l = OPTION_BIND (LHD l) (\h. OPTION_BIND (LTL l) (λt. SOME (t, h)))`,
  simp[LTL_HD_HD, LTL_HD_TL] >>
  Cases_on `LTL_HD l` >> simp[]);

Theorem LGENLIST_SOME[simp]:
  (LGENLIST f (SOME 0) = [||]) /\
  (!n. LGENLIST f (SOME (SUC n)) = f 0 ::: LGENLIST (f o SUC) (SOME n))
Proof
  rpt strip_tac >> irule (iffLR LTL_HD_11) >>
  simp[LTL_HD_LTL_LHD, Excl "LTL_HD_11"]
QED

val LGENLIST_SOME_compute = save_thm(
  "LGENLIST_SOME_compute[compute]",
  CONJ (CONJUNCT1 LGENLIST_SOME)
       (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV (CONJUNCT2 LGENLIST_SOME)))

val LNTH_LGENLIST = Q.store_thm(
  "LNTH_LGENLIST",
  `!n f lim.
     LNTH n (LGENLIST f lim) =
       case lim of NONE => SOME (f n)
                 | SOME lim0 => if n < lim0 then SOME (f n) else NONE`,
  Induct_on `n` >> simp[LNTH] >> rpt gen_tac
  >- (Cases_on `lim` >> simp[] >> rename [`0 < n`] >> Cases_on `n` >> simp[]) >>
  Cases_on `lim` >> simp[] >>
  rename [`SUC n < lim`] >> Cases_on `lim` >> simp[]);

val LNTH_LMAP = Q.store_thm(
  "LNTH_LMAP[simp]",
  `!n f l. LNTH n (LMAP f l) = OPTION_MAP f (LNTH n l)`,
  Induct >> simp[LNTH] >> rpt gen_tac >>
  Q.SPEC_THEN `l` STRUCT_CASES_TAC llist_CASES >> simp[])

val LLENGTH_LGENLIST = Q.store_thm(
  "LLENGTH_LGENLIST[simp,compute]",
  `!f. LLENGTH (LGENLIST f limopt) = limopt`,
  Cases_on `limopt`
  >- metis_tac[NOT_LFINITE_NO_LENGTH, LFINITE_LGENLIST] >>
  rename [`LGENLIST _ (SOME n)`] >> Induct_on `n` >> simp[]);

val LMAP_LGENLIST = Q.store_thm(
  "LMAP_LGENLIST[simp]",
  `LMAP f (LGENLIST g limopt) = LGENLIST (f o g) limopt`,
  simp[LNTH_EQ, LNTH_LGENLIST] >>
  Cases_on `limopt` >> simp[] >> rw[]);

val LGENLIST_EQ_CONS = Q.store_thm(
  "LGENLIST_EQ_CONS",
  `(LGENLIST f NONE = h:::t) <=>
     (h = f 0) /\ (t = LGENLIST (f o (+) 1) NONE)`,
  simp[LGENLIST_def] >> simp[SimpLHS, Once LUNFOLD] >>
  `!m. LUNFOLD (\n. SOME (n + 1, f n)) m =
       LUNFOLD (\n. SOME (n + 1, f(n + m))) 0` suffices_by metis_tac[] >>
  gen_tac >> simp[Once LLIST_STRONG_BISIMULATION] >>
  qexists_tac `\l1 l2. ?k m.
    (l1 = LUNFOLD (\n. SOME (n + 1, f n)) (m + k)) /\
    (l2 = LUNFOLD (\n. SOME (n + 1, f (n + m))) k)` >> simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_CLAUSES] >>
  dsimp[] >> rpt gen_tac >> disj2_tac >>
  qspec_then `LUNFOLD (\n. SOME (n + 1, f n)) (k + m)` strip_assume_tac
    llist_CASES >> simp[]
  >- fs[Once LUNFOLD] >>
  pop_assum mp_tac >>
  simp[SimpL ``$==>``, Once LUNFOLD] >> rw[] >>
  map_every qexists_tac [`k+1`, `m`] >> simp[] >>
  simp[Once LUNFOLD, SimpLHS]);

(* ----------------------------------------------------------------------
    LREPEAT : 'a list -> 'a llist

    Infinite repetitions of the argument.  If it's [], then the result is
    [||]
   ---------------------------------------------------------------------- *)

Definition LREPEAT_def[nocompute]:
  LREPEAT l = if NULL l then [||]
              else LGENLIST (\n. EL (n MOD LENGTH l) l) NONE
End

val LGENLIST_CHUNK_GENLIST = Q.store_thm(
  "LGENLIST_CHUNK_GENLIST",
  `LGENLIST f NONE =
     LAPPEND (fromList (GENLIST f n)) (LGENLIST (f o (+) n) NONE)`,
  simp[Once LLIST_STRONG_BISIMULATION] >>
  qexists_tac `\l1 l2. ?m n.
    (l1 = LGENLIST (f o (+) m) NONE) /\
    (l2 = LAPPEND (fromList (GENLIST (f o (+) m) n))
                  (LGENLIST (f o $+ (m + n)) NONE))` >>
  simp[] >> conj_tac
  >- (map_every qexists_tac [`0`, `n`] >>
      `$+ 0 = I` by simp[FUN_EQ_THM] >> simp[]) >>
  dsimp[] >> qx_genl_tac [`m`, `n`] >>
  disj2_tac >>
  Q.SPEC_THEN `LGENLIST (f o $+ m) NONE` strip_assume_tac llist_CASES >>
  fs[LGENLIST_EQ_CONS] >> rw[] >>
  map_every qexists_tac [`m + 1`] >> simp[combinTheory.o_DEF] >>
  Cases_on `n` >> simp[]
  >- (simp[LGENLIST_EQ_CONS] >> qexists_tac `0` >> simp[combinTheory.o_DEF]) >>
  rename [`SUC k`] >> qexists_tac `k` >> simp[listTheory.GENLIST_CONS] >>
  simp[combinTheory.o_DEF, arithmeticTheory.ADD1]);

val LREPEAT_thm = Q.store_thm(
  "LREPEAT_thm",
  `LREPEAT l = LAPPEND (fromList l) (LREPEAT l)`,
  rw[LREPEAT_def] >- (Cases_on `l` >> fs[]) >>
  `0 < LENGTH l /\ l <> []` by (Cases_on `l` >> fs[]) >>
  qmatch_abbrev_tac `LGENLIST f NONE = LAPPEND (fromList l) _` >>
  `(l = GENLIST f (LENGTH l)) /\ (f = f o (+) (LENGTH l))`
     suffices_by metis_tac[LGENLIST_CHUNK_GENLIST] >>
  simp[Abbr`f`, combinTheory.o_DEF] >>
  simp[listTheory.LIST_EQ_REWRITE])

val LREPEAT_NIL = Q.store_thm(
  "LREPEAT_NIL[simp,compute]",
  `LREPEAT [] = LNIL`,
  simp[LREPEAT_def]);

val LREPEAT_EQ_LNIL = Q.store_thm(
  "LREPEAT_EQ_LNIL[simp]",
  `((LREPEAT l = LNIL) <=> (l = [])) /\
   ((LNIL = LREPEAT l) <=> (l = []))`,
  Cases_on `l` >> simp[] >> conj_tac >> simp[Once LREPEAT_thm])

val LHD_LREPEAT = Q.store_thm(
  "LHD_LREPEAT[simp,compute]",
  `LHD (LREPEAT l) = LHD (fromList l)`,
  Cases_on `l = []` >> simp[] >> simp[Once LREPEAT_thm, LHD_LAPPEND]);

val LTL_LREPEAT = Q.store_thm(
  "LTL_LREPEAT[simp,compute]",
  `LTL (LREPEAT l) = OPTION_MAP (\t. LAPPEND t (LREPEAT l)) (LTL (fromList l))`,
  Cases_on `l = []` >> simp[] >> simp[Once LREPEAT_thm, LTL_LAPPEND] >>
  Cases_on `l` >> fs[]);

val LLENGTH_LREPEAT = Q.store_thm(
  "LLENGTH_LREPEAT",
  `LLENGTH (LREPEAT l) = if NULL l then SOME 0 else NONE`,
  rw[LREPEAT_def])

(* --------------------------------------------------------------------------
   Case constant, distinctness etc. for TypeBase
   -------------------------------------------------------------------------- *)

Definition llist_CASE_def[nocompute]:
  llist_CASE ll b f =
    case LTL_HD ll of
      NONE => b
    | SOME(ltl,lhd) => f lhd ltl
End

Theorem llist_CASE_compute[simp,compute]:
  (llist_CASE [||] b f = b) /\
  (llist_CASE (x:::ll) b f = f x ll)
Proof
  rw[llist_CASE_def]
QED

Theorem LLIST_BISIMULATION_I =
 LLIST_BISIMULATION |> SPEC_ALL |> PURE_ONCE_REWRITE_RULE[EQ_IMP_THM]
                    |> CONJUNCT2 |> Q.GEN `ll1` |> Q.GEN `ll2`

Theorem LLIST_CASE_CONG:
  !M M' v f.
    M = M' /\ (M' = [||] ==> v = v') /\
    (!a0 a1. M' = a0:::a1 ==> f a0 a1 = f' a0 a1) ==>
    llist_CASE M v f = llist_CASE M' v' f'
Proof
  rpt GEN_TAC >>
  llist_CASE_TAC ``M':'a llist`` >>
  rw[]
QED

Theorem LLIST_CASE_EQ:
  llist_CASE (x:'a llist) v f = v' <=>
  x = [||] /\ v = v' \/ ?a l. x = a:::l /\ f a l = v'
Proof
  llist_CASE_TAC ``x:'a llist`` >> rw[]
QED

Theorem LLIST_CASE_ELIM:
  !f'. f'(llist_CASE (x:'a llist) v f) <=>
  x = [||] /\ f' v \/ ?a l. x = a:::l /\ f'(f a l)
Proof
  llist_CASE_TAC ``x:'a llist`` >> rw[FUN_EQ_THM]
QED

Theorem LLIST_DISTINCT:
  !a1 a0. [||] <> a0:::a1
Proof
  rw[]
QED

Definition LSET_def:
  LSET l x = ?n. LNTH n l = SOME x
End

Theorem LSET[simp]:
  LSET LNIL = {} /\
  LSET (x:::xs) = x INSERT LSET xs
Proof
  fs [EXTENSION] \\ fs [LSET_def,IN_DEF]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (Cases_on `n` \\ fs [] \\ metis_tac [])
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC n` \\ fs [])
QED

Definition llist_rel_def:
  llist_rel R l1 l2 <=>
    LLENGTH l1 = LLENGTH l2 /\
    !i x y. LNTH i l1 = SOME x /\ LNTH i l2 = SOME y ==> R x y
End

(* --------------------------------------------------------------------------
   Update TypeBase
   -------------------------------------------------------------------------- *)

Overload "case" = “llist_CASE”;
val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    {
     ax = TypeBasePure.ORIG llist_Axiom,
     induction = TypeBasePure.ORIG LLIST_BISIMULATION_I,
     case_def = llist_CASE_compute,
     case_cong = LLIST_CASE_CONG,
     case_eq = LLIST_CASE_EQ,
     case_elim = LLIST_CASE_ELIM,
     nchotomy = llist_CASES,
     size = NONE,
     encode = NONE,
     lift = NONE,
     one_one = SOME LCONS_11,
     distinct = SOME LLIST_DISTINCT,
     fields = [],
     accessors = [],
     updates = [],
     destructors = [],
     recognizers = []
    }
  ]

(* ----------------------------------------------------------------------
    Temporal logic style operators
   ---------------------------------------------------------------------- *)

val (eventually_rules,eventually_ind,eventually_cases) = Hol_reln‘
  (!ll. P ll ==> eventually P ll) /\
  (!h t. eventually P t ==> eventually P (h:::t))
’;

Theorem eventually_thm[simp]:
  (eventually P [||] = P [||]) /\
  (eventually P (h:::t) = (P (h:::t) \/ eventually P t))
Proof
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [eventually_cases])) THEN
  SRW_TAC [][Cong (REWRITE_RULE [GSYM AND_IMP_INTRO] OR_CONG)]
QED

val (always_rules,always_coind,always_cases) = Hol_coreln‘
  (!h t. (P (h ::: t) /\ always P t) ==> always P (h ::: t))
’;

Theorem always_thm[simp]:
  (always P [||] <=> F) /\
  !h t. always P (h:::t) <=> P (h:::t) /\ always P t
Proof conj_tac >> simp[Once always_cases]
QED

Theorem always_conj_l:
  !ll. always (\x. P x /\ Q x) ll ==> always P ll
Proof
  ho_match_mp_tac always_coind >> rw[] >> Cases_on`ll` >> fs[]
QED

Theorem always_eventually_ind:
  (!ll. (P ll \/ (~P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
  !ll. ll <> [||] ==> always(eventually P) ll ==> Q ll
Proof
  `(!ll. (P ll \/ (~P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
   (!ll. eventually P ll ==> (Q ll))`
     by (strip_tac >> ho_match_mp_tac eventually_ind >>
         fs[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
         Cases_on ‘P (h:::t)’ >> simp[]) >>
  rw[] >> Cases_on`ll` >> fs[] >> res_tac >> first_x_assum irule >> simp[]
QED

Theorem always_DROP:
  !ll. always P ll ==> always P (THE(LDROP k ll))
Proof
  Induct_on`k` >> Cases_on`ll` >> fs[always_thm,LDROP] >>
  rw[] >> imp_res_tac always_thm >> fs[]
QED

val (until_rules,until_ind,until_cases) = Hol_reln‘
  (!ll. Q ll ==> until P Q ll) /\
  (!h t. P (h:::t) /\ until P Q t ==> until P Q (h:::t))
’;

Theorem eventually_until_EQN: eventually P = until (K T) P
Proof
  simp[FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >> conj_tac
  >- (Induct_on ‘eventually’ >> rpt strip_tac
      >- (irule (CONJUNCT1 (SPEC_ALL until_rules)) >> simp[])
      >- (irule (CONJUNCT2 (SPEC_ALL until_rules)) >> simp[]))
  >- (Induct_on ‘until’ >> simp[eventually_rules])
QED

(* might be nice if this was also true, but behaviour of eventually at LNIL
   as written doesn't allow it; we would have to have
     eventually P [||] <=> T
*)
(*
Theorem eventually_NOT_always_EQN: eventually P = $~ o always ($~ o P)
Proof
  simp[FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >> conj_tac
  >- (Induct_on ‘eventually’ >> simp[] >> Cases >> simp[]) >>
  CONV_TAC (STRIP_QUANT_CONV CONTRAPOS_CONV) >> simp[] >>
  ho_match_mp_tac always_coind >> Cases >> simp[]
QED
*)

(* ----------------------------------------------------------------------
    Discriminating finite and infinite lists
   ---------------------------------------------------------------------- *)

Definition fromSeq_def:
  fromSeq f = LUNFOLD (\x. SOME (SUC x, f x)) 0
End

Theorem fromSeq_LCONS:
  fromSeq f = LCONS (f 0) (fromSeq (f o SUC))
Proof
  PURE_REWRITE_TAC[fromSeq_def,Once LUNFOLD] >>
  simp[] >>
  PURE_REWRITE_TAC[Once LUNFOLD_BISIMULATION] >>
  qexists_tac ‘\x y. x = SUC y’ >>
  rw[Once LUNFOLD]
QED

Theorem fromList_fromSeq:
  !ll. (?l. ll = fromList l) \/ (?f. ll = fromSeq f)
Proof
  strip_tac >>
  Cases_on ‘LFINITE ll’ >-
   (drule_then strip_assume_tac LFINITE_toList >>
    disj1_tac >>
    qexists_tac ‘THE(toList ll)’ >>
    drule_then MATCH_ACCEPT_TAC (GSYM to_fromList)) >>
  disj2_tac >>
  qexists_tac ‘\n. THE(LNTH n ll)’ >>
  PURE_REWRITE_TAC[Once LLIST_BISIMULATION] >>
  qexists_tac ‘\x y. ~LFINITE x /\ (?n. y = (fromSeq (\n. THE (LNTH n x))))’ >>
  rw[] >>
  last_x_assum kall_tac >>
  rename1 ‘ll = [||]’ >>
  disj2_tac >>
  simp[Once fromSeq_LCONS] >>
  Cases_on ‘ll’ >>
  FULL_SIMP_TAC std_ss [LFINITE_THM,LNTH_THM,LHD_THM,LTL_THM] >>
  simp[Once fromSeq_LCONS,combinTheory.o_DEF]
QED

Theorem llist_forall_split:
  !P. (!ll. P ll) <=> (!l. P (fromList l)) /\ (!f. P (fromSeq f))
Proof
  gen_tac \\ eq_tac \\ rpt strip_tac
  \\ asm_rewrite_tac []
  \\ qspec_then ‘ll’ mp_tac fromList_fromSeq
  \\ strip_tac \\ asm_rewrite_tac []
QED

Theorem LHD_fromSeq[simp]:
  !f. LHD (fromSeq f) = SOME (f 0)
Proof
  rw [Once fromSeq_LCONS]
QED

Theorem LTL_fromSeq[simp]:
  !f. LTL (fromSeq f) = SOME (fromSeq (f o SUC))
Proof
  rw [Once fromSeq_LCONS]
QED

Theorem LNTH_fromSeq[simp]:
  !n f. LNTH n (fromSeq f) = SOME (f n)
Proof
  Induct \\ rw [LNTH]
QED

Theorem LTAKE_fromSeq[simp]:
  !n f. LTAKE n (fromSeq f) = SOME (GENLIST f n)
Proof
  Induct \\ rw []
  \\ rw [Once fromSeq_LCONS, GSYM listTheory.GENLIST_CONS]
QED

Theorem LDROP_fromSeq[simp]:
  !n f. LDROP n (fromSeq f) = SOME (fromSeq (f o ((+) n)))
Proof
  Induct \\ rw []
  THEN1 (AP_TERM_TAC \\ rw [FUN_EQ_THM,ADD1])
  \\ rw [Once fromSeq_LCONS]
  \\ AP_TERM_TAC \\ rw [FUN_EQ_THM,ADD1]
QED

Theorem LFINITE_fromSeq[simp]:
  !f. ~LFINITE (fromSeq f)
Proof
  rw [LFINITE]
QED

Theorem LLENGTH_fromSeq[simp]:
  !f. LLENGTH (fromSeq f) = NONE
Proof
  rw [LLENGTH]
QED

Theorem LGENLIST_EQ_fromSeq:
  !f. LGENLIST f NONE = fromSeq f
Proof
  rewrite_tac [LGENLIST_def,fromSeq_def,ADD1]
QED

Theorem LGENLIST_EQ_fromList:
  !f k. LGENLIST f (SOME k) = fromList (GENLIST f k)
Proof
  Induct_on ‘k’ \\ fs [listTheory.GENLIST_CONS]
QED

Theorem LAPPEND_fromSeq[simp]:
  (!f ll. LAPPEND (fromSeq f) ll = fromSeq f) /\
  (!l f.  LAPPEND (fromList l) (fromSeq f) =
          fromSeq (\n. if n < LENGTH l then EL n l else f (n - LENGTH l)))
Proof
  conj_tac
  THEN1 (gen_tac \\ match_mp_tac NOT_LFINITE_APPEND \\ rw [])
  \\ Induct
  THEN1 (rw [LAPPEND] \\ AP_TERM_TAC \\ rw [FUN_EQ_THM])
  \\ rw [LAPPEND] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rw [Once fromSeq_LCONS]
  \\ AP_TERM_TAC \\ rw [FUN_EQ_THM]
QED

Theorem LMAP_fromSeq[simp]:
  !f g. LMAP f (fromSeq g) = fromSeq (f o g)
Proof
  rewrite_tac [GSYM LGENLIST_EQ_fromSeq,LMAP_LGENLIST]
QED

Theorem LMAP_fromList:
  LMAP f (fromList l) = fromList(MAP f l)
Proof
  Induct_on `l` >> fs[]
QED

Theorem MAP_toList :
    !ll f. LFINITE ll ==> MAP f (THE (toList ll)) = THE (toList (LMAP f ll))
Proof
    rpt STRIP_TAC
 >> ‘ll = fromList (THE (toList ll))’ by METIS_TAC [to_fromList]
 >> POP_ORW
 >> simp [LMAP_fromList, to_fromList, from_toList]
QED

Theorem exists_fromSeq[simp]:
  !p f. exists p (fromSeq f) = ?i. p (f i)
Proof
  rw [] \\ reverse eq_tac
  THEN1
   (fs [PULL_EXISTS]
    \\ qid_spec_tac ‘f’
    \\ Induct_on ‘i’ \\ rw []
    \\ rw [Once fromSeq_LCONS])
  \\ qsuff_tac ‘!ll. exists p ll ==> !f. ll = fromSeq f ==> ?i. p (f i)’
  THEN1 rw []
  \\ ho_match_mp_tac exists_ind \\ rw []
  \\ pop_assum mp_tac
  \\ rw [Once fromSeq_LCONS]
  THEN1 (qexists_tac ‘0’ \\ fs [])
  \\ first_x_assum (qspec_then ‘f o SUC’ mp_tac)
  \\ rw [] \\ qexists_tac ‘SUC i’ \\ fs []
QED

Theorem every_fromSeq[simp]:
  !p f. every p (fromSeq f) = !i. p (f i)
Proof
  rewrite_tac [every_def] \\ rw []
QED

Theorem LFILTER_fromSeq:
  !p f.
    LFILTER p (fromSeq f) =
      if !i. ~p (f i) then LNIL else
      if p (f 0) then LCONS (f 0) (LFILTER p (fromSeq (f o SUC)))
                 else LFILTER p (fromSeq (f o SUC))
Proof
  gen_tac \\ gen_tac \\ IF_CASES_TAC
  \\ rw [LFILTER_EQ_NIL,Once fromSeq_LCONS]
QED

(* more theorems about fromList and fromSeq *)

Theorem fromList_11[simp]:
  !xs ys. fromList xs = fromList ys <=> xs = ys
Proof
  Induct \\ Cases_on ‘ys’ \\ fs []
QED

Theorem fromSeq_11[simp]:
  !f g. fromSeq f = fromSeq g <=> f = g
Proof
  rw [] \\ eq_tac \\ rw [] \\ fs [FUN_EQ_THM]
  \\ gen_tac \\ rename [‘f n = g n’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘f’
  \\ qid_spec_tac ‘g’
  \\ Induct_on ‘n’ \\ fs []
  \\ once_rewrite_tac [fromSeq_LCONS] \\ fs []
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem fromList_NEQ_fromSeq[simp]:
  !l f. fromList l <> fromSeq f
Proof
  CCONTR_TAC \\ fs []
  \\ qspec_then ‘l’ mp_tac LFINITE_fromList
  \\ qspec_then ‘f’ mp_tac LFINITE_fromSeq
  \\ fs []
QED

Theorem LFINITE_IMP_fromList:
  !ll. LFINITE ll ==> ?l. ll = fromList l
Proof
  rw [] \\ qspec_then ‘ll’ mp_tac fromList_fromSeq
  \\ rw [] \\ fs []
QED

Theorem NOT_LFINITE_IMP_fromSeq:
  !ll. ~LFINITE ll ==> ?f. ll = fromSeq f
Proof
  rw [] \\ qspec_then ‘ll’ mp_tac fromList_fromSeq
  \\ rw [] \\ fs [LFINITE_fromList]
QED

(* suffix over lazy lists *)

Definition LSUFFIX_def:
  LSUFFIX xs zs <=> ?ys. xs = LAPPEND (fromList ys) zs \/ zs = LNIL
End

Theorem LSUFFIX:
  LSUFFIX l LNIL = T /\
  LSUFFIX LNIL (LCONS y ys) = F /\
  LSUFFIX (LCONS x xs) l = (LCONS x xs = l \/ LSUFFIX xs l)
Proof
  fs [LSUFFIX_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (rename [‘fromList zs’] \\ Cases_on ‘zs’ \\ fs []
         \\ disj2_tac \\ qexists_tac ‘t’ \\ fs [])
  THEN1 (qexists_tac ‘[]’ \\ fs [])
  THEN1 (qexists_tac ‘x::ys’ \\ fs [])
QED

Theorem LSUFFIX_fromList:
  !xs ys. LSUFFIX (fromList xs) (fromList ys) <=> IS_SUFFIX xs ys
Proof
  rpt gen_tac \\ fs [LSUFFIX_def,LAPPEND_fromList]
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac rich_listTheory.SNOC_INDUCT \\ rw []
  THEN1
   (qspec_then ‘ys’ mp_tac rich_listTheory.SNOC_CASES \\ rpt strip_tac
    \\ asm_rewrite_tac [rich_listTheory.IS_SUFFIX] \\ fs [])
  \\ rewrite_tac [GSYM rich_listTheory.SNOC_APPEND]
  \\ qspec_then ‘ys’ mp_tac rich_listTheory.SNOC_CASES \\ rpt strip_tac
  \\ asm_rewrite_tac [rich_listTheory.IS_SUFFIX]
  \\ fs [GSYM PULL_EXISTS]
  \\ Cases_on ‘l = []’ \\ fs []
  \\ asm_rewrite_tac [rich_listTheory.IS_SUFFIX]
  \\ first_x_assum (qspec_then ‘l’ mp_tac)
  \\ asm_simp_tac std_ss []
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem LSUFFIX_REFL[simp]:
  !s. LSUFFIX s s
Proof
  rw [LSUFFIX_def] \\ qexists_tac ‘[]’ \\ fs []
QED

Theorem LSUFFIX_TRANS:
  !x y z. LSUFFIX x y /\ LSUFFIX y z ==> LSUFFIX x z
Proof
  rw [LSUFFIX_def]
  \\ fs [LAPPEND_EQ_LNIL]
  \\ rename [‘LAPPEND (fromList zs1) (LAPPEND (fromList zs2) _)’]
  \\ qexists_tac ‘zs1 ++ zs2’
  \\ rewrite_tac [GSYM LAPPEND_ASSOC,LAPPEND_fromList]
QED

Theorem LSUFFIX_ANTISYM:
  !x y. LSUFFIX x y /\ LSUFFIX y x /\ LFINITE x ==> x = y
Proof
  rw [LSUFFIX_def,LAPPEND_EQ_LNIL]
  \\ imp_res_tac LFINITE_IMP_fromList \\ rw []
  \\ fs [LAPPEND_fromList]
QED

Theorem LTAKE_LAPPEND_fromList:
  !ll l n.
    LTAKE (n + LENGTH l) (LAPPEND (fromList l) ll) =
      OPTION_MAP (APPEND l) (LTAKE n ll)
Proof
  rw [] \\ Cases_on `LTAKE n ll` \\ fs []
  THEN1 (
    `LFINITE ll` by (fs [LFINITE] \\ goal_assum drule)
    \\ drule LFINITE_HAS_LENGTH \\ strip_tac \\ rename1 `SOME m`
    \\ irule LTAKE_LLENGTH_NONE
    \\ qexists_tac `m + LENGTH l` \\ rw []
    THEN1 (
      drule LTAKE_LLENGTH_SOME \\ strip_tac
      \\ Cases_on `n <= m` \\ fs []
      \\ drule (GEN_ALL LTAKE_TAKE_LESS)
      \\ disch_then drule \\ fs [])
    \\ fs [LLENGTH_APPEND, LFINITE_fromList])
  \\ Induct_on `l` \\ rw []
  \\ fs [LTAKE_CONS_EQ_SOME]
  \\ goal_assum(drule o PURE_ONCE_REWRITE_RULE[CONJ_SYM])
  \\ simp[]
QED

Theorem LTAKE_LPREFIX:
  !x ll.
   ~LFINITE ll ==>
   ?l. LTAKE x ll = SOME l /\ LPREFIX (fromList l) ll
Proof
  rpt strip_tac >>
  imp_res_tac NOT_LFINITE_IMP_fromSeq >> VAR_EQ_TAC >>
  simp[LPREFIX_fromList,LFINITE_toList_SOME,LPREFIX_fromList,toList]
QED

Theorem LPREFIX_NTH:
  LPREFIX l1 l2 <=>
    !i v. LNTH i l1 = SOME v ==> LNTH i l2 = SOME v
Proof
  qspec_then `l1` strip_assume_tac fromList_fromSeq
  \\ qspec_then `l2` strip_assume_tac fromList_fromSeq
  \\ rw [LPREFIX_def,from_toList]
  \\ fs [toList,FUN_EQ_THM]
  \\ fs [LNTH_fromList]
  THEN1
   (qid_spec_tac `l'` \\ qid_spec_tac `l` \\ Induct \\ fs []
    \\ Cases_on `l'` \\ fs [] THEN1 (qexists_tac `0` \\ fs [])
    \\ rw [] \\ eq_tac \\ rw []
    \\ TRY (Cases_on `i` \\ fs [] \\ NO_TAC)
    THEN1 (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
    \\ first_x_assum (qspec_then `SUC i` mp_tac) \\ fs [])
  THEN1
   (qid_spec_tac `l`
    \\ ho_match_mp_tac rich_listTheory.SNOC_INDUCT
    \\ fs [GSYM ADD1,rich_listTheory.GENLIST] \\ rw []
    \\ eq_tac \\ rw []
    THEN1
     (Cases_on `i = LENGTH l` \\ fs []
      \\ fs [rich_listTheory.SNOC_APPEND,
             rich_listTheory.EL_LENGTH_APPEND,rich_listTheory.EL_APPEND1])
    \\ fs [rich_listTheory.SNOC_APPEND,
           rich_listTheory.EL_LENGTH_APPEND,rich_listTheory.EL_APPEND1])
  THEN1 (qexists_tac `LENGTH l` \\ fs [])
  \\ eq_tac \\ rw []
QED

(* ----------------------------------------------------------------------
    Lazy list bisimulation up-to context, = and transitivity
   ---------------------------------------------------------------------- *)

Inductive llist_upto:
  (llist_upto R x x) /\
  (R x y ==> llist_upto R x y) /\
  (llist_upto R x y /\ llist_upto R y z ==> llist_upto R x z) /\
  (llist_upto R x y ==> llist_upto R (LAPPEND z x) (LAPPEND z y))
End

val [llist_upto_eq,llist_upto_rel,llist_upto_trans,llist_upto_context] =
  llist_upto_rules |> SPEC_ALL |> CONJUNCTS |> map GEN_ALL
  |> curry (ListPair.map save_thm)
    ["llist_upto_eq","llist_upto_rel",
     "llist_upto_trans","llist_upto_context"]

Theorem LLIST_BISIM_UPTO:
  !ll1 ll2 R.
    R ll1 ll2 /\
    (!ll3 ll4.
      R ll3 ll4 ==>
      ll3 = [||] /\ ll4 = [||] \/
      LHD ll3 = LHD ll4 /\
      llist_upto R (THE (LTL ll3)) (THE (LTL ll4)))
  ==> ll1 = ll2
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[LLIST_BISIMULATION]
  >> qexists_tac `llist_upto R`
  >> conj_tac >- rw[llist_upto_rules]
  >> ho_match_mp_tac llist_upto_ind
  >> rpt conj_tac
  >- rw[llist_upto_rules]
  >- first_x_assum ACCEPT_TAC
  >- (rw[]
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac >- simp[]
      >> metis_tac[llist_upto_rules])
  >- (rw[llist_upto_rules]
      >> Cases_on `ll3 = [||]`
      >- (Cases_on `ll4` >> fs[llist_upto_rules])
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac
      >- (Cases_on `z` >> simp[])
      >> Cases_on `z` >- simp[]
      >> simp[]
      >> Cases_on `ll3` >> Cases_on `ll4`
      >> fs[] >> rpt VAR_EQ_TAC
      >> CONV_TAC(RAND_CONV
                  (RAND_CONV
                   (RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM(cj 1 LAPPEND)]))))
      >> CONV_TAC(RATOR_CONV
                  (RAND_CONV
                   (RAND_CONV(RAND_CONV
                              (PURE_ONCE_REWRITE_CONV [GSYM(cj 1 LAPPEND)])))))
      >> PURE_ONCE_REWRITE_TAC[GSYM(CONJUNCT2 LAPPEND)]
      >> simp[GSYM LAPPEND_ASSOC]
      >> metis_tac[llist_upto_rules])
QED

Theorem LDROP_LCONS_LNTH:
  !n xs a t. LDROP n xs = SOME (a:::t) ==> LNTH n xs = SOME a
Proof
  Induct \\ fs [] \\ Cases \\ fs []
QED

Triviality LDROP_WHILE_LEMMA:
  !n k xs ys zs y z.
    LTAKE n xs = SOME ys /\
    LTAKE k xs = SOME zs /\
    LNTH n xs = SOME y /\
    LNTH k xs = SOME z /\
    ~P y /\ ~P z /\ EVERY P ys /\ EVERY P zs ==>
    n = k
Proof
  Induct \\ Cases_on ‘k’ \\ fs []
  \\ Cases_on ‘xs’ \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ fs []
  \\ res_tac
QED

Theorem LDROP_WHILE[local]:
  ?f.
    (!P. f P LNIL = LNIL) /\
    (!P x xs. f P (LCONS x xs) = if P x then f P xs else LCONS x xs) /\
    (!P l. every P l ==> f P l = LNIL)
Proof
  qabbrev_tac ‘foo = λP l n. ?x ls. LNTH n l = SOME x /\ ~P x /\
                                    LTAKE n l = SOME ls /\ EVERY P ls’
  \\ qexists_tac ‘λP l. if every P l then LNIL else
                        THE (LDROP (@n. foo P l n) l)’
  \\ rpt strip_tac \\ fs []
  \\ reverse (Cases_on ‘P x’) \\ fs []
  >-
   (qsuff_tac ‘!n. foo P (x:::xs) n <=> n = 0’ >- fs []
    \\ unabbrev_all_tac \\ fs []
    \\ rw [] \\ eq_tac \\ rw []
    \\ Cases_on ‘n’ \\ gvs [])
  \\ Cases_on ‘every P xs’ \\ fs []
  \\ fs [every_def,exists_thm_strong]
  \\ fs [listTheory.EVERY_MEM] \\ fs [GSYM listTheory.EVERY_MEM]
  \\ drule_then assume_tac LDROP_LCONS_LNTH
  \\ qsuff_tac ‘(!k. foo P xs k <=> k = n) /\
                (!k. foo P (x:::xs) k <=> k = SUC n)’ >- fs []
  \\ rw [Abbr‘foo’]
  \\ rw [] \\ eq_tac \\ rw []
  >- (imp_res_tac LDROP_WHILE_LEMMA \\ fs [])
  \\ Cases_on ‘k’ \\ gvs []
  \\ imp_res_tac LDROP_WHILE_LEMMA \\ fs []
QED

val LDROP_WHILE = new_specification("LDROP_WHILE",["LDROP_WHILE"],LDROP_WHILE);

Theorem LTAKE_WHILE[local]:
  ?f.
    (!P. f P LNIL = LNIL) /\
    (!P x xs. f P (LCONS x xs) = if P x then x ::: f P xs else LNIL) /\
    (!P l. every P l ==> f P l = l)
Proof
  qabbrev_tac ‘foo = λP l n. ?x ls. LNTH n l = SOME x /\ ~P x /\
                                    LTAKE n l = SOME ls /\ EVERY P ls’
  \\ qexists_tac ‘λP l. if every P l then l else
                        fromList (THE (LTAKE (@n. foo P l n) l))’
  \\ rpt strip_tac \\ fs []
  \\ reverse (Cases_on ‘P x’) \\ fs []
  >-
   (qsuff_tac ‘!n. foo P (x:::xs) n <=> n = 0’ >- fs []
    \\ unabbrev_all_tac \\ fs []
    \\ rw [] \\ eq_tac \\ rw []
    \\ Cases_on ‘n’ \\ gvs [])
  \\ Cases_on ‘every P xs’ \\ fs []
  \\ fs [every_def,exists_thm_strong]
  \\ fs [listTheory.EVERY_MEM] \\ fs [GSYM listTheory.EVERY_MEM]
  \\ drule_then assume_tac LDROP_LCONS_LNTH
  \\ qsuff_tac ‘(!k. foo P xs k <=> k = n) /\
                (!k. foo P (x:::xs) k <=> k = SUC n)’ >- fs []
  \\ rw [Abbr‘foo’]
  \\ rw [] \\ eq_tac \\ rw []
  >- (imp_res_tac LDROP_WHILE_LEMMA \\ fs [])
  \\ Cases_on ‘k’ \\ gvs []
  \\ imp_res_tac LDROP_WHILE_LEMMA \\ fs []
QED

val LTAKE_WHILE = new_specification("LTAKE_WHILE",["LTAKE_WHILE"],LTAKE_WHILE);

Theorem LTAKE_WHILE_LDROP_WHILE:
  !P l. LAPPEND (LTAKE_WHILE P l) (LDROP_WHILE P l) = l
Proof
  rw [] \\ Cases_on ‘every P l’
  >- fs [LTAKE_WHILE,LDROP_WHILE,LAPPEND_NIL_2ND]
  \\ fs [every_def,exists_thm_strong]
  \\ fs [listTheory.EVERY_MEM] \\ fs [GSYM listTheory.EVERY_MEM]
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘l'’
  \\ qid_spec_tac ‘l’
  \\ qid_spec_tac ‘n’
  \\ Induct
  >- fs [LTAKE_WHILE,LDROP_WHILE]
  \\ Cases
  \\ fs [LTAKE_WHILE,LDROP_WHILE,PULL_EXISTS]
QED

Definition lbind_def:
  lbind ll f = LFLATTEN (LMAP f ll)
End

Theorem lbind_EQ_NIL:
  lbind ll f = [||] <=>
  !e. e IN LSET ll ==> f e = [||]
Proof
  REWRITE_TAC [Once $ DECIDE “(p = q:bool) = (~p = ~q)”] >>
  simp_tac pure_ss [NOT_FORALL_THM] >>
  simp[lbind_def, LFLATTEN_EQ_NIL, every_def,
       exists_LNTH, LSET_def, PULL_EXISTS, IN_DEF] >>
  metis_tac[]
QED

Theorem LFLATTEN_APPEND_FINITE1:
  !l1 l2.
    LFINITE l1 ==>
    LFLATTEN (LAPPEND l1 l2) = LAPPEND (LFLATTEN l1) (LFLATTEN l2)
Proof
  Induct_on ‘LFINITE’ using LFINITE_INDUCTION >> simp[LAPPEND_ASSOC]
QED

Theorem LFINITE_LFILTER:
  !ll. LFINITE ll ==> LFINITE (LFILTER P ll)
Proof
  Induct_on ‘LFINITE’ >> rw[]
QED

Theorem not_compose:
  $~ o ($~ o f) = f /\ $~ o $~ = I
Proof
  simp[FUN_EQ_THM]
QED

Theorem LFLATTEN_fromList_of_NILs:
  EVERY ($= LNIL) l ==> LFLATTEN (fromList l) = LNIL
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem LFINITE_LFLATTEN:
  LFINITE (LFLATTEN ll) <=>
    LFINITE $ LFILTER ($~ o $= LNIL) ll /\ every LFINITE ll
Proof
  reverse eq_tac >> rw[] >> simp[every_def] >~
  [‘~exists _ ll’]
  >- (strip_tac >> qpat_x_assum ‘LFINITE _’ mp_tac >>
      pop_assum mp_tac >> Induct_on ‘exists’ >> simp[]) >~
  [‘every LFINITE ll’]
  >- (rpt $ pop_assum mp_tac >> qid_spec_tac ‘ll’ >> Induct_on ‘LFINITE’ >>
      rpt strip_tac >> gs[LFILTER_EQ_NIL, not_compose, iffRL LFLATTEN_EQ_NIL]>>
      drule_then strip_assume_tac LFILTER_EQ_CONS >>
      gvs[LFLATTEN_APPEND_FINITE1, LFINITE_fromList,
          not_compose, LFLATTEN_fromList_of_NILs] >>
      drule_at (Pos last) every_LAPPEND2_LFINITE >>
      simp[LFINITE_fromList]) >>
  rpt $ pop_assum mp_tac >> qid_spec_tac ‘ll’ >> Induct_on ‘LFINITE’ >>
  rw[]
  >- gs[LFLATTEN_EQ_NIL, iffRL LFILTER_EQ_NIL, not_compose] >>
  Cases_on ‘LFILTER ($~ o $= LNIL) ll’ >> simp[] >>
  drule_then strip_assume_tac LFILTER_EQ_CONS >>
  gvs[not_compose, LFLATTEN_APPEND_FINITE1, LFINITE_fromList,
      LFILTER_APPEND] >>
  rename [‘LNIL <> hl’,
          ‘LAPPEND (LFLATTEN $ fromList l) (LAPPEND hl $ LFLATTEN ll2) =
           h:::ll1’] >>
  ‘FILTER ($~ o $= LNIL) l = []’
    by simp[listTheory.FILTER_EQ_NIL, SF ETA_ss] >>
  gs[LFLATTEN_fromList_of_NILs] >>
  Cases_on ‘hl’ >> gvs[] >> rename [‘LFLATTEN _ = LAPPEND t _’] >>
  first_x_assum $ qspec_then ‘t:::ll2’ mp_tac >> simp[LFLATTEN_APPEND] >>
  rw[] >> rw[]
QED

Theorem LFLATTEN_EQ_CONS:
  LFLATTEN ll = h:::t <=>
  ?p e t1 t2.
    ll = LAPPEND p ((h:::t1) ::: t2) /\
    LFINITE p /\ every ($= LNIL) p /\
    t = LAPPEND t1 (LFLATTEN t2)
Proof
  reverse eq_tac >> rpt strip_tac
  >- (simp[LFLATTEN_APPEND_FINITE1] >>
      ‘LFLATTEN p = LNIL’ suffices_by simp[] >>
      simp[LFLATTEN_EQ_NIL]) >>
  ‘exists ($~ o $= LNIL) ll’
    by (CCONTR_TAC >> gs[GSYM every_def, GSYM LFLATTEN_EQ_NIL]) >>
  rpt (pop_assum mp_tac) >> map_every qid_spec_tac [‘h’, ‘t’, ‘ll’] >>
  Induct_on ‘exists’ >> rw[] >~
  [‘LNIL <> hl’, ‘LAPPEND hl $ LFLATTEN t1 = h:::t2’]
  >- (Cases_on ‘hl’ >> gvs[] >> irule_at Any EQ_REFL >> qexists ‘LNIL’ >>
      simp[]) >~
  [‘LAPPEND hl $ LFLATTEN t1 = h:::t2’] >>
  Cases_on ‘hl’ >> gvs[]
  >- (qexists ‘LNIL ::: p’ >> simp[] >> metis_tac[]) >>
  qexists ‘LNIL’ >> simp[]
QED

Theorem lbind_APPEND:
  LFINITE l1 ==>
  lbind (LAPPEND l1 l2) f = LAPPEND (lbind l1 f) (lbind l2 f)
Proof
  simp[lbind_def, LMAP_APPEND, LFLATTEN_APPEND_FINITE1]
QED

Theorem lbind_CONS[simp]:
  lbind (h:::t) f = LAPPEND (f h) (lbind t f)
Proof
  simp[lbind_def]
QED

Theorem LMAP_EQ_NIL[simp]:
  (LMAP f l = LNIL <=> l = LNIL) /\
  (LNIL = LMAP f l <=> l = LNIL)
Proof
  Cases_on ‘l’ >> simp[]
QED

Theorem LMAP_EQ_CONS:
  LMAP f l = h:::t <=> ?h0 t0. l = h0:::t0 /\ h = f h0 /\ t = LMAP f t0
Proof
  Cases_on ‘l’ >> simp[] >> metis_tac[]
QED

Theorem LMAP_EQ_APPEND_FINITE1:
  !ll ll1 ll2.
    LFINITE ll1 ==>
    (LMAP f ll = LAPPEND ll1 ll2 <=>
     ?ll10 ll20. ll = LAPPEND ll10 ll20 /\ LMAP f ll10 = ll1 /\
                 LMAP f ll20 = ll2)
Proof
  Induct_on ‘LFINITE’ >> simp[LMAP_EQ_CONS, PULL_EXISTS] >> metis_tac[]
QED

Theorem lbind_EQ_CONS:
  lbind ll f = h:::t <=>
  ?p e s t1 t2.
    ll = LAPPEND p (e ::: s) /\ LFINITE p /\
    (!e0. e0 IN LSET p ==> f e0 = [||]) /\
    t = LAPPEND t1 t2 /\
    f e = h:::t1 /\
    lbind s f = t2
Proof
  reverse eq_tac >> rpt strip_tac
  >- (simp[lbind_APPEND] >> ‘lbind p f = LNIL’ by simp[lbind_EQ_NIL] >>
      simp[]) >>
  gvs[lbind_def, LFLATTEN_EQ_CONS, LMAP_EQ_APPEND_FINITE1, LMAP_EQ_CONS] >>
  rpt $ irule_at Any EQ_REFL >> simp[] >>
  gs[every_LNTH, PULL_EXISTS, LSET_def, IN_DEF]
QED

Theorem LSET_exists:
  x IN LSET ll <=> exists ($= x) ll
Proof
  simp[IN_DEF, LSET_def, exists_LNTH] >> metis_tac[]
QED

Theorem exists_APPEND:
  !l1 l2. exists P (LAPPEND l1 l2) <=> exists P l1 \/ LFINITE l1 /\ exists P l2
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM] >> rpt conj_tac >~
  [‘exists _ (LAPPEND _ _) ==> _’]
  >- (Induct_on‘exists’ >> rw[] >> rename [‘LAPPEND l1 l2 = h:::t’] >>
      Cases_on ‘l1’ >> gvs[] >> metis_tac[]) >~
  [‘exists _ _ ==> _’]
  >- (Induct_on ‘exists’ >> simp[]) >>
  Induct_on ‘LFINITE’ >> simp[]
QED

Theorem LAPPEND11_FINITE1:
  !l1 l2 l3. LFINITE l1 ==> (LAPPEND l1 l2 = LAPPEND l1 l3 <=> l2 = l3)
Proof
  Induct_on ‘LFINITE’ >> simp[]
QED

Theorem every_APPEND_EQN:
  every P (LAPPEND l1 l2) <=> every P l1 /\ (LFINITE l1 ==> every P l2)
Proof
  reverse $ Cases_on ‘LFINITE l1’ >> simp[NOT_LFINITE_APPEND] >>
  pop_assum mp_tac >> Induct_on ‘LFINITE’ >> simp[] >> metis_tac[]
QED

Theorem exists_FLATTEN:
  exists P (LFLATTEN ll) <=>
  ?p e0 s.
    LFINITE p /\ every LFINITE p /\ ll = LAPPEND p (e0:::s) /\ exists P e0
Proof
  eq_tac
  >- (qid_spec_tac ‘ll’ >> Induct_on ‘exists’ >> rw[] >>
      gvs[LFLATTEN_EQ_CONS, exists_APPEND] >> dsimp[] >~
      [‘exists P (LFLATTEN t2)’, ‘LFLATTEN _ = LAPPEND t1 (LFLATTEN t2)’]
      >- (first_x_assum $ qspec_then ‘t1:::t2’ mp_tac >> simp[] >> rw[] >>
          rename [‘t1:::t2 = LAPPEND p0 (e0:::s)’,
                  ‘LAPPEND p ((h:::t1):::t2)’] >>
          Cases_on ‘p0’ >> gvs[]
          >- (irule_at Any EQ_REFL >> simp[] >> irule MONO_every >>
              first_assum $ irule_at Any >> simp[]) >>
          rename [‘LAPPEND p ((h:::hl) ::: LAPPEND t (e0:::s))’] >>
          qexists ‘LAPPEND p ((h:::hl) ::: t)’ >>
          simp[LAPPEND11_FINITE1, LAPPEND_ASSOC,
               every_APPEND_EQN] >> irule MONO_every >>
          first_assum $ irule_at Any >> simp[]) >>
      irule_at Any EQ_REFL >> simp[] >> irule MONO_every >>
      first_assum $ irule_at Any >> simp[]) >>
  simp[PULL_EXISTS, LFLATTEN_APPEND_FINITE1, exists_APPEND, LFINITE_LFLATTEN,
       LFINITE_LFILTER]
QED

Theorem LSET_FLATTEN:
  LSET $ LFLATTEN ll = { e | ?p e0 s. ll = LAPPEND p (e0:::s) /\ e IN LSET e0 /\
                                      LFINITE p /\ every LFINITE p }
Proof
  simp[LSET_exists, EXTENSION, exists_FLATTEN] >> metis_tac[]
QED

Theorem every_LMAP:
  every P (LMAP f l) <=> every (P o f) l
Proof
  eq_tac
  >- (qid_spec_tac ‘l’ >> ho_match_mp_tac every_coind >> simp[]) >>
  ‘!l. (?l0. l = LMAP f l0 /\ every (P o f) l0) ==> every P l’
    suffices_by simp[PULL_EXISTS] >>
  ho_match_mp_tac every_coind >> simp[LMAP_EQ_CONS, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem LSET_lbind:
  LSET (lbind ll f) = { e | ?p e0 s. ll = LAPPEND p (e0:::s) /\
                                     LFINITE p /\ every (LFINITE o f) p /\
                                     e IN LSET $ f e0 }
Proof
  simp[EXTENSION,lbind_def, LSET_FLATTEN, SF CONJ_ss, LMAP_EQ_APPEND_FINITE1,
       PULL_EXISTS, LMAP_EQ_CONS, every_LMAP] >>
  metis_tac[]
QED

Theorem LSET_APPEND:
  LSET (LAPPEND l1 l2) = LSET l1 UNION (if LFINITE l1 then LSET l2 else {})
Proof
  reverse $ Cases_on ‘LFINITE l1’ >> simp[NOT_LFINITE_APPEND] >>
  pop_assum mp_tac >> Induct_on ‘LFINITE’ >>
  simp[INSERT_UNION_EQ]
QED

Theorem LSET_FINITE_pfx:
  x IN LSET ll <=> ?p s. ll = LAPPEND p (x:::s) /\ LFINITE p
Proof
  simp[EQ_IMP_THM, PULL_EXISTS, LSET_APPEND] >>
  simp[IN_DEF, LSET_def, PULL_EXISTS] >> qid_spec_tac ‘ll’ >> Induct_on ‘n’ >>
  Cases_on ‘ll’ >> simp[] >> strip_tac >- (qexists ‘LNIL’ >> simp[]) >>
  first_x_assum $ drule_then strip_assume_tac >> gvs[] >>
  rename [‘h:::(LAPPEND p _)’] >> qexists ‘h:::p’ >> simp[] >>
  metis_tac[]
QED

Overload rpt_el = “λe. LGENLIST (K e) NONE”

Theorem fromList_EQ_CONS:
  fromList l = h:::t <=> ?t0. l = h::t0 /\ t = fromList t0
Proof
  Cases_on ‘l’ >> simp[] >> metis_tac[]
QED

Theorem GENLIST_EQ_CONS:
  GENLIST f n = h::t <=> 0 < n /\ f 0 = h /\ t = GENLIST (f o SUC) (n - 1)
Proof
  Cases_on ‘n’ >> simp[listTheory.GENLIST_CONS] >> metis_tac[]
QED

Theorem LGENLIST_SOME_EQ_CONS:
  LGENLIST f (SOME n) = h:::t <=>
  0 < n /\ f 0 = h /\ t = LGENLIST (f o SUC) (SOME (n - 1))
Proof
  simp[LGENLIST_EQ_fromList, fromList_EQ_CONS, GENLIST_EQ_CONS]
QED

Theorem every_LGENLIST:
  (every P (LGENLIST f (SOME n)) <=> (!m. m < n ==> P (f m))) /\
  (every P (LGENLIST f NONE) <=> !m. P (f m))
Proof
  conj_tac >> eq_tac >~
  [‘_ ==> every P (LGENLIST f NONE)’]
  >- (‘!ll. (?f. ll = LGENLIST f NONE /\ !m. P (f m)) ==> every P ll’
        suffices_by metis_tac[]>>
      ho_match_mp_tac every_coind >>
      simp[LGENLIST_EQ_CONS, PULL_EXISTS] >> rw[] >>
      irule_at Any EQ_REFL >> simp[]) >~
  [‘_ ==> every _ _ ’]
  >- (‘!ll. (?f n. ll = LGENLIST f (SOME n) /\ !m. m < n ==> P (f m)) ==>
            every P ll’
        suffices_by metis_tac[] >>
      ho_match_mp_tac every_coind >> simp[LGENLIST_SOME_EQ_CONS, PULL_EXISTS] >>
      rpt strip_tac >> irule_at Any EQ_REFL >> simp[]) >~
  [‘every _ (LGENLIST f (SOME n))’]
  >- (map_every qid_spec_tac [‘f’, ‘n’] >> Induct >>
      simp[LT_SUC, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  CONV_TAC CONTRAPOS_CONV >> qid_spec_tac ‘f’ >>
  simp[GSYM every_def, PULL_EXISTS] >> CONV_TAC SWAP_FORALL_CONV >>
  Induct >> rpt strip_tac >>
  Cases_on ‘LGENLIST f NONE’ >> gvs[LGENLIST_EQ_CONS] >>
  first_x_assum $ drule_at Concl >> gs[ADD1]
QED

Theorem rpt_el_CONS':
  e ::: rpt_el e = rpt_el e
Proof
  Cases_on ‘rpt_el e’ >> gs[LGENLIST_EQ_CONS]
QED

Theorem rpt_el_EQ_APPEND:
  rpt_el e = LAPPEND l1 l2 <=>
  if LFINITE l1 then every ($= e) l1 /\ l2 = rpt_el e
  else l1 = rpt_el e
Proof
  reverse $ rw[NOT_LFINITE_APPEND] >- metis_tac[] >>
  pop_assum mp_tac >> Induct_on ‘LFINITE’ >> simp[] >> conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> simp[Once $ GSYM rpt_el_CONS', SimpLHS] >> metis_tac[]
QED

(*
Theorem LFLATTEN_rpt_el:
  LFLATTEN (rpt_el l) = if LFINITE l then LREPEAT (THE (toList l))
                        else l
Proof
  Cases_on ‘LFINITE l’ >> simp[]
  >- (Cases_on ‘l = LNIL’ >> simp[toList_THM, LFLATTEN_EQ_NIL, every_LGENLIST]>>
      ONCE_REWRITE_TAC [LLIST_BISIMULATION] >>
      qexists ‘λl1 l2. ?l. LFINITE l /\ l1 = LFLATTEN (rpt_el l) /\
                           l2 = LREPEAT (THE (toList l))’ >>
      rw[] >- (irule_at Any EQ_REFL >> simp[]) >>
      rename [‘LFLATTEN (rpt_el ll) = LNIL’] >>
      Cases_on ‘LFLATTEN (rpt_el ll)’ >> simp[]
      >- gvs[LFLATTEN_EQ_NIL, every_LGENLIST, toList_THM] >>
      simp[] >> gvs[LFLATTEN_EQ_CONS] >>
      Cases_on ‘ll = LNIL’
      >- (gvs[toList_THM, rpt_el_EQ_APPEND] >>
          gs[LGENLIST_EQ_CONS]) >>
      gvs[rpt_el_EQ_APPEND, LGENLIST_EQ_CONS] >>
      rename [‘every _ pfx’] >> Cases_on ‘pfx’ >> gvs[] >>
      simp[to_fromList] >> rename [‘LAPPEND ’
*)


Theorem lbind_thm:
  lbind LNIL f = LNIL /\
  lbind (h:::t) f = LAPPEND (f h) $ lbind t f
Proof
  simp[lbind_def]
QED

Theorem lbind_notASSOC:
  let f b = if b then rpt_el T else [|F|] ;
      g b = if b then LNIL else [| 1 |] ;
      bs = [|T; F|]
  in
    lbind bs (λb. lbind (f b) g) <> lbind (lbind bs f) g
Proof
  simp[lbind_def, NOT_LFINITE_APPEND] >>
  ‘LFLATTEN (rpt_el LNIL : num llist llist) = LNIL’ suffices_by simp[] >>
  simp[LFLATTEN_EQ_NIL, every_LGENLIST]
QED

Theorem LPREFIX_LAPPEND_fromList:
  (LPREFIX (LAPPEND (fromList l) l1) (LAPPEND (fromList l) l2))
  <=> (LPREFIX l1 l2)
Proof
  fs[LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>metis_tac[]
QED

val _ = export_theory();
