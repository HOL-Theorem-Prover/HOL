(*****************************************************************************)
(* Theorems to support a simple compiler, with programs represented as       *)
(* ML list of HOL definitions.                                               *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
******************************************************************************)
(*
quietdec := true;
loadPath :="dff" :: !loadPath;
map load  ["metisLib","composeTheory","devTheory","dffTheory"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory devTheory dffTheory metisLib;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open metisLib arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory dffTheory devTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************p************************************************************)
(* Start new theory "compile"                                                *)
(*****************************************************************************)
val _ = new_theory "compile";

(*****************************************************************************)
(* |- f ===> g = !x. f x ==> g x                                             *)
(*****************************************************************************)
val _ = set_fixity "===>" (Infixr 540);
val DEV_IMP_def =
 xDefine "DEV_IMP" `$===> f g = !x. f x ==> g x`;

val DEV_IMP_REFL =
 store_thm
  ("DEV_IMP_REFL",
   ``!f. f ===> f``,
   RW_TAC std_ss [DEV_IMP_def]);

val DEV_IMP_TRANS =
 store_thm
  ("DEV_IMP_TRANS",
   ``!f g. (f ===> g) /\ (g ===> h) ==> (f ===> h)``,
   RW_TAC std_ss [DEV_IMP_def]);

(*****************************************************************************)
(* Rename device signals to standard names                                   *)
(*****************************************************************************)
val DEV_QUANT_RENAME =
 store_thm
  ("DEV_QUANT_RENAME",
   ``!P.
      (!(p1,p2,p3,p4). P(p1, p2, p3, p4)) = 
      !load inp done out. P(load, inp, done, out)``,
   SIMP_TAC std_ss [GSYM LAMBDA_PROD,FORALL_PROD]);

(*****************************************************************************)
(* Normalise for use in compiling                                            *)
(*****************************************************************************)
val DEV_QUANT_NORM =
 store_thm
  ("DEV_QUANT_NORM",
   ``(!P. (!(p1,p2,p3,p4). P(p1, p2, p3, p4)) = 
          !p. P(FST p, FST(SND p), FST(SND(SND p)), SND(SND(SND p))))
     /\
     (!P. (!p1 p2 p3 p4. P(p1, p2, p3, p4)) = 
          !p. P(FST p, FST(SND p), FST(SND(SND p)), SND(SND(SND p))))``,
   SIMP_TAC std_ss [GSYM LAMBDA_PROD,FORALL_PROD]);

(*****************************************************************************)
(* First the operators:                                                      *)
(*                                                                           *)
(*  Seq f1 f2      f1 followed by f2 in series                               *)
(*  Par f1 f2      f1 in parallel with f2                                    *)
(*  Ite f1 f2 f3   if f1 then f2 else f3                                     *)
(*  Rec f1 f2 f3   tail recursion with test f1, base f2 and step f3          *)
(*****************************************************************************)

val Seq_def =
 Define `Seq f1 f2 = \x. f2(f1 x)`;

val Par_def =
 Define `Par f1 f2 = \x. (f1 x, f2 x)`;

val Ite_def =
 Define `Ite f1 f2 f3 = \x. if f1 x then f2 x else f3 x`;

val Rec_def = Define `Rec = TAILREC`;

(*****************************************************************************)
(* Seq is just reverse order function composition                            *)
(*****************************************************************************)
val Seq_o =
 store_thm
  ("Seq_o",
   ``Seq f1 f2 = f2 o f1``,
   RW_TAC std_ss [Seq_def,o_THM,FUN_EQ_THM]);

(*****************************************************************************)
(* Precede a device with a function                                          *)
(*****************************************************************************)
val PRECEDE_def =
 Define
  `PRECEDE f d = 
    \(load,inp,done,out). ?v. COMB f (inp,v) /\ d(load,v,done,out)`;

val PRECEDE_ID =
 store_thm
  ("PRECEDE_ID",
   ``PRECEDE (\x.x) d = d``,
   RW_TAC std_ss [PRECEDE_def,COMB_def,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [FULL_SIMP_TAC std_ss [GSYM FUN_EQ_THM]
       THEN RW_TAC std_ss []
       THEN METIS_TAC[PAIR,ETA_AX],
      Q.EXISTS_TAC `FST(SND x)`
       THEN RW_TAC std_ss []]);

(*****************************************************************************)
(* Precede a device with a combinational circuit                             *)
(*****************************************************************************)
val PRECEDE_DEV =
 store_thm
  ("PRECEDE_DEV",
   ``!f1 f2 P.
      (P ===> DEV f2)
      ==>
      PRECEDE f1 P
      ===> 
      DEV (Seq f1 f2)``,
   RW_TAC std_ss 
    [PRECEDE_def,FORALL_PROD,DEV_IMP_def,DEV_def,SAFE_DEV_def,COMB_def,
     LIV_def,Seq_def]
    THENL
     [RES_TAC
       THEN Q.EXISTS_TAC `t''`
       THEN RW_TAC std_ss [],
      RES_TAC,
      PROVE_TAC[]]);

(*****************************************************************************)
(* Follow a device with a function                                          *)
(*****************************************************************************)
val FOLLOW_def =
 Define
  `FOLLOW d f =
    \(load,inp,done,out). ?v. d(load,inp,done,v) /\ COMB f (v,out)`;

val FOLLOW_ID =
 store_thm
  ("FOLLOW_ID",
   ``FOLLOW d (\x.x) = d``,
   RW_TAC std_ss [FOLLOW_def,COMB_def,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [FULL_SIMP_TAC std_ss [GSYM FUN_EQ_THM]
       THEN RW_TAC std_ss []
       THEN METIS_TAC[PAIR,ETA_AX],
      Q.EXISTS_TAC `SND(SND(SND x))`
       THEN RW_TAC std_ss []]);

(*****************************************************************************)
(* Follow a device with a combinational circuit                              *)
(*****************************************************************************)
val FOLLOW_DEV =
 store_thm
  ("FOLLOW_DEV",
   ``!f2 f1 P.
      (P ===> DEV f1)
      ==>
      FOLLOW P f2
      ===> 
      DEV (Seq f1 f2)``,
   RW_TAC std_ss 
    [FOLLOW_def,FORALL_PROD,DEV_IMP_def,DEV_def,SAFE_DEV_def,
     LIV_def,Seq_def,COMB_def]
    THENL
     [RES_TAC
       THEN Q.EXISTS_TAC `t''`
       THEN RW_TAC std_ss [],
      RES_TAC,
      PROVE_TAC[]]);

(*****************************************************************************)
(* Introduction rules for devices                                            *)
(*****************************************************************************)
val ATM_INTRO =
 store_thm
  ("ATM_INTRO",
   ``!f. ATM f ===> DEV f``,
   SIMP_TAC std_ss [DEV_IMP_def,FORALL_PROD,ATM]);

val SEQ_INTRO =
 store_thm
  ("SEQ_INTRO",
   ``!P1 P2 f1 f2.
      (P1 ===> DEV f1) /\  (P2 ===> DEV f2)
      ==>
      SEQ P1 P2 ===> DEV (Seq f1 f2)``,
   RW_TAC std_ss [FORALL_PROD,SEQ_def,DEV_IMP_def]
    THEN `DEV f1 (c0,p_1',c1,data)` by PROVE_TAC[]
    THEN `DEV f2 (c1,data,c2,p_2)` by PROVE_TAC[]
    THEN `SEQ (DEV f1) (DEV f2) (p_1,p_1',p_1'',p_2)` 
          by IMP_RES_TAC((hd o IMP_CANON o snd o EQ_IMP_RULE)(SPEC_ALL SEQ_def))
    THEN IMP_RES_TAC SEQ
    THEN FULL_SIMP_TAC std_ss [o_DEF,GSYM Seq_def]);

val PAR_INTRO =
 store_thm
  ("PAR_INTRO",
   ``!P1 P2 f1 f2.
      (P1 ===> DEV f1) /\  (P2  ===> DEV f2)
      ==>
      PAR P1 P2 ===> DEV (Par f1 f2)``,
   RW_TAC std_ss [FORALL_PROD,PAR_def,DEV_IMP_def]
    THEN `DEV f1 (start,p_1',done',data')` by PROVE_TAC[]
    THEN `DEV f2 (start,p_1',done'',data'')` by PROVE_TAC[]
    THEN `!out. 
           (out = (\t. (out' t,out'' t))) ==>
            PAR (DEV f1) (DEV f2) (p_1,p_1',p_1'',out)`
          by (IMP_RES_TAC((hd o IMP_CANON o snd o EQ_IMP_RULE)(SPEC_ALL PAR_def))
               THEN RW_TAC std_ss [])
    THEN FULL_SIMP_TAC std_ss [Par_def]
    THEN IMP_RES_TAC PAR);

val ITE_INTRO =
 store_thm
  ("ITE_INTRO",
   ``!P1 P2 P3 f1 f2 f3.
      (P1 ===> DEV f1) /\  (P2 ===> DEV f2) /\  (P3 ===> DEV f3)
       ==>
       ITE P1 P2 P3 ===> DEV (Ite f1 f2 f3)``,
   RW_TAC std_ss [FORALL_PROD,PAR_def,ITE_def,Ite_def,DEV_IMP_def]
    THEN `DEV f1 (start,p_1',done_e,data_e)` by PROVE_TAC[]
    THEN `DEV f2 (start_f,q,done_f,data_f)` by PROVE_TAC[]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC[]
    THEN `ITE (DEV f1) (DEV f2) (DEV f3) (p_1,p_1',p_1'',p_2)`
          by IMP_RES_TAC((hd o IMP_CANON o snd o EQ_IMP_RULE)(SPEC_ALL ITE_def))
    THEN IMP_RES_TAC ITE);

val REC_INTRO =
 store_thm
  ("REC_INTRO",
   ``!f1 f2 f3 P1 P2 P3 .
      TOTAL(f1,f2,f3)
      ==>
      (P1 ===> DEV f1) /\  (P2 ===> DEV f2) /\  (P3 ===> DEV f3)
       ==>
       REC P1 P2 P3 ===> DEV (Rec f1 f2 f3)``,
   SIMP_TAC std_ss [FORALL_PROD,DEV_IMP_def]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN RW_TAC std_ss [FORALL_PROD,PAR_def,REC_def]
    THEN `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC[]
    THEN `DEV f2 (start_f,q,done_f,p_2)` by PROVE_TAC[]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC[]
    THEN `REC (DEV f1) (DEV f2) (DEV f3) (p_1,p_1',p_1'',p_2)`
          by IMP_RES_TAC((hd o IMP_CANON o snd o EQ_IMP_RULE)(SPEC_ALL REC_def))
    THEN IMP_RES_TAC REC
    THEN RW_TAC arith_ss [Rec_def]);

(*****************************************************************************)
(* An expression is just a HOL term built using a devices defined earlier    *)
(* in a program (see description of programs below) and Seq, Par,            *)
(* Ite and Rec:                                                              *)
(*                                                                           *)
(*  expr := Lib f                                                            *)
(*        | Atm f                                                            *)
(*        | Seq expr expr                                                    *)
(*        | Par expr expr                                                    *)
(*        | Ite expr expr expr                                               *)
(*        | Rec expr expr expr                                               *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*  ``Rec (Seq Fst Test0) Ident (Par (Seq Fst Dec) Mult)``                   *)
(*                                                                           *)
(* (where Fst, Test0, Ident, Dec, Mult previously defined)                   *)
(*                                                                           *)
(* A program is a list of definitions whose left hand sides are variables    *)
(* or constants and whose right hand sides are expressions built using       *)
(* constants defined earlier in the program and Seq, Par and Ite.            *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*  [Define `Test0    = \n. n=0`,                                            *)
(*   Define `Ident    = \(n,acc). (n,acc)`,                                  *)
(*   Define `Dec      = \n. n-1`,                                            *)
(*   Define `Mult     = \(n,acc). n*acc`,                                    *)
(*   Define `Fst      = \(n,acc). n`,                                        *)
(*   Define `Snd      = \(n,acc). acc`,                                      *)
(*   Define `FactIter = Rec (Seq Fst Test0) Ident (Par (Seq Fst Dec) Mult)`, *)
(*   Define `Fact     = Seq FactIter Snd`];                                  *)
(*                                                                           *)
(* Note that a program is represented here an ML list of theorems (which     *)
(* are definitions).                                                         *)
(*****************************************************************************)

(*****************************************************************************)
(* A Rec satisfies the expected recursive equation if total                  *)
(* Unused?                                                                   *)
(*****************************************************************************)
val TOTAL_LEMMA_COR =
 store_thm
  ("TOTAL_LEMMA_COR",
   ``!f1 f2 f3.
      TOTAL (f1,f2,f3) 
      ==>
      !x. Rec f1 f2 f3 x = if f1 x then f2 x else Rec f1 f2 f3 (f3 x)``,
   METIS_TAC[TOTAL_LEMMA,Rec_def]);

(*****************************************************************************)
(* A well-formed (i.e. total) recursive definition is a Rec                  *)
(*****************************************************************************)
val TOTAL_THM =
 store_thm
  ("TOTAL_THM",
   ``!f f1 f2 f3.
      TOTAL(f1,f2,f3)
      ==>
      (!x. f x = if f1 x then f2 x else f (f3 x))
      ==>
      (f = Rec f1 f2 f3)``,
   REWRITE_TAC [Rec_def,FUN_EQ_THM]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC TOTAL_LEMMA
    THEN IMP_RES_TAC TOTAL_def
    THEN measureInduct_on `variant x`
    THEN Cases_on `f1 x`
    THEN PROVE_TAC[]);

(*****************************************************************************)
(* Monotonicity of ===> lemmas for device refinement                         *)
(*****************************************************************************)
val PRECEDE_DEV_IMP =
 store_thm
  ("PRECEDE_DEV_IMP",
   ``!f P Q. 
       (P ===> Q) ==> (PRECEDE f P ===> PRECEDE f Q)``,
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD,PRECEDE_def,COMB_def]
    THEN METIS_TAC[]);

val FOLLOW_DEV_IMP =
 store_thm
  ("FOLLOW_DEV_IMP",
   ``!f P Q. 
       (P ===> Q) ==> (FOLLOW P f ===> FOLLOW Q f)``,
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD,FOLLOW_def,COMB_def]
    THEN METIS_TAC[]);

val SEQ_DEV_IMP =
 store_thm
  ("SEQ_DEV_IMP",
   ``!P1 P2 Q1 Q2. 
       P1 ===> Q1 /\ P2 ===> Q2
       ==>
       (SEQ P1 P2 ===> SEQ Q1 Q2)``,   
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD]
    THEN FULL_SIMP_TAC std_ss [SEQ_def]   (* Not needed, but speeds up proof *)
    THEN PROVE_TAC[]);

val PAR_DEV_IMP =
 store_thm
  ("PAR_DEV_IMP",
   ``!P1 P2 Q1 Q2. 
       P1 ===> Q1 /\ P2 ===> Q2
       ==>
       (PAR P1 P2 ===> PAR Q1 Q2)``,   
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD]
    THEN FULL_SIMP_TAC std_ss [PAR_def]
    THEN PROVE_TAC[]);

val ITE_DEV_IMP =
 store_thm
  ("ITE_DEV_IMP",
   ``!P1 P2 P3 Q1 Q2 Q3. 
       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3
       ==>
       (ITE P1 P2 P3 ===> ITE Q1 Q2 Q3)``,   
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD]
    THEN FULL_SIMP_TAC std_ss [ITE_def]
    THEN PROVE_TAC[]);

val REC_DEV_IMP =
 store_thm
  ("REC_DEV_IMP",
   ``!P1 P2 P3 Q1 Q2 Q3. 
       P1 ===> Q1 /\ P2 ===> Q2 /\ P3 ===> Q3
       ==>
       (REC P1 P2 P3 ===> REC Q1 Q2 Q3)``,   
   RW_TAC std_ss [DEV_IMP_def,FORALL_PROD]
    THEN FULL_SIMP_TAC std_ss [REC_def]
    THEN PROVE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Tag constant for the measure function. Used infix.                        *)
(*---------------------------------------------------------------------------*)

val _ = new_constant ("measuring", bool --> alpha --> bool);
val _ = add_infix ("measuring", 90, NONASSOC);

(*****************************************************************************)
(* f <> g = \t. (f t, g t)                                                   *)
(*****************************************************************************)
val BUS_CONCAT_def =
 Define
  `BUS_CONCAT f g = \t. (f t, g t)`;

val _ = set_fixity "<>" (Infixr 510);
val _ = overload_on ("<>", ``BUS_CONCAT``);

val COMB_FST =
 store_thm
  ("COMB_FST",
   ``COMB FST (f <> g, h) = (h = f)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val COMB_SND =
 store_thm
  ("COMB_SND",
   ``COMB SND (f <> g, h) = (h = g)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val COMB_CONCAT_FST =
 store_thm
  ("COMB_CONCAT_FST",
   ``COMB (\(x,y). P x) (inp1 <> inp2, out) = COMB P (inp1,out)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val COMB_CONCAT_SND =
 store_thm
  ("COMB_CONCAT_SND",
   ``COMB (\(x,y). P y) (inp1 <> inp2, out) = COMB P (inp2,out)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val COMB_CONCAT_SPLIT =
 store_thm
  ("COMB_CONCAT_SPLIT",
   ``COMB (f <> g) (inp, out1 <> out2) = 
      COMB f (inp,out1) /\ COMB g (inp,out2)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val FUN_EXISTS_PROD =
 store_thm
  ("FUN_EXISTS_PROD",
   ``(?f. P f) = ?f1 f2. P(f1 <> f2)``,
   RW_TAC std_ss [BUS_CONCAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `\t. FST(f t)` THEN Q.EXISTS_TAC `\t. SND(f t)`
       THEN RW_TAC std_ss [ETA_THM],
      PROVE_TAC[]]);

val FUN_FORALL_PROD =
 store_thm
  ("FUN_FORALL_PROD",
   ``(!f. P f) = !f1 f2. P(f1 <> f2)``,
   RW_TAC std_ss [BUS_CONCAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN POP_ASSUM(ASSUME_TAC o Q.SPECL[`FST o f`,`SND o f`])
    THEN FULL_SIMP_TAC std_ss [ETA_THM]);

val BUS_CONCAT_ETA =
 store_thm
  ("BUS_CONCAT_ETA",
   ``(\t. (f <> g) t) = f <> g``,
   ZAP_TAC std_ss [ETA_THM]);

val ID_o =
 store_thm
  ("ID_o",
   ``((\x. x) o f) = f``,
   RW_TAC std_ss [FUN_EQ_THM]);

val o_ID =
 store_thm
  ("o_ID",
   ``(f o (\x. x)) = f``,
   RW_TAC std_ss [FUN_EQ_THM]);

val ID_CONST =
 store_thm
  ("ID_CONST",
   ``((\x. c) o f) = \t. c``,
   RW_TAC std_ss [FUN_EQ_THM]);

(***** Disabled, pending a more general approach that works for all sizes ****
(*****************************************************************************)
(* Bus selector operators                                                    *)
(*****************************************************************************)

val SEL_2_1_def =
 Define
  `SEL_2_1 (inp,out) = (out = FST o inp)`;

val SEL_2_2_def =
 Define
  `SEL_2_2 (inp,out) = (out = SND o inp)`;

val SEL_3_1_def =
 Define
  `SEL_3_1 (inp,out) = (out = FST o inp)`;

val SEL_3_2_def =
 Define
  `SEL_3_2 (inp,out) = (out = FST o SND o inp)`;

val SEL_3_3_def =
 Define
  `SEL_3_3 (inp,out) = (out = SND o SND o inp)`;

val SEL_DEFS =
 save_thm
  ("SEL_DEFS",
   LIST_CONJ[SEL_2_1_def,SEL_2_2_def,
             SEL_3_1_def,SEL_3_2_def,SEL_3_3_def]);

val COMP_SEL_2_1 =
 store_thm
  ("COMP_SEL_2_1",
   ``COMB (\(x,y). x) = SEL_2_1``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`x`)
    THEN SIMP_TAC std_ss 
          [COMB_def,SEL_2_1_def,FORALL_PROD,o_DEF,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMP_SEL_2_2 =
 store_thm
  ("COMP_SEL_2_2",
   ``COMB (\(x,y). y) = SEL_2_2``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`x`)
    THEN SIMP_TAC std_ss 
          [COMB_def,SEL_2_2_def,FORALL_PROD,o_DEF,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMP_SEL_3_1 =
 store_thm
  ("COMP_SEL_3_1",
   ``COMB (\(x,y,z). x) = SEL_3_1``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`x`)
    THEN SIMP_TAC std_ss 
          [COMB_def,SEL_3_1_def,FORALL_PROD,o_DEF,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMP_SEL_3_2 =
 store_thm
  ("COMP_SEL_3_2",
   ``COMB (\(x,y,z). y) = SEL_3_2``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`x`)
    THEN SIMP_TAC std_ss 
          [COMB_def,SEL_3_2_def,FORALL_PROD,o_DEF,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMP_SEL_3_3 =
 store_thm
  ("COMP_SEL_3_3",
   ``COMB (\(x,y,z). z) = SEL_3_3``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Q.SPEC_TAC(`x`,`x`)
    THEN SIMP_TAC std_ss 
          [COMB_def,SEL_3_3_def,FORALL_PROD,o_DEF,FUN_EQ_THM]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMP_SEL_CLAUSES =
 save_thm
  ("COMP_SEL_CLAUSES",
   LIST_CONJ
    [COMP_SEL_2_1,COMP_SEL_2_2,
     COMP_SEL_3_1,COMP_SEL_3_2,COMP_SEL_3_3]);

val SEL_2_1_CONCAT =
 store_thm
  ("SEL_2_1_CONCAT",
   ``SEL_2_1(inp1 <> inp2, out) = (out = inp1)``,
   RW_TAC std_ss [SEL_2_1_def,FUN_EQ_THM,BUS_CONCAT_def]);

val SEL_2_2_CONCAT =
 store_thm
  ("SEL_2_2_CONCAT",
   ``SEL_2_2(inp1 <> inp2, out) = (out = inp2)``,
   RW_TAC std_ss [SEL_2_2_def,FUN_EQ_THM,BUS_CONCAT_def]);

val SEL_3_1_CONCAT =
 store_thm
  ("SEL_3_1_CONCAT",
   ``SEL_3_1(inp1 <> (inp2 <> inp3), out) = (out = inp1)``,
   RW_TAC std_ss [SEL_3_1_def,FUN_EQ_THM,BUS_CONCAT_def]);

val SEL_3_2_CONCAT =
 store_thm
  ("SEL_3_2_CONCAT",
   ``SEL_3_2(inp1 <> (inp2 <> inp3), out) = (out = inp2)``,
   RW_TAC std_ss [SEL_3_2_def,FUN_EQ_THM,BUS_CONCAT_def])

val SEL_3_3_CONCAT =
 store_thm
  ("SEL_3_3_CONCAT",
   ``SEL_3_3(inp1 <> (inp2 <> inp3), out) = (out = inp3)``,
   RW_TAC std_ss [SEL_3_3_def,FUN_EQ_THM,BUS_CONCAT_def]);

val SEL_CONCAT_CLAUSES =
 save_thm
  ("SEL_CONCAT_CLAUSES",
   LIST_CONJ
    [SEL_2_1_CONCAT,SEL_2_2_CONCAT,
     SEL_3_1_CONCAT,SEL_3_2_CONCAT,SEL_3_3_CONCAT]);
******************************************************************************)

(*****************************************************************************)
(* Identitly device (i.e. piece of wire)                                     *)
(*****************************************************************************)
val COMB_ID =
 store_thm
  ("COMB_ID",
   ``COMB (\x. x) (inp,out) = (out = inp)``,
   RW_TAC std_ss [COMB_def,FUN_EQ_THM]);

(*****************************************************************************)
(* Constant combinational device                                             *)
(*****************************************************************************)
val CONSTANT_def =
 Define
  `CONSTANT c out = !t. out t = c`;

val COMB_CONSTANT_1 =
 store_thm
  ("COMB_CONSTANT_1",
   ``COMB (\x. c) (inp,out) = CONSTANT c out``,
   RW_TAC std_ss [COMB_def,CONSTANT_def]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMB_CONSTANT_2 =
 store_thm
  ("COMB_CONSTANT_2",
   ``COMB (\(x,y). c) (inp,out) = CONSTANT c out``,
   RW_TAC std_ss [COMB_def,CONSTANT_def]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val COMB_CONSTANT_3 =
 store_thm
  ("COMB_CONSTANT_3",
   ``COMB (\(x,y,z). c) (inp,out) = CONSTANT c out``,
   RW_TAC std_ss [COMB_def,CONSTANT_def]
    THEN GEN_BETA_TAC
    THEN PROVE_TAC[]);

val DEL_CONCAT =
 store_thm
  ("DEL_CONCAT",
   ``DEL(inp1 <> inp2, out1 <> out2) = DEL(inp1,out1) /\ DEL(inp2,out2)``,
   RW_TAC std_ss [DEL_THM,BUS_CONCAT_def]
    THEN PROVE_TAC[]);

val DFF_CONCAT =
 store_thm
  ("DFF_CONCAT",
   ``DFF(inp1 <> inp2, clk, out1 <> out2) = 
      DFF(inp1,clk,out1) /\ DFF(inp2,clk,out2)``,
   RW_TAC std_ss [DFF_def,BUS_CONCAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN Cases_on `POSEDGE clk (t + 1)`
    THEN RW_TAC std_ss []
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SPEC_ALL(el 2 thl)))
    THEN PROVE_TAC[PAIR_EQ]);

val MUX_CONCAT =
 store_thm
  ("MUX_CONCAT",
   ``MUX(sel, inp11 <> inp12, inp21 <> inp22, out1 <> out2) = 
      MUX(sel,inp11,inp21,out1) /\ MUX(sel,inp12,inp22,out2)``,
   RW_TAC std_ss [MUX_def,BUS_CONCAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN Cases_on `sel t`
    THEN RW_TAC std_ss []
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(SPEC_ALL(el 2 thl)))
    THEN PROVE_TAC[PAIR_EQ]);

val BUS_CONCAT_ELIM =
 store_thm
  ("BUS_CONCAT_ELIM",
   ``(\x1. P1 x1) <> (\x2. P2 x2) = \x. (P1 x, P2 x)``,
   RW_TAC std_ss [BUS_CONCAT_def,FUN_EQ_THM]);

val BUS_CONCAT_PAIR =
 store_thm
  ("BUS_CONCAT_PAIR",
   ``(f1 <> g1 = f2 <> g2) = (f1 = f2) /\ (g1 = g2)``,
   RW_TAC std_ss [BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

val BUS_CONCAT_o =
 store_thm
  ("BUS_CONCAT_o",
   ``(f <> g) o h = (f o h) <> (g o h)``,
   RW_TAC std_ss [BUS_CONCAT_def,FUN_EQ_THM]);

(*****************************************************************************)
(* Versions of POSEDGE_IMP, CALL, SELECT, FINISH, ATM, SEQ, PAR, ITE and REC *)
(* suitable for rewriting hardware combinatory expressions.                  *)
(*****************************************************************************)

val POSEDGE_IMP =
 store_thm
  ("POSEDGE_IMP",
   ``POSEDGE_IMP = 
      \(inp,out).
         ?c0 c1. DEL (inp,c0) /\ NOT (c0,c1) /\ AND (c1,inp,out)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,POSEDGE_IMP_def]);

val CALL =
 store_thm
  ("CALL",
   ``CALL = 
      \(load,inp,done,done_g,data_g,start_e,inp_e).
         ?c0 c1 start sel.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,CALL_def]);

val SELECT =
 store_thm
  ("SELECT",
   ``SELECT = 
      \(done_e,data_e,start_f,start_g).
         ?start' not_e.
           POSEDGE_IMP (done_e,start') /\ AND (start',data_e,start_f) /\
           NOT (data_e,not_e) /\ AND (not_e,start',start_g)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,SELECT_def]);

val FINISH =
 store_thm
  ("FINISH",
   ``FINISH = 
      \(done_e,done_f,done_g,done).
         ?c2 c3 c4.
           DEL (done_g,c3) /\ AND (done_g,c3,c4) /\
           AND (done_f,done_e,c2) /\ AND (c2,c4,done)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,FINISH_def]);

val ATM =
 store_thm
  ("ATM",
   ``ATM f = 
      \(load,inp,done,out).
       ?c0 c1.
         POSEDGE_IMP (load,c0) /\ NOT (c0,done) /\ COMB f (inp,c1) /\
         DEL (c1,out)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,ATM_def]);

val SEQ =
 store_thm
  ("SEQ",
   ``SEQ f g = 
      \(load,inp,done,out).
      ?not_c2 c0 c1 c2 data.
        NOT (c2,not_c2) /\ OR (not_c2,load,c0) /\ f (c0,inp,c1,data) /\
        g (c1,data,c2,out) /\ AND (c1,c2,done)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,SEQ_def]);

val PAR =
 store_thm
  ("PAR",
   ``PAR f g = 
      \(load,inp,done,out).
         ?c0 c1 start done' done'' data' data'' out' out''.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           f (start,inp,done',data') /\ g (start,inp,done'',data'') /\
           DFF (data',done',out') /\ DFF (data'',done'',out'') /\
           AND (done',done'',done) /\ (out = (\t. (out' t,out'' t)))``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,PAR_def]);

val ITE =
 store_thm
  ("ITE",
   ``ITE e f g = 
      \(load,inp,done,out).
         ?c0 c1 c2 start start' done_e data_e q not_e data_f data_g sel
            done_f done_g start_f start_g.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           e (start,inp,done_e,data_e) /\ POSEDGE_IMP (done_e,start') /\
           DFF (data_e,done_e,sel) /\ DFF (inp,start,q) /\
           AND (start',data_e,start_f) /\ NOT (data_e,not_e) /\
           AND (start',not_e,start_g) /\ f (start_f,q,done_f,data_f) /\
           g (start_g,q,done_g,data_g) /\ MUX (sel,data_f,data_g,out) /\
           AND (done_e,done_f,c2) /\ AND (c2,done_g,done)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,ITE_def]);

val REC =
 store_thm
  ("REC",
   ``REC e f g = 
      \(load,inp,done,out).
         ?done_g data_g start_e q done_e data_e start_f start_g inp_e
            done_f.
           CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
           DFF (inp_e,start_e,q) /\ e (start_e,inp_e,done_e,data_e) /\
           SELECT (done_e,data_e,start_f,start_g) /\
           f (start_f,q,done_f,out) /\ g (start_g,q,done_g,data_g) /\
           FINISH (done_e,done_f,done_g,done)``,
   RW_TAC std_ss [FUN_EQ_THM,FORALL_PROD,REC_def]);

(*****************************************************************************)
(* Temporal refinement using Melham's theory                                 *)
(*****************************************************************************)
val DEL_Del =
 store_thm
  ("DEL_Del",
   ``DEL(inp,out) = (out 0 = inp 0) /\ Del(inp,out)``,
   PROVE_TAC[DEL_THM,Del]);
     
val _ = export_theory();
