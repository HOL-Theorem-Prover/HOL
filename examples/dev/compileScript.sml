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
map load
 ["metisLib","composeTheory","devTheory","dffTheory"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory
     composeTheory devTheory dffTheory tempabsTheory metisLib;
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
     composeTheory dffTheory tempabsTheory devTheory;
val op by = BasicProvers.byA

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "compile"                                                *)
(*****************************************************************************)
val _ = new_theory "compile";
val _ = ParseExtras.temp_loose_equality()

(*****************************************************************************)
(* |- f ===> g = !x. f x ==> g x                                             *)
(*****************************************************************************)
val DEV_IMP_def =
 Define `DEV_IMP f g = !x. f x ==> g x`;

val _ = set_fixity "===>" (Infixr 451);
val _ = overload_on("===>", ``$DEV_IMP``);

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
(* Abstract on rising edge ("s at clk" analogous to PSL's "s@clk")           *)
(*****************************************************************************)
val _ = set_fixity "at" (Infixl 650);
val at_def =
 Define
  `$at s clk = s when Rise clk`;

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

val _ = set_fixity "<>" (Infixr 375);
val _ = overload_on ("<>", ``BUS_CONCAT``);

(*****************************************************************************)
(* Eliminate let-terms, preserving sharing                                   *)
(* (not currently used as COMB_SYNTH_CONV does the proof on-the-fly)         *)
(*****************************************************************************)
val COMB_LET =
 store_thm
  ("COMB_LET",
   ``COMB (\x. (let y = f1 x in f2(x,y))) (inp,out)
     =
    ?v. COMB f1 (inp,v) /\ COMB f2 (inp <> v,out)``,
   EQ_TAC
    THEN RW_TAC std_ss [COMB_def,BUS_CONCAT_def,LET_DEF]
    THENL
     [Q.EXISTS_TAC `\t. f1 (inp t)`
       THEN RW_TAC std_ss [],
      PROVE_TAC[]]);

(*****************************************************************************)
(* Identitly device (i.e. piece of wire)                                     *)
(*****************************************************************************)
val COMB_ID =
 store_thm
  ("COMB_ID",
   ``COMB (\x. x) (inp,out) = (out = inp)``,
   RW_TAC std_ss [COMB_def,FUN_EQ_THM]);

val COMB_IN_SPLIT =
 store_thm
  ("COMB_IN_SPLIT",
   ``COMB P (inp1 <> inp2, out) =
      (out = P o (inp1 <> inp2 ))``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

(* COMB_CONCAT_SPLIT  *)

val COMB_OUT_SPLIT =
 store_thm
  ("COMB_OUT_SPLIT",
   ``COMB (f <> g) (inp, out1 <> out2) =
      COMB f (inp,out1) /\ COMB g (inp,out2)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,FUN_EQ_THM]
    THEN PROVE_TAC[]);

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

val COMB_NOT =
 store_thm
  ("COMB_NOT",
   ``COMB $~ (inp,out) = NOT(inp,out)``,
   RW_TAC std_ss [COMB_def,NOT_def]);

val COMB_AND =
 store_thm
  ("COMB_AND",
   ``COMB (UNCURRY $/\) (in1<>in2,out) = AND(in1,in2,out)``,
   RW_TAC std_ss [COMB_def,AND_def,BUS_CONCAT_def]);

val AND_at =
 store_thm
  ("AND_at",
   ``AND(in1,in2,out)
     ==>
     AND(in1 at clk,in2 at clk,out at clk)``,
   RW_TAC std_ss [AND_def,at_def,when]);

val NOT_at =
 store_thm
  ("NOT_at",
   ``NOT(inp,out) ==> NOT(inp at clk,out at clk)``,
   RW_TAC std_ss [NOT_def,at_def,when]);

val COMB_OR =
 store_thm
  ("COMB_OR",
   ``COMB (UNCURRY $\/) (in1<>in2,out) = OR(in1,in2,out)``,
   RW_TAC std_ss [COMB_def,OR_def,BUS_CONCAT_def]);

val COMB_MUX =
 store_thm
  ("COMB_MUX",
   ``COMB
      (\(sw,in1,in2). if sw then in1 else in2)
      (in1<>in2<>in3,out) =
     MUX(in1,in2,in3,out)``,
   RW_TAC std_ss [COMB_def,MUX_def,BUS_CONCAT_def]);

val OR_at =
 store_thm
  ("OR_at",
   ``OR(in1,in2,out)
     ==>
     OR(in1 at clk,in2 at clk,out at clk)``,
   RW_TAC std_ss [OR_def,at_def,when]);

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

val BUS_SPLIT =
 store_thm
  ("BUS_SPLIT",
   ``!v. ?v1 v2. v = v1 <> v2``,
   RW_TAC std_ss [BUS_CONCAT_def,FUN_EQ_THM]
    THEN Q.EXISTS_TAC `FST o v`
    THEN Q.EXISTS_TAC `SND o v`
    THEN RW_TAC std_ss []);

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

Theorem DEL_CONCAT:
   DEL(inp1 <> inp2, out1 <> out2) = DEL(inp1,out1) /\ DEL(inp2,out2)
Proof
  RW_TAC std_ss [DEL_def,BUS_CONCAT_def] THEN PROVE_TAC[]
QED

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

val COMB_COND_CONCAT =
 store_thm
  ("COMB_COND_CONCAT",
   ``COMB (\(sw,in1,in2). (if sw then in1 else in2))
       (sel <> (inp11 <> inp12) <> inp21 <> inp22,out1 <> out2) =
     COMB (\(sw,in1,in2). (if sw then in1 else in2))
       (sel <> inp11 <> inp21,out1) /\
     COMB (\(sw,in1,in2). (if sw then in1 else in2))
       (sel <> inp12 <> inp22,out2)``,
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def]
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
         ?c0 c1. DELT (inp,c0) /\ NOT (c0,c1) /\ AND (c1,inp,out)``,
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
   ``DEL = Del``,
   RW_TAC std_ss [FUN_EQ_THM]
    THEN Cases_on `x`
    THEN RW_TAC std_ss [DEL_def,Del]);

(* Sort of transparent latch

        sw       d
        |        |        |------|
        |        |        |      |
        |        |     |-----|   |
        |        |     | DEL |   |
        |        |     |-----|   |
        |        |        |      |
        |        |      c |      |
        |        |        |      |
      |---------------------|    |
      |         MUX         |    |
      |---------------------|    |
                 |               |
                 +---------------|
                 |
                 q
*)

val LATCH_def =
 Define
  `LATCH(sw,d,q) = ?c. MUX(sw,d,c,q) /\ DEL(q,c)`;

val LATCH_THM =
 store_thm
  ("LATCH_THM",
   ``LATCH(sw,d,q) =
      (!t. sw t ==> (q t = d t)) /\ (!t. ~(sw(t+1)) ==> (q(t+1) = q t))``,
   RW_TAC std_ss [LATCH_def,MUX_def,DEL_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN RW_TAC std_ss []
    THEN Q.EXISTS_TAC `\t. if t=0 then q 0 else q(t-1)`
    THEN BETA_TAC
    THEN RW_TAC arith_ss []
    THEN `(t-1)+1 = t` by DECIDE_TAC
    THEN PROVE_TAC[]);

val LATCH_IMP =
 store_thm
  ("LATCH_IMP",
   ``LATCH(sw,d,q) ==> !t. q(t+1) = if sw(t+1) then d(t+1) else q t``,
   RW_TAC std_ss [LATCH_def,MUX_def,DELF_def,DEL_def]
    THEN PROVE_TAC[]);

(* Implementation of DFF using LATCH

          clk          d          q
           |           |          |
           |           |          |
    |-------------|    |          |
    | POSEDGE_IMP |    |          |
    |-------------|    |          |
           |           |          |
        sw |           |          |
           |           |          |
         |--------------------------|
         |           LATCH          |
         |--------------------------|
                      |
                      |
                      q
*)

val DFF_IMP_def =
 Define
  `DFF_IMP(d,clk,q) = ?sw. POSEDGE_IMP(clk,sw) /\ LATCH(sw,d,q)`;

val DFF_IMP_THM =
 store_thm
  ("DFF_IMP_THM",
   ``!p. DFF_IMP p ==> DFF p``,
   Ho_Rewrite.REWRITE_TAC[FORALL_PROD]
    THEN RW_TAC std_ss [DFF_IMP_def,DFF_def,LATCH_THM]
    THEN IMP_RES_TAC POSEDGE_IMPL
    THEN PROVE_TAC[]);

val Inf_Rise_POSEDGE =
 store_thm
  ("Inf_Rise_POSEDGE",
   ``Inf(Rise sig) = Inf(POSEDGE sig)``,
   RW_TAC std_ss [Rise,POSEDGE_def,tempabsTheory.Inf_thm2]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THENL
     [`?t'. t <= t' /\ ~sig t' /\ sig (t' + 1)` by PROVE_TAC[]
       THEN Q.EXISTS_TAC `t'+1`
       THEN RW_TAC arith_ss [],
      `?t'. (t+1) <= t' /\ ~(t' = 0) /\ ~sig (t' - 1) /\ sig t'` by PROVE_TAC[]
       THEN Q.EXISTS_TAC `t'-1`
       THEN RW_TAC arith_ss []]);

(*****************************************************************************)
(* Flip-flop that powers up outputting T                                     *)
(*****************************************************************************)
val DtypeT_def =
 Define `DtypeT(ck,d,q) = (q 0 = T) /\ Dtype(ck,d,q)`;

(*****************************************************************************)
(* Flip-flop that powers up outputting F                                     *)
(*****************************************************************************)
val DtypeF_def =
 Define `DtypeF(ck,d,q) = (q 0 = F) /\ Dtype(ck,d,q)`;

(*****************************************************************************)
(* General Dtype parameterised on initial state                              *)
(*****************************************************************************)
val DTYPE_def =
 Define `DTYPE v (ck,d,q) = (q 0 = v) /\ Dtype(ck,d,q)`;

(*****************************************************************************)
(* Compute output signal of DTYPE                                            *)
(*****************************************************************************)
val DTYPE_FUN_def =
 Define
  `(DTYPE_FUN v ck d 0 = v)
   /\
   (DTYPE_FUN v ck d (SUC t) = if Rise ck t then d t else DTYPE_FUN v ck d t)`;

(*****************************************************************************)
(* Delete a DTYPE if its output isn't connected to anything                  *)
(*****************************************************************************)
val DTYPE_ELIM =
 store_thm
  ("DTYPE_ELIM",
   ``(?q. DTYPE v (ck,d,q)) = T``,
   RW_TAC std_ss [DTYPE_def,Dtype]
    THEN Q.EXISTS_TAC `DTYPE_FUN v ck d`
    THEN RW_TAC std_ss [DTYPE_FUN_def,GSYM ADD1]);

val at_CONCAT =
 store_thm
  ("at_CONCAT",
   ``(s1 at clk) <> (s2 at clk) = (s1 <> s2) at clk``,
   RW_TAC std_ss [BUS_CONCAT_def,at_def,when,o_DEF]);

(*****************************************************************************)
(* Clock has an infinite number of rising edges                              *)
(*****************************************************************************)
val InfRise_def =
 Define `InfRise clk = Inf(Rise clk)`;

(* Old version
val DEL_IMP =
 store_thm
  ("DEL_IMP",
   ``InfRise clk ==> !d q. Dtype(clk,d,q) ==> DEL(d at clk, q at clk)``,
   PROVE_TAC[Dtype_correct,DEL_def,Del,InfRise_def,at_def]);
*)

val DEL_IMP =
 store_thm
  ("DEL_IMP",
   ``InfRise clk ==> !d q. (?v. DTYPE v (clk,d,q)) ==> DEL(d at clk, q at clk)``,
   METIS_TAC[DTYPE_def,Dtype_correct,DEL_def,Del,InfRise_def,at_def]);

val Dtype0 =
 store_thm
  ("Dtype0",
   ``Dtype (clk,d,q) /\ Istimeof 0 (Rise clk) t
     ==>
     !t'. t' <= t ==> (q t' = q 0)``,
   RW_TAC arith_ss [Dtype,Istimeof]
    THEN Induct_on `t'`
    THEN RW_TAC arith_ss [ADD1]);

val IstimeofTimeof0 =
 store_thm
  ("IstimeofTimeof0",
   ``Istimeof 0 sig t ==> (t = Timeof sig 0)``,
   RW_TAC std_ss [Istimeof,Timeof]
    THEN `!u. sig u /\ (!t'. t' < u ==> ~sig t') = (u = t)` by ALL_TAC
    THENL
     [Induct_on `t`
       THEN RW_TAC arith_ss []
       THENL
        [Cases_on `u=0`
          THEN RW_TAC arith_ss []
          THEN `0 < u` by DECIDE_TAC
          THEN PROVE_TAC[],
         Cases_on `u = SUC t`
          THEN RW_TAC arith_ss []
          THEN Cases_on `u < SUC t`
          THENL
           [PROVE_TAC[],
            `SUC t < u` by DECIDE_TAC
             THEN PROVE_TAC[]]],
      METIS_TAC
       [BETA_RULE(Q.ISPEC `\t. sig t /\ !t'. t' < t ==> ~sig t'` SELECT_UNIQUE)]]);

(* Old versions
val DELT_IMP =
 store_thm
  ("DELT_IMP",
   ``InfRise clk ==> !d q. DtypeT(clk,d,q) ==> DELT(d at clk, q at clk)``,
   RW_TAC std_ss[PURE_REWRITE_RULE[GSYM DEL_def]DELT_def,
                 Del,DtypeT_def,DEL_IMP,Istimeof_thm7,InfRise_def]
    THEN RW_TAC std_ss [at_def,when,Timeof]
    THEN `?t. Istimeof 0 (Rise clk) t` by PROVE_TAC[]
    THEN IMP_RES_TAC Dtype0
    THEN RW_TAC std_ss [GSYM Timeof]
    THEN METIS_TAC[IstimeofTimeof0,DECIDE``t <= t``]);

val DELF_IMP =
 store_thm
  ("DELF_IMP",
   ``InfRise clk ==> !d q. DtypeF(clk,d,q) ==> DELF(d at clk, q at clk)``,
   RW_TAC std_ss[PURE_REWRITE_RULE[GSYM DEL_def]DELF_def,
                 Del,DtypeF_def,DEL_IMP,Istimeof_thm7,InfRise_def]
    THEN RW_TAC std_ss [at_def,when,Timeof]
    THEN `?t. Istimeof 0 (Rise clk) t` by PROVE_TAC[]
    THEN IMP_RES_TAC Dtype0
    THEN RW_TAC std_ss [GSYM Timeof]
    THEN METIS_TAC[IstimeofTimeof0,DECIDE``t <= t``]);
*)

val DELT_IMP =
 store_thm
  ("DELT_IMP",
   ``InfRise clk ==> !d q. DTYPE T (clk,d,q) ==> DELT(d at clk, q at clk)``,
   RW_TAC std_ss[PURE_REWRITE_RULE[GSYM DEL_def]DELT_def,
                 Del,DTYPE_def,DEL_IMP,Istimeof_thm7,InfRise_def]
    THEN RW_TAC std_ss [at_def,when,Timeof]
    THEN `?t. Istimeof 0 (Rise clk) t` by PROVE_TAC[]
    THEN IMP_RES_TAC Dtype0
    THEN RW_TAC std_ss [GSYM Timeof]
    THEN METIS_TAC[IstimeofTimeof0,DECIDE``t <= t``]);

val DELF_IMP =
 store_thm
  ("DELF_IMP",
   ``InfRise clk ==> !d q. DTYPE F (clk,d,q) ==> DELF(d at clk, q at clk)``,
   RW_TAC std_ss[PURE_REWRITE_RULE[GSYM DEL_def]DELF_def,
                 Del,DTYPE_def,DEL_IMP,Istimeof_thm7,InfRise_def]
    THEN RW_TAC std_ss [at_def,when,Timeof]
    THEN `?t. Istimeof 0 (Rise clk) t` by PROVE_TAC[]
    THEN IMP_RES_TAC Dtype0
    THEN RW_TAC std_ss [GSYM Timeof]
    THEN METIS_TAC[IstimeofTimeof0,DECIDE``t <= t``]);

val TRUE_at =
 store_thm
  ("TRUE_at",
   ``TRUE out ==> TRUE(out at clk)``,
   RW_TAC std_ss [TRUE_def,at_def,when]);

val FALSE_at =
 store_thm
  ("FALSE_at",
   ``FALSE out ==> FALSE(out at clk)``,
   RW_TAC std_ss [FALSE_def,at_def,when]);

val CONSTANT_at =
 store_thm
  ("CONSTANT_at",
   ``CONSTANT c out ==> CONSTANT c (out at clk)``,
   RW_TAC std_ss [CONSTANT_def,at_def,when]);

val COMB_at =
 store_thm
  ("COMB_at",
   ``COMB f (inp,out) ==> COMB f (inp at clk,out at clk)``,
   RW_TAC std_ss [COMB_def,at_def,when]);

val MUX_at =
 store_thm
  ("MUX_at",
   ``MUX(sw,in1,in2,out)
     ==>
     MUX(sw at clk,in1 at clk,in2 at clk,out at clk)``,
   RW_TAC std_ss [MUX_def,at_def,when]);

val UNWIND_THM =
 store_thm
  ("UNWIND_THM",
   ``!P x y. (x = y) /\ P x = (x = y) /\ P y``,
   PROVE_TAC[]);

(*---------------------------------------------------------------------------*)

val K_INTRO_THM = Q.store_thm
  ("K_INTRO_THM",
   `!u. (\v.u) = K u`,RW_TAC std_ss [FUN_EQ_THM]);

val I_INTRO_THM = Q.store_thm
  ("I_INTRO_THM",
   `(\v.v) = I`,RW_TAC std_ss [FUN_EQ_THM]);

val _ = Parse.reveal "C";

val thlist =
 map (C (curry Q.prove)
        (RW_TAC std_ss [FUN_EQ_THM,BUS_CONCAT_def,combinTheory.C_THM]))
   [`!x y. K x <> K y = K (x,y)`,
    `!x y. (\v.x) <> (\v.y) = K (x,y)`,
    `!u. I <> K u = C ($,) u`,
    `I<>I = S $, I`];

val BUS_CONCAT_LIFTERS = save_thm
  ("BUS_CONCAT_LIFTERS",LIST_CONJ thlist);

val BUS_CONCAT_LIFTERS1 = Q.store_thm
   ("BUS_CONCAT_LIFTERS1",
    `(!f a. f <> K a = C ($, o f) a) /\
     (!f a. K a <> f = ($, a) o f)`,
   RW_TAC std_ss [FUN_EQ_THM,BUS_CONCAT_def]);


val Let_def = Define `Let f1 f2 = \x:'a. let v:'c = f1(x) in f2(x,v):'b`;

val Let =
 store_thm
  ("Let",
   ``Let f1 f2 = Seq (Par (\x.x) f1) f2``,
   RW_TAC std_ss [Let_def,Seq_def,Par_def,LET_DEF]);

val _ = export_theory();
