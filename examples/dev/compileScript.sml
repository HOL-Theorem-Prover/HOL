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
map load  ["metisLib","composeTheory","devTheory"];
open arithmeticTheory pairLib pairTheory PairRules combinTheory 
     composeTheory devTheory metisLib;
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
     composeTheory devTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "compile"                                                *)
(*****************************************************************************)
val _ = new_theory "compile";

(*****************************************************************************)
(* |- f ===> g = !x. f x ==> g x                                             *)
(*****************************************************************************)
val _ = set_fixity "===>" (Infixr 550);
val DEV_IMP_def =
 xDefine "DEV_IMP" `$===> f g = !x. f x ==> g x`;

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

(*---------------------------------------------------------------------------*)
(* Tag constant for the measure function. Used infix.                        *)
(*---------------------------------------------------------------------------*)

val _ = new_constant ("measuring", bool --> alpha --> bool);
val _ = add_infix ("measuring", 90, NONASSOC);

val _ = export_theory();
