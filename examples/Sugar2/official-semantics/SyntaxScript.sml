
(*****************************************************************************)
(* IPSL is an attempt to make Accellera PSL (Sugar) closer to ITL by         *)
(* defining SEREs as formulas via a chop operator.                           *)
(*                                                                           *)
(* Create "SyntaxTheory" representing abstract syntax of IPSL                *)
(*                                                                           *)
(* Created Thu Feb  6 10:01:51 GMT 2003                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Version of Define that doesn't add to the EVAL compset
******************************************************************************)
val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;w

(******************************************************************************
* Start a new theory called SyntaxTheory
******************************************************************************)
val _ = new_theory "Syntax";
   
(******************************************************************************
* Boolean expressions
******************************************************************************)
val bexp_def =
 Hol_datatype
  `bexp = B_PROP   of 'a                         (* atomic proposition       *)
        | B_NOT    of bexp                       (* negation                 *)
        | B_AND    of bexp # bexp`;              (* conjunction              *)

(******************************************************************************
* Definition of disjunction
******************************************************************************)

val B_OR_def =
 pureDefine `B_OR(b1,b2) = B_NOT(B_AND(B_NOT b1, B_NOT b2))`;

(******************************************************************************
* Definition of truth
******************************************************************************)

val B_TRUE_def =
 pureDefine `B_TRUE = B_OR(B_PROP ARB, B_NOT(B_PROP ARB))`;

(******************************************************************************
* Definition of falsity
******************************************************************************)

val B_FALSE_def =
 pureDefine `B_FALSE = B_NOT B_TRUE`;

(******************************************************************************
* Sugar Extended Regular Expressions (SEREs) 
******************************************************************************)
val sere_def =
 Hol_datatype
  `sere = S_BOOL        of 'a bexp               (* boolean expression       *)
        | S_CAT         of sere # sere           (* r1 ;  r2                 *)
        | S_FUSION      of sere # sere           (* r1 :  r2                 *)
        | S_OR          of sere # sere           (* r1 |  r2                 *)
        | S_AND         of sere # sere           (* r1 && r2                 *)
        | S_REPEAT      of sere                  (* r[*]                     *)
        | S_CLOCK       of sere # 'a bexp`;      (* r@clk                    *)

(******************************************************************************
* Formulas of Sugar Foundation Language (FL)
******************************************************************************)
val fl_def =
 Hol_datatype
  `fl = F_BOOL         of 'a bexp                (* boolean expression       *)
      | F_NOT          of fl                     (* \neg f                   *)
      | F_AND          of fl # fl                (* f1 \wedge f2             *)
      | F_NEXT         of fl                     (* X! f                     *)
      | F_UNTIL        of fl # fl                (* [f1 U f2]                *)
      | F_SUFFIX_IMP   of 'a sere # fl           (* {r}(f)                   *)
      | F_STRONG_IMP   of 'a sere # 'a sere      (* {r1} |-> {r2}!           *)
      | F_WEAK_IMP     of 'a sere # 'a sere      (* {r1} |-> {r2}            *)
      | F_ABORT        of fl # 'a bexp           (* f abort b                *)
      | F_STRONG_CLOCK of fl # 'a bexp`;         (* f@clk!                   *)

(******************************************************************************
* Formulas of Sugar Optional Branching Extension (OBE)
******************************************************************************)
val obe_def =
 Hol_datatype
  `obe = O_BOOL        of 'a bexp                (* boolean expression       *)
       | O_NOT         of obe                    (* \neg f                   *)
       | O_AND         of obe # obe              (* f1 \wedge f2             *)
       | O_EX          of obe                    (* EX f                     *)
       | O_EU          of obe # obe              (* E[f1 U f2]               *)
       | O_EG          of obe`;                  (* EG f                     *)

val _ = export_theory();







