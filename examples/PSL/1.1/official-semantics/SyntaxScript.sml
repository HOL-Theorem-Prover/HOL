(*****************************************************************************)
(* Create "SyntaxTheory" representing abstract syntax of PSL Version 1.1     *)
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
* Start a new theory called SyntaxTheory
******************************************************************************)
val _ = new_theory "Syntax";

(******************************************************************************
* Boolean expressions
******************************************************************************)
val bexp_def =
 Hol_datatype
  `bexp = B_PROP   of 'a                         (* atomic proposition       *)
        | B_TRUE                                 (* true                     *)
        | B_FALSE                                (* false                    *)
        | B_NOT of bexp                          (* negation                 *)
        | B_AND of bexp # bexp`;                 (* conjunction              *)

(******************************************************************************
* Sequential Extended Regular Expressions (SEREs)
******************************************************************************)
val sere_def =
 Hol_datatype
  `sere = S_BOOL        of 'a bexp               (* boolean expression       *)
        | S_CAT         of sere # sere           (* r1 ;  r2                 *)
        | S_FUSION      of sere # sere           (* r1 :  r2                 *)
        | S_OR          of sere # sere           (* r1 |  r2                 *)
        | S_AND         of sere # sere           (* r1 && r2                 *)
        | S_EMPTY                                (* [*0]                     *)
        | S_REPEAT      of sere                  (* r[*]                     *)
        | S_CLOCK       of sere # 'a bexp`;      (* r@c                      *)

(******************************************************************************
* Formulas of Sugar Foundation Language (FL)
******************************************************************************)
val fl_def =
 Hol_datatype
  `fl = F_STRONG_BOOL  of 'a bexp                (* b!                       *)
      | F_WEAK_BOOL    of 'a bexp                (* b                        *)
      | F_NOT          of fl                     (* not f                    *)
      | F_AND          of fl # fl                (* f1 and f2                *)
      | F_STRONG_SERE  of 'a sere                (* r!                       *)
      | F_WEAK_SERE    of 'a sere                (* r                        *)
      | F_NEXT         of fl                     (* X! f                     *)
      | F_UNTIL        of fl # fl                (* [f1 U f2]                *)
      | F_ABORT        of fl # 'a bexp           (* f abort b                *)
      | F_CLOCK        of fl # 'a bexp           (* f@b                      *)
      | F_SUFFIX_IMP   of 'a sere # fl`;         (* r |-> f                  *)

(******************************************************************************
* Formulas of Sugar Optional Branching Extension (OBE)
******************************************************************************)
val obe_def =
 Hol_datatype
  `obe = O_BOOL        of 'a bexp                (* boolean expression       *)
       | O_NOT         of obe                    (* not f                    *)
       | O_AND         of obe # obe              (* f1 and f2                *)
       | O_EX          of obe                    (* EX f                     *)
       | O_EU          of obe # obe              (* E[f1 U f2]               *)
       | O_EG          of obe`;                  (* EG f                     *)

val _ = export_theory();








