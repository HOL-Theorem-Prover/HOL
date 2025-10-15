(*****************************************************************************)
(* Create "SyntaxTheory" representing abstract syntax of PSL                 *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

Theory Syntax

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Boolean expressions
******************************************************************************)
Datatype:
   bexp = B_PROP   of 'a                         (* atomic proposition       *)
        | B_NOT    of bexp                       (* negation                 *)
        | B_AND    of bexp # bexp                (* conjunction              *)
End

(******************************************************************************
* Sugar Extended Regular Expressions (SEREs)
******************************************************************************)
Datatype:
   sere = S_BOOL        of 'a bexp               (* boolean expression       *)
        | S_CAT         of sere # sere           (* r1 ;  r2                 *)
        | S_FUSION      of sere # sere           (* r1 :  r2                 *)
        | S_OR          of sere # sere           (* r1 |  r2                 *)
        | S_AND         of sere # sere           (* r1 && r2                 *)
        | S_REPEAT      of sere                  (* r[*]                     *)
        | S_CLOCK       of sere # 'a bexp        (* r@clk                    *)
End

(******************************************************************************
* Formulas of Sugar Foundation Language (FL)
******************************************************************************)
Datatype:
   fl = F_BOOL         of 'a bexp                (* boolean expression       *)
      | F_NOT          of fl                     (* \neg f                   *)
      | F_AND          of fl # fl                (* f1 \wedge f2             *)
      | F_NEXT         of fl                     (* X! f                     *)
      | F_UNTIL        of fl # fl                (* [f1 U f2]                *)
      | F_SUFFIX_IMP   of 'a sere # fl           (* {r}(f)                   *)
      | F_STRONG_IMP   of 'a sere # 'a sere      (* {r1} |-> {r2}!           *)
      | F_WEAK_IMP     of 'a sere # 'a sere      (* {r1} |-> {r2}            *)
      | F_ABORT        of fl # 'a bexp           (* f abort b                *)
      | F_STRONG_CLOCK of fl # 'a bexp           (* f@clk!                   *)
End

(******************************************************************************
* Formulas of Sugar Optional Branching Extension (OBE)
******************************************************************************)
Datatype:
   obe = O_BOOL        of 'a bexp                (* boolean expression       *)
       | O_NOT         of obe                    (* \neg f                   *)
       | O_AND         of obe # obe              (* f1 \wedge f2             *)
       | O_EX          of obe                    (* EX f                     *)
       | O_EU          of obe # obe              (* E[f1 U f2]               *)
       | O_EG          of obe                    (* EG f                     *)
End
