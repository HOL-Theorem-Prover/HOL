(*****************************************************************************)
(* Create "SyntaxTheory" representing abstract syntax of PSL Version 1.1     *)
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
   bexp = B_PROP   'a                            (* atomic proposition       *)
        | B_TRUE                                 (* true                     *)
        | B_FALSE                                (* false                    *)
        | B_NOT    bexp                          (* negation                 *)
        | B_AND    (bexp # bexp)                 (* conjunction              *)
End

(******************************************************************************
* Sequential Extended Regular Expressions (SEREs)
******************************************************************************)
Datatype:
   sere = S_BOOL           ('a bexp)             (* boolean expression       *)
        | S_CAT            (sere # sere)         (* r1 ;  r2                 *)
        | S_FUSION         (sere # sere)         (* r1 :  r2                 *)
        | S_OR             (sere # sere)         (* r1 |  r2                 *)
        | S_AND            (sere # sere)         (* r1 && r2                 *)
        | S_EMPTY                                (* [*0]                     *)
        | S_REPEAT         sere                  (* r[*]                     *)
        | S_CLOCK          (sere # 'a bexp)      (* r@c                      *)
End

(******************************************************************************
* Formulas of Sugar Foundation Language (FL)
******************************************************************************)
Datatype:
   fl = F_STRONG_BOOL     ('a bexp)              (* b!                       *)
      | F_WEAK_BOOL       ('a bexp)              (* b                        *)
      | F_NOT             fl                     (* not f                    *)
      | F_AND             (fl # fl)              (* f1 and f2                *)
      | F_STRONG_SERE     ('a sere)              (* r!                       *)
      | F_WEAK_SERE       ('a sere)              (* r                        *)
      | F_NEXT            fl                     (* X! f                     *)
      | F_UNTIL           (fl # fl)              (* [f1 U f2]                *)
      | F_ABORT           (fl # 'a bexp)         (* f abort b                *)
      | F_CLOCK           (fl # 'a bexp)         (* f@b                      *)
      | F_SUFFIX_IMP      ('a sere # fl)         (* r |-> f                  *)
End

(******************************************************************************
* Formulas of Sugar Optional Branching Extension (OBE)
******************************************************************************)
Datatype:
   obe = O_BOOL           ('a bexp)              (* boolean expression       *)
       | O_NOT            obe                    (* not f                    *)
       | O_AND            (obe # obe)            (* f1 and f2                *)
       | O_EX             obe                    (* EX f                     *)
       | O_EU             (obe # obe)            (* E[f1 U f2]               *)
       | O_EG             obe                    (* EG f                     *)
End
