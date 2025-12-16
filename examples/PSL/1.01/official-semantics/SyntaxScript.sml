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
   bexp = B_PROP    'a                         (* atomic proposition       *)
        | B_NOT     bexp                       (* negation                 *)
        | B_AND     (bexp # bexp)              (* conjunction              *)
End

(****************************************************************************** *)
(* * Sugar Extended Regular Expressions (SEREs) *)
(* ******************************************************************************)
Datatype:
   sere = S_BOOL         ('a bexp)             (* boolean expression       *)
        | S_CAT          (sere # sere)         (* r1 ;  r2                 *)
        | S_FUSION       (sere # sere)         (* r1 :  r2                 *)
        | S_OR           (sere # sere)         (* r1 |  r2                 *)
        | S_AND          (sere # sere)         (* r1 && r2                 *)
        | S_REPEAT       sere                  (* r[*]                     *)
        | S_CLOCK        (sere # 'a bexp)      (* r@clk                    *)
End

(****************************************************************************** *)
(* * Formulas of Sugar Foundation Language (FL) *)
(* ******************************************************************************)
Datatype:
   fl = F_BOOL          ('a bexp)              (* boolean expression       *)
      | F_NOT           fl                     (* \neg f                   *)
      | F_AND           (fl # fl)              (* f1 \wedge f2             *)
      | F_NEXT          fl                     (* X! f                     *)
      | F_UNTIL         (fl # fl)              (* [f1 U f2]                *)
      | F_SUFFIX_IMP    ('a sere # fl)         (* {r}(f)                   *)
      | F_STRONG_IMP    ('a sere # 'a sere)    (* {r1} |-> {r2}!           *)
      | F_WEAK_IMP      ('a sere # 'a sere)    (* {r1} |-> {r2}            *)
      | F_ABORT         (fl # 'a bexp)         (* f abort b                *)
      | F_STRONG_CLOCK  (fl # 'a bexp)         (* f@clk!                   *)
End

(****************************************************************************** *)
(* * Formulas of Sugar Optional Branching Extension (OBE) *)
(* ******************************************************************************)
Datatype:
   obe = O_BOOL         ('a bexp)              (* boolean expression       *)
       | O_NOT          obe                    (* \neg f                   *)
       | O_AND          (obe # obe)            (* f1 \wedge f2             *)
       | O_EX           obe                    (* EX f                     *)
       | O_EU           (obe # obe)            (* E[f1 U f2]               *)
       | O_EG           obe                    (* EG f                     *)
End
