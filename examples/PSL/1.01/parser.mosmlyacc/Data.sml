
(*****************************************************************************)
(* Data.sml  -- the abstract syntax datatype for PSL/Sugar                   *)
(*****************************************************************************)


(******************************************************************************
* Boolean expressions
******************************************************************************)
datatype bexp =
    B_PROP of string                              (* atomic proposition      *)
  | B_NOT  of bexp                                (* negation                *)
  | B_AND  of bexp * bexp                         (* conjunction             *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | B_OR   of bexp * bexp                         (* disjunction             *)
  | B_IMP  of bexp * bexp                         (* implication             *)
  | B_IFF  of bexp * bexp                         (* logical equivalence     *)
  | B_TRUE                                        (* T                       *)
  | B_FALSE                                       (* F                       *)
;

(******************************************************************************
* Specification of an iteration number or range (Count of LRM A.3.6)
******************************************************************************)
type range = int * int option;

(******************************************************************************
* Sequential Extended Regular Expressions (SEREs)
******************************************************************************)
datatype sere =
    S_BOOL               of bexp                  (* boolean expression      *)
  | S_CAT                of sere * sere           (* r1 ;  r2                *)
  | S_FUSION             of sere * sere           (* r1 :  r2                *)
  | S_OR                 of sere * sere           (* r1 |  r2                *)
  | S_AND                of sere * sere           (* r1 && r2                *)
  | S_REPEAT             of sere                  (* r[*]                    *)
  | S_CLOCK              of sere * bexp           (* r@clk                   *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | S_FLEX_AND           of sere * sere           (* r1 &  r2                *)
  | S_RANGE_REPEAT       of sere * range          (* r[* i]                  *)
  | S_NON_ZERO_REPEAT    of sere                  (* r[+]                    *)
  | S_RANGE_EQ_REPEAT    of bexp * range          (* r[= i]                  *)
  | S_RANGE_GOTO_REPEAT  of bexp * range          (* r[-> i]                 *)
;

(******************************************************************************
* Formulas of the Foundation Language (FL)
******************************************************************************)
datatype fl =
    F_BOOL              of bexp                   (* boolean expression      *)
  | F_NOT               of fl                     (* \neg f                  *)
  | F_AND               of fl * fl                (* f1 \wedge f2            *)
  | F_STRONG_X          of fl                     (* X! f                    *)
  | F_U                 of fl * fl                (* [f1 U f2]               *)
  | F_SUFFIX_IMP        of sere * fl              (* {r}(f)                  *)
  | F_STRONG_IMP        of sere * sere            (* {r1} |-> {r2}!          *)
  | F_WEAK_IMP          of sere * sere            (* {r1} |-> {r2}           *)
  | F_ABORT             of fl * bexp              (* f abort b               *)
  | F_STRONG_CLOCK      of fl * bexp              (* f@clk!                  *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | F_WEAK_CLOCK        of fl * bexp              (* f@clk                   *)
  | F_OR                of fl * fl                (* f1 \vee f2              *)
  | F_IMP               of fl * fl                (* f1 \rightarrow f2       *)
  | F_IFF               of fl * fl                (* f1 \leftrightarrow f2   *)
  | F_WEAK_X            of fl                     (* X f                     *)
  | F_F                 of fl                     (* F f                     *)
  | F_G                 of fl                     (* G f                     *)
  | F_W                 of fl * fl                (* [f1 W f2]               *)
  | F_ALWAYS            of fl                     (* always f                *)
  | F_NEVER             of fl                     (* never f                 *)
  | F_WEAK_NEXT         of fl                     (* next f                  *)
  | F_STRONG_NEXT       of fl                     (* next! f                 *)
  | F_STRONG_EVENTUALLY of fl                     (* next! f                 *)
  | F_STRONG_UNTIL      of fl * fl                (* [f1 until! f2]          *)
  | F_WEAK_UNTIL        of fl * fl                (* [f1 until f2]           *)
  | F_STRONG_UNTIL_INC  of fl * fl                (* [f1 until!_ f2]         *)
  | F_WEAK_UNTIL_INC    of fl * fl                (* [f1 until_ f2]          *)
  | F_STRONG_BEFORE     of fl * fl                (* [f1 before! f2]         *)
  | F_WEAK_BEFORE       of fl * fl                (* [f1 before f2]          *)
  | F_STRONG_BEFORE_INC of fl * fl                (* [f1 before!_ f2]        *)
  | F_WEAK_BEFORE_INC   of fl * fl                (* [f1 before_ f2]         *)
  | F_NUM_WEAK_X        of int * fl               (* X[n](f)                 *)
  | F_NUM_STRONG_X      of int * fl               (* X![n](f)                *)
  | F_NUM_WEAK_NEXT     of int * fl               (* next[n](f)              *)
  | F_NUM_STRONG_NEXT   of int * fl               (* next![n](f)             *)
  | F_NUM_WEAK_NEXT_A   of range * fl             (* next_a[n](f)            *)
  | F_NUM_STRONG_NEXT_A of range * fl             (* next_a![n](f)           *)
  | F_NUM_WEAK_NEXT_E   of range * fl             (* next_e[n](f)            *)
  | F_NUM_STRONG_NEXT_E of range * fl             (* next_e![n](f)           *)
  | F_STRONG_NEXT_EVENT of bexp * fl              (* next_event!(b)(f)       *)
  | F_WEAK_NEXT_EVENT   of bexp * fl              (* next_event(b)(f)        *)
  | F_NUM_STRONG_NEXT_EVENT
                        of bexp * int * fl        (* next_event!(b)[i](f)    *)
  | F_NUM_WEAK_NEXT_EVENT
                        of bexp * int * fl        (* next_event(b)[i](f)     *)
  | F_NUM_STRONG_NEXT_EVENT_A
                        of bexp * range  * fl     (* next_event_a!(b)[i](f)  *)
  | F_NUM_WEAK_NEXT_EVENT_A
                        of bexp * range  * fl     (* next_event_a(b)[i](f)   *)
  | F_NUM_STRONG_NEXT_EVENT_E
                        of bexp * range  * fl     (* next_event_e!(b)[i](f)  *)
  | F_NUM_WEAK_NEXT_EVENT_E
                        of bexp * range  * fl     (* next_event_e(b)[i](f)   *)
  | F_SKIP_STRONG_IMP   of sere * sere            (* {r1} |=> {r2}!          *)
  | F_SKIP_WEAK_IMP     of sere * sere            (* {r1} |=> {r2}           *)
  | F_SERE_ALWAYS       of sere                   (* always r                *)
  | F_SERE_NEVER        of sere                   (* never r                 *)
  | F_SERE_STRONG_EVENTUALLY
                        of sere                   (* eventually! r           *)
  | F_STRONG_WITHIN     of sere * bexp * sere     (* within!(r1,b)r2         *)
  | F_WEAK_WITHIN       of sere * bexp * sere     (* within(r1,b)r2          *)
  | F_STRONG_WITHIN_INC of sere * bexp * sere     (* within!_(r1,b)r2        *)
  | F_WEAK_WITHIN_INC   of sere * bexp * sere     (* within_(r1,b)r2         *)
  | F_STRONG_WHILENOT   of bexp * sere            (* whilenot!(b)r           *)
  | F_WEAK_WHILENOT     of bexp * sere            (* whilenot(b)r            *)
  | F_STRONG_WHILENOT_INC
                        of bexp * sere            (* whilenot!_(b)r          *)
  | F_WEAK_WHILENOT_INC of bexp * sere            (* whilenot_(b)r           *)
;


(******************************************************************************
* Formulas of the Optional Branching Extension (OBE)
******************************************************************************)
datatype obe =
    O_BOOL        of bexp                        (* boolean expression       *)
  | O_NOT         of obe                         (* \neg f                   *)
  | O_AND         of obe * obe                   (* f1 \wedge f2             *)
  | O_EX          of obe                         (* EX f                     *)
  | O_EU          of obe * obe                   (* E[f1 U f2]               *)
  | O_EG          of obe                         (* EG f                     *)
;


