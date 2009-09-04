(*****************************************************************************)
(* Create "ExtendedSyntaxTheory" representing abstract syntax of full PSL    *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open intLib stringLib stringTheory SyntaxTheory SyntacticSugarTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called ExtendedSyntaxTheory
******************************************************************************)
val _ = new_theory "ExtendedSyntax";

(******************************************************************************
* Extended boolean expressions
******************************************************************************)
val ebexp_def =
 time
 Hol_datatype
  `ebexp =
    EB_PROP              of string                (* atomic proposition      *)
  | EB_NOT               of ebexp                 (* negation                *)
  | EB_AND               of ebexp # ebexp         (* conjunction             *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | EB_OR                of ebexp # ebexp         (* disjunction             *)
  | EB_IMP               of ebexp # ebexp         (* implication             *)
  | EB_IFF               of ebexp # ebexp         (* logical equivalence     *)
  | EB_TRUE                                       (* T                       *)
  | EB_FALSE                                      (* F                       *)
  `;

(******************************************************************************
* Specification of an iteration number or range (Count of LRM A.3.6)
******************************************************************************)
val _ = type_abbrev("range", ``:num # num option``);

(******************************************************************************
* Extended Sequential Extended Regular Expressions (SEREs)
******************************************************************************)
val esere_def =
 time
 Hol_datatype
  `esere =
    ES_BOOL              of ebexp                 (* boolean expression      *)
  | ES_CAT               of esere # esere         (* r1 ;  r2                *)
  | ES_FUSION            of esere # esere         (* r1 :  r2                *)
  | ES_OR                of esere # esere         (* r1 |  r2                *)
  | ES_AND               of esere # esere         (* r1 && r2                *)
  | ES_REPEAT            of esere                 (* r[*]                    *)
  | ES_CLOCK             of esere # ebexp         (* r@clk                   *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | ES_FLEX_AND          of esere # esere         (* r1 &  r2                *)
  | ES_RANGE_REPEAT      of esere # range         (* r[* i]                  *)
  | ES_NON_ZERO_REPEAT   of esere                 (* r[+]                    *)
  | ES_RANGE_EQ_REPEAT   of ebexp # range         (* b[= i]                  *)
  | ES_RANGE_GOTO_REPEAT of ebexp # range         (* b[-> i]                 *)
  `;

(******************************************************************************
* Extended Formulas
* runtime: 589.300s,    gctime: 151.590s,     systime: 3.800s. (on bass)
******************************************************************************)
val efl_def =
 time
 Hol_datatype
  `efl =
    EF_BOOL              of ebexp                 (* boolean expression      *)
  | EF_NOT               of efl                   (* \neg f                  *)
  | EF_AND               of efl # efl             (* f1 \wedge f2            *)
  | EF_STRONG_X          of efl                   (* X! f                    *)
  | EF_U                 of efl # efl             (* [f1 U f2]               *)
  | EF_SUFFIX_IMP        of esere # efl           (* {r}(f)                  *)
  | EF_STRONG_IMP        of esere # esere         (* {r1} |-> {r2}!          *)
  | EF_WEAK_IMP          of esere # esere         (* {r1} |-> {r2}           *)
  | EF_ABORT             of efl # ebexp           (* f abort b               *)
  | EF_STRONG_CLOCK      of efl # ebexp           (* f@clk!                  *)
(*=========  Following are defined operators (i.e. syntactic sugar) =========*)
  | EF_WEAK_CLOCK        of efl # ebexp           (* f@clk                   *)
  | EF_OR                of efl # efl             (* f1 \vee f2              *)
  | EF_IMP               of efl # efl             (* f1 \rightarrow f2       *)
  | EF_IFF               of efl # efl             (* f1 \leftrightarrow f2   *)
  | EF_WEAK_X            of efl                   (* X f                     *)
  | EF_F                 of efl                   (* F f                     *)
  | EF_G                 of efl                   (* G f                     *)
  | EF_W                 of efl # efl             (* [f1 W f2]               *)
  | EF_ALWAYS            of efl                   (* always f                *)
  | EF_NEVER             of efl                   (* never f                 *)
  | EF_WEAK_NEXT         of efl                   (* next f                  *)
  | EF_STRONG_NEXT       of efl                   (* next! f                 *)
  | EF_STRONG_EVENTUALLY of efl                   (* next! f                 *)
  | EF_STRONG_UNTIL      of efl # efl             (* [f1 until! f2]          *)
  | EF_WEAK_UNTIL        of efl # efl             (* [f1 until f2]           *)
  | EF_STRONG_UNTIL_INC  of efl # efl             (* [f1 until!_ f2]         *)
  | EF_WEAK_UNTIL_INC    of efl # efl             (* [f1 until_ f2]          *)
  | EF_STRONG_BEFORE     of efl # efl             (* [f1 before! f2]         *)
  | EF_WEAK_BEFORE       of efl # efl             (* [f1 before f2]          *)
  | EF_STRONG_BEFORE_INC
                         of efl # efl             (* [f1 before!_ f2]        *)
  | EF_WEAK_BEFORE_INC   of efl # efl             (* [f1 before_ f2]         *)
  | EF_NUM_WEAK_X        of num # efl             (* X[n](f)                 *)
  | EF_NUM_STRONG_X      of num # efl             (* X![n](f)                *)
  | EF_NUM_WEAK_NEXT     of num # efl             (* next[n](f)              *)
  | EF_NUM_STRONG_NEXT   of num # efl             (* next![n](f)             *)
  | EF_NUM_WEAK_NEXT_A   of range # efl           (* next_a[n](f)            *)
  | EF_NUM_STRONG_NEXT_A of range # efl            (* next_a![n](f)           *)
  | EF_NUM_WEAK_NEXT_E   of range # efl           (* next_e[n](f)            *)
  | EF_NUM_STRONG_NEXT_E of range # efl            (* next_e![n](f)           *)
  | EF_STRONG_NEXT_EVENT of ebexp # efl            (* next_event!(b)(f)       *)
  | EF_WEAK_NEXT_EVENT   of ebexp # efl           (* next_event(b)(f)        *)
  | EF_NUM_STRONG_NEXT_EVENT
                         of ebexp # num # efl     (* next_event!(b)[i](f)    *)
  | EF_NUM_WEAK_NEXT_EVENT
                         of ebexp # num # efl     (* next_event(b)[i](f)     *)
  | EF_NUM_STRONG_NEXT_EVENT_A
                         of ebexp # range # efl   (* next_event_a!(b)[i](f)  *)
  | EF_NUM_WEAK_NEXT_EVENT_A
                         of ebexp # range # efl   (* next_event_a(b)[i](f)   *)
  | EF_NUM_STRONG_NEXT_EVENT_E
                         of ebexp # range # efl   (* next_event_e!(b)[i](f)  *)
  | EF_NUM_WEAK_NEXT_EVENT_E
                         of ebexp # range # efl   (* next_event_e(b)[i](f)   *)
  | EF_SKIP_STRONG_IMP   of esere # esere         (* {r1} |=> {r2}!          *)
  | EF_SKIP_WEAK_IMP     of esere # esere         (* {r1} |=> {r2}           *)
  | EF_SERE_ALWAYS       of esere                 (* always r                *)
  | EF_SERE_NEVER        of esere                 (* never r                 *)
  | EF_SERE_STRONG_EVENTUALLY
                         of esere                 (* eventually! r           *)
  | EF_STRONG_WITHIN     of esere # ebexp # esere (* within!(r1,b)r2         *)
  | EF_WEAK_WITHIN       of esere # ebexp # esere (* within(r1,b)r2          *)
  | EF_STRONG_WITHIN_INC of esere # ebexp # esere (* within!_(r1,b)r2        *)
  | EF_WEAK_WITHIN_INC   of esere # ebexp # esere (* within_(r1,b)r2         *)
  | EF_STRONG_WHILENOT   of ebexp # esere         (* whilenot!(b)r           *)
  | EF_WEAK_WHILENOT     of ebexp # esere         (* whilenot(b)r            *)
  | EF_STRONG_WHILENOT_INC
                         of ebexp # esere         (* whilenot!_(b)r          *)
  | EF_WEAK_WHILENOT_INC of ebexp # esere         (* whilenot_(b)r           *)
  `;


(******************************************************************************
* Translate booleans from extended syntax into core syntax
******************************************************************************)
val B_DESUGAR_def =
 Define
  `(B_DESUGAR(EB_PROP p)     = B_PROP p)                          /\
   (B_DESUGAR(EB_NOT b)      = B_NOT(B_DESUGAR b))                /\
   (B_DESUGAR(EB_AND(b1,b2)) = B_AND(B_DESUGAR b1, B_DESUGAR b2)) /\
   (B_DESUGAR(EB_OR(b1,b2))  = B_OR(B_DESUGAR b1, B_DESUGAR b2))  /\
   (B_DESUGAR(EB_IMP(b1,b2)) = B_IMP(B_DESUGAR b1, B_DESUGAR b2)) /\
   (B_DESUGAR(EB_IFF(b1,b2)) = B_IFF(B_DESUGAR b1, B_DESUGAR b2)) /\
   (B_DESUGAR EB_TRUE        = B_TRUE)                            /\
   (B_DESUGAR EB_FALSE       = B_FALSE)`;


(******************************************************************************
* Translate extended SEREs into core syntax
******************************************************************************)
val S_DESUGAR_def =
 Define
  `(S_DESUGAR(ES_BOOL b) =
     S_BOOL(B_DESUGAR b))
   /\
   (S_DESUGAR(ES_CAT(r1,r2)) =
     S_CAT(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (S_DESUGAR(ES_FUSION(r1,r2)) =
     S_FUSION(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (S_DESUGAR(ES_OR(r1,r2)) =
     S_OR(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (S_DESUGAR(ES_AND(r1,r2)) =
     S_AND(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (S_DESUGAR(ES_REPEAT r) =
     S_REPEAT(S_DESUGAR r))
   /\
   (S_DESUGAR(ES_CLOCK(r,b)) =
     S_CLOCK(S_DESUGAR r, B_DESUGAR b))
   /\
   (S_DESUGAR(ES_FLEX_AND(r1,r2)) =
     S_FLEX_AND(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (S_DESUGAR(ES_RANGE_REPEAT(r,rng)) =
     S_RANGE_REPEAT(S_DESUGAR r, rng))
   /\
   (S_DESUGAR(ES_NON_ZERO_REPEAT r) =
     S_NON_ZERO_REPEAT(S_DESUGAR r))
   /\
   (S_DESUGAR(ES_RANGE_EQ_REPEAT(b, rng)) =
     S_RANGE_EQ_REPEAT(B_DESUGAR b, rng))
   /\
   (S_DESUGAR(ES_RANGE_GOTO_REPEAT(b,rng)) =
     S_RANGE_GOTO_REPEAT(B_DESUGAR b, rng))`;

(******************************************************************************
* Definitions connecting syntax-oriented names with semantic constants
******************************************************************************)
val F_STRONG_X_def = Define `F_STRONG_X = F_NEXT`;

val F_U_def = Define `F_U = F_UNTIL`;

val F_IMP_def = Define `F_IMP = F_IMPLIES`;

(******************************************************************************
* Translate extended formulas into core syntax
******************************************************************************)
val F_DESUGAR_def =
 Define
  `(F_DESUGAR(EF_BOOL b) =
     F_BOOL(B_DESUGAR b))
   /\
   (F_DESUGAR(EF_NOT f) =
     F_NOT(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_AND(f1,f2)) =
     F_AND(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_STRONG_X f) =
     F_STRONG_X(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_U(f1,f2)) =
     F_U(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_SUFFIX_IMP(r,f)) =
     F_SUFFIX_IMP(S_DESUGAR r, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_STRONG_IMP(r1,r2)) =
     F_STRONG_IMP(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_WEAK_IMP(r1,r2)) =
     F_WEAK_IMP(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_ABORT(f,b)) =
     F_ABORT(F_DESUGAR f, B_DESUGAR b))
   /\
   (F_DESUGAR(EF_STRONG_CLOCK(f,b)) =
     F_STRONG_CLOCK(F_DESUGAR f, B_DESUGAR b))
   /\
   (F_DESUGAR(EF_WEAK_CLOCK(f,b)) =
     F_WEAK_CLOCK(F_DESUGAR f, B_DESUGAR b))
   /\
   (F_DESUGAR(EF_OR(f1,f2)) =
     F_OR(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_IMP(f1,f2)) =
     F_IMP(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_IFF(f1,f2)) =
     F_IFF(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_WEAK_X f) =
     F_WEAK_X(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_F f) =
     F_F(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_G f) =
     F_G(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_W(f1,f2)) =
     F_W(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_ALWAYS f) =
     F_ALWAYS(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NEVER f) =
     F_NEVER(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_WEAK_NEXT f) =
     F_WEAK_NEXT(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_STRONG_NEXT f) =
     F_STRONG_NEXT(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_STRONG_EVENTUALLY f) =
     F_STRONG_EVENTUALLY(F_DESUGAR f))
   /\
   (F_DESUGAR(EF_STRONG_UNTIL(f1,f2)) =
     F_STRONG_UNTIL(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_WEAK_UNTIL(f1,f2)) =
     F_WEAK_UNTIL(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_STRONG_UNTIL_INC(f1,f2)) =
     F_STRONG_UNTIL_INC(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_WEAK_UNTIL_INC(f1,f2)) =
     F_WEAK_UNTIL_INC(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_STRONG_BEFORE(f1,f2)) =
     F_STRONG_BEFORE(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_WEAK_BEFORE(f1,f2)) =
     F_WEAK_BEFORE(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_STRONG_BEFORE_INC(f1,f2)) =
     F_STRONG_BEFORE_INC(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_WEAK_BEFORE_INC(f1,f2)) =
     F_WEAK_BEFORE_INC(F_DESUGAR f1, F_DESUGAR f2))
   /\
   (F_DESUGAR(EF_NUM_WEAK_X(n,f)) =
     F_NUM_WEAK_X(n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_X(n,f)) =
     F_NUM_STRONG_X(n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT(n,f)) =
     F_NUM_WEAK_NEXT(n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT(n,f)) =
     F_NUM_STRONG_NEXT(n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT_A(rng,f)) =
     F_NUM_WEAK_NEXT_A(rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT_A(rng,f)) =
     F_NUM_STRONG_NEXT_A(rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT_E(rng,f)) =
     F_NUM_WEAK_NEXT_E(rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT_E(rng,f)) =
     F_NUM_STRONG_NEXT_E(rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_STRONG_NEXT_EVENT(b,f)) =
     F_STRONG_NEXT_EVENT(B_DESUGAR b, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_WEAK_NEXT_EVENT(b,f)) =
     F_WEAK_NEXT_EVENT(B_DESUGAR b, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT_EVENT(b,n,f)) =
     F_NUM_STRONG_NEXT_EVENT(B_DESUGAR b, n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT_EVENT(b,n,f)) =
     F_NUM_WEAK_NEXT_EVENT(B_DESUGAR b, n, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT_EVENT_A(b,rng,f)) =
     F_NUM_STRONG_NEXT_EVENT_A(B_DESUGAR b, rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT_EVENT_A(b,rng,f)) =
     F_NUM_WEAK_NEXT_EVENT_A(B_DESUGAR b, rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_STRONG_NEXT_EVENT_E(b,rng,f)) =
     F_NUM_STRONG_NEXT_EVENT_E(B_DESUGAR b, rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_NUM_WEAK_NEXT_EVENT_E(b,rng,f)) =
     F_NUM_WEAK_NEXT_EVENT_E(B_DESUGAR b, rng, F_DESUGAR f))
   /\
   (F_DESUGAR(EF_SKIP_STRONG_IMP(r1,r2)) =
     F_SKIP_STRONG_IMP(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_SKIP_WEAK_IMP(r1,r2)) =
     F_SKIP_WEAK_IMP(S_DESUGAR r1, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_SERE_ALWAYS r) =
     F_SERE_ALWAYS(S_DESUGAR r))
   /\
   (F_DESUGAR(EF_SERE_NEVER r) =
     F_SERE_NEVER(S_DESUGAR r))
   /\
   (F_DESUGAR(EF_SERE_STRONG_EVENTUALLY r) =
     F_SERE_STRONG_EVENTUALLY(S_DESUGAR r))
   /\
   (F_DESUGAR(EF_STRONG_WITHIN(r1,b,r2)) =
     F_STRONG_WITHIN(S_DESUGAR r1, B_DESUGAR b, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_WEAK_WITHIN(r1,b,r2)) =
     F_WEAK_WITHIN(S_DESUGAR r1, B_DESUGAR b, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_STRONG_WITHIN_INC(r1,b,r2)) =
     F_STRONG_WITHIN_INC(S_DESUGAR r1, B_DESUGAR b, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_WEAK_WITHIN_INC(r1,b,r2)) =
     F_WEAK_WITHIN_INC(S_DESUGAR r1, B_DESUGAR b, S_DESUGAR r2))
   /\
   (F_DESUGAR(EF_STRONG_WHILENOT(b,r)) =
     F_STRONG_WHILENOT(B_DESUGAR b, S_DESUGAR r))
   /\
   (F_DESUGAR(EF_WEAK_WHILENOT(b,r)) =
     F_WEAK_WHILENOT(B_DESUGAR b, S_DESUGAR r))
   /\
   (F_DESUGAR(EF_STRONG_WHILENOT_INC(b,r)) =
     F_STRONG_WHILENOT_INC(B_DESUGAR b, S_DESUGAR r))
   /\
   (F_DESUGAR(EF_WEAK_WHILENOT_INC(b,r)) =
     F_WEAK_WHILENOT_INC(B_DESUGAR b, S_DESUGAR r))`;

val _ = export_theory();
