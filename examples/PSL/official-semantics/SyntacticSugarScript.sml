(*****************************************************************************)
(* Definitions from LRM B.3 "Syntactic sugaring"                             *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(*
quietdec := true;
loadPath := "../official-semantics" :: !loadPath;
map load ["intLib","stringTheory","SyntaxTheory"];
open intLib stringTheory SyntaxTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open intLib stringTheory SyntaxTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called SyntacticSugarTheory
******************************************************************************)
val _ = new_theory "SyntacticSugar";

(******************************************************************************
* pureDefine doesn't export definitions to theCompset (for EVAL).
******************************************************************************)
val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(******************************************************************************
* Additional boolean operators
******************************************************************************)

(******************************************************************************
* Definition of disjunction
******************************************************************************)

val B_OR_def =
 pureDefine `B_OR(b1,b2) = B_NOT(B_AND(B_NOT b1, B_NOT b2))`;

(******************************************************************************
* Definition of implication
******************************************************************************)

val B_IMP_def =
 pureDefine `B_IMP(b1,b2) = B_OR(B_NOT b1, b2)`;

(******************************************************************************
* Definition of logical equivalence
******************************************************************************)

val B_IFF_def =
 pureDefine `B_IFF(b1,b2) = B_AND(B_IMP(b1, b2),B_IMP(b2, b1))`;

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
* Additional SERE operators
******************************************************************************)

(******************************************************************************
* SERE versions of T and F
******************************************************************************)

val S_TRUE_def  = Define `S_TRUE  = S_BOOL B_TRUE`
and S_FALSE_def = Define `S_FALSE = S_BOOL B_FALSE`;

(******************************************************************************
* {r1} & {r2} = {{r1} && {r2;T[*]}} | {{r1;T[*]} && {r2}}
******************************************************************************)
val S_FLEX_AND_def =
 Define 
  `S_FLEX_AND(r1,r2) = 
    S_OR
     (S_AND(r1,S_CAT(r2, S_REPEAT S_TRUE)),
      S_AND(S_CAT(r1,S_REPEAT S_TRUE), r2))`;

(******************************************************************************
*         |  F[*]                  if i = 0
* r[*i] = <
*         |  r;r;...;r (i times)   otherwise
******************************************************************************)
val S_REPEAT_ITER_def =
 Define 
  `S_REPEAT_ITER r i = 
    if i=0 then S_REPEAT(S_BOOL B_FALSE) 
           else if i=1 then r else S_CAT(r, S_REPEAT_ITER r (i-1))`;

(******************************************************************************
* RANGE_ITER(i, j) op f = (f i) op (f(i+1)) op ... op (f j)
******************************************************************************)

(******************************************************************************
* RANGE_ITER_AUX op f i n = (f i) op (f(i+1)) op ... op (f n)
******************************************************************************)
val RANGE_ITER_AUX_def =
 Define 
  `(RANGE_ITER_AUX op f i 0 = f i)
   /\
   (RANGE_ITER_AUX op f i (SUC n) = op(f i, RANGE_ITER_AUX op f (i+1) n))`;

(******************************************************************************
* Prove if-then-else form needed by computeLib
******************************************************************************)
val RANGE_ITER_AUX =
 prove
  (``RANGE_ITER_AUX op f i n = 
      if n=0 then f i
             else op(f i, RANGE_ITER_AUX op f (i+1) (n-1))``,
   Cases_on `n` THEN RW_TAC arith_ss [RANGE_ITER_AUX_def]);

val _ = computeLib.add_funs[RANGE_ITER_AUX];

val RANGE_ITER_def =
 Define `RANGE_ITER(i, j) op f = RANGE_ITER_AUX op f i (j-i)`;

(******************************************************************************
* S_RANGE_REPEAT(r, (i,j)) = r[*i..j] = {r[*i]} | {r[*(i+1)]} | ... | {r[*j]}
******************************************************************************)
val S_RANGE_REPEAT_def =
 Define
  `(S_RANGE_REPEAT(r, (i, SOME j)) = RANGE_ITER(i, j) S_OR (S_REPEAT_ITER r))
   /\
   (S_RANGE_REPEAT(r, (i, NONE)) = S_CAT(S_REPEAT_ITER r i, S_REPEAT r))`;

(******************************************************************************
* r[+] = r;r[*] 
******************************************************************************)
val S_NON_ZERO_REPEAT_def =
 Define `S_NON_ZERO_REPEAT r = S_CAT(r, S_REPEAT r)`;

(******************************************************************************
* b[=i] = {!b[*];b}[*i];!b[*]
******************************************************************************)
val S_EQ_REPEAT_ITER_def =
 Define
  `S_EQ_REPEAT_ITER b i =
    S_CAT
     (S_REPEAT_ITER (S_CAT(S_REPEAT(S_BOOL(B_NOT b)),S_BOOL b)) i,
      S_REPEAT(S_BOOL(B_NOT b)))`;

(******************************************************************************
* S_RANGE_EQ_REPEAT(b, (i,j)) = 
*  b[=i..j] = {b[=i]} | {b[*=i+1)]} | ... | {b[=j]}
******************************************************************************)
val S_RANGE_EQ_REPEAT_def =
 Define
  `(S_RANGE_EQ_REPEAT(b, (i, SOME j)) = 
     RANGE_ITER(i, j) S_OR (S_EQ_REPEAT_ITER b))
   /\
   (S_RANGE_EQ_REPEAT(b, (i, NONE)) = 
     S_CAT(S_EQ_REPEAT_ITER b i, S_REPEAT S_TRUE))`;

(******************************************************************************
* b[->i] = {!b[*];b}[*i]
******************************************************************************)
val S_GOTO_REPEAT_ITER_def =
 Define
  `S_GOTO_REPEAT_ITER b = 
    S_REPEAT_ITER (S_CAT(S_REPEAT(S_BOOL(B_NOT b)),S_BOOL b))`;

(******************************************************************************
* S_RANGE_GOTO_REPEAT(b, (i,j)) = 
*  b[=i..j] = {b[=i]} | {b[*=i+1)]} | ... | {b[=j]}
******************************************************************************)
val S_RANGE_GOTO_REPEAT_def =
 Define
  `(S_RANGE_GOTO_REPEAT(b, (i, SOME j)) = 
     RANGE_ITER(i, j) S_OR (S_GOTO_REPEAT_ITER b))
   /\
   (S_RANGE_GOTO_REPEAT(b, (i, NONE)) = S_GOTO_REPEAT_ITER b i)`;

(******************************************************************************
* Formula disjunction: f1 \/ f2
******************************************************************************)
val F_OR_def =
 Define
  `F_OR(f1,f2) = F_NOT(F_AND(F_NOT f1, F_NOT f2))`;

(******************************************************************************
* Formula implication: f1 --> f2
******************************************************************************)
val F_IMPLIES_def =
 Define 
  `F_IMPLIES(f1,f2) = F_OR(F_NOT f1, f2)`;

(******************************************************************************
* Formula equivalence: f1 <--> f2
******************************************************************************)
val F_IFF_def =
 Define 
  `F_IFF(f1,f2) = F_AND(F_IMPLIES(f1, f2), F_IMPLIES(f2, f1))`;
      
(******************************************************************************
* Weak next: X f
******************************************************************************)
val F_WEAK_X_def =
 Define
  `F_WEAK_X f = F_NOT(F_NEXT(F_NOT f))`;

(******************************************************************************
* Eventually: F f
******************************************************************************)
val F_F_def =
 Define
  `F_F f = F_UNTIL(F_BOOL B_TRUE, f)`;
      
(******************************************************************************
* Always: G f
******************************************************************************)
val F_G_def =
 Define
  `F_G f = F_NOT(F_F(F_NOT f))`;

(******************************************************************************
* Weak until: [f1 W f2]
******************************************************************************)
val F_W_def =
 Define
  `F_W(f1,f2) = F_OR(F_UNTIL(f1,f2), F_G f1)`;

(******************************************************************************
* always f
******************************************************************************)
val F_ALWAYS_def =
 Define
  `F_ALWAYS = F_G`;

(******************************************************************************
* never f
******************************************************************************)
val F_NEVER_def =
 Define
  `F_NEVER f = F_G(F_NOT f)`;

(******************************************************************************
* Strong next: next! f
******************************************************************************)
val F_STRONG_NEXT_def =
 Define
  `F_STRONG_NEXT f = F_NEXT f`;

(******************************************************************************
* Weak next: next f
******************************************************************************)
val F_WEAK_NEXT_def =
 Define
  `F_WEAK_NEXT = F_WEAK_X`;

(******************************************************************************
* eventually! f
******************************************************************************)
val F_STRONG_EVENTUALLY_def =
 Define
  `F_STRONG_EVENTUALLY = F_F`;

(******************************************************************************
* f1 until! f2
******************************************************************************)
val F_STRONG_UNTIL_def =
 Define
  `F_STRONG_UNTIL = F_UNTIL`;

(******************************************************************************
* f1 until f2
******************************************************************************)
val F_WEAK_UNTIL_def =
 Define
  `F_WEAK_UNTIL = F_W`;

(******************************************************************************
* f1 until!_ f2
******************************************************************************)
val F_STRONG_UNTIL_INC_def =
 Define
  `F_STRONG_UNTIL_INC(f1,f2) = F_UNTIL(f1, F_AND(f1,f2))`;

(******************************************************************************
* f1 until_ f2
******************************************************************************)
val F_WEAK_UNTIL_INC_def =
 Define
  `F_WEAK_UNTIL_INC(f1,f2) = F_W(f1, F_AND(f1,f2))`;

(******************************************************************************
* f1 before! f2
******************************************************************************)
val F_STRONG_BEFORE_def =
 Define
  `F_STRONG_BEFORE(f1,f2) = F_UNTIL(F_NOT f2, F_AND(f1, F_NOT f2))`;

(******************************************************************************
* f1 before f2
******************************************************************************)
val F_WEAK_BEFORE_def =
 Define
  `F_WEAK_BEFORE(f1,f2) = F_W(F_NOT f2, F_AND(f1, F_NOT f2))`;

(******************************************************************************
* f1 before!_ f2
******************************************************************************)
val F_STRONG_BEFORE_INC_def =
 Define
  `F_STRONG_BEFORE_INC(f1,f2) = F_UNTIL(F_NOT f2, f1)`;

(******************************************************************************
* f1 before_ f2
******************************************************************************)
val F_WEAK_BEFORE_INC_def =
 Define
  `F_WEAK_BEFORE_INC(f1,f2) = F_W(F_NOT f2, f1)`;

(******************************************************************************
*          |  f                        if i = 0
* X![i]f = <
*          |  X! X! ... X! (i times)   otherwise
******************************************************************************)
val F_NUM_STRONG_X_def =
 Define 
  `F_NUM_STRONG_X(i,f) = FUNPOW F_NEXT i f`;

(******************************************************************************
*         |  f                     if i = 0
* X[i]f = <
*         |  X X ... X (i times)   otherwise
*
* Note double-negation redundancy:
* EVAL ``F_NUM_WEAK_X(2,f)``;
* > val it =
*     |- F_NUM_WEAK_X (2,f) =
*        F_NOT (F_NEXT (F_NOT (F_NOT (F_NEXT (F_NOT f))))) : thm
* 
******************************************************************************)
val F_NUM_WEAK_X_def =
 Define 
  `F_NUM_WEAK_X(i,f) = FUNPOW F_WEAK_X i f`;

(******************************************************************************
* next![i] f = X! [i] f
******************************************************************************)
val F_NUM_STRONG_NEXT_def =
 Define 
  `F_NUM_STRONG_NEXT = F_NUM_STRONG_X`;

(******************************************************************************
* next[i] f = X [i] f
******************************************************************************)
val F_NUM_WEAK_NEXT_def =
 Define 
  `F_NUM_WEAK_NEXT = F_NUM_WEAK_X`;

(******************************************************************************
* next_a![i..j]f = X![i]f /\ ... /\ X![j]f
******************************************************************************)
val F_NUM_STRONG_NEXT_A_def =
 Define 
  `F_NUM_STRONG_NEXT_A((i, SOME j),f) = 
    RANGE_ITER (i,j) $F_AND (\n. F_NUM_STRONG_X(n,f))`;

(******************************************************************************
* next_a[i..j]f = X[i]f /\ ... /\ X[j]f
******************************************************************************)
val F_NUM_WEAK_NEXT_A_def =
 Define 
  `F_NUM_WEAK_NEXT_A((i, SOME j),f) = 
    RANGE_ITER (i,j) $F_AND (\n. F_NUM_WEAK_X(n,f))`;

(******************************************************************************
* next_e![i..j]f = X![i]f \/ ... \/ X![j]f
******************************************************************************)
val F_NUM_STRONG_NEXT_E_def =
 Define 
  `F_NUM_STRONG_NEXT_E((i, SOME j),f) = 
    RANGE_ITER (i,j) $F_OR (\n. F_NUM_STRONG_X(n,f))`;

(******************************************************************************
* next_e[i..j]f = X[i]f \/ ... \/ X[j]f
******************************************************************************)
val F_NUM_WEAK_NEXT_E_def =
 Define 
  `F_NUM_WEAK_NEXT_E((i, SOME j),f) = 
    RANGE_ITER (i,j) $F_OR (\n. F_NUM_WEAK_X(n,f))`;

(******************************************************************************
* next_event!(b)(f) = [!b U (b & f)]
******************************************************************************)
val F_STRONG_NEXT_EVENT_def =
 Define 
  `F_STRONG_NEXT_EVENT(b,f) =
    F_UNTIL(F_BOOL(B_NOT b), F_AND(F_BOOL b, f))`;

(******************************************************************************
* next_event(b)(f) = [!b W (b & f)]
******************************************************************************)
val F_WEAK_NEXT_EVENT_def =
 Define 
  `F_WEAK_NEXT_EVENT(b,f) =
    F_W(F_BOOL(B_NOT b), F_AND(F_BOOL b, f))`;

(******************************************************************************
* next_event!(b)[k](f) = next_event!
*                         (b)
*                         (X! next_event!(b) ... (X! next_event!(b)(f)) ... ) 
*                          |---------------- k-1 times ----------------|
******************************************************************************)
val F_NUM_STRONG_NEXT_EVENT_def =
 Define 
  `F_NUM_STRONG_NEXT_EVENT(b,k,f) = 
    F_STRONG_NEXT_EVENT
     (b, FUNPOW (\f. F_NEXT(F_STRONG_NEXT_EVENT(b,f))) (k-1) f)`;

(******************************************************************************
* next_event(b)[k](f) = next_event
*                         (b)
*                         (X next_event(b) ... (X next_event(b)(f)) ... ) 
*                          |-------------- k-1 times --------------|
******************************************************************************)
val F_NUM_WEAK_NEXT_EVENT_def =
 Define 
  `F_NUM_WEAK_NEXT_EVENT(b,k,f) = 
    F_WEAK_NEXT_EVENT
     (b, FUNPOW (\f. F_NEXT(F_WEAK_NEXT_EVENT(b,f))) (k-1) f)`;

(******************************************************************************
* next_event_a!(b)[k..l](f) =
*  next_event! (b) [k] (f) /\ ... /\ next_event! (b) [l] (f)
******************************************************************************)
val F_NUM_STRONG_NEXT_EVENT_A_def =
 Define 
  `F_NUM_STRONG_NEXT_EVENT_A(b,(k,SOME l),f) = 
    RANGE_ITER (k,l) $F_AND (\n. F_NUM_STRONG_NEXT_EVENT(b,n,f))`;

(******************************************************************************
* next_event_a(b)[k..l](f) =
*  next_event (b) [k] (f) /\ ... /\ next_event (b) [l] (f)
******************************************************************************)
val F_NUM_WEAK_NEXT_EVENT_A_def =
 Define 
  `F_NUM_WEAK_NEXT_EVENT_A(b,(k,SOME l),f) = 
    RANGE_ITER (k,l) $F_AND (\n. F_NUM_WEAK_NEXT_EVENT(b,n,f))`;

(******************************************************************************
* next_event_e!(b)[k..l](f) =
*  next_event! (b) [k] (f) \/ ... \/ next_event! (b) [l] (f)
******************************************************************************)
val F_NUM_STRONG_NEXT_EVENT_E_def =
 Define 
  `F_NUM_STRONG_NEXT_EVENT_E(b,(k,SOME l),f) = 
    RANGE_ITER (k,l) $F_OR (\n. F_NUM_STRONG_NEXT_EVENT(b,n,f))`;

(******************************************************************************
* next_event_a(b)[k..l](f) =
*  next_event (b) [k] (f) \/ ... \/ next_event (b) [l] (f)
******************************************************************************)
val F_NUM_WEAK_NEXT_EVENT_E_def =
 Define 
  `F_NUM_WEAK_NEXT_EVENT_E(b,(k,SOME l),f) = 
    RANGE_ITER (k,l) $F_OR (\n. F_NUM_WEAK_NEXT_EVENT(b,n,f))`;

(******************************************************************************
* {r1} |=> {r2}! = {r1} |-> {T;r2}!
******************************************************************************)
val F_SKIP_STRONG_IMP_def =
 Define
  `F_SKIP_STRONG_IMP(r1,r2) = F_STRONG_IMP(r1, S_CAT(S_TRUE, r2))`;

(******************************************************************************
* {r1} |=> {r2} = {r1} |-> {T;r2}
******************************************************************************)
val F_SKIP_WEAK_IMP_def =
 Define
  `F_SKIP_WEAK_IMP(r1,r2) = F_WEAK_IMP(r1, S_CAT(S_TRUE, r2))`;

(******************************************************************************
* always{r} = {T[*]} |-> {r}
******************************************************************************)
val F_SERE_ALWAYS_def =
 Define
  `F_SERE_ALWAYS r = F_WEAK_IMP(S_REPEAT S_TRUE, r)`;

(******************************************************************************
* never{r} = {T[*];r} |-> {F}
******************************************************************************)
val F_SERE_NEVER_def =
 Define
  `F_SERE_NEVER r = F_WEAK_IMP(S_CAT(S_REPEAT S_TRUE, r), S_FALSE) `;

(******************************************************************************
* eventually! {r} = {T} |-> {T[*];r}!
******************************************************************************)
val F_SERE_STRONG_EVENTUALLY_def =
 Define
  `F_SERE_STRONG_EVENTUALLY r = 
    F_STRONG_IMP(S_TRUE, S_CAT(S_REPEAT S_TRUE, r))`;

(******************************************************************************
* within!(r1,b){r2} = {r1} |-> {r2&&b[=0];b}!
******************************************************************************)
val F_STRONG_WITHIN_def =
 Define
  `F_STRONG_WITHIN (r1,b,r2) = 
    F_STRONG_IMP(r1, S_CAT(S_AND(r2, S_EQ_REPEAT_ITER b 0), S_BOOL b))`;

(******************************************************************************
* within(r1,b){r2} = {r1} |-> {r2&&b[=0];b}
******************************************************************************)
val F_WEAK_WITHIN_def =
 Define
  `F_WEAK_WITHIN (r1,b,r2) = 
    F_WEAK_IMP(r1, S_CAT(S_AND(r2, S_EQ_REPEAT_ITER b 0), S_BOOL b))`;

(******************************************************************************
* within!_(r1,b){r2} = {r1} |-> {r2&&{b[=0];b}}!
******************************************************************************)
val F_STRONG_WITHIN_INC_def =
 Define
  `F_STRONG_WITHIN_INC (r1,b,r2) = 
    F_STRONG_IMP(r1, S_AND(r2, S_CAT(S_EQ_REPEAT_ITER b 0, S_BOOL b)))`;

(******************************************************************************
* within_(r1,b){r2} = {r1} |-> {r2&&{b[=0];b}}
******************************************************************************)
val F_WEAK_WITHIN_INC_def =
 Define
  `F_WEAK_WITHIN_INC (r1,b,r2) = 
    F_WEAK_IMP(r1, S_AND(r2, S_CAT(S_EQ_REPEAT_ITER b 0, S_BOOL b)))`;

(******************************************************************************
* within(r1,b){r2} = {r1} |-> {r2&&b[=0];b}
******************************************************************************)
val F_WEAK_WITHIN_def =
 Define
  `F_WEAK_WITHIN (r1,b,r2) = 
    F_WEAK_IMP(r1, S_CAT(S_AND(r2, S_EQ_REPEAT_ITER b 0), S_BOOL b))`;

(******************************************************************************
* whilenot!(b){r} = within!(T,b){r}
******************************************************************************)
val F_STRONG_WHILENOT_def =
 Define
  `F_STRONG_WHILENOT (b,r) =  F_STRONG_WITHIN(S_TRUE,b,r)`;

(******************************************************************************
* whilenot(b){r} = within(T,b){r}
******************************************************************************)
val F_WEAK_WHILENOT_def =
 Define
  `F_WEAK_WHILENOT (b,r) =  F_WEAK_WITHIN(S_TRUE,b,r)`;

(******************************************************************************
* whilenot!_(b){r} = within!_(T,b){r}
******************************************************************************)
val F_STRONG_WHILENOT_INC_def =
 Define
  `F_STRONG_WHILENOT_INC (b,r) =  F_STRONG_WITHIN_INC(S_TRUE,b,r)`;

(******************************************************************************
* whilenot_(b){r} = within_(T,b){r}
******************************************************************************)
val F_WEAK_WHILENOT_INC_def =
 Define
  `F_WEAK_WHILENOT_INC (b,r) =  F_WEAK_WITHIN_INC(S_TRUE,b,r)`;

(******************************************************************************
* Define weak clocking: f@clk = !(!f)@clk)
******************************************************************************)
val F_WEAK_CLOCK_def =
 Define
  `F_WEAK_CLOCK(f,clk) = F_NOT(F_STRONG_CLOCK(F_NOT f, clk))`;

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
