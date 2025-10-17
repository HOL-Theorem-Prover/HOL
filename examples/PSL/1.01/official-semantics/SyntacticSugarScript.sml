(*****************************************************************************)
(* Definitions from LRM B.3 "Syntactic sugaring"                             *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(*
quietdec := true;
loadPath := "../official-semantics" :: !loadPath;
map load ["intLib","stringLib","stringTheory","SyntaxTheory"];
open intLib stringLib stringTheory SyntaxTheory;
quietdec := false;
*)

Theory SyntacticSugar
Ancestors
  string Syntax
Libs
  intLib stringLib

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Ensure term_of_int has correct type
* (i.e. not  int/1 -> term)
******************************************************************************)
val term_of_int = numLib.term_of_int;

(******************************************************************************
* Additional boolean operators
******************************************************************************)

(******************************************************************************
* Definition of disjunction
******************************************************************************)

Definition B_OR_def[nocompute]:
  B_OR(b1,b2) = B_NOT(B_AND(B_NOT b1, B_NOT b2))
End

(******************************************************************************
* Definition of implication
******************************************************************************)

Definition B_IMP_def[nocompute]:
  B_IMP(b1,b2) = B_OR(B_NOT b1, b2)
End

(******************************************************************************
* Definition of logical equivalence
******************************************************************************)

Definition B_IFF_def[nocompute]:
  B_IFF(b1,b2) = B_AND(B_IMP(b1, b2),B_IMP(b2, b1))
End

(******************************************************************************
* Definition of truth
******************************************************************************)

Definition B_TRUE_def[nocompute]:
  B_TRUE = B_OR(B_PROP ARB, B_NOT(B_PROP ARB))
End

(******************************************************************************
* Definition of falsity
******************************************************************************)

Definition B_FALSE_def[nocompute]:
  B_FALSE = B_NOT B_TRUE
End

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
Definition S_FLEX_AND_def:
   S_FLEX_AND(r1,r2) =
    S_OR
     (S_AND(r1,S_CAT(r2, S_REPEAT S_TRUE)),
      S_AND(S_CAT(r1,S_REPEAT S_TRUE), r2))
End

(******************************************************************************
*         |  F[*]                  if i = 0
* r[*i] = <
*         |  r;r;...;r (i times)   otherwise
******************************************************************************)
Definition S_REPEAT_ITER_def:
   S_REPEAT_ITER r i =
    if i=0 then S_REPEAT(S_BOOL B_FALSE)
           else if i=1 then r else S_CAT(r, S_REPEAT_ITER r (i-1))
End

(******************************************************************************
* RANGE_ITER(i, j) op f = (f i) op (f(i+1)) op ... op (f j)
******************************************************************************)

(******************************************************************************
* RANGE_ITER_AUX op f i n = (f i) op (f(i+1)) op ... op (f n)
******************************************************************************)
Definition RANGE_ITER_AUX_def:
   (RANGE_ITER_AUX op f i 0 = f i)
   /\
   (RANGE_ITER_AUX op f i (SUC n) = op(f i, RANGE_ITER_AUX op f (i+1) n))
End

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

Definition RANGE_ITER_def:
  RANGE_ITER(i, j) op f = RANGE_ITER_AUX op f i (j-i)
End

(******************************************************************************
* S_RANGE_REPEAT(r, (i,j)) = r[*i..j] = {r[*i]} | {r[*(i+1)]} | ... | {r[*j]}
******************************************************************************)
Definition S_RANGE_REPEAT_def:
   (S_RANGE_REPEAT(r, (i, SOME j)) = RANGE_ITER(i, j) S_OR (S_REPEAT_ITER r))
   /\
   (S_RANGE_REPEAT(r, (i, NONE)) = S_CAT(S_REPEAT_ITER r i, S_REPEAT r))
End

(******************************************************************************
* r[+] = r;r[*]
******************************************************************************)
Definition S_NON_ZERO_REPEAT_def:
  S_NON_ZERO_REPEAT r = S_CAT(r, S_REPEAT r)
End

(******************************************************************************
* b[=i] = {!b[*];b}[*i];!b[*]
******************************************************************************)
Definition S_EQ_REPEAT_ITER_def:
   S_EQ_REPEAT_ITER b i =
    S_CAT
     (S_REPEAT_ITER (S_CAT(S_REPEAT(S_BOOL(B_NOT b)),S_BOOL b)) i,
      S_REPEAT(S_BOOL(B_NOT b)))
End

(******************************************************************************
* S_RANGE_EQ_REPEAT(b, (i,j)) =
*  b[=i..j] = {b[=i]} | {b[*=i+1)]} | ... | {b[=j]}
******************************************************************************)
Definition S_RANGE_EQ_REPEAT_def:
   (S_RANGE_EQ_REPEAT(b, (i, SOME j)) =
     RANGE_ITER(i, j) S_OR (S_EQ_REPEAT_ITER b))
   /\
   (S_RANGE_EQ_REPEAT(b, (i, NONE)) =
     S_CAT(S_EQ_REPEAT_ITER b i, S_REPEAT S_TRUE))
End

(******************************************************************************
* b[->i] = {!b[*];b}[*i]
******************************************************************************)
Definition S_GOTO_REPEAT_ITER_def:
   S_GOTO_REPEAT_ITER b =
    S_REPEAT_ITER (S_CAT(S_REPEAT(S_BOOL(B_NOT b)),S_BOOL b))
End

(******************************************************************************
* S_RANGE_GOTO_REPEAT(b, (i,j)) =
*  b[=i..j] = {b[=i]} | {b[*=i+1)]} | ... | {b[=j]}
******************************************************************************)
Definition S_RANGE_GOTO_REPEAT_def:
   (S_RANGE_GOTO_REPEAT(b, (i, SOME j)) =
     RANGE_ITER(i, j) S_OR (S_GOTO_REPEAT_ITER b))
   /\
   (S_RANGE_GOTO_REPEAT(b, (i, NONE)) = S_GOTO_REPEAT_ITER b i)
End

(******************************************************************************
* Formula disjunction: f1 \/ f2
******************************************************************************)
Definition F_OR_def:
   F_OR(f1,f2) = F_NOT(F_AND(F_NOT f1, F_NOT f2))
End

(******************************************************************************
* Formula implication: f1 --> f2
******************************************************************************)
Definition F_IMPLIES_def:
   F_IMPLIES(f1,f2) = F_OR(F_NOT f1, f2)
End

(******************************************************************************
* Formula implication: f1 --> f2
* (alternative definition to match ML datatype)
******************************************************************************)
Definition F_IMP_def:
   F_IMP = F_IMPLIES
End

(******************************************************************************
* Formula equivalence: f1 <--> f2
******************************************************************************)
Definition F_IFF_def:
   F_IFF(f1,f2) = F_AND(F_IMPLIES(f1, f2), F_IMPLIES(f2, f1))
End

(******************************************************************************
* Weak next: X f
******************************************************************************)
Definition F_WEAK_X_def:
   F_WEAK_X f = F_NOT(F_NEXT(F_NOT f))
End

(******************************************************************************
* Eventually: F f
******************************************************************************)
Definition F_F_def:
   F_F f = F_UNTIL(F_BOOL B_TRUE, f)
End

(******************************************************************************
* Always: G f
******************************************************************************)
Definition F_G_def:
   F_G f = F_NOT(F_F(F_NOT f))
End

(******************************************************************************
* Weak until: [f1 W f2]
******************************************************************************)
Definition F_W_def:
   F_W(f1,f2) = F_OR(F_UNTIL(f1,f2), F_G f1)
End

(******************************************************************************
* always f
******************************************************************************)
Definition F_ALWAYS_def:
   F_ALWAYS = F_G
End

(******************************************************************************
* never f
******************************************************************************)
Definition F_NEVER_def:
   F_NEVER f = F_G(F_NOT f)
End

(******************************************************************************
* Strong next: next! f
******************************************************************************)
Definition F_STRONG_NEXT_def:
   F_STRONG_NEXT f = F_NEXT f
End

(******************************************************************************
* Weak next: next f
******************************************************************************)
Definition F_WEAK_NEXT_def:
   F_WEAK_NEXT = F_WEAK_X
End

(******************************************************************************
* eventually! f
******************************************************************************)
Definition F_STRONG_EVENTUALLY_def:
   F_STRONG_EVENTUALLY = F_F
End

(******************************************************************************
* f1 until! f2
******************************************************************************)
Definition F_STRONG_UNTIL_def:
   F_STRONG_UNTIL = F_UNTIL
End

(******************************************************************************
* f1 until f2
******************************************************************************)
Definition F_WEAK_UNTIL_def:
   F_WEAK_UNTIL = F_W
End

(******************************************************************************
* f1 until!_ f2
******************************************************************************)
Definition F_STRONG_UNTIL_INC_def:
   F_STRONG_UNTIL_INC(f1,f2) = F_UNTIL(f1, F_AND(f1,f2))
End

(******************************************************************************
* f1 until_ f2
******************************************************************************)
Definition F_WEAK_UNTIL_INC_def:
   F_WEAK_UNTIL_INC(f1,f2) = F_W(f1, F_AND(f1,f2))
End

(******************************************************************************
* f1 before! f2
******************************************************************************)
Definition F_STRONG_BEFORE_def:
   F_STRONG_BEFORE(f1,f2) = F_UNTIL(F_NOT f2, F_AND(f1, F_NOT f2))
End

(******************************************************************************
* f1 before f2
******************************************************************************)
Definition F_WEAK_BEFORE_def:
   F_WEAK_BEFORE(f1,f2) = F_W(F_NOT f2, F_AND(f1, F_NOT f2))
End

(******************************************************************************
* f1 before!_ f2
******************************************************************************)
Definition F_STRONG_BEFORE_INC_def:
   F_STRONG_BEFORE_INC(f1,f2) = F_UNTIL(F_NOT f2, f1)
End

(******************************************************************************
* f1 before_ f2
******************************************************************************)
Definition F_WEAK_BEFORE_INC_def:
   F_WEAK_BEFORE_INC(f1,f2) = F_W(F_NOT f2, f1)
End

(******************************************************************************
*          |  f                        if i = 0
* X![i]f = <
*          |  X! X! ... X! (i times)   otherwise
******************************************************************************)
Definition F_NUM_STRONG_X_def:
   F_NUM_STRONG_X(i,f) = FUNPOW F_NEXT i f
End

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
Definition F_NUM_WEAK_X_def:
   F_NUM_WEAK_X(i,f) = FUNPOW F_WEAK_X i f
End

(******************************************************************************
* next![i] f = X! [i] f
******************************************************************************)
Definition F_NUM_STRONG_NEXT_def:
   F_NUM_STRONG_NEXT = F_NUM_STRONG_X
End

(******************************************************************************
* next[i] f = X [i] f
******************************************************************************)
Definition F_NUM_WEAK_NEXT_def:
   F_NUM_WEAK_NEXT = F_NUM_WEAK_X
End

(******************************************************************************
* next_a![i..j]f = X![i]f /\ ... /\ X![j]f
******************************************************************************)
Definition F_NUM_STRONG_NEXT_A_def:
   F_NUM_STRONG_NEXT_A((i, SOME j),f) =
    RANGE_ITER (i,j) $F_AND (\n. F_NUM_STRONG_X(n,f))
End

(******************************************************************************
* next_a[i..j]f = X[i]f /\ ... /\ X[j]f
******************************************************************************)
Definition F_NUM_WEAK_NEXT_A_def:
   F_NUM_WEAK_NEXT_A((i, SOME j),f) =
    RANGE_ITER (i,j) $F_AND (\n. F_NUM_WEAK_X(n,f))
End

(******************************************************************************
* next_e![i..j]f = X![i]f \/ ... \/ X![j]f
******************************************************************************)
Definition F_NUM_STRONG_NEXT_E_def:
   F_NUM_STRONG_NEXT_E((i, SOME j),f) =
    RANGE_ITER (i,j) $F_OR (\n. F_NUM_STRONG_X(n,f))
End

(******************************************************************************
* next_e[i..j]f = X[i]f \/ ... \/ X[j]f
******************************************************************************)
Definition F_NUM_WEAK_NEXT_E_def:
   F_NUM_WEAK_NEXT_E((i, SOME j),f) =
    RANGE_ITER (i,j) $F_OR (\n. F_NUM_WEAK_X(n,f))
End

(******************************************************************************
* next_event!(b)(f) = [!b U (b & f)]
******************************************************************************)
Definition F_STRONG_NEXT_EVENT_def:
   F_STRONG_NEXT_EVENT(b,f) =
    F_UNTIL(F_BOOL(B_NOT b), F_AND(F_BOOL b, f))
End

(******************************************************************************
* next_event(b)(f) = [!b W (b & f)]
******************************************************************************)
Definition F_WEAK_NEXT_EVENT_def:
   F_WEAK_NEXT_EVENT(b,f) =
    F_W(F_BOOL(B_NOT b), F_AND(F_BOOL b, f))
End

(******************************************************************************
* next_event!(b)[k](f) = next_event!
*                         (b)
*                         (X! next_event!(b) ... (X! next_event!(b)(f)) ... )
*                          |---------------- k-1 times ----------------|
******************************************************************************)
Definition F_NUM_STRONG_NEXT_EVENT_def:
   F_NUM_STRONG_NEXT_EVENT(b,k,f) =
    F_STRONG_NEXT_EVENT
     (b, FUNPOW (\f. F_NEXT(F_STRONG_NEXT_EVENT(b,f))) (k-1) f)
End

(******************************************************************************
* next_event(b)[k](f) = next_event
*                         (b)
*                         (X next_event(b) ... (X next_event(b)(f)) ... )
*                          |-------------- k-1 times --------------|
******************************************************************************)
Definition F_NUM_WEAK_NEXT_EVENT_def:
   F_NUM_WEAK_NEXT_EVENT(b,k,f) =
    F_WEAK_NEXT_EVENT
     (b, FUNPOW (\f. F_NEXT(F_WEAK_NEXT_EVENT(b,f))) (k-1) f)
End

(******************************************************************************
* next_event_a!(b)[k..l](f) =
*  next_event! (b) [k] (f) /\ ... /\ next_event! (b) [l] (f)
******************************************************************************)
Definition F_NUM_STRONG_NEXT_EVENT_A_def:
   F_NUM_STRONG_NEXT_EVENT_A(b,(k,SOME l),f) =
    RANGE_ITER (k,l) $F_AND (\n. F_NUM_STRONG_NEXT_EVENT(b,n,f))
End

(******************************************************************************
* next_event_a(b)[k..l](f) =
*  next_event (b) [k] (f) /\ ... /\ next_event (b) [l] (f)
******************************************************************************)
Definition F_NUM_WEAK_NEXT_EVENT_A_def:
   F_NUM_WEAK_NEXT_EVENT_A(b,(k,SOME l),f) =
    RANGE_ITER (k,l) $F_AND (\n. F_NUM_WEAK_NEXT_EVENT(b,n,f))
End

(******************************************************************************
* next_event_e!(b)[k..l](f) =
*  next_event! (b) [k] (f) \/ ... \/ next_event! (b) [l] (f)
******************************************************************************)
Definition F_NUM_STRONG_NEXT_EVENT_E_def:
   F_NUM_STRONG_NEXT_EVENT_E(b,(k,SOME l),f) =
    RANGE_ITER (k,l) $F_OR (\n. F_NUM_STRONG_NEXT_EVENT(b,n,f))
End

(******************************************************************************
* next_event_a(b)[k..l](f) =
*  next_event (b) [k] (f) \/ ... \/ next_event (b) [l] (f)
******************************************************************************)
Definition F_NUM_WEAK_NEXT_EVENT_E_def:
   F_NUM_WEAK_NEXT_EVENT_E(b,(k,SOME l),f) =
    RANGE_ITER (k,l) $F_OR (\n. F_NUM_WEAK_NEXT_EVENT(b,n,f))
End

(******************************************************************************
* {r1} |=> {r2}! = {r1} |-> {T;r2}!
******************************************************************************)
Definition F_SKIP_STRONG_IMP_def:
   F_SKIP_STRONG_IMP(r1,r2) = F_STRONG_IMP(r1, S_CAT(S_TRUE, r2))
End

(******************************************************************************
* {r1} |=> {r2} = {r1} |-> {T;r2}
******************************************************************************)
Definition F_SKIP_WEAK_IMP_def:
   F_SKIP_WEAK_IMP(r1,r2) = F_WEAK_IMP(r1, S_CAT(S_TRUE, r2))
End

(******************************************************************************
* always{r} = {T[*]} |-> {r}
******************************************************************************)
Definition F_SERE_ALWAYS_def:
   F_SERE_ALWAYS r = F_WEAK_IMP(S_REPEAT S_TRUE, r)
End

(******************************************************************************
* never{r} = {T[*];r} |-> {F}
******************************************************************************)
Definition F_SERE_NEVER_def:
   F_SERE_NEVER r = F_WEAK_IMP(S_CAT(S_REPEAT S_TRUE, r), S_FALSE)
End

(******************************************************************************
* eventually! {r} = {T} |-> {T[*];r}!
******************************************************************************)
Definition F_SERE_STRONG_EVENTUALLY_def:
   F_SERE_STRONG_EVENTUALLY r =
    F_STRONG_IMP(S_TRUE, S_CAT(S_REPEAT S_TRUE, r))
End

(******************************************************************************
* within!(r1,b){r2} = {r1} |-> {r2&&b[=0];b}!
******************************************************************************)
Definition F_STRONG_WITHIN_def:
   F_STRONG_WITHIN (r1,b,r2) =
    F_STRONG_IMP(r1, S_CAT(S_AND(r2, S_EQ_REPEAT_ITER b 0), S_BOOL b))
End

(******************************************************************************
* within(r1,b){r2} = {r1} |-> {r2&&b[=0];b}
******************************************************************************)
Definition F_WEAK_WITHIN_def:
   F_WEAK_WITHIN (r1,b,r2) =
    F_WEAK_IMP(r1, S_CAT(S_AND(r2, S_EQ_REPEAT_ITER b 0), S_BOOL b))
End

(******************************************************************************
* within!_(r1,b){r2} = {r1} |-> {r2&&{b[=0];b}}!
******************************************************************************)
Definition F_STRONG_WITHIN_INC_def:
   F_STRONG_WITHIN_INC (r1,b,r2) =
    F_STRONG_IMP(r1, S_AND(r2, S_CAT(S_EQ_REPEAT_ITER b 0, S_BOOL b)))
End

(******************************************************************************
* within_(r1,b){r2} = {r1} |-> {r2&&{b[=0];b}}
******************************************************************************)
Definition F_WEAK_WITHIN_INC_def:
   F_WEAK_WITHIN_INC (r1,b,r2) =
    F_WEAK_IMP(r1, S_AND(r2, S_CAT(S_EQ_REPEAT_ITER b 0, S_BOOL b)))
End

(******************************************************************************
* whilenot!(b){r} = within!(T,b){r}
******************************************************************************)
Definition F_STRONG_WHILENOT_def:
   F_STRONG_WHILENOT (b,r) =  F_STRONG_WITHIN(S_TRUE,b,r)
End

(******************************************************************************
* whilenot(b){r} = within(T,b){r}
******************************************************************************)
Definition F_WEAK_WHILENOT_def:
   F_WEAK_WHILENOT (b,r) =  F_WEAK_WITHIN(S_TRUE,b,r)
End

(******************************************************************************
* whilenot!_(b){r} = within!_(T,b){r}
******************************************************************************)
Definition F_STRONG_WHILENOT_INC_def:
   F_STRONG_WHILENOT_INC (b,r) =  F_STRONG_WITHIN_INC(S_TRUE,b,r)
End

(******************************************************************************
* whilenot_(b){r} = within_(T,b){r}
******************************************************************************)
Definition F_WEAK_WHILENOT_INC_def:
   F_WEAK_WHILENOT_INC (b,r) =  F_WEAK_WITHIN_INC(S_TRUE,b,r)
End

(******************************************************************************
* Define weak clocking: f@clk = !(!f)@clk)
******************************************************************************)
Definition F_WEAK_CLOCK_def:
   F_WEAK_CLOCK(f,clk) = F_NOT(F_STRONG_CLOCK(F_NOT f, clk))
End
