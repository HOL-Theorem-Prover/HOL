(*****************************************************************************)
(* Definitions from LRM B.3 "Syntactic sugaring"                             *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(*
quietdec := true;
loadPath := "../official-semantics" :: !loadPath;
map load 
 ["SyntaxTheory", "FinitePathTheory", "PathTheory", 
   "UnclockedSemanticsTheory","intLib","res_quanTools"];
open SyntaxTheory FinitePathTheory PathTheory UnclockedSemanticsTheory
     listTheory rich_listTheory intLib res_quanTools;
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
open SyntaxTheory FinitePathTheory PathTheory UnclockedSemanticsTheory
     listTheory rich_listTheory intLib res_quanTools;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called Sugar1Defs with Sugar1Theory as a parent 
******************************************************************************)
val _ = new_theory "SyntacticSugar";

(******************************************************************************
* Additional SERE operators
******************************************************************************)

(******************************************************************************
* {r1} & {r2} = {{r1} && {r2;T[*]}} | {{r1;T[*]} && {r2}}
******************************************************************************)
val S_FLEX_AND_def =
 Define 
  `S_FLEX_AND(r1,r2) = 
    S_OR
     (S_AND(r1,S_CAT(r2, S_REPEAT(S_BOOL B_TRUE))),
      S_AND(S_CAT(r1,S_REPEAT(S_BOOL B_TRUE)), r2))`;

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
* S_RANGE_REPEAT r (i,j)) = r[*i..j] = {r[*i]} | {r[*(i+1)]} | ... | {r[*j]}
******************************************************************************)
val S_RANGE_REPEAT_def =
 Define
  `(S_RANGE_REPEAT r (i, SOME j) = RANGE_ITER(i, j) S_OR (S_REPEAT_ITER r))
   /\
   (S_RANGE_REPEAT r (i, NONE) = S_CAT(S_REPEAT_ITER r i, S_REPEAT r))`;

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
* S_RANGE_EQ_REPEAT r (i,j)) = r[=i..j] = {r[=i]} | {r[*=i+1)]} | ... | {r[=j]}
******************************************************************************)
val S_RANGE_EQ_REPEAT_def =
 Define
  `(S_RANGE_EQ_REPEAT b (i, SOME j) = 
     RANGE_ITER(i, j) S_OR (S_EQ_REPEAT_ITER b))
   /\
   (S_RANGE_EQ_REPEAT b (i, NONE) = 
     S_CAT(S_EQ_REPEAT_ITER b i, S_REPEAT(S_BOOL B_TRUE)))`;

(******************************************************************************
* b[->i] = {!b[*];b}[*i]
******************************************************************************)
val S_GOTO_REPEAT_ITER_def =
 Define
  `S_GOTO_REPEAT_ITER b = 
    S_REPEAT_ITER (S_CAT(S_REPEAT(S_BOOL(B_NOT b)),S_BOOL b))`;

(******************************************************************************
* S_RANGE_GOTO_REPEAT r (i,j)) = 
*  r[=i..j] = {r[=i]} | {r[*=i+1)]} | ... | {r[=j]}
******************************************************************************)
val S_RANGE_GOTO_REPEAT_def =
 Define
  `(S_RANGE_GOTO_REPEAT b (i, SOME j) = 
     RANGE_ITER(i, j) S_OR (S_GOTO_REPEAT_ITER b))
   /\
   (S_RANGE_GOTO_REPEAT b (i, NONE) = S_GOTO_REPEAT_ITER b i)`;


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
* Define weak clocking: f@clk = !(!f)@clk)
******************************************************************************)
val F_WEAK_CLOCK_def =
 Define
  `F_WEAK_CLOCK(f,clk) = F_NOT(F_STRONG_CLOCK(F_NOT f, clk))`;


val _ = export_theory();
