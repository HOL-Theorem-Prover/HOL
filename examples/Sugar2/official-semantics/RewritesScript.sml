
(*****************************************************************************)
(* Create "RewritesTheory" containing SEM_1 rewrites semantics               *)
(*                                                                           *)
(* Created Wed Jan 1 2003                                                    *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(*
quietdec := true;
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
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS = 
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [num_to_def,xnum_to_def,IN_DEF,num_to_def,xnum_to_def,LENGTH_def]];

(******************************************************************************
* Start a new theory called UnclockedSugarSemantics
******************************************************************************)
val _ = new_theory "Rewrites";

(******************************************************************************
* SEM_1 rules for compiling clocked SEREs to unclocked SEREs
******************************************************************************)
val S_CLOCK_COMP_def =
 Define
  `(S_CLOCK_COMP c (S_BOOL b) = 
     (S_CAT (S_REPEAT (S_BOOL (B_NOT c)),S_BOOL(B_AND(c, b)))))
   /\
   (S_CLOCK_COMP c (S_CAT(r1,r2)) =  
     S_CAT(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_FUSION(r1,r2)) = 
     S_FUSION(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_OR(r1,r2)) = 
     S_OR(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_AND(r1,r2))  = 
     S_AND(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (S_CLOCK_COMP c (S_REPEAT r) = 
     S_REPEAT(S_CLOCK_COMP c r))
   /\
   (S_CLOCK_COMP c (S_CLOCK(r, c1)) = 
     (S_CAT (S_REPEAT (S_BOOL (B_NOT c1)), 
             S_FUSION(S_BOOL c1, S_CLOCK_COMP c1 r))))`;

(******************************************************************************
* Some abbreviations needed for definition of F_CLOCK_COMP
******************************************************************************)

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
* Strongly on first posedge.
* Exists a posedge and true on it: [!c U (c /\ f)]
******************************************************************************)
val F_U_CLOCK_def =
 Define
  `F_U_CLOCK c f = F_UNTIL(F_BOOL(B_NOT c),F_AND(F_BOOL c, f))`;

(******************************************************************************
* Weakly on first posedge.
* On first posedge, if there is a posedge: [!c U (c /\ f)]
******************************************************************************)
val F_W_CLOCK_def =
 Define
  `F_W_CLOCK c f = F_W(F_BOOL(B_NOT c),F_AND(F_BOOL c, f))`;

(******************************************************************************
* Non-standard rewrite for abort that avoids need for assuming w_0 |= c
******************************************************************************)
val F_INIT_CLOCK_COMP_def =
 Define
  `(F_INIT_CLOCK_COMP c (F_BOOL b) = 
     F_BOOL b)
   /\
   (F_INIT_CLOCK_COMP c (F_NOT f) = 
     F_NOT(F_INIT_CLOCK_COMP c f))
   /\
   (F_INIT_CLOCK_COMP c (F_AND(f1,f2)) = 
     F_AND(F_INIT_CLOCK_COMP c f1, F_INIT_CLOCK_COMP c f2))
   /\
   (F_INIT_CLOCK_COMP c (F_NEXT f) = 
     F_NEXT(F_U_CLOCK c (F_INIT_CLOCK_COMP c f)))
   /\
   (F_INIT_CLOCK_COMP c (F_UNTIL(f1,f2)) = 
     F_UNTIL(F_IMPLIES(F_BOOL c, F_INIT_CLOCK_COMP c f1), 
             F_AND(F_BOOL c, F_INIT_CLOCK_COMP c f2)))
   /\
   (F_INIT_CLOCK_COMP c (F_SUFFIX_IMP(r,f)) = 
     F_SUFFIX_IMP(S_CLOCK_COMP c r, F_U_CLOCK c (F_INIT_CLOCK_COMP c f)))  
(*     F_SUFFIX_IMP(S_CLOCK_COMP c r, F_INIT_CLOCK_COMP c f))  *)
   /\
   (F_INIT_CLOCK_COMP c (F_STRONG_IMP(r1,r2)) = 
     F_STRONG_IMP (S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (F_INIT_CLOCK_COMP c (F_WEAK_IMP(r1,r2)) = 
     F_WEAK_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (F_INIT_CLOCK_COMP c (F_ABORT (f,b)) =
(*     F_ABORT(F_INIT_CLOCK_COMP c f, B_AND(c,b)))                 *)
     F_OR(F_BOOL b, F_ABORT(F_INIT_CLOCK_COMP c f, B_AND(c,b)))) 
   /\
   (F_INIT_CLOCK_COMP c (F_STRONG_CLOCK(f,c1)) =   
     F_U_CLOCK c1 (F_INIT_CLOCK_COMP c1 f))`;

(******************************************************************************
* SEM_1 rules for compiling clocked FL formulas to unclocked formulas
******************************************************************************)
val F_CLOCK_COMP_def =
 Define
  `(F_CLOCK_COMP c (F_BOOL b) = 
     F_BOOL b)
   /\
   (F_CLOCK_COMP c (F_NOT f) = 
     F_NOT(F_CLOCK_COMP c f))
   /\
   (F_CLOCK_COMP c (F_AND(f1,f2)) = 
     F_AND(F_CLOCK_COMP c f1, F_CLOCK_COMP c f2))
   /\
   (F_CLOCK_COMP c (F_NEXT f) = 
     F_NEXT(F_U_CLOCK c (F_CLOCK_COMP c f)))
   /\
   (F_CLOCK_COMP c (F_UNTIL(f1,f2)) = 
     F_UNTIL(F_IMPLIES(F_BOOL c, F_CLOCK_COMP c f1), 
             F_AND(F_BOOL c, F_CLOCK_COMP c f2)))
   /\
   (F_CLOCK_COMP c (F_SUFFIX_IMP(r,f)) = 
     F_SUFFIX_IMP(S_CLOCK_COMP c r, F_U_CLOCK c (F_CLOCK_COMP c f)))  
(*     F_SUFFIX_IMP(S_CLOCK_COMP c r, F_CLOCK_COMP c f)) *)
   /\
   (F_CLOCK_COMP c (F_STRONG_IMP(r1,r2)) = 
     F_STRONG_IMP (S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (F_CLOCK_COMP c (F_WEAK_IMP(r1,r2)) = 
     F_WEAK_IMP(S_CLOCK_COMP c r1, S_CLOCK_COMP c r2))
   /\
   (F_CLOCK_COMP c (F_ABORT (f,b)) =
     F_ABORT(F_CLOCK_COMP c f, B_AND(c,b)))                
(*     F_OR(F_BOOL b, F_ABORT(F_CLOCK_COMP c f, B_AND(c,b)))) *)
   /\
   (F_CLOCK_COMP c (F_STRONG_CLOCK(f,c1)) =   
     F_U_CLOCK c1 (F_CLOCK_COMP c1 f))`;
 
val _ = export_theory();

