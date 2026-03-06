
(*****************************************************************************)
(* Create "RewritesTheory" with rewrites semantics from LRM Version 1.1      *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(*
quietdec := true;
map load
 ["SyntacticSugarTheory","ClockedSemanticsTheory"];
quietdec := false;
*)

Theory Rewrites
Ancestors
  SyntacticSugar ClockedSemantics

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Version 1.1 rules for compiling clocked SEREs to unclocked SEREs
******************************************************************************)
Definition S_CLOCK_COMP_def:
   (S_CLOCK_COMP c (S_BOOL b) =
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
   (S_CLOCK_COMP c S_EMPTY =
     S_EMPTY)
   /\
   (S_CLOCK_COMP c (S_REPEAT r) =
     S_REPEAT(S_CLOCK_COMP c r))
   /\
   (S_CLOCK_COMP c (S_CLOCK(r, c1)) =
     S_CLOCK_COMP c1 r)
End

(******************************************************************************
* Some abbreviations needed for definition of F_CLOCK_COMP
******************************************************************************)

(******************************************************************************
* Strongly on first posedge.
* Exists a posedge and true on it: [!c U (c /\ f)]
******************************************************************************)
Definition F_U_CLOCK_def:
   F_U_CLOCK c f = F_UNTIL(F_WEAK_BOOL(B_NOT c),F_AND(F_WEAK_BOOL c, f))
End

(******************************************************************************
* Weakly on first posedge.
* On first posedge, if there is a posedge: [!c W (c /\ f)]
******************************************************************************)
Definition F_W_CLOCK_def:
   F_W_CLOCK c f = F_W(F_WEAK_BOOL(B_NOT c),F_AND(F_WEAK_BOOL c, f))
End

(******************************************************************************
* Version 1.1 rules for compiling clocked formulas to unclocked formulas
******************************************************************************)
Definition F_CLOCK_COMP_def:
   (F_CLOCK_COMP c (F_STRONG_BOOL b) =
     F_U_CLOCK c (F_WEAK_BOOL b))
   /\
   (F_CLOCK_COMP c (F_WEAK_BOOL b) =
     F_W_CLOCK c (F_WEAK_BOOL b))
   /\
   (F_CLOCK_COMP c (F_NOT f) =
     F_NOT(F_CLOCK_COMP c f))
   /\
   (F_CLOCK_COMP c (F_AND(f1,f2)) =
     F_AND(F_CLOCK_COMP c f1, F_CLOCK_COMP c f2))
   /\
   (F_CLOCK_COMP c (F_NEXT f) =
     F_U_CLOCK c (F_NEXT(F_U_CLOCK c (F_CLOCK_COMP c f))))
   /\
   (F_CLOCK_COMP c (F_UNTIL(f1,f2)) =
     F_UNTIL(F_IMPLIES(F_WEAK_BOOL c, F_CLOCK_COMP c f1),
             F_AND(F_WEAK_BOOL c, F_CLOCK_COMP c f2)))
   /\
   (F_CLOCK_COMP c (F_ABORT (f,b)) =
     F_ABORT(F_CLOCK_COMP c f, b))
   /\
   (F_CLOCK_COMP c (F_CLOCK(f,c1)) =
     F_CLOCK_COMP c1 f)
   /\
   (F_CLOCK_COMP c (F_SUFFIX_IMP(r,f)) =
     F_SUFFIX_IMP(S_CLOCK_COMP c r, F_CLOCK_COMP c f))
   /\
   (F_CLOCK_COMP c (F_STRONG_SERE r) =
     F_STRONG_SERE(S_CLOCK_COMP c r))
   /\
   (F_CLOCK_COMP c (F_WEAK_SERE r) =
     F_WEAK_SERE(S_CLOCK_COMP c r))
End
