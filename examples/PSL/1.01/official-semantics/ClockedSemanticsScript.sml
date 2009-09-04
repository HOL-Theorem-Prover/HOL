
(*****************************************************************************)
(* Create "ClockedSemanticsTheory" for clocked "SEM 1" and semantics         *)
(* F_SEM w c f means "w |=c= f"  in the clocked semantics                    *)
(* where w is a finite or infinite word i.e. w : ('prop -> bool)path         *)
(* and c is a boolean expression, i.e. c :                                   *)
(*                                                                           *)
(* Created Fri Dec 27 04:18:32 GMT 2002                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theory of paths and additional definitions of functions on lists
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
app load
 ["bossLib", "SyntaxTheory", "PathTheory", "KripkeTheory",
  "UnclockedSemanticsTheory", "rich_listTheory", "intLib","res_quanLib"];
open SyntaxTheory PathTheory KripkeTheory
     UnclockedSemanticsTheory        (* Needed for S_SEM w c (S_CLOCK(r,c1)) *)
     listTheory rich_listTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories of paths and lists
******************************************************************************)
open SyntaxTheory PathTheory KripkeTheory
     UnclockedSemanticsTheory        (* Needed for S_SEM w c (S_CLOCK(r,c1)) *)
     listTheory rich_listTheory res_quanLib;

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
* Start a new theory called ClockedSemantics
******************************************************************************)
val _ = new_theory "ClockedSemantics";

(******************************************************************************
* Clocked semantics of SEREs
* S_SEM w c r means "w is in the language of r in context of clock c"
******************************************************************************)
val S_SEM_def =
 Define
  `(S_SEM w c (S_BOOL b) =
     LENGTH w >= 1
     /\
     (!i :: (0 to (LENGTH w - 1)). B_SEM (ELEM w i) (B_NOT c))
     /\
     B_SEM (ELEM w (LENGTH w - 1)) (B_AND(c,b)))
   /\
   (S_SEM w c (S_CAT(r1,r2)) =
     ?w1 w2. (w = w1 <> w2) /\ S_SEM w1 c r1 /\ S_SEM w2 c r2)
   /\
   (S_SEM w c (S_FUSION(r1,r2)) =
     ?w1 w2 l. (w = w1 <> [l] <> w2) /\
               S_SEM (w1<>[l]) c r1 /\ S_SEM ([l]<>w2) c r2)
   /\
   (S_SEM w c (S_OR(r1,r2)) =
     S_SEM w c r1 \/ S_SEM w c r2)
   /\
   (S_SEM w c (S_AND(r1,r2)) =
     S_SEM w c r1 /\ S_SEM w c r2)
   /\
   (S_SEM w c (S_REPEAT r) =
     ?wlist. (w = CONCAT wlist) /\ EVERY (\w. S_SEM w c r) wlist)
   /\
   (S_SEM w c (S_CLOCK(r,c1)) =
     ?i :: (0 to LENGTH w).
       US_SEM (SEL w (0,i)) (S_CAT(S_REPEAT(S_BOOL(B_NOT c1)),S_BOOL c1))
       /\
       S_SEM (RESTN w i) c1 r)`;

(******************************************************************************
* Original clocked "SEM 1" semantics of Sugar formulas, partly unfolded
* (see commented out stuff) to avoid need for TFL hacks to prove termination.
******************************************************************************)
val OLD_F_SEM_def =
  Define
  `(OLD_F_SEM w c (F_BOOL b) = B_SEM (ELEM w 0) b)
    /\
    (OLD_F_SEM w c (F_NOT f) =
      ~(OLD_F_SEM w  c  f))
    /\
    (OLD_F_SEM w c (F_AND(f1,f2)) =
      OLD_F_SEM w c f1 /\ OLD_F_SEM w c f2)
    /\
    (OLD_F_SEM w c (F_NEXT f) =
      ?i :: (1 to LENGTH w).
        S_SEM (SEL w (1,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
        /\
        OLD_F_SEM (RESTN w i) c f)
    /\
    (OLD_F_SEM w c (F_UNTIL(f1,f2)) =
      ?k :: (0 to LENGTH w).
(*      OLD_F_SEM (RESTN w k) B_TRUE (F_BOOL c) /\                            *)
        B_SEM (ELEM w k) c      /\
        OLD_F_SEM (RESTN w k) c f2  /\
        !j :: (0 to k).
(*        OLD_F_SEM (RESTN w j) B_TRUE (F_BOOL c) ==> OLD_F_SEM (RESTN w j) c f1) *)
          B_SEM (ELEM w j) c ==> OLD_F_SEM (RESTN w j) c f1)
    /\
    (OLD_F_SEM w c (F_SUFFIX_IMP(r,f)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r
        ==>
        ?j :: (i to LENGTH w).
           S_SEM (SEL w (i,j)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
           /\
           OLD_F_SEM (RESTN w j) c f)
    /\
    (OLD_F_SEM w c (F_STRONG_IMP(r1,r2)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r1
        ==>
        ?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
    /\
    (OLD_F_SEM w c (F_WEAK_IMP(r1,r2)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r1
        ==>
        ((?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
         \/
         (!j :: (i to LENGTH w). ?w'. S_SEM (SEL w (i,j) <> w') c r2)))
    /\
    (OLD_F_SEM w c (F_ABORT (f,b)) =
      OLD_F_SEM w c f
      \/
(*    OLD_F_SEM w c (F_BOOL b)                                 *)
      B_SEM (ELEM w 0) b
      \/
      ?i :: (1 to LENGTH w).
(*      ?w'. OLD_F_SEM (RESTN w i) B_TRUE (F_BOOL(B_AND(c,b))) *)
        ?w'. B_SEM (ELEM w i) (B_AND(c,b))
             /\
             OLD_F_SEM (CAT(SEL w (0,i-1),w')) c f)
    /\
    (OLD_F_SEM w c (F_STRONG_CLOCK(f,c1)) =
      ?i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c1)),S_BOOL c1))
        /\
        OLD_F_SEM (RESTN w i) c1 f)`;

(******************************************************************************
* Derivation of "golden" form of clocked "SEM 1" semantics of Sugar formulas
******************************************************************************)
val OLD_F_SEM =
  store_thm
   ("OLD_F_SEM",
    ``(OLD_F_SEM w c (F_BOOL b) = B_SEM (ELEM w 0) b)
      /\
      (OLD_F_SEM w c (F_NOT f) =
        ~(OLD_F_SEM w  c  f))
      /\
      (OLD_F_SEM w c (F_AND(f1,f2)) =
        OLD_F_SEM w c f1 /\ OLD_F_SEM w c f2)
      /\
      (OLD_F_SEM w c (F_NEXT f) =
        ?i :: (1 to LENGTH w).
          S_SEM (SEL w (1,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
          /\
          OLD_F_SEM (RESTN w i) c f)
      /\
      (OLD_F_SEM w c (F_UNTIL(f1,f2)) =
        ?k :: (0 to LENGTH w).
          OLD_F_SEM (RESTN w k) B_TRUE (F_BOOL c) /\
          OLD_F_SEM (RESTN w k) c f2              /\
          !j :: (0 to k).
            OLD_F_SEM (RESTN w j) B_TRUE (F_BOOL c) ==> OLD_F_SEM (RESTN w j) c f1)
      /\
      (OLD_F_SEM w c (F_SUFFIX_IMP(r,f)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r
        ==>
        ?j :: (i to LENGTH w).
           S_SEM (SEL w (i,j)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
           /\
           OLD_F_SEM (RESTN w j) c f)
      /\
      (OLD_F_SEM w c (F_STRONG_IMP(r1,r2)) =
        !i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) c r1
          ==>
          ?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
      /\
      (OLD_F_SEM w c (F_WEAK_IMP(r1,r2)) =
        !i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) c r1
          ==>
          ((?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
           \/
           (!j :: (i to LENGTH w). ?w'. S_SEM (SEL w (i,j) <> w') c r2)))
      /\
      (OLD_F_SEM w c (F_ABORT (f,b)) =
        OLD_F_SEM w c f
        \/
        OLD_F_SEM w c (F_BOOL b)
        \/
        ?i :: (1 to LENGTH w).
          ?w'. OLD_F_SEM (RESTN w i) B_TRUE (F_BOOL(B_AND(c,b)))
               /\
               OLD_F_SEM (CAT(SEL w (0,i-1),w')) c f)
      /\
      (OLD_F_SEM w c (F_STRONG_CLOCK(f,c1)) =
        ?i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c1)),S_BOOL c1))
          /\
          OLD_F_SEM (RESTN w i) c1 f)``,
      RW_TAC arith_ss [OLD_F_SEM_def,ELEM_RESTN,B_SEM_def]);

(******************************************************************************
* Clocked "SEM 1" semantics of Sugar formulas, partly unfolded
* with additional |w|>0 for boolean formulas
* (see commented out stuff) to avoid need for TFL hacks to prove termination.
******************************************************************************)
val F_SEM_def =
  Define
  `(F_SEM w c (F_BOOL b) =
     LENGTH w > 0 /\ B_SEM (ELEM w 0) b)
    /\
    (F_SEM w c (F_NOT f) =
      ~(F_SEM w  c  f))
    /\
    (F_SEM w c (F_AND(f1,f2)) =
      F_SEM w c f1 /\ F_SEM w c f2)
    /\
    (F_SEM w c (F_NEXT f) =
      ?i :: (1 to LENGTH w).
        S_SEM (SEL w (1,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
        /\
        F_SEM (RESTN w i) c f)
    /\
    (F_SEM w c (F_UNTIL(f1,f2)) =
      ?k :: (0 to LENGTH w).
(*      F_SEM (RESTN w k) B_TRUE (F_BOOL c) /\                            *)
        B_SEM (ELEM w k) c /\
        F_SEM (RESTN w k) c f2  /\
        !j :: (0 to k).
(*        F_SEM (RESTN w j) B_TRUE (F_BOOL c) ==> F_SEM (RESTN w j) c f1) *)
          B_SEM (ELEM w j) c ==> F_SEM (RESTN w j) c f1)
    /\
    (F_SEM w c (F_SUFFIX_IMP(r,f)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r
        ==>
        ?j :: (i to LENGTH w).
           S_SEM (SEL w (i,j)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
           /\
           F_SEM (RESTN w j) c f)
    /\
    (F_SEM w c (F_STRONG_IMP(r1,r2)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r1
        ==>
        ?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
    /\
    (F_SEM w c (F_WEAK_IMP(r1,r2)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r1
        ==>
        ((?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
         \/
         (!j :: (i to LENGTH w). ?w'. S_SEM (SEL w (i,j) <> w') c r2)))
    /\
    (F_SEM w c (F_ABORT (f,b)) =
      F_SEM w c f
      \/
(*    F_SEM w c (F_BOOL b)                                 *)
      LENGTH w > 0 /\ B_SEM (ELEM w 0) b
      \/
      ?i :: (1 to LENGTH w).
(*      ?w'. F_SEM (RESTN w i) B_TRUE (F_BOOL(B_AND(c,b))) *)
        ?w'. B_SEM (ELEM w i) (B_AND(c,b))
             /\
             F_SEM (CAT(SEL w (0,i-1),w')) c f)
    /\
    (F_SEM w c (F_STRONG_CLOCK(f,c1)) =
      ?i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c1)),S_BOOL c1))
        /\
        F_SEM (RESTN w i) c1 f)`;

(******************************************************************************
* Derivation of "golden" form of clocked "SEM 1" semantics of Sugar formulas
******************************************************************************)
val F_SEM =
  store_thm
   ("F_SEM",
    ``(F_SEM w c (F_BOOL b) =
        LENGTH w > 0 /\ B_SEM (ELEM w 0) b)
      /\
      (F_SEM w c (F_NOT f) =
        ~(F_SEM w  c  f))
      /\
      (F_SEM w c (F_AND(f1,f2)) =
        F_SEM w c f1 /\ F_SEM w c f2)
      /\
      (F_SEM w c (F_NEXT f) =
        ?i :: (1 to LENGTH w).
          S_SEM (SEL w (1,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
          /\
          F_SEM (RESTN w i) c f)
      /\
      (F_SEM w c (F_UNTIL(f1,f2)) =
        ?k :: (0 to LENGTH w).
          F_SEM (RESTN w k) B_TRUE (F_BOOL c) /\
          F_SEM (RESTN w k) c f2              /\
          !j :: (0 to k).
            F_SEM (RESTN w j) B_TRUE (F_BOOL c) ==> F_SEM (RESTN w j) c f1)
      /\
      (F_SEM w c (F_SUFFIX_IMP(r,f)) =
      !i :: (0 to LENGTH w).
        S_SEM (SEL w (0,i)) c r
        ==>
        ?j :: (i to LENGTH w).
           S_SEM (SEL w (i,j)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))
           /\
           F_SEM (RESTN w j) c f)
      /\
      (F_SEM w c (F_STRONG_IMP(r1,r2)) =
        !i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) c r1
          ==>
          ?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
      /\
      (F_SEM w c (F_WEAK_IMP(r1,r2)) =
        !i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) c r1
          ==>
          ((?j :: (i to LENGTH w). S_SEM (SEL w (i,j)) c r2)
           \/
           (!j :: (i to LENGTH w). ?w'. S_SEM (SEL w (i,j) <> w') c r2)))
      /\
      (F_SEM w c (F_ABORT (f,b)) =
        F_SEM w c f
        \/
        F_SEM w c (F_BOOL b)
        \/
        ?i :: (1 to LENGTH w).
          ?w'. F_SEM (RESTN w i) B_TRUE (F_BOOL(B_AND(c,b)))
               /\
               F_SEM (CAT(SEL w (0,i-1),w')) c f)
      /\
      (F_SEM w c (F_STRONG_CLOCK(f,c1)) =
        ?i :: (0 to LENGTH w).
          S_SEM (SEL w (0,i)) B_TRUE (S_CAT(S_REPEAT(S_BOOL(B_NOT c1)),S_BOOL c1))
          /\
          F_SEM (RESTN w i) c1 f)``,
      RW_TAC arith_ss [F_SEM_def,ELEM_RESTN,B_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC (arith_ss ++ resq_SS)
             [GT_xnum_num_def,num_to_def,xnum_to_def,RESTN_FINITE,LENGTH_def,
              LENGTH_RESTN_INFINITE]
       THEN EQ_TAC
       THEN RW_TAC arith_ss []
       THEN RW_TAC arith_ss []
       THENL
        [Q.EXISTS_TAC `k`
          THEN RW_TAC arith_ss [FinitePathTheory.LENGTH_RESTN],
         Q.EXISTS_TAC `k`
          THEN RW_TAC arith_ss [FinitePathTheory.LENGTH_RESTN],
         REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `i`
          THEN RW_TAC arith_ss [FinitePathTheory.LENGTH_RESTN]
          THEN PROVE_TAC[],
         REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `i`
          THEN RW_TAC arith_ss [FinitePathTheory.LENGTH_RESTN]
          THEN PROVE_TAC[]]);

val _ = export_theory();
