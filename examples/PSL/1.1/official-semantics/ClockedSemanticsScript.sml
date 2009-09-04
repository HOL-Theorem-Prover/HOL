
(*****************************************************************************)
(* Create "Clockedsugarsemanticstheory" containing clocked  semantics        *)
(* of PSL Version 1.1.                                                       *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theory of syntax, paths and models
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
map load
 ["SyntaxTheory","UnclockedSemanticsTheory"];
open SyntaxTheory PathTheory ModelTheory UnclockedSemanticsTheory;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories of sequences and lists
******************************************************************************)
open SyntaxTheory PathTheory ModelTheory UnclockedSemanticsTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called ClockedSemantics
******************************************************************************)
val _ = new_theory "ClockedSemantics";

(******************************************************************************
* pureDefine doesn't export definitions to theCompset (for EVAL).
******************************************************************************)
val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(******************************************************************************
* CLOCK_TICK v c formalises "v is a clock tick of c"
******************************************************************************)
val CLOCK_TICK_def =
 Define
  `CLOCK_TICK v c =
    LENGTH v > 0                    /\
    B_SEM (ELEM v (LENGTH v - 1)) c /\
    !i :: LESS(LENGTH v - 1). B_SEM (ELEM v i) (B_NOT c)`;

(******************************************************************************
* Clocked semantics of SEREs.
* S_SEM v r means "v is in the language of r" in the clocked semantics
* where v is a finite word, i.e. a list of letters: v :  ('a letter)list.
* S_SEM_def is a simple structural recursion for easy definition
* (see clause for ``S_SEM v (S_REPEAT r)``).
* Theorem S_SEM gives LRM v1.1 version.
******************************************************************************)
val S_SEM_def =
 pureDefine
  `(S_SEM v c (S_BOOL b) = CLOCK_TICK v c /\ B_SEM (ELEM v (LENGTH v - 1)) b)
   /\
   (S_SEM v c (S_CAT(r1,r2)) =
     ?v1 v2. (v = v1 <> v2) /\ S_SEM v1 c r1 /\ S_SEM v2 c r2)
   /\
   (S_SEM v c (S_FUSION(r1,r2)) =
     ?v1 v2 l. (v = v1 <> [l] <> v2) /\
               S_SEM (v1<>[l]) c r1 /\ S_SEM ([l]<>v2) c r2)
   /\
   (S_SEM v c (S_OR(r1,r2)) =
     S_SEM v c r1 \/ S_SEM v c r2)
   /\
   (S_SEM v c (S_AND(r1,r2)) =
     S_SEM v c r1 /\ S_SEM v c r2)
   /\
   (S_SEM v c S_EMPTY =
     (v = []))
   /\
   (S_SEM v c (S_REPEAT r) =
     ?vlist. (v = CONCAT vlist) /\ EVERY (\v. S_SEM v c r) vlist)
   /\
   (S_SEM v c (S_CLOCK(r,c1)) =
       S_SEM v c1 r)`;

(* Lemma for deriving theorem S_SEM below *)
val S_SEM_REPEAT =
 store_thm
  ("S_SEM_REPEAT",
   ``S_SEM v c (S_REPEAT r) =
      S_SEM v c S_EMPTY \/
      ?v1 v2.
       ~(v=[]) /\ (v = v1 <> v2) /\ S_SEM v1 c r /\ S_SEM v2 c (S_REPEAT r)``,
    Induct_on `v`
     THEN RW_TAC std_ss [S_SEM_def]
     THENL
      [Q.EXISTS_TAC `[]`
        THEN RW_TAC list_ss [FinitePathTheory.CONCAT_def],
       EQ_TAC
        THEN RW_TAC list_ss []
        THENL
         [Cases_on `vlist`
           THEN FULL_SIMP_TAC list_ss [FinitePathTheory.CONCAT_def]
           THEN Q.EXISTS_TAC `h'` THEN Q.EXISTS_TAC `CONCAT t`
           THEN PROVE_TAC[],
          Q.EXISTS_TAC `v1::vlist`
           THEN RW_TAC list_ss [FinitePathTheory.CONCAT_def]]]);


(******************************************************************************
* Clocked semantics of SEREs.
* S_SEM v r means "v is in the language of r" in the clocked semantics: v |=c r
* where v is a finite word, i.e. a list of letters: v :  ('a letter)list.
* S_SEM_def is a simple structural recursion for easy definition
* (see clause for ``S_SEM v (S_REPEAT r)``).
* Theorem S_SEM gives LRM v1.1 version.
******************************************************************************)
val S_SEM =
 store_thm
  ("S_SEM",
   ``(S_SEM v c (S_BOOL b) = CLOCK_TICK v c /\ B_SEM (ELEM v (LENGTH v - 1)) b)
     /\
     (S_SEM v c (S_CAT(r1,r2)) =
       ?v1 v2. (v = v1 <> v2) /\ S_SEM v1 c r1 /\ S_SEM v2 c r2)
     /\
     (S_SEM v c (S_FUSION(r1,r2)) =
       ?v1 v2 l. (v = v1 <> [l] <> v2) /\
                 S_SEM (v1<>[l]) c r1 /\ S_SEM ([l]<>v2) c r2)
     /\
     (S_SEM v c (S_OR(r1,r2)) =
       S_SEM v c r1 \/ S_SEM v c r2)
     /\
     (S_SEM v c (S_AND(r1,r2)) =
       S_SEM v c r1 /\ S_SEM v c r2)
     /\
     (S_SEM v c S_EMPTY =
       (v = []))
     /\
     (S_SEM v c (S_REPEAT r) =
       S_SEM v c S_EMPTY \/
        ?v1 v2.
         ~(v=[]) /\ (v = v1 <> v2) /\ S_SEM v1 c r /\ S_SEM v2 c (S_REPEAT r))
     /\
     (S_SEM v c (S_CLOCK(r,c1)) =
         S_SEM v c1 r)``,
   RW_TAC std_ss [S_SEM_def, GSYM S_SEM_REPEAT]);


(******************************************************************************
* F_SEM v c f means "v |=c f"  in the clocked semantics
* where v is a finite or infinite word i.e. v : ('prop letter)path
* F_SEM_def is unfolded version for easy definition.
* Theorem F_SEM gives version corresponding to LRM v1.1
******************************************************************************)
val F_SEM_def =
 Define
   `(F_SEM v c (F_NOT f) =
      ~(F_SEM (COMPLEMENT v) c f))
    /\
    (F_SEM v c (F_AND(f1,f2)) =
      F_SEM v c f1 /\ F_SEM v c f2)
    /\
    (F_SEM v c (F_STRONG_BOOL b) =
      ?j :: LESS(LENGTH v). CLOCK_TICK (SEL v (0,j)) c /\ B_SEM (ELEM v j) b)
    /\
    (F_SEM v c (F_WEAK_BOOL b) =
      !j :: LESS(LENGTH v).
        CLOCK_TICK (SEL (COMPLEMENT v) (0,j)) c ==> B_SEM (ELEM v j) b)
    /\
    (F_SEM v c (F_STRONG_SERE r) =
      ?j :: LESS(LENGTH v). S_SEM (SEL v (0,j)) c r)
(*
    /\
    (F_SEM v c (F_WEAK_SERE r) =
      !j :: LESS(LENGTH v).
       F_SEM (CAT(SEL v (0,j),TOP_OMEGA)) c (F_STRONG_SERE r))
*)
    /\
    (F_SEM v c (F_WEAK_SERE r) =
      !j :: LESS(LENGTH v).
        ?k :: LESS(LENGTH(CAT(SEL v (0,j),TOP_OMEGA))).
          S_SEM (SEL(CAT(SEL v (0,j),TOP_OMEGA)) (0,k)) c r)
    /\
    (F_SEM v c (F_NEXT f) =
      ?j k :: LESS(LENGTH v).
        j < k                        /\
        CLOCK_TICK (SEL v (0,j)) c   /\
        CLOCK_TICK (SEL v (j+1,k)) c /\
        F_SEM (RESTN v k) c f)
    /\
    (F_SEM v c (F_UNTIL(f1,f2)) =
      ?k :: LESS(LENGTH v).
        B_SEM (ELEM v k) c /\
        F_SEM (RESTN v k) c f2 /\
        !j :: LESS k. B_SEM (ELEM (COMPLEMENT v) j) c ==> F_SEM (RESTN v j) c f1)
    /\
(* Contains j=0 bug spoteed by Thomas Turk
    (F_SEM v c (F_ABORT (f,b)) =
      F_SEM v c f
      \/
      ?j :: LESS(LENGTH v).
         B_SEM (ELEM v j) b /\ F_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) c f)
*)
    (F_SEM v c (F_ABORT (f,b)) =
      F_SEM v c f
      \/
      ?j :: LESS(LENGTH v).
         B_SEM (ELEM v j) b
         /\
         if j=0 then F_SEM TOP_OMEGA c f
                else F_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) c f)
    /\
    (F_SEM v c (F_CLOCK(f,c1)) =
      F_SEM v c1 f)
    /\
    (F_SEM v c (F_SUFFIX_IMP(r,f)) =
      !j :: LESS(LENGTH v).
        S_SEM (SEL (COMPLEMENT v) (0,j)) c r ==> F_SEM (RESTN v j) c f)`;

(******************************************************************************
* F_SEM v c f means "v |=c f"  in the clocked semantics
* where v is a finite or infinite word i.e. v : ('prop letter)path
* F_SEM_def is unfolded version for easy definition.
* Theorem F_SEM gives version corresponding to LRM v1.1
******************************************************************************)
val F_SEM =
 store_thm
  ("F_SEM",
   ``(F_SEM v c (F_NOT f) =
       ~(F_SEM (COMPLEMENT v) c f))
     /\
     (F_SEM v c (F_AND(f1,f2)) =
       F_SEM v c f1 /\ F_SEM v c f2)
     /\
     (F_SEM v c (F_STRONG_BOOL b) =
       ?j :: LESS(LENGTH v). CLOCK_TICK (SEL v (0,j)) c /\ B_SEM (ELEM v j) b)
     /\
     (F_SEM v c (F_WEAK_BOOL b) =
       !j :: LESS(LENGTH v).
         CLOCK_TICK (SEL (COMPLEMENT v) (0,j)) c ==> B_SEM (ELEM v j) b)
     /\
     (F_SEM v c (F_STRONG_SERE r) =
       ?j :: LESS(LENGTH v). S_SEM (SEL v (0,j)) c r)
     /\
     (F_SEM v c (F_WEAK_SERE r) =
       !j :: LESS(LENGTH v).
        F_SEM (CAT(SEL v (0,j),TOP_OMEGA)) c (F_STRONG_SERE r))
(*
     /\
     (F_SEM v c (F_WEAK_SERE r) =
       !j :: LESS(LENGTH v).
         ?k :: LESS(LENGTH(CAT(SEL v (0,j),TOP_OMEGA))).
           S_SEM (SEL(CAT(SEL v (0,j),TOP_OMEGA)) (0,k)) c r)
*)
     /\
     (F_SEM v c (F_NEXT f) =
       ?j k :: LESS(LENGTH v).
         j < k                        /\
         CLOCK_TICK (SEL v (0,j)) c   /\
         CLOCK_TICK (SEL v (j+1,k)) c /\
         F_SEM (RESTN v k) c f)
     /\
     (F_SEM v c (F_UNTIL(f1,f2)) =
       ?k :: LESS(LENGTH v).
         B_SEM (ELEM v k) c /\
         F_SEM (RESTN v k) c f2 /\
         !j :: LESS k. B_SEM (ELEM (COMPLEMENT v) j) c ==> F_SEM (RESTN v j) c f1)
     /\
(* Contains j=0 bug spoteed by Thomas Turk
    (F_SEM v c (F_ABORT (f,b)) =
      F_SEM v c f
      \/
      ?j :: LESS(LENGTH v).
         B_SEM (ELEM v j) b /\ F_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) c f)
*)
    (F_SEM v c (F_ABORT (f,b)) =
      F_SEM v c f
      \/
      ?j :: LESS(LENGTH v).
         B_SEM (ELEM v j) b
         /\
         if j=0 then F_SEM TOP_OMEGA c f
                else F_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) c f)
     /\
     (F_SEM v c (F_CLOCK(f,c1)) =
       F_SEM v c1 f)
     /\
     (F_SEM v c (F_SUFFIX_IMP(r,f)) =
       !j :: LESS(LENGTH v).
         S_SEM (SEL (COMPLEMENT v) (0,j)) c r ==> F_SEM (RESTN v j) c f)``,
   RW_TAC std_ss [F_SEM_def]);

val _ = export_theory();

