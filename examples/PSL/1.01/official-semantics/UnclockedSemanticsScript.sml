
(*****************************************************************************)
(* Create "UnclockedSugarSemanticsTheory" containing unclocked "SEM 1"       *)
(* semantics of the basic language.                                          *)
(*                                                                           *)
(* Created Wed Dec 25 23:02:12 GMT 2002                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theory of finite and infinite sequences and additional definitions of
functions on lists (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
map load
 ["SyntaxTheory", "SyntacticSugarTheory", "PathTheory", "KripkeTheory",
  "rich_listTheory", "intLib"];

open SyntaxTheory SyntacticSugarTheory
     PathTheory KripkeTheory listTheory rich_listTheory intLib;

val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories of sequences and lists
******************************************************************************)
open SyntaxTheory SyntacticSugarTheory PathTheory KripkeTheory
     listTheory rich_listTheory intLib;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called UnclockedSugarSemantics
******************************************************************************)
val _ = new_theory "UnclockedSemantics";

(******************************************************************************
* pureDefine doesn't export definitions to theCompset (for EVAL).
******************************************************************************)
val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(******************************************************************************
* B_SEM l b means "l |= b" where l is a letter, i.e. l : 'prop -> bool
******************************************************************************)
val B_SEM_def =
 Define
  `(B_SEM l (B_PROP(p:'prop)) = p IN l)
   /\
   (B_SEM l (B_NOT b)         = ~(B_SEM l b))
   /\
   (B_SEM l (B_AND(b1,b2))    = B_SEM l b1 /\ B_SEM l b2)`;

val B_SEM =
 store_thm
  ("B_SEM",
   ``(B_SEM l (B_PROP p)     = p IN l)
     /\
     (B_SEM l B_TRUE         = T)
     /\
     (B_SEM l B_FALSE        = F)
     /\
     (B_SEM l (B_NOT b)      = ~(B_SEM l b))
     /\
     (B_SEM l (B_AND(b1,b2)) = B_SEM l b1 /\ B_SEM l b2)
     /\
     (B_SEM l (B_OR(b1,b2)) = B_SEM l b1 \/ B_SEM l b2)``,
   RW_TAC std_ss [B_SEM_def,B_OR_def,B_TRUE_def,B_FALSE_def]
    THEN PROVE_TAC[]);

(******************************************************************************
* Unclocked "SEM 1" semantics of SEREs.
* US_SEM w r means "w is in the language of r" in the unclocked semantics
* where w is a word, i.e. a list of letters: w : ('prop -> bool)list
******************************************************************************)
val US_SEM_def =
 pureDefine
  `(US_SEM w (S_BOOL b) = (LENGTH w = 1) /\ B_SEM (ELEM w 0) b)
   /\
   (US_SEM w (S_CAT(r1,r2)) =
     ?w1 w2. (w = w1 <> w2) /\ US_SEM w1 r1 /\ US_SEM w2 r2)
   /\
   (US_SEM w (S_FUSION(r1,r2)) =
     ?w1 w2 l. (w = w1 <> [l] <> w2) /\
               US_SEM (w1<>[l]) r1 /\ US_SEM ([l]<>w2) r2)
   /\
   (US_SEM w (S_OR(r1,r2)) =
     US_SEM w r1 \/ US_SEM w r2)
   /\
   (US_SEM w (S_AND(r1,r2)) =
     US_SEM w r1 /\ US_SEM w r2)
   /\
   (US_SEM w (S_REPEAT r) =
     ?wlist. (w = CONCAT wlist) /\ EVERY (\w. US_SEM w r) wlist)`;

(******************************************************************************
* Original unclocked "SEM 1" semantics of Sugar formulas
* UF_SEM w f means "w |= f"  in the unclocked semantics
* where w is a finite or infinite word i.e. w : ('prop -> bool)path
******************************************************************************)
val OLD_UF_SEM_def =
 Define
   `(OLD_UF_SEM w (F_BOOL b) =
      B_SEM (ELEM w 0) b)
    /\
    (OLD_UF_SEM w (F_NOT f) =
      ~(OLD_UF_SEM w f))
    /\
    (OLD_UF_SEM w (F_AND(f1,f2)) =
      OLD_UF_SEM w f1 /\ OLD_UF_SEM w f2)
    /\
    (OLD_UF_SEM w (F_NEXT f) =
      LENGTH w > 1 /\ OLD_UF_SEM (RESTN w 1) f)
    /\
    (OLD_UF_SEM w (F_UNTIL(f1,f2)) =
      ?k :: (0 to LENGTH w).
        OLD_UF_SEM (RESTN w k) f2 /\ !j :: (0 to k). OLD_UF_SEM (RESTN w j) f1)
    /\
    (OLD_UF_SEM w (F_SUFFIX_IMP(r,f)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r ==> OLD_UF_SEM (RESTN w j) f)
    /\
    (OLD_UF_SEM w (F_STRONG_IMP(r1,r2)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r1
        ==>
        ?k :: (j to LENGTH w). US_SEM (SEL w (j,k)) r2)
    /\
    (OLD_UF_SEM w (F_WEAK_IMP(r1,r2)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r1
        ==>
        ((?k :: (j to LENGTH w). US_SEM (SEL w (j,k)) r2)
         \/
         (!k :: (j to LENGTH w). ?w'. US_SEM (SEL w (j,k) <> w') r2)))
    /\
    (OLD_UF_SEM w (F_ABORT (f,b)) =
      OLD_UF_SEM w f
      \/
      OLD_UF_SEM w (F_BOOL b)
      \/
      ?j :: (1 to LENGTH w).
        ?w'. OLD_UF_SEM (RESTN w j) (F_BOOL b)
             /\
             OLD_UF_SEM (CAT(SEL w (0,j-1),w')) f)`;

(******************************************************************************
* Unclocked "SEM 1" semantics of Sugar formulas
* with additional |w|>0 for boolean formulas
* UF_SEM w f means "w |= f"  in the unclocked semantics
* where w is a finite or infinite word i.e. w : ('prop -> bool)path
******************************************************************************)
val UF_SEM_def =
 Define
   `(UF_SEM w (F_BOOL b) =
      LENGTH w > 0 /\ B_SEM (ELEM w 0) b)
    /\
    (UF_SEM w (F_NOT f) =
      ~(UF_SEM w f))
    /\
    (UF_SEM w (F_AND(f1,f2)) =
      UF_SEM w f1 /\ UF_SEM w f2)
    /\
    (UF_SEM w (F_NEXT f) =
      LENGTH w > 1 /\ UF_SEM (RESTN w 1) f)
    /\
    (UF_SEM w (F_UNTIL(f1,f2)) =
      ?k :: (0 to LENGTH w).
        UF_SEM (RESTN w k) f2 /\ !j :: (0 to k). UF_SEM (RESTN w j) f1)
    /\
    (UF_SEM w (F_SUFFIX_IMP(r,f)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r ==> UF_SEM (RESTN w j) f)
    /\
    (UF_SEM w (F_STRONG_IMP(r1,r2)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r1
        ==>
        ?k :: (j to LENGTH w). US_SEM (SEL w (j,k)) r2)
    /\
    (UF_SEM w (F_WEAK_IMP(r1,r2)) =
      !j :: (0 to LENGTH w).
        US_SEM (SEL w (0,j)) r1
        ==>
        ((?k :: (j to LENGTH w). US_SEM (SEL w (j,k)) r2)
         \/
         (!k :: (j to LENGTH w). ?w'. US_SEM (SEL w (j,k) <> w') r2)))
    /\
    (UF_SEM w (F_ABORT (f,b)) =
      UF_SEM w f
      \/
      UF_SEM w (F_BOOL b)
      \/
      ?j :: (1 to LENGTH w).
        ?w'. UF_SEM (RESTN w j) (F_BOOL b)
             /\
             UF_SEM (CAT(SEL w (0,j-1),w')) f)`;

(******************************************************************************
* PATH M p is true iff p is a path with respect to transition relation M.R
******************************************************************************)
val PATH_def = Define `PATH M p s = IS_INFINITE p /\ (ELEM p 0 = s) /\ (!n. M.R(ELEM p n, ELEM p (n+1)))`;

(******************************************************************************
* O_SEM M s f means "M, s |= f"
******************************************************************************)
val O_SEM_def =
 Define
  `(O_SEM M (O_BOOL b) s = B_SEM (M.L s) b)
   /\
   (O_SEM M (O_NOT f) s = ~(O_SEM M f s))
   /\
   (O_SEM M (O_AND(f1,f2)) s = O_SEM M f1 s /\ O_SEM M f2 s)
   /\
   (O_SEM M (O_EX f) s =
     ?p. PATH M p s /\ O_SEM M f (ELEM p 1))
   /\
   (O_SEM M (O_EU(f1,f2)) s =
     ?p. PATH M p s /\
         ?k :: (0 to LENGTH p). O_SEM M f2 (ELEM p k) /\ !j. j < k ==> O_SEM M f1 (ELEM p j))
   /\
   (O_SEM M (O_EG f) s =
     ?p. PATH M p s /\ !j :: (0 to LENGTH p). O_SEM M f (ELEM p j))`;

val _ = export_theory();

