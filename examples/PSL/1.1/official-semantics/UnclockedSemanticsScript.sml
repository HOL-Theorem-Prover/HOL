
(*****************************************************************************)
(* Create "UnclockedSemanticsTheory" containing unclocked  semantics         *)
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
loadPath                                  (* Add path to loadPath            *)
 :=
 "../../path" :: !loadPath;
map load
 ["SyntaxTheory","PSLPathTheory","ModelTheory"];
quietdec := false;
*)

Theory UnclockedSemantics
Ancestors
  Syntax PSLPath Model

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = ParseExtras.temp_loose_equality()

(* Moved to ModelScript.sml
(******************************************************************************
* A letter is either TOP, or BOTTOM
* or a set of atomic propositions repersenting a state
******************************************************************************)
val letter_def =
 Hol_datatype
  `letter = TOP | BOTTOM | STATE of ('prop -> bool)`;
*)

(******************************************************************************
* B_SEM l b means "l ||= b" where l is a letter
******************************************************************************)
Definition B_SEM_def:
   (B_SEM TOP b = T)
   /\
   (B_SEM BOTTOM b = F)
   /\
   (B_SEM (STATE s) (B_PROP(p:'prop)) = p IN s)
   /\
   (B_SEM (STATE s) B_TRUE = T)
   /\
   (B_SEM (STATE s) B_FALSE = F)
   /\
   (B_SEM (STATE s) (B_NOT b) = ~(B_SEM (STATE s) b))
   /\
   (B_SEM (STATE s) (B_AND(b1,b2)) = B_SEM (STATE s) b1 /\ B_SEM (STATE s) b2)
End

(******************************************************************************
* Unclocked semantics of SEREs.
* US_SEM v r means "v is in the language of r" in the unclocked semantics
* where v is a finite word, i.e. a list of letters: v :  ('a letter)list.
* US_SEM_def is a simple structural recursion for easy definition
* (see clause for ``US_SEM v (S_REPEAT r)``).
* Theorem US_SEM gives version corresponding to LRM Version 1.1.
******************************************************************************)
Definition US_SEM_def[nocompute]:
   (US_SEM v (S_BOOL b) = (LENGTH v = 1) /\ B_SEM (ELEM v 0) b)
   /\
   (US_SEM v (S_CAT(r1,r2)) =
     ?v1 v2. (v = v1 <> v2) /\ US_SEM v1 r1 /\ US_SEM v2 r2)
   /\
   (US_SEM v (S_FUSION(r1,r2)) =
     ?v1 v2 l. (v = v1 <> [l] <> v2) /\
               US_SEM (v1<>[l]) r1 /\ US_SEM ([l]<>v2) r2)
   /\
   (US_SEM v (S_OR(r1,r2)) =
     US_SEM v r1 \/ US_SEM v r2)
   /\
   (US_SEM v (S_AND(r1,r2)) =
     US_SEM v r1 /\ US_SEM v r2)
   /\
   (US_SEM v S_EMPTY =
     (v = []))
   /\
   (US_SEM v (S_REPEAT r) =
     ?vlist. (v = CONCAT vlist) /\ EVERY (\v. US_SEM v r) vlist)
End

(* Lemma for deriving theorem US_SEM below *)
Theorem US_SEM_REPEAT:
     US_SEM v (S_REPEAT r) =
      US_SEM v S_EMPTY \/
      ?v1 v2.
       ~(v=[]) /\ (v = v1 <> v2) /\ US_SEM v1 r /\ US_SEM v2 (S_REPEAT r)
Proof
    Induct_on `v`
     THEN RW_TAC std_ss [US_SEM_def]
     THENL
      [Q.EXISTS_TAC `[]`
        THEN RW_TAC list_ss [FinitePSLPathTheory.CONCAT_def],
       EQ_TAC
        THEN RW_TAC list_ss []
        THENL
         [Cases_on `vlist`
           THEN FULL_SIMP_TAC list_ss [FinitePSLPathTheory.CONCAT_def]
           THEN Q.EXISTS_TAC `h'` THEN Q.EXISTS_TAC `CONCAT t`
           THEN PROVE_TAC[],
          Q.EXISTS_TAC `v1::vlist`
           THEN RW_TAC list_ss [FinitePSLPathTheory.CONCAT_def]]]
QED

(******************************************************************************
* Unclocked semantics of SEREs.
* US_SEM v r means "v is in the language of r" in the unclocked semantics
* where v is a finite word, i.e. a list of letters: v :  ('a letter)list.
* US_SEM_def is a simple structural recursion for easy definition
* (see clause for ``US_SEM v (S_REPEAT r)``).
* Theorem US_SEM gives version corresponding to LRM Version 1.1.
******************************************************************************)
Theorem US_SEM:
     (US_SEM v (S_BOOL b) = (LENGTH v = 1) /\ B_SEM (ELEM v 0) b)
     /\
     (US_SEM v (S_CAT(r1,r2)) =
       ?v1 v2. (v = v1 <> v2) /\ US_SEM v1 r1 /\ US_SEM v2 r2)
     /\
     (US_SEM v (S_FUSION(r1,r2)) =
       ?v1 v2 l. (v = v1 <> [l] <> v2) /\
                 US_SEM (v1<>[l]) r1 /\ US_SEM ([l]<>v2) r2)
     /\
     (US_SEM v (S_OR(r1,r2)) =
       US_SEM v r1 \/ US_SEM v r2)
     /\
     (US_SEM v (S_AND(r1,r2)) =
       US_SEM v r1 /\ US_SEM v r2)
     /\
     (US_SEM v S_EMPTY =
       (v = []))
     /\
     (US_SEM v (S_REPEAT r) =
       US_SEM v S_EMPTY \/
        ?v1 v2.
         ~(v=[]) /\ (v = v1 <> v2) /\ US_SEM v1 r /\ US_SEM v2 (S_REPEAT r))
Proof
   RW_TAC std_ss [US_SEM_def, GSYM US_SEM_REPEAT]
QED

(******************************************************************************
* Complement a path
******************************************************************************)
Definition COMPLEMENT_LETTER_def:
   (COMPLEMENT_LETTER TOP      = BOTTOM) /\
   (COMPLEMENT_LETTER BOTTOM   = TOP)    /\
   (COMPLEMENT_LETTER(STATE s) = STATE s)
End

(******************************************************************************
* Complement a path
******************************************************************************)
Definition COMPLEMENT_def:
   (COMPLEMENT(FINITE p)   = FINITE(MAP COMPLEMENT_LETTER p)) /\
   (COMPLEMENT(INFINITE f) = INFINITE(COMPLEMENT_LETTER o f))
End

(******************************************************************************
* \top^\omega
******************************************************************************)
Definition TOP_OMEGA_def:
  TOP_OMEGA = INFINITE(\n. TOP)
End

(******************************************************************************
* LESS m is predicate to test if a number is less than m
* LESS : num -> num -> bool
* LESSX m is predicate to test if a number is less than extended number m
* LESSX : xnum -> num -> bool
* Now defined in PSLPathTheory
******************************************************************************)

(******************************************************************************
* UF_SEM v f means "v |= f"  in the unclocked semantics
* where v is a finite or infinite word i.e. v : ('prop -> bool)path
* UF_SEM_def is unfolded version for easy definition.
* Theorem UF_SEM gives version corresponding to LRM v1.1
******************************************************************************)
Definition UF_SEM_def:
    (UF_SEM v (F_NOT f) =
      ~(UF_SEM (COMPLEMENT v) f))
    /\
    (UF_SEM v (F_AND(f1,f2)) =
      UF_SEM v f1 /\ UF_SEM v f2)
    /\
    (UF_SEM v (F_STRONG_BOOL b) =
      (LENGTH v > 0) /\ B_SEM (ELEM v 0) b)
    /\
    (UF_SEM v (F_WEAK_BOOL b) =
      (LENGTH v = XNUM 0) \/ B_SEM (ELEM v 0) b)
    /\
    (UF_SEM v (F_STRONG_SERE r) =
      ?j :: (LESS(LENGTH v)). US_SEM (SEL v (0,j)) r)
(*
    /\
    (UF_SEM v (F_WEAK_SERE r) =
      !j :: (LESS(LENGTH v)).
       UF_SEM (CAT(SEL v (0,j),TOP_OMEGA)) (F_STRONG_SERE r))
*)
    /\
    (UF_SEM v (F_WEAK_SERE r) =
      !j :: (LESS(LENGTH v)).
        ?k :: (LESS(LENGTH(CAT(SEL v (0,j),TOP_OMEGA)))).
          US_SEM (SEL(CAT(SEL v (0,j),TOP_OMEGA)) (0,k)) r)
    /\
    (UF_SEM v (F_NEXT f) =
      LENGTH v > 1 /\ UF_SEM (RESTN v 1) f)
    /\
    (UF_SEM v (F_UNTIL(f1,f2)) =
      ?k :: (LESS(LENGTH v)).
        UF_SEM (RESTN v k) f2 /\ !j :: (LESS k). UF_SEM (RESTN v j) f1)
    /\
(* Contains j=0 bug spotted by Thomas Turk
     (UF_SEM v (F_ABORT (f,b)) =
       UF_SEM v f
       \/
       ?j :: (LESS(LENGTH v)).
          B_SEM (ELEM v j) b /\ UF_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) f)
*)
    (UF_SEM v (F_ABORT (f,b)) =
      UF_SEM v f
      \/
      ?j :: (LESS(LENGTH v)).
        B_SEM (ELEM v j) b
        /\
        if j=0 then UF_SEM TOP_OMEGA f
               else UF_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) f)
    /\
    (UF_SEM v (F_SUFFIX_IMP(r,f)) =
      !j :: (LESS(LENGTH v)).
        US_SEM (SEL (COMPLEMENT v) (0,j)) r ==> UF_SEM (RESTN v j) f)
End

(******************************************************************************
* UF_SEM v f means "v |= f"  in the unclocked semantics
* where v is a finite or infinite word i.e. v : ('prop -> bool)path
* UF_SEM_def is unfolded version for easy definition.
* Theorem UF_SEM gives version corresponding to LRM v1.1
******************************************************************************)
Theorem UF_SEM:
     (UF_SEM v (F_NOT f) =
       ~(UF_SEM (COMPLEMENT v) f))
     /\
     (UF_SEM v (F_AND(f1,f2)) =
       UF_SEM v f1 /\ UF_SEM v f2)
     /\
     (UF_SEM v (F_STRONG_BOOL b) =
       (LENGTH v > 0) /\ B_SEM (ELEM v 0) b)
     /\
     (UF_SEM v (F_WEAK_BOOL b) =
       (LENGTH v = XNUM 0) \/ B_SEM (ELEM v 0) b)
     /\
     (UF_SEM v (F_STRONG_SERE r) =
       ?j :: (LESS(LENGTH v)). US_SEM (SEL v (0,j)) r)
     /\
     (UF_SEM v (F_WEAK_SERE r) =
       !j :: (LESS(LENGTH v)).
        UF_SEM (CAT(SEL v (0,j),TOP_OMEGA)) (F_STRONG_SERE r))
(*
     /\
     (UF_SEM v (F_WEAK_SERE r) =
       !j :: (LESS(LENGTH v)).
         ?k :: (LESS(LENGTH(CAT(SEL v (0,j),TOP_OMEGA)))).
           US_SEM (SEL(CAT(SEL v (0,j),TOP_OMEGA)) (0,k)) r)
*)
     /\
     (UF_SEM v (F_NEXT f) =
       LENGTH v > 1 /\ UF_SEM (RESTN v 1) f)
     /\
     (UF_SEM v (F_UNTIL(f1,f2)) =
       ?k :: (LESS(LENGTH v)).
         UF_SEM (RESTN v k) f2 /\ !j :: (LESS k). UF_SEM (RESTN v j) f1)
     /\
(* Contains j=0 bug spotted by Thomas Turk
     (UF_SEM v (F_ABORT (f,b)) =
       UF_SEM v f
       \/
       ?j :: (LESS(LENGTH v)).
          B_SEM (ELEM v j) b /\ UF_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) f)
*)
    (UF_SEM v (F_ABORT (f,b)) =
      UF_SEM v f
      \/
      ?j :: (LESS(LENGTH v)).
        B_SEM (ELEM v j) b
        /\
        if j=0 then UF_SEM TOP_OMEGA f
               else UF_SEM (CAT(SEL v (0,j-1),TOP_OMEGA)) f)
     /\
     (UF_SEM v (F_SUFFIX_IMP(r,f)) =
       !j :: (LESS(LENGTH v)).
         US_SEM (SEL (COMPLEMENT v) (0,j)) r ==> UF_SEM (RESTN v j) f)
Proof
   RW_TAC std_ss [UF_SEM_def]
QED

(*****************************************************************************)
(* Map a function over a path (used to define Lhat -- see LRM B.2.2)         *)
(*****************************************************************************)
Definition MAP_PATH_def:
   (MAP_PATH g (FINITE l) = FINITE(MAP g l))
   /\
   (MAP_PATH g (INFINITE f) = INFINITE(\n. g(f n)))
End

(******************************************************************************
* UF_VALID M f means "Lhat(pi) |= f" for all computations pi of M
******************************************************************************)
Definition UF_VALID_def:  (* from UnclockedSemanticsScript.sml *)
   UF_VALID M f =
    !v::(COMPUTATION M). UF_SEM (MAP_PATH (\s. STATE(M.L s)) v) f
End

(******************************************************************************
* PATH M s is true of p iff p is a computation path of M
* (now defined in ModelTheory)
******************************************************************************)

(******************************************************************************
* O_SEM M s f means "M, s |= f"
******************************************************************************)
Definition O_SEM_def:
   (O_SEM M (O_BOOL b) s = B_SEM (STATE(M.L s)) b)
   /\
   (O_SEM M (O_NOT f) s = ~(O_SEM M f s))
   /\
   (O_SEM M (O_AND(f1,f2)) s = O_SEM M f1 s /\ O_SEM M f2 s)
   /\
   (O_SEM M (O_EX f) s =
     ?p :: PATH M s.
       (LENGTH p > 1) /\ (ELEM p 0 = s) /\ O_SEM M f (ELEM p 1))
   /\
   (O_SEM M (O_EU(f1,f2)) s =
     ?p :: PATH M s.
       ?k :: (LESS(LENGTH p)).
         (ELEM p 0 = s)        /\
         O_SEM M f2 (ELEM p k) /\
         !j. j < k ==> O_SEM M f1 (ELEM p j))
   /\
   (O_SEM M (O_EG f) s =
     ?p :: PATH M s.
       (ELEM p 0 = s) /\ !j :: (LESS(LENGTH p)). O_SEM M f (ELEM p j))
End

(******************************************************************************
* O_VALID M f means "M, s |= f" for all initial states s
******************************************************************************)
Definition O_VALID_def:
   O_VALID M f = !s::(M.S0). O_SEM M f s
End
