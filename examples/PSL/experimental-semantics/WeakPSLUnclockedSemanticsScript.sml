(*****************************************************************************)
(* Create "WeakPSLUnclockedSemanticsTheory"                                  *)
(*****************************************************************************)

(******************************************************************************
* Load theory of syntax, paths and models
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;                         (* Switch off output               *)
loadPath                                  (* Add official-semantics to path  *)
 :=
 "../1.1/official-semantics" :: "../path" :: !loadPath;
map load
 ["intLib", "Cooper","rich_listTheory",   (* Load useful theories            *)
  "FinitePathTheory", "PathTheory",
  "res_quanLib", "res_quanTheory",
  "SyntaxTheory","SyntacticSugarTheory",
  "LemmasTheory","ProjectionTheory",
  "UnclockedSemanticsTheory"];
open FinitePathTheory PathTheory          (* Open theories                   *)
     SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory
     LemmasTheory ProjectionTheory
     arithmeticTheory listTheory
     rich_listTheory
     res_quanLib res_quanTheory;
intLib.deprecate_int();                   (* Set num as default numbers type *)
quietdec := false;                        (* Restore output                  *)
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory LemmasTheory ProjectionTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start a new theory called WeakPSLUnclockedSemanticsTheory                 *)
(*****************************************************************************)

val _ = new_theory "WeakPSLUnclockedSemantics";

(*****************************************************************************)
(* N^f = { w | w is a finite list of states/letters } (the set of neutral    *)
(* finite words)                                                             *)
(*                                                                           *)
(* we let \epsilon be the empty (neutral) word                               *)
(*                                                                           *)
(* W = { W(w) | w \in N^f } (the set of weak finite words)                   *)
(*                                                                           *)
(* Let A = N^f U W                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Definition of a datatypetype A. It creates a tagged disjoint union with   *)
(* elements ``N l``, ``W l`` and ``S l``, where l is a HOL list.             *)
(*****************************************************************************)
val A_def =
 Hol_datatype
  `A = N of 'a list
     | W of 'a list
     | S of 'a list`;

(*****************************************************************************)
(* Retrieve from data-base (DB) automatically proved theorems about A        *)
(*****************************************************************************)
val A_11       = assoc "A_11"       (DB.theorems "-")
and A_distinct = assoc "A_distinct" (DB.theorems "-");

val A_ELEM_def =
 Define
  `(A_ELEM (N l) n = EL n l)
   /\
   (A_ELEM (W l) n = EL n l)
   /\
   (A_ELEM (S l) n = EL n l)`;

(*****************************************************************************)
(* We define concatenation ( * ) on A: if v,w \in N then v*w is just the     *)
(* list concatenation of v and w (remember v,w finite) v*W(w) = W(v*w)       *)
(* and for v\in W and w\in A v*w = v                                         *)
(*****************************************************************************)

(*****************************************************************************)
(* For readability overload "++" onto HOL's list append constant APPEND,     *)
(* and make it a left associative infix with precedence 500.                 *)
(*****************************************************************************)
val _ = set_fixity "++" (Infixl 500);
val _ = overload_on("++", ``APPEND``);

(*****************************************************************************)
(* Define ``CONC`` for concatenation on values of type A.                    *)
(*****************************************************************************)
val _ = set_fixity "CONC" (Infixl 500);

val CONC_def =
 Define
  `(N v CONC N w = N(v++w))
   /\
   (N v CONC W w = W(v++w))
   /\
   (N v CONC S w = S(v++w))
   /\
   (W v CONC a   = W v)
   /\
   (S v CONC a   = S v)`;

(*****************************************************************************)
(* Overload "*" on to "CONC" for readability.                                *)
(*****************************************************************************)
val _ = overload_on("*", ``$CONC``);

(*****************************************************************************)
(* We want to show that A is closed under *, that * is associative on A and  *)
(* that \epsilon is the identity for this operation.                         *)
(*****************************************************************************)
val CONC_IDENTITY =
 prove
  (``(N[] * a = a) /\ (a * N[] = a)``,
   Cases_on `a`
    THEN RW_TAC list_ss [CONC_def]);

val CONC_ASSOC =
 prove
  (``a * (b * c) = (a * b) * c``,
   Cases_on `a` THEN Cases_on `b` THEN Cases_on `c`
    THEN RW_TAC list_ss [CONC_def]);

val ASSOC_CONC =
 prove
  (``ASSOC $*``,
   RW_TAC std_ss [operatorTheory.ASSOC_DEF,CONC_ASSOC]);

(*****************************************************************************)
(* for w \in N |w| is the number of elements in w, and |W(w)| = |w|          *)
(*****************************************************************************)

(*****************************************************************************)
(* Represent |w| by LEN w. HOL's built-in length function on lists           *)
(* is LENGTH.                                                                *)
(*****************************************************************************)
val LEN_def =
 Define
  `(LEN(N w) = LENGTH w)
   /\
   (LEN(W w) = LENGTH w)
   /\
   (LEN(S w) = LENGTH w)`;

(*****************************************************************************)
(* we want to show that if w \in N then                                      *)
(* |w*v| = |w|+|v|, |W(w)*v| = |w| and |S(w)*v| = |w|                        *)
(*****************************************************************************)
val LEN =
 prove
  (``(LEN(N w * a) = LEN(N w) + LEN a)
     /\
     (LEN(W w * a) = LEN(W w))
     /\
     (LEN(S w * a) = LEN(S w))``,
   Cases_on `a`
    THEN RW_TAC list_ss [LEN_def,CONC_def]);

(*****************************************************************************)
(* We define (on A) w<=v (prefix) if there is u \in A such that w*u=v        *)
(*****************************************************************************)
val PREFIX_def = Define `PREFIX w v = ?u. w*u = v`;

val STRICT_PREFIX_def = Define `STRICT_PREFIX w v = PREFIX w v /\ ~(w = v)`;

(*****************************************************************************)
(* u<w   is u is prefix of w and u/=w                                        *)
(* One could try to prove that if u<w u is neutral                           *)
(*****************************************************************************)

val STRICT_PREFIX_NEUTRAL =
 prove
  (``STRICT_PREFIX u w ==> ?l. u = N l``,
   Cases_on `u` THEN Cases_on `w`
    THEN RW_TAC list_ss [STRICT_PREFIX_def,PREFIX_def,CONC_def]);

val IS_WEAK_def =
 Define
  `(IS_WEAK(W w) = T)    /\ (IS_WEAK(N w) = F)    /\ (IS_WEAK(S w) = F)`
and IS_NEUTRAL_def =
 Define
  `(IS_NEUTRAL(W w) = F) /\ (IS_NEUTRAL(N w) = T) /\ (IS_NEUTRAL(S w) = F)`
and IS_STRONG_def =
 Define
  `(IS_STRONG(W w) = F)  /\ (IS_STRONG(N w) = F)  /\ (IS_STRONG(S w) = T)`;

val IS_LETTER_def =
 Define
  `(IS_LETTER(N w) = ?l. w = [l])
   /\
   (IS_LETTER(W w) = ?l. w = [l])
   /\
   (IS_LETTER(S w) = ?l. w = [l])`;

(*****************************************************************************)
(* WeakPSL Semantics of SEREs                                                *)
(*****************************************************************************)

(*######################################################################
#
# [Notation: w^- = W(w) and w^+ = S(w)]
#
# Weak/neutral word definition
# ----------------------------
# for finite w \in W U N U S
#
# we define (let l be a letter or \epsilon^-)
#
# w|==wns b <=> either w=\epsilon^- or (w not \in S and |w|=1 and w^0||-b)
# w|==wns r1;r2 <=> there exist u,v s.t. uv=w and u|==wns r1 and v|==wns r2
# w|==wns r1:r2 <=> there exist u,v,l s.t. ulv=w and ul|==wns r1 and lv|==wns r2
# w|==wns r1&r2 <=> w|==wns r1 and w|==wns r2
# w|==wns r1|r2 <=> w|==wns r1 or w|==wns r2
# w|==wns r*   <=> either w=\epsilon
#                  or there exist w_1,..w_j
#                     s.t. w=w_1w_2...w_j and for 1<=i<=j w_i|==wns r
######################################################################*)

val WUS_SEM_def =
 Define
  `(WUS_SEM v (S_BOOL b) =
     (v = W[]) \/ (~(IS_STRONG v) /\ (LEN v = 1) /\ B_SEM (A_ELEM v 0) b))
   /\
   (WUS_SEM v (S_CAT(r1,r2)) =
     ?v1 v2. (v = v1 * v2) /\ WUS_SEM v1 r1 /\ WUS_SEM v2 r2)
   /\
   (WUS_SEM v (S_FUSION(r1,r2)) =
     ?v1 v2 l. (IS_LETTER l \/ (l = W[])) /\ (v = v1*l*v2)
               /\
               WUS_SEM (v1*l) r1  /\ WUS_SEM (l*v2) r2)
   /\
   (WUS_SEM v (S_AND(r1,r2)) =
     WUS_SEM v r1 /\ WUS_SEM v r2)
   /\
   (WUS_SEM v (S_OR(r1,r2)) =
     WUS_SEM v r1 \/ WUS_SEM v r2)
   /\
   (WUS_SEM v S_EMPTY = (v = N[]) \/ (v = W[]))
   /\
   (WUS_SEM v (S_REPEAT r) =
     ?vlist. (v = FOLDL $* (N[]) vlist) /\ EVERY (\v. WUS_SEM v r) vlist)`;

(*****************************************************************************)
(* We can now prove with fusion in the language                              *)
(*   for all unclocked r: W(\espilon) |==wns r                               *)
(*****************************************************************************)
local
val WUS_SEM_SIMP_TAC =
 RW_TAC list_ss
  [S_CLOCK_FREE_def,WUS_SEM_def,IS_WEAK_def,IS_NEUTRAL_def,LEN_def,A_ELEM_def]
in
val TightTrueEmpty =
 prove
  (``!r. S_CLOCK_FREE r ==> WUS_SEM (W[]) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      WUS_SEM_SIMP_TAC,
      (* S_CAT (r,r') *)
      WUS_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W []`
       THEN RW_TAC list_ss [CONC_def],
      (* S_FUSION (r,r') *)
      WUS_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W []`
       THEN RW_TAC list_ss [CONC_def,IS_LETTER_def],
      (* S_OR (r,r') *)
      WUS_SEM_SIMP_TAC,
      (* S_AND (r,r') *)
      WUS_SEM_SIMP_TAC,
      (* S_EMPTY *)
      WUS_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `[W []]`
       THEN RW_TAC list_ss [CONC_def],
      (* S_REPEAT (r,r') *)
      WUS_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `[W []]`
       THEN RW_TAC list_ss [CONC_def],
      (* S_REPEAT (r,r') *)
      WUS_SEM_SIMP_TAC])
end;

(*****************************************************************************)
(* Weaken a word                                                             *)
(*****************************************************************************)
val WEAKEN_def =
 Define `(WEAKEN(N l) = W l) /\ (WEAKEN(W l) = W l) /\ (WEAKEN(S l) = S l)`;

val LEN_WEAKEN =
 prove
  (``LEN(WEAKEN w) = LEN w``,
   Cases_on `w`
    THEN RW_TAC list_ss [WEAKEN_def,LEN_def]);

(*****************************************************************************)
(* Tight prefix theorem                                                      *)
(* w |==wns r and u <= w => W(u) |==wns r                                    *)
(*****************************************************************************)
val APPEND_EQ_NIL =
 prove
  (``!l1 l2. (LENGTH(l1++l2) = 0) ==> (l1 = []) /\ (l2 = [])``,
   Induct
    THEN RW_TAC list_ss []
    THEN `LENGTH l2 = 0` by DECIDE_TAC
    THEN PROVE_TAC[LENGTH_NIL]);

val APPEND_EQ_SINGLETON =
 prove
  (``!l1 l2. (LENGTH(l1++l2) = 1) ==> (l1 = []) \/ (l2 = [])``,
   Induct
    THEN RW_TAC list_ss []
    THEN `LENGTH l2 = 0` by DECIDE_TAC
    THEN PROVE_TAC[LENGTH_NIL]);

val APPEND_NIL_CANCEL =
 prove
  (``!l1 l2. (l1++l2 = l1) ==> (l2 = [])``,
   Induct
    THEN RW_TAC list_ss []);

val PREFIX_CONC =
 prove
  (``PREFIX u v1 ==> !v2. PREFIX u (v1 * v2)``,
   Cases_on `u` THEN Cases_on `v1`
    THEN RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `v2`
    THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct]
    THENL
     [Q.EXISTS_TAC `N(l''++l''')` THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `W(l''++l''')` THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `S(l''++l''')` THEN RW_TAC list_ss [CONC_def]]);

val HD_APPEND =
 prove
  (``!v1 v2. ~(v1 = []) ==> (HD(APPEND v1 v2) = HD v1)``,
   Induct
    THEN RW_TAC list_ss []);

val TL_APPEND =
 prove
  (``!v1 v2. ~(v1 = []) ==> (TL(APPEND v1 v2) = APPEND (TL v1) v2)``,
   Induct
    THEN RW_TAC list_ss []);

val LIST_TRICHOTOMY_LEMMA1 =
 prove
  (``~(v = []) ==> (h::u ++ u' = v ++ v') ==> (h = HD v) /\ (u ++ u' = TL v ++ v')``,
   RW_TAC list_ss []
    THEN PROVE_TAC[HD,HD_APPEND,TL,TL_APPEND]);

val LIST_TRICHOTOMY_LEMMA2 =
 prove
  (``~(v = []) ==> (!w. ~(HD v::u ++ w = v)) ==> !w. ~(u ++ w = TL v)``,
   RW_TAC list_ss []
    THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
    THEN Cases_on `~(u ++ w = TL v)`
    THEN FULL_SIMP_TAC list_ss []
    THEN `HD v :: u ++ w = HD v :: TL v` by PROVE_TAC[]
    THEN `~(NULL v)` by PROVE_TAC[NULL_EQ_NIL]
    THEN FULL_SIMP_TAC std_ss [CONS]
    THEN RES_TAC);

val LIST_TRICHOTOMY_LEMMA3 =
 prove
  (``!u v.
      (u ++ u' = v ++ v') /\ (!w. ~(u ++ w = v))
      ==>
      ?w. v ++ w = u``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `v=[]`
    THEN RW_TAC list_ss []
    THEN IMP_RES_TAC LIST_TRICHOTOMY_LEMMA1
    THEN RW_TAC list_ss []
    THEN `TL(HD v::u ++ u') = TL(v ++ v')` by PROVE_TAC[]
    THEN FULL_SIMP_TAC list_ss []
    THEN IMP_RES_TAC LIST_TRICHOTOMY_LEMMA2
    THEN RES_TAC
    THEN `HD v :: TL v ++ w = HD v :: u` by PROVE_TAC[]
    THEN PROVE_TAC[APPEND,CONS,NULL_EQ_NIL]);

val LIST_TRICHOTOMY =
 prove
  (``!u v.
      (?u' v'. u ++ u'  = v ++ v')
      ==>
      (?w. u ++ w = v) \/ (?w. v ++ w = u)``,
   RW_TAC list_ss []
    THEN Cases_on `(?w. u ++ w = v)`  (* u<=v *)
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss []
    THEN Induct_on `u`
    THEN RW_TAC list_ss []
    THEN PROVE_TAC[LIST_TRICHOTOMY_LEMMA3,APPEND]);

val PREFIX_TRICHOTOMY =
 prove
  (``!v1 v2 w.
       PREFIX v1 w /\ PREFIX v2 w ==> STRICT_PREFIX v1 v2 \/ PREFIX v2 v1``,
   REPEAT GEN_TAC
    THEN Cases_on `v1` THEN Cases_on `v2` THEN Cases_on `w`
    THEN RW_TAC list_ss [PREFIX_def,STRICT_PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'`
    THEN FULL_SIMP_TAC list_ss [PREFIX_def,STRICT_PREFIX_def,CONC_def,A_11,A_distinct]
    THEN Cases_on `?u. l' ++ u = l`
    THEN FULL_SIMP_TAC list_ss [PREFIX_def,STRICT_PREFIX_def,CONC_def,A_11,A_distinct]
    THEN ZAP_TAC list_ss [CONC_def,A_11]
    THEN Cases_on `?u. l++u = l'`
    THEN ZAP_TAC list_ss [CONC_def,A_11]
    THEN FULL_SIMP_TAC list_ss []
    THEN IMP_RES_TAC LIST_TRICHOTOMY
    THEN RES_TAC);

val PREFIX_REFL =
 prove
  (``!v. PREFIX v v``,
   Induct
    THEN RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Q.EXISTS_TAC `N[]`
    THEN RW_TAC list_ss [CONC_def]);

val APPEND_LEFT_CANCEL =
 store_thm
  ("APPEND_LEFT_CANCEL",
   ``(APPEND l l1 = APPEND l l2) = (l1 = l2)``,
   Induct_on `l`
    THEN ZAP_TAC list_ss []);

val PREFIX_CANCEL =
 prove
  (``(PREFIX (N(u ++ v1)) (N(u ++ v2)) ==> PREFIX (N v1) (N v2)) /\
     (PREFIX (W(u ++ v1)) (N(u ++ v2)) ==> PREFIX (W v1) (N v2)) /\
     (PREFIX (S(u ++ v1)) (N(u ++ v2)) ==> PREFIX (S v1) (N v2)) /\
     (PREFIX (N(u ++ v1)) (W(u ++ v2)) ==> PREFIX (N v1) (W v2)) /\
     (PREFIX (W(u ++ v1)) (W(u ++ v2)) ==> PREFIX (W v1) (W v2)) /\
     (PREFIX (S(u ++ v1)) (W(u ++ v2)) ==> PREFIX (S v1) (W v2)) /\
     (PREFIX (N(u ++ v1)) (S(u ++ v2)) ==> PREFIX (N v1) (S v2)) /\
     (PREFIX (W(u ++ v1)) (S(u ++ v2)) ==> PREFIX (W v1) (S v2)) /\
     (PREFIX (S(u ++ v1)) (S(u ++ v2)) ==> PREFIX (S v1) (S v2))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u'`
    THEN FULL_SIMP_TAC std_ss
          [GSYM APPEND_ASSOC,CONC_def,A_11,A_distinct,APPEND_LEFT_CANCEL]
    THEN PROVE_TAC[CONC_def]);

val B_FALSE =
 prove
  (``B_SEM (STATE s) B_FALSE = F``,
   RW_TAC list_ss [B_SEM_def]);

val IS_WEAK_LEN_0 =
 prove
  (``!v. IS_WEAK v /\ (LEN v = 0) = (v = W[])``,
   Induct
    THEN RW_TAC list_ss [IS_WEAK_def,LEN_def,LENGTH_NIL]);

val FOLDL_W_NIL =
 prove
  (``!l. ALL_EL (\v. v = W []) l ==> (FOLDL $* (W []) l = W[])``,
   Induct
    THEN RW_TAC list_ss [CONC_def]);

val FOLDL_N_NIL =
 prove
  (``!l. ~(l = []) ==> ALL_EL (\v. v = W []) l ==> (FOLDL $* (N []) l = W[])``,
   Induct
    THEN RW_TAC list_ss [CONC_def,FOLDL_W_NIL]);

(*****************************************************************************)
(* Not sure why I defined WS_CATN here and S_CATN in ProjectionTheory.       *)
(* Probably could get away with just the latter, but I'm too lazy to redo    *)
(* the proofs!                                                               *)
(*****************************************************************************)
val WS_CATN_def =
 Define
  `(WS_CATN 0 r = r) /\ (WS_CATN (SUC n) r = S_CAT(r, WS_CATN n r))`;

(*****************************************************************************)
(* Theorem to connect WS_CATN and S_CATN in the LRM 1.1 semantics            *)
(*****************************************************************************)
val US_SEM_WS_CATN =
 store_thm
  ("US_SEM_WS_CATN",
   ``!n w r. US_SEM w (WS_CATN n r) = US_SEM w (S_CATN (SUC n) r)``,
   Induct
    THEN RW_TAC list_ss [US_SEM,WS_CATN_def,S_CATN_def]);

val ASSOC_FOLDL =
 prove
  (``!l x y. ASSOC f ==> (FOLDL f (f x y) l = f x (FOLDL f y l))``,
   Induct
    THEN RW_TAC list_ss [operatorTheory.ASSOC_DEF]);

val FOLDL_CONCAT_N =
 prove
  (``!vlist v. FOLDL $* v vlist = v * FOLDL $* (N []) vlist``,
   PROVE_TAC[ASSOC_FOLDL,ASSOC_CONC,CONC_IDENTITY]);

val WUS_SEM_CAT_REPEAT_CATN =
 store_thm
  ("WUS_SEM_CAT_REPEAT_CATN",
   ``!v r. WUS_SEM v (S_CAT(S_REPEAT r, r)) = ?n. WUS_SEM v (WS_CATN n r)``,
   RW_TAC list_ss [WUS_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THENL
     [Induct_on `vlist`
       THEN RW_TAC list_ss [CONC_IDENTITY,WS_CATN_def,WUS_SEM_def]
       THEN ZAP_TAC std_ss [WS_CATN_def]
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN Q.EXISTS_TAC `SUC n`
       THEN RW_TAC list_ss [WS_CATN_def,WUS_SEM_def]
       THEN Q.EXISTS_TAC `h` THEN Q.EXISTS_TAC `FOLDL $* (N []) vlist * v2`
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[FOLDL_CONCAT_N,CONC_ASSOC],
      Q.UNDISCH_TAC `WUS_SEM v (WS_CATN n r)`
       THEN Q.SPEC_TAC(`v`,`v`)
       THEN Q.SPEC_TAC(`r`,`r`)
       THEN Q.SPEC_TAC(`n`,`n`)
       THEN Induct
       THEN RW_TAC list_ss [WS_CATN_def]
       THENL
        [Q.EXISTS_TAC `N[]` THEN Q.EXISTS_TAC `v`
          THEN RW_TAC list_ss [CONC_IDENTITY]
          THEN Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [],
         FULL_SIMP_TAC list_ss [WUS_SEM_def]
          THEN RES_TAC
          THEN RW_TAC std_ss []
          THEN Q.EXISTS_TAC `v1 * FOLDL $* (N []) vlist`
          THEN Q.EXISTS_TAC `v2'`
          THEN RW_TAC std_ss [CONC_ASSOC]
          THEN Q.EXISTS_TAC `v1::vlist`
          THEN RW_TAC list_ss [CONC_IDENTITY]
          THEN PROVE_TAC[FOLDL_CONCAT_N]]]);

val FOLDLN_def =
 Define
  `(FOLDLN 0 f e l = e) /\
   (FOLDLN (SUC n) f e l = FOLDLN n f (f e (HD l)) (TL l))`;

val FOLDLN_LENGTH =
 prove
  (``!l f e. FOLDLN (LENGTH l) f e l = FOLDL f e l``,
   Induct
    THEN RW_TAC list_ss [FOLDLN_def]);

val FOLDLN_ASSOC =
 prove
  (``!n v1 v2 l. FOLDLN n $* (v1 * v2) l = v1 * FOLDLN n $* v2 l``,
   Induct
    THEN RW_TAC list_ss [FOLDLN_def,CONC_ASSOC]);

val FOLDLN_CATN =
 prove
  (``!l v0 r.
      ALL_EL (\v. WUS_SEM v r) l /\ WUS_SEM v0 r
      ==>
      !n. n <= LENGTH l ==> WUS_SEM (FOLDLN n $* v0 l) (WS_CATN n r)``,
   Induct
    THEN RW_TAC list_ss [FOLDLN_def,WS_CATN_def]
    THEN Cases_on `n = 0`
    THEN RW_TAC list_ss [FOLDLN_def,WS_CATN_def]
    THEN `?m. n = SUC m` by Cooper.COOPER_TAC
    THEN RW_TAC list_ss [FOLDLN_def,WS_CATN_def]
    THEN FULL_SIMP_TAC arith_ss [WUS_SEM_def]
    THEN RES_TAC
    THEN Q.EXISTS_TAC `v0`
    THEN Q.EXISTS_TAC `FOLDLN m $* h l`
    THEN RW_TAC list_ss [FOLDLN_ASSOC]);

val WUS_SEM_REPEAT_WS_CATN =
 store_thm
  ("WUS_SEM_REPEAT_WS_CATN",
   ``!v r. WUS_SEM v (S_REPEAT r) = (v = N[])
           \/
           ?n. WUS_SEM v (WS_CATN n r)``,
   RW_TAC list_ss []
    THEN EQ_TAC
    THENL
     [SIMP_TAC list_ss[WUS_SEM_def]
       THEN REPEAT STRIP_TAC
       THEN Cases_on `v = N[]`
       THEN ASM_REWRITE_TAC[]
       THEN Cases_on `vlist`
       THEN FULL_SIMP_TAC list_ss [CONC_IDENTITY]
       THEN RES_TAC
       THEN `LENGTH t <= LENGTH t` by DECIDE_TAC
       THEN IMP_RES_TAC FOLDLN_CATN
       THEN Q.EXISTS_TAC `LENGTH t`
       THEN FULL_SIMP_TAC list_ss [FOLDLN_LENGTH],
      RW_TAC list_ss [WUS_SEM_def]
       THENL
        [Q.EXISTS_TAC `[]`
          THEN RW_TAC list_ss [],
         Q.UNDISCH_TAC `WUS_SEM v (WS_CATN n r)`
          THEN Q.SPEC_TAC(`v`,`v`)
          THEN Q.SPEC_TAC(`r`,`r`)
          THEN Q.SPEC_TAC(`n`,`n`)
          THEN Induct
          THEN RW_TAC list_ss [WS_CATN_def]
          THENL
           [Q.EXISTS_TAC `[v]`
             THEN RW_TAC list_ss [CONC_IDENTITY],
            FULL_SIMP_TAC list_ss [WUS_SEM_def]
             THEN RES_TAC
             THEN Q.EXISTS_TAC `v1::vlist`
             THEN RW_TAC list_ss [CONC_IDENTITY]
             THEN PROVE_TAC[FOLDL_CONCAT_N]]]]);

val NN_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (N u) (N v) ==> PREFIX (N(w ++ u)) (N(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_IDENTITY,A_11,A_distinct]
    THENL
     [PROVE_TAC[CONC_IDENTITY],
      Q.EXISTS_TAC `N(h::t)`
       THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `N l`
       THEN RW_TAC std_ss [CONC_def,GSYM APPEND_ASSOC,APPEND],
      Q.EXISTS_TAC `N l`
       THEN RW_TAC std_ss [CONC_def,GSYM APPEND_ASSOC,APPEND]]);

val WN_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (W u) (N v) ==> PREFIX (W(w ++ u)) (N(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_IDENTITY,A_11,A_distinct]);

val NW_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (N u) (W v) ==> PREFIX (N(w ++ u)) (W(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_IDENTITY,A_11,A_distinct]
    THENL
     [Q.EXISTS_TAC `W[]`
       THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `W(h::t)`
       THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `W l`
       THEN RW_TAC std_ss [CONC_def,GSYM APPEND_ASSOC,APPEND],
      Q.EXISTS_TAC `W l`
       THEN RW_TAC std_ss [CONC_def,GSYM APPEND_ASSOC,APPEND]]);

val WW_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (W u) (W v) ==> PREFIX (W(w ++ u)) (W(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_IDENTITY,A_11,A_distinct]);

local
val WUS_SEM_SIMPS =
  [WUS_SEM_def,IS_WEAK_def,IS_NEUTRAL_def,LEN_def,A_ELEM_def,
   WEAKEN_def,(*WEAKEN,*)LEN_WEAKEN,PREFIX_def,PREFIX_def,CONC_def]
in
val TightPrefix_S_BOOL =
 prove
  (``!b w.
      WUS_SEM w (S_BOOL b)
      ==>
      !u. PREFIX u w ==> WUS_SEM (WEAKEN u) (S_BOOL b)``,
   RW_TAC list_ss WUS_SEM_SIMPS
    THEN Cases_on `u` THEN Cases_on `u'`
    THEN FULL_SIMP_TAC list_ss
          (WUS_SEM_SIMPS@[IS_STRONG_def,CONC_def,A_11,A_distinct])
    THEN `(LENGTH l = 0) \/ (LENGTH l' = 0)` by DECIDE_TAC
    THEN (`l  = []` by PROVE_TAC[LENGTH_NIL] ORELSE
          `l' = []` by PROVE_TAC[LENGTH_NIL])
    THEN FULL_SIMP_TAC list_ss [])
end;

val TightPrefix_S_CAT =
 prove
  (``(!w. WUS_SEM w r ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r) /\
     (!w. WUS_SEM w r' ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r')
     ==>
     !w. WUS_SEM w (S_CAT (r,r'))
         ==>
         !u. PREFIX u w ==> WUS_SEM (WEAKEN u) (S_CAT (r,r'))``,
   RW_TAC list_ss [WUS_SEM_def]
    THEN Cases_on `PREFIX u v1`
    THENL
     [RES_TAC
       THEN Q.EXISTS_TAC `WEAKEN u` THEN Q.EXISTS_TAC `v2`
       THEN RW_TAC list_ss []
       THEN Cases_on `u` THEN Cases_on `v2`
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def],
      `STRICT_PREFIX v1 u`
        by PROVE_TAC[PREFIX_TRICHOTOMY,PREFIX_def,PREFIX_CONC,PREFIX_REFL]
       THEN FULL_SIMP_TAC list_ss [STRICT_PREFIX_def,PREFIX_def]
       THEN Q.EXISTS_TAC `v1` THEN Q.EXISTS_TAC `WEAKEN u''`
       THEN RW_TAC list_ss [CONC_def]
       THENL
        [Cases_on `v1` THEN Cases_on `v2` THEN Cases_on `u''`
          THEN FULL_SIMP_TAC list_ss [WEAKEN_def,CONC_def,A_11,A_distinct],
         FULL_SIMP_TAC list_ss [GSYM CONC_ASSOC]
          THEN Cases_on `v1` THEN Cases_on `v2` THEN Cases_on `u'' * u'`
          THEN FULL_SIMP_TAC list_ss [WEAKEN_def,CONC_def,A_11,A_distinct]
          THEN RW_TAC std_ss []
          THEN RES_TAC]]);

val CONC_WEAKEN =
 store_thm
  ("CONC_WEAKEN",
   ``!u v. WEAKEN u * v = WEAKEN u``,
   Cases_on `u`
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def]);

val WEAKEN_CONC =
 store_thm
  ("WEAKEN_CONC",
   ``!v1 v2. WEAKEN(v1 * v2) = v1 * WEAKEN v2``,
   REPEAT GEN_TAC
    THEN Cases_on `v1` THEN Cases_on `v2`
    THEN RW_TAC list_ss []
    THEN FULL_SIMP_TAC list_ss [WEAKEN_def]
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def]);

val APPEND_NIL_CANCEL =
 store_thm
  ("APPEND_NIL_CANCEL",
   ``!l1 l2. (l1 = l1 ++ l2 ) = (l2 = [])``,
   RW_TAC list_ss []
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN `LENGTH l1 = LENGTH(l1 ++ l2)` by PROVE_TAC[]
    THEN FULL_SIMP_TAC list_ss []
    THEN `LENGTH l2 = 0` by DECIDE_TAC
    THEN PROVE_TAC[LENGTH_NIL]);

(***********************************************************************
* if w\in N and w finite and for some u,u', w*u=w*u' then u=u'
************************************************************************
**
** Assume w \in N and w finite
**  if B is W, N or S then w*u \in B iff u \in B
**   Assume that w*u=w*u'
**     then u \in B iff u' \in B.
**     and also |u|=|u'| since |w|+|u|=|w*u|=|w*u|=|w|+|u'|
**     Now assume for contradiction that u/=u'
**      then there is k such that u^k/=u'^k.
**       but then (w*u)^(|w|+k)/=(w*u')^(|w|+k) contradicting the
**       assumption.
**
************************************************************************)
val CONC_CANCEL =
 store_thm
  ("CONC_CANCEL",
   ``!w u u'. IS_NEUTRAL w ==> ((w * u = w * u') = (u = u'))``,
   Cases_on `w` THEN Cases_on `u` THEN Cases_on `u'`
    THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct,IS_NEUTRAL_def]);

(***********************************************************************
* For v,w in A if v<=w and w<=v then w=v (antisymmetry)
************************************************************************
**
** Assume that v,w in A and v<=w and w<=v th
**  then there is u1 and u2 such that
**   v*u1=w and w*u2=v
**    if v \in N then w also \in N (because w*u2=w)
**       and v=w (antisymmetry of <= on neutral words)
**    if v \in W (\in S)
**      then v*u1=v so v=w.
***********************************************************************)
val PREFIX_ANTISYM =
 store_thm
  ("PREFIX_ANTISYM",
   ``!v w. PREFIX v w /\ PREFIX w v ==> (w = v)``,
   RW_TAC list_ss [PREFIX_def]
    THEN Cases_on `w` THEN Cases_on `u` THEN Cases_on `u'`
    THEN FULL_SIMP_TAC list_ss [CONC_def,A_distinct,A_11]
    THEN `l'' ++ l' = []` by PROVE_TAC[APPEND_NIL_CANCEL,APPEND_ASSOC]
    THEN FULL_SIMP_TAC list_ss [APPEND_eq_NIL]);

(***********************************************************************
* if l is a letter or \epsilon^- and v1*l*v2 \in A then
*
*   if v1*l<=u<=v1*l*v2 then there is v2' s.t. v1*l*v2'=u and l*v2'<=l*v2
************************************************************************
**
** Assume that l is a letter or \epsilon^-  [MJCG: this is not needed]
** and v1*l*v2 \in A
**  and that u is such that v1*l<=u<=v1*l*v2
**
**  Either v1 \in N or not
**   Assume v1 \in N.
**   let v2' be such that v1*l*v2'=u, so v1*l*v2'<=v1*l*v2
**    let x be such that (v1*l*v2')*x=v1*l*v2.
**     By associativity  v1*((l*v2')*x)=v1*(l*v2).
**      so by the previous lemma (l*v2')*x=l*v2 so l*v2'<=l*v2
**   Assume v1 \in W U S.
**    If v1 \in S U W. then v1*l=v1*l*v2=v1, by antisymmetry also u=v1
**     let v2'=\epsilon then v1*l*v2'=u and l*v2'=l<=l*v2.
***********************************************************************)
val PREFIX_FUSION_LEMMA =
 store_thm
  ("PREFIX_FUSION_LEMMA",
   ``!v1 v2 l.
       PREFIX (v1 * l) u /\ PREFIX u (v1 * l * v2)
       ==>
       ?v2'. (v1 * l * v2' = u) /\ PREFIX (l * v2') (l * v2)``,
   RW_TAC list_ss []
    THEN Cases_on `IS_NEUTRAL v1`
    THEN FULL_SIMP_TAC list_ss [GSYM CONC_ASSOC,CONC_def]
    THENL
     [PROVE_TAC[CONC_CANCEL,CONC_ASSOC,PREFIX_def],
      Cases_on `v1`
       THEN FULL_SIMP_TAC list_ss [CONC_def,IS_NEUTRAL_def]
       THEN IMP_RES_TAC PREFIX_ANTISYM
       THEN RW_TAC list_ss []
       THEN Q.EXISTS_TAC `v2`
       THEN RW_TAC list_ss [PREFIX_def]
       THEN Cases_on `l`
       THEN RW_TAC list_ss
             [CONC_def,GSYM CONC_ASSOC,CONC_CANCEL,IS_NEUTRAL_def]
       THEN Cases_on `v2`
       THEN RW_TAC list_ss [CONC_def,CONC_CANCEL,IS_NEUTRAL_def]
       THEN Q.EXISTS_TAC `N[]`
       THEN RW_TAC list_ss [CONC_def,CONC_CANCEL,IS_NEUTRAL_def]]);

val TightPrefix_S_FUSION =
 prove
  (``(!w. WUS_SEM w r ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r) /\
     (!w. WUS_SEM w r' ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r')
     ==>
     !w. WUS_SEM w (S_FUSION (r,r'))
         ==>
         !u. PREFIX u w ==> WUS_SEM (WEAKEN u) (S_FUSION (r,r'))``,
   RW_TAC list_ss [WUS_SEM_def]
    THEN Cases_on `STRICT_PREFIX u (v1 * l)`
    THEN FULL_SIMP_TAC list_ss [CONC_def,GSYM CONC_ASSOC]
    THENL
     [FULL_SIMP_TAC list_ss [STRICT_PREFIX_def]
       THEN RES_TAC
       THEN Q.EXISTS_TAC `WEAKEN u`
       THEN Q.EXISTS_TAC `v2`
       THEN Q.EXISTS_TAC `l`
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def,CONC_WEAKEN],
      `PREFIX (v1 * l) u`
        by PROVE_TAC
            [CONC_ASSOC,PREFIX_TRICHOTOMY,PREFIX_def,PREFIX_CONC,PREFIX_REFL]
       THEN FULL_SIMP_TAC std_ss [CONC_ASSOC]
       THEN `?v2'. (v1 * l * v2' = u) /\  PREFIX (l * v2') (l * v2)`
             by PROVE_TAC[PREFIX_FUSION_LEMMA]
       THEN `WUS_SEM (WEAKEN(l * v2')) r'` by PROVE_TAC[]
       THEN `WUS_SEM (l * WEAKEN v2') r'` by PROVE_TAC[WEAKEN_CONC]
       THEN Q.EXISTS_TAC `v1`
       THEN Q.EXISTS_TAC `WEAKEN v2'`
       THEN Q.EXISTS_TAC `l`
       THEN `l * WEAKEN v2' = WEAKEN(l * v2')` by PROVE_TAC[WEAKEN_CONC]
       THEN RW_TAC std_ss [GSYM CONC_ASSOC]
       THEN REWRITE_TAC[WEAKEN_CONC],
      FULL_SIMP_TAC list_ss [STRICT_PREFIX_def]
       THEN RES_TAC
       THEN Q.EXISTS_TAC `WEAKEN u`
       THEN Q.EXISTS_TAC `v2`
       THEN Q.EXISTS_TAC `W[]`
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def,CONC_WEAKEN],
      RES_TAC
       THEN Q.EXISTS_TAC `WEAKEN u`
       THEN Q.EXISTS_TAC `v2`
       THEN Q.EXISTS_TAC `W[]`
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def,CONC_WEAKEN]]);

val TightPrefix_WS_CATN =
 prove
  (``(!w. WUS_SEM w r ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r)
     ==>
     !n w.
      WUS_SEM w (WS_CATN n r)
      ==>
      !u. PREFIX u w ==> WUS_SEM (WEAKEN u) (WS_CATN n r)``,
   DISCH_TAC
    THEN Induct
    THEN RW_TAC list_ss [WS_CATN_def]
    THEN RES_TAC
    THEN IMP_RES_TAC TightPrefix_S_CAT);

val PREFIX_N_EMPTY =
 store_thm
  ("PREFIX_N_EMPTY",
   ``!w. PREFIX w (N[]) = (w = N[])``,
   Cases_on `w`
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def,PREFIX_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THENL
     [Cases_on `u`
       THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct],
      Q.EXISTS_TAC `N[]`
       THEN RW_TAC list_ss [CONC_def]]);

val PREFIX_W_EMPTY =
 store_thm
  ("PREFIX_W_EMPTY",
   ``!w. PREFIX w (W[]) ==> (WEAKEN w = W[])``,
   Cases_on `w`
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def,PREFIX_def]
    THEN Cases_on `u`
    THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct]);

val TightPrefix_S_REPEAT =
 prove
  (``!r.
      (!w. S_CLOCK_FREE r /\ WUS_SEM w r ==>
           !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r) ==>
      !w. S_CLOCK_FREE (S_REPEAT r) /\ WUS_SEM w (S_REPEAT r) ==>
          !u. PREFIX u w ==> WUS_SEM (WEAKEN u) (S_REPEAT r)``,
   RW_TAC std_ss [S_CLOCK_FREE_def]
    THEN `!w. WUS_SEM w r ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r`
          by PROVE_TAC[]
    THEN IMP_RES_TAC TightPrefix_WS_CATN
    THEN FULL_SIMP_TAC list_ss [WUS_SEM_REPEAT_WS_CATN]
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THEN ZAP_TAC std_ss [PREFIX_N_EMPTY]
    THEN FULL_SIMP_TAC list_ss [PREFIX_N_EMPTY,WEAKEN_def,A_distinct]
    THEN Q.EXISTS_TAC `0`
    THEN RW_TAC list_ss [WS_CATN_def,TightTrueEmpty]);

val TightPrefix =
 prove
  (``!r. S_CLOCK_FREE r
         ==>
         !w. WUS_SEM w r ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      PROVE_TAC[TightPrefix_S_BOOL],
      (* S_CAT (r,r') *)
      RW_TAC std_ss [S_CLOCK_FREE_def]
       THEN `!w. WUS_SEM w r  ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r`
             by PROVE_TAC[]
       THEN `!w. WUS_SEM w r' ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r'`
             by PROVE_TAC[]
       THEN IMP_RES_TAC TightPrefix_S_CAT,
      (* S_FUSION (r,r') *)
      RW_TAC std_ss [S_CLOCK_FREE_def]
       THEN `!w. WUS_SEM w r  ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r`
              by PROVE_TAC[]
       THEN `!w. WUS_SEM w r' ==> !u. PREFIX u w ==> WUS_SEM (WEAKEN u) r'`
             by PROVE_TAC[]
       THEN IMP_RES_TAC TightPrefix_S_FUSION,
      (* S_OR (r,r') *)
      RW_TAC std_ss [WUS_SEM_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_AND (r,r') *)
      RW_TAC std_ss [WUS_SEM_def,S_CLOCK_FREE_def]
       THEN PROVE_TAC[],
      (* S_EMPTY *)
      RW_TAC std_ss [WUS_SEM_def,S_CLOCK_FREE_def]
       THEN Cases_on `u`
       THEN FULL_SIMP_TAC list_ss [PREFIX_def,CONC_def,WEAKEN_def,A_distinct]
       THEN Cases_on `u`
       THEN FULL_SIMP_TAC list_ss
             [PREFIX_def,CONC_def,WEAKEN_def,A_distinct,A_11],
      (* S_REPEAT r *)
      PROVE_TAC[TightPrefix_S_REPEAT],
      (* S_CLOCK (r,c) *)
      RW_TAC std_ss [S_CLOCK_FREE_def]]);

val NEUTRAL_CONC_EQ =
 store_thm
  ("NEUTRAL_CONC_EQ",
   ``!w v1 v2. (N w = v1 * v2) ==> ?w1 w2. (v1 = N w1) /\ (v2 = N w2)``,
   Cases_on `v1` THEN Cases_on `v2`
    THEN RW_TAC list_ss [CONC_def]);


val FOLDL_NW_FALSE =
 prove
  (``~(N w = FOLDL $* (W l) vlist)``,
   Induct_on `vlist`
    THEN RW_TAC list_ss [CONC_def]);

val FOLDL_NS_FALSE =
 prove
  (``~(N w = FOLDL $* (S l) vlist)``,
   Induct_on `vlist`
    THEN RW_TAC list_ss [CONC_def]);

val US_SEM_WUS_SEM_CATN =
 store_thm
  ("US_SEM_WUS_SEM_CATN",
   ``(!w. US_SEM w r = WUS_SEM (N w) r)
     ==>
     !n w. US_SEM w (WS_CATN n r) = WUS_SEM (N w) (WS_CATN n r)``,
   DISCH_TAC
    THEN Induct
    THEN RW_TAC list_ss [WS_CATN_def,US_SEM,WUS_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THENL
     [Q.EXISTS_TAC `N v1` THEN Q.EXISTS_TAC `N v2`
       THEN PROVE_TAC[CONC_def],
      Cases_on `v1` THEN Cases_on `v2`
       THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct,TOP_FREE_APPEND]
       THEN PROVE_TAC[]]);

(*****************************************************************************)
(* Because this proof is tweaked from one for an earlier version with a      *)
(* ``TOP_FREE w`` hypothesis, it is likely that it is more complicated       *)
(* than needed.                                                              *)
(*****************************************************************************)
local
open FinitePathTheory;
val SIMP =
 RW_TAC list_ss
  [S_CLOCK_FREE_def,US_SEM_def,WUS_SEM_def,IS_STRONG_def,LEN_def,A_ELEM_def,
   ELEM_def,HEAD_def,RESTN_def];
in
val TightNeutralEquiv =
 prove
  (``!r. S_CLOCK_FREE r ==> !w. US_SEM w r = WUS_SEM (N w) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      SIMP,
      (* S_CAT (r,r') *)
      SIMP
       THEN EQ_TAC
       THEN RW_TAC list_ss []
       THENL
        [Q.EXISTS_TAC `N v1` THEN Q.EXISTS_TAC `N v2`
          THEN RW_TAC list_ss [CONC_def],
         IMP_RES_TAC NEUTRAL_CONC_EQ
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [A_11,CONC_def]
          THEN Q.EXISTS_TAC `w1` THEN Q.EXISTS_TAC `w2`
          THEN RW_TAC list_ss []]
       THEN PROVE_TAC[TOP_FREE_APPEND],
      (* S_FUSION (r,r') *)
      SIMP
       THEN EQ_TAC
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [TOP_FREE_APPEND]
       THENL
        [Q.EXISTS_TAC `N v1` THEN Q.EXISTS_TAC `N v2` THEN Q.EXISTS_TAC `N[l]`
          THEN ZAP_TAC list_ss [CONC_def,IS_LETTER_def,TOP_FREE_APPEND]
          THEN RW_TAC list_ss [CONC_def]
          THEN `TOP_FREE([l]++v2)` by PROVE_TAC[TOP_FREE_APPEND]
          THEN FULL_SIMP_TAC list_ss []
          THEN PROVE_TAC[],
         IMP_RES_TAC NEUTRAL_CONC_EQ
          THEN IMP_RES_TAC(GSYM NEUTRAL_CONC_EQ)
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [A_11,CONC_def,IS_LETTER_def]
          THEN RW_TAC list_ss []
          THEN Q.EXISTS_TAC `w1'` THEN Q.EXISTS_TAC `w2` THEN Q.EXISTS_TAC `l`
          THEN FULL_SIMP_TAC list_ss [TOP_FREE_APPEND]
          THEN `TOP_FREE([l]++w2)` by PROVE_TAC[TOP_FREE_APPEND]
          THEN FULL_SIMP_TAC list_ss []
          THEN PROVE_TAC[],
         IMP_RES_TAC NEUTRAL_CONC_EQ
          THEN IMP_RES_TAC(GSYM NEUTRAL_CONC_EQ)
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [A_distinct]],
      (* S_OR (r,r') *)
      SIMP,
      (* S_AND (r,r') *)
      SIMP,
      (* S_EMPTY *)
      SIMP,
      (* S_REPEAT r *)
      RW_TAC list_ss
       [WUS_SEM_REPEAT_WS_CATN,S_CLOCK_FREE_def,US_SEM_REPEAT_CATN]
       THEN EQ_TAC
       THEN RW_TAC list_ss []
       THENL
        [`!w. US_SEM w r = WUS_SEM (N w) r` by PROVE_TAC[]
          THEN POP_ASSUM
                (fn th => ASSUME_TAC(GSYM(MATCH_MP US_SEM_WUS_SEM_CATN th)))
          THEN RW_TAC list_ss [US_SEM_WS_CATN]
          THEN Cases_on `n=0`
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [S_CATN_def,US_SEM]
          THEN `?m. n = SUC m` by Cooper.COOPER_TAC
          THEN DISJ2_TAC
          THEN Q.EXISTS_TAC `m`
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [S_CATN_def,US_SEM]
          THEN PROVE_TAC[],
         Q.EXISTS_TAC `0`
          THEN RW_TAC list_ss [S_CATN_def,US_SEM],
         `!w. US_SEM w r = WUS_SEM (N w) r` by PROVE_TAC[]
          THEN POP_ASSUM
                (fn th => ASSUME_TAC(GSYM(MATCH_MP US_SEM_WUS_SEM_CATN th)))
          THEN `US_SEM w (WS_CATN n r)` by PROVE_TAC[]
          THEN FULL_SIMP_TAC list_ss [US_SEM_WS_CATN]
          THEN PROVE_TAC[]],
      (* S_CLOCK (r,c) *)
      RW_TAC std_ss [S_CLOCK_FREE_def]]);
end;

val _ = export_theory();

