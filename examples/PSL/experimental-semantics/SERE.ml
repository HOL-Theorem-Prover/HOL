
(*****************************************************************************)
(* Simple example encoding part of Johan's April 15, 2004 message            *)
(* (with changes for fusion from later messages, and proof hints from Johan) *)
(*                                                                           *)
(* UPDATES:                                                                  *)
(* END changed by Johan Martensson Mon Apr 26 2004                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Load in useful stuff                                                      *)
(*****************************************************************************)
quietdec := true;                         (* Switch off output               *)
map load 
 ["intLib", "Cooper","rich_listTheory"];  (* Load useful theories            *)
intLib.deprecate_int();                   (* Set num as default numbers type *)
open rich_listTheory;                     (* Open theories                   *)
quietdec := false;                        (* Restore output                  *)

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
(* Here is a datatype definition of a type A (hopefully self-explanatory).   *)
(* It creates a tagged disjoint union with elements ``N l`` and ``W l``,     *)
(* where l is a HOL list (a pre-defined datatype).                           *)
(*****************************************************************************)
val A_def =
 Hol_datatype
  `A = N of 'a list
     | W of 'a list`;

(*****************************************************************************)
(* Retrieve from data-base (DB) automatically proved theorems about A        *)
(*****************************************************************************)
val A_11       = assoc "A_11"       (DB.theorems "-")
and A_distinct = assoc "A_distinct" (DB.theorems "-");

val ELEM_def =
 Define
  `(ELEM (N l) n = EL n l) 
   /\
   (ELEM (W l) n = EL n l) `;

(*****************************************************************************)
(* We define concatenation ( * ) on A: if v,w \in N then v*w is just the     *)
(* list concatenation of v and w (remember v,w finite) v*W(w) = W(v*w)       *)
(* and for v\in W and w\in A v*w = v                                         *)
(*****************************************************************************)

(*****************************************************************************)
(* For readability overload "++" onto HOL's list append constant APPEND,     *)
(* and make it a left associative infix with precedence 500.                 *)
(*****************************************************************************)
set_fixity "++" (Infixl 500);
overload_on("++", ``APPEND``);

(*****************************************************************************)
(* Define ``CONC`` for concatenation on values of type A.                    *)
(*****************************************************************************)
set_fixity "CONC" (Infixl 500);

val CONC_def =
 Define
  `(N v CONC N w = N(v++w))
   /\
   (N v CONC W w = W(v++w))
   /\
   (W v CONC a   = W v)`;

(*****************************************************************************)
(* Overload "*" on to "CONC" for readability.                                *)
(*****************************************************************************)
overload_on("*", ``$CONC``);

(*****************************************************************************)
(* We want to show that A is closed under *, that * is associative on A and  *)
(* that \epsilon is the identity for this operation.                         *)
(*****************************************************************************)
val CONC_identity =
 prove
  (``(N[] * a = a) /\ (a * N[] = a)``,
   Cases_on `a`
    THEN RW_TAC list_ss [CONC_def]);

val CONC_assoc =
 prove
  (``a * (b * c) = (a * b) * c``,
   Cases_on `a` THEN Cases_on `b` THEN Cases_on `c`
    THEN RW_TAC list_ss [CONC_def]);

val ASSOC_CONC =
 prove
  (``ASSOC $*``, 
   RW_TAC std_ss [operatorTheory.ASSOC_DEF,CONC_assoc]);

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
   (LEN(W w) = LENGTH w)`;

(*****************************************************************************)
(* we want to show that if w \in N then                                      *)
(* |w*v| = |w|+|v| and                                                       *)
(* |W(w)*v| = |w|                                                            *)
(*****************************************************************************)
val LEN =
 prove
  (``(LEN(N w * a) = LEN(N w) + LEN a)
     /\
     (LEN(W w * a) = LEN(W w))``,
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

(*****************************************************************************)
(* We also define W(w)^k = w^k                                               *)
(*****************************************************************************)
val ELEM_def =
 Define
  `(ELEM (N l) n = EL n l) 
   /\
   (ELEM (W l) n = EL n l) `;

(*****************************************************************************)
(* The problem with fusion is that if w is a weak word that matches          *)
(* the beginning (but not the whole of) r1, then w should match r1:r2, so    *)
(* we need to see to it that the definition doesn't require that l matches   *)
(* the beginning of r2 in this case.                                         *)
(*                                                                           *)
(* This is the point of the end operator. We define for w \in N              *)
(*                                                                           *)
(*  end(w) = \epsilon                                                        *)
(*  end(W(w)) = W(\epsilon)                                                  *)
(*****************************************************************************)
val END_def =
 Define
  `(END(N w) = N[])
   /\
   (END(W w) = W[])`;

(*****************************************************************************)
(* Now we can use it to turn on/turn off words because                       *)
(*                                                                           *)
(* end(v)*w = w but                                                          *)
(* end(W(v))*w = W(\epsilon)                                                 *)
(*****************************************************************************)
val END =
 prove
  (``!v w. (END(N v) * w = w) /\ (END(W v) * w = W[])``,
   GEN_TAC
    THEN Cases_on `w`
    THEN RW_TAC list_ss [LEN_def,CONC_def,END_def]);

(*****************************************************************************)
(* We can now define tight satisfaction:                                     *)
(* w,v and u are finite neutral or weak words.                               *)
(* (definition below incorporates fusion from later message)                 *)
(*                                                                           *)
(* w|==. b     <=> w=\epsilon^- or (w \in N and |w|=1 and w^0||=b)           *)
(* w|==. r1;r2 <=>                                                           *)
(*        there exist v,u s.t. v*u=w and v|==. r1 and u|==.  r2              *)
(* w|==. r1:r2 <=>                                                           *)
(*        there exist v,u \in A and l s.t. v*l*u=w and v*l|==. r1            *)
(*                                          and end(v)*l*u|==.  r2           *)
(* w|==. r1&r2 <=> w|==. r1 and w|==.  r2                                    *)
(* w|==. r1|r2 <=> w|==. r1 or  w|==.  r2                                    *)
(* w|==. r*   <=> either w=\epsilon or there exists w1,w2,..wn such that     *)
(*                     w=*(w1w2..wn)=w1*w2*..*wn                             *)
(*                     and forall 1<=k<=n wk|==. r                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Boolean expressions                                                       *)
(*****************************************************************************)
val bexp_def =
 Hol_datatype
  `bexp = B_PROP   of 'a                         (* atomic proposition       *)
        | B_NOT    of bexp                       (* negation                 *)
        | B_AND    of bexp # bexp`;              (* conjunction              *)

(*****************************************************************************)
(* B_SEM l b means "l |= b" where l is a letter, i.e. l : 'prop -> bool      *)
(*****************************************************************************)
val B_SEM_def =
 Define
  `(B_SEM l (B_PROP(p:'prop)) = p IN l)
   /\
   (B_SEM l (B_NOT b)         = ~(B_SEM l b))
   /\
   (B_SEM l (B_AND(b1,b2))    = B_SEM l b1 /\ B_SEM l b2)`;

(*****************************************************************************)
(* Syntax of Sequential Extended Regular Expressions (SEREs)                 *)
(*****************************************************************************)
val sere_def =
 Hol_datatype
  `sere = S_BOOL        of 'a bexp               (* boolean expression       *)
        | S_CAT         of sere # sere           (* r1 ;  r2                 *)
        | S_FUSION      of sere # sere           (* r1 :  r2                 *)
        | S_OR          of sere # sere           (* r1 |  r2                 *)
        | S_AND         of sere # sere           (* r1 && r2                 *)
        | S_REPEAT      of sere`;                (* r[*]                     *)

(*****************************************************************************)
(* Structural induction rule for SEREs                                       *)
(*****************************************************************************)
val sere_induct = save_thm
  ("sere_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(r1,r2). P r1 /\ P r2`]
         (TypeBase.induction_of "sere")))));

(*****************************************************************************)
(* Some auxiliary definitions                                                *)
(*****************************************************************************)
val IS_WEAK_def   = Define `(IS_WEAK (W w)   = T) /\ (IS_WEAK (N w)   = F)`
and IS_NEUTRAL_def = Define `(IS_NEUTRAL (W w) = F) /\ (IS_NEUTRAL (N w) = T)`;

val IS_LETTER_def =
 Define
  `(IS_LETTER(N w) = ?l. w = [l])
   /\
   (IS_LETTER(W w) = ?l. w = [l])`;

(*****************************************************************************)
(* Semantics of SEREs                                                        *)
(*****************************************************************************)
val US_SEM_def =
 Define
  `(US_SEM v (S_BOOL b) = (IS_WEAK v   /\ (LEN v = 0))
                           \/ 
                          (IS_NEUTRAL v /\ (LEN v = 1) /\ B_SEM (ELEM v 0) b))
   /\
   (US_SEM v (S_CAT(r1,r2)) =
     ?v1 v2. (v = v1 * v2) /\ US_SEM v1 r1 /\ US_SEM v2 r2)
   /\
   (US_SEM v (S_FUSION(r1,r2)) =
     ?v1 v2 l. IS_LETTER l /\ (v = v1*l*v2)
               /\  
               US_SEM (v1*l) r1  /\ US_SEM (END(v1)*l*v2) r2)
   /\
   (US_SEM v (S_OR(r1,r2)) =
     US_SEM v r1 \/ US_SEM v r2)
   /\
   (US_SEM v (S_AND(r1,r2)) =
     US_SEM v r1 /\ US_SEM v r2)
   /\
   (US_SEM v (S_REPEAT r) =
     ?vlist. (v = FOLDL $* (N[]) vlist) /\ EVERY (\v. US_SEM v r) vlist)`;

(*****************************************************************************)
(* We can now prove with fusion in the language                              *)
(*   for all r: W(\espilon)|==.r                                             *)
(*****************************************************************************)
local
val S_SEM_SIMP_TAC =
 RW_TAC list_ss [US_SEM_def,IS_WEAK_def,IS_NEUTRAL_def,LEN_def,ELEM_def]
in
val TightTrueEmpty =
 prove
  (``!r. US_SEM (W[]) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      S_SEM_SIMP_TAC,
      (* S_CAT (r,r') *)
      S_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W []`
       THEN RW_TAC list_ss [CONC_def],
      (* S_FUSION (r,r') *)
      S_SEM_SIMP_TAC
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W []`
       THEN Q.EXISTS_TAC `W [b]`
       THEN RW_TAC list_ss [CONC_def,END,IS_LETTER_def],
      (* S_OR (r,r') *)
      S_SEM_SIMP_TAC,
      (* S_AND (r,r') *)
      S_SEM_SIMP_TAC,
      (* S_REPEAT (r,r') *)
      S_SEM_SIMP_TAC  
       THEN Q.EXISTS_TAC `[W []]`
       THEN RW_TAC list_ss [CONC_def]])
end;

(*****************************************************************************)
(* Weaken a word                                                             *)
(*****************************************************************************)
val WEAKEN_def = Define `(WEAKEN(N l) = W l) /\ (WEAKEN(W l) = W l)`;

val WEAKEN =
 prove
  (``(IS_WEAK(WEAKEN w) = T) /\ (IS_NEUTRAL(WEAKEN w) = F)``,
   Cases_on `w`
    THEN RW_TAC list_ss [IS_WEAK_def,IS_NEUTRAL_def,WEAKEN_def]);

val LEN_WEAKEN =
 prove
  (``LEN(WEAKEN w) = LEN w``,
   Cases_on `w`
    THEN RW_TAC list_ss [WEAKEN_def,LEN_def]);

(*****************************************************************************)
(* Tight prefix theorem                                                      *)
(* w|==.r and u<w => W(u)|==.r                                               *)
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
     [Q.EXISTS_TAC `N(l''++l''')`
       THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `W(l''++l''')`
       THEN RW_TAC list_ss [CONC_def]]);

(*****************************************************************************)
(* Not sure if this is needed                                                *)
(*****************************************************************************)
val STRICT_PREFIX_CONC =
 prove
  (``STRICT_PREFIX u v1 ==> !v2. STRICT_PREFIX u (v1 * v2)``,
   Cases_on `u` THEN Cases_on `v1`
    THEN RW_TAC list_ss [STRICT_PREFIX_def,PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `v2`
    THEN FULL_SIMP_TAC list_ss [CONC_def,A_11,A_distinct]
    THENL
     [Q.EXISTS_TAC `N(l''++l''')`
       THEN RW_TAC list_ss [CONC_def],
      Q.EXISTS_TAC `W(l''++l''')`
       THEN RW_TAC list_ss [CONC_def],
      Cases_on `l = l' ++ l'''`
       THEN RW_TAC list_ss []
       THEN `l''' ++ l'' = []` by PROVE_TAC[APPEND_ASSOC,APPEND_NIL_CANCEL]
       THEN `(l''' = []) /\ (l'' = [])` by PROVE_TAC[APPEND_EQ_NIL,LENGTH_NIL]
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []]);

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
     (PREFIX (N(u ++ v1)) (W(u ++ v2)) ==> PREFIX (N v1) (W v2)) /\
     (PREFIX (W(u ++ v1)) (W(u ++ v2)) ==> PREFIX (W v1) (W v2))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u'`
    THEN FULL_SIMP_TAC std_ss 
          [GSYM APPEND_ASSOC,CONC_def,A_11,A_distinct,APPEND_LEFT_CANCEL]
    THEN PROVE_TAC[CONC_def]);

val STRICT_PREFIX_CANCEL =
 prove
  (``(STRICT_PREFIX (N(u ++ v1)) (N(u ++ v2)) ==> STRICT_PREFIX (N v1) (N v2)) /\
     (STRICT_PREFIX (W(u ++ v1)) (N(u ++ v2)) ==> STRICT_PREFIX (W v1) (N v2)) /\
     (STRICT_PREFIX (N(u ++ v1)) (W(u ++ v2)) ==> STRICT_PREFIX (N v1) (W v2)) /\
     (STRICT_PREFIX (W(u ++ v1)) (W(u ++ v2)) ==> STRICT_PREFIX (W v1) (W v2))``,
   RW_TAC list_ss [STRICT_PREFIX_def]
    THEN PROVE_TAC[PREFIX_CANCEL]);

val B_FALSE_def =
 Define `B_FALSE = B_AND(B_PROP ARB, B_NOT(B_PROP ARB))`;

val B_FALSE =
 prove
  (``B_SEM v B_FALSE = F``,
   RW_TAC list_ss [B_FALSE_def,B_SEM_def]);

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

val S_CATN_def =
 Define
  `(S_CATN 0 r = r) /\ (S_CATN (SUC n) r = S_CAT(r, S_CATN n r))`;

val ASSOC_FOLDL =
 prove
  (``!l x y. ASSOC f ==> (FOLDL f (f x y) l = f x (FOLDL f y l))``,
   Induct
    THEN RW_TAC list_ss [operatorTheory.ASSOC_DEF]);

val FOLDL_CONCAT_N =
 prove
  (``!vlist v. FOLDL $* v vlist = v * FOLDL $* (N []) vlist``,
   PROVE_TAC[ASSOC_FOLDL,ASSOC_CONC,CONC_identity]);

 val US_SEM_CAT_REPEAT_CATN =                      
  store_thm                                                                
   ("US_SEM_CAT_REPEAT_CATN",                                                  
    ``!v r. US_SEM v (S_CAT(S_REPEAT r, r)) = ?n. US_SEM v (S_CATN n r)``,
    RW_TAC list_ss [US_SEM_def]
     THEN EQ_TAC
     THEN RW_TAC list_ss []
     THENL                                                                 
      [Induct_on `vlist`
        THEN RW_TAC list_ss [CONC_identity,S_CATN_def,US_SEM_def]
        THEN ZAP_TAC std_ss [S_CATN_def]
        THEN RW_TAC std_ss []
        THEN RES_TAC
        THEN Q.EXISTS_TAC `SUC n` 
        THEN RW_TAC list_ss [S_CATN_def,US_SEM_def]
        THEN Q.EXISTS_TAC `h` THEN Q.EXISTS_TAC `FOLDL $* (N []) vlist * v2`
        THEN RW_TAC std_ss []
        THEN PROVE_TAC[FOLDL_CONCAT_N,CONC_assoc],
       Q.UNDISCH_TAC `US_SEM v (S_CATN n r)`
        THEN Q.SPEC_TAC(`v`,`v`)
        THEN Q.SPEC_TAC(`r`,`r`)
        THEN Q.SPEC_TAC(`n`,`n`)
        THEN Induct
        THEN RW_TAC list_ss [S_CATN_def]
        THENL                                                              
         [Q.EXISTS_TAC `N[]` THEN Q.EXISTS_TAC `v`
           THEN RW_TAC list_ss [CONC_identity]
           THEN Q.EXISTS_TAC `[]`
           THEN RW_TAC list_ss [],
          FULL_SIMP_TAC list_ss [US_SEM_def]
           THEN RES_TAC
           THEN RW_TAC std_ss []
           THEN Q.EXISTS_TAC `v1 * FOLDL $* (N []) vlist` THEN Q.EXISTS_TAC `v2'`
           THEN RW_TAC std_ss [CONC_assoc]
           THEN Q.EXISTS_TAC `v1::vlist`
           THEN RW_TAC list_ss [CONC_identity]
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
    THEN RW_TAC list_ss [FOLDLN_def,CONC_assoc]);

val FOLDLN_CATN =
 prove
  (``!l v0 r.
      ALL_EL (\v. US_SEM v r) l /\ US_SEM v0 r 
      ==> 
      !n. n <= LENGTH l ==> US_SEM (FOLDLN n $* v0 l) (S_CATN n r)``,
   Induct
    THEN RW_TAC list_ss [FOLDLN_def,S_CATN_def]
    THEN Cases_on `n = 0`
    THEN RW_TAC list_ss [FOLDLN_def,S_CATN_def]
    THEN `?m. n = SUC m` by Cooper.COOPER_TAC
    THEN RW_TAC list_ss [FOLDLN_def,S_CATN_def]
    THEN FULL_SIMP_TAC arith_ss [US_SEM_def]
    THEN RES_TAC
    THEN Q.EXISTS_TAC `v0`
    THEN Q.EXISTS_TAC `FOLDLN m $* h l`
    THEN RW_TAC list_ss [FOLDLN_ASSOC]);

 val US_SEM_REPEAT_CATN =                      
  store_thm                                                                
   ("US_SEM_REPEAT_CATN",                                                  
    ``!v r. US_SEM v (S_REPEAT r) = (v = N[]) \/ ?n. US_SEM v (S_CATN n r)``,
    RW_TAC list_ss []
     THEN EQ_TAC
     THENL
      [SIMP_TAC list_ss[US_SEM_def]
        THEN REPEAT STRIP_TAC
        THEN Cases_on `v = N[]`
        THEN ASM_REWRITE_TAC[]
        THEN Cases_on `vlist`
        THEN FULL_SIMP_TAC list_ss [CONC_identity]
        THEN RES_TAC
        THEN `LENGTH t <= LENGTH t` by DECIDE_TAC
        THEN IMP_RES_TAC FOLDLN_CATN
        THEN Q.EXISTS_TAC `LENGTH t`
        THEN FULL_SIMP_TAC list_ss [FOLDLN_LENGTH],
       RW_TAC list_ss [US_SEM_def]
        THENL
         [Q.EXISTS_TAC `[]`
           THEN RW_TAC list_ss [],
          Q.UNDISCH_TAC `US_SEM v (S_CATN n r)`
           THEN Q.SPEC_TAC(`v`,`v`)
           THEN Q.SPEC_TAC(`r`,`r`)
           THEN Q.SPEC_TAC(`n`,`n`)
           THEN Induct
           THEN RW_TAC list_ss [S_CATN_def]
           THENL
            [Q.EXISTS_TAC `[v]`
              THEN RW_TAC list_ss [CONC_identity],
             FULL_SIMP_TAC list_ss [US_SEM_def]
              THEN RES_TAC
              THEN Q.EXISTS_TAC `v1::vlist`
              THEN RW_TAC list_ss [CONC_identity]
              THEN PROVE_TAC[FOLDL_CONCAT_N]]]]);

val WEAKEN_CONC =
 prove
  (``!v w. WEAKEN v * w = WEAKEN v``,
   Induct
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def]);

val END_WEAKEN =
 prove
  (``!v. END(WEAKEN v) = W[]``,
   Induct
    THEN RW_TAC list_ss [CONC_def,WEAKEN_def,END_def]);

val NN_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (N u) (N v) ==> PREFIX (N(w ++ u)) (N(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_identity,A_11,A_distinct]
    THENL
     [PROVE_TAC[CONC_identity],
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
          [CONC_def,CONC_identity,A_11,A_distinct]);

val NW_APPEND_PREFIX =
 prove
  (``!u v. PREFIX (N u) (W v) ==> PREFIX (N(w ++ u)) (W(w ++ v))``,
   RW_TAC list_ss [PREFIX_def,CONC_def]
    THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `v` THEN Cases_on `w`
    THEN FULL_SIMP_TAC list_ss
          [CONC_def,CONC_identity,A_11,A_distinct]
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
          [CONC_def,CONC_identity,A_11,A_distinct]);

val APPEND_STRICT_PREFIX =
 prove
  (``!u v.
      (STRICT_PREFIX (N u) (N v) ==> STRICT_PREFIX (N(w ++ u)) (N(w ++ v))) /\
      (STRICT_PREFIX (W u) (N v) ==> STRICT_PREFIX (W(w ++ u)) (N(w ++ v))) /\
      (STRICT_PREFIX (N u) (W v) ==> STRICT_PREFIX (N(w ++ u)) (W(w ++ v))) /\
      (STRICT_PREFIX (W u) (W v) ==> STRICT_PREFIX (W(w ++ u)) (W(w ++ v)))``,
   RW_TAC list_ss 
    [STRICT_PREFIX_def,
     NN_APPEND_PREFIX,WN_APPEND_PREFIX,NW_APPEND_PREFIX,WW_APPEND_PREFIX]);

val NOT_STRICT_PREFIX_N =
 prove
  (``!u. ~STRICT_PREFIX u (N [])``,
   GEN_TAC
    THEN Cases_on `u` 
    THEN RW_TAC list_ss [CONC_def,STRICT_PREFIX_def,PREFIX_def]
    THEN Cases_on `l = []`
    THEN RW_TAC list_ss [CONC_def]
    THEN Cases_on `u` 
    THEN RW_TAC list_ss [CONC_def,STRICT_PREFIX_def,PREFIX_def]);

local
val S_SEM_SIMPS =
  [US_SEM_def,IS_WEAK_def,IS_NEUTRAL_def,LEN_def,ELEM_def,
   WEAKEN_def,WEAKEN,LEN_WEAKEN,PREFIX_def,STRICT_PREFIX_def,CONC_def];
in
val TightPrefix_S_BOOL =
 prove
  (``!b w. 
      US_SEM w (S_BOOL b)
      ==>
      !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) (S_BOOL b)``,
   RW_TAC list_ss S_SEM_SIMPS
    THEN Cases_on `u` THEN Cases_on `u'`
    THEN FULL_SIMP_TAC list_ss (S_SEM_SIMPS@[CONC_def,A_11,A_distinct])
    THEN `(LENGTH l = 0) \/ (LENGTH l' = 0)` by DECIDE_TAC
    THEN `l' = []` by PROVE_TAC[LENGTH_NIL]
    THEN FULL_SIMP_TAC list_ss [])
end;

val TightPrefix_S_CAT =
 prove
  (``(!w. US_SEM w r ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r) /\
     (!w. US_SEM w r' ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r')
     ==>
     !w. US_SEM w (S_CAT (r,r')) 
         ==>
         !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) (S_CAT (r,r'))``,
   RW_TAC list_ss [US_SEM_def]
    THEN Cases_on `STRICT_PREFIX u v1`
    THENL
     [RES_TAC
       THEN Q.EXISTS_TAC `WEAKEN u` THEN Q.EXISTS_TAC `v2`
       THEN RW_TAC list_ss []
       THEN Cases_on `u` THEN Cases_on `v2`
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def],
      `PREFIX v1 u` by PROVE_TAC[PREFIX_TRICHOTOMY,STRICT_PREFIX_def,PREFIX_CONC,PREFIX_REFL]
       THEN FULL_SIMP_TAC list_ss [PREFIX_def]
       THEN Cases_on `v1` THEN Cases_on `v2` THEN Cases_on `u` THEN Cases_on `u'`
       THEN FULL_SIMP_TAC list_ss [WEAKEN_def,CONC_def,A_11,A_distinct]
       THEN Q.EXISTS_TAC`N l` THEN Q.EXISTS_TAC `W l'''`
       THEN RW_TAC list_ss [CONC_def]
       THEN IMP_RES_TAC STRICT_PREFIX_CANCEL
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [WEAKEN_def]]);

val TightPrefix_S_FUSION =
 prove
  (``(!w. US_SEM w r ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r) /\
     (!w. US_SEM w r' ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r')
     ==>
     !w. US_SEM w (S_FUSION (r,r')) 
         ==>
         !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) (S_FUSION (r,r'))``,
   RW_TAC list_ss [US_SEM_def]
    THEN Cases_on `STRICT_PREFIX u (v1 * l)`
    THENL
     [`US_SEM (WEAKEN u) r` by PROVE_TAC[]
       THEN `US_SEM (WEAKEN u * l) r` by PROVE_TAC[WEAKEN_CONC]
       THEN `US_SEM (W[]) r'` by PROVE_TAC[TightTrueEmpty]
       THEN `US_SEM (END(WEAKEN u) * (l * v2)) r'` by RW_TAC list_ss [END_WEAKEN,CONC_def]
       THEN Q.EXISTS_TAC `WEAKEN u` THEN Q.EXISTS_TAC `v2` THEN Q.EXISTS_TAC `l`
       THEN RW_TAC list_ss []
       THEN Cases_on `u` 
       THEN RW_TAC list_ss [WEAKEN_def,CONC_def]
       THEN FULL_SIMP_TAC std_ss [CONC_assoc,WEAKEN_def],
      `PREFIX (v1 * l) u` by PROVE_TAC[PREFIX_TRICHOTOMY,STRICT_PREFIX_def,PREFIX_CONC,PREFIX_REFL]
       THEN FULL_SIMP_TAC list_ss [PREFIX_def]
       THEN Cases_on `v1` THEN Cases_on `v2` THEN Cases_on `u` THEN Cases_on `u'` THEN Cases_on `l`
       THEN FULL_SIMP_TAC list_ss [WEAKEN_def,CONC_def,A_11,A_distinct]
       THEN Q.EXISTS_TAC`N l'` THEN Q.EXISTS_TAC `W l''''` THEN Q.EXISTS_TAC `N l'''''` 
       THEN RW_TAC list_ss [CONC_def,END_def]
       THEN FULL_SIMP_TAC list_ss [CONC_def,END_def]
       THEN IMP_RES_TAC STRICT_PREFIX_CANCEL
       THEN PROVE_TAC[APPEND_STRICT_PREFIX,WEAKEN_def]]);

val TightPrefix_S_CATN =
 prove
  (``(!w. US_SEM w r ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r) 
     ==>
     !n w. 
      US_SEM w (S_CATN n r) 
      ==>
      !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) (S_CATN n r)``,
   DISCH_TAC
    THEN Induct
    THEN RW_TAC list_ss [S_CATN_def]
    THEN RES_TAC
    THEN IMP_RES_TAC TightPrefix_S_CAT);
 
val TightPrefix =
 prove
  (``!r w. US_SEM w r ==> !u. STRICT_PREFIX u w ==> US_SEM (WEAKEN u) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      PROVE_TAC[TightPrefix_S_BOOL],
      (* S_CAT (r,r') *)
      RW_TAC std_ss []
       THEN IMP_RES_TAC TightPrefix_S_CAT,
      (* S_FUSION (r,r') *)
      RW_TAC std_ss []
       THEN IMP_RES_TAC TightPrefix_S_FUSION,
      (* S_OR (r,r') *)
      RW_TAC std_ss [US_SEM_def]
       THEN PROVE_TAC[],
      (* S_AND (r,r') *)
      RW_TAC std_ss [US_SEM_def]
       THEN PROVE_TAC[],
      (* S_REPEAT (r,r') *)
      PROVE_TAC[US_SEM_REPEAT_CATN,NOT_STRICT_PREFIX_N,TightPrefix_S_CATN]]);


