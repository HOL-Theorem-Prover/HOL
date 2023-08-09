(* ------------------------------------------------------------------------- *)
(* Necklace Theory - monocoloured and multicoloured.                         *)
(* ------------------------------------------------------------------------- *)

(*

Necklace Theory
===============

Consider the set N of necklaces of length n (i.e. with number of beads = n)
with a colors (i.e. the number of bead colors = a). A linear picture of such
a necklace is:

+--+--+--+--+--+--+--+
|2 |4 |0 |3 |1 |2 |3 |  p = 7, with (lots of) beads of a = 5 colors: 01234.
+--+--+--+--+--+--+--+

Since a bead can have any of the a colors, and there are n beads in total,

Number of such necklaces = CARD N = a*a*...*a = a^n.

There is only 1 necklace of pure color A, 1 necklace with pure color B, etc.

Number of monocoloured necklaces = a = CARD S, where S = monocoloured necklaces.

So, N = S UNION M, where M = multicoloured necklaces (i.e. more than one color).

Since S and M are disjoint, CARD M = CARD N - CARD S = a^n - a.

*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "necklace";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* val _ = load "helperFunctionTheory"; *)
open arithmeticTheory pred_setTheory listTheory;
open helperNumTheory helperSetTheory;
open helperListTheory; (* for LENGTH_NON_NIL, LIST_TO_SET_SING_IFF *)


(* ------------------------------------------------------------------------- *)
(* Necklace Theory Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Necklace:
   necklace_def      |- !n a. necklace n a =
                              {ls | LENGTH ls = n /\ set ls SUBSET count a}
   necklace_element  |- !n a ls. ls IN necklace n a <=>
                                 LENGTH ls = n /\ set ls SUBSET count a
   necklace_length   |- !n a ls. ls IN necklace n a ==> LENGTH ls = n
   necklace_colors   |- !n a ls. ls IN necklace n a ==> set ls SUBSET count a
   necklace_property |- !n a ls. ls IN necklace n a ==>
                                 LENGTH ls = n /\ set ls SUBSET count a
   necklace_0        |- !a. necklace 0 a = {[]}
   necklace_empty    |- !n. 0 < n ==> (necklace n 0 = {})
   necklace_not_nil  |- !n a ls. 0 < n /\ ls IN necklace n a ==> ls <> []
   necklace_suc      |- !n a. necklace (SUC n) a =
                              IMAGE (\(c,ls). c::ls) (count a CROSS necklace n a)
!  necklace_eqn      |- !n a. necklace n a =
                              if n = 0 then {[]}
                              else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a)
   necklace_1        |- !a. necklace 1 a = {[e] | e IN count a}
   necklace_finite   |- !n a. FINITE (necklace n a)
   necklace_card     |- !n a. CARD (necklace n a) = a ** n

   Mono-colored necklace:
   monocoloured_def  |- !n a. monocoloured n a =
                              {ls | ls IN necklace n a /\ (ls <> [] ==> SING (set ls))}
   monocoloured_element
                     |- !n a ls. ls IN monocoloured n a <=>
                                 ls IN necklace n a /\ (ls <> [] ==> SING (set ls))
   monocoloured_necklace   |- !n a ls. ls IN monocoloured n a ==> ls IN necklace n a
   monocoloured_subset     |- !n a. monocoloured n a SUBSET necklace n a
   monocoloured_finite     |- !n a. FINITE (monocoloured n a)
   monocoloured_0    |- !a. monocoloured 0 a = {[]}
   monocoloured_1    |- !a. monocoloured 1 a = necklace 1 a
   necklace_1_monocoloured
                     |- !a. necklace 1 a = monocoloured 1 a
   monocoloured_empty|- !n. 0 < n ==> monocoloured n 0 = {}
   monocoloured_mono |- !n. monocoloured n 1 = necklace n 1
   monocoloured_suc  |- !n a. 0 < n ==>
                              monocoloured (SUC n) a = IMAGE (\ls. HD ls::ls) (monocoloured n a)
   monocoloured_0_card   |- !a. CARD (monocoloured 0 a) = 1
   monocoloured_card     |- !n a. 0 < n ==> CARD (monocoloured n a) = a
!  monocoloured_eqn      |- !n a. monocoloured n a =
                                  if n = 0 then {[]}
                                  else IMAGE (\c. GENLIST (K c) n) (count a)
   monocoloured_card_eqn |- !n a. CARD (monocoloured n a) = if n = 0 then 1 else a

   Multi-colored necklace:
   multicoloured_def     |- !n a. multicoloured n a = necklace n a DIFF monocoloured n a
   multicoloured_element |- !n a ls. ls IN multicoloured n a <=>
                                     ls IN necklace n a /\ ls <> [] /\ ~SING (set ls)
   multicoloured_necklace|- !n a ls. ls IN multicoloured n a ==> ls IN necklace n a
   multicoloured_subset  |- !n a. multicoloured n a SUBSET necklace n a
   multicoloured_finite  |- !n a. FINITE (multicoloured n a)
   multicoloured_0       |- !a. multicoloured 0 a = {}
   multicoloured_1       |- !a. multicoloured 1 a = {}
   multicoloured_n_0     |- !n. multicoloured n 0 = {}
   multicoloured_n_1     |- !n. multicoloured n 1 = {}
   multicoloured_empty   |- !n. multicoloured n 0 = {} /\ multicoloured n 1 = {}
   multi_mono_disjoint   |- !n a. DISJOINT (multicoloured n a) (monocoloured n a)
   multi_mono_exhaust    |- !n a. necklace n a = multicoloured n a UNION monocoloured n a
   multicoloured_card    |- !n a. 0 < n ==> (CARD (multicoloured n a) = a ** n - a)
   multicoloured_card_eqn|- !n a. CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a
   multicoloured_nonempty|- !n a. 1 < n /\ 1 < a ==> multicoloured n a <> {}
   multicoloured_not_monocoloured
                         |- !n a ls. ls IN multicoloured n a ==> ls NOTIN monocoloured n a
   multicoloured_not_monocoloured_iff
                         |- !n a ls. ls IN necklace n a ==>
                                     (ls IN multicoloured n a <=> ls NOTIN monocoloured n a)
   multicoloured_or_monocoloured
                         |- !n a ls. ls IN necklace n a ==>
                                     ls IN multicoloured n a \/ ls IN monocoloured n a
*)


(* ------------------------------------------------------------------------- *)
(* Helper Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Necklace                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define necklaces as lists of length n, i.e. with n beads, in a colors. *)
Definition necklace_def[nocompute]:
    necklace n a = {ls | LENGTH ls = n /\ (set ls) SUBSET (count a) }
End
(* Note: use [nocompute] as this is not effective. *)

(* Theorem: ls IN necklace n a <=> (LENGTH ls = n /\ (set ls) SUBSET (count a)) *)
(* Proof: by necklace_def *)
Theorem necklace_element:
  !n a ls. ls IN necklace n a <=> (LENGTH ls = n /\ (set ls) SUBSET (count a))
Proof
  simp[necklace_def]
QED

(* Theorem: ls IN (necklace n a) ==> LENGTH ls = n *)
(* Proof: by necklace_def *)
Theorem necklace_length:
  !n a ls. ls IN (necklace n a) ==> LENGTH ls = n
Proof
  simp[necklace_def]
QED

(* Theorem: ls IN (necklace n a) ==> set ls SUBSET count a *)
(* Proof: by necklace_def *)
Theorem necklace_colors:
  !n a ls. ls IN (necklace n a) ==> set ls SUBSET count a
Proof
  simp[necklace_def]
QED

(* Idea: If ls in (necklace n a), LENGTH ls = n and colors in count a. *)

(* Theorem: ls IN (necklace n a) ==> LENGTH ls = n /\ set ls SUBSET count a *)
(* Proof: by necklace_def *)
Theorem necklace_property:
  !n a ls. ls IN (necklace n a) ==> LENGTH ls = n /\ set ls SUBSET count a
Proof
  simp[necklace_def]
QED

(* ------------------------------------------------------------------------- *)
(* Know the necklaces.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: zero-length necklaces of whatever colors is the set of NIL. *)

(* Theorem: necklace 0 a = {[]} *)
(* Proof:
     necklace 0 a
   = {ls | (LENGTH ls = 0) /\ (set ls) SUBSET (count a) }  by necklace_def
   = {ls | ls = [] /\ (set []) SUBSET (count a) }          by LENGTH_NIL
   = {ls | ls = [] /\ [] SUBSET (count a) }                by LIST_TO_SET
   = {[]}                                                  by EMPTY_SUBSET
*)
Theorem necklace_0:
  !a. necklace 0 a = {[]}
Proof
  rw[necklace_def, EXTENSION] >>
  metis_tac[LIST_TO_SET, EMPTY_SUBSET]
QED

(* Idea: necklaces with some length but 0 colors is EMPTY. *)

(* Theorem: 0 < n ==> (necklace n 0 = {}) *)
(* Proof:
     necklace n 0
   = {ls | LENGTH ls = n /\ (set ls) SUBSET (count 0) }  by necklace_def
   = {ls | LENGTH ls = n /\ (set ls) SUBSET {}           by COUNT_0
   = {ls | LENGTH ls = n /\ (set ls = {}) }              by SUBSET_EMPTY
   = {ls | LENGTH ls = n /\ (ls = []) }                  by LIST_TO_SET_EQ_EMPTY
   = {}                                                  by LENGTH_NIL, 0 < n
*)
Theorem necklace_empty:
  !n. 0 < n ==> (necklace n 0 = {})
Proof
  rw[necklace_def, EXTENSION]
QED

(* Idea: A necklace of length n <> 0 is non-NIL. *)

(* Theorem: 0 < n /\ ls IN (necklace n a) ==> ls <> [] *)
(* Proof:
   By contradiction, suppose ls = [].
   Then n = LENGTH ls         by necklace_element
          = LENGTH [] = 0     by LENGTH_NIL
   This contradicts 0 < n.
*)
Theorem necklace_not_nil:
  !n a ls. 0 < n /\ ls IN (necklace n a) ==> ls <> []
Proof
  rw[necklace_def] >>
  metis_tac[LENGTH_NON_NIL]
QED

(* ------------------------------------------------------------------------- *)
(* To show: (necklace n a) is FINITE.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: Relate (necklace (n+1) a) to (necklace n a) for induction. *)

(* Theorem: necklace (SUC n) a =
            IMAGE (\(c, ls). c :: ls) (count a CROSS necklace n a) *)
(* Proof:
   By necklace_def, EXTENSION, this is to show:
   (1) LENGTH x = SUC n /\ set x SUBSET count a ==>
       ?h t. (x = h::t) /\ h < a /\ (LENGTH t = n) /\ set t SUBSET count a
       Note SUC n <> 0                   by SUC_NOT_ZERO
         so ?h t. x = h::t               by list_CASES
       Take these h, t, true             by LENGTH, MEM
   (2) h < a /\ set t SUBSET count a ==> x < a ==> LENGTH (h::t) = SUC (LENGTH t)
       This is true                      by LENGTH
   (3) h < a /\ set t SUBSET count a ==> set (h::t) SUBSET count a
       Note set (h::t) c <=>
            (c = h) \/ set t c           by LIST_TO_SET_DEF
       If c = h, h < a
          ==> h IN count a               by IN_COUNT
       If set t c, set t SUBSET count a
          ==> c IN count a               by SUBSET_DEF
       Thus set (h::t) SUBSET count a    by SUBSET_DEF
*)
Theorem necklace_suc:
  !n a. necklace (SUC n) a =
        IMAGE (\(c, ls). c :: ls) (count a CROSS necklace n a)
Proof
  rw[necklace_def, EXTENSION] >>
  rw[pairTheory.EXISTS_PROD, EQ_IMP_THM] >| [
    `SUC n <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    qexists_tac `h` >>
    qexists_tac `t` >>
    fs[],
    simp[],
    fs[]
  ]
QED

(* Idea: display the necklaces. *)

(* Theorem: necklace n a =
            if n = 0 then {[]}
            else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a) *)
(* Proof: by necklace_0, necklace_suc. *)
Theorem necklace_eqn[compute]:
  !n a. necklace n a =
        if n = 0 then {[]}
        else IMAGE (\(c,ls). c::ls) (count a CROSS necklace (n - 1) a)
Proof
  rw[necklace_0] >>
  metis_tac[necklace_suc, num_CASES, SUC_SUB1]
QED

(*
> EVAL ``necklace 3 2``;
= {[1; 1; 1]; [1; 1; 0]; [1; 0; 1]; [1; 0; 0]; [0; 1; 1]; [0; 1; 0]; [0; 0; 1]; [0; 0; 0]}
> EVAL ``necklace 2 3``;
= {[2; 2]; [2; 1]; [2; 0]; [1; 2]; [1; 1]; [1; 0]; [0; 2]; [0; 1]; [0; 0]}
*)

(* Idea: Unit-length necklaces are singletons from (count a). *)

(* Theorem: necklace 1 a = {[e] | e IN count a} *)
(* Proof:
   Let f = (\(c,ls). c::ls).
     necklace 1 a
   = necklace (SUC 0) a                       by ONE
   = IMAGE f ((count a) CROSS (necklace 0 a)) by necklace_suc
   = IMAGE f ((count a) CROSS {[]})           by necklace_0
   = {[e] | e IN count a}                     by EXTENSION
*)
Theorem necklace_1:
  !a. necklace 1 a = {[e] | e IN count a}
Proof
  rewrite_tac[ONE] >>
  rw[necklace_suc, necklace_0, pairTheory.EXISTS_PROD, EXTENSION]
QED

(* Idea: The set of (necklace n a) is finite. *)

(* Theorem: FINITE (necklace n a) *)
(* Proof:
   By induction on n.
   Base: FINITE (necklace 0 a)
      Note necklace 0 a = {[]}           by necklace_0
       and FINITE {[]}                   by FINITE_SING
   Step: FINITE (necklace n a) ==> FINITE (necklace (SUC n) a)
      Let f = (\(c, ls). c :: ls), b = count a, c = necklace n a.
      Note necklace (SUC n) a
         = IMAGE f (b CROSS c)           by necklace_suc
       and FINITE b                      by FINITE_COUNT
       and FINITE c                      by induction hypothesis
        so FINITE (b CROSS c)            by FINITE_CROSS
      Thus FINITE (necklace (SUC n) a)   by IMAGE_FINITE
*)
Theorem necklace_finite:
  !n a. FINITE (necklace n a)
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[necklace_0] >>
  simp[necklace_suc]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (necklace n a) = a^n.                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: size of (necklace n a) = a^n. *)

(* Theorem: CARD (necklace n a) = a ** n *)
(* Proof:
   By induction on n.
   Base: CARD (necklace 0 a) = a ** 0
        CARD (necklace 0 a)
      = CARD {[]}                            by necklace_0
      = 1                                    by CARD_SING
      = a ** 0                               by EXP_0
   Step: CARD (necklace n a) = a ** n ==>
         CARD (necklace (SUC n) a) = a ** SUC n
      Let f = (\(c, ls). c :: ls), b = count a, c = necklace n a.
      Note FINITE b                          by FINITE_COUNT
       and FINITE c                          by necklace_finite
       and FINITE (b CROSS c)                by FINITE_CROSS
      Also INJ f (b CROSS c) univ(:num list) by INJ_DEF, CONS_11
           CARD (necklace (SUC n) a)
         = CARD (IMAGE f (b CROSS c))        by necklace_suc
         = CARD (b CROSS c)                  by INJ_CARD_IMAGE_EQN
         = CARD b * CARD c                   by CARD_CROSS
         = a * CARD c                        by CARD_COUNT
         = a * a ** n                        by induction hypothesis
         = a ** SUC n                        by EXP
*)
Theorem necklace_card:
  !n a. CARD (necklace n a) = a ** n
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[necklace_0] >>
  qabbrev_tac `f = (\(c:num, ls:num list). c :: ls)` >>
  qabbrev_tac `b = count a` >>
  qabbrev_tac `c = necklace n a` >>
  `FINITE b` by rw[FINITE_COUNT, Abbr`b`] >>
  `FINITE c` by rw[necklace_finite, Abbr`c`] >>
  `necklace (SUC n) a = IMAGE f (b CROSS c)` by rw[necklace_suc, Abbr`f`, Abbr`b`, Abbr`c`] >>
  `INJ f (b CROSS c) univ(:num list)` by rw[INJ_DEF, pairTheory.FORALL_PROD, Abbr`f`] >>
  `FINITE (b CROSS c)` by rw[FINITE_CROSS] >>
  `CARD (necklace (SUC n) a) = CARD (b CROSS c)` by rw[INJ_CARD_IMAGE_EQN] >>
  `_ = CARD b * CARD c` by rw[CARD_CROSS] >>
  `_ = a * a ** n` by fs[Abbr`b`, Abbr`c`] >>
  simp[EXP]
QED

(* ------------------------------------------------------------------------- *)
(* Mono-colored necklace - necklace with a single color.                     *)
(* ------------------------------------------------------------------------- *)

(* Define mono-colored necklace *)
Definition monocoloured_def[nocompute]:
    monocoloured n a =
       {ls | ls IN necklace n a /\ (ls <> [] ==> SING (set ls)) }
End
(* Note: use [nocompute] as this is not effective. *)

(* Theorem: ls IN monocoloured n a <=>
            ls IN necklace n a /\ (ls <> [] ==> SING (set ls)) *)
(* Proof: by monocoloured_def *)
Theorem monocoloured_element:
  !n a ls. ls IN monocoloured n a <=>
           ls IN necklace n a /\ (ls <> [] ==> SING (set ls))
Proof
  simp[monocoloured_def]
QED

(* ------------------------------------------------------------------------- *)
(* Know the Mono-coloured necklaces.                                         *)
(* ------------------------------------------------------------------------- *)

(* Idea: A monocoloured necklace is indeed a necklace. *)

(* Theorem: ls IN monocoloured n a ==> ls IN necklace n a *)
(* Proof: by monocoloured_def *)
Theorem monocoloured_necklace:
  !n a ls. ls IN monocoloured n a ==> ls IN necklace n a
Proof
  simp[monocoloured_def]
QED

(* Idea: The monocoloured set is subset of necklace set. *)

(* Theorem: (monocoloured n a) SUBSET (necklace n a) *)
(* Proof: by monocoloured_necklace, SUBSET_DEF *)
Theorem monocoloured_subset:
  !n a. (monocoloured n a) SUBSET (necklace n a)
Proof
  simp[monocoloured_necklace, SUBSET_DEF]
QED

(* Idea: The monocoloured set is FINITE. *)

(* Theorem: FINITE (monocoloured n a) *)
(* Proof:
   Note (monocoloured n a) SUBSET (necklace n a)  by monocoloured_subset
    and FINITE (necklace n a)                     by necklace_finite
     so FINITE (monocoloured n a)                 by SUBSET_FINITE
*)
Theorem monocoloured_finite:
  !n a. FINITE (monocoloured n a)
Proof
  metis_tac[monocoloured_subset, necklace_finite, SUBSET_FINITE]
QED

(* Idea: Zero-length monocoloured set is singleton NIL. *)

(* Theorem: monocoloured 0 a = {[]} *)
(* Proof:
     monocoloured 0 a
   = {ls | ls IN necklace 0 a /\ (ls <> [] ==> SING (set ls)) }  by monocoloured_def
   = {ls | ls IN {[]} /\ (ls <> [] ==> SING (set ls)) }          by necklace_0
   = {[]}                                                        by IN_SING
*)
Theorem monocoloured_0:
  !a. monocoloured 0 a = {[]}
Proof
  rw[monocoloured_def, necklace_0, EXTENSION, EQ_IMP_THM]
QED

(* Idea: Unit-length monocoloured set are necklaces of length 1. *)

(* Theorem: monocoloured 1 a = necklace 1 a *)
(* Proof:
   By necklace_def, monocoloured_def, EXTENSION,
   this is to show:
      (LENGTH x = 1) /\ set x SUBSET count a /\ (x <> [] ==> SING (set x)) <=>
      (LENGTH x = 1) /\ set x SUBSET count a
   This is true         by LIST_TO_SET_SING
*)
Theorem monocoloured_1:
  !a. monocoloured 1 a = necklace 1 a
Proof
  rw[necklace_def, monocoloured_def, EXTENSION] >>
  metis_tac[LIST_TO_SET_SING]
QED

(* Idea: Unit-length necklaces are monocoloured. *)

(* Theorem: necklace 1 a = monocoloured 1 a *)
(* Proof: by monocoloured_1 *)
Theorem necklace_1_monocoloured:
  !a. necklace 1 a = monocoloured 1 a
Proof
  simp[monocoloured_1]
QED

(* Idea: Some non-NIL necklaces are monocoloured. *)

(* Theorem: 0 < n ==> monocoloured n 0 = {} *)
(* Proof:
   Note (monocoloured n 0) SUBSET (necklace n 0)   by monocoloured_subset
    but necklace n 0 = {}                          by necklace_empty
     so monocoloured n 0 = {}                      by SUBSET_EMPTY
*)
Theorem monocoloured_empty:
  !n. 0 < n ==> monocoloured n 0 = {}
Proof
  metis_tac[monocoloured_subset, necklace_empty, SUBSET_EMPTY]
QED

(* Idea: One-colour necklaces are monocoloured. *)

(* Theorem: monocoloured n 1 = necklace n 1 *)
(* Proof:
   By monocoloured_def, necklace_def, EXTENSION,
   this is to show:
        set x SUBSET count 1 /\ x <> [] ==> SING (set x)
   Note count 1 = {0}           by COUNT_1
    and set x <> {}             by LIST_TO_SET
     so set x = {0}             by SUBSET_SING_IFF
     or SING (set x)            by SING_DEF
*)
Theorem monocoloured_mono:
  !n. monocoloured n 1 = necklace n 1
Proof
  rw[monocoloured_def, necklace_def, EXTENSION, EQ_IMP_THM] >>
  fs[COUNT_1] >>
  `set x = {0}` by fs[SUBSET_SING_IFF] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (monocoloured n a) = a.                                     *)
(* ------------------------------------------------------------------------- *)

(* Idea: Relate (monocoloured (SUC n) a) to (monocoloured n a) for induction. *)

(* Theorem: 0 < n ==> (monocoloured (SUC n) a =
                      IMAGE (\ls. HD ls :: ls) (monocoloured n a)) *)
(* Proof:
   By monocoloured_def, necklace_def, EXTENSION, this is to show:
   (1) 0 < n /\ LENGTH x = SUC n /\ set x SUBSET count a /\ x <> [] ==> SING (set x) ==>
       ?ls. (x = HD ls::ls) /\ (LENGTH ls = n /\ set ls SUBSET count a) /\
            (ls <> [] ==> SING (set ls))
       Note SUC n <> 0                   by SUC_NOT_ZERO
         so x <> []                      by LENGTH_NIL
        ==> ?h t. x = h::t               by list_CASES
        and LENGTH t = n                 by LENGTH
        but t <> []                      by LENGTH_NON_NIL, 0 < n
         so ?k p. t = k::p               by list_CASES
       Thus x = h::k::p                  by above
        Now h IN set x                   by MEM
        and k IN set x                   by MEM, SUBSET_DEF
         so h = k                        by IN_SING, SING (set x)
       Let ls = t,
       then set ls SUBSET count a        by MEM, SUBSET_DEF
        and SING (set ls)                by LIST_TO_SET_DEF
   (2) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       LENGTH (HD ls::ls) = SUC (LENGTH ls)
       This is true                      by LENGTH
   (3) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       set (HD ls::ls) SUBSET count a
       Note ls <> []                     by LENGTH_NON_NIL
         so ?h t. ls = h::t              by list_CASES
       Also set (h::ls) x <=>
            (x = h) \/ set t x           by LIST_TO_SET_DEF
       Thus set (h::ls) SUBSET count a   by SUBSET_DEF
   (4) 0 < LENGTH ls /\ set ls SUBSET count a /\ ls <> [] ==> SING (set ls) ==>
       SING (set (HD ls::ls))
       Note ls <> []                     by LENGTH_NON_NIL
         so ?h t. ls = h::t              by list_CASES
       Also set (h::ls) x <=>
            (x = h) \/ set t x           by LIST_TO_SET_DEF
       Thus SING (set (h::ls))           by SUBSET_DEF
*)
Theorem monocoloured_suc:
  !n a. 0 < n ==> (monocoloured (SUC n) a =
                  IMAGE (\ls. HD ls :: ls) (monocoloured n a))
Proof
  rw[monocoloured_def, necklace_def, EXTENSION] >>
  rw[pairTheory.EXISTS_PROD, EQ_IMP_THM] >| [
    `SUC n <> 0` by decide_tac >>
    `x <> [] /\ ?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `LENGTH t = n` by fs[] >>
    `t <> []` by metis_tac[LENGTH_NON_NIL] >>
    `h IN set x` by fs[] >>
    `?k p. t = k::p` by metis_tac[list_CASES] >>
    `HD t IN set x` by rfs[SUBSET_DEF] >>
    `HD t = h` by metis_tac[SING_DEF, IN_SING] >>
    qexists_tac `t` >>
    fs[],
    simp[],
    `ls <> [] /\ ?h t. ls = h::t` by metis_tac[LENGTH_NON_NIL, list_CASES] >>
    fs[],
    `ls <> [] /\ ?h t. ls = h::t` by metis_tac[LENGTH_NON_NIL, list_CASES] >>
    fs[]
  ]
QED

(* Idea: size of (monocoloured 0 a) = 1. *)

(* Theorem: CARD (monocoloured 0 a) = 1 *)
(* Proof:
   Note monocoloured 0 a = {[]}        by monocoloured_0
     so CARD (monocoloured 0 a) = 1    by CARD_SING
*)
Theorem monocoloured_0_card:
  !a. CARD (monocoloured 0 a) = 1
Proof
  simp[monocoloured_0]
QED

(* Idea: size of (monocoloured n a) = a. *)

(* Theorem: 0 < n ==> CARD (monocoloured n a) = a *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> (CARD (monocoloured 0 a) = a)
      True by 0 < 0 = F.
   Step: 0 < n ==> CARD (monocoloured n a) = a ==>
         0 < SUC n ==> (CARD (monocoloured (SUC n) a) = a)
      If n = 0,
         CARD (monocoloured (SUC 0) a)
       = CARD (monocoloured 1 a)             by ONE
       = CARD (necklace 1 a)                 by monocoloured_1
       = a ** 1                              by necklace_card
       = a                                   by EXP_1
      If n <> 0, then 0 < n.
         Let f = (\ls. HD ls :: ls).
         Then INJ f (monocoloured n a)
                    univ(:num list)          by INJ_DEF, CONS_11
          and FINITE (monocoloured n a)      by monocoloured_finite
          CARD (monocoloured (SUC n) a)
        = CARD (IMAGE f (monocoloured n a))  by monocoloured_suc
        = CARD (monocoloured n a)            by INJ_CARD_IMAGE_EQN
        = a                                  by induction hypothesis
*)
Theorem monocoloured_card:
  !n a. 0 < n ==> CARD (monocoloured n a) = a
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  (Cases_on `n = 0` >> simp[]) >-
  simp[monocoloured_1, necklace_card] >>
  qabbrev_tac `f = \ls:num list. HD ls :: ls` >>
  `INJ f (monocoloured n a) univ(:num list)` by rw[INJ_DEF, Abbr`f`] >>
  `FINITE (monocoloured n a)` by rw[monocoloured_finite] >>
  `CARD (monocoloured (SUC n) a) =
    CARD (IMAGE f (monocoloured n a))` by rw[monocoloured_suc, Abbr`f`] >>
  `_ = CARD (monocoloured n a)` by rw[INJ_CARD_IMAGE_EQN] >>
  fs[]
QED

(* Theorem: monocoloured n a =
            if n = 0 then {[]} else IMAGE (\c. GENLIST (K c) n) (count a) *)
(* Proof:
   If n = 0, true                            by monocoloured_0
   If n <> 0, then 0 < n.
   By monocoloured_def, necklace_def, EXTENSION, this is to show:
   (1) 0 < LENGTH x /\ set x SUBSET count a /\ x <> [] ==> SING (set x) ==>
       ?c. (x = GENLIST (K c) (LENGTH x)) /\ c < a
       Note x <> []                          by LENGTH_NON_NIL
         so ?c. set x = {c}                  by SING_DEF
       Then c < a                            by SUBSET_DEF, IN_COUNT
        and x = GENLIST (K c) (LENGTH x)     by LIST_TO_SET_SING_IFF
   (2) c < a ==> LENGTH (GENLIST (K c) n) = n,
       This is true                          by LENGTH_GENLIST
   (3) c < a ==> set (GENLIST (K c) n) SUBSET count a
       Note set (GENLIST (K c) n) = {c}      by GENLIST_K_SET
         so c < a ==> {c} SUBSET (count a)   by SUBSET_DEF
   (4) c < a /\ GENLIST (K c) n <> [] ==> SING (set (GENLIST (K c) n))
       Note set (GENLIST (K c) n) = {c}      by GENLIST_K_SET
         so SING (set (GENLIST (K c) n))     by SING_DEF
*)
Theorem monocoloured_eqn[compute]:
  !n a. monocoloured n a =
        if n = 0 then {[]}
        else IMAGE (\c. GENLIST (K c) n) (count a)
Proof
  rw_tac bool_ss[] >-
  simp[monocoloured_0] >>
  `0 < n` by decide_tac >>
  rw[monocoloured_def, necklace_def, EXTENSION, EQ_IMP_THM] >| [
    `x <> []` by metis_tac[LENGTH_NON_NIL] >>
    `SING (set x) /\ ?c. set x = {c}` by rw[GSYM SING_DEF] >>
    `c < a` by fs[SUBSET_DEF] >>
    `?b. x = GENLIST (K b) (LENGTH x)` by metis_tac[LIST_TO_SET_SING_IFF] >>
    metis_tac[GENLIST_K_SET, IN_SING],
    simp[],
    rw[GENLIST_K_SET],
    rw[GENLIST_K_SET]
  ]
QED

(*
> EVAL ``monocoloured 2 3``; = {[2; 2]; [1; 1]; [0; 0]}: thm
> EVAL ``monocoloured 3 2``; = {[1; 1; 1]; [0; 0; 0]}: thm
*)

(* Slight improvement of a previous result. *)

(* Theorem: CARD (monocoloured n a) = if n = 0 then 1 else a *)
(* Proof:
   If n = 0,
        CARD (monocoloured 0 a)
      = CARD {[]}                  by monocoloured_eqn
      = 1                          by CARD_SING
   If n <> 0, then 0 < n.
      Let f = (\c:num. GENLIST (K c) n).
      Then INJ f (count a) univ(:num list)
                                   by INJ_DEF, GENLIST_K_SET, IN_SING
       and FINITE (count a)        by FINITE_COUNT
        CARD (monocoloured n a)
      = CARD (IMAGE f (count a))   by monocoloured_eqn
      = CARD (count a)             by INJ_CARD_IMAGE_EQN
      = a                          by CARD_COUNT
*)
Theorem monocoloured_card_eqn:
  !n a. CARD (monocoloured n a) = if n = 0 then 1 else a
Proof
  rw[monocoloured_eqn] >>
  qmatch_abbrev_tac `CARD (IMAGE f (count a)) = a` >>
  `INJ f (count a) univ(:num list)` by
  (rw[INJ_DEF, Abbr`f`] >>
  `0 < n` by decide_tac >>
  metis_tac[GENLIST_K_SET, IN_SING]) >>
  rw[INJ_CARD_IMAGE_EQN]
QED

(* ------------------------------------------------------------------------- *)
(* Multi-colored necklace                                                    *)
(* ------------------------------------------------------------------------- *)

(* Define multi-colored necklace *)
Definition multicoloured_def:
    multicoloured n a = (necklace n a) DIFF (monocoloured n a)
End
(* Note: EVAL can handle set DIFF. *)

(*
> EVAL ``multicoloured 3 2``;
= {[1; 1; 0]; [1; 0; 1]; [1; 0; 0]; [0; 1; 1]; [0; 1; 0]; [0; 0; 1]}: thm
> EVAL ``multicoloured 2 3``;
= {[2; 1]; [2; 0]; [1; 2]; [1; 0]; [0; 2]; [0; 1]}: thm
*)

(* Theorem: ls IN multicoloured n a <=>
            ls IN necklace n a /\ ls <> [] /\ ~SING (set ls) *)
(* Proof:
       ls IN multicoloured n a
   <=> ls IN (necklace n a) DIFF (monocoloured n a)          by multicoloured_def
   <=> ls IN (necklace n a) /\ ls NOTIN (monocoloured n a)   by IN_DIFF
   <=> ls IN (necklace n a) /\
       ~ls IN necklace n a /\ (ls <> [] ==> SING (set ls))   by monocoloured_def
   <=> ls IN (necklace n a) /\ ls <> [] /\ ~SING (set ls)    by logical equivalence

       t /\ ~(t /\ (p ==> q))
     = t /\ (~t \/  ~(p ==> q))
     = t /\ ~t \/ (t /\ ~(~p \/ q))
     = t /\ (p /\ ~q)
*)
Theorem multicoloured_element:
  !n a ls. ls IN multicoloured n a <=>
           ls IN necklace n a /\ ls <> [] /\ ~SING (set ls)
Proof
  (rw[multicoloured_def, monocoloured_def, EQ_IMP_THM] >> simp[])
QED

(* ------------------------------------------------------------------------- *)
(* Know the Multi-coloured necklaces.                                        *)
(* ------------------------------------------------------------------------- *)

(* Idea: multicoloured is a necklace. *)

(* Theorem: ls IN multicoloured n a ==> ls IN necklace n a *)
(* Proof: by multicoloured_def *)
Theorem multicoloured_necklace:
  !n a ls. ls IN multicoloured n a ==> ls IN necklace n a
Proof
  simp[multicoloured_def]
QED

(* Idea: The multicoloured set is subset of necklace set. *)

(* Theorem: (multicoloured n a) SUBSET (necklace n a) *)
(* Proof:
   Note multicoloured n a
      = (necklace n a) DIFF (monocoloured n a)       by multicoloured_def
     so (multicoloured n a) SUBSET (necklace n a)    by DIFF_SUBSET
*)
Theorem multicoloured_subset:
  !n a. (multicoloured n a) SUBSET (necklace n a)
Proof
  simp[multicoloured_def]
QED

(* Idea: multicoloured set is FINITE. *)

(* Theorem: FINITE (multicoloured n a) *)
(* Proof:
   Note multicoloured n a
      = (necklace n a) DIFF (monocoloured n a)    by multicoloured_def
    and FINITE (necklace n a)                     by necklace_finite
     so FINITE (multicoloured n a)                by FINITE_DIFF
*)
Theorem multicoloured_finite:
  !n a. FINITE (multicoloured n a)
Proof
  simp[multicoloured_def, necklace_finite, FINITE_DIFF]
QED

(* Idea: (multicoloured 0 a) is EMPTY. *)

(* Theorem: multicoloured 0 a = {} *)
(* Proof:
     multicoloured 0 a
   = (necklace 0 a) DIFF (monocoloured 0 a)  by multicoloured_def
   = {[]} - {[]}                             by necklace_0, monocoloured_0
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_0:
  !a. multicoloured 0 a = {}
Proof
  simp[multicoloured_def, necklace_0, monocoloured_0]
QED

(* Idea: (mutlicoloured 1 a) is also EMPTY. *)

(* Theorem: multicoloured 1 a = {} *)
(* Proof:
     multicoloured 1 a
   = (necklace 1 a) DIFF (monocoloured 1 a)  by multicoloured_def
   = (necklace 1 a) DIFF (necklace 1 a)      by monocoloured_1
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_1:
  !a. multicoloured 1 a = {}
Proof
  simp[multicoloured_def, monocoloured_1]
QED

(* Idea: (multicoloured n 0) without color is EMPTY. *)

(* Theorem: multicoloured n 0 = {} *)
(* Proof:
   If n = 0,
      Then multicoloured 0 0 = {}              by multicoloured_0
   If n <> 0, then 0 < n.
       multicoloured n 0
     = (necklace n 0) DIFF (monocoloured n 0)  by multicoloured_def
     = {} DIFF (monocoloured n 0)              by necklace_empty
     = {}                                      by EMPTY_DIFF
*)
Theorem multicoloured_n_0:
  !n. multicoloured n 0 = {}
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[multicoloured_0] >>
  simp[multicoloured_def, necklace_empty]
QED

(* Idea: (multicoloured n 1) with one color is EMPTY. *)

(* Theorem: multicoloured n 1 = {} *)
(* Proof:
      multicoloured n 1
   = (necklace n 1) DIFF (monocoloured n 1)  by multicoloured_def
   = {necklace n 1} DIFF (necklace n 1)      by monocoloured_mono
   = {}                                      by DIFF_EQ_EMPTY
*)
Theorem multicoloured_n_1:
  !n. multicoloured n 1 = {}
Proof
  simp[multicoloured_def, monocoloured_mono]
QED

(* Theorem: multicoloured n 0 = {} /\ multicoloured n 1 = {} *)
(* Proof: by multicoloured_n_0, multicoloured_n_1. *)
Theorem multicoloured_empty:
  !n. multicoloured n 0 = {} /\ multicoloured n 1 = {}
Proof
  simp[multicoloured_n_0, multicoloured_n_1]
QED

(* ------------------------------------------------------------------------- *)
(* To show: CARD (multicoloured n a) = a^n - a.                              *)
(* ------------------------------------------------------------------------- *)

(* Idea: a multicoloured necklace is not monocoloured. *)

(* Theorem: DISJOINT (multicoloured n a) (monocoloured n a) *)
(* Proof:
   Let s = necklace n a, t = monocoloured n a.
   Then multicoloured n a = s DIFF t      by multicoloured_def
     so DISJOINT (multicoloured n a) t    by DISJOINT_DIFF
*)
Theorem multi_mono_disjoint:
  !n a. DISJOINT (multicoloured n a) (monocoloured n a)
Proof
  simp[multicoloured_def, DISJOINT_DIFF]
QED

(* Idea: a necklace is either monocoloured or multicolored. *)

(* Theorem: necklace n a = (multicoloured n a) UNION (monocoloured n a) *)
(* Proof:
   Let s = necklace n a, t = monocoloured n a.
   Then multicoloured n a = s DIFF t      by multicoloured_def
    Now t SUBSET s                        by monocoloured_subset
     so necklace n a = s
      = (multicoloured n a) UNION t       by UNION_DIFF
*)
Theorem multi_mono_exhaust:
  !n a. necklace n a = (multicoloured n a) UNION (monocoloured n a)
Proof
  simp[multicoloured_def, monocoloured_subset, UNION_DIFF]
QED

(* Idea: size of (multicoloured n a) = a^n - a. *)

(* Theorem: 0 < n ==> (CARD (multicoloured n a) = a ** n - a) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note t SUBSET s                 by monocoloured_subset
    and FINITE s                   by necklace_finite
        CARD (multicoloured n a)
      = CARD (s DIFF t)            by multicoloured_def
      = CARD s - CARD t            by SUBSET_DIFF_CARD, t SUBSET s
      = a ** n - CARD t            by necklace_card
      = a ** n - a                 by monocoloured_card, 0 < n
*)
Theorem multicoloured_card:
  !n a. 0 < n ==> (CARD (multicoloured n a) = a ** n - a)
Proof
  rpt strip_tac >>
  `(monocoloured n a) SUBSET (necklace n a)` by rw[monocoloured_subset] >>
  `FINITE (necklace n a)` by rw[necklace_finite] >>
  simp[multicoloured_def, SUBSET_DIFF_CARD, necklace_card, monocoloured_card]
QED

(* Theorem: CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a *)
(* Proof:
   If n = 0,
        CARD (multicoloured 0 a)
      = CARD {}                    by multicoloured_0
      = 0                          by CARD_EMPTY
   If n <> 0, then 0 < n.
        CARD (multicoloured 0 a)
      = a ** n - a                 by multicoloured_card
*)
Theorem multicoloured_card_eqn:
  !n a. CARD (multicoloured n a) = if n = 0 then 0 else a ** n - a
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[multicoloured_0] >>
  simp[multicoloured_card]
QED

(* Idea: (multicoloured n a) NOT empty when 1 < n /\ 1 < a. *)

(* Theorem: 1 < n /\ 1 < a ==> (multicoloured n a) <> {} *)
(* Proof:
   Let s = multicoloured n a.
   Then FINITE s               by multicoloured_finite
    and CARD s = a ** n - a    by multicoloured_card
   Note a < a ** n             by EXP_LT, 1 < a, 1 < n
   Thus CARD s <> 0,
     or s <> {}                by CARD_EMPTY
*)
Theorem multicoloured_nonempty:
  !n a. 1 < n /\ 1 < a ==> (multicoloured n a) <> {}
Proof
  rpt strip_tac >>
  qabbrev_tac `s = multicoloured n a` >>
  `FINITE s` by rw[multicoloured_finite, Abbr`s`] >>
  `CARD s = a ** n - a` by rw[multicoloured_card, Abbr`s`] >>
  `a < a ** n` by rw[EXP_LT] >>
  `CARD s <> 0` by decide_tac >>
  rfs[]
QED

(* ------------------------------------------------------------------------- *)

(* For revised necklace proof using GCD. *)

(* Idea: multicoloured lists are not monocoloured. *)

(* Theorem: ls IN multicoloured n a ==> ~(ls IN monocoloured n a) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note multicoloured n a = s DIFF t   by multicoloured_def
     so ls IN multicoloured n a
    ==> ls NOTIN t                     by IN_DIFF
*)
Theorem multicoloured_not_monocoloured:
  !n a ls. ls IN multicoloured n a ==> ~(ls IN monocoloured n a)
Proof
  simp[multicoloured_def]
QED

(* Theorem: ls IN necklace n a ==>
            (ls IN multicoloured n a <=> ~(ls IN monocoloured n a)) *)
(* Proof:
   Let s = necklace n a,
       t = monocoloured n a.
   Note multicoloured n a = s DIFF t   by multicoloured_def
     so ls IN multicoloured n a
    <=> ls IN s /\ ls NOTIN t          by IN_DIFF
*)
Theorem multicoloured_not_monocoloured_iff:
  !n a ls. ls IN necklace n a ==>
           (ls IN multicoloured n a <=> ~(ls IN monocoloured n a))
Proof
  simp[multicoloured_def]
QED

(* Theorem: ls IN necklace n a ==>
            ls IN multicoloured n a \/ ls IN monocoloured n a *)
(* Proof: by multicoloured_def. *)
Theorem multicoloured_or_monocoloured:
  !n a ls. ls IN necklace n a ==>
           ls IN multicoloured n a \/ ls IN monocoloured n a
Proof
  simp[multicoloured_def]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
