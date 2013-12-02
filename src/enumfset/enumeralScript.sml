(* file HS/PIN/enumeralScript.sml, created 4/15/13 F.L. Morris *)
(* PIN-based finite set representation; name a homage to numeralTheory *)
(* Revision of 5/12/13 - bringing back bt & bl to avoid finiteness hyps. *)

structure enumeralScript = struct

open HolKernel boolLib Parse;

(* app load ["totoTheory", "res_quanLib", "intLib", "totoTacs"]; *)

val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory res_quanTheory res_quanLib;
open totoTheory bossLib listTheory totoTacs;

val _ = new_theory "enumeral";

(* "enumeral" for "enumerated finite set", wordplay on "NUMERAL" *)

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val _ = Defn.def_suffix := ""; (* replacing default "_def" *)

(* ***************************************************************** *)
(* Following switch, BigSig, allows "maybe_thm" to act either as     *)
(* store_thm or as prove, thus maximizing or minimizing the output   *)
(* from print_theory and the stuff known to DB.match, DB.find        *)
(* ***************************************************************** *)

val BigSig = false;

fun maybe_thm (s, tm, tac) = if BigSig then store_thm (s, tm, tac)
                                       else prove (tm, tac);

val _ = Hol_datatype `bt = nt | node of bt => 'a => bt`;
val _ = Hol_datatype `bl = nbl | zerbl of bl
                               | onebl of 'a => 'a bt => bl`;

val bt_11 = save_thm ("bt_11", theorem "bt_11");
(* |- !a0 a1 a2 a0' a1' a2'. (node a0 a1 a2 = node a0' a1' a2') <=>
                             (a0 = a0') /\ (a1 = a1') /\ (a2 = a2') *)

val bt_distinct = save_thm ("bt_distinct", theorem "bt_distinct");
(* |- !a2 a1 a0. nt <> node a0 a1 a2 *)

val bt_case_def = save_thm ("bt_case_def", definition "bt_case_def");

val bt_size_def = definition "bt_size_def";
(* |- (!f. bt_size f nt = 0) /\
       !f a0 a1 a2. bt_size f (node a0 a1 a2) =
         1 + (bt_size f a0 + (f a1 + bt_size f a2)) *)

val bl_size_def = definition "bl_size_def";
(* |- (!f. bl_size f nbl = 0) /\
       (!f a. bl_size f (zerbl a) = 1 + bl_size f a) /\
       !f a0 a1 a2. bl_size f (onebl a0 a1 a2) =
         1 + (f a0 + (bt_size f a1 + bl_size f a2)) *)

(* helper function, BL_ACCUM, for use only by BL_CONS: *)

val BL_ACCUM = Define`(BL_ACCUM (a:'a) ac nbl = onebl a ac nbl)
                   /\ (BL_ACCUM a ac (zerbl bl) = onebl a ac bl)
                   /\ (BL_ACCUM a ac (onebl r rft bl) =
                        zerbl (BL_ACCUM a (node ac r rft) bl))`;

val BL_CONS = Define`BL_CONS (a:'a) bl = BL_ACCUM a nt bl`;

val list_to_bl = Define`(list_to_bl [] = nbl)
                     /\ (list_to_bl (a:'a :: l) = BL_CONS a (list_to_bl l))`;

(* flatten a bt back to a list, without and with an accumulating parameter. *)

val bt_to_list = Define
`(bt_to_list (nt:'a bt) = []) /\
 (bt_to_list (node l x r) = bt_to_list l ++ [x] ++ bt_to_list r)`;

val bt_to_list_ac = Define
`(bt_to_list_ac (nt:'a bt) m = m) /\
 (bt_to_list_ac (node l x r) m = bt_to_list_ac l (x :: bt_to_list_ac r m))`;

val bt_to_list_ac_thm = maybe_thm ("bt_to_list_ac_thm",
``!t:'a bt m. bt_to_list_ac t m = bt_to_list t ++ m``,
Induct THEN RW_TAC (srw_ss ()) [bt_to_list, bt_to_list_ac]);

val bt_to_list_thm = store_thm ("bt_to_list_thm",
``!t:'a bt. bt_to_list t = bt_to_list_ac t []``,
REWRITE_TAC [bt_to_list_ac_thm, APPEND_NIL]);

(* Although we should have no need to prove in HOL that bl's built with
BL_CONS have the desirable balance properties that make them efficient,
we do need a lemma about the size of bl's to support inductive definitions.*)

(* helper function, bt_rev, for use here and below by bt_to_bl: *)

val bt_rev = Define
   `(bt_rev (nt:'a bt) bl = bl)
 /\ (bt_rev (node lft r rft) bl = bt_rev lft (onebl r rft bl))`;

val K2 = Define`K2 (a:'a) = 2`;

val bt_rev_size = maybe_thm ("bt_rev_size", Term
`!ft bl:'a bl. bl_size K2 (bt_rev ft bl) = bt_size K2 ft + bl_size K2 bl`,
Induct THEN
ASM_REWRITE_TAC [bl_size_def, bt_size_def, K2,bt_rev,arithmeticTheory.ADD] THEN
SIMP_TAC arith_ss []);

(* How to turn a bl into a bt (unreversibly). bl_rev is named after the
   classical helper function for reverse (listTheory's REV). *)

val bl_rev = Define`(bl_rev ft (nbl:'a bl) = ft) /\
                 (bl_rev ft (zerbl b) = bl_rev ft b) /\
                 (bl_rev ft (onebl a f b) = bl_rev (node ft a f) b)`;

val bl_to_bt = Define`bl_to_bt = bl_rev (nt:'a bt)`;

(* And how to turn a bt into a condensed bl (or "cl") - zerbls omitted -
   by dissasembling left subtrees only. Helper bt_rev is defined above. *)

val bt_to_bl = Define`bt_to_bl (t:'a bt) = bt_rev t nbl`;

(* Likely to be needed: *)

val slinky = maybe_thm ("slinky", Term
`!(t:'a bt) bb. bl_to_bt (bt_rev t bb) = bl_rev t bb`,
Induct THENL
[REWRITE_TAC [bl_to_bt, bt_rev]
,REPEAT GEN_TAC THEN ASM_REWRITE_TAC [bt_rev, bl_rev]]);

val bt_to_bl_to_bt_ID = maybe_thm ("bt_to_bl_to_bt_ID", Term
`!t:'a bt. bl_to_bt (bt_to_bl t) = t`,
REWRITE_TAC [bt_to_bl, slinky, bl_rev]);

val list_to_bt = Define`list_to_bt (l:'c list) = bl_to_bt (list_to_bl l)`;

(* *****  We use "OL" for strictly                                  ***** *)
(* ***** ordered lists where the whole element is the key;          ***** *)
(* ***** eventually "ORL" for function-modeling sorted lists.       ***** *)

val OL = Define`(OL (cmp:'a toto) ([]:'a list) = T) /\
                (OL cmp (a :: l) = OL cmp l /\
                   (!p. MEM p l ==> (apto cmp a p = LESS)))`;

(* ***************************************************************** *)
(*  merge sorting for sets here, with initial "s"; plain merge etc.  *)
(*  are reserved as names for association-list sorting.              *)
(* ***************************************************************** *)

val smerge = Define
`(smerge (cmp:'a toto) [] [] = []) /\
 (smerge cmp (x:'a :: l) [] = x :: l) /\
 (smerge cmp [] (y:'a :: m) = y :: m) /\
 (smerge cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => x :: (smerge cmp l (y :: m))
                                 | EQUAL => x :: (smerge cmp l m)
                                 | GREATER => y :: (smerge cmp (x :: l) m))`;

val smerge_nil = store_thm ("smerge_nil",
``!cmp:'a toto l. (smerge cmp l [] = l) /\ (smerge cmp [] l = l)``,
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [smerge]);

(* corresponding merge_set will need ORL hypotheses, and corresp. merge_ORL
   will need 3 `merge ... =  ... UNION ...` by MATCH_MP_TAC merge_set THEN...*)

val smerge_set = maybe_thm ("smerge_set",
``!cmp:'a toto l m. (set (smerge cmp l m) = set l UNION set m)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [smerge, smerge_nil] THEN
Induct_on `m` THEN
RW_TAC (srw_ss ()) [smerge, smerge_nil] THEN
Cases_on `apto cmp h h'` THENL
[ALL_TAC, `h = h'` by IMP_RES_TAC toto_equal_eq, ALL_TAC] THEN
RW_TAC (srw_ss ()) [toto_equal_eq] THEN
RW_TAC bool_ss [toto_equal_eq, EXTENSION, IN_INSERT, IN_UNION, DISJ_ASSOC] THEN
tautLib.TAUT_TAC);

val smerge_OL = store_thm ("smerge_OL",
``!cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (smerge cmp l m)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [smerge, OL, smerge_nil] THEN
Induct_on `m` THEN
RW_TAC (srw_ss ()) [smerge, OL, smerge_nil] THEN
Cases_on `apto cmp h h'` THEN RW_TAC (srw_ss ()) [OL] THENL
[`MEM p l \/ MEM p (h' :: m)`
 by (RW_TAC bool_ss [GSYM IN_LIST_TO_SET, GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set, IN_LIST_TO_SET]) THENL
 [RES_TAC
 ,`(p = h') \/ MEM p m` by ASM_REWRITE_TAC [GSYM MEM] THENL
  [AR, RES_TAC THEN IMP_RES_TAC totoLLtrans
 ]]
,`MEM p l \/ MEM p m`
 by (RW_TAC bool_ss [GSYM IN_LIST_TO_SET, GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set, IN_LIST_TO_SET]) THENL
 [RES_TAC
 ,RES_TAC THEN IMP_RES_TAC totoELtrans
 ]
,`MEM p (h :: l) \/ MEM p m`
 by (RW_TAC bool_ss [GSYM IN_LIST_TO_SET, GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set, IN_LIST_TO_SET]) THENL
 [`(p = h) \/ MEM p l` by ASM_REWRITE_TAC [GSYM MEM] THENL
  [ASM_REWRITE_TAC [GSYM toto_antisym],
   RES_TAC THEN IMP_RES_TAC totoGLtrans
  ]
  ,RES_TAC
]]);

val OL_sublists = Define
`(OL_sublists cmp ([]:'a list option list) = T) /\
 (OL_sublists cmp (NONE :: lol) = OL_sublists cmp lol) /\
 (OL_sublists cmp (SOME m :: lol) = OL cmp m /\ OL_sublists cmp lol)`;

val OL_sublists_ind = theorem "OL_sublists_ind";

(* OL_sublists_ind = |- !P. (!cmp. P cmp []) /\
          (!cmp lol. P cmp lol ==> P cmp (NONE::lol)) /\
          (!cmp m lol. P cmp lol ==> P cmp (SOME m::lol)) ==> !v v1. P v v1 *)

val lol_set = Define
`(lol_set ([]:'a list option list) = {}) /\
 (lol_set (NONE :: lol) = lol_set lol) /\
 (lol_set (SOME m :: lol) = set m UNION lol_set lol)`;

val incr_smerge = Define
`(incr_smerge cmp (l:'a list) [] = [SOME l]) /\
 (incr_smerge cmp l (NONE :: lol) = SOME l :: lol) /\
 (incr_smerge cmp l (SOME m :: lol) =
   NONE :: incr_smerge cmp (smerge cmp l m) lol)`;

val incr_smerge_set = maybe_thm ("incr_smerge_set", ``!cmp lol l:'a list.
               lol_set (incr_smerge cmp l lol) = set l UNION lol_set lol``,
HO_MATCH_MP_TAC OL_sublists_ind THEN
RW_TAC bool_ss [incr_smerge, smerge_set, lol_set, UNION_ASSOC]);

val incr_smerge_OL = store_thm ("incr_smerge_OL", ``!cmp lol l:'a list.
OL_sublists cmp lol /\ OL cmp l ==> OL_sublists cmp (incr_smerge cmp l lol)``,
HO_MATCH_MP_TAC OL_sublists_ind THEN
RW_TAC bool_ss [incr_smerge, smerge_OL, OL_sublists]);

val smerge_out = Define
`(smerge_out (cmp:'a toto) l ([]:'a list option list) = l) /\
 (smerge_out cmp l (NONE :: lol) = smerge_out cmp l lol) /\
 (smerge_out cmp l (SOME m :: lol) = smerge_out cmp (smerge cmp l m) lol)`;

val smerge_out_ind = theorem "smerge_out_ind";

(* smerge_out_ind = |- !P. (!cmp l. P cmp l []) /\
     (!cmp l lol. P cmp l lol ==> P cmp l (NONE::lol)) /\
     (!cmp l m lol. P cmp (smerge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
     !v v1 v2. P v v1 v2 *)

val smerge_out_set = maybe_thm ("smerge_out_set", ``!cmp:'a toto l:'a list lol.
         set (smerge_out cmp l lol) = set l UNION lol_set lol``,
HO_MATCH_MP_TAC smerge_out_ind THEN
RW_TAC bool_ss [smerge_out, lol_set, smerge_set, UNION_EMPTY, UNION_ASSOC]);

val smerge_out_OL = maybe_thm ("smerge_out_OL", ``!cmp:'a toto l:'a list lol.
OL cmp l /\ OL_sublists cmp lol ==> OL cmp (smerge_out cmp l lol)``,
HO_MATCH_MP_TAC smerge_out_ind THEN
RW_TAC bool_ss [smerge_out, OL_sublists] THEN
METIS_TAC [smerge_OL]);

val incr_sbuild = Define
`(incr_sbuild (cmp:'a toto) [] = []) /\
 (incr_sbuild cmp (x :: l) = incr_smerge cmp [x] (incr_sbuild cmp l))`;

val incr_sbuild_set = maybe_thm ("incr_sbuild_set",
``!cmp l:'a list. lol_set (incr_sbuild cmp l) = set l``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [lol_set, incr_sbuild, incr_smerge_set, INSERT_UNION_EQ]);

val  OL_EMPTY = maybe_thm ("OL_EMPTY",
``!cmp:'a toto. OL cmp []``,
REWRITE_TAC [OL]);

val OL_SING = maybe_thm ("OL_SING",
``!cmp:'a toto x. OL cmp [x]``,
RW_TAC bool_ss [OL, MEM]);

val incr_sbuild_OL = maybe_thm ("incr_sbuild_OL",
``!cmp l:'a list. OL_sublists cmp (incr_sbuild cmp l)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [incr_sbuild, incr_smerge_OL, OL_sublists] THEN
METIS_TAC [OL_SING, incr_smerge_OL]);

val incr_ssort = Define
`incr_ssort (cmp:'a toto) l = smerge_out cmp [] (incr_sbuild cmp l)`;

val incr_ssort_set = maybe_thm ("incr_ssort_set",
``!cmp:'a toto l. set (incr_ssort cmp l) = set l``,
RW_TAC (srw_ss ()) [incr_ssort, smerge_out_set, incr_sbuild_set]);

val incr_ssort_OL = maybe_thm ("incr_ssort_OL",
``!cmp:'a toto l. OL cmp (incr_ssort cmp l)``,
REWRITE_TAC [incr_ssort] THEN
METIS_TAC [incr_sbuild_OL, OL, smerge_out_OL]);

val OL_MEM_EQ = maybe_thm ("OL_MEM_EQ",
``!cmp:'a toto l m. OL cmp l /\ OL cmp m ==>
   ((!x. MEM x l = MEM x m) <=> (l = m))``,
GEN_TAC THEN Induct THENL
[Induct THENL
 [REWRITE_TAC []
 ,REPEAT STRIP_TAC THEN EQ_TAC THENL
  [CONV_TAC LEFT_IMP_FORALL_CONV THEN Q.EXISTS_TAC `h` THEN
   REWRITE_TAC [MEM]
  ,REWRITE_TAC [GSYM NOT_CONS_NIL]
 ]]
,GEN_TAC THEN Induct THENL
 [STRIP_TAC THEN EQ_TAC THENL
  [CONV_TAC LEFT_IMP_FORALL_CONV THEN Q.EXISTS_TAC `h` THEN
   REWRITE_TAC [MEM]
  ,REWRITE_TAC [NOT_CONS_NIL]
  ]
 ,GEN_TAC THEN REWRITE_TAC [OL, MEM, CONS_11] THEN STRIP_TAC THEN
  `(!x. MEM x l <=> MEM x m) <=> (l = m)` by RES_TAC THEN
  EQ_TAC THENL [ALL_TAC, RW_TAC bool_ss []] THEN
  `~MEM h l /\ ~MEM h' m` by METIS_TAC [CONJUNCT1 toto_glneq] THEN
  CONV_TAC LEFT_IMP_FORALL_CONV THEN Cases_on `apto cmp h h'` THENL
  [Q.EXISTS_TAC `h` THEN AR THEN METIS_TAC [totoLLtrans, CONJUNCT1 toto_glneq]
  ,CONV_TAC EXISTS_IMP_CONV THEN DISCH_TAC THEN
   `h = h'` by IMP_RES_TAC toto_equal_eq THEN
   `!x. MEM x l <=> MEM x m` by METIS_TAC[] THEN
   AR THEN RES_TAC
  ,Q.EXISTS_TAC `h'` THEN AR THEN IMP_RES_TAC toto_antisym THEN
   METIS_TAC [totoLLtrans, CONJUNCT1 toto_glneq]
]]]);

(* *********** end of digression to program sorting ************** *)

(* Define the set represented (according to a total order) by a bt *)

(* Following should really be called "bt_to_set", but ENUMERAL, like
   NUMERAL, will flag the terms that represent sets as trees. *)

val bt_to_set = xDefine "bt_to_set"
`(ENUMERAL cmp nt = {}) /\
 (ENUMERAL (cmp:'a toto) (node l x r) =
{y | y IN ENUMERAL cmp l /\ (apto cmp y x = LESS)} UNION {x} UNION
{z | z IN ENUMERAL cmp r /\ (apto cmp x z = LESS)})`;

val bt_to_set_lb = Define`bt_to_set_lb cmp (lb:'a) t =
                     {x | x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS)}`;

val bt_to_set_ub = Define`bt_to_set_ub cmp t (ub:'a) =
                     {x | x IN ENUMERAL cmp t /\ (apto cmp x ub = LESS)}`;

val bt_to_set_mut_rec = maybe_thm ("bt_to_set_mut_rec",
``!cmp:'a toto l x r. ENUMERAL cmp (node l x r) =
        bt_to_set_ub cmp l x UNION {x} UNION bt_to_set_lb cmp x r``,
REWRITE_TAC [bt_to_set_lb, bt_to_set_ub] THEN REWRITE_TAC [bt_to_set]);

val bt_to_set_lb_ub = Define`bt_to_set_lb_ub cmp lb t (ub:'a) =
{x | x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}`;

val IN_bt_to_set = store_thm ("IN_bt_to_set",
``(!cmp:'a toto y. y IN ENUMERAL cmp nt = F) /\
  (!cmp:'a toto l x r y. y IN ENUMERAL cmp (node l x r) =
   y IN ENUMERAL cmp l /\ (apto cmp y x = LESS) \/ (y = x) \/
   y IN ENUMERAL cmp r /\ (apto cmp x y = LESS))``,
RW_TAC (srw_ss ()) [bt_to_set] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
tautLib.TAUT_TAC);

(* Following look-up function (disguised as two theorems) to make bt's
   imitate IN on finite sets, may or may not be the reasonable way to go. *)

val NOT_IN_nt = save_thm ("NOT_IN_nt", CONJUNCT1 IN_bt_to_set);

(* NOT_IN_nt = |- !cmp y. y IN ENUMERAL cmp nt <=> F *)

val IN_node = store_thm ("IN_node",
``!cmp x:'a l y r. x IN ENUMERAL cmp (node l y r) <=> case apto cmp x y of
 LESS => x IN ENUMERAL cmp l | EQUAL => T | GREATER => x IN ENUMERAL cmp r``,
RW_TAC (srw_ss ()) [bt_to_set] THEN Cases_on `apto cmp x y` THEN
(Q.SUBGOAL_THEN `(x = y) = (apto cmp x y = EQUAL)` SUBST1_TAC
           THEN1 MATCH_ACCEPT_TAC (GSYM toto_equal_eq)) THEN
IMP_RES_TAC toto_antisym THEN RW_TAC (srw_ss ()) []);

(* Following "mut_rec" theorems seem relevant to conversion to ol's, not to
   evaluating IN. *)

val bt_to_set_lb_ub_mut_rec = maybe_thm ("bt_to_set_lb_ub_mut_rec",
``!cmp:'a toto lb l x r ub. bt_to_set_lb_ub cmp lb (node l x r) ub =
     if apto cmp lb x = LESS then
       if apto cmp x ub = LESS then
         bt_to_set_lb_ub cmp lb l x UNION {x} UNION  bt_to_set_lb_ub cmp x r ub
       else
         bt_to_set_lb_ub cmp lb l ub
     else
       bt_to_set_lb_ub cmp lb r ub``,
RW_TAC (srw_ss ()) [bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp x' ub = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN RW_TAC (srw_ss ()) []
,Q.UNDISCH_TAC `apto cmp lb x' = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN RW_TAC (srw_ss ()) []
]);

val bt_to_set_lb_mut_rec = maybe_thm ("bt_to_set_lb_mut_rec",
``!cmp:'a toto lb l x r. bt_to_set_lb cmp lb (node l x r) =
     if apto cmp lb x = LESS then
         bt_to_set_lb_ub cmp lb l x UNION {x} UNION  bt_to_set_lb cmp x r
     else
       bt_to_set_lb cmp lb r``,
RW_TAC (srw_ss ()) [bt_to_set_lb, bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp lb x' = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN RW_TAC (srw_ss ()) []
]);

val bt_to_set_ub_mut_rec = maybe_thm ("bt_to_set_ub_mut_rec",
``!cmp:'a toto ub l x r. bt_to_set_ub cmp (node l x r) ub =
     if apto cmp x ub = LESS then
         bt_to_set_ub cmp l x UNION {x} UNION  bt_to_set_lb_ub cmp x r ub
     else
       bt_to_set_ub cmp l ub``,
RW_TAC (srw_ss ()) [bt_to_set_ub, bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp x' ub = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN RW_TAC (srw_ss ()) []
]);

(* ****************************************************************** *)
(* For computational purposes, we need to go from ENUMERAL-terms to   *)
(* ordered lists of the same elements. Possiibly to no purpose, we    *)
(* supply first a general translation that extracts from any bt at all*)
(* the list of the same elements as are in bt_to_set of it. Later, we *)
(* will see that checking for no out-of-order elements separately     *)
(* allows a faster translation by bt_to_list, with about half the     *)
(* comparisons of the general method. (See better_bt_to_ol below.)    *)
(* ****************************************************************** *)

val bt_to_ol_lb_ub = Define
`(bt_to_ol_lb_ub (cmp:'a toto) lb nt ub = []) /\
 (bt_to_ol_lb_ub cmp lb (node l x r) ub =
   if apto cmp lb x = LESS then
      if apto cmp x ub = LESS then
            bt_to_ol_lb_ub cmp lb l x ++ [x] ++ bt_to_ol_lb_ub cmp x r ub
      else bt_to_ol_lb_ub cmp lb l ub
   else bt_to_ol_lb_ub cmp lb r ub)`;

val bt_to_ol_lb = Define
`(bt_to_ol_lb (cmp:'a toto) lb nt = []) /\
 (bt_to_ol_lb cmp lb (node l x r) =
   if apto cmp lb x = LESS then
            bt_to_ol_lb_ub cmp lb l x ++ [x] ++ bt_to_ol_lb cmp x r
   else bt_to_ol_lb cmp lb r)`;

val bt_to_ol_ub = Define
`(bt_to_ol_ub (cmp:'a toto) nt ub = []) /\
 (bt_to_ol_ub cmp (node l x r) ub =
   if apto cmp x ub = LESS then
            bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb_ub cmp x r ub
   else bt_to_ol_ub cmp l ub)`;

val bt_to_ol = Define
`(bt_to_ol (cmp:'a toto) nt = []) /\
 (bt_to_ol cmp (node l x r) =
   bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb cmp x r)`;

(* Show ordered lists have the correct sets of elements: *)

val ol_set_lb_ub = maybe_thm ("ol_set_lb_ub",``!cmp:'a toto t lb ub.
   bt_to_set_lb_ub cmp lb t ub = set (bt_to_ol_lb_ub cmp lb t ub)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bt_to_set_lb_ub_mut_rec, bt_to_ol_lb_ub,
                    LIST_TO_SET_APPEND, EXTENSION] THEN
RW_TAC (srw_ss ()) [NOT_IN_nt, bt_to_set_lb_ub]);

val ol_set_lb =  maybe_thm ("ol_set_lb",``!cmp:'a toto t lb.
   bt_to_set_lb cmp lb t = set (bt_to_ol_lb cmp lb t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bt_to_set_lb_mut_rec, bt_to_ol_lb,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb_ub] THEN
RW_TAC (srw_ss ()) [NOT_IN_nt, bt_to_set_lb]);

val ol_set_ub = maybe_thm ("ol_set_ub",``!cmp:'a toto t ub.
   bt_to_set_ub cmp t ub = set (bt_to_ol_ub cmp t ub)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bt_to_set_ub_mut_rec, bt_to_ol_ub,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb_ub] THEN
RW_TAC (srw_ss ()) [NOT_IN_nt, bt_to_set_ub]);

val ol_set = store_thm ("ol_set",
``!cmp:'a toto t. ENUMERAL cmp t = set (bt_to_ol cmp t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bt_to_set_mut_rec, bt_to_ol,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb, ol_set_ub] THEN
REWRITE_TAC [NOT_IN_nt]);

(* We have neglected so far to prove that bt_to_ol and its kin produce
   lists satisfying OL cmp. *)

val list_split_lem = maybe_thm ("list_split_lem",
``!cmp:'a toto l x r. OL cmp (l ++ [x] ++ r) <=>
   OL cmp l /\ (!a. a IN set l ==> (apto cmp a x = LESS)) /\
   OL cmp r /\ (!z. z IN set r ==> (apto cmp x z = LESS))``,
GEN_TAC THEN Induct THEN RW_TAC (srw_ss ()) [OL] THEN EQ_TAC THEN
RW_TAC (srw_ss ()) [] THENL
[POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []
,RES_TAC
,RES_TAC
,Q.UNDISCH_THEN `!a. (a = h) \/ MEM a l ==> (apto cmp a p = LESS)`
                MATCH_MP_TAC THEN REWRITE_TAC []
,MATCH_MP_TAC totoLLtrans THEN Q.EXISTS_TAC `x` THEN CONJ_TAC THENL
 [Q.UNDISCH_THEN `!a. (a = h) \/ MEM a l ==> (apto cmp a x = LESS)`
                MATCH_MP_TAC THEN REWRITE_TAC []
 ,RES_TAC
]]);

val MEM_lb_ub_lem = maybe_thm ("MEM_lb_ub_lem",
``!cmp:'a toto lb t ub a. MEM a (bt_to_ol_lb_ub cmp lb t ub) ==>
    (apto cmp lb a = LESS) /\ (apto cmp a ub = LESS)``,
REWRITE_TAC [GSYM IN_LIST_TO_SET, GSYM ol_set_lb_ub] THEN
RW_TAC (srw_ss ()) [bt_to_set_lb_ub]);

val OL_bt_to_ol_lb_ub = store_thm ("OL_bt_to_ol_lb_ub",
``!cmp:'a toto t lb ub. OL cmp (bt_to_ol_lb_ub cmp lb t ub)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bt_to_ol_lb_ub, ol_set_lb_ub, list_split_lem] THEN
IMP_RES_TAC MEM_lb_ub_lem THEN REWRITE_TAC [OL]);

val MEM_lb_lem = maybe_thm ("MEM_lb_lem",
``!cmp:'a toto lb t a. MEM a (bt_to_ol_lb cmp lb t) ==>(apto cmp lb a = LESS)``,
REWRITE_TAC [GSYM IN_LIST_TO_SET, GSYM ol_set_lb] THEN
RW_TAC (srw_ss ()) [bt_to_set_lb]);

val OL_bt_to_ol_lb = store_thm ("OL_bt_to_ol_lb",
``!cmp:'a toto t lb. OL cmp (bt_to_ol_lb cmp lb t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())
 [bt_to_ol_lb, ol_set_lb, list_split_lem, OL_bt_to_ol_lb_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_lb_ub_lem
,IMP_RES_TAC MEM_lb_lem
]);

val MEM_ub_lem = maybe_thm ("MEM_ub_lem",
``!cmp:'a toto t ub a. MEM a (bt_to_ol_ub cmp t ub) ==>(apto cmp a ub = LESS)``,
REWRITE_TAC [GSYM ol_set_ub] THEN
RW_TAC (srw_ss ()) [bt_to_set_ub]);

val OL_bt_to_ol_ub = store_thm ("OL_bt_to_ol_ub",
``!cmp:'a toto t ub. OL cmp (bt_to_ol_ub cmp t ub)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())
 [bt_to_ol_ub, ol_set_ub, list_split_lem, OL_bt_to_ol_lb_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_ub_lem
,IMP_RES_TAC MEM_lb_ub_lem
]);

val OL_bt_to_ol = store_thm ("OL_bt_to_ol",
``!cmp:'a toto t. OL cmp (bt_to_ol cmp t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())
 [bt_to_ol, GSYM ol_set, list_split_lem, OL_bt_to_ol_lb, OL_bt_to_ol_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_ub_lem
,IMP_RES_TAC MEM_lb_lem
]);

(* ******* Now to suppress the APPENDing ******** *)

val bt_to_ol_lb_ub_ac = Define
`(bt_to_ol_lb_ub_ac (cmp:'a toto) lb nt ub m = m) /\
 (bt_to_ol_lb_ub_ac cmp lb (node l x r) ub m =
 if apto cmp lb x = LESS then
    if apto cmp x ub = LESS then
      bt_to_ol_lb_ub_ac cmp lb l x (x :: bt_to_ol_lb_ub_ac cmp x r ub m)
    else bt_to_ol_lb_ub_ac cmp lb l ub m
 else bt_to_ol_lb_ub_ac cmp lb r ub m)`;

val ol_lb_ub_ac_thm = maybe_thm ("ol_lb_ub_ac_thm",
``!cmp:'a toto t lb ub m. bt_to_ol_lb_ub_ac cmp lb t ub m =
                          bt_to_ol_lb_ub cmp lb t ub ++ m``,
GEN_TAC THEN Induct THEN RW_TAC (srw_ss ())[bt_to_ol_lb_ub, bt_to_ol_lb_ub_ac]);

val bt_to_ol_lb_ac = Define
`(bt_to_ol_lb_ac (cmp:'a toto) lb nt m = m) /\
 (bt_to_ol_lb_ac cmp lb (node l x r) m =
 if apto cmp lb x = LESS then
      bt_to_ol_lb_ub_ac cmp lb l x (x :: bt_to_ol_lb_ac cmp x r m)
 else bt_to_ol_lb_ac cmp lb r m)`;

val ol_lb_ac_thm = maybe_thm ("ol_lb_ac_thm",
``!cmp:'a toto t lb m. bt_to_ol_lb_ac cmp lb t m = bt_to_ol_lb cmp lb t ++ m``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())[bt_to_ol_lb, bt_to_ol_lb_ac, ol_lb_ub_ac_thm]);

val bt_to_ol_ub_ac = Define
`(bt_to_ol_ub_ac (cmp:'a toto) nt ub m = m) /\
 (bt_to_ol_ub_ac cmp (node l x r) ub m =
    if apto cmp x ub = LESS then
      bt_to_ol_ub_ac cmp l x (x :: bt_to_ol_lb_ub_ac cmp x r ub m)
    else bt_to_ol_ub_ac cmp l ub m)`;

val ol_ub_ac_thm = maybe_thm ("ol_ub_ac_thm",
``!cmp:'a toto t ub m. bt_to_ol_ub_ac cmp t ub m = bt_to_ol_ub cmp t ub ++ m``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())[bt_to_ol_ub, bt_to_ol_ub_ac, ol_lb_ub_ac_thm]);

val bt_to_ol_ac = Define
`(bt_to_ol_ac (cmp:'a toto) nt m = m) /\
 (bt_to_ol_ac cmp (node l x r) m =
      bt_to_ol_ub_ac cmp l x (x :: bt_to_ol_lb_ac cmp x r m))`;

val ol_ac_thm = maybe_thm ("ol_ac_thm",
``!cmp:'a toto t m. bt_to_ol_ac cmp t m = bt_to_ol cmp t ++ m``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ())[bt_to_ol, bt_to_ol_ac, ol_lb_ac_thm, ol_ub_ac_thm]);

(* ********* "OWL" for [set] Ordered With List *********** *)

val OWL = Define`OWL (cmp:'a toto) (s:'a set) (l:'a list) =
(s = set l) /\ OL cmp l`;

val OWL_unique = maybe_thm ("OWL_unique",
``!cmp:'a toto s l m. OWL cmp s l /\ OWL cmp s m ==> (l = m)``,
RW_TAC bool_ss [OWL] THEN METIS_TAC [OL_MEM_EQ]);

(* We want to compute bt_to_ol  with as few comparisons as may be. The
   definitions have used APPEND. *)

val bt_FINITE = maybe_thm ("bt_FINITE",
``!cmp:'a toto t:'a bt. FINITE (ENUMERAL cmp t)``,
REWRITE_TAC [ol_set, FINITE_LIST_TO_SET]);

val OWL_bt_to_ol = store_thm ("OWL_bt_to_ol",
``!cmp:'a toto t. OWL cmp (ENUMERAL cmp t) (bt_to_ol cmp t)``,
RW_TAC bool_ss [OWL, ol_set, OL_bt_to_ol]);

(* We already have the two pieces of OWL:

  OL_bt_to_ol = |- !t cmp. OL cmp (bt_to_ol cmp t)
  ol_set = |- !cmp t. ENUMERAL cmp t = set (bt_to_ol cmp t) *)

(* ************* Stuff about ZSL, OSL, and OU (some interesting proofs)
   appeared not of any use, exiled to OU.stuff ********************* *)

(* Prove that bt_to_ol inverts list_to_bt for ordered lists, using OL_MEM_EQ *)

val OL_set_EQ = maybe_thm ("OL_set_EQ",
``!cmp:'a toto l m. OL cmp l /\ OL cmp m ==> ((set l = set m) <=> (l = m))``,
REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP OL_MEM_EQ) THEN
REWRITE_TAC [IN_LIST_TO_SET, EXTENSION]);

(* "OU" for "Ordered Union" - used for intermediate (tree, binary list) pair
   in converting betw. binary lists and rightist trees. *)

val OU = Define`OU (cmp:'a toto) (t:'a set) (u:'a set) =
         {x | x IN t /\ (!z. z IN u ==> (apto cmp x z = LESS))} UNION u`;

val UO = Define`UO (cmp:'a toto) (s:'a set) (t:'a set) =
         s UNION {y | y IN t /\ (!z. z IN s ==> (apto cmp z y = LESS))}`;

val EMPTY_OU = store_thm ("EMPTY_OU",
``!cmp:'a toto sl:'a set. OU cmp {} sl = sl``,
REWRITE_TAC [OU, NOT_IN_EMPTY, UNION_EMPTY, GSPEC_F]);

val OU_EMPTY = store_thm ("OU_EMPTY",
``!cmp:'a toto t:'a set. OU cmp t {} = t``,
REWRITE_TAC [OU, NOT_IN_EMPTY, UNION_EMPTY, GSPEC_ID]);

val sing_UO = maybe_thm ("sing_UO",``!cmp:'a toto x:'a t:'a set.
        {x} UNION {y | y IN t /\ (apto cmp x y = LESS)} = UO cmp {x} t``,
RW_TAC bool_ss [UO, IN_SING]);

val LESS_UO_LEM = store_thm ("LESS_UO_LEM",
``!cmp:'a toto x:'a y:'a s:'a set.
  (!z. z IN UO cmp {x} s ==> (apto cmp y z = LESS)) <=> (apto cmp y x = LESS)``,
RW_TAC bool_ss [GSYM sing_UO] THEN EQ_TAC THEN
REWRITE_TAC [IN_UNION, IN_SING] THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THENL
[CONV_TAC LEFT_IMP_FORALL_CONV THEN
 Q.EXISTS_TAC `x` THEN RW_TAC bool_ss []
,REPEAT STRIP_TAC THENL [AR, IMP_RES_TAC toto_trans_less]
]);

val bt_to_set_OU_UO = maybe_thm ("bt_to_set_OU_UO",
``!cmp:'a toto l:'a bt x:'a r:'a bt. ENUMERAL cmp (node l x r) =
 OU cmp (ENUMERAL cmp l) (UO cmp {x} (ENUMERAL cmp r))``,
RW_TAC bool_ss [OU, bt_to_set, LESS_UO_LEM] THEN
REWRITE_TAC [GSYM UNION_ASSOC] THEN ONCE_REWRITE_TAC [sing_UO] THEN REFL_TAC);

val OU_UO_OU_LEM = maybe_thm ("OU_UO_OU_lem",
``!cmp:'a toto l x r. OU cmp l (UO cmp {x} r) = UO cmp (OU cmp l {x}) r``,
RW_TAC (srw_ss ()) [OU, UO, EXTENSION, IN_UNION] THEN
EQ_TAC THEN REPEAT STRIP_TAC THEN AR THEN
METIS_TAC [totoLLtrans]);

val LESS_ALL = Define`LESS_ALL (cmp:'a toto) (x:'a) (s:'a set) =
                      !y. y IN s ==> (apto cmp x y = LESS)`;

val IN_OU = maybe_thm ("IN_OU",
``!cmp:'a toto x:'a u:'a set v:'a set.
  x IN OU cmp u v <=> (if LESS_ALL cmp x v then x IN u else x IN v)``,
RW_TAC bool_ss [OU, LESS_ALL, IN_UNION] THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN AR THEN
Q.SUBGOAL_THEN `x NOTIN v` (REWRITE_TAC o ulist) THEN
DISCH_TAC THEN RES_THEN MP_TAC THEN REWRITE_TAC [toto_refl, all_cpn_distinct]);

val OU_SUBSET_UNION = maybe_thm ("OU_SUBSET_UNION",
``!cmp:'a toto u:'a set v:'a set. OU cmp u v SUBSET u UNION v``,
REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET_DEF, IN_OU, IN_UNION] THEN
METIS_TAC []);

val LESS_ALL_UNION = maybe_thm ("LESS_ALL_UNION",
``!cmp:'a toto x:'a u:'a set v:'a set.
   LESS_ALL cmp x (u UNION v) = LESS_ALL cmp x u /\ LESS_ALL cmp x v``,
RW_TAC bool_ss [LESS_ALL, IN_UNION] THEN METIS_TAC []);

val NOT_IN_OU_LEM = maybe_thm ("NOT_IN_OU_LEM",
``!cmp:'a toto x:'a u:'a set v:'a set.
 x IN u UNION v ==> x NOTIN OU cmp u v ==> ?y. y IN v /\ apto cmp x y <> LESS``,
RW_TAC bool_ss [IN_UNION, IN_OU, LESS_ALL] THENL
[RES_THEN MP_TAC THEN REWRITE_TAC [toto_refl, all_cpn_distinct]
,METIS_TAC []]);

val cpn_NOT_LESS = maybe_thm ("cpn_NOT_LESS",
``!c:cpn. c <> LESS ==> (c = GREATER) \/ (c = EQUAL)``,
METIS_TAC [cpn_nchotomy]);

val LESS_ALL_OU = store_thm ("LESS_ALL_OU",
``!cmp:'a toto x:'a u:'a set v:'a set.
   LESS_ALL cmp x (OU cmp u v) = LESS_ALL cmp x u /\ LESS_ALL cmp x v``,
RW_TAC bool_ss [GSYM LESS_ALL_UNION] THEN REWRITE_TAC [LESS_ALL] THEN
EQ_TAC THENL
[REPEAT STRIP_TAC THEN Cases_on `y IN OU cmp u v` THENL
 [RES_TAC
 ,IMP_RES_TAC NOT_IN_OU_LEM THEN
  Q.SUBGOAL_THEN `y' IN OU cmp u v` ASSUME_TAC
  THEN1 ASM_REWRITE_TAC [OU, IN_UNION] THEN
  RES_TAC THEN IMP_RES_TAC cpn_NOT_LESS THENL
  [IMP_RES_TAC toto_trans_less
  ,IMP_RES_TAC toto_equal_sym THEN IMP_RES_TAC toto_trans_less
  ]
 ]
,METIS_TAC [OU_SUBSET_UNION, SUBSET_DEF]
]);

val OU_ASSOC = store_thm ("OU_ASSOC",
``!cmp a b c:'a set. OU cmp a (OU cmp b c) = OU cmp (OU cmp a b) c``,
RW_TAC bool_ss [IN_OU, EXTENSION, IN_UNION] THEN
REWRITE_TAC [LESS_ALL_OU] THEN METIS_TAC []);

val bl_to_set = Define
`(bl_to_set (cmp:'a toto) (nbl:'a bl) = {}) /\
 (bl_to_set cmp (zerbl b) = bl_to_set cmp b) /\
 (bl_to_set cmp (onebl x t b) =
  OU cmp ({x} UNION {y | y IN ENUMERAL cmp t /\ (apto cmp x y = LESS)})
         (bl_to_set cmp  b))`;

val bl_to_set_OU_UO = maybe_thm ("bl_to_set_OU_UO",
``!cmp:'a toto x t b. bl_to_set cmp (onebl x t b) =
                      OU cmp (UO cmp {x} (ENUMERAL cmp t)) (bl_to_set cmp b)``,
REWRITE_TAC [bl_to_set, sing_UO]);

val bl_rev_set_lem = maybe_thm ("bl_rev_set_lem",``!cmp:'a toto b t.
 ENUMERAL cmp (bl_rev t b) = OU cmp (ENUMERAL cmp t) (bl_to_set cmp b)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bl_rev, bl_to_set_OU_UO] THEN
REWRITE_TAC [bl_to_set, OU_EMPTY] THEN
REWRITE_TAC [bt_to_set_OU_UO, OU_ASSOC]);

(* Converting a bl to a bt preserves the represented set: *)

val bl_to_bt_set = maybe_thm ("bl_to_bt_set",
``!cmp:'a toto b. ENUMERAL cmp (bl_to_bt b) = bl_to_set cmp b``,
REWRITE_TAC [bl_to_bt, bl_rev_set_lem, bt_to_set, EMPTY_OU]);

(* Now to show that building a bl from a list does the same. *)

(* We aim to show that LESS_ALL cmp a (bl_to_set cmp b) ==>
                (bl_to_set cmp (BL_CONS a bl) = a INSERT bl_to_set cmp b). *)

(* Generalizing for the recursion in BL_ACCUM, we hope to show that
  LESS_ALL cmp a (ENUMERAL cmp t) /\ LESS_ALL cmp a (bl_to_set b) ==>
  (bl_to_set cmp (BL_ACCUM a t b) =
      a INSERT (OU cmp (ENUMERAL cmp t) (bl_to_set cmp b))) . *)

val LESS_ALL_UO_LEM = store_thm ("LESS_ALL_UO_LEM",
``!cmp:'a toto a s. LESS_ALL cmp a s ==> (UO cmp {a} s = a INSERT s)``,
RW_TAC (srw_ss ()) [LESS_ALL, UO, EXTENSION, IN_UNION] THEN METIS_TAC []);

val LESS_ALL_OU_UO_LEM = store_thm ("LESS_ALL_OU_UO_LEM",
``!cmp:'a toto a s t. LESS_ALL cmp a s /\ LESS_ALL cmp a t ==>
                      (OU cmp (UO cmp {a} s) t = a INSERT (OU cmp s t))``,
REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC LESS_ALL_UO_LEM THEN
RW_TAC (srw_ss ()) [UO, OU, EXTENSION, IN_UNION] THEN
METIS_TAC [LESS_ALL]);

val BL_ACCUM_set = maybe_thm ("BL_ACCUM_set",
``!cmp:'a toto a b t.
 LESS_ALL cmp a (ENUMERAL cmp t) /\ LESS_ALL cmp a (bl_to_set cmp b) ==>
    (bl_to_set cmp (BL_ACCUM a t b) =
      a INSERT (OU cmp (ENUMERAL cmp t) (bl_to_set cmp b)))``,
GEN_TAC THEN GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [BL_ACCUM, bl_to_set_OU_UO, bt_to_set_OU_UO] THENL
[METIS_TAC [LESS_ALL_UO_LEM, LESS_ALL_OU_UO_LEM, bl_to_set]
,METIS_TAC [LESS_ALL_UO_LEM, LESS_ALL_OU_UO_LEM, bl_to_set]
,REWRITE_TAC [bl_to_set] THEN
`LESS_ALL cmp a (UO cmp {a'} (ENUMERAL cmp b0)) /\
 LESS_ALL cmp a (bl_to_set cmp b)` by ASM_REWRITE_TAC [GSYM LESS_ALL_OU] THEN
`LESS_ALL cmp a (ENUMERAL cmp (node t a' b0))`
 by ASM_REWRITE_TAC [bt_to_set_OU_UO, LESS_ALL_OU] THEN
 RES_TAC THEN ASM_REWRITE_TAC [bt_to_set_OU_UO, OU_ASSOC]
]);

val BL_CONS_set = maybe_thm ("BL_CONS_set",
``!cmp:'a toto a b. LESS_ALL cmp a (bl_to_set cmp b) ==>
        (bl_to_set cmp (BL_CONS a b) = a INSERT bl_to_set cmp b)``,
REPEAT STRIP_TAC THEN REWRITE_TAC [BL_CONS] THEN
Q.SUBGOAL_THEN `OU cmp (ENUMERAL cmp nt) (bl_to_set cmp b) = bl_to_set cmp b`
(SUBST1_TAC o SYM)
THEN1 REWRITE_TAC [bt_to_set, EMPTY_OU] THEN
`LESS_ALL cmp a (ENUMERAL cmp nt)`
 by REWRITE_TAC [LESS_ALL, NOT_IN_EMPTY, bt_to_set] THEN
IMP_RES_TAC BL_ACCUM_set);

val list_to_bl_set = maybe_thm ("list_to_bl_set",
``!cmp:'a toto l. OL cmp l ==> (bl_to_set cmp (list_to_bl l) = set l)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [bl_to_set, list_to_bl, LIST_TO_SET_THM, OL] THEN
RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC BL_CONS_set THEN
RES_THEN SUBST1_TAC THEN RW_TAC bool_ss [IN_LIST_TO_SET, LESS_ALL]);

val bt_to_ol_ID = maybe_thm ("bt_to_ol_ID",
``!cmp:'a toto. !l::OL cmp. bt_to_ol cmp (list_to_bt l) = l``,
GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN
REWRITE_TAC [SPECIFICATION] THEN GEN_TAC THEN DISCH_TAC THEN
Q.SUBGOAL_THEN `OL cmp (bt_to_ol cmp (list_to_bt l)) /\ OL cmp l`
(REWRITE_TAC o ulist o GSYM o MATCH_MP OL_set_EQ)
THEN1 ASM_REWRITE_TAC [OL_bt_to_ol] THEN
IMP_RES_THEN (SUBST1_TAC o SYM) list_to_bl_set THEN
REWRITE_TAC [GSYM bl_to_bt_set, list_to_bt, ol_set]);

val bt_to_ol_ID_IMP = save_thm ("bt_to_ol_ID_IMP", REWRITE_RULE [SPECIFICATION]
                     (CONV_RULE (ONCE_DEPTH_CONV RES_FORALL_CONV) bt_to_ol_ID));

(* bt_to_ol_ID_IMP: |- !cmp l. OL cmp l ==> (bt_to_ol cmp (list_to_bt l) = l) *)

val list_to_bt_ID = maybe_thm ("list_to_bt_ID", ``!cmp:'a toto t:'a bt.
          ENUMERAL cmp (list_to_bt (bt_to_ol cmp t)) = ENUMERAL cmp t``,
METIS_TAC [bt_to_ol_ID_IMP, ol_set, OL_bt_to_ol]);

(* Set operations. We already have smerge_set and smerge_OL. *)
(* "OL_UNION" possibly not the best name. *)

val OL_UNION = maybe_thm ("OL_UNION",
``!cmp:'a toto. !l m::OL cmp. OL cmp (smerge cmp l m) /\
                      (set (smerge cmp l m) = set l UNION set m)``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, smerge_set, smerge_OL]);

val OL_UNION_IMP = save_thm ("OL_UNION_IMP", REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_UNION));

(* OL_UNION_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (smerge cmp l m) /\ (set (smerge cmp l m) = set l UNION set m) *)

val ENUMERAL_UNION = maybe_thm ("ENUMERAL_UNION",
``!cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (smerge cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s UNION ENUMERAL cmp t``,
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (smerge cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC smerge_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
REWRITE_TAC [smerge_set]);

(* **************** Similar treatment of intersection: ************* *)

val sinter = Define
`(sinter (cmp:'a toto) [] [] = []) /\
 (sinter cmp (x:'a :: l) [] = []) /\
 (sinter cmp [] (y:'a :: m) = []) /\
 (sinter cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => sinter cmp l (y :: m)
                                 | EQUAL => x :: (sinter cmp l m)
                                 | GREATER => sinter cmp (x :: l) m)`;

val sinter_ind = theorem "sinter_ind";

val sinter_nil = maybe_thm ("sinter_nil",
``!cmp:'a toto l. (sinter cmp l [] = []) /\ (sinter cmp [] l = [])``,
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [sinter]);

val sinter_subset_inter = maybe_thm ("sinter_subset_inter",
``!cmp:'a toto l m x. MEM x (sinter cmp l m) ==> MEM x l /\ MEM x m``,
HO_MATCH_MP_TAC sinter_ind THEN
RW_TAC (srw_ss()) [sinter, MEM] THEN POP_ASSUM MP_TAC THEN
Cases_on `apto cmp x y` THEN RW_TAC (srw_ss ()) [] THEN RES_TAC THEN AR THEN
DISJ1_TAC THEN IMP_RES_TAC toto_equal_eq);

val sinter_OL = maybe_thm ("sinter_OL",
``!cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (sinter cmp l m)``,
HO_MATCH_MP_TAC sinter_ind THEN
RW_TAC (srw_ss()) [sinter, sinter_nil, OL] THEN
Cases_on `apto cmp x y` THEN RW_TAC (srw_ss ()) [OL] THEN
IMP_RES_TAC sinter_subset_inter THEN RES_TAC);

val inter_subset_sinter = maybe_thm ("inter_subset_sinter",
``!cmp:'a toto x l. OL cmp l /\ MEM x l ==>
     !m. OL cmp m /\ MEM x m ==> MEM x (sinter cmp l m)``,
GEN_TAC THEN GEN_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
GEN_TAC THEN STRIP_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
RW_TAC (srw_ss()) [sinter] THENL
[RW_TAC (srw_ss ()) [toto_refl, MEM]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 RW_TAC (srw_ss ()) [sinter, MEM] THENL
 [IMP_RES_TAC OL THEN IMP_RES_TAC totoLLtrans THEN
  IMP_RES_TAC toto_not_less_refl
 ,IMP_RES_TAC OL THEN RES_TAC
 ]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 RW_TAC (srw_ss ()) [sinter, MEM] THENL
 [`OL cmp l` by IMP_RES_TAC OL THEN RES_TAC THEN
  `MEM h' (h' :: m)` by REWRITE_TAC [MEM] THEN RES_TAC
 ,IMP_RES_TAC toto_equal_eq THEN AR
 ,`apto cmp h h' = LESS` by IMP_RES_TAC OL THEN
  IMP_RES_TAC totoLGtrans THEN IMP_RES_TAC toto_not_less_refl
 ]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 RW_TAC (srw_ss ()) [sinter, MEM] THENL
 [`MEM x (h' :: m)` by ASM_REWRITE_TAC [MEM] THEN IMP_RES_TAC OL THEN RES_TAC
 ,DISJ2_TAC THEN IMP_RES_TAC OL THEN RES_TAC
 ,IMP_RES_TAC OL THEN RES_TAC
]]);

(* Note that sinter_set, unlike smerge_set, depends on sorted input lists. *)

val sinter_set = maybe_thm ("sinter_set", ``!cmp:'a toto l m.
 OL cmp l /\ OL cmp m ==> (set (sinter cmp l m) = set l INTER set m)``,
RW_TAC (srw_ss ()) [IN_INTER, EXTENSION, IN_LIST_TO_SET] THEN EQ_TAC THENL
[MATCH_ACCEPT_TAC sinter_subset_inter
,METIS_TAC [inter_subset_sinter]
]);

val OL_INTER = maybe_thm ("OL_INTER",
``!cmp:'a toto. !l m::OL cmp. OL cmp (sinter cmp l m) /\
                      (set (sinter cmp l m) = set l INTER set m)``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, sinter_set, sinter_OL]);

val OL_INTER_IMP = save_thm ("OL_INTER_IMP", REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_INTER));

(* OL_INTER_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (sinter cmp l m) /\ (set (sinter cmp l m) = set l INTER set m) *)

val ENUMERAL_INTER = maybe_thm ("ENUMERAL_INTER",
``!cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (sinter cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s INTER ENUMERAL cmp t``,
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (sinter cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC sinter_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
MATCH_MP_TAC sinter_set THEN AR);

(* **************** Similar treatment of set difference: ************* *)

val sdiff = Define
`(sdiff (cmp:'a toto) [] [] = []) /\
 (sdiff cmp (x:'a :: l) [] = (x::l)) /\
 (sdiff cmp [] (y:'a :: m) = []) /\
 (sdiff cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => x :: sdiff cmp l (y :: m)
                                 | EQUAL => sdiff cmp l m
                                 | GREATER => sdiff cmp (x :: l) m)`;

val sdiff_ind = theorem "sdiff_ind";

val sdiff_nil = maybe_thm ("sdiff_nil",
``!cmp:'a toto l. (sdiff cmp l [] = l) /\ (sdiff cmp [] l = [])``,
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [sdiff]);

val diff_subset_sdiff = maybe_thm ("diff_subset_sdiff",
``!cmp:'a toto l m x. MEM x l /\ ~MEM x m ==> MEM x (sdiff cmp l m)``,
HO_MATCH_MP_TAC sdiff_ind THEN
RW_TAC (srw_ss()) [sdiff, MEM] THEN POP_ASSUM MP_TAC THEN
Cases_on `apto cmp x y` THEN RW_TAC (srw_ss ()) [] THEN RES_TAC THEN AR THEN
IMP_RES_TAC toto_equal_eq);

val OL_NOT_MEM = maybe_thm ("OL_NOT_MEM",
``!cmp:'a toto x l. OL cmp (x::l) ==> ~MEM x l``,
REPEAT GEN_TAC THEN REWRITE_TAC [OL] THEN STRIP_TAC THEN
DISCH_TAC THEN RES_THEN MP_TAC THEN
REWRITE_TAC [toto_refl, all_cpn_distinct]);

val sdiff_subset_diff = maybe_thm ("sdiff_subset_diff",
``!cmp:'a toto x l m. OL cmp l /\ OL cmp m ==>
                      MEM x (sdiff cmp l m) ==> MEM x l /\ ~MEM x m``,
GEN_TAC THEN GEN_TAC THEN Induct THEN REWRITE_TAC [MEM, sdiff_nil] THEN
GEN_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
RW_TAC (srw_ss()) [sdiff] THEN POP_ASSUM MP_TAC THEN
`OL cmp m` by IMP_RES_TAC OL THEN `OL cmp l` by IMP_RES_TAC OL THENL
[Cases_on `apto cmp h h'` THEN
 RW_TAC (srw_ss ()) [sdiff, MEM] THEN DISJ2_TAC THEN RES_TAC
,Cases_on `apto cmp h h'` THEN
 RW_TAC (srw_ss ()) [sdiff, MEM] THENL
 [IMP_RES_TAC toto_glneq
 ,METIS_TAC [MEM]
 ,IMP_RES_TAC toto_equal_eq THEN METIS_TAC [OL_NOT_MEM]
 ,`(x = h) \/ MEM x l` by METIS_TAC [] THEN IMP_RES_TAC toto_antisym THENL
  [AR THEN IMP_RES_TAC toto_glneq
  ,METIS_TAC [OL, totoLLtrans, toto_glneq]
 ]]
,Cases_on `apto cmp h h'` THEN
 RW_TAC (srw_ss ()) [sdiff, MEM] THENL
 [METIS_TAC [OL, totoLLtrans, toto_glneq]
 ,METIS_TAC [MEM]
]]);

val sdiff_OL = maybe_thm ("sdiff_OL",
``!cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (sdiff cmp l m)``,
GEN_TAC THEN Induct THEN1 REWRITE_TAC [sdiff_nil, OL] THEN GEN_TAC THEN
Induct THEN1 (REWRITE_TAC [sdiff_nil] THEN tautLib.TAUT_TAC) THEN
RW_TAC (srw_ss ()) [sdiff] THEN REWRITE_TAC [OL] THEN
IMP_RES_TAC OL THEN
Cases_on `apto cmp h h'` THEN RW_TAC (srw_ss ()) [OL] THEN
IMP_RES_TAC sdiff_subset_diff THEN RES_TAC);

(* Note that sdiff_set, like sinter_set, depends on sorted input lists. *)

val sdiff_set = maybe_thm ("sdiff_set", ``!cmp:'a toto l m.
 OL cmp l /\ OL cmp m ==> (set (sdiff cmp l m) = set l DIFF set m)``,
RW_TAC (srw_ss ()) [IN_DIFF, EXTENSION, IN_LIST_TO_SET] THEN EQ_TAC THENL
[METIS_TAC [sdiff_subset_diff]
,MATCH_ACCEPT_TAC diff_subset_sdiff
]);

val OL_DIFF = maybe_thm ("OL_DIFF",
``!cmp:'a toto. !l m::OL cmp. OL cmp (sdiff cmp l m) /\
                      (set (sdiff cmp l m) = set l DIFF set m)``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, sdiff_set, sdiff_OL]);

val OL_DIFF_IMP = save_thm ("OL_DIFF_IMP", REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_DIFF));

(* OL_DIFF_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (sdiff cmp l m) /\ (set (sdiff cmp l m) = set l DIFF set m) *)

val ENUMERAL_DIFF = maybe_thm ("ENUMERAL_DIFF",
``!cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (sdiff cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s DIFF ENUMERAL cmp t``,
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (sdiff cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC sdiff_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
MATCH_MP_TAC sdiff_set THEN AR);

(* ********************************************************************* *)
(*                  Theorems to assist conversions                       *)
(* ********************************************************************* *)

val ENUMERAL_set = store_thm ("ENUMERAL_set",
``!cmp l:'a list. set l = ENUMERAL cmp (list_to_bt (incr_ssort cmp l))``,
REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV (REWR_CONV (GSYM incr_ssort_set))) THEN
Q.SUBGOAL_THEN
`incr_ssort cmp l = bt_to_ol cmp (list_to_bt (incr_ssort cmp l))`
SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_ol_ID_IMP) THEN MATCH_ACCEPT_TAC incr_ssort_OL
,REWRITE_TAC [list_to_bt_ID, ol_set]
]);

val OL_ENUMERAL = store_thm ("OL_ENUMERAL",
``!cmp l:'a list. OL cmp l ==> (set l = ENUMERAL cmp (list_to_bt l))``,
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN
`l = bt_to_ol cmp (list_to_bt l)` SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_ol_ID_IMP) THEN AR
,REWRITE_TAC [list_to_bt_ID, ol_set]
]);

val bt_to_ol_thm = maybe_thm ("bt_to_ol_thm",
``!cmp:'a toto t. bt_to_ol cmp t = bt_to_ol_ac cmp t []``,
RW_TAC (srw_ss ()) [ol_ac_thm]);

val OWL_UNION_THM = store_thm ("OWL_UNION_THM", ``!cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s UNION t) (smerge cmp l m)``,
METIS_TAC [OWL, OL_UNION_IMP]);

val OWL_INTER_THM = store_thm ("OWL_INTER_THM", ``!cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s INTER t) (sinter cmp l m)``,
METIS_TAC [OWL, OL_INTER_IMP]);

val OWL_DIFF_THM = store_thm ("OWL_DIFF_THM", ``!cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s DIFF t) (sdiff cmp l m)``,
METIS_TAC [OWL, OL_DIFF_IMP]);

(* ******************************************************************* *)
(*  Test for a bt with no spurious nodes, as should be invariably the  *)
(*  case, and justify quicker bt_to_ol for bt's passing the test,      *)
(*  makes exactly n - 1 comparisons in passing a tree with n nodes.    *)
(* ******************************************************************* *)

val OL_bt_lb_ub = Define
`(OL_bt_lb_ub cmp lb (nt:'a bt) ub = (apto cmp lb ub = LESS)) /\
 (OL_bt_lb_ub cmp lb (node l x r) ub = OL_bt_lb_ub cmp lb l x /\
                                       OL_bt_lb_ub cmp x r ub)`;

val OL_bt_lb = Define
`(OL_bt_lb cmp lb (nt:'a bt) = T) /\
 (OL_bt_lb cmp lb (node l x r) = OL_bt_lb_ub cmp lb l x /\
                                 OL_bt_lb cmp x r)`;

val OL_bt_ub = Define
`(OL_bt_ub cmp (nt:'a bt) ub = T) /\
 (OL_bt_ub cmp (node l x r) ub = OL_bt_ub cmp l x /\
                                 OL_bt_lb_ub cmp x r ub)`;

val OL_bt = Define
`(OL_bt cmp (nt:'a bt) = T) /\
 (OL_bt cmp (node l x r) = OL_bt_ub cmp l x /\ OL_bt_lb cmp x r)`;

val OL_bt_lb_ub_lem = maybe_thm ("OL_bt_lb_ub_lem",
``!cmp t lb ub. OL_bt_lb_ub cmp lb t ub ==> (apto cmp lb ub = LESS)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [OL_bt_lb_ub] THEN METIS_TAC [ totoLLtrans]);

val OL_bt_lb_ub_thm = maybe_thm ("OL_bt_lb_ub_thm",
``!cmp t:'a bt lb ub. OL_bt_lb_ub cmp lb t ub ==>
                      (bt_to_ol_lb_ub cmp lb t ub = bt_to_list t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [OL_bt_lb_ub, bt_to_ol_lb_ub, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]);

val OL_bt_lb_thm = maybe_thm ("OL_bt_lb_thm",
``!cmp t:'a bt lb. OL_bt_lb cmp lb t ==>
                   (bt_to_ol_lb cmp lb t = bt_to_list t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [OL_bt_lb, bt_to_ol_lb, OL_bt_lb_ub_thm, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]);

val OL_bt_ub_thm = maybe_thm ("OL_bt_ub_thm",
``!cmp t:'a bt ub. OL_bt_ub cmp t ub ==>
                   (bt_to_ol_ub cmp t ub = bt_to_list t)``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [OL_bt_ub, bt_to_ol_ub, OL_bt_lb_ub_thm, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]);

val OL_bt_thm = maybe_thm ("OL_bt_thm",
``!cmp t:'a bt. OL_bt cmp t ==> (bt_to_ol cmp t = bt_to_list t)``,
GEN_TAC THEN Cases THEN
RW_TAC (srw_ss ()) [OL_bt, bt_to_ol, OL_bt_lb_thm, OL_bt_ub_thm, bt_to_list]);

val better_bt_to_ol = store_thm ("better_bt_to_ol",
``!cmp t:'a bt. bt_to_ol cmp t = if OL_bt cmp t then bt_to_list_ac t []
                                                else bt_to_ol_ac cmp t []``,
METIS_TAC [OL_bt_thm, bt_to_list_thm, bt_to_ol_thm]);

(* ******************* Theorem to support set_TO_OWL ********************* *)

val set_OWL_thm = store_thm ("set_OWL_thm",
``!cmp l:'a list. OWL cmp (set l) (incr_ssort cmp l)``,
REWRITE_TAC [OWL, incr_ssort_set, incr_ssort_OL]);

val _ = export_theory ();
val _ = print_theory "-";

end;
