(* file HS/PIN/enumeralScript.sml, created 4/15/13 F.L. Morris *)
(* PIN-based finite set representation; name a homage to numeralTheory *)
(* Revision of 5/12/13 - bringing back bt & bl to avoid finiteness hyps. *)
Theory enumeral
Ancestors
  pred_set relation res_quan toto list
Libs
  pred_setLib res_quanLib


(* app load ["totoTheory", "res_quanLib"]; *)

val _ = set_trace "Unicode" 0;
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``
Type cpn[local] = “:ordering”
val _ = ParseExtras.temp_loose_equality()

(* "enumeral" for "enumerated finite set", wordplay on "NUMERAL" *)

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

Datatype: bt = nt | node bt 'a bt
End
Datatype: bl = nbl | zerbl bl | onebl 'a ('a bt) bl
End

val bt_size_def = definition "bt_size_def";
val bl_size_def = definition "bl_size_def";

(* helper function, BL_ACCUM, for use only by BL_CONS: *)

Definition BL_ACCUM:  (BL_ACCUM (a:'a) ac nbl = onebl a ac nbl)
                   /\ (BL_ACCUM a ac (zerbl bl) = onebl a ac bl)
                   /\ (BL_ACCUM a ac (onebl r rft bl) =
                        zerbl (BL_ACCUM a (node ac r rft) bl))
End

Definition BL_CONS:  BL_CONS (a:'a) bl = BL_ACCUM a nt bl
End

Definition list_to_bl:  (list_to_bl [] = nbl)
                     /\ (list_to_bl (a:'a :: l) = BL_CONS a (list_to_bl l))
End

(* flatten a bt back to a list, without and with an accumulating parameter. *)

Definition bt_to_list:
 (bt_to_list (nt:'a bt) = []) /\
 (bt_to_list (node l x r) = bt_to_list l ++ [x] ++ bt_to_list r)
End

Definition bt_to_list_ac:
 (bt_to_list_ac (nt:'a bt) m = m) /\
 (bt_to_list_ac (node l x r) m = bt_to_list_ac l (x :: bt_to_list_ac r m))
End

Theorem bt_to_list_ac_thm[local]:
  !t:'a bt m. bt_to_list_ac t m = bt_to_list t ++ m
Proof
Induct THEN SRW_TAC [] [bt_to_list, bt_to_list_ac]
QED

Theorem bt_to_list_thm:
  !t:'a bt. bt_to_list t = bt_to_list_ac t []
Proof
REWRITE_TAC [bt_to_list_ac_thm, APPEND_NIL]
QED

(* Although we should have no need to prove in HOL that bl's built with
BL_CONS have the desirable balance properties that make them efficient,
we do need a lemma about the size of bl's to support inductive definitions.*)

(* helper function, bt_rev, for use here and below by bt_to_bl: *)

Definition bt_rev:
    (bt_rev (nt:'a bt) bl = bl)
 /\ (bt_rev (node lft r rft) bl = bt_rev lft (onebl r rft bl))
End

Definition K2:  K2 (a:'a) = 2
End

Theorem bt_rev_size[local]:
 !ft bl:'a bl. bl_size K2 (bt_rev ft bl) = bt_size K2 ft + bl_size K2 bl
Proof
Induct THEN
ASM_REWRITE_TAC [bl_size_def, bt_size_def, K2,bt_rev,arithmeticTheory.ADD] THEN
SIMP_TAC arith_ss []
QED

(* How to turn a bl into a bt (unreversibly). bl_rev is named after the
   classical helper function for reverse (listTheory's REV). *)

Definition bl_rev:  (bl_rev ft (nbl:'a bl) = ft) /\
                 (bl_rev ft (zerbl b) = bl_rev ft b) /\
                 (bl_rev ft (onebl a f b) = bl_rev (node ft a f) b)
End

Definition bl_to_bt:  bl_to_bt = bl_rev (nt:'a bt)
End

(* And how to turn a bt into a condensed bl (or "cl") - zerbls omitted -
   by dissasembling left subtrees only. Helper bt_rev is defined above. *)

Definition bt_to_bl:  bt_to_bl (t:'a bt) = bt_rev t nbl
End

(* Likely to be needed: *)

Theorem slinky[local]:
 !(t:'a bt) bb. bl_to_bt (bt_rev t bb) = bl_rev t bb
Proof
Induct THENL
[REWRITE_TAC [bl_to_bt, bt_rev]
,REPEAT GEN_TAC THEN ASM_REWRITE_TAC [bt_rev, bl_rev]]
QED

Theorem bt_to_bl_to_bt_ID[local]:
 !t:'a bt. bl_to_bt (bt_to_bl t) = t
Proof
REWRITE_TAC [bt_to_bl, slinky, bl_rev]
QED

Definition list_to_bt:  list_to_bt (l:'c list) = bl_to_bt (list_to_bl l)
End

(* *****  We use "OL" for strictly                                  ***** *)
(* ***** ordered lists where the whole element is the key;          ***** *)
(* ***** eventually "ORL" for function-modeling sorted lists.       ***** *)

Definition OL:  (OL (cmp:'a toto) ([]:'a list) = T) /\
                (OL cmp (a :: l) = OL cmp l /\
                   (!p. MEM p l ==> (apto cmp a p = LESS)))
End

(* ***************************************************************** *)
(*  merge sorting for sets here, with initial "s"; plain merge etc.  *)
(*  are reserved as names for association-list sorting.              *)
(* ***************************************************************** *)

Definition smerge:
 (smerge (cmp:'a toto) [] [] = []) /\
 (smerge cmp (x:'a :: l) [] = x :: l) /\
 (smerge cmp [] (y:'a :: m) = y :: m) /\
 (smerge cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => x :: (smerge cmp l (y :: m))
                                 | EQUAL => x :: (smerge cmp l m)
                                 | GREATER => y :: (smerge cmp (x :: l) m))
End

Theorem smerge_nil:
  !cmp:'a toto l. (smerge cmp l [] = l) /\ (smerge cmp [] l = l)
Proof
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [smerge]
QED

(* corresponding merge_set will need ORL hypotheses, and corresp. merge_ORL
   will need 3 `merge ... =  ... UNION ...` by MATCH_MP_TAC merge_set THEN...*)

Theorem smerge_set[local]:
  !cmp:'a toto l m. (set (smerge cmp l m) = set l UNION set m)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [smerge, smerge_nil] THEN
Induct_on `m` THEN
SRW_TAC [] [smerge, smerge_nil] THEN
Cases_on `apto cmp h h'` THENL
[ALL_TAC, `h = h'` by IMP_RES_TAC toto_equal_eq, ALL_TAC] THEN
SRW_TAC [] [toto_equal_eq] THEN
RW_TAC bool_ss [toto_equal_eq, EXTENSION, IN_INSERT, IN_UNION, DISJ_ASSOC] THEN
tautLib.TAUT_TAC
QED

Theorem smerge_OL:
  !cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (smerge cmp l m)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [smerge, OL, smerge_nil] THEN
Induct_on `m` THEN
SRW_TAC [] [smerge, OL, smerge_nil] THEN
Cases_on `apto cmp h h'` THEN SRW_TAC [] [OL] THENL
[`MEM p l \/ MEM p (h' :: m)`
 by (RW_TAC bool_ss [GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set]) THENL
 [RES_TAC
 ,`(p = h') \/ MEM p m` by ASM_REWRITE_TAC [GSYM MEM] THENL
  [AR, RES_TAC THEN IMP_RES_TAC totoLLtrans
 ]]
,`MEM p l \/ MEM p m`
 by (RW_TAC bool_ss [GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set]) THENL
 [RES_TAC
 ,RES_TAC THEN IMP_RES_TAC totoELtrans
 ]
,`MEM p (h :: l) \/ MEM p m`
 by (RW_TAC bool_ss [GSYM IN_UNION] THEN
     ASM_REWRITE_TAC [GSYM smerge_set]) THENL
 [`(p = h) \/ MEM p l` by ASM_REWRITE_TAC [GSYM MEM] THENL
  [ASM_REWRITE_TAC [GSYM toto_antisym],
   RES_TAC THEN IMP_RES_TAC totoGLtrans
  ]
  ,RES_TAC
]]
QED

Definition OL_sublists:
 (OL_sublists cmp ([]:'a list option list) = T) /\
 (OL_sublists cmp (NONE :: lol) = OL_sublists cmp lol) /\
 (OL_sublists cmp (SOME m :: lol) = OL cmp m /\ OL_sublists cmp lol)
End

val OL_sublists_ind = theorem "OL_sublists_ind";

(* OL_sublists_ind = |- !P. (!cmp. P cmp []) /\
          (!cmp lol. P cmp lol ==> P cmp (NONE::lol)) /\
          (!cmp m lol. P cmp lol ==> P cmp (SOME m::lol)) ==> !v v1. P v v1 *)

Definition lol_set:
 (lol_set ([]:'a list option list) = {}) /\
 (lol_set (NONE :: lol) = lol_set lol) /\
 (lol_set (SOME m :: lol) = set m UNION lol_set lol)
End

Definition incr_smerge:
 (incr_smerge cmp (l:'a list) [] = [SOME l]) /\
 (incr_smerge cmp l (NONE :: lol) = SOME l :: lol) /\
 (incr_smerge cmp l (SOME m :: lol) =
   NONE :: incr_smerge cmp (smerge cmp l m) lol)
End

Theorem incr_smerge_set[local]:
    !cmp lol l:'a list.
               lol_set (incr_smerge cmp l lol) = set l UNION lol_set lol
Proof
HO_MATCH_MP_TAC OL_sublists_ind THEN
RW_TAC bool_ss [incr_smerge, smerge_set, lol_set, UNION_ASSOC]
QED

Theorem incr_smerge_OL:   !cmp lol l:'a list.
OL_sublists cmp lol /\ OL cmp l ==> OL_sublists cmp (incr_smerge cmp l lol)
Proof
HO_MATCH_MP_TAC OL_sublists_ind THEN
RW_TAC bool_ss [incr_smerge, smerge_OL, OL_sublists]
QED

Definition smerge_out:
 (smerge_out (cmp:'a toto) l ([]:'a list option list) = l) /\
 (smerge_out cmp l (NONE :: lol) = smerge_out cmp l lol) /\
 (smerge_out cmp l (SOME m :: lol) = smerge_out cmp (smerge cmp l m) lol)
End

val smerge_out_ind = theorem "smerge_out_ind";

(* smerge_out_ind = |- !P. (!cmp l. P cmp l []) /\
     (!cmp l lol. P cmp l lol ==> P cmp l (NONE::lol)) /\
     (!cmp l m lol. P cmp (smerge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
     !v v1 v2. P v v1 v2 *)

Theorem smerge_out_set[local]:
    !cmp:'a toto l:'a list lol.
         set (smerge_out cmp l lol) = set l UNION lol_set lol
Proof
HO_MATCH_MP_TAC smerge_out_ind THEN
RW_TAC bool_ss [smerge_out, lol_set, smerge_set, UNION_EMPTY, UNION_ASSOC]
QED

Theorem smerge_out_OL[local]:
    !cmp:'a toto l:'a list lol.
OL cmp l /\ OL_sublists cmp lol ==> OL cmp (smerge_out cmp l lol)
Proof
HO_MATCH_MP_TAC smerge_out_ind THEN
RW_TAC bool_ss [smerge_out, OL_sublists] THEN
METIS_TAC [smerge_OL]
QED

Definition incr_sbuild:
 (incr_sbuild (cmp:'a toto) [] = []) /\
 (incr_sbuild cmp (x :: l) = incr_smerge cmp [x] (incr_sbuild cmp l))
End

Theorem incr_sbuild_set[local]:
  !cmp l:'a list. lol_set (incr_sbuild cmp l) = set l
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [lol_set, incr_sbuild, incr_smerge_set, INSERT_UNION_EQ]
QED

Theorem  OL_EMPTY[local]:
  !cmp:'a toto. OL cmp []
Proof
REWRITE_TAC [OL]
QED

Theorem OL_SING[local]:
  !cmp:'a toto x. OL cmp [x]
Proof
RW_TAC bool_ss [OL, MEM]
QED

Theorem incr_sbuild_OL[local]:
  !cmp l:'a list. OL_sublists cmp (incr_sbuild cmp l)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [incr_sbuild, incr_smerge_OL, OL_sublists] THEN
METIS_TAC [OL_SING, incr_smerge_OL]
QED

Definition incr_ssort:
 incr_ssort (cmp:'a toto) l = smerge_out cmp [] (incr_sbuild cmp l)
End

Theorem incr_ssort_set[local]:
  !cmp:'a toto l. set (incr_ssort cmp l) = set l
Proof
SRW_TAC [] [incr_ssort, smerge_out_set, incr_sbuild_set]
QED

Theorem incr_ssort_OL[local]:
  !cmp:'a toto l. OL cmp (incr_ssort cmp l)
Proof
REWRITE_TAC [incr_ssort] THEN
METIS_TAC [incr_sbuild_OL, OL, smerge_out_OL]
QED

Theorem OL_MEM_EQ[local]:
  !cmp:'a toto l m. OL cmp l /\ OL cmp m ==>
   ((!x. MEM x l = MEM x m) <=> (l = m))
Proof
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
]]]
QED

(* *********** end of digression to program sorting ************** *)

(* Define the set represented (according to a total order) by a bt *)

(* Following should really be called "bt_to_set", but ENUMERAL, like
   NUMERAL, will flag the terms that represent sets as trees. *)

Definition bt_to_set:
 (ENUMERAL cmp nt = {}) /\
 (ENUMERAL (cmp:'a toto) (node l x r) =
    {y | y IN ENUMERAL cmp l /\ (apto cmp y x = LESS)} UNION {x} UNION
    {z | z IN ENUMERAL cmp r /\ (apto cmp x z = LESS)})
End

Definition bt_to_set_lb:  bt_to_set_lb cmp (lb:'a) t =
                     {x | x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS)}
End

Definition bt_to_set_ub:  bt_to_set_ub cmp t (ub:'a) =
                     {x | x IN ENUMERAL cmp t /\ (apto cmp x ub = LESS)}
End

Theorem bt_to_set_mut_rec[local]:
  !cmp:'a toto l x r. ENUMERAL cmp (node l x r) =
        bt_to_set_ub cmp l x UNION {x} UNION bt_to_set_lb cmp x r
Proof
REWRITE_TAC [bt_to_set_lb, bt_to_set_ub] THEN REWRITE_TAC [bt_to_set]
QED

Definition bt_to_set_lb_ub:  bt_to_set_lb_ub cmp lb t (ub:'a) =
{x | x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}
End

Theorem IN_bt_to_set:
  (!cmp:'a toto y. y IN ENUMERAL cmp nt = F) /\
  (!cmp:'a toto l x r y. y IN ENUMERAL cmp (node l x r) =
   y IN ENUMERAL cmp l /\ (apto cmp y x = LESS) \/ (y = x) \/
   y IN ENUMERAL cmp r /\ (apto cmp x y = LESS))
Proof
SRW_TAC [] [bt_to_set] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
tautLib.TAUT_TAC
QED

(* Following look-up function (disguised as two theorems) to make bt's
   imitate IN on finite sets, may or may not be the reasonable way to go. *)

Theorem NOT_IN_nt = CONJUNCT1 IN_bt_to_set;

(* NOT_IN_nt = |- !cmp y. y IN ENUMERAL cmp nt <=> F *)

Theorem IN_node:
  !cmp x:'a l y r. x IN ENUMERAL cmp (node l y r) <=> case apto cmp x y of
 LESS => x IN ENUMERAL cmp l | EQUAL => T | GREATER => x IN ENUMERAL cmp r
Proof
SRW_TAC [] [bt_to_set] THEN Cases_on `apto cmp x y` THEN
(Q.SUBGOAL_THEN `(x = y) = (apto cmp x y = EQUAL)` SUBST1_TAC
           THEN1 MATCH_ACCEPT_TAC (GSYM toto_equal_eq)) THEN
IMP_RES_TAC toto_antisym THEN SRW_TAC [] []
QED

(* Following "mut_rec" theorems seem relevant to conversion to ol's, not to
   evaluating IN. *)

Theorem bt_to_set_lb_ub_mut_rec[local]:
  !cmp:'a toto lb l x r ub. bt_to_set_lb_ub cmp lb (node l x r) ub =
     if apto cmp lb x = LESS then
       if apto cmp x ub = LESS then
         bt_to_set_lb_ub cmp lb l x UNION {x} UNION  bt_to_set_lb_ub cmp x r ub
       else
         bt_to_set_lb_ub cmp lb l ub
     else
       bt_to_set_lb_ub cmp lb r ub
Proof
SRW_TAC [] [bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp x' ub = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN SRW_TAC [] []
,Q.UNDISCH_TAC `apto cmp lb x' = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN SRW_TAC [] []
]
QED

Theorem bt_to_set_lb_mut_rec[local]:
  !cmp:'a toto lb l x r. bt_to_set_lb cmp lb (node l x r) =
     if apto cmp lb x = LESS then
         bt_to_set_lb_ub cmp lb l x UNION {x} UNION  bt_to_set_lb cmp x r
     else
       bt_to_set_lb cmp lb r
Proof
SRW_TAC [] [bt_to_set_lb, bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp lb x' = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN SRW_TAC [] []
]
QED

Theorem bt_to_set_ub_mut_rec[local]:
  !cmp:'a toto ub l x r. bt_to_set_ub cmp (node l x r) ub =
     if apto cmp x ub = LESS then
         bt_to_set_ub cmp l x UNION {x} UNION  bt_to_set_lb_ub cmp x r ub
     else
       bt_to_set_ub cmp l ub
Proof
SRW_TAC [] [bt_to_set_ub, bt_to_set_lb_ub, EXTENSION, IN_bt_to_set] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN IMP_RES_TAC totoLLtrans THENL
[Q.UNDISCH_TAC `apto cmp x' ub = LESS` THEN AR
,IMP_RES_TAC NOT_EQ_LESS_IMP THEN SRW_TAC [] []
]
QED

(* ****************************************************************** *)
(* For computational purposes, we need to go from ENUMERAL-terms to   *)
(* ordered lists of the same elements. Possiibly to no purpose, we    *)
(* supply first a general translation that extracts from any bt at all*)
(* the list of the same elements as are in bt_to_set of it. Later, we *)
(* will see that checking for no out-of-order elements separately     *)
(* allows a faster translation by bt_to_list, with about half the     *)
(* comparisons of the general method. (See better_bt_to_ol below.)    *)
(* ****************************************************************** *)

Definition bt_to_ol_lb_ub:
 (bt_to_ol_lb_ub (cmp:'a toto) lb nt ub = []) /\
 (bt_to_ol_lb_ub cmp lb (node l x r) ub =
   if apto cmp lb x = LESS then
      if apto cmp x ub = LESS then
            bt_to_ol_lb_ub cmp lb l x ++ [x] ++ bt_to_ol_lb_ub cmp x r ub
      else bt_to_ol_lb_ub cmp lb l ub
   else bt_to_ol_lb_ub cmp lb r ub)
End

Definition bt_to_ol_lb:
 (bt_to_ol_lb (cmp:'a toto) lb nt = []) /\
 (bt_to_ol_lb cmp lb (node l x r) =
   if apto cmp lb x = LESS then
            bt_to_ol_lb_ub cmp lb l x ++ [x] ++ bt_to_ol_lb cmp x r
   else bt_to_ol_lb cmp lb r)
End

Definition bt_to_ol_ub:
 (bt_to_ol_ub (cmp:'a toto) nt ub = []) /\
 (bt_to_ol_ub cmp (node l x r) ub =
   if apto cmp x ub = LESS then
            bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb_ub cmp x r ub
   else bt_to_ol_ub cmp l ub)
End

Definition bt_to_ol:
 (bt_to_ol (cmp:'a toto) nt = []) /\
 (bt_to_ol cmp (node l x r) =
   bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb cmp x r)
End

(* Show ordered lists have the correct sets of elements: *)

Theorem ol_set_lb_ub[local]:
   !cmp:'a toto t lb ub.
   bt_to_set_lb_ub cmp lb t ub = set (bt_to_ol_lb_ub cmp lb t ub)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bt_to_set_lb_ub_mut_rec, bt_to_ol_lb_ub,
                    LIST_TO_SET_APPEND, EXTENSION] THEN
SRW_TAC [] [NOT_IN_nt, bt_to_set_lb_ub]
QED

Theorem ol_set_lb[local]:
   !cmp:'a toto t lb.
   bt_to_set_lb cmp lb t = set (bt_to_ol_lb cmp lb t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bt_to_set_lb_mut_rec, bt_to_ol_lb,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb_ub] THEN
SRW_TAC [] [NOT_IN_nt, bt_to_set_lb]
QED

Theorem ol_set_ub[local]:
   !cmp:'a toto t ub.
   bt_to_set_ub cmp t ub = set (bt_to_ol_ub cmp t ub)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bt_to_set_ub_mut_rec, bt_to_ol_ub,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb_ub] THEN
SRW_TAC [] [NOT_IN_nt, bt_to_set_ub]
QED

Theorem ol_set:
  !cmp:'a toto t. ENUMERAL cmp t = set (bt_to_ol cmp t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bt_to_set_mut_rec, bt_to_ol,
                    LIST_TO_SET_APPEND, EXTENSION, ol_set_lb, ol_set_ub] THEN
REWRITE_TAC [NOT_IN_nt]
QED

(* We have neglected so far to prove that bt_to_ol and its kin produce
   lists satisfying OL cmp. *)

Theorem list_split_lem[local]:
  !cmp:'a toto l x r. OL cmp (l ++ [x] ++ r) <=>
   OL cmp l /\ (!a. a IN set l ==> (apto cmp a x = LESS)) /\
   OL cmp r /\ (!z. z IN set r ==> (apto cmp x z = LESS))
Proof
GEN_TAC THEN Induct THEN SRW_TAC [] [OL] THEN EQ_TAC THEN
SRW_TAC [] [] THENL
[POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []
,RES_TAC
,RES_TAC
,Q.UNDISCH_THEN `!a. (a = h) \/ MEM a l ==> (apto cmp a p = LESS)`
                MATCH_MP_TAC THEN REWRITE_TAC []
,MATCH_MP_TAC totoLLtrans THEN Q.EXISTS_TAC `x` THEN CONJ_TAC THENL
 [Q.UNDISCH_THEN `!a. (a = h) \/ MEM a l ==> (apto cmp a x = LESS)`
                MATCH_MP_TAC THEN REWRITE_TAC []
 ,RES_TAC
]]
QED

Theorem MEM_lb_ub_lem[local]:
  !cmp:'a toto lb t ub a. MEM a (bt_to_ol_lb_ub cmp lb t ub) ==>
    (apto cmp lb a = LESS) /\ (apto cmp a ub = LESS)
Proof
REWRITE_TAC [GSYM ol_set_lb_ub] THEN
SRW_TAC [] [bt_to_set_lb_ub]
QED

Theorem OL_bt_to_ol_lb_ub:
  !cmp:'a toto t lb ub. OL cmp (bt_to_ol_lb_ub cmp lb t ub)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bt_to_ol_lb_ub, ol_set_lb_ub, list_split_lem] THEN
IMP_RES_TAC MEM_lb_ub_lem THEN REWRITE_TAC [OL]
QED

Theorem MEM_lb_lem[local]:
  !cmp:'a toto lb t a. MEM a (bt_to_ol_lb cmp lb t) ==>(apto cmp lb a = LESS)
Proof
REWRITE_TAC [GSYM ol_set_lb] THEN
SRW_TAC [] [bt_to_set_lb]
QED

Theorem OL_bt_to_ol_lb:
  !cmp:'a toto t lb. OL cmp (bt_to_ol_lb cmp lb t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC []
 [bt_to_ol_lb, ol_set_lb, list_split_lem, OL_bt_to_ol_lb_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_lb_ub_lem
,IMP_RES_TAC MEM_lb_lem
]
QED

Theorem MEM_ub_lem[local]:
  !cmp:'a toto t ub a. MEM a (bt_to_ol_ub cmp t ub) ==>(apto cmp a ub = LESS)
Proof
REWRITE_TAC [GSYM ol_set_ub] THEN
SRW_TAC [] [bt_to_set_ub]
QED

Theorem OL_bt_to_ol_ub:
  !cmp:'a toto t ub. OL cmp (bt_to_ol_ub cmp t ub)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC []
 [bt_to_ol_ub, ol_set_ub, list_split_lem, OL_bt_to_ol_lb_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_ub_lem
,IMP_RES_TAC MEM_lb_ub_lem
]
QED

Theorem OL_bt_to_ol:
  !cmp:'a toto t. OL cmp (bt_to_ol cmp t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC []
 [bt_to_ol, ol_set, list_split_lem, OL_bt_to_ol_lb, OL_bt_to_ol_ub] THENL
[REWRITE_TAC [OL]
,IMP_RES_TAC MEM_ub_lem
,IMP_RES_TAC MEM_lb_lem
]
QED

(* ******* Now to suppress the APPENDing ******** *)

Definition bt_to_ol_lb_ub_ac:
 (bt_to_ol_lb_ub_ac (cmp:'a toto) lb nt ub m = m) /\
 (bt_to_ol_lb_ub_ac cmp lb (node l x r) ub m =
 if apto cmp lb x = LESS then
    if apto cmp x ub = LESS then
      bt_to_ol_lb_ub_ac cmp lb l x (x :: bt_to_ol_lb_ub_ac cmp x r ub m)
    else bt_to_ol_lb_ub_ac cmp lb l ub m
 else bt_to_ol_lb_ub_ac cmp lb r ub m)
End

Theorem ol_lb_ub_ac_thm[local]:
  !cmp:'a toto t lb ub m. bt_to_ol_lb_ub_ac cmp lb t ub m =
                          bt_to_ol_lb_ub cmp lb t ub ++ m
Proof
GEN_TAC THEN Induct THEN SRW_TAC [][bt_to_ol_lb_ub, bt_to_ol_lb_ub_ac]
QED

Definition bt_to_ol_lb_ac:
 (bt_to_ol_lb_ac (cmp:'a toto) lb nt m = m) /\
 (bt_to_ol_lb_ac cmp lb (node l x r) m =
 if apto cmp lb x = LESS then
      bt_to_ol_lb_ub_ac cmp lb l x (x :: bt_to_ol_lb_ac cmp x r m)
 else bt_to_ol_lb_ac cmp lb r m)
End

Theorem ol_lb_ac_thm[local]:
  !cmp:'a toto t lb m. bt_to_ol_lb_ac cmp lb t m = bt_to_ol_lb cmp lb t ++ m
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [][bt_to_ol_lb, bt_to_ol_lb_ac, ol_lb_ub_ac_thm]
QED

Definition bt_to_ol_ub_ac:
 (bt_to_ol_ub_ac (cmp:'a toto) nt ub m = m) /\
 (bt_to_ol_ub_ac cmp (node l x r) ub m =
    if apto cmp x ub = LESS then
      bt_to_ol_ub_ac cmp l x (x :: bt_to_ol_lb_ub_ac cmp x r ub m)
    else bt_to_ol_ub_ac cmp l ub m)
End

Theorem ol_ub_ac_thm[local]:
  !cmp:'a toto t ub m. bt_to_ol_ub_ac cmp t ub m = bt_to_ol_ub cmp t ub ++ m
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [][bt_to_ol_ub, bt_to_ol_ub_ac, ol_lb_ub_ac_thm]
QED

Definition bt_to_ol_ac:
 (bt_to_ol_ac (cmp:'a toto) nt m = m) /\
 (bt_to_ol_ac cmp (node l x r) m =
      bt_to_ol_ub_ac cmp l x (x :: bt_to_ol_lb_ac cmp x r m))
End

Theorem ol_ac_thm[local]:
  !cmp:'a toto t m. bt_to_ol_ac cmp t m = bt_to_ol cmp t ++ m
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [][bt_to_ol, bt_to_ol_ac, ol_lb_ac_thm, ol_ub_ac_thm]
QED

(* ********* "OWL" for [set] Ordered With List *********** *)

Definition OWL:  OWL (cmp:'a toto) (s:'a set) (l:'a list) =
(s = set l) /\ OL cmp l
End

Theorem OWL_unique[local]:
  !cmp:'a toto s l m. OWL cmp s l /\ OWL cmp s m ==> (l = m)
Proof
RW_TAC bool_ss [OWL] THEN
METIS_TAC [OL_MEM_EQ]
QED

(* We want to compute bt_to_ol  with as few comparisons as may be. The
   definitions have used APPEND. *)

Theorem bt_FINITE[local]:
  !cmp:'a toto t:'a bt. FINITE (ENUMERAL cmp t)
Proof
REWRITE_TAC [ol_set, FINITE_LIST_TO_SET]
QED

Theorem OWL_bt_to_ol:
  !cmp:'a toto t. OWL cmp (ENUMERAL cmp t) (bt_to_ol cmp t)
Proof
RW_TAC bool_ss [OWL, ol_set, OL_bt_to_ol]
QED

(* We already have the two pieces of OWL:

  OL_bt_to_ol = |- !t cmp. OL cmp (bt_to_ol cmp t)
  ol_set = |- !cmp t. ENUMERAL cmp t = set (bt_to_ol cmp t) *)

(* ************* Stuff about ZSL, OSL, and OU (some interesting proofs)
   appeared not of any use, exiled to OU.stuff ********************* *)

(* Prove that bt_to_ol inverts list_to_bt for ordered lists, using OL_MEM_EQ *)

Theorem OL_set_EQ[local]:
  !cmp:'a toto l m. OL cmp l /\ OL cmp m ==> ((set l = set m) <=> (l = m))
Proof
REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP OL_MEM_EQ) THEN
REWRITE_TAC [EXTENSION]
QED

(* "OU" for "Ordered Union" - used for intermediate (tree, binary list) pair
   in converting betw. binary lists and rightist trees. *)

Definition OU:  OU (cmp:'a toto) (t:'a set) (u:'a set) =
         {x | x IN t /\ (!z. z IN u ==> (apto cmp x z = LESS))} UNION u
End

Definition UO:  UO (cmp:'a toto) (s:'a set) (t:'a set) =
         s UNION {y | y IN t /\ (!z. z IN s ==> (apto cmp z y = LESS))}
End

Theorem EMPTY_OU:
  !cmp:'a toto sl:'a set. OU cmp {} sl = sl
Proof
REWRITE_TAC [OU, NOT_IN_EMPTY, UNION_EMPTY, GSPEC_F]
QED

Theorem OU_EMPTY:
  !cmp:'a toto t:'a set. OU cmp t {} = t
Proof
REWRITE_TAC [OU, NOT_IN_EMPTY, UNION_EMPTY, GSPEC_ID]
QED

Theorem sing_UO[local]:
   !cmp:'a toto x:'a t:'a set.
        {x} UNION {y | y IN t /\ (apto cmp x y = LESS)} = UO cmp {x} t
Proof
RW_TAC bool_ss [UO, IN_SING]
QED

Theorem LESS_UO_LEM:
  !cmp:'a toto x:'a y:'a s:'a set.
  (!z. z IN UO cmp {x} s ==> (apto cmp y z = LESS)) <=> (apto cmp y x = LESS)
Proof
RW_TAC bool_ss [GSYM sing_UO] THEN EQ_TAC THEN
REWRITE_TAC [IN_UNION, IN_SING] THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THENL
[CONV_TAC LEFT_IMP_FORALL_CONV THEN
 Q.EXISTS_TAC `x` THEN RW_TAC bool_ss []
,REPEAT STRIP_TAC THENL [AR, IMP_RES_TAC toto_trans_less]
]
QED

Theorem bt_to_set_OU_UO[local]:
  !cmp:'a toto l:'a bt x:'a r:'a bt. ENUMERAL cmp (node l x r) =
 OU cmp (ENUMERAL cmp l) (UO cmp {x} (ENUMERAL cmp r))
Proof
RW_TAC bool_ss [OU, bt_to_set, LESS_UO_LEM] THEN
REWRITE_TAC [GSYM UNION_ASSOC] THEN ONCE_REWRITE_TAC [sing_UO] THEN REFL_TAC
QED

Theorem OU_UO_OU_LEM[local]:
  !cmp:'a toto l x r. OU cmp l (UO cmp {x} r) = UO cmp (OU cmp l {x}) r
Proof
SRW_TAC [] [OU, UO, EXTENSION, IN_UNION] THEN
EQ_TAC THEN REPEAT STRIP_TAC THEN AR THEN
METIS_TAC [totoLLtrans]
QED

Definition LESS_ALL:  LESS_ALL (cmp:'a toto) (x:'a) (s:'a set) =
                      !y. y IN s ==> (apto cmp x y = LESS)
End

Theorem IN_OU[local]:
  !cmp:'a toto x:'a u:'a set v:'a set.
  x IN OU cmp u v <=> (if LESS_ALL cmp x v then x IN u else x IN v)
Proof
RW_TAC bool_ss [OU, LESS_ALL, IN_UNION] THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN AR THEN
Q.SUBGOAL_THEN `x NOTIN v` (REWRITE_TAC o ulist) THEN
DISCH_TAC THEN RES_THEN MP_TAC THEN REWRITE_TAC [toto_refl, all_cpn_distinct]
QED

Theorem OU_SUBSET_UNION[local]:
  !cmp:'a toto u:'a set v:'a set. OU cmp u v SUBSET u UNION v
Proof
REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET_DEF, IN_OU, IN_UNION] THEN
METIS_TAC []
QED

Theorem LESS_ALL_UNION[local]:
  !cmp:'a toto x:'a u:'a set v:'a set.
   LESS_ALL cmp x (u UNION v) = LESS_ALL cmp x u /\ LESS_ALL cmp x v
Proof
RW_TAC bool_ss [LESS_ALL, IN_UNION] THEN METIS_TAC []
QED

Theorem NOT_IN_OU_LEM[local]:
  !cmp:'a toto x:'a u:'a set v:'a set.
 x IN u UNION v ==> x NOTIN OU cmp u v ==> ?y. y IN v /\ apto cmp x y <> LESS
Proof
RW_TAC bool_ss [IN_UNION, IN_OU, LESS_ALL] THENL
[RES_THEN MP_TAC THEN REWRITE_TAC [toto_refl, all_cpn_distinct]
,METIS_TAC []]
QED

Theorem cpn_NOT_LESS[local]:
  !c:cpn. c <> LESS ==> (c = GREATER) \/ (c = EQUAL)
Proof
METIS_TAC [cpn_nchotomy]
QED

Theorem LESS_ALL_OU:
  !cmp:'a toto x:'a u:'a set v:'a set.
   LESS_ALL cmp x (OU cmp u v) = LESS_ALL cmp x u /\ LESS_ALL cmp x v
Proof
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
]
QED

Theorem OU_ASSOC:
  !cmp a b c:'a set. OU cmp a (OU cmp b c) = OU cmp (OU cmp a b) c
Proof
RW_TAC bool_ss [IN_OU, EXTENSION, IN_UNION] THEN
REWRITE_TAC [LESS_ALL_OU] THEN METIS_TAC []
QED

Definition bl_to_set:
 (bl_to_set (cmp:'a toto) (nbl:'a bl) = {}) /\
 (bl_to_set cmp (zerbl b) = bl_to_set cmp b) /\
 (bl_to_set cmp (onebl x t b) =
  OU cmp ({x} UNION {y | y IN ENUMERAL cmp t /\ (apto cmp x y = LESS)})
         (bl_to_set cmp  b))
End

Theorem bl_to_set_OU_UO[local]:
  !cmp:'a toto x t b. bl_to_set cmp (onebl x t b) =
                      OU cmp (UO cmp {x} (ENUMERAL cmp t)) (bl_to_set cmp b)
Proof
REWRITE_TAC [bl_to_set, sing_UO]
QED

Theorem bl_rev_set_lem[local]:
   !cmp:'a toto b t.
 ENUMERAL cmp (bl_rev t b) = OU cmp (ENUMERAL cmp t) (bl_to_set cmp b)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bl_rev, bl_to_set_OU_UO] THEN
REWRITE_TAC [bl_to_set, OU_EMPTY] THEN
REWRITE_TAC [bt_to_set_OU_UO, OU_ASSOC]
QED

(* Converting a bl to a bt preserves the represented set: *)

Theorem bl_to_bt_set[local]:
  !cmp:'a toto b. ENUMERAL cmp (bl_to_bt b) = bl_to_set cmp b
Proof
REWRITE_TAC [bl_to_bt, bl_rev_set_lem, bt_to_set, EMPTY_OU]
QED

(* Now to show that building a bl from a list does the same. *)

(* We aim to show that LESS_ALL cmp a (bl_to_set cmp b) ==>
                (bl_to_set cmp (BL_CONS a bl) = a INSERT bl_to_set cmp b). *)

(* Generalizing for the recursion in BL_ACCUM, we hope to show that
  LESS_ALL cmp a (ENUMERAL cmp t) /\ LESS_ALL cmp a (bl_to_set b) ==>
  (bl_to_set cmp (BL_ACCUM a t b) =
      a INSERT (OU cmp (ENUMERAL cmp t) (bl_to_set cmp b))) . *)

Theorem LESS_ALL_UO_LEM:
  !cmp:'a toto a s. LESS_ALL cmp a s ==> (UO cmp {a} s = a INSERT s)
Proof
SRW_TAC [] [LESS_ALL, UO, EXTENSION, IN_UNION] THEN METIS_TAC []
QED

Theorem LESS_ALL_OU_UO_LEM:
  !cmp:'a toto a s t. LESS_ALL cmp a s /\ LESS_ALL cmp a t ==>
                      (OU cmp (UO cmp {a} s) t = a INSERT (OU cmp s t))
Proof
REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC LESS_ALL_UO_LEM THEN
SRW_TAC [] [UO, OU, EXTENSION, IN_UNION] THEN
METIS_TAC [LESS_ALL]
QED

Theorem BL_ACCUM_set[local]:
  !cmp:'a toto a b t.
 LESS_ALL cmp a (ENUMERAL cmp t) /\ LESS_ALL cmp a (bl_to_set cmp b) ==>
    (bl_to_set cmp (BL_ACCUM a t b) =
      a INSERT (OU cmp (ENUMERAL cmp t) (bl_to_set cmp b)))
Proof
GEN_TAC THEN GEN_TAC THEN Induct THEN
SRW_TAC [] [BL_ACCUM, bl_to_set_OU_UO, bt_to_set_OU_UO] THENL
[METIS_TAC [LESS_ALL_UO_LEM, LESS_ALL_OU_UO_LEM, bl_to_set]
,METIS_TAC [LESS_ALL_UO_LEM, LESS_ALL_OU_UO_LEM, bl_to_set]
,REWRITE_TAC [bl_to_set] THEN
`LESS_ALL cmp a (UO cmp {a'} (ENUMERAL cmp b0)) /\
 LESS_ALL cmp a (bl_to_set cmp b)` by ASM_REWRITE_TAC [GSYM LESS_ALL_OU] THEN
`LESS_ALL cmp a (ENUMERAL cmp (node t a' b0))`
 by ASM_REWRITE_TAC [bt_to_set_OU_UO, LESS_ALL_OU] THEN
 RES_TAC THEN ASM_REWRITE_TAC [bt_to_set_OU_UO, OU_ASSOC]
]
QED

Theorem BL_CONS_set[local]:
  !cmp:'a toto a b. LESS_ALL cmp a (bl_to_set cmp b) ==>
        (bl_to_set cmp (BL_CONS a b) = a INSERT bl_to_set cmp b)
Proof
REPEAT STRIP_TAC THEN REWRITE_TAC [BL_CONS] THEN
Q.SUBGOAL_THEN `OU cmp (ENUMERAL cmp nt) (bl_to_set cmp b) = bl_to_set cmp b`
(SUBST1_TAC o SYM)
THEN1 REWRITE_TAC [bt_to_set, EMPTY_OU] THEN
`LESS_ALL cmp a (ENUMERAL cmp nt)`
 by REWRITE_TAC [LESS_ALL, NOT_IN_EMPTY, bt_to_set] THEN
IMP_RES_TAC BL_ACCUM_set
QED

Theorem list_to_bl_set[local]:
  !cmp:'a toto l. OL cmp l ==> (bl_to_set cmp (list_to_bl l) = set l)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [bl_to_set, list_to_bl, LIST_TO_SET_THM, OL] THEN
RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC BL_CONS_set THEN
RES_THEN SUBST1_TAC THEN RW_TAC bool_ss [LESS_ALL]
QED

Theorem bt_to_ol_ID[local]:
  !cmp:'a toto. !l::OL cmp. bt_to_ol cmp (list_to_bt l) = l
Proof
GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN
REWRITE_TAC [SPECIFICATION] THEN GEN_TAC THEN DISCH_TAC THEN
Q.SUBGOAL_THEN `OL cmp (bt_to_ol cmp (list_to_bt l)) /\ OL cmp l`
(REWRITE_TAC o ulist o GSYM o MATCH_MP OL_set_EQ)
THEN1 ASM_REWRITE_TAC [OL_bt_to_ol] THEN
IMP_RES_THEN (SUBST1_TAC o SYM) list_to_bl_set THEN
REWRITE_TAC [GSYM bl_to_bt_set, list_to_bt, ol_set]
QED

Theorem bt_to_ol_ID_IMP = REWRITE_RULE [SPECIFICATION]
                     (CONV_RULE (ONCE_DEPTH_CONV RES_FORALL_CONV) bt_to_ol_ID);

(* bt_to_ol_ID_IMP: |- !cmp l. OL cmp l ==> (bt_to_ol cmp (list_to_bt l) = l) *)

Theorem list_to_bt_ID[local]:
    !cmp:'a toto t:'a bt.
          ENUMERAL cmp (list_to_bt (bt_to_ol cmp t)) = ENUMERAL cmp t
Proof
METIS_TAC [bt_to_ol_ID_IMP, ol_set, OL_bt_to_ol]
QED

(* Set operations. We already have smerge_set and smerge_OL. *)
(* "OL_UNION" possibly not the best name. *)

Theorem OL_UNION[local]:
  !cmp:'a toto. !l m::OL cmp. OL cmp (smerge cmp l m) /\
                      (set (smerge cmp l m) = set l UNION set m)
Proof
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
SRW_TAC [] [SPECIFICATION, smerge_set, smerge_OL]
QED

Theorem OL_UNION_IMP = REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_UNION);

(* OL_UNION_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (smerge cmp l m) /\ (set (smerge cmp l m) = set l UNION set m) *)

Theorem ENUMERAL_UNION[local]:
  !cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (smerge cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s UNION ENUMERAL cmp t
Proof
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (smerge cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC smerge_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
REWRITE_TAC [smerge_set]
QED

(* **************** Similar treatment of intersection: ************* *)

Definition sinter:
 (sinter (cmp:'a toto) [] [] = []) /\
 (sinter cmp (x:'a :: l) [] = []) /\
 (sinter cmp [] (y:'a :: m) = []) /\
 (sinter cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => sinter cmp l (y :: m)
                                 | EQUAL => x :: (sinter cmp l m)
                                 | GREATER => sinter cmp (x :: l) m)
End

val sinter_ind = theorem "sinter_ind";

Theorem sinter_nil[local]:
  !cmp:'a toto l. (sinter cmp l [] = []) /\ (sinter cmp [] l = [])
Proof
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [sinter]
QED

Theorem sinter_subset_inter[local]:
  !cmp:'a toto l m x. MEM x (sinter cmp l m) ==> MEM x l /\ MEM x m
Proof
HO_MATCH_MP_TAC sinter_ind THEN
RW_TAC (srw_ss()) [sinter, MEM] THEN POP_ASSUM MP_TAC THEN
Cases_on `apto cmp x y` THEN SRW_TAC [] [] THEN RES_TAC THEN AR THEN
DISJ1_TAC THEN IMP_RES_TAC toto_equal_eq
QED

Theorem sinter_OL[local]:
  !cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (sinter cmp l m)
Proof
HO_MATCH_MP_TAC sinter_ind THEN
RW_TAC (srw_ss()) [sinter, sinter_nil, OL] THEN
Cases_on `apto cmp x y` THEN SRW_TAC [] [OL] THEN
IMP_RES_TAC sinter_subset_inter THEN RES_TAC
QED

Theorem inter_subset_sinter[local]:
  !cmp:'a toto x l. OL cmp l /\ MEM x l ==>
     !m. OL cmp m /\ MEM x m ==> MEM x (sinter cmp l m)
Proof
GEN_TAC THEN GEN_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
GEN_TAC THEN STRIP_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
RW_TAC (srw_ss()) [sinter] THENL
[SRW_TAC [] [toto_refl, MEM]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 SRW_TAC [] [sinter, MEM] THENL
 [IMP_RES_TAC OL THEN IMP_RES_TAC totoLLtrans THEN
  IMP_RES_TAC toto_not_less_refl
 ,IMP_RES_TAC OL THEN RES_TAC
 ]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 SRW_TAC [] [sinter, MEM] THENL
 [`OL cmp l` by IMP_RES_TAC OL THEN RES_TAC THEN
  `MEM h' (h' :: m)` by REWRITE_TAC [MEM] THEN RES_TAC
 ,IMP_RES_TAC toto_equal_eq THEN AR
 ,`apto cmp h h' = LESS` by IMP_RES_TAC OL THEN
  IMP_RES_TAC totoLGtrans THEN IMP_RES_TAC toto_not_less_refl
 ]
,Cases_on `apto cmp h h'` THEN RES_TAC THEN
 SRW_TAC [] [sinter, MEM] THENL
 [`MEM x (h' :: m)` by ASM_REWRITE_TAC [MEM] THEN IMP_RES_TAC OL THEN RES_TAC
 ,DISJ2_TAC THEN IMP_RES_TAC OL THEN RES_TAC
 ,IMP_RES_TAC OL THEN RES_TAC
]]
QED

(* Note that sinter_set, unlike smerge_set, depends on sorted input lists. *)

Theorem sinter_set[local]:
    !cmp:'a toto l m.
 OL cmp l /\ OL cmp m ==> (set (sinter cmp l m) = set l INTER set m)
Proof
SRW_TAC [] [IN_INTER, EXTENSION] THEN EQ_TAC THENL
[MATCH_ACCEPT_TAC sinter_subset_inter
,METIS_TAC [inter_subset_sinter]
]
QED

Theorem OL_INTER[local]:
  !cmp:'a toto. !l m::OL cmp. OL cmp (sinter cmp l m) /\
                      (set (sinter cmp l m) = set l INTER set m)
Proof
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
SRW_TAC [] [SPECIFICATION, sinter_set, sinter_OL]
QED

Theorem OL_INTER_IMP = REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_INTER);

(* OL_INTER_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (sinter cmp l m) /\ (set (sinter cmp l m) = set l INTER set m) *)

Theorem ENUMERAL_INTER[local]:
  !cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (sinter cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s INTER ENUMERAL cmp t
Proof
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (sinter cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC sinter_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
MATCH_MP_TAC sinter_set THEN AR
QED

(* **************** Similar treatment of set difference: ************* *)

Definition sdiff:
 (sdiff (cmp:'a toto) [] [] = []) /\
 (sdiff cmp (x:'a :: l) [] = (x::l)) /\
 (sdiff cmp [] (y:'a :: m) = []) /\
 (sdiff cmp (x :: l) (y :: m) = case apto cmp x y of
                                   LESS => x :: sdiff cmp l (y :: m)
                                 | EQUAL => sdiff cmp l m
                                 | GREATER => sdiff cmp (x :: l) m)
End

val sdiff_ind = theorem "sdiff_ind";

Theorem sdiff_nil[local]:
  !cmp:'a toto l. (sdiff cmp l [] = l) /\ (sdiff cmp [] l = [])
Proof
REPEAT STRIP_TAC THEN Cases_on `l` THEN REWRITE_TAC [sdiff]
QED

Theorem diff_subset_sdiff[local]:
  !cmp:'a toto l m x. MEM x l /\ ~MEM x m ==> MEM x (sdiff cmp l m)
Proof
HO_MATCH_MP_TAC sdiff_ind THEN
RW_TAC (srw_ss()) [sdiff, MEM] THEN POP_ASSUM MP_TAC THEN
Cases_on `apto cmp x y` THEN SRW_TAC [] [] THEN RES_TAC THEN AR THEN
IMP_RES_TAC toto_equal_eq
QED

Theorem OL_NOT_MEM[local]:
  !cmp:'a toto x l. OL cmp (x::l) ==> ~MEM x l
Proof
REPEAT GEN_TAC THEN REWRITE_TAC [OL] THEN STRIP_TAC THEN
DISCH_TAC THEN RES_THEN MP_TAC THEN
REWRITE_TAC [toto_refl, all_cpn_distinct]
QED

Theorem sdiff_subset_diff[local]:
  !cmp:'a toto x l m. OL cmp l /\ OL cmp m ==>
                      MEM x (sdiff cmp l m) ==> MEM x l /\ ~MEM x m
Proof
GEN_TAC THEN GEN_TAC THEN Induct THEN REWRITE_TAC [MEM, sdiff_nil] THEN
GEN_TAC THEN Induct THEN REWRITE_TAC [MEM] THEN
RW_TAC (srw_ss()) [sdiff] THEN POP_ASSUM MP_TAC THEN
`OL cmp m` by IMP_RES_TAC OL THEN `OL cmp l` by IMP_RES_TAC OL THENL
[Cases_on `apto cmp h h'` THEN
 SRW_TAC [] [sdiff, MEM] THEN DISJ2_TAC THEN RES_TAC
,Cases_on `apto cmp h h'` THEN
 SRW_TAC [] [sdiff, MEM] THENL
 [IMP_RES_TAC toto_glneq
 ,METIS_TAC [MEM]
 ,IMP_RES_TAC toto_equal_eq THEN METIS_TAC [OL_NOT_MEM]
 ,`(x = h) \/ MEM x l` by METIS_TAC [] THEN IMP_RES_TAC toto_antisym THENL
  [AR THEN IMP_RES_TAC toto_glneq
  ,METIS_TAC [OL, totoLLtrans, toto_glneq]
 ]]
,Cases_on `apto cmp h h'` THEN
 SRW_TAC [] [sdiff, MEM] THENL
 [METIS_TAC [OL, totoLLtrans, toto_glneq]
 ,METIS_TAC [MEM]
]]
QED

Theorem sdiff_OL[local]:
  !cmp:'a toto l m. OL cmp l /\ OL cmp m ==> OL cmp (sdiff cmp l m)
Proof
GEN_TAC THEN Induct THEN1 REWRITE_TAC [sdiff_nil, OL] THEN GEN_TAC THEN
Induct THEN1 (REWRITE_TAC [sdiff_nil] THEN tautLib.TAUT_TAC) THEN
SRW_TAC [] [sdiff] THEN REWRITE_TAC [OL] THEN
IMP_RES_TAC OL THEN
Cases_on `apto cmp h h'` THEN SRW_TAC [] [OL] THEN
IMP_RES_TAC sdiff_subset_diff THEN RES_TAC
QED

(* Note that sdiff_set, like sinter_set, depends on sorted input lists. *)

Theorem sdiff_set[local]:
    !cmp:'a toto l m.
 OL cmp l /\ OL cmp m ==> (set (sdiff cmp l m) = set l DIFF set m)
Proof
SRW_TAC [] [IN_DIFF, EXTENSION] THEN EQ_TAC THENL
[METIS_TAC [sdiff_subset_diff]
,MATCH_ACCEPT_TAC diff_subset_sdiff
]
QED

Theorem OL_DIFF[local]:
  !cmp:'a toto. !l m::OL cmp. OL cmp (sdiff cmp l m) /\
                      (set (sdiff cmp l m) = set l DIFF set m)
Proof
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
SRW_TAC [] [SPECIFICATION, sdiff_set, sdiff_OL]
QED

Theorem OL_DIFF_IMP = REWRITE_RULE [SPECIFICATION]
                             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) OL_DIFF);

(* OL_DIFF_IMP = |- !cmp l. OL cmp l ==> !m. OL cmp m ==>
       OL cmp (sdiff cmp l m) /\ (set (sdiff cmp l m) = set l DIFF set m) *)

Theorem ENUMERAL_DIFF[local]:
  !cmp:'a toto s t:'a bt.
 ENUMERAL cmp (list_to_bt (sdiff cmp (bt_to_ol cmp s) (bt_to_ol cmp t))) =
 ENUMERAL cmp s DIFF ENUMERAL cmp t
Proof
RW_TAC bool_ss [ol_set] THEN
`OL cmp (bt_to_ol cmp s) /\ OL cmp (bt_to_ol cmp t)`
 by REWRITE_TAC [OL_bt_to_ol] THEN
`OL cmp (sdiff cmp (bt_to_ol cmp s) (bt_to_ol cmp t))`
 by IMP_RES_TAC sdiff_OL THEN
IMP_RES_THEN SUBST1_TAC bt_to_ol_ID_IMP THEN
MATCH_MP_TAC sdiff_set THEN AR
QED

(* ********************************************************************* *)
(*                  Theorems to assist conversions                       *)
(* ********************************************************************* *)

Theorem ENUMERAL_set:
  !cmp l:'a list. set l = ENUMERAL cmp (list_to_bt (incr_ssort cmp l))
Proof
REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV (REWR_CONV (GSYM incr_ssort_set))) THEN
Q.SUBGOAL_THEN
`incr_ssort cmp l = bt_to_ol cmp (list_to_bt (incr_ssort cmp l))`
SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_ol_ID_IMP) THEN MATCH_ACCEPT_TAC incr_ssort_OL
,REWRITE_TAC [list_to_bt_ID, ol_set]
]
QED

Theorem OL_ENUMERAL:
  !cmp l:'a list. OL cmp l ==> (set l = ENUMERAL cmp (list_to_bt l))
Proof
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN
`l = bt_to_ol cmp (list_to_bt l)` SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_ol_ID_IMP) THEN AR
,REWRITE_TAC [list_to_bt_ID, ol_set]
]
QED

Theorem bt_to_ol_thm[local]:
  !cmp:'a toto t. bt_to_ol cmp t = bt_to_ol_ac cmp t []
Proof
SRW_TAC [] [ol_ac_thm]
QED

Theorem OWL_UNION_THM:   !cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s UNION t) (smerge cmp l m)
Proof
METIS_TAC [OWL, OL_UNION_IMP]
QED

Theorem OWL_INTER_THM:   !cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s INTER t) (sinter cmp l m)
Proof
METIS_TAC [OWL, OL_INTER_IMP]
QED

Theorem OWL_DIFF_THM:   !cmp:'a toto s l t m.
    OWL cmp s l /\ OWL cmp t m ==> OWL cmp (s DIFF t) (sdiff cmp l m)
Proof
METIS_TAC [OWL, OL_DIFF_IMP]
QED

(* ******************************************************************* *)
(*  Test for a bt with no spurious nodes, as should be invariably the  *)
(*  case, and justify quicker bt_to_ol for bt's passing the test,      *)
(*  makes exactly n - 1 comparisons in passing a tree with n nodes.    *)
(* ******************************************************************* *)

Definition OL_bt_lb_ub:
 (OL_bt_lb_ub cmp lb (nt:'a bt) ub = (apto cmp lb ub = LESS)) /\
 (OL_bt_lb_ub cmp lb (node l x r) ub = OL_bt_lb_ub cmp lb l x /\
                                       OL_bt_lb_ub cmp x r ub)
End

Definition OL_bt_lb:
 (OL_bt_lb cmp lb (nt:'a bt) = T) /\
 (OL_bt_lb cmp lb (node l x r) = OL_bt_lb_ub cmp lb l x /\
                                 OL_bt_lb cmp x r)
End

Definition OL_bt_ub:
 (OL_bt_ub cmp (nt:'a bt) ub = T) /\
 (OL_bt_ub cmp (node l x r) ub = OL_bt_ub cmp l x /\
                                 OL_bt_lb_ub cmp x r ub)
End

Definition OL_bt:
 (OL_bt cmp (nt:'a bt) = T) /\
 (OL_bt cmp (node l x r) = OL_bt_ub cmp l x /\ OL_bt_lb cmp x r)
End

Theorem OL_bt_lb_ub_lem[local]:
  !cmp t lb ub. OL_bt_lb_ub cmp lb t ub ==> (apto cmp lb ub = LESS)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [OL_bt_lb_ub] THEN METIS_TAC [ totoLLtrans]
QED

Theorem OL_bt_lb_ub_thm[local]:
  !cmp t:'a bt lb ub. OL_bt_lb_ub cmp lb t ub ==>
                      (bt_to_ol_lb_ub cmp lb t ub = bt_to_list t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [OL_bt_lb_ub, bt_to_ol_lb_ub, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]
QED

Theorem OL_bt_lb_thm[local]:
  !cmp t:'a bt lb. OL_bt_lb cmp lb t ==>
                   (bt_to_ol_lb cmp lb t = bt_to_list t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [OL_bt_lb, bt_to_ol_lb, OL_bt_lb_ub_thm, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]
QED

Theorem OL_bt_ub_thm[local]:
  !cmp t:'a bt ub. OL_bt_ub cmp t ub ==>
                   (bt_to_ol_ub cmp t ub = bt_to_list t)
Proof
GEN_TAC THEN Induct THEN
SRW_TAC [] [OL_bt_ub, bt_to_ol_ub, OL_bt_lb_ub_thm, bt_to_list] THEN
METIS_TAC [OL_bt_lb_ub_lem]
QED

Theorem OL_bt_thm[local]:
  !cmp t:'a bt. OL_bt cmp t ==> (bt_to_ol cmp t = bt_to_list t)
Proof
GEN_TAC THEN Cases THEN
SRW_TAC [] [OL_bt, bt_to_ol, OL_bt_lb_thm, OL_bt_ub_thm, bt_to_list]
QED

Theorem better_bt_to_ol:
  !cmp t:'a bt. bt_to_ol cmp t = if OL_bt cmp t then bt_to_list_ac t []
                                                else bt_to_ol_ac cmp t []
Proof
METIS_TAC [OL_bt_thm, bt_to_list_thm, bt_to_ol_thm]
QED

(* ******************* Theorem to support set_TO_OWL ********************* *)

Theorem set_OWL_thm:
  !cmp l:'a list. OWL cmp (set l) (incr_ssort cmp l)
Proof
REWRITE_TAC [OWL, incr_ssort_set, incr_ssort_OL]
QED
