(* file HS/PIN/fmapalScript.sml, created 6/2/13 F.L. Morris *)
(* tree-based finite function representation; name a homage to numeralTheory *)
(* Uses bt, bl basics from enumeralScript, puts 'a#'b in place of 'a. *)

structure fmapalScript = struct

open HolKernel boolLib Parse;

(* app load ["totoTheory", "totoTacs", "res_quanLib", "enumeralTheory",
          "finite_mapTheory", "combinTheory"]; *)
(* comment out above load when Holmaking *)
val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory res_quanTheory res_quanLib;
open pairTheory PairRules optionTheory finite_mapTheory;
open totoTheory totoTacs bossLib listTheory enumeralTheory;

val _ = new_theory "fmapal";

(* "fmapal" for "numeral-ish finite map", wordplay on "NUMERAL", "enumeral". *)
(* Temptation to call it "funeralTheory" reluctantly resisted. *)

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];
fun rrs th = REWRITE_RULE [SPECIFICATION] th;
val _ = intLib.deprecate_int (); (* because intLib gets loaded now (9/13) *)

(* ****** Make FUNION infix. ********* *)

val _ = set_fixity "FUNION" (Infixl 500);

val _ = Defn.def_suffix := ""; (* replacing default "_def" *)

(* ***************************************************************** *)
(* Following switch, BigSig, allows "maybe_thm" to act either as     *)
(* store_thm or as prove, thus maximizing or minimizing the output   *)
(* from print_theory and the stuff known to DB.match, DB.find        *)
(* ***************************************************************** *)

val BigSig = false;

fun maybe_thm (s, tm, tac) = if BigSig then store_thm (s, tm, tac)
                                       else prove (tm, tac);

val ORL = Define`(ORL (cmp:'a toto) ([]:('a#'b)list) = T) /\
                 (ORL cmp ((a,b) :: l) = ORL cmp l /\
                   (!p q. MEM (p,q) l ==> (apto cmp a p = LESS)))`;

val ORL_LEM = maybe_thm ("ORL_LEM", Term
`!cmp l:('a#'b)list m. ORL cmp (l ++ m) ==> ORL cmp l /\ ORL cmp m`,
GEN_TAC THEN Induct THEN REWRITE_TAC [APPEND, ORL] THEN
P_PGEN_TAC (Term`x:'a,y:'b`) THEN ASM_REWRITE_TAC [ORL] THEN
REWRITE_TAC [MEM_APPEND] THEN REPEAT STRIP_TAC THEN RES_TAC THEN AR);

val MEM_FST = maybe_thm ("MEM_FST",
``!x l:('a#'b)list. (?y. MEM (x,y) l) <=> MEM x (MAP FST l)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [MEM, MAP]
,P_PGEN_TAC ``a:'a, b:'b`` THEN RW_TAC (srw_ss ()) [MAP,MEM] THEN
 METIS_TAC [MEM]
]);

val ORL_OL_FST = maybe_thm ("ORL_OL_FST",
``!cmp:'a toto l:('a#'b) list. ORL cmp l <=> OL cmp (MAP FST l)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [ORL, OL, MAP]
,P_PGEN_TAC ``a:'a, b:'b`` THEN RW_TAC (srw_ss ()) [MAP, ORL, OL] THEN
 CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV FORALL_IMP_CONV)) THEN
 REWRITE_TAC [MEM_FST]
]);

(* A useful way of combining option values, that I don't find premade: *)

val optry = Define`(optry (SOME p) (q:'z option) = SOME p)
                /\ (optry NONE q = q)`;

val optry_case = maybe_thm ("optry_case", Term
`!p q:'z option. optry p q = case p of SOME x => SOME x | NONE => q`,
REPEAT GEN_TAC THEN Cases_on `p` THEN REWRITE_TAC [optry, option_CLAUSES] THEN
BETA_TAC THEN REFL_TAC);

val optry_ASSOC = maybe_thm ("optry_ASSOC", Term
`!p q r:'z option. optry p (optry q r) = optry (optry p q) r`,
REPEAT GEN_TAC THEN
Cases_on `p` THEN REWRITE_TAC [option_case_def, optry]);

val optry_ID = maybe_thm ("optry_ID", Term
`(!p:'z option. optry p NONE = p) /\ (!p:'z option. optry NONE p = p)`,
REWRITE_TAC [optry] THEN Cases THEN REWRITE_TAC [optry]);

val IS_SOME_optry = maybe_thm ("IS_SOME_optry",
``!a b:'a option. IS_SOME a ==> (optry a b = a)``,
REPEAT GEN_TAC THEN Cases_on `a` THEN
ASM_REWRITE_TAC [optry, option_CLAUSES]);

val optry_list = Define
  `(optry_list (f:'z->'g option) ([]:'z option list) = NONE)
/\ (optry_list f ((NONE:'z option) :: l) = optry_list f l)
/\ (optry_list f (SOME (z:'z) :: l) = optry (f z) (optry_list f l))`;

(* We define the following function, assocv, to give the option-valued
function embodied by an association list. The name is chosen both to
avoid confusion with the usual contraction for "associative" and to
indicate departure from the Lisp-ML tradition of assoc's that return
the argument-value pair; "v" is for "value [only]". *)

val assocv = Define`(assocv ([]:('a#'b)list) (a:'a) = NONE)
                 /\ (assocv ((x:'a, y:'b) :: l) a =
                      if a = x then SOME y else assocv l a)`;

(* But for more convenient partial application below at incr_merge_lem: *)

val vcossa = Define`vcossa a (l:('a#'b)list) = assocv l a`;

(* Define an update-like binary operation on option valued functions: *)

val OPTION_UPDATE = Define
`OPTION_UPDATE (f:'a->'b option) g x = optry (f x) (g x)`;

val IS_SOME_OPTION_UPDATE = prove (
``!u (v:'a -> 'b option). IS_SOME o OPTION_UPDATE u v =
                          IS_SOME o u UNION IS_SOME o v``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
REWRITE_TAC [rrs IN_UNION, combinTheory.o_THM, OPTION_UPDATE, optry_case] THEN
Cases_on `u x` THEN REWRITE_TAC [option_CLAUSES] THEN
BETA_TAC THEN REWRITE_TAC [option_CLAUSES]);

(* ***************************************************************** *)
(*  merge sorting for functions (as association lists here. We call  *)
(*  the basic list-combining function, which gives priority to the   *)
(*  first argument, just "merge". This corresponds to FUNION in fmap,*)
(*  not to FMERGE. Corresponding set functions use "smerge", etc.    *)
(* ***************************************************************** *)

val merge = Define`(merge (cmp:'a toto) [] (l:('a#'b)list) = l)
                 /\ (merge (cmp:'a toto) l [] = l)
                 /\ (merge (cmp:'a toto) ((a1, b1) :: l1) ((a2, b2) :: l2) =
                    case apto cmp a1 a2 of
                    LESS => (a1, b1) :: merge cmp l1 ((a2, b2) :: l2)
                 | EQUAL => (a1, b1:'b) :: merge cmp l1 l2
               | GREATER => (a2, b2) :: merge cmp ((a1, b1) :: l1) l2)`;

val merge_ind = theorem "merge_ind";

(* merge_ind = |- !P.
     (!cmp. P cmp [] []) /\ (!cmp v8 v9. P cmp [] (v8::v9)) /\
     (!cmp v12 v13 v5. P cmp ((v12,v13)::v5) []) /\
     (!cmp a1 b1 l1 a2 b2 l2.
        ((apto cmp a1 a2 = EQUAL) ==> P cmp l1 l2) /\
        ((apto cmp a1 a2 = GREATER) ==> P cmp ((a1,b1)::l1) l2) /\
        ((apto cmp a1 a2 = LESS) ==> P cmp l1 ((a2,b2)::l2)) ==>
        P cmp ((a1,b1)::l1) ((a2,b2)::l2)) ==>
     !v v1 v2. P v v1 v2 *)

val merge_thm = maybe_thm ("merge_thm", Term
`!cmp:'a toto. (!m:('a#'b)list. merge cmp [] m = m)
            /\ (!l:('a#'b)list. merge cmp l [] = l)
            /\ (!a1:'a b1:'b a2:'a b2:'b l1 l2.
                merge cmp ((a1, b1) :: l1) ((a2, b2) :: l2) =
                    case apto cmp a1 a2 of
                     LESS => (a1, b1) :: merge cmp l1 ((a2, b2) :: l2)
                 | EQUAL => (a1, b1:'b) :: merge cmp l1 l2
               | GREATER => (a2, b2) :: merge cmp ((a1, b1) :: l1) l2)`,
GEN_TAC THEN REWRITE_TAC [merge] THEN CONJ_TAC THENL
[Cases_on `m:('a#'b)list` THEN REWRITE_TAC [merge]
,Cases_on `l:('a#'b)list` THENL
 [REWRITE_TAC [merge]
 ,PURE_ONCE_REWRITE_TAC [GSYM PAIR] THEN REWRITE_TAC [merge]]]);

(* If we are to use incr_sort, we doubtless will need to prove that its
ouput is sorted and contains the pairs that assocv would find from its
argument. *)

(* Possibly better imitate enumeral more: _ORL thms might come from
   lemmas like MAP FST (merge cmp l m) = smerge cmp (MAP FST l) (MAP FST m),
   and corresponding to _set thms might be _assocv thms, or direct to fmaps.*)

val merge_FST_smerge = maybe_thm ("merge_FST_smerge",
``!cmp:'a toto l m:('a#'b)list.
         MAP FST (merge cmp l m) = smerge cmp (MAP FST l) (MAP FST m)``,
GEN_TAC THEN Induct THENL
[REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [merge_thm, smerge_nil, MAP]
,P_PGEN_TAC (Term`(a:'a,b:'b)`) THEN Induct THENL
 [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [merge_thm, smerge_nil, MAP]
 ,P_PGEN_TAC (Term`(a':'a,b':'b)`) THEN
  RW_TAC (srw_ss ()) [merge_thm, smerge, MAP, FST] THEN
  Cases_on `apto cmp a a'` THEN
  RW_TAC (srw_ss ()) []
]]);

val merge_ORL = maybe_thm ("merge_ORL", ``!cmp:'a toto l m:('a#'b)list.
         ORL cmp l /\ ORL cmp m ==> ORL cmp (merge cmp l m)``,
METIS_TAC [smerge_OL, merge_FST_smerge, ORL_OL_FST]);

(* **** We need to show that assocv is preserved by sorting **** *)

val merge_subset_union = maybe_thm ("merge_subset_union",
``!cmp:'a toto l m:('a#'b)list h.
              MEM h (merge cmp l m) ==> MEM h l \/ MEM h m``,
HO_MATCH_MP_TAC merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
[REWRITE_TAC [MEM, merge]
,REWRITE_TAC [MEM, merge]
,REWRITE_TAC [MEM, merge]
,CONV_TAC (RAND_CONV (REWRITE_CONV [merge])) THEN
 Cases_on `apto cmp a1 a2` THEN
 REWRITE_TAC [all_cpn_distinct] THEN
 STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC [cpn_case_def] THEN
 CONV_TAC (LAND_CONV (REWRITE_CONV [MEM])) THEN
 STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [MEM]]);

val MEM_MEM_merge = maybe_thm ("MEM_MEM_merge",
``!cmp:'a toto l m:('a#'b)list x y.
     MEM (x,y) l ==> MEM (x,y) (merge cmp l m)``,
HO_MATCH_MP_TAC merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MEM, merge] THEN
Cases_on `apto cmp a1 a2` THEN
REWRITE_TAC [all_cpn_distinct] THEN
REPEAT STRIP_TAC THEN REWRITE_TAC [cpn_case_def, MEM] THEN RES_TAC THEN AR);

val NOT_MEM_merge = maybe_thm ("NOT_MEM_merge",
``!cmp:'a toto l m:('a#'b)list x y. (!z.~MEM (x,z) l) ==>
   (MEM (x,y) (merge cmp l m) <=> MEM (x,y) m)``,
HO_MATCH_MP_TAC merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MEM, merge] THENL
[DISCH_TAC THEN AR
,REWRITE_TAC [DE_MORGAN_THM] THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV) THEN
 Cases_on `apto cmp a1 a2` THEN
 REWRITE_TAC [cpn_distinct, GSYM cpn_distinct] THEN
 REPEAT STRIP_TAC THEN
 REWRITE_TAC [cpn_case_def, MEM] THENL
 [RES_TAC THEN AR
 ,IMP_RES_THEN (REWRITE_TAC o ulist o SYM) toto_equal_imp_eq THEN
  RES_TAC THEN UNDISCH_TAC (Term`!z. (x:'a,z:'b) <> (a1,b1)`) THEN
  ASM_REWRITE_TAC [PAIR_EQ, DE_MORGAN_THM] THEN
  CONV_TAC (LAND_CONV (FORALL_OR_CONV THENC (RAND_CONV FORALL_NOT_CONV))) THEN
  SUBGOAL_THEN (Term`?z:'b.z=b1`) (REWRITE_TAC o ulist) THENL
  [EXISTS_TAC (Term`b1:'b`) THEN REFL_TAC
  ,DISCH_TAC THEN AR
  ]
 ,RES_TAC THEN AR
]]);

(* By good fortune, the previous three lemmas about merge (including
   merge_subset_union) did not care if the lists were sorted or not. *)

(* ****** more lemmas that do need an ORL hypothesis ****** *)

val ORL_single_valued = prove (Term`!cmp l. ORL cmp l ==>
 !x:'a y:'b z. MEM (x,y) l /\ MEM (x,z) l ==> (z = y)`,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [MEM]
,P_PGEN_TAC (Term`p:'a,q:'b`) THEN 
 DISCH_TAC THEN IMP_RES_TAC ORL THEN REPEAT GEN_TAC THEN
 Cases_on `apto cmp x p` THEN
 IMP_RES_TAC toto_glneq THEN IMP_RES_TAC toto_equal_imp_eq THEN
 ASM_REWRITE_TAC [MEM, PAIR_EQ] THEN STRIP_TAC THEN RES_TAC THENL
 [AR
 ,IMP_RES_THEN MP_TAC toto_glneq THEN REWRITE_TAC []
 ,IMP_RES_THEN MP_TAC toto_glneq THEN REWRITE_TAC []
 ]]);

val merge_MEM_thm = maybe_thm ("merge_MEM_thm",
``!cmp:'a toto l m:('a#'b)list. ORL cmp l /\ ORL cmp m ==>
 (!x y. MEM (x,y) (merge cmp l m)
 <=> MEM (x,y) l \/ MEM (x,y) m /\ !z.~MEM (x,z) l)``,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[Cases_on `!z. ~MEM (x,z) l` THENL
 [DISCH_TAC THEN IMP_RES_TAC merge_subset_union THEN AR
 ,DISCH_TAC THEN
  UNDISCH_TAC (Term`~!z. ~MEM (x:'a,z:'b) l`) THEN
  CONV_TAC (LAND_CONV NOT_FORALL_CONV) THEN REWRITE_TAC [] THEN STRIP_TAC THEN
  SUBGOAL_THEN (Term`MEM (x:'a,z:'b) (merge cmp l m)`) ASSUME_TAC THENL
  [IMP_RES_TAC MEM_MEM_merge THEN AR
  ,SUBGOAL_THEN (Term`ORL cmp (merge cmp (l:('a#'b)list) m)`)
   (MP_TAC o MATCH_MP ORL_single_valued) THENL
   [MATCH_MP_TAC merge_ORL THEN AR
   ,DISCH_THEN (fn imp =>
                SUBGOAL_THEN (Term`y:'b = z`) (ASM_REWRITE_TAC o ulist) THEN
                MATCH_MP_TAC imp) THEN
    EXISTS_TAC (Term`x:'a`) THEN AR
 ]]]
,STRIP_TAC THENL
 [IMP_RES_TAC MEM_MEM_merge THEN AR
 ,IMP_RES_TAC NOT_MEM_merge THEN AR
]]);

val ORL_TL = maybe_thm ("ORL_TL", Term
`!cmp ab:('a#'b) l. ORL cmp (ab::l) ==> ORL cmp l`,
GEN_TAC THEN P_PGEN_TAC (Term`a:'a,b:'b`) THEN
REWRITE_TAC [ORL] THEN REPEAT STRIP_TAC THEN AR);

val assocv_MEM_thm = maybe_thm ("assocv_MEM_thm",
``!cmp l. ORL cmp l ==> (!x:'a y:'b. (assocv l x = SOME y) <=> MEM (x,y) l)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [assocv, MEM, option_CLAUSES]
,P_PGEN_TAC (Term`p:'a,q:'b`) THEN
 DISCH_TAC THEN REPEAT GEN_TAC THEN IMP_RES_TAC ORL_TL THEN RES_TAC THEN
 Cases_on `x = p` THENL
 [EQ_TAC THENL
  [ASM_REWRITE_TAC [assocv, MEM, PAIR_EQ, option_CLAUSES] THEN
   DISCH_TAC THEN AR
  ,SUBGOAL_THEN (Term`MEM (x:'a,q:'b) ((p,q)::l)`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC [MEM]
   ,DISCH_TAC THEN SUBGOAL_THEN (Term`q:'b = y`)
                   (fn eq => ASSUME_TAC eq THEN
                             ASM_REWRITE_TAC [assocv, option_CLAUSES]) THEN
    IMP_RES_TAC ORL_single_valued]]
 ,ASM_REWRITE_TAC [MEM, assocv, PAIR_EQ]
]]);

(* Following 2 lemmas can be proved with hypothesis ORL cmp l from
   assoc_MEM_thm, but are easier to use without the hypothesis. *)

val assocv_NOT_MEM = maybe_thm ("assocv_NOT_MEM", Term
`!x:'a l. (assocv l x = NONE) <=> !y:'b. ~MEM (x,y) l`,
GEN_TAC THEN Induct THEN REWRITE_TAC [assocv, MEM] THEN
P_PGEN_TAC (Term`a:'a,b:'b`) THEN
ASM_REWRITE_TAC [assocv, PAIR_EQ] THEN COND_CASES_TAC THENL
[REWRITE_TAC [option_CLAUSES] THEN CONV_TAC NOT_FORALL_CONV THEN
 EXISTS_TAC (Term`b:'b`) THEN REWRITE_TAC []
,AR]);

val NOT_MEM_merge = maybe_thm ("NOT_MEM_merge",
``!cmp:'a toto l m. ORL cmp l /\ ORL cmp m ==>
       !a. (!z. ~MEM (a:'a,z:'b) (merge cmp l m)) ==>
           (!z. ~MEM (a,z) l) /\ (!z. ~MEM (a,z) m)``,
REPEAT GEN_TAC THEN DISCH_THEN (fn conj => GEN_TAC THEN
                                ASSUME_TAC (MATCH_MP merge_ORL conj) THEN
CONV_TAC (RAND_CONV (AND_FORALL_CONV THENC
                     QUANT_CONV (REWRITE_CONV [GSYM DE_MORGAN_THM])) THENC
          BINOP_CONV FORALL_NOT_CONV THENC
          CONTRAPOS_CONV THENC REWRITE_CONV [NOT_CLAUSES]) THEN
STRIP_TAC THEN MP_TAC (MATCH_MP merge_MEM_thm conj)) THENL
[DISCH_TAC THEN EXISTS_TAC (Term`z:'b`) THEN
 MATCH_MP_TAC MEM_MEM_merge THEN AR
,DISCH_THEN (REWRITE_TAC o ulist) THEN
 Cases_on `?y. MEM (a,y) l` THENL
 [UNDISCH_TAC (Term`?y. MEM (a:'a,y:'b) l`) THEN STRIP_TAC THEN
  EXISTS_TAC (Term`y:'b`) THEN AR
 ,UNDISCH_TAC (Term`~?y. MEM (a:'a,y:'b) l`) THEN
  CONV_TAC (LAND_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THEN
  EXISTS_TAC (Term`z:'b`) THEN AR
]]);

val assocv_merge = maybe_thm ("assocv_merge", Term`!cmp l m:('a#'b)list a.
 ORL cmp l /\ ORL cmp m ==>
 (assocv (merge cmp l m) a = optry (assocv l a) (assocv m a))`,
REPEAT GEN_TAC THEN DISCH_THEN (fn conj =>
                                ASSUME_TAC (MATCH_MP merge_ORL conj) THEN
                                MP_TAC (MATCH_MP merge_MEM_thm conj) THEN
                                ASSUME_TAC conj) THEN
Cases_on `assocv (merge cmp l m) a` THEN
REWRITE_TAC [optry_case] THENL
[DISCH_THEN (fn th => ALL_TAC) THEN IMP_RES_TAC assocv_NOT_MEM THEN
 SUBGOAL_THEN (Term`(!b. ~MEM (a:'a,b:'b) l) /\ !b. ~MEM (a:'a,b:'b) m`)
              MP_TAC THENL
 [CONJ_TAC THEN IMP_RES_TAC (MATCH_MP NOT_MEM_merge
                             (ASSUME (Term`ORL cmp (l:('a#'b)list) /\
                                           ORL cmp (m:('a#'b)list)`)))
 ,REWRITE_TAC [GSYM assocv_NOT_MEM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [option_CLAUSES]
 ]
,IMP_RES_TAC assocv_MEM_thm THEN
 DISCH_THEN (IMP_RES_THEN MP_TAC) THEN
 UNDISCH_TAC (Term`ORL cmp (l:('a#'b)list) /\
                   ORL cmp (m:('a#'b)list)`) THEN STRIP_TAC THEN
 STRIP_TAC THENL
 [IMP_RES_TAC assocv_MEM_thm THEN ASM_REWRITE_TAC [option_CLAUSES] THEN
  BETA_TAC THEN REFL_TAC
 ,IMP_RES_TAC assocv_NOT_MEM THEN
  IMP_RES_TAC assocv_MEM_thm THEN ASM_REWRITE_TAC [option_CLAUSES]
 ]]);

val merge_fun = maybe_thm ("merge_fun",
``!cmp:'a toto l:('a#'b)list m. ORL cmp l /\ ORL cmp m ==>
(assocv (merge cmp l m) = OPTION_UPDATE (assocv l) (assocv m))``,
REPEAT STRIP_TAC THEN
CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC [OPTION_UPDATE] THEN
MATCH_MP_TAC assocv_merge THEN AR);

(* Continue development of sorting in same imitative style as for merge. *)

val incr_merge = Define`
   (incr_merge cmp (l:('a#'b)list) [] = [SOME l])
/\ (incr_merge cmp (l:('a#'b)list) (NONE :: lol) = SOME l :: lol)
/\ (incr_merge cmp (l:('a#'b)list) (SOME m :: lol) = 
                 NONE :: incr_merge cmp (merge cmp l m) lol)`;

val ORL_sublists = Define`(ORL_sublists cmp ([]:('a#'b)list option list) = T)
 /\ (ORL_sublists cmp (NONE :: (lol:('a#'b)list option list)) =
                                                       ORL_sublists cmp lol)
 /\ (ORL_sublists cmp (SOME m :: (lol:('a#'b)list option list)) =
                                      ORL cmp m /\ ORL_sublists cmp lol)`;

val ORL_sublists_ind = theorem"ORL_sublists_ind";

(* ORL_sublists_ind =
  |- !P. (!cmp. P cmp []) /\ (!cmp lol. P cmp lol ==> P cmp (NONE::lol)) /\
         (!cmp m lol. P cmp lol ==> P cmp (SOME m::lol)) ==>
         !v v1. P v v1 *)

val ORL_OL_FST_sublists = maybe_thm ("ORL_OL_FST_sublists",
``!cmp lol:('a#'b)list option list. ORL_sublists cmp lol =
  OL_sublists cmp (MAP (OPTION_MAP (MAP FST)) lol)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss()) [ORL_sublists, OL_sublists, MAP]
,Cases THEN
 RW_TAC (srw_ss ()) [ORL_sublists, OL_sublists, MAP, OPTION_MAP_DEF] THEN
 ASM_REWRITE_TAC [ORL_OL_FST]
]);

val incr_merge_FST_smerge = maybe_thm ("incr_merge_FST_smerge",
``!cmp lol l:('a#'b)list. MAP (OPTION_MAP (MAP FST)) (incr_merge cmp l lol) =
incr_smerge cmp (MAP FST l) (MAP (OPTION_MAP (MAP FST)) lol)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss()) [incr_merge, incr_smerge, MAP]
,Cases THEN
 RW_TAC (srw_ss ()) [incr_merge, incr_smerge, MAP, OPTION_MAP_DEF] THEN
 REWRITE_TAC [merge_FST_smerge]
]);

val incr_merge_ORL = maybe_thm ("incr_merge_ORL",
``!cmp:'a toto l:('a#'b)list lol. ORL cmp l /\
         ORL_sublists cmp lol ==> ORL_sublists cmp (incr_merge cmp l lol)``,
METIS_TAC [smerge_OL, incr_smerge_OL, merge_ORL, merge_FST_smerge,
           incr_merge_FST_smerge, ORL_OL_FST, ORL_OL_FST_sublists]);

val NOT_MEM_NIL = maybe_thm ("NOT_MEM_NIL",
``(!x:'c. ~MEM x l) <=> (l = [])``,
EQ_TAC THENL
[CONV_TAC (CONTRAPOS_CONV THENC (RAND_CONV (NOT_FORALL_CONV))) THEN
 Cases_on `l` THEN RW_TAC (srw_ss ()) [] THEN
 Q.EXISTS_TAC `h` THEN REWRITE_TAC []
,RW_TAC bool_ss [MEM]]);

val SOME_MEM_NOT_NIL = maybe_thm ("SOME_MEM_NOT_NIL",
``~(!ab:'a#'b. MEM ab ((x,y)::l) <=> MEM ab [])``,
RW_TAC (srw_ss()) [MEM] THEN Q.EXISTS_TAC `x,y` THEN REWRITE_TAC []);

val ORL_NOT_MEM = maybe_thm ("ORL_NOT_MEM", Term
`(!cmp (b:'b) x y l. ORL cmp ((x:'a,y)::l) ==> ~MEM (x,b) l) /\
 (!cmp (a:'a) (b:'b) x y l. ORL cmp ((x,y)::l) /\ (apto cmp a x = LESS) ==>
                                                ~MEM (a,b) ((x,y)::l))`,
CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [ORL] THEN STRIP_TAC THENL
[DISCH_TAC THEN RES_THEN MP_TAC
,REWRITE_TAC [MEM, DE_MORGAN_THM, PAIR_EQ] THEN
 IMP_RES_TAC toto_glneq THEN AR THEN
 STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC totoLLtrans THEN
 UNDISCH_TAC (Term`apto cmp a (a:'a) = LESS`)] THEN
REWRITE_TAC [toto_refl, all_cpn_distinct]);

val ORL_MEM_FST	= maybe_thm ("ORL_MEM_FST",
``!cmp l:('a#'b)list. ORL cmp l ==>
    !x y p q. MEM (x,y) l /\ MEM (p,q) l /\ (x = p) ==> (y = q)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [MEM]
,P_PGEN_TAC ``g:'a,h:'b`` THEN RW_TAC (srw_ss ()) [] THENL
[`~MEM (g,q) l` by MATCH_MP_TAC (CONJUNCT1 ORL_NOT_MEM) THEN
 Q.EXISTS_TAC `cmp` THEN Q.EXISTS_TAC `h` THEN AR
,`~MEM (g,y) l` by MATCH_MP_TAC (CONJUNCT1 ORL_NOT_MEM) THEN
 Q.EXISTS_TAC `cmp` THEN Q.EXISTS_TAC `h` THEN AR
,IMP_RES_TAC ORL_TL THEN `p = p` by REFL_TAC THEN RES_TAC
]]);

val ORL_MEM_EQ = maybe_thm ("ORL_MEM_EQ",
``!cmp l m:('a#'b)list. ORL cmp l /\ ORL cmp m ==>
   ((!ab. MEM ab l <=> MEM ab m) <=> (l = m))``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [GSYM NOT_MEM_NIL]
,P_PGEN_TAC ``x:'a,y:'b`` THEN Induct THENL
 [RW_TAC (srw_ss()) [SOME_MEM_NOT_NIL]
 ,P_PGEN_TAC ``p:'a,q:'b`` THEN
  STRIP_TAC THEN IMP_RES_TAC ORL_NOT_MEM THEN
  EQ_TAC THENL
  [Cases_on `apto cmp x p` THENL
   [CONV_TAC LEFT_IMP_FORALL_CONV THEN
    Q.EXISTS_TAC `x,y` THEN
    `~MEM (x,y) ((p,q)::m)` by (RES_TAC THEN AR) THEN ASM_REWRITE_TAC [MEM]
   ,REWRITE_TAC [list_11, PAIR_EQ] THEN
    Q.SUBGOAL_THEN `(!ab. MEM ab l <=> MEM ab m) <=> (l = m)` (SUBST1_TAC o SYM)
    THEN1 (IMP_RES_TAC ORL_TL THEN RES_TAC) THEN
    `x = p` by IMP_RES_TAC toto_equal_eq THEN
    `MEM (x,y) ((x,y)::l)` by REWRITE_TAC [MEM] THEN
    `MEM (p,q) ((p,q)::m)` by REWRITE_TAC [MEM] THEN
    DISCH_THEN (fn eq => `MEM (p,q) ((x,y)::l)` by ASM_REWRITE_TAC [eq] THEN
                         ASSUME_TAC eq) THEN
    `y = q` by IMP_RES_TAC ORL_MEM_FST THEN
    AR THEN P_PGEN_TAC ``g:'a,h:'b`` THEN
    Cases_on `(g = x) /\ (h = y)` THENL
    [METIS_TAC [PAIR_EQ]
    ,Q.SUBGOAL_THEN `MEM (g,h) l = MEM (g,h) ((x,y)::l)` SUBST1_TAC
     THEN1 (REWRITE_TAC [MEM, PAIR_EQ] THEN METIS_TAC []) THEN
     Q.SUBGOAL_THEN `MEM (g,h) m = MEM (g,h) ((p,q)::m)` SUBST1_TAC
     THEN1 (REWRITE_TAC [MEM, PAIR_EQ] THEN METIS_TAC []) THEN AR
    ]
   ,`apto cmp p x = LESS` by IMP_RES_TAC toto_antisym THEN
    CONV_TAC LEFT_IMP_FORALL_CONV THEN
    Q.EXISTS_TAC `p,q` THEN
    `~MEM (p,q) ((x,y)::l)` by (RES_TAC THEN AR) THEN ASM_REWRITE_TAC [MEM]
   ]
  ,DISCH_TAC THEN AR
]]]);

val merge_ASSOC = maybe_thm ("merge_ASSOC",
``!cmp:'a toto k l m:('a#'b)list. ORL cmp k /\ ORL cmp l /\ ORL cmp m ==>
   (merge cmp k (merge cmp l m) = merge cmp (merge cmp k l) m)``,
REPEAT STRIP_TAC THEN
`ORL cmp (merge cmp l m) /\ ORL cmp (merge cmp k l)` by
  (CONJ_TAC THEN MATCH_MP_TAC merge_ORL THEN AR) THEN
Q.SUBGOAL_THEN `ORL cmp (merge cmp k (merge cmp l m)) /\
                ORL cmp (merge cmp (merge cmp k l) m)`
(fn cj => REWRITE_TAC [GSYM (MATCH_MP ORL_MEM_EQ cj)] THEN STRIP_ASSUME_TAC cj)
THEN1 (CONJ_TAC THEN MATCH_MP_TAC merge_ORL THEN AR) THEN
P_PGEN_TAC ``x:'a,y:'b`` THEN
REWRITE_TAC [MATCH_MP merge_MEM_thm (CONJ (Q.ASSUME `ORL cmp k`)
                               (Q.ASSUME `ORL cmp (merge cmp l m)`))]
			       THEN
REWRITE_TAC [MATCH_MP merge_MEM_thm (CONJ (Q.ASSUME `ORL cmp l`)
                                           (Q.ASSUME `ORL cmp m`))] THEN
REWRITE_TAC [MATCH_MP merge_MEM_thm (CONJ (Q.ASSUME `ORL cmp
                           (merge cmp k l)`) (Q.ASSUME `ORL cmp m`))] THEN
REWRITE_TAC [MATCH_MP merge_MEM_thm (CONJ (Q.ASSUME `ORL cmp k`)
                                           (Q.ASSUME `ORL cmp l`))] THEN
METIS_TAC []);

(* Now to figure out how to use merge_ASSOC. Idea, I think, is to show
   that assocv o merge_out is preserved throughout. *)

val OPTION_UPDATE_ASSOC = maybe_thm ("OPTION_UPDATE_ASSOC",
``!f g h:'a -> 'b option. OPTION_UPDATE f (OPTION_UPDATE g h) =
                          OPTION_UPDATE (OPTION_UPDATE f g) h``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
REWRITE_TAC [OPTION_UPDATE, optry_ASSOC]);

val incr_build = Define`(incr_build cmp [] = [])
                     /\ (incr_build cmp (ab:('a#'b) :: l) =
                                incr_merge cmp [ab] (incr_build cmp l))`;

val incr_build_ORL = maybe_thm ("incr_build_ORL",
            ``!cmp l:('a#'b)list. ORL_sublists cmp (incr_build cmp l)``,
GEN_TAC THEN Induct THEN REWRITE_TAC [incr_build] THENL
[REWRITE_TAC [ORL_sublists]
,P_PGEN_TAC (Term`a:'a,b:'b`) THEN MATCH_MP_TAC incr_merge_ORL THEN
 ASM_REWRITE_TAC [ORL, MEM]]);

val merge_out = Define
  `(merge_out (cmp:'a toto) (l:('a#'b)list) ([]:('a#'b)list option list) = l)
/\ (merge_out cmp (l:('a#'b)list) (NONE :: lol) = merge_out cmp l lol)
/\ (merge_out cmp (l:('a#'b)list) ((SOME (m:('a#'b)list)) :: lol) =
                                     merge_out cmp (merge cmp l m) lol)`;

val merge_out_ORL = maybe_thm ("merge_out_ORL",
``!cmp lol:('a#'b)list option list l. ORL cmp l /\
   ORL_sublists cmp lol ==> ORL cmp (merge_out cmp l lol)``,
HO_MATCH_MP_TAC ORL_sublists_ind THEN REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC [merge_out] THEN
IMP_RES_TAC ORL_sublists THEN RES_TAC THEN
SUBGOAL_THEN (Term`ORL cmp (merge cmp l m:('a#'b)list)`)
             (fn th => ASSUME_TAC th THEN RES_TAC) THEN
IMP_RES_TAC merge_ORL);

val incr_flat = Define`incr_flat
 (cmp:'a toto) (lol:('a#'b)list option list) = merge_out cmp [] lol`;

(* by not utilizing incr_flat in incr_sort, we ease writing conversions. *)

val incr_sort = Define`incr_sort (cmp:'a toto) (l:('a#'b)list) =
                       merge_out cmp [] (incr_build cmp l)`;

val incr_sort_ORL = maybe_thm ("incr_sort_ORL", Term
`!cmp l:('a#'b)list. ORL cmp (incr_sort cmp l)`,
REPEAT GEN_TAC THEN REWRITE_TAC [incr_sort, incr_flat] THEN
MATCH_MP_TAC merge_out_ORL THEN
REWRITE_TAC [ORL, incr_build_ORL]);

(* ************ work up to incr_sort_fun *********** *)

val OPTION_FLAT = Define
`(OPTION_FLAT ([]:'z list option list) = []) /\
 (OPTION_FLAT (NONE:'z list option :: l) = OPTION_FLAT l) /\
 (OPTION_FLAT (SOME a :: l) = a ++ OPTION_FLAT l)`;

val OPTION_FLAT_ind = theorem "OPTION_FLAT_ind";

(* OPTION_FLAT_ind = |- !P. P [] /\ (!l. P l ==> P (NONE::l)) /\
                            (!a l. P l ==> P (SOME a::l)) ==> !v. P v *)

val assocv_optry_lem = maybe_thm ("assocv_optry_lem", Term
`!x l:('a#'b)list m. assocv (l ++ m) x = optry (assocv l x) (assocv m x)`,
GEN_TAC THEN Induct THEN REWRITE_TAC [APPEND, optry_ID, assocv] THEN
P_PGEN_TAC (Term`p:'a,q:'b`) THEN
REWRITE_TAC [assocv] THEN Cases_on `x = p` THEN AR THEN REWRITE_TAC [optry]);

val assocv_APPEND = maybe_thm ("assocv_APPEND",
``!l:('a#'b)list m. assocv (l ++ m) = OPTION_UPDATE (assocv l) (assocv m)``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
REWRITE_TAC [OPTION_UPDATE, assocv_optry_lem]);

val assocv_merge_out = maybe_thm ("assocv_merge_out",
``!cmp lol:('a#'b)list option list l. ORL cmp l /\ ORL_sublists cmp lol ==>
        (assocv (merge_out cmp l lol) = assocv (l ++ OPTION_FLAT lol))``,
GEN_TAC THEN
HO_MATCH_MP_TAC OPTION_FLAT_ind THEN
RW_TAC (srw_ss ()) [OPTION_FLAT, merge_out] THENL
[`ORL_sublists cmp lol` by (ONCE_REWRITE_TAC [GSYM ORL_sublists] THEN AR) THEN
 RES_TAC
,`ORL cmp a /\ ORL_sublists cmp lol` by REWRITE_TAC [REWRITE_RULE
        [ORL_sublists] (Q.ASSUME `ORL_sublists cmp (SOME a ::lol)`)] THEN
 `ORL cmp (merge cmp l a)` by
    (MATCH_MP_TAC merge_ORL THEN AR) THEN
  RES_TAC THEN IMP_RES_TAC merge_fun THEN ASM_REWRITE_TAC [assocv_APPEND]
]);

val assocv_incr_flat = maybe_thm ("assocv_incr_flat",
``!cmp lol:('a#'b)list option list. ORL_sublists cmp lol ==>
  (assocv (incr_flat cmp lol) = assocv (OPTION_FLAT lol))``,
REPEAT STRIP_TAC THEN `ORL cmp []` by REWRITE_TAC [ORL] THEN
IMP_RES_TAC assocv_merge_out THEN POP_ASSUM MP_TAC THEN
REWRITE_TAC [incr_flat, APPEND]);

val assocv_incr_merge = maybe_thm ("assocv_incr_merge",
``!cmp lol:('a#'b)list option list l m. ORL cmp l /\ ORL cmp m /\
  ORL_sublists cmp lol ==>
  (assocv (merge_out cmp l (incr_merge cmp m lol)) =
   assocv (merge_out cmp (merge cmp l m) lol))``,
GEN_TAC THEN Induct THEN RW_TAC (srw_ss ())
 [assocv_merge_out, OPTION_FLAT, merge_out, incr_merge, assocv_APPEND] THEN
Cases_on `h` THEN RW_TAC (srw_ss ()) [incr_merge, merge_out] THEN
`ORL cmp x /\ ORL_sublists cmp lol` by METIS_TAC [ORL_sublists] THEN
Q.SUBGOAL_THEN `merge cmp (merge cmp l m) x = merge cmp l (merge cmp m x)`
SUBST1_TAC THEN1 (MATCH_MP_TAC (GSYM merge_ASSOC) THEN AR) THEN
`ORL cmp (merge cmp m x)` by (MATCH_MP_TAC merge_ORL THEN AR) THEN
`ORL_sublists cmp (incr_merge cmp (merge cmp m x) lol)` by
  (MATCH_MP_TAC incr_merge_ORL THEN AR) THEN
METIS_TAC [assocv_merge_out]);

val assocv_NIL = maybe_thm ("assocv_NIL",
``assocv ([]:('a#'b)list) = K NONE``,
CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) [assocv]);

val OPTION_UPDATE_K_NONE = maybe_thm ("OPTION_UPDATE_K_NONE",
``!f:'a->'b option. (OPTION_UPDATE f (K NONE) = f) /\
                    (OPTION_UPDATE (K NONE) f = f)``,
CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
RW_TAC (srw_ss ()) [OPTION_UPDATE, optry_ID]);

val ORL_SING = maybe_thm ("ORL_SING",
``!cmp x:('a#'b). ORL cmp [x]``,
GEN_TAC THEN P_PGEN_TAC ``a:'a,b:'b`` THEN REWRITE_TAC [ORL, MEM]);

val assocv_incr_build = maybe_thm ("assocv_incr_build",
``!cmp:'a toto m l:('a#'b)list. ORL cmp l ==>
 (assocv (merge_out cmp l (incr_build cmp m)) = assocv (l ++ m))``,
GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [assocv_APPEND, incr_build, merge_out] THENL
[REWRITE_TAC [OPTION_UPDATE_K_NONE, assocv_NIL, merge_thm]
,Q.SUBGOAL_THEN
 `OPTION_UPDATE (assocv l) (assocv (h::m)) = assocv ((l ++ [h]) ++ m)`
  SUBST1_TAC THENL
 [Q.SUBGOAL_THEN `h::m = [h] ++ m` SUBST1_TAC THEN1 REWRITE_TAC [APPEND] THEN
  RW_TAC (srw_ss ()) [assocv_APPEND, OPTION_UPDATE_ASSOC]
 ,`ORL cmp [h]` by MATCH_ACCEPT_TAC ORL_SING THEN
  `ORL_sublists cmp (incr_build cmp m)` by MATCH_ACCEPT_TAC incr_build_ORL THEN
  Q.SUBGOAL_THEN
  `assocv (merge_out cmp l (incr_merge cmp [h] (incr_build cmp m))) =
   assocv (merge_out cmp (merge cmp l [h]) (incr_build cmp m))`
  SUBST1_TAC THEN1 (MATCH_MP_TAC assocv_incr_merge THEN AR) THEN
  `ORL cmp (merge cmp l [h])` by (MATCH_MP_TAC merge_ORL THEN AR) THEN
  RES_THEN SUBST1_TAC THEN
  METIS_TAC [merge_fun, assocv_APPEND]
]]);

(* at last: incr_sort not only sorts, but it is stable in the sense that
   the list coming out (with guaranteed only one entry for any key) has the
   same behavior under assocv as the (possibly duplicitous) list going in. *)

val incr_sort_fun = maybe_thm ("incr_sort_fun",
``!cmp: 'a toto l:('a#'b)list. assocv (incr_sort cmp l) = assocv l``,
REPEAT GEN_TAC THEN REWRITE_TAC [incr_sort, incr_flat] THEN
Q.SUBGOAL_THEN `assocv l = assocv ([] ++ l)` SUBST1_TAC 
THEN1 REWRITE_TAC [APPEND] THEN
MATCH_MP_TAC assocv_incr_build THEN REWRITE_TAC [ORL]);

(* ********** Relating association lists to finite maps ************ *)
(* Define "unlookup", sending an option-valued function to an fmap.  *)
(* ***************************************************************** *)

val unlookup = Define`unlookup (f:'a -> 'b option) =
                      FUN_FMAP (THE o f) (IS_SOME o f)`;

(* and prove that unlookup sends OPTION_UPDATE to FUNION *)

(* ********* We require a short interlude relating option-valued ******** *)
(* ********* and finite functions, via FLOOKUP and unlookup.     ******** *)

val FUPDATE_ALT = prove (
``!f:'a |-> 'b l. f |++ REVERSE l = FOLDR (combin$C FUPDATE) f l``,
REPEAT GEN_TAC THEN REWRITE_TAC [FUPDATE_LIST, combinTheory.C_DEF]
THEN BETA_TAC THEN REWRITE_TAC [rich_listTheory.FOLDL_REVERSE]);

val IS_SOME_FDOM = maybe_thm ("IS_SOME_FDOM",
``!f:'a |-> 'b. IS_SOME o FLOOKUP f = FDOM f``,
Induct THEN CONJ_TAC THENL
[REWRITE_TAC [EXTENSION, FDOM_FEMPTY, NOT_IN_EMPTY] THEN
 REWRITE_TAC [SPECIFICATION, combinTheory.o_THM, option_CLAUSES, FLOOKUP_EMPTY]
,GEN_TAC THEN DISCH_THEN (ASSUME_TAC o REWRITE_RULE [combinTheory.o_THM] o
                          CONV_RULE FUN_EQ_CONV) THEN
 REPEAT STRIP_TAC THEN
 ASM_REWRITE_TAC [FDOM_FUPDATE, EXTENSION, IN_INSERT] THEN GEN_TAC THEN
 REWRITE_TAC [SPECIFICATION, combinTheory.o_THM, FLOOKUP_UPDATE] THEN
 Cases_on `x = x'` THEN ASM_REWRITE_TAC [option_CLAUSES] THEN
 REWRITE_TAC [GSYM (ASSUME ``x:'a <> x'``)]]);

val FINITE_FLOOKUP = maybe_thm ("FINITE_FLOOKUP",
``!f:'a |-> 'b. FINITE (IS_SOME o FLOOKUP f)``,
REWRITE_TAC [IS_SOME_FDOM, FDOM_FINITE]);

val FLOOKUP_unlookup_FDOM = maybe_thm ("FLOOKUP_unlookup_FDOM",
``!f:'a |-> 'b. FDOM (unlookup (FLOOKUP f)) = FDOM f``,
REWRITE_TAC [unlookup] THEN ASSUME_TAC (SPEC_ALL FINITE_FLOOKUP) THEN
IMP_RES_TAC FUN_FMAP_DEF THEN ASM_REWRITE_TAC [IS_SOME_FDOM] THEN
GEN_TAC THEN ASSUME_TAC (SPEC ``f':'a |-> 'b`` FDOM_FINITE) THEN
IMP_RES_TAC FUN_FMAP_DEF THEN AR);

val FLOOKUP_unlookup_ID = maybe_thm ("FLOOKUP_unlookup_ID",
``!f:'a |-> 'b. unlookup (FLOOKUP f) = f``,
GEN_TAC THEN REWRITE_TAC [fmap_EXT] THEN CONJ_TAC THEN
REWRITE_TAC [FLOOKUP_unlookup_FDOM] THEN REPEAT STRIP_TAC THEN
REWRITE_TAC [unlookup] THEN ASSUME_TAC (SPEC_ALL FINITE_FLOOKUP) THEN
IMP_RES_THEN
 (STRIP_ASSUME_TAC o REWRITE_RULE [IS_SOME_FDOM]) FUN_FMAP_DEF THEN
ASM_REWRITE_TAC [IS_SOME_FDOM] THEN RES_TAC THEN
ASM_REWRITE_TAC [option_CLAUSES, FLOOKUP_DEF, combinTheory.o_THM]);

val unlookup_FLOOKUP_ID = maybe_thm ("unlookup_FLOOKUP_ID",``!g:'a->'b option.
 FINITE (IS_SOME o g) ==> (FLOOKUP (unlookup g) = g)``,
GEN_TAC THEN REWRITE_TAC [unlookup] THEN DISCH_TAC THEN
IMP_RES_TAC (REWRITE_RULE [SPECIFICATION] FUN_FMAP_DEF) THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
ASM_REWRITE_TAC [FLOOKUP_DEF, SPECIFICATION] THEN
Cases_on `(IS_SOME o g) x` THEN
ASM_REWRITE_TAC [option_CLAUSES] THEN REWRITE_TAC [combinTheory.o_THM] THENL
[RES_TAC THEN AR THEN
 UNDISCH_TAC ``(IS_SOME o (g:'a->'b option)) x`` THEN
 ASM_REWRITE_TAC [combinTheory.o_THM, option_CLAUSES]
,UNDISCH_TAC ``~(IS_SOME o (g:'a->'b option)) x`` THEN
 ASM_REWRITE_TAC [combinTheory.o_THM, option_CLAUSES] THEN
 DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val unlookup_FDOM = maybe_thm ("unlookup_FDOM", ``!g:'a->'b option.
 FINITE (IS_SOME o g) ==> (FDOM (unlookup g) = IS_SOME o g)``,
GEN_TAC THEN
DISCH_THEN (SUBST1_TAC o SYM o MATCH_MP unlookup_FLOOKUP_ID) THEN
REWRITE_TAC [IS_SOME_FDOM, FLOOKUP_unlookup_ID]);

val unlookup_11 = maybe_thm ("unlookup_11",
``!f g:'a ->'b option. FINITE (IS_SOME o f) /\ FINITE (IS_SOME o g) ==>
                       (unlookup f = unlookup g) ==> (f = g)``,
REPEAT STRIP_TAC THEN
IMP_RES_THEN
 (PURE_ONCE_REWRITE_TAC o ulist o SYM) unlookup_FLOOKUP_ID THEN AR);

(* ******* end of interlude as described above; still more ********* *)
(* ******* lemmas to come, adjusting to finite_mapTheory.  ********* *)

val unlookup_FUNION = maybe_thm ("unlookup_FUNION",
``!u (v:'a -> 'b option). FINITE (IS_SOME o u) /\ FINITE (IS_SOME o v) ==>
      (unlookup u FUNION unlookup v = unlookup (OPTION_UPDATE u v))``,
REPEAT STRIP_TAC THEN
SUBGOAL_THEN ``FINITE (IS_SOME o OPTION_UPDATE u (v:'a -> 'b option))``
             ASSUME_TAC
THEN1 ASM_REWRITE_TAC [IS_SOME_OPTION_UPDATE, FINITE_UNION] THEN
REWRITE_TAC [fmap_EXT] THEN CONJ_TAC THEN
IMP_RES_TAC unlookup_FDOM THEN
ASM_REWRITE_TAC [FUNION_DEF, IS_SOME_OPTION_UPDATE, IN_UNION] THEN
REPEAT STRIP_TAC THEN
(SUBGOAL_THEN ``x IN (IS_SOME o OPTION_UPDATE (u:'a->'b option) v)`` ASSUME_TAC
 THEN1 ASM_REWRITE_TAC [IS_SOME_OPTION_UPDATE, IN_UNION]) THEN
REWRITE_TAC [unlookup] THENL
[ALL_TAC, Cases_on `x IN IS_SOME o u` THEN AR] THEN
IMP_RES_TAC FUN_FMAP_DEF THEN
ASM_REWRITE_TAC [combinTheory.o_THM] THEN
IMP_RES_TAC (fst (EQ_IMP_RULE (SPEC_ALL SPECIFICATION))) THEN
ASM_REWRITE_TAC [OPTION_UPDATE, option_CLAUSES, optry] THEN
AP_TERM_TAC THEN
IMP_RES_TAC (fst (EQ_IMP_RULE (INST_TYPE [beta |-> ``:bool``]
                               (SPEC_ALL combinTheory.o_THM)))) THEN
IMP_RES_THEN (REWRITE_TAC o ulist) IS_SOME_optry THEN
UNDISCH_TAC ``x NOTIN IS_SOME o (u:'a -> 'b option)`` THEN
REWRITE_TAC [SPECIFICATION, combinTheory.o_THM] THEN
Cases_on `u x` THEN REWRITE_TAC [optry, option_CLAUSES]);

(* ****** Get back to imitating enumeralTheory with a constant FMAPAL  ***** *)
(* ****** of type ('a#'b)bt -> ('a |-> 'b) (but call the definition    ***** *)
(* ****** bt_to_fmap, like the bt_to_set of enumeralTheory).           ***** *)

val bt_to_fmap = xDefine "bt_to_fmap"
`(FMAPAL (cmp:'a toto) nt = (FEMPTY:'a|->'b)) /\
 (FMAPAL (cmp:'a toto) (node l (x:'a,v:'b) r) =
  DRESTRICT (FMAPAL cmp l) {y | apto cmp y x = LESS} FUNION
  FEMPTY |+ (x,v) FUNION
  DRESTRICT (FMAPAL cmp r) {z | apto cmp x z = LESS})`;

val bt_to_fmap_ind  = theorem "bt_to_fmap_ind";

(* bt_to_fmap_ind = |- !P.
     (!cmp. P cmp nt) /\
     (!cmp l x v r. P cmp l /\ P cmp r ==> P cmp (node l (x,v) r))
     ==> !v v1. P v v1 *)

(* lemmas to help with FAPPLY_node, various _mut_rec's *)

val FUNION_DRESTRICT = maybe_thm ("FUNION_DRESTRICT", (*cf. DRESTRICT_FUNION*)
``!f:'a|->'b g s.
   DRESTRICT (f FUNION g) s = DRESTRICT f s FUNION DRESTRICT g s``,
REPEAT GEN_TAC THEN REWRITE_TAC [fmap_EXT, FDOM_DRESTRICT, FDOM_FUNION] THEN
CONJ_TAC THENL
[ONCE_REWRITE_TAC [INTER_COMM] THEN MATCH_ACCEPT_TAC UNION_OVER_INTER
,GEN_TAC THEN Cases_on `x IN FDOM f` THEN ASM_REWRITE_TAC [DRESTRICT_DEF] THEN
 ASM_REWRITE_TAC [IN_UNION, IN_INTER] THEN
 RW_TAC (srw_ss ()) [FDOM_FUNION, FDOM_DRESTRICT, FUNION_DEF, DRESTRICT_DEF]]);

val DRESTRICT_SING = maybe_thm ("DRESTRICT_SING",
``!x:'a y:'b s. x IN s ==> (DRESTRICT (FEMPTY |+ (x,y)) s = FEMPTY |+ (x,y))``,
RW_TAC (srw_ss ()) [DRESTRICT_DEF]);

val DRESTRICT_SING_FEMPTY = maybe_thm ("DRESTRICT_SING_FEMPTY",
``!x:'a y:'b s. x NOTIN s ==> (DRESTRICT (FEMPTY |+ (x,y)) s = FEMPTY)``,
RW_TAC (srw_ss ()) [DRESTRICT_DEF]);

val DRESTRICT_IN = maybe_thm ("DRESTRICT_IN",
``!s x f:'a|->'b. x IN s ==> (DRESTRICT f s ' x = f ' x)``,
GEN_TAC THEN GEN_TAC THEN Induct THEN
RW_TAC (srw_ss ()) [DRESTRICT_DEF, IN_INTER, FAPPLY_FUPDATE_THM]);

val DRESTRICT_NOT_IN = maybe_thm ("DRESTRICT_NOT_IN",
``!s x f:'a|->'b. x NOTIN s ==> (DRESTRICT f s ' x = FEMPTY ' x)``,
RW_TAC (srw_ss ()) [DRESTRICT_DEF, IN_INTER]);

val IN_FDOM_DRESTRICT_IMP = maybe_thm ("IN_FDOM_DRESTRICT_IMP",
``!f:'a|->'b s x. x IN FDOM (DRESTRICT f s) ==> x IN s``,
METIS_TAC [FDOM_DRESTRICT, IN_INTER]);

(* Following two theorems should be used by application conversion. *)

val FAPPLY_nt = store_thm ("FAPPLY_nt",
``!cmp x. FMAPAL cmp (nt:('a#'b)bt) ' x = FEMPTY ' x``,
REWRITE_TAC [bt_to_fmap]);

val FAPPLY_node = store_thm ("FAPPLY_node",
``!cmp x l a:'a b:'b r. FMAPAL cmp (node l (a,b) r) ' x =
       case apto cmp x a of LESS => FMAPAL cmp l ' x
                       |   EQUAL => b
                       | GREATER => FMAPAL cmp r ' x``,
RW_TAC (srw_ss ()) [bt_to_fmap, FUNION_DEF] THENL
[Q.SUBGOAL_THEN `x IN {y | apto cmp y a = LESS}`
 (fn xin => RW_TAC (srw_ss ()) [MATCH_MP DRESTRICT_IN xin,
                                CONV_RULE SET_SPEC_CONV xin]) THEN
 METIS_TAC [IN_INTER, FDOM_DRESTRICT]
,`apto cmp a a = LESS` by IMP_RES_THEN
 (MATCH_ACCEPT_TAC o CONV_RULE SET_SPEC_CONV) IN_FDOM_DRESTRICT_IMP THEN
 METIS_TAC [toto_refl, all_cpn_distinct]
,RW_TAC (srw_ss ()) [toto_refl, FAPPLY_FUPDATE_THM]
,POP_ASSUM (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV SET_SPEC_CONV) o
            REWRITE_RULE [FDOM_DRESTRICT, IN_INTER]) THEN
 RW_TAC (srw_ss ()) [] THENL
 [Cases_on `apto cmp x a` THEN RW_TAC (srw_ss ()) [] THENL
  [IMP_RES_THEN SUBST1_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
   Q.SUBGOAL_THEN `x NOTIN {z | apto cmp a z = LESS}`
    (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_NOT_IN) THEN
   CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN
   RW_TAC (srw_ss ()) [GSYM toto_antisym]
  ,METIS_TAC [toto_equal_eq]
  ,Q.SUBGOAL_THEN `x IN {z | apto cmp a z = LESS}`
                  (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_IN) THEN
   CONV_TAC SET_SPEC_CONV THEN ASM_REWRITE_TAC [GSYM toto_antisym]
  ]
 ,Q.SUBGOAL_THEN `x IN {z | apto cmp a z = LESS}`
  (fn xin => RW_TAC (srw_ss ()) [MATCH_MP DRESTRICT_IN xin,
         REWRITE_RULE [GSYM toto_antisym] (CONV_RULE SET_SPEC_CONV xin)]) THEN
  CONV_TAC SET_SPEC_CONV THEN
  REWRITE_TAC [GSYM toto_antisym] THEN
  `apto cmp x a <> EQUAL` by ASM_REWRITE_TAC [toto_equal_eq] THEN
  METIS_TAC [cpn_nchotomy]
]]);

(* Following theorems prepare for converting bt's to association lists. *)

val bt_to_fmap_lb = Define`bt_to_fmap_lb cmp lb (t:('a#'b)bt) =
                        DRESTRICT (FMAPAL cmp t) {x | apto cmp lb x = LESS}`;

val bt_to_fmap_ub = Define`bt_to_fmap_ub cmp (t:('a#'b)bt) ub =
                        DRESTRICT (FMAPAL cmp t) {x | apto cmp x ub = LESS}`;

val bt_to_fmap_mut_rec = maybe_thm ("bt_to_fmap_mut_rec",
``!cmp:'a toto l x y r. FMAPAL cmp (node l (x:'a,y:'b) r) =
   bt_to_fmap_ub cmp l x FUNION FEMPTY |+ (x,y) FUNION bt_to_fmap_lb cmp x r``,
 REWRITE_TAC [bt_to_fmap_lb, bt_to_fmap_ub, bt_to_fmap]);

val bt_to_fmap_lb_ub = Define`bt_to_fmap_lb_ub cmp lb (t:('a#'b)bt) ub =
DRESTRICT (FMAPAL cmp t) {x | (apto cmp lb x = LESS) /\
                               (apto cmp x ub = LESS)}`;

(* ******** Interlude defining bt_map and connecting it with ENUMERAL, FST,
            FMAPAL, and FDOM. bt_map will be used by o_f_CONV.        ****** *)

val bt_map = Define
`(bt_map (f:'a ->'b) (nt:'a bt) = (nt:'b bt)) /\
 (bt_map f (node l x r) = node (bt_map f l) (f x) (bt_map f r))`;

val bt_FST_FDOM = store_thm ("bt_FST_FDOM",
``!cmp t:('a#'b)bt. FDOM (FMAPAL cmp t) = ENUMERAL cmp (bt_map FST t)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_to_set, bt_to_fmap, bt_map]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [bt_to_set, bt_to_fmap, bt_map,  FDOM_DRESTRICT] THEN
 REWRITE_TAC [EXTENSION, IN_INTER, IN_UNION] THEN
 GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REFL_TAC]);

val bt_fst_lb_FDOM = maybe_thm ("bt_fst_lb_FDOM", ``!cmp lb t:('a#'b)bt.
 FDOM (bt_to_fmap_lb cmp lb t) = bt_to_set_lb cmp lb (bt_map FST t)``,
RW_TAC (srw_ss ()) [bt_to_set_lb,  bt_to_fmap_lb, bt_FST_FDOM, FDOM_DRESTRICT]
THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REFL_TAC);

val bt_fst_ub_FDOM = maybe_thm ("bt_fst_ub_FDOM", ``!cmp t:('a#'b)bt ub.
 FDOM (bt_to_fmap_ub cmp t ub) = bt_to_set_ub cmp (bt_map FST t) ub``,
RW_TAC (srw_ss ()) [bt_to_set_ub,  bt_to_fmap_ub, bt_FST_FDOM, FDOM_DRESTRICT]
THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REFL_TAC);

val bt_fst_lb_ub_FDOM = maybe_thm ("bt_fst_lb_ub_FDOM",
``!cmp lb t:('a#'b)bt ub. FDOM (bt_to_fmap_lb_ub cmp lb t ub) =
                          bt_to_set_lb_ub cmp lb (bt_map FST t) ub``,
RW_TAC (srw_ss ())
 [bt_to_set_lb_ub,  bt_to_fmap_lb_ub, bt_FST_FDOM, FDOM_DRESTRICT]
THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REFL_TAC);

val IN_lb_ub_imp = maybe_thm ("IN_lb_ub_imp",
``!cmp x lb t:'a bt ub. x IN bt_to_set_lb_ub cmp lb t ub ==>
                      (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)``,
RW_TAC (srw_ss ()) [bt_to_set_lb_ub]);

val IN_lb_imp = maybe_thm ("IN_lb_imp",
``!cmp x lb t:'a bt. x IN bt_to_set_lb cmp lb t ==> (apto cmp lb x = LESS)``,
RW_TAC (srw_ss ()) [bt_to_set_lb]);

val IN_ub_imp = maybe_thm ("IN_ub_imp",
``!cmp x t:'a bt ub. x IN bt_to_set_ub cmp t ub ==> (apto cmp x ub = LESS)``,
RW_TAC (srw_ss ()) [bt_to_set_ub]);

val piecewise_FUNION = prove (
``!a b c x y z:'a|->'b.(a=x)/\(b=y)/\(c=z)==>
                       (a FUNION b FUNION c = x FUNION y FUNION z)``,
METIS_TAC []);

val bt_to_fmap_lb_ub_mut_rec = maybe_thm ("bt_to_fmap_lb_ub_mut_rec",
``!cmp lb l x:'a y:'b r ub. bt_to_fmap_lb_ub cmp lb (node l (x,y) r) ub =
  if apto cmp lb x = LESS then
    if apto cmp x ub = LESS then
      bt_to_fmap_lb_ub cmp lb l x FUNION FEMPTY |+ (x,y) FUNION
      bt_to_fmap_lb_ub cmp x r ub
    else
      bt_to_fmap_lb_ub cmp lb l ub
  else
    bt_to_fmap_lb_ub cmp lb r ub``,
RW_TAC (srw_ss ()) [fmap_EXT, bt_fst_lb_ub_FDOM] THEN
RW_TAC (srw_ss ()) [bt_to_fmap_lb_ub, bt_to_set_lb_ub, bt_map] THENL
[REWRITE_TAC [EXTENSION, IN_UNION, bt_to_set] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
 METIS_TAC [totoLLtrans, IN_SING]
,IMP_RES_TAC IN_lb_ub_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 AP_THM_TAC THEN AP_TERM_TAC THEN
 MATCH_MP_TAC piecewise_FUNION THEN
 REPEAT CONJ_TAC THENL
 [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,MATCH_MP_TAC DRESTRICT_SING THEN
  CONV_TAC SET_SPEC_CONV THEN AR
 ,AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ]
,REWRITE_TAC [bt_to_set, EXTENSION, IN_UNION] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN EQ_TAC THEN STRIP_TAC THEN AR THEN
 METIS_TAC [totoLLtrans, IN_SING, NOT_EQ_LESS_IMP]
,IMP_RES_TAC IN_lb_ub_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 Q.SUBGOAL_THEN `({z | apto cmp x z = LESS} INTER
 {x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}) = {}` SUBST1_TAC THENL
 [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,Q.SUBGOAL_THEN
  `x NOTIN {x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}`
  (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_SING_FEMPTY) THENL
  [CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
  ,REWRITE_TAC [DRESTRICT_IS_FEMPTY, FUNION_FEMPTY_2] THEN
   Q.SUBGOAL_THEN `{x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}
                   SUBSET {y | apto cmp y x = LESS}`
   (SUBST1_TAC o REWRITE_RULE [SYM (CONJUNCT2 INTER_SUBSET_EQN)]) THENL
   [REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
    METIS_TAC [totoLLtrans, NOT_EQ_LESS_IMP]
   ,REFL_TAC
 ]]]
,REWRITE_TAC [bt_to_set, EXTENSION, IN_UNION] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN EQ_TAC THEN STRIP_TAC THEN AR THEN
 METIS_TAC [totoLLtrans, IN_SING, NOT_EQ_LESS_IMP]
,IMP_RES_TAC IN_lb_ub_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 Q.SUBGOAL_THEN `({y | apto cmp y x = LESS} INTER
 {x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}) = {}` SUBST1_TAC THENL
 [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,Q.SUBGOAL_THEN
  `x NOTIN {x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}`
  (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_SING_FEMPTY) THENL
  [CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
  ,REWRITE_TAC [DRESTRICT_IS_FEMPTY, FUNION_FEMPTY_1] THEN
   Q.SUBGOAL_THEN `{x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}
                   SUBSET {z | apto cmp x z = LESS}`
   (SUBST1_TAC o REWRITE_RULE [SYM (CONJUNCT2 INTER_SUBSET_EQN)]) THENL
   [REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
    METIS_TAC [totoLLtrans, NOT_EQ_LESS_IMP]
   ,REFL_TAC
 ]]]
]);

val bt_to_fmap_lb_mut_rec = maybe_thm ("bt_to_fmap_lb_mut_rec",
``!cmp lb l x:'a y:'b r. bt_to_fmap_lb cmp lb (node l (x,y) r) =
  if apto cmp lb x = LESS then
      bt_to_fmap_lb_ub cmp lb l x FUNION FEMPTY |+ (x,y) FUNION
      bt_to_fmap_lb cmp x r
  else
    bt_to_fmap_lb cmp lb r``,
RW_TAC (srw_ss ()) [fmap_EXT, bt_fst_lb_ub_FDOM, bt_fst_lb_FDOM] THEN
RW_TAC (srw_ss ()) [bt_to_fmap_lb_ub, bt_to_set_lb_ub, bt_map,
                    bt_to_fmap_lb, bt_to_set_lb] THENL
[REWRITE_TAC [EXTENSION, IN_UNION, bt_to_set] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
 METIS_TAC [totoLLtrans, IN_SING]
,IMP_RES_TAC IN_lb_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 AP_THM_TAC THEN AP_TERM_TAC THEN
 MATCH_MP_TAC piecewise_FUNION THEN
 REPEAT CONJ_TAC THENL
 [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,MATCH_MP_TAC DRESTRICT_SING THEN
  CONV_TAC SET_SPEC_CONV THEN AR
 ,AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ]
,REWRITE_TAC [bt_to_set, EXTENSION, IN_UNION] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN EQ_TAC THEN STRIP_TAC THEN AR THEN
 METIS_TAC [totoLLtrans, IN_SING, NOT_EQ_LESS_IMP]
,IMP_RES_TAC IN_lb_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 Q.SUBGOAL_THEN `({y | apto cmp y x = LESS} INTER
                  {x | (apto cmp lb x = LESS)}) = {}` SUBST1_TAC THENL
 [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,Q.SUBGOAL_THEN
  `x NOTIN {x | (apto cmp lb x = LESS)}`
  (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_SING_FEMPTY) THENL
  [CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
  ,REWRITE_TAC [DRESTRICT_IS_FEMPTY, FUNION_FEMPTY_1] THEN
   Q.SUBGOAL_THEN `{x | (apto cmp lb x = LESS)}
                   SUBSET {z | apto cmp x z = LESS}`
   (SUBST1_TAC o REWRITE_RULE [SYM (CONJUNCT2 INTER_SUBSET_EQN)]) THENL
   [REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
    METIS_TAC [totoLLtrans, NOT_EQ_LESS_IMP]
   ,REFL_TAC
 ]]]
]);

val bt_to_fmap_ub_mut_rec = maybe_thm ("bt_to_fmap_ub_mut_rec",
``!cmp l x:'a y:'b r ub. bt_to_fmap_ub cmp (node l (x,y) r) ub =
  if apto cmp x ub = LESS then
      bt_to_fmap_ub cmp l x FUNION FEMPTY |+ (x,y) FUNION
      bt_to_fmap_lb_ub cmp x r ub
  else
      bt_to_fmap_ub cmp l ub``,
RW_TAC (srw_ss ()) [fmap_EXT, bt_fst_lb_ub_FDOM, bt_fst_ub_FDOM] THEN
RW_TAC (srw_ss ()) [bt_to_fmap_lb_ub, bt_to_set_lb_ub, bt_map,
                    bt_to_fmap_ub, bt_to_set_ub] THENL
[REWRITE_TAC [EXTENSION, IN_UNION, bt_to_set] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
 METIS_TAC [totoLLtrans, IN_SING]
,IMP_RES_TAC IN_ub_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 AP_THM_TAC THEN AP_TERM_TAC THEN
 MATCH_MP_TAC piecewise_FUNION THEN
 REPEAT CONJ_TAC THENL
 [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,MATCH_MP_TAC DRESTRICT_SING THEN
  CONV_TAC SET_SPEC_CONV THEN AR
 ,AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ]
,REWRITE_TAC [bt_to_set, EXTENSION, IN_UNION] THEN GEN_TAC THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN EQ_TAC THEN STRIP_TAC THEN AR THEN
 METIS_TAC [totoLLtrans, IN_SING, NOT_EQ_LESS_IMP]
,IMP_RES_TAC IN_ub_imp THEN
 REWRITE_TAC [bt_to_fmap, FUNION_DRESTRICT, DRESTRICT_DRESTRICT] THEN
 Q.SUBGOAL_THEN `{z | apto cmp x z = LESS} INTER {x | apto cmp x ub = LESS}
                  = {}` SUBST1_TAC THENL
 [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN GEN_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
 ,Q.SUBGOAL_THEN
  `x NOTIN {x | (apto cmp x ub = LESS)}`
  (REWRITE_TAC o ulist o MATCH_MP DRESTRICT_SING_FEMPTY) THENL
  [CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN METIS_TAC [totoLLtrans]
  ,REWRITE_TAC [DRESTRICT_IS_FEMPTY, FUNION_FEMPTY_2] THEN
   Q.SUBGOAL_THEN `{x | (apto cmp x ub = LESS)}
                   SUBSET {y | apto cmp y x = LESS}`
   (SUBST1_TAC o REWRITE_RULE [SYM (CONJUNCT2 INTER_SUBSET_EQN)]) THENL
   [REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
    METIS_TAC [totoLLtrans, NOT_EQ_LESS_IMP]
   ,REFL_TAC
 ]]]
]);

(* ******************************************************************* *)
(* Continue to imitate enumeralTheory with conversion to ordered lists *)
(* As with sets, we supply a general translation, good for any junky   *)
(* tree. As far as can be foreseen, only the better_bt_to_orl, which   *)
(* checks by ORL_bt that the tree is ordered and then uses bt_to_list, *)
(* will be needed in practice.                                         *)
(* ******************************************************************* *)

val bt_to_orl_lb_ub = Define
`(bt_to_orl_lb_ub (cmp:'a toto) lb nt ub = []) /\
 (bt_to_orl_lb_ub cmp lb (node l (x:'a,y:'b) r) ub =
   if apto cmp lb x = LESS then
      if apto cmp x ub = LESS then
            bt_to_orl_lb_ub cmp lb l x ++ [(x,y)] ++ bt_to_orl_lb_ub cmp x r ub
      else bt_to_orl_lb_ub cmp lb l ub
   else bt_to_orl_lb_ub cmp lb r ub)`;

val bt_to_orl_lb = Define
`(bt_to_orl_lb (cmp:'a toto) lb nt = []) /\
 (bt_to_orl_lb cmp lb (node l (x:'a,y:'b) r) =
   if apto cmp lb x = LESS then
            bt_to_orl_lb_ub cmp lb l x ++ [(x,y)] ++ bt_to_orl_lb cmp x r
   else bt_to_orl_lb cmp lb r)`;

val bt_to_orl_ub = Define
`(bt_to_orl_ub (cmp:'a toto) nt ub = []) /\
 (bt_to_orl_ub cmp (node l (x:'a,y:'b) r) ub =
   if apto cmp x ub = LESS then
            bt_to_orl_ub cmp l x ++ [(x,y)] ++ bt_to_orl_lb_ub cmp x r ub
   else bt_to_orl_ub cmp l ub)`;

val bt_to_orl = Define
`(bt_to_orl (cmp:'a toto) nt = []) /\
 (bt_to_orl cmp (node l (x:'a,y:'b) r) =
   bt_to_orl_ub cmp l x ++ [(x,y)] ++ bt_to_orl_lb cmp x r)`;

(* Analogous to "set" as a constant denoting conversion from 'a list to
 'a set, we use "fmap" for conversion from association list to ('a,'b)fmap. *)

val fmap = Define
`fmap (l:('a#'b)list) = FEMPTY |++ REVERSE l`;

val FUPDATE_LIST_FUNION = maybe_thm ("FUPDATE_LIST_FUNION",
``!f l:('a#'b)list g. g |++ l FUNION f = (g FUNION f) |++ l``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [FUPDATE_LIST_THM]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [FUPDATE_LIST_THM, FUNION_FUPDATE_1]
]);

val fmap_rec = maybe_thm ("fmap_rec",
``(fmap ([]:('a#'b)list) = FEMPTY) /\
  (!h:'a#'b l. fmap (h::l) = fmap l |+ h)``,
CONJ_TAC THEN REWRITE_TAC [fmap, REVERSE_DEF, FUPDATE_LIST_THM] THEN
REWRITE_TAC [FUPDATE_LIST_APPEND, FUPDATE_LIST_THM]);

val fmap_NIL = maybe_thm ("fmap_NIL",
``fmap ([]:('a#'b)list) = FEMPTY``,
REWRITE_TAC [fmap_rec]);

val fmap_UNIT = maybe_thm ("fmap_UNIT",
``!h:'a#'b. fmap [h] = FEMPTY |+ h``,
REWRITE_TAC [fmap_rec]);

val fmap_APPEND = maybe_thm ("fmap_APPEND",
``!m n:('a#'b)list. fmap (m ++ n) = fmap m FUNION fmap n``,
RW_TAC (srw_ss ()) [fmap, FUPDATE_LIST_APPEND, REVERSE_APPEND] THEN
REWRITE_TAC [FUPDATE_LIST_FUNION, FUNION_FEMPTY_1]);

(* Show ordered lists represent the right finite maps. *)

val orl_fmap_lb_ub = maybe_thm ("orl_fmap_lb_ub",``!cmp t:('a#'b)bt lb ub.
   bt_to_fmap_lb_ub cmp lb t ub = fmap (bt_to_orl_lb_ub cmp lb t ub)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_to_orl_lb_ub, fmap_NIL, bt_to_fmap_lb_ub,
                     bt_to_fmap, DRESTRICT_FEMPTY]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [bt_to_fmap_lb_ub_mut_rec, bt_to_orl_lb_ub,
                     fmap_APPEND, fmap_UNIT]
]);

val orl_fmap_lb =  maybe_thm ("orl_fmap_lb",``!cmp t:('a#'b)bt lb.
   bt_to_fmap_lb cmp lb t = fmap (bt_to_orl_lb cmp lb t)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_to_orl_lb, fmap_NIL, bt_to_fmap_lb,
                     bt_to_fmap, DRESTRICT_FEMPTY]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [bt_to_fmap_lb_mut_rec, bt_to_orl_lb,
                     fmap_APPEND, fmap_UNIT, orl_fmap_lb_ub]
]);

val orl_fmap_ub =  maybe_thm ("orl_fmap_ub",``!cmp t:('a#'b)bt ub.
   bt_to_fmap_ub cmp t ub = fmap (bt_to_orl_ub cmp t ub)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_to_orl_ub, fmap_NIL, bt_to_fmap_ub,
                     bt_to_fmap, DRESTRICT_FEMPTY]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [bt_to_fmap_ub_mut_rec, bt_to_orl_ub,
                     fmap_APPEND, fmap_UNIT, orl_fmap_lb_ub]
]);

val orl_fmap = maybe_thm ("orl_fmap",
``!cmp t:('a#'b)bt. FMAPAL cmp t = fmap (bt_to_orl cmp t)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_to_orl, fmap_NIL, bt_to_fmap,
                     bt_to_fmap, DRESTRICT_FEMPTY]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [bt_to_fmap_mut_rec, bt_to_orl, fmap_APPEND,
                     fmap_UNIT, orl_fmap_lb, orl_fmap_ub]
]);

(* But we must prove that results from bt_to_orl etc. satisfy ORL cmp. *)

val MEM_MAP_FST_LEM = maybe_thm ("MEM_MAP_FST_LEM",
``!x l:('a#'b)list. MEM x (MAP FST l) <=> ?y. (MEM (x,y) l)``,
GEN_TAC THEN Induct THEN REWRITE_TAC [MAP, MEM] THEN
P_PGEN_TAC ``a:'a,b:'b`` THEN REWRITE_TAC [PAIR_EQ] THEN
EQ_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN AR THENL
[Q.EXISTS_TAC `b` THEN REWRITE_TAC []
,RES_TAC THEN Q.EXISTS_TAC `y` THEN AR
,DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN AR
]);

val ORL_ALT = maybe_thm ("ORL_ALT",
``(!cmp. ORL cmp ([]:('a#'b)list) = T) /\
  (!cmp b a l. ORL cmp ((a:'a,b:'b)::l) <=> ORL cmp l /\
               !p. MEM p (MAP FST l) ==> (apto cmp a p = LESS))``,
REWRITE_TAC [ORL, MEM_MAP_FST_LEM] THEN
CONV_TAC (ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
REPEAT GEN_TAC THEN REFL_TAC);

val ORL_split_lem = maybe_thm ("ORL_split_lem",
``!cmp l x:'a y:'b r. ORL cmp (l ++ [(x,y)] ++ r) <=>
   ORL cmp l /\ (!a. a IN set (MAP FST l) ==> (apto cmp a x = LESS)) /\
   ORL cmp r /\ (!z. z IN set (MAP FST r) ==> (apto cmp x z = LESS))``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [ORL_ALT]
,P_PGEN_TAC ``p:'a,q:'b`` THEN RW_TAC (srw_ss ()) [ORL_ALT] THEN EQ_TAC THEN
 RW_TAC (srw_ss ()) [] THENL
 [POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []
 ,RES_TAC
 ,RES_TAC
 ,Q.UNDISCH_THEN `!a. (a = p) \/ MEM a (MAP FST l) ==> (apto cmp a p' = LESS)`
                 MATCH_MP_TAC THEN REWRITE_TAC []
 ,MATCH_MP_TAC totoLLtrans THEN Q.EXISTS_TAC `x` THEN CONJ_TAC THENL
  [Q.UNDISCH_THEN `!a. (a = p) \/ MEM a (MAP FST l) ==> (apto cmp a x = LESS)`
                 MATCH_MP_TAC THEN REWRITE_TAC []
  ,RES_TAC
]]]);

val bt_orl_ol_lb_ub = maybe_thm ("bt_orl_ol_lb_ub",
``!cmp t:('a#'b)bt lb ub. MAP FST (bt_to_orl_lb_ub cmp lb t ub) =
                          bt_to_ol_lb_ub cmp lb (bt_map FST t) ub``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_ol_lb_ub, bt_to_orl_lb_ub, bt_map, MAP]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss()) [bt_to_ol_lb_ub, bt_to_orl_lb_ub, bt_map, MAP]
]);

val ORL_bt_to_orl_lb_ub = maybe_thm ("ORL_bt_to_orl_lb_ub",
``!cmp t:('a#'b)bt lb ub. ORL cmp (bt_to_orl_lb_ub cmp lb t ub)``,
REWRITE_TAC [ORL_OL_FST, bt_orl_ol_lb_ub, OL_bt_to_ol_lb_ub]);

val bt_orl_ol_lb = maybe_thm ("bt_orl_ol_lb",
``!cmp t:('a#'b)bt lb. MAP FST (bt_to_orl_lb cmp lb t) =
                          bt_to_ol_lb cmp lb (bt_map FST t)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_ol_lb, bt_to_orl_lb, bt_map, MAP]
,P_PGEN_TAC ``x:'a,y:'b`` THEN RW_TAC (srw_ss())
 [bt_to_ol_lb, bt_to_orl_lb, bt_orl_ol_lb_ub, bt_map, MAP]
]);

val ORL_bt_to_orl_lb = maybe_thm ("ORL_bt_to_orl_lb",
``!cmp t:('a#'b)bt lb. ORL cmp (bt_to_orl_lb cmp lb t)``,
REWRITE_TAC [ORL_OL_FST, bt_orl_ol_lb, OL_bt_to_ol_lb]);

val bt_orl_ol_ub = maybe_thm ("bt_orl_ol_ub",
``!cmp t:('a#'b)bt ub. MAP FST (bt_to_orl_ub cmp t ub) =
                          bt_to_ol_ub cmp (bt_map FST t) ub``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_ol_ub, bt_to_orl_ub, bt_map, MAP]
,P_PGEN_TAC ``x:'a,y:'b`` THEN RW_TAC (srw_ss())
 [bt_to_ol_ub, bt_to_orl_ub, bt_orl_ol_lb_ub, bt_map, MAP]
]);

val ORL_bt_to_orl_ub = maybe_thm ("ORL_bt_to_orl_ub",
``!cmp t:('a#'b)bt ub. ORL cmp (bt_to_orl_ub cmp t ub)``,
REWRITE_TAC [ORL_OL_FST, bt_orl_ol_ub, OL_bt_to_ol_ub]);

val bt_orl_ol = maybe_thm ("bt_orl_ol",
``!cmp t:('a#'b)bt. MAP FST (bt_to_orl cmp t) =
                          bt_to_ol cmp (bt_map FST t)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_ol, bt_to_orl, bt_map, MAP]
,P_PGEN_TAC ``x:'a,y:'b`` THEN RW_TAC (srw_ss())
 [bt_to_ol, bt_to_orl, bt_orl_ol_lb, bt_orl_ol_ub, bt_map, MAP]
]);

val ORL_bt_to_orl = maybe_thm ("ORL_bt_to_orl",
``!cmp t:('a#'b)bt. ORL cmp (bt_to_orl cmp t)``,
REWRITE_TAC [ORL_OL_FST, bt_orl_ol, OL_bt_to_ol]);

(* Now, still imitating enumeralTheory, to remove the APPENDs. *)

val bt_to_orl_lb_ub_ac = Define
`(bt_to_orl_lb_ub_ac cmp lb (nt:('a#'b)bt) ub m = m) /\
 (bt_to_orl_lb_ub_ac cmp lb (node l (x:'a,y:'b) r) ub m =
 if apto cmp lb x = LESS then
    if apto cmp x ub = LESS then
      bt_to_orl_lb_ub_ac cmp lb l x ((x,y) :: bt_to_orl_lb_ub_ac cmp x r ub m)
    else bt_to_orl_lb_ub_ac cmp lb l ub m
 else bt_to_orl_lb_ub_ac cmp lb r ub m)`;

val orl_lb_ub_ac_thm = maybe_thm ("orl_lb_ub_ac_thm",
``!cmp t:('a#'b)bt lb ub m. bt_to_orl_lb_ub_ac cmp lb t ub m =
                          bt_to_orl_lb_ub cmp lb t ub ++ m``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ())[bt_to_orl_lb_ub, bt_to_orl_lb_ub_ac]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ())[bt_to_orl_lb_ub, bt_to_orl_lb_ub_ac]
]);

val bt_to_orl_lb_ac = Define
`(bt_to_orl_lb_ac cmp lb (nt:('a#'b)bt) m = m) /\
 (bt_to_orl_lb_ac cmp lb (node l (x:'a,y:'b) r) m =
 if apto cmp lb x = LESS then
      bt_to_orl_lb_ub_ac cmp lb l x ((x,y) :: bt_to_orl_lb_ac cmp x r m)
 else bt_to_orl_lb_ac cmp lb r m)`;

val orl_lb_ac_thm = maybe_thm ("orl_lb_ac_thm",
``!cmp t:('a#'b)bt lb m. bt_to_orl_lb_ac cmp lb t m =
                          bt_to_orl_lb cmp lb t ++ m``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ())[bt_to_orl_lb, bt_to_orl_lb_ac]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ())[bt_to_orl_lb, bt_to_orl_lb_ac, orl_lb_ub_ac_thm]
]);

val bt_to_orl_ub_ac = Define
`(bt_to_orl_ub_ac cmp (nt:('a#'b)bt) ub m = m) /\
 (bt_to_orl_ub_ac cmp (node l (x:'a,y:'b) r) ub m =
 if apto cmp x ub = LESS then
      bt_to_orl_ub_ac cmp l x ((x,y) :: bt_to_orl_lb_ub_ac cmp x r ub m)
 else bt_to_orl_ub_ac cmp l ub m)`;

val orl_ub_ac_thm = maybe_thm ("orl_ub_ac_thm",
``!cmp t:('a#'b)bt ub m. bt_to_orl_ub_ac cmp t ub m =
                         bt_to_orl_ub cmp t ub ++ m``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ())[bt_to_orl_ub, bt_to_orl_ub_ac]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ())[bt_to_orl_ub, bt_to_orl_ub_ac, orl_lb_ub_ac_thm]
]);

val bt_to_orl_ac = Define
`(bt_to_orl_ac cmp (nt:('a#'b)bt) m = m) /\
 (bt_to_orl_ac cmp (node l (x:'a,y:'b) r) m =
      bt_to_orl_ub_ac cmp l x ((x,y) :: bt_to_orl_lb_ac cmp x r m))`;

val orl_ac_thm = maybe_thm ("orl_ac_thm",
``!cmp t:('a#'b)bt m. bt_to_orl_ac cmp t m = bt_to_orl cmp t ++ m``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ())[bt_to_orl, bt_to_orl_ac]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ())[bt_to_orl, bt_to_orl_ac, orl_lb_ac_thm, orl_ub_ac_thm]
]);

(* ********* "ORWL" for (fmap) ORdered With List ************ *)

val ORWL = Define `ORWL cmp (f:'a|->'b) l = (f = fmap l) /\ ORL cmp l`;

val MEM_IN_DOM_fmap = maybe_thm ("MEM_IN_DOM_fmap",
``!cmp l:('a#'b)list. ORL cmp l ==> (!a b. MEM (a,b) l <=>
               a IN FDOM (fmap l) /\ (b = fmap l ' a))``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [FDOM_FEMPTY, fmap_rec, NOT_IN_EMPTY, MEM]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 DISCH_THEN (fn orlc => 
  STRIP_ASSUME_TAC (MATCH_MP (CONJUNCT1 ORL_NOT_MEM) orlc) THEN
  STRIP_ASSUME_TAC (REWRITE_RULE [ORL] orlc)) THEN
 RW_TAC (srw_ss ()) [fmap_rec, FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN
 METIS_TAC []
]);

val ORWL_unique = maybe_thm ("ORWL_unique",
``!cmp f:'a|->'b l m. ORWL cmp f l /\ ORWL cmp f m ==> (l = m)``,
RW_TAC bool_ss [ORWL] THEN
Q.SUBGOAL_THEN `ORL cmp l /\ ORL cmp m`
 (SUBST1_TAC o SYM o MATCH_MP ORL_MEM_EQ) THEN1 AR THEN
P_PGEN_TAC ``a:'a,b:'b`` THEN METIS_TAC [MEM_IN_DOM_fmap]);

val assocv_fmap_thm = maybe_thm ("assocv_fmap_thm",
``!l:('a#'b)list. assocv l = FLOOKUP (fmap l)``,
Induct THEN CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THENL
[RW_TAC (srw_ss()) [assocv, FLOOKUP_DEF, fmap_rec, FDOM_FEMPTY]
,P_PGEN_TAC ``a:'a,b:'b`` THEN
 RW_TAC (srw_ss ()) [assocv, FLOOKUP_DEF, fmap_rec] THENL
 [METIS_TAC []
 ,METIS_TAC [FAPPLY_FUPDATE_THM]
 ,METIS_TAC []
]]);

val fmap_ALT = maybe_thm ("fmap_ALT",
``!l:('a#'b)list. fmap l = unlookup (assocv l)``,
RW_TAC (srw_ss ()) [assocv_fmap_thm, FLOOKUP_unlookup_ID]);

val incr_sort_fmap = maybe_thm ("incr_sort_fmap",
``!cmp l:('a#'b)list. fmap (incr_sort cmp l) = fmap l``,
REWRITE_TAC [fmap_ALT, incr_sort_fun]);

val ORWL_bt_to_orl = store_thm ("ORWL_bt_to_orl",
``!cmp t:('a#'b)bt. ORWL cmp (FMAPAL cmp t) (bt_to_orl cmp t)``,
RW_TAC bool_ss [ORWL, orl_fmap, ORL_bt_to_orl]);

(* We already have the two separate pieces of the above:
   ORL_bt_to_orl = |- !cmp t. ORL cmp (bt_to_orl cmp t)
   orl_fmap = |- !cmp t. FMAPAL cmp t = fmap (bt_to_orl cmp t) *)

val IS_SOME_assocv_rec = maybe_thm ("IS_SOME_assocv_rec",
``(IS_SOME o assocv ([]:('a#'b)list) = {}) /\
  (!a:'a b:'b l. IS_SOME o assocv ((a,b)::l) = a INSERT IS_SOME o assocv l)``,
RW_TAC (srw_ss ()) [assocv, combinTheory.o_THM, EXTENSION, SPECIFICATION] THEN
Cases_on `x = a` THEN RW_TAC (srw_ss ()) []);

val FINITE_assocv = maybe_thm ("FINITE_assocv",
``!l:('a#'b)list. FINITE (IS_SOME o assocv l)``,
Induct THENL
[REWRITE_TAC [FINITE_EMPTY, IS_SOME_assocv_rec]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 ASM_REWRITE_TAC [FINITE_INSERT, IS_SOME_assocv_rec]
]);

val assocv_one_to_one  = maybe_thm ("assocv_one_to_one", Term
`!cmp l m:('a#'b)list. ORL cmp l /\ ORL cmp m ==>
                  (assocv l = assocv m) ==> (l = m)`,
REPEAT GEN_TAC THEN
DISCH_THEN (fn cj => REWRITE_TAC [SYM (MATCH_MP ORL_MEM_EQ cj)]
            THEN STRIP_ASSUME_TAC cj) THEN
REPEAT STRIP_TAC THEN
Q.SPEC_TAC (`ab`,`ab`) THEN P_PGEN_TAC ``a:'a,b:'b`` THEN
IMP_RES_THEN (REWRITE_TAC o ulist o GSYM) assocv_MEM_thm THEN AR);

(* Prove bt_to_orl inverts list_to_bt for ordered lists, using above lemmas. *)

val ORL_fmap_EQ = maybe_thm ("ORL_fmap_EQ",
``!cmp l m:('a#'b)list. ORL cmp l /\ ORL cmp m ==>
                        ((fmap l = fmap m) <=> (l = m))``,
REPEAT GEN_TAC THEN
DISCH_THEN (ASSUME_TAC o MATCH_MP assocv_one_to_one) THEN EQ_TAC THENL
[REWRITE_TAC [fmap_ALT] THEN METIS_TAC [FINITE_assocv, unlookup_11]
,STRIP_TAC THEN AR
]);

(* OFU, UFO imitate OU, UO from enumeralTheory respectively *)

val OFU = Define`OFU cmp (f:'a|->'b) (g:'a|->'b) =
                 DRESTRICT f {x | LESS_ALL cmp x (FDOM g)} FUNION g`;

val UFO = Define`UFO cmp (f:'a|->'b) (g:'a|->'b) =
      f FUNION DRESTRICT g {y | !z. z IN FDOM f ==> (apto cmp z y = LESS)}`;

val FDOM_OFU = maybe_thm ("FDOM_OFU",
``!cmp (f:'a|->'b) (g:'a|->'b). FDOM (OFU cmp f g) = OU cmp (FDOM f) (FDOM g)``,
RW_TAC (srw_ss())
 [OFU, OU, LESS_ALL, FDOM_DRESTRICT, EXTENSION, IN_UNION, IN_INTER]);

val FDOM_UFO = maybe_thm ("FDOM_UFO",
``!cmp (f:'a|->'b) (g:'a|->'b). FDOM (UFO cmp f g) = UO cmp (FDOM f) (FDOM g)``,
RW_TAC (srw_ss())
 [UFO, UO, FDOM_DRESTRICT, EXTENSION, IN_UNION, IN_INTER]);

val sing_UFO = maybe_thm ("sing_UFO",
``!cmp x:'a y:'b t:'a|->'b. UFO cmp (FEMPTY |+ (x,y)) t =
  (FEMPTY |+ (x,y)) FUNION (DRESTRICT t {z | apto cmp x z = LESS})``,
RW_TAC (srw_ss ()) [UFO]);

val bt_to_fmap_OFU_UFO = maybe_thm ("bt_to_fmap_OFU_UFO",
``!cmp l x:'a y:'b r. FMAPAL cmp (node l (x,y) r) =
   OFU cmp (FMAPAL cmp l) (UFO cmp (FEMPTY |+ (x,y)) (FMAPAL cmp r))``,
RW_TAC (srw_ss ()) [OFU, bt_to_fmap, LESS_UO_LEM, FDOM_OFU, FDOM_UFO] THEN
REWRITE_TAC [GSYM FUNION_ASSOC] THEN
ONCE_REWRITE_TAC [GSYM sing_UFO] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
AP_TERM_TAC THEN RW_TAC (srw_ss ()) [UO, LESS_ALL, EXTENSION] THEN
METIS_TAC [totoLLtrans]);

val FAPPLY_OFU = maybe_thm ("FAPPLY_OFU",
``!cmp x u:'a|->'b v:'a|->'b. OFU cmp u v ' x =
   if LESS_ALL cmp x (FDOM v) then u ' x else v ' x``,
RW_TAC (srw_ss ()) [OFU, FDOM_OFU, FUNION_DEF, DRESTRICT_DEF] THEN
`x NOTIN FDOM u` by METIS_TAC [] THEN
`x NOTIN FDOM v` by METIS_TAC [LESS_ALL, all_cpn_distinct, toto_equal_eq] THEN
IMP_RES_THEN SUBST1_TAC NOT_FDOM_FAPPLY_FEMPTY THEN REFL_TAC);

val OFU_FEMPTY = maybe_thm ("OFU_FEMPTY",
``!cmp t:'a|->'b. OFU cmp t FEMPTY = t``,
RW_TAC (srw_ss ()) [fmap_EXT, OU_EMPTY, FDOM_OFU, FAPPLY_OFU, LESS_ALL]);

val FEMPTY_OFU = maybe_thm ("FEMPTY_OFU",
``!cmp f:'a|->'b. OFU cmp FEMPTY f = f``,
RW_TAC (srw_ss ())
 [fmap_EXT, EMPTY_OU, FDOM_OFU, FAPPLY_OFU] THEN
  `~LESS_ALL cmp x (FDOM f)` by RW_TAC (srw_ss ()) [LESS_ALL]
  THEN1 (Q.EXISTS_TAC `x` THEN RW_TAC (srw_ss ()) [toto_refl]) THEN AR);

val LESS_ALL_OFU = maybe_thm ("LESS_ALL_OFU",
``!cmp x u:'a|->'b v:'a|->'b. LESS_ALL cmp x (FDOM (OFU cmp u v)) <=>
                          LESS_ALL cmp x (FDOM u) /\ LESS_ALL cmp x (FDOM v)``,
METIS_TAC  [FDOM_OFU, LESS_ALL_OU]);

val OFU_ASSOC = maybe_thm ("OFU_ASSOC",
``!cmp f g h:'a|->'b. OFU cmp f (OFU cmp g h) = OFU cmp (OFU cmp f g) h``,
RW_TAC bool_ss [fmap_EXT, FDOM_OFU, OU_ASSOC] THEN
RW_TAC bool_ss [FAPPLY_OFU, FUNION_DEF, OFU, LESS_ALL_OFU] THEN METIS_TAC []);

val bl_to_fmap = Define
`(bl_to_fmap cmp (nbl:('a#'b)bl) = FEMPTY) /\
 (bl_to_fmap cmp (zerbl b) = bl_to_fmap cmp b) /\
 (bl_to_fmap cmp (onebl (x,y) t b) =
  OFU cmp (FEMPTY |+ (x,y) FUNION
           DRESTRICT (FMAPAL cmp t) {z | apto cmp x z = LESS})
          (bl_to_fmap cmp b))`;

val bl_to_fmap_OFU_UFO = maybe_thm ("bl_to_fmap_OFU_UFO",
``!cmp x:'a y:'b t b. bl_to_fmap cmp (onebl (x,y) t b) =
  OFU cmp (UFO cmp (FEMPTY |+ (x,y)) (FMAPAL cmp t)) (bl_to_fmap cmp b)``,
REWRITE_TAC [bl_to_fmap, sing_UFO]);

val bl_rev_fmap_lem = maybe_thm ("bl_rev_fmap_lem", ``!cmp b t:('a#'b)bt.
 FMAPAL cmp (bl_rev t b) = OFU cmp (FMAPAL cmp t) (bl_to_fmap cmp b)``,
GEN_TAC THEN Induct THEN TRY (GEN_TAC THEN P_PGEN_TAC ``x:'a,y:'b``) THEN
RW_TAC (srw_ss ()) [bl_rev, bl_to_fmap_OFU_UFO] THEN
REWRITE_TAC [bl_to_fmap, OFU_FEMPTY, bt_to_fmap_OFU_UFO, OFU_ASSOC]);

(* Converting a bl to a bt preserves the represented fmap. *)

val bl_to_bt_fmap = maybe_thm ("bl_to_bt_fmap",
``!cmp b:('a#'b)bl. FMAPAL cmp (bl_to_bt b) = bl_to_fmap cmp b``,
REWRITE_TAC [bl_to_bt, bl_rev_fmap_lem, bt_to_fmap, FEMPTY_OFU]);

(* Imitating enumeralTheory as usual, we next aim to show that building a 
   bl from a list does the same, and to begin with that 

    LESS_ALL cmp x (FDOM (bl_to_fmap cmp b)) ==>
    (bl_to_fmap cmp (BL_CONS (x,y) b) = bl_to_fmap cmp b |+ (x,y),

   or generalizing to suit BL_ACCUM, that

    LESS_ALL cmp x (FDOM (FMAPAL cmp t)) /\
    LESS_ALL cmp x (FDOM (bl_to_fmap cmp b)) ==>
       (bl_to_fmap cmp (BL_ACCUM (x,y) t b) =
       (OFU cmp (FMAPAL cmp t) (bl_to_fmap cmp b)) |+ (x,y) .  *)

val LESS_ALL_UFO_LEM = maybe_thm ("LESS_ALL_UFO_LEM",
``!cmp x:'a y:'b f. LESS_ALL cmp x (FDOM f) ==>
                    (UFO cmp (FEMPTY |+ (x,y)) f = f |+ (x,y))``,
RW_TAC (srw_ss ()) [LESS_ALL, UFO, fmap_EXT, FUNION_DEF, DRESTRICT_DEF,
                    EXTENSION, FAPPLY_FUPDATE_THM] THEN
METIS_TAC []);

val LESS_ALL_OFU_UFO_LEM = maybe_thm ("LESS_ALL_OFU_UFO_LEM",
``!cmp x:'a y:'b f g. LESS_ALL cmp x (FDOM f) /\ LESS_ALL cmp x (FDOM g) ==>
(OFU cmp (UFO cmp (FEMPTY |+ (x,y)) f) g = (OFU cmp f g) |+ (x,y))``,
REPEAT STRIP_TAC THEN IMP_RES_THEN (REWRITE_TAC o ulist)  LESS_ALL_UFO_LEM THEN
RW_TAC (srw_ss ()) [fmap_EXT] THENL
[REWRITE_TAC [FDOM_OFU, FDOM_FUPDATE] THEN
 IMP_RES_THEN SUBST1_TAC (GSYM LESS_ALL_UO_LEM) THEN
 IMP_RES_TAC LESS_ALL_OU_UO_LEM
,RW_TAC (srw_ss ()) [FAPPLY_OFU, FAPPLY_FUPDATE_THM] THEN RES_TAC
]);

val DRESTRICT_SUPERSET = maybe_thm ("DRESTRICT_SUPERSET",
``!f:'a|->'b s. FDOM f SUBSET s ==> (DRESTRICT f s = f)``,
RW_TAC (srw_ss ()) [DRESTRICT_DEF, SUBSET_DEF, fmap_EXT] THEN
METIS_TAC [EXTENSION, IN_INTER]);

val SING_FUNION = maybe_thm ("SING_FUNION",
``!f x:'a y:'b. FEMPTY |+ (x,y) FUNION f = f |+ (x,y)``,
RW_TAC (srw_ss ())
 [fmap_EXT, FUNION_DEF, FAPPLY_FUPDATE_THM, GSYM INSERT_SING_UNION]);

val BL_ACCUM_fmap = maybe_thm ("BL_ACCUM_fmap",
``!cmp x:'a y:'b b t. LESS_ALL cmp x (FDOM (FMAPAL cmp t)) /\
                      LESS_ALL cmp x (FDOM (bl_to_fmap cmp b)) ==>
   (bl_to_fmap cmp (BL_ACCUM (x,y) t b) =
    OFU cmp (FMAPAL cmp t) (bl_to_fmap cmp b) |+ (x,y))``,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct THEN
TRY (GEN_TAC THEN P_PGEN_TAC ``p:'a,q:'b``) THEN
RW_TAC (srw_ss ()) [BL_ACCUM, bl_to_fmap_OFU_UFO, bt_to_fmap_OFU_UFO] THENL
[METIS_TAC [LESS_ALL_UFO_LEM, LESS_ALL_OFU_UFO_LEM, bl_to_fmap]
,METIS_TAC [LESS_ALL_UFO_LEM, LESS_ALL_OFU_UFO_LEM, bl_to_fmap]
,REWRITE_TAC  [bl_to_fmap] THEN
 `LESS_ALL cmp x (FDOM (UFO cmp (FEMPTY |+ (p,q)) (FMAPAL cmp b0))) /\
  LESS_ALL cmp x (FDOM (bl_to_fmap cmp b))` by
 ASM_REWRITE_TAC [GSYM LESS_ALL_OFU] THEN
 `LESS_ALL cmp x (FDOM (FMAPAL cmp (node t (p,q) b0)))`
 by ASM_REWRITE_TAC [bt_to_fmap_OFU_UFO, LESS_ALL_OFU] THEN
 RES_TAC THEN ASM_REWRITE_TAC [bt_to_fmap_OFU_UFO, OFU_ASSOC]
]);

val BL_CONS_fmap = maybe_thm ("BL_CONS_fmap",
``!cmp x:'a y:'b b. LESS_ALL cmp x (FDOM (bl_to_fmap cmp b)) ==>
      (bl_to_fmap cmp (BL_CONS (x,y) b) = bl_to_fmap cmp b |+ (x,y))``,
REPEAT STRIP_TAC THEN REWRITE_TAC [BL_CONS] THEN
Q.SUBGOAL_THEN `OFU cmp (FMAPAL cmp nt) (bl_to_fmap cmp b) = bl_to_fmap cmp b`
(SUBST1_TAC o SYM)
THEN1 REWRITE_TAC [bt_to_fmap, FEMPTY_OFU] THEN
`LESS_ALL cmp x (FDOM (FMAPAL cmp nt))`
by REWRITE_TAC [LESS_ALL, NOT_IN_EMPTY, bt_to_fmap, FDOM_FEMPTY] THEN
IMP_RES_TAC BL_ACCUM_fmap THEN AR);

val list_to_bl_fmap = maybe_thm ("list_to_bl_fmap",
``!cmp l:('a#'b)list. ORL cmp l ==>
   (bl_to_fmap cmp (list_to_bl l) = fmap l)``,
GEN_TAC THEN Induct THEN TRY (P_PGEN_TAC ``x:'a, y:'b``) THEN
RW_TAC (srw_ss ()) [bl_to_fmap, list_to_bl, fmap_rec, ORL] THEN
RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC BL_CONS_fmap THEN
RES_THEN SUBST1_TAC THEN METIS_TAC [MEM_IN_DOM_fmap, LESS_ALL]);

val bt_to_orl_ID = maybe_thm ("bt_to_orl_ID",
``!cmp. !l::ORL cmp. bt_to_orl cmp (list_to_bt l) = (l:('a#'b)list)``,
GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN
REWRITE_TAC [SPECIFICATION] THEN GEN_TAC THEN DISCH_TAC THEN
Q.SUBGOAL_THEN `ORL cmp (bt_to_orl cmp (list_to_bt l)) /\ ORL cmp l`
(REWRITE_TAC o ulist o GSYM o MATCH_MP ORL_fmap_EQ)
THEN1 ASM_REWRITE_TAC [ORL_bt_to_orl] THEN
IMP_RES_THEN (SUBST1_TAC o SYM) list_to_bl_fmap THEN
REWRITE_TAC [GSYM bl_to_bt_fmap, list_to_bt, orl_fmap]);

val bt_to_orl_ID_IMP = save_thm ("bt_to_orl_ID_IMP", REWRITE_RULE
 [SPECIFICATION] (CONV_RULE (ONCE_DEPTH_CONV RES_FORALL_CONV) bt_to_orl_ID));

(* bt_to_orl_ID_IMP = !cmp l. ORL cmp l ==> (bt_to_orl cmp (list_to_bt l) = l)*)

val orl_to_bt_ID = maybe_thm ("orl_to_bt_ID", ``!cmp t:('a#'b)bt.
                 FMAPAL cmp (list_to_bt (bt_to_orl cmp t)) = FMAPAL cmp t``,
METIS_TAC [bt_to_orl_ID_IMP, orl_fmap, ORL_bt_to_orl]);

(* ************************************************************************* *)
(* *********************** Now to prove merge_fmap ************************* *)
(* ************************************************************************* *)

val assocv_MEM_MAP_THE = maybe_thm ("assocv_MEM_MAP_THE",
``!x f:'a->'b option l. MEM x l /\ ALL_DISTINCT l /\ IS_SOME (f x) ==>
                       (assocv (MAP (\x. (x, THE (f x))) l) x = f x)``,
GEN_TAC THEN GEN_TAC THEN Induct THEN
REWRITE_TAC [MEM, ALL_DISTINCT, MAP] THEN BETA_TAC THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [assocv] THENL
[UNDISCH_TAC (Term`IS_SOME ((f:'a->'b option) x)`) THEN
 ASM_REWRITE_TAC [option_CLAUSES]
,COND_CASES_TAC THENL
 [UNDISCH_TAC (Term`MEM (x:'a) l`) THEN AR
 ,RES_TAC]]);

(* ********* merge_smerge not used, but seems hygienic *********** *)

val merge_smerge = maybe_thm ("merge_smerge", ``!cmp l m:('a#'b)list.
         MAP FST (merge cmp l m) = smerge cmp (MAP FST l) (MAP FST m)``,
GEN_TAC THEN Induct THEN TRY (P_PGEN_TAC ``a:'a,b:'b``) THEN
RW_TAC (srw_ss ()) [merge_thm] THEN
Induct_on `m` THEN TRY (P_PGEN_TAC ``c:'a,d:'b``) THEN
Cases_on `apto cmp a c` THEN
RW_TAC (srw_ss ()) [smerge, smerge_nil, merge_thm, MAP]);

val IS_SOME_assocv = maybe_thm ("IS_SOME_assocv",
``!l:('a#'b)list. IS_SOME o (assocv l) = set (MAP FST l)``,
CONV_TAC (QUANT_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [combinTheory.o_THM] THEN Induct THENL
[RW_TAC (srw_ss ()) [assocv, LIST_TO_SET, combinTheory.C_THM]
,P_PGEN_TAC (Term`y:'a,z:'b`) THEN GEN_TAC THEN
 ASM_REWRITE_TAC [assocv, LIST_TO_SET_THM, MAP, FST, HD] THEN
 CONV_TAC (RAND_CONV (REWR_CONV (GSYM SPECIFICATION))) THEN
 REWRITE_TAC [IN_INSERT] THEN Cases_on `x = y` THEN AR THENL
 [REWRITE_TAC [option_CLAUSES]
 ,REWRITE_TAC [SPECIFICATION]
]]);

val FDOM_assocv = maybe_thm ("FDOM_assocv",
``!l:('a#'b)list. FDOM (unlookup (assocv l)) = set (MAP FST l)``,
GEN_TAC THEN 
MP_TAC (ISPEC ``MAP FST (l:('a#'b)list)`` FINITE_LIST_TO_SET) THEN
REWRITE_TAC [GSYM IS_SOME_assocv] THEN
MATCH_ACCEPT_TAC unlookup_FDOM);

val fmap_FDOM = store_thm ("fmap_FDOM",
``!l:('a#'b)list. FDOM (fmap l) = set (MAP FST l)``,
REWRITE_TAC [fmap, FDOM_FUPDATE_LIST,
              LIST_TO_SET_REVERSE, FDOM_FEMPTY, UNION_EMPTY,
              rich_listTheory.MAP_REVERSE]);

val FUPDATE_LIST_SNOC = maybe_thm ("FUPDATE_LIST_SNOC",
``!l:('a#'b)list fm xy. fm |++ (l ++ [xy]) = (fm |++ l) |+ xy``,
REWRITE_TAC [FUPDATE_LIST_APPEND, FUPDATE_LIST, FOLDL]);

val FINITE_IS_SOME_assocv = maybe_thm ("FINITE_IS_SOME_assocv",
``!l:('a#'b)list. FINITE (IS_SOME o assocv l)``,
REWRITE_TAC [IS_SOME_assocv, FINITE_LIST_TO_SET]);

val fmap_ALT = maybe_thm ("fmap_ALT",
``!l:('a#'b)list. fmap l = unlookup (assocv l)``,
REWRITE_TAC [FUPDATE_ALT, fmap_EXT] THEN GEN_TAC THEN CONJ_TAC THENL
[REWRITE_TAC [fmap_FDOM, FDOM_assocv]
,GEN_TAC THEN 
 REWRITE_TAC [fmap_FDOM, fmap, SPECIFICATION] THEN
 Induct_on `l` THENL
 [REWRITE_TAC [MAP, LIST_TO_SET_THM, rrs NOT_IN_EMPTY]
 ,P_PGEN_TAC ``y:'a,v:'b`` THEN
  ASSUME_TAC (ISPEC ``(y:'a,v:'b)::l`` FINITE_IS_SOME_assocv) THEN
  ASSUME_TAC (SPEC_ALL FINITE_IS_SOME_assocv) THEN
  IMP_RES_THEN (ASSUME_TAC o
   REWRITE_RULE [IS_SOME_assocv, SPECIFICATION]) FUN_FMAP_DEF THEN
  DISCH_THEN (fn ins => MP_TAC ins THEN ASSUME_TAC ins) THEN
  REWRITE_TAC [MAP, FST, LIST_TO_SET_THM, rrs IN_INSERT] THEN
  REWRITE_TAC [REVERSE_DEF, FUPDATE_LIST_SNOC, unlookup] THEN
  Cases_on `x = y` THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE_THM] THENL
  [SUBGOAL_THEN ``set (MAP FST ((y:'a,v:'b)::l)) y`` ASSUME_TAC
   THEN1 REWRITE_TAC [MAP, FST, LIST_TO_SET_THM, rrs IN_INSERT] THEN
   REWRITE_TAC [IS_SOME_assocv] THEN
   RES_THEN (REWRITE_TAC o ulist) THEN
   REWRITE_TAC [THE_DEF, assocv, combinTheory.o_THM]
  ,DISCH_TAC THEN RES_THEN (REWRITE_TAC o ulist) THEN
   ASM_REWRITE_TAC [unlookup, IS_SOME_assocv] THEN
   RES_THEN (REWRITE_TAC o ulist) THEN
   ASM_REWRITE_TAC [combinTheory.o_THM, assocv]
]]]);

val merge_fmap = maybe_thm ("merge_fmap",
``!cmp l m:('a#'b)list. ORL cmp l /\ ORL cmp m ==>
   (fmap (merge cmp l m) = fmap l FUNION fmap m)``,
RW_TAC bool_ss [fmap_ALT] THEN
SUBST1_TAC (MATCH_MP unlookup_FUNION (CONJ
 (Q.SPEC `l` FINITE_IS_SOME_assocv) (Q.SPEC `m` FINITE_IS_SOME_assocv))) THEN
AP_TERM_TAC THEN IMP_RES_TAC merge_fun);

(* *** Summary theorems, with and without restricted quantification: **** *)

val ORL_FUNION = maybe_thm ("ORL_FUNION",
``!cmp. !l:('a#'b)list m::ORL cmp. ORL cmp (merge cmp l m) /\
            (fmap (merge cmp l m) = fmap l FUNION fmap m)``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, merge_ORL, merge_fmap]);

val ORL_FUNION_IMP = save_thm ("ORL_FUNION_IMP", REWRITE_RULE [SPECIFICATION]
                       (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) ORL_FUNION));

(* ORL_FUNION_IMP = |- !cmp l. ORL cmp l ==> !m. ORL cmp m ==>
   ORL cmp (merge cmp l m) /\ (fmap (merge cmp l m) = fmap l FUNION fmap m) *)

val FMAPAL_FUNION = maybe_thm ("FMAPAL_FUNION",
``!cmp f g:('a#'b)bt.
  FMAPAL cmp (list_to_bt (merge cmp (bt_to_orl cmp f) (bt_to_orl cmp g))) =
  FMAPAL cmp f FUNION FMAPAL cmp g``,
RW_TAC bool_ss [orl_fmap] THEN
`ORL cmp (bt_to_orl cmp f) /\ ORL cmp (bt_to_orl cmp g)`
by REWRITE_TAC [ORL_bt_to_orl] THEN
`ORL cmp (merge cmp (bt_to_orl cmp f) (bt_to_orl cmp g))`
by IMP_RES_TAC merge_ORL THEN
IMP_RES_THEN SUBST1_TAC bt_to_orl_ID_IMP THEN
IMP_RES_TAC merge_fmap);

(* We really need a merge-like computation rule for DRESTRICT. It might
   be that and a logarithmic rule for IN FDOM wd. be enough for now.    *)

val FMAPAL_FDOM_THM = store_thm ("FMAPAL_FDOM_THM",
``(!cmp x:'a. x IN FDOM (FMAPAL cmp (nt:('a#'b)bt)) = F) /\
  (!cmp x a:'a b:'b l r. x IN FDOM (FMAPAL cmp (node l (a,b) r)) =
        case apto cmp x a of
             LESS => x IN FDOM (FMAPAL cmp l)
          | EQUAL => T
        | GREATER => x IN FDOM (FMAPAL cmp r))``,
RW_TAC (srw_ss ()) [IN_bt_to_set, bt_FST_FDOM, bt_map] THEN
Q.SUBGOAL_THEN `(x = a) <=> (apto cmp x a = EQUAL)` SUBST1_TAC
THEN1 MATCH_ACCEPT_TAC (GSYM toto_equal_eq) THEN
Cases_on `apto cmp x a` THEN
RW_TAC (srw_ss ()) [GSYM toto_antisym]);

(* *********************************************************************** *)
(* inter_merge, for domain restriction, followed by diff_merge, for        *)
(* domain restriction to the complement, are shown to implement DRESTRICT. *)
(* *********************************************************************** *)

val inter_merge = Define
`(inter_merge cmp [] [] = []) /\
 (inter_merge cmp ((a:'a,b:'b)::l) ([]:'a list) = []) /\
 (inter_merge cmp [] (y:'a::m) = []) /\
 (inter_merge cmp ((a,b)::l) (y::m) = case apto cmp a y of
      LESS => inter_merge cmp l (y::m)
   | EQUAL => (a,b) :: inter_merge cmp l m
 | GREATER => inter_merge cmp ((a,b)::l) m)`;

val inter_merge_ind = theorem "inter_merge_ind";

(* inter_merge_ind = |- !P.
     (!cmp. P cmp [] []) /\ (!cmp a b l. P cmp ((a,b)::l) []) /\
     (!cmp y m. P cmp [] (y::m)) /\
     (!cmp a b l y m.
        ((apto cmp a y = EQUAL) ==> P cmp l m) /\
        ((apto cmp a y = GREATER) ==> P cmp ((a,b)::l) m) /\
        ((apto cmp a y = LESS) ==> P cmp l (y::m)) ==>
        P cmp ((a,b)::l) (y::m)) ==>
     !v v1 v2. P v v1 v2 *)

val inter_merge_subset_inter = maybe_thm ("inter_merge_subset_inter",
``!cmp:'a toto l:('a#'b)list m.
  !x z. MEM (x,z) (inter_merge cmp l m) ==> MEM (x,z) l /\ MEM x m``,
HO_MATCH_MP_TAC inter_merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC [inter_merge, MEM] THEN
Cases_on `apto cmp a y` THEN
REWRITE_TAC [all_cpn_distinct] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [cpn_case_def] THENL
[METIS_TAC [MEM]
,`a = y` by IMP_RES_TAC toto_equal_eq THEN
 RW_TAC bool_ss [MEM] THEN DISJ2_TAC THEN RES_TAC
,METIS_TAC [MEM]
]);

val LESS_NOT_MEM = maybe_thm ("LESS_NOT_MEM",
``!cmp x m y:'a. (apto cmp x y = LESS) /\ OL cmp (y::m) ==> ~MEM x m``,
GEN_TAC THEN GEN_TAC THEN Induct THEN RW_TAC (srw_ss ()) [MEM] THENL
[METIS_TAC [OL, MEM, totoLLtrans, toto_glneq]
,IMP_RES_TAC OL THEN
 `apto cmp x h = LESS` by (MATCH_MP_TAC totoLLtrans THEN
                           Q.EXISTS_TAC `y` THEN AR THEN
                           METIS_TAC [OL, MEM]) THEN
 RES_TAC
]);

val inter_subset_inter_merge = maybe_thm ("inter_subset_inter_merge",
``!cmp:'a toto l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
   !x z. MEM (x,z) l /\ MEM x m ==> MEM (x,z) (inter_merge cmp l m)``,
HO_MATCH_MP_TAC inter_merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC [inter_merge, MEM] THEN
Cases_on `apto cmp a y` THEN
REWRITE_TAC [all_cpn_distinct, MEM] THEN STRIP_TAC THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [cpn_case_def] THENL
[`a <> y` by IMP_RES_TAC toto_glneq THEN ASM_REWRITE_TAC [PAIR_EQ] THEN
 IMP_RES_TAC LESS_NOT_MEM THEN
 `ORL cmp l` by IMP_RES_TAC ORL THEN METIS_TAC []
,`a = y` by IMP_RES_TAC toto_equal_eq THEN ASM_REWRITE_TAC [MEM, PAIR_EQ] THEN
 `OL cmp m` by IMP_RES_TAC OL THEN
 `ORL cmp l` by IMP_RES_TAC ORL THEN
 IMP_RES_TAC ORL_NOT_MEM THEN METIS_TAC []
,`a <> y` by IMP_RES_TAC toto_glneq THEN
 IMP_RES_TAC LESS_NOT_MEM THEN
 `OL cmp m` by IMP_RES_TAC OL THEN
 IMP_RES_TAC toto_antisym THEN IMP_RES_TAC ORL_NOT_MEM THEN
 `y <> a` by IMP_RES_TAC toto_glneq THEN
 REPEAT STRIP_TAC THENL
 [METIS_TAC [PAIR_EQ]
 ,METIS_TAC []
 ,METIS_TAC [MEM, ORL_NOT_MEM]
 ,METIS_TAC []
]]);

val inter_merge_MEM_thm = maybe_thm ("inter_merge_MEM_thm",
``!cmp:'a toto l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
 (!x y. MEM (x,y) (inter_merge cmp l m) <=> MEM (x,y) l /\ MEM x m)``,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[MATCH_ACCEPT_TAC inter_merge_subset_inter
,IMP_RES_TAC inter_subset_inter_merge THEN STRIP_TAC THEN RES_TAC
]);

val FST_inter_merge = maybe_thm ("FST_inter_merge",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
 (set (MAP FST (inter_merge cmp l m)) = set (MAP FST l) INTER set m)``,
RW_TAC (srw_ss ())
 [inter_merge_MEM_thm, EXTENSION, IN_LIST_TO_SET, MEM_MAP_FST_LEM] THEN
CONV_TAC (LAND_CONV EXISTS_AND_CONV) THEN REFL_TAC);

val inter_merge_ORL = maybe_thm ("inter_merge_ORL",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
                        ORL cmp (inter_merge cmp l m)``,
GEN_TAC THEN Induct THEN TRY (P_PGEN_TAC ``x:'a,y:'b``) THEN Induct THEN
RW_TAC (srw_ss ()) [inter_merge] THEN REWRITE_TAC [ORL] THEN
IMP_RES_TAC ORL THEN IMP_RES_TAC OL THEN
Cases_on `apto cmp x h` THEN RW_TAC (srw_ss ()) [] THEN
RW_TAC bool_ss [ORL] THEN IMP_RES_TAC inter_merge_subset_inter THEN RES_TAC);

val IN_IS_SOME_NOT_NONE = maybe_thm ("IN_IS_SOME_NOT_NONE",
``!x f:'a->'b option. (f x = NONE) ==> ~(x IN IS_SOME o f)``,
REWRITE_TAC [SPECIFICATION, combinTheory.o_THM] THEN
METIS_TAC [option_CLAUSES]);

val inter_merge_fmap = maybe_thm ("inter_merge_fmap",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
   (fmap (inter_merge cmp l m) = DRESTRICT (fmap l) (set m))``,
RW_TAC bool_ss
 [fmap_ALT, fmap_EXT, FDOM_assocv, DRESTRICT_DEF, FST_inter_merge] THEN
REWRITE_TAC [unlookup] THEN
`x IN set (MAP FST (inter_merge cmp l m))`
 by (IMP_RES_TAC FST_inter_merge THEN AR) THEN
`x IN set (MAP FST l)` by IMP_RES_TAC IN_INTER THEN
`x IN IS_SOME o assocv (inter_merge cmp l m) /\ x IN IS_SOME o assocv l`
 by ASM_REWRITE_TAC [IS_SOME_assocv] THEN
`FINITE (IS_SOME o assocv (inter_merge cmp l m)) /\ FINITE (IS_SOME o assocv l)`
 by REWRITE_TAC [FINITE_IS_SOME_assocv] THEN
IMP_RES_TAC FUN_FMAP_DEF THEN ASM_REWRITE_TAC [combinTheory.o_THM] THEN
AP_TERM_TAC THEN
STRIP_ASSUME_TAC (ISPEC ``assocv (l:('a#'b)list) x`` option_nchotomy) THENL
[METIS_TAC [IN_IS_SOME_NOT_NONE]
,AR THEN
 Q.SUBGOAL_THEN `ORL cmp (inter_merge cmp l m)`
 (REWRITE_TAC o ulist o MATCH_MP assocv_MEM_thm)
 THEN1 IMP_RES_TAC inter_merge_ORL THEN
 REWRITE_TAC [MATCH_MP inter_merge_MEM_thm
              (CONJ (Q.ASSUME `ORL cmp l`) (Q.ASSUME `OL cmp m`))] THEN
 CONJ_TAC THENL
 [METIS_TAC [assocv_MEM_thm]
 ,METIS_TAC [IN_INTER, IN_LIST_TO_SET]
]]);

(* *** Summary theorems, with and without restricted quantification: **** *)

val ORL_DRESTRICT = maybe_thm ("ORL_DRESTRICT",
``!cmp. !l:('a#'b)list::ORL cmp. !m::OL cmp. ORL cmp (inter_merge cmp l m) /\
            (fmap (inter_merge cmp l m) = DRESTRICT (fmap l) (set m))``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, inter_merge_ORL, inter_merge_fmap]);

val ORL_DRESTRICT_IMP = save_thm ("ORL_DRESTRICT_IMP",
REWRITE_RULE [SPECIFICATION]
             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) ORL_DRESTRICT));

(* ORL_DRESTRICT_IMP = |- !cmp l. ORL cmp l ==> !m. OL cmp m ==>
       ORL cmp (inter_merge cmp l m) /\
       (fmap (inter_merge cmp l m) = DRESTRICT (fmap l) (set m)) *)

val FMAPAL_DRESTRICT = maybe_thm ("FMAPAL_DRESTRICT",
``!cmp f:('a#'b)bt s:'a bt.
 FMAPAL cmp (list_to_bt (inter_merge cmp (bt_to_orl cmp f) (bt_to_ol cmp s))) =
 DRESTRICT (FMAPAL cmp f) (ENUMERAL cmp s)``,
RW_TAC bool_ss [orl_fmap, ol_set] THEN
`ORL cmp (bt_to_orl cmp f) /\ OL cmp (bt_to_ol cmp s)`
by REWRITE_TAC [ORL_bt_to_orl, OL_bt_to_ol] THEN
`ORL cmp (inter_merge cmp (bt_to_orl cmp f) (bt_to_ol cmp s))`
by IMP_RES_TAC inter_merge_ORL THEN
IMP_RES_THEN SUBST1_TAC bt_to_orl_ID_IMP THEN
IMP_RES_TAC inter_merge_fmap);

(* ********* Do the the corresponding stuff for diff_merge ******* *)

val diff_merge = Define
`(diff_merge cmp [] [] = []) /\
 (diff_merge cmp ((a:'a,b:'b)::l) ([]:'a list) = (a,b)::l) /\
 (diff_merge cmp [] (y:'a::m) = []) /\
 (diff_merge cmp ((a,b)::l) (y::m) = case apto cmp a y of
      LESS => (a,b) :: diff_merge cmp l (y::m)
   | EQUAL => diff_merge cmp l m
 | GREATER => diff_merge cmp ((a,b)::l) m)`;

val diff_merge_ind = theorem "diff_merge_ind";

(* diff_merge_ind = |- !P.
     (!cmp. P cmp [] []) /\ (!cmp a b l. P cmp ((a,b)::l) []) /\
     (!cmp y m. P cmp [] (y::m)) /\
     (!cmp a b l y m.
        ((apto cmp a y = EQUAL) ==> P cmp l m) /\
        ((apto cmp a y = GREATER) ==> P cmp ((a,b)::l) m) /\
        ((apto cmp a y = LESS) ==> P cmp l (y::m)) ==>
        P cmp ((a,b)::l) (y::m)) ==>
     !v v1 v2. P v v1 v2 *)

val inter_subset_diff_merge = maybe_thm ("inter_subset_diff_merge",
``!cmp:'a toto l:('a#'b)list m.
 !x z. MEM (x,z) l /\ ~MEM x m ==> MEM (x,z) (diff_merge cmp l m)``,
HO_MATCH_MP_TAC diff_merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC [diff_merge, MEM] THEN
Cases_on `apto cmp a y` THEN
REWRITE_TAC [all_cpn_distinct] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC [cpn_case_def] THENL
[METIS_TAC [MEM]
,`a = y` by IMP_RES_TAC toto_equal_eq THEN
 RW_TAC bool_ss [MEM] THEN RES_TAC
,METIS_TAC [MEM]
]);

val diff_merge_subset_inter = maybe_thm ("diff_merge_subset_inter",
``!cmp:'a toto l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
   !x z. MEM (x,z) (diff_merge cmp l m) ==> MEM (x,z) l /\ ~MEM x m``,
HO_MATCH_MP_TAC diff_merge_ind THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC [diff_merge, MEM] THEN
Cases_on `apto cmp a y` THEN
REWRITE_TAC [all_cpn_distinct, MEM] THEN STRIP_TAC THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [cpn_case_def] THENL
[`a <> y` by IMP_RES_TAC toto_glneq THEN
 IMP_RES_TAC LESS_NOT_MEM THEN
 `OL cmp m` by IMP_RES_TAC OL THEN
 IMP_RES_TAC ORL_NOT_MEM THEN
 IMP_RES_TAC toto_antisym THEN `y <> a` by IMP_RES_TAC toto_glneq THEN
 IMP_RES_TAC ORL THEN
 REPEAT STRIP_TAC THENL
 [IMP_RES_TAC MEM THENL
  [ASM_REWRITE_TAC [GSYM PAIR_EQ]
  ,DISJ2_TAC THEN RES_TAC
  ]
 ,METIS_TAC [MEM]
 ,METIS_TAC [MEM, PAIR_EQ]
 ]
,`a = y` by IMP_RES_TAC toto_equal_eq THEN ASM_REWRITE_TAC [MEM, PAIR_EQ] THEN
 `OL cmp m` by IMP_RES_TAC OL THEN
 `ORL cmp l` by IMP_RES_TAC ORL THEN
 IMP_RES_TAC ORL_NOT_MEM THEN METIS_TAC []
,`a <> y` by IMP_RES_TAC toto_glneq THEN ASM_REWRITE_TAC [PAIR_EQ] THEN
 IMP_RES_TAC toto_antisym THEN IMP_RES_TAC LESS_NOT_MEM THEN
 `OL cmp m` by IMP_RES_TAC OL THEN
 METIS_TAC [MEM, PAIR_EQ, ORL_NOT_MEM]
]);

val diff_merge_MEM_thm = maybe_thm ("diff_merge_MEM_thm",
``!cmp:'a toto l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
 (!x y. MEM (x,y) (diff_merge cmp l m) <=> MEM (x,y) l /\ ~MEM x m)``,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN IMP_RES_TAC diff_merge_subset_inter THEN AR
,MATCH_ACCEPT_TAC inter_subset_diff_merge
]);

val FST_diff_merge = maybe_thm ("FST_diff_merge",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
 (set (MAP FST (diff_merge cmp l m)) = set (MAP FST l) DIFF set m)``,
RW_TAC (srw_ss ())
 [diff_merge_MEM_thm, EXTENSION, IN_LIST_TO_SET, MEM_MAP_FST_LEM] THEN
CONV_TAC (LAND_CONV EXISTS_AND_CONV) THEN REFL_TAC);

val diff_merge_ORL = maybe_thm ("diff_merge_ORL",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
                        ORL cmp (diff_merge cmp l m)``,
GEN_TAC THEN Induct THEN TRY (P_PGEN_TAC ``x:'a,y:'b``) THEN Induct THEN
RW_TAC (srw_ss ()) [diff_merge] THEN REWRITE_TAC [ORL] THEN
IMP_RES_TAC ORL THEN IMP_RES_TAC OL THEN
Cases_on `apto cmp x h` THEN RW_TAC (srw_ss ()) [] THEN
RW_TAC bool_ss [ORL] THEN IMP_RES_TAC diff_merge_subset_inter THEN RES_TAC);

val INTER_OVER_DIFF = maybe_thm ("INTER_OVER_DIFF",
``!a b c:'a set. a INTER (b DIFF c) = a INTER b DIFF a INTER c``,
RW_TAC bool_ss [EXTENSION, IN_INTER, IN_DIFF] THEN tautLib.TAUT_TAC);

val INTER_COMPL_DIFF = maybe_thm ("INTER_COMPL_DIFF",
``!a b:'a set. a INTER (COMPL b) = a DIFF b``,
RW_TAC bool_ss [EXTENSION, IN_INTER, IN_DIFF, IN_COMPL]);

val diff_merge_fmap = maybe_thm ("diff_merge_fmap",
``!cmp l:('a#'b)list m. ORL cmp l /\ OL cmp m ==>
   (fmap (diff_merge cmp l m) = DRESTRICT (fmap l) (COMPL (set m)))``,
RW_TAC bool_ss [fmap_ALT, fmap_EXT, FDOM_assocv, DRESTRICT_DEF,
                FST_diff_merge, INTER_COMPL_DIFF] THEN
REWRITE_TAC [unlookup] THEN
`x IN set (MAP FST (diff_merge cmp l m))`
 by (IMP_RES_TAC FST_diff_merge THEN AR) THEN
`x IN set (MAP FST l)` by IMP_RES_TAC IN_DIFF THEN
`x IN IS_SOME o assocv (diff_merge cmp l m) /\ x IN IS_SOME o assocv l`
 by ASM_REWRITE_TAC [IS_SOME_assocv] THEN
`FINITE (IS_SOME o assocv (diff_merge cmp l m)) /\ FINITE (IS_SOME o assocv l)`
 by REWRITE_TAC [FINITE_IS_SOME_assocv] THEN
IMP_RES_TAC FUN_FMAP_DEF THEN ASM_REWRITE_TAC [combinTheory.o_THM] THEN
AP_TERM_TAC THEN
STRIP_ASSUME_TAC (ISPEC ``assocv (l:('a#'b)list) x`` option_nchotomy) THENL
[METIS_TAC [IN_IS_SOME_NOT_NONE]
,AR THEN
 Q.SUBGOAL_THEN `ORL cmp (diff_merge cmp l m)`
 (REWRITE_TAC o ulist o MATCH_MP assocv_MEM_thm)
 THEN1 IMP_RES_TAC diff_merge_ORL THEN
 REWRITE_TAC [MATCH_MP diff_merge_MEM_thm
              (CONJ (Q.ASSUME `ORL cmp l`) (Q.ASSUME `OL cmp m`))] THEN
 CONJ_TAC THENL
 [METIS_TAC [assocv_MEM_thm]
 ,METIS_TAC [IN_DIFF, IN_LIST_TO_SET]
]]);

(* *** Summary theorems, with and without restricted quantification: **** *)

val ORL_DRESTRICT_COMPL = maybe_thm ("ORL_DRESTRICT_COMPL",
``!cmp. !l:('a#'b)list::ORL cmp. !m::OL cmp. ORL cmp (diff_merge cmp l m) /\
(fmap (diff_merge cmp l m) = DRESTRICT (fmap l) (COMPL (set m)))``,
CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
RW_TAC (srw_ss ()) [SPECIFICATION, diff_merge_ORL, diff_merge_fmap]);

val ORL_DRESTRICT_COMPL_IMP = save_thm ("ORL_DRESTRICT_COMPL_IMP",
REWRITE_RULE [SPECIFICATION]
             (CONV_RULE (DEPTH_CONV RES_FORALL_CONV) ORL_DRESTRICT_COMPL));

(* ORL_DRESTRICT_COMPL_IMP = |- !cmp l. ORL cmp l ==> !m. OL cmp m ==>
       ORL cmp (diff_merge cmp l m) /\
       (fmap (diff_merge cmp l m) = DRESTRICT (fmap l) (COMPL (set m))) *)

val FMAPAL_DRESTRICT_COMPL = maybe_thm ("FMAPAL_DRESTRICT_COMPL",
``!cmp f:('a#'b)bt s:'a bt.
FMAPAL cmp (list_to_bt (diff_merge cmp (bt_to_orl cmp f) (bt_to_ol cmp s))) =
DRESTRICT (FMAPAL cmp f) (COMPL (ENUMERAL cmp s))``,
RW_TAC bool_ss [orl_fmap, ol_set] THEN
`ORL cmp (bt_to_orl cmp f) /\ OL cmp (bt_to_ol cmp s)`
by REWRITE_TAC [ORL_bt_to_orl, OL_bt_to_ol] THEN
`ORL cmp (diff_merge cmp (bt_to_orl cmp f) (bt_to_ol cmp s))`
by IMP_RES_TAC diff_merge_ORL THEN
IMP_RES_THEN SUBST1_TAC bt_to_orl_ID_IMP THEN
IMP_RES_TAC diff_merge_fmap);

(* ********************************************************************* *)
(*                  Theorems to assist conversions                       *)
(* ********************************************************************* *)

val FMAPAL_fmap = store_thm ("FMAPAL_fmap",
``!cmp l:('a#'b)list. fmap l = FMAPAL cmp (list_to_bt (incr_sort cmp l))``,
REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV (REWR_CONV (GSYM incr_sort_fmap))) THEN
Q.SUBGOAL_THEN
`incr_sort cmp l = bt_to_orl cmp (list_to_bt (incr_sort cmp l))`
SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_orl_ID_IMP) THEN MATCH_ACCEPT_TAC incr_sort_ORL
,REWRITE_TAC [orl_to_bt_ID, orl_fmap]
]);

val ORL_FMAPAL = store_thm ("ORL_FMAPAL",
``!cmp l:('a#'b)list. ORL cmp l ==> (fmap l = FMAPAL cmp (list_to_bt l))``,
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN
`l = bt_to_orl cmp (list_to_bt l)` SUBST1_TAC THENL
[MATCH_MP_TAC (GSYM bt_to_orl_ID_IMP) THEN AR
,REWRITE_TAC [orl_to_bt_ID, orl_fmap]
]);

val bt_to_orl_thm = maybe_thm ("bt_to_orl_thm",
``!cmp t:('a#'b)bt. bt_to_orl cmp t = bt_to_orl_ac cmp t []``,
RW_TAC (srw_ss ()) [orl_ac_thm]);

val ORWL_FUNION_THM = store_thm ("ORWL_FUNION_THM", ``!cmp s:'a|->'b l t m.
    ORWL cmp s l /\ ORWL cmp t m ==> ORWL cmp (s FUNION t) (merge cmp l m)``,
METIS_TAC [ORWL, ORL_FUNION_IMP]);

val ORWL_DRESTRICT_THM = store_thm ("ORWL_DRESTRICT_THM",``!cmp s:'a|->'b l t m.
ORWL cmp s l /\ OWL cmp t m ==> ORWL cmp (DRESTRICT s t)(inter_merge cmp l m)``,
METIS_TAC [OWL, ORWL, ORL_DRESTRICT_IMP]);

val ORWL_DRESTRICT_COMPL_THM = store_thm ("ORWL_DRESTRICT_COMPL_THM",
``!cmp s:'a|->'b l t m. ORWL cmp s l /\ OWL cmp t m ==>
                        ORWL cmp (DRESTRICT s (COMPL t)) (diff_merge cmp l m)``,
METIS_TAC [OWL, ORWL, ORL_DRESTRICT_COMPL_IMP]);

val bt_map_ACTION = maybe_thm ("bt_map_ACTION",
``!f:'b->'c g:'a->'b t:'a bt. bt_map f (bt_map g t) = bt_map (f o g) t``,
GEN_TAC THEN GEN_TAC THEN Induct THEN RW_TAC (srw_ss ()) [bt_map]);

(* The following may be useful for o_f_CONV, and more so for tc_CONV. *)

val AP_SND = Define`AP_SND (f:'b->'c) (a:'a,b:'b) = (a, f b)`;

val FST_two_ways = prove (
``!f:'b->'c. FST o AP_SND f = (FST:'a#'b->'a)``,
GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN
P_PGEN_TAC ``a:'a,b:'b`` THEN RW_TAC (srw_ss ()) [combinTheory.o_THM, AP_SND]);

val o_f_bt_map = store_thm ("o_f_bt_map",
``!cmp f:'b -> 'c t:('a#'b)bt.
   f o_f FMAPAL cmp t = FMAPAL cmp (bt_map (AP_SND f) t)``,
REPEAT GEN_TAC THEN REWRITE_TAC [fmap_EXT, FDOM_o_f] THEN CONJ_TAC THENL
[REWRITE_TAC [bt_FST_FDOM, bt_map_ACTION, FST_two_ways]
,GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
 Induct_on `t` THENL
 [REWRITE_TAC [bt_FST_FDOM, bt_to_set, bt_map, NOT_IN_EMPTY]
 ,P_PGEN_TAC ``a:'a,b:'b`` THEN
  DISCH_THEN (fn infd => ASSUME_TAC infd THEN
              IMP_RES_THEN (REWRITE_TAC o ulist)
                           (REWRITE_RULE [GSYM o_f_FDOM] o_f_DEF) THEN
              MP_TAC (REWRITE_RULE [FMAPAL_FDOM_THM] infd)) THEN
  REWRITE_TAC [bt_map, AP_SND, FAPPLY_node] THEN
  Cases_on `apto cmp x a` THEN RW_TAC (srw_ss ()) []
]]);

(* **** following is for INSERT - {} sets, adapted to fmap etc. **** *)

val FAPPLY_fmap_NIL = store_thm ("FAPPLY_fmap_NIL",
``!x:'a. fmap ([]:('a#'b)list) ' x = FEMPTY ' x``,
RW_TAC (srw_ss ()) [fmap, FUPDATE_LIST_THM]);

val FAPPLY_fmap_CONS = store_thm ("FAPPLY_fmap_CONS",
``!x y:'a z:'b l. fmap ((y,z)::l) ' x =
   if x = y then z else fmap l ' x``,
RW_TAC (srw_ss ()) [fmap, FUPDATE_LIST_SNOC, FAPPLY_FUPDATE_THM]);

val fmap_CONS = maybe_thm ("fmap_CONS",
``!x:'a y:'b l. fmap ((x,y)::l) = fmap l |+ (x,y)``,
RW_TAC (srw_ss ()) [fmap, FUPDATE_LIST_SNOC, FAPPLY_FUPDATE_THM]);

val o_f_FUPDATE_ALT = maybe_thm ("o_f_FUPDATE_ALT",
``!f:'b->'c fm:'a|->'b k v. f o_f fm |+ (k,v) = (f o_f fm) |+ (k,f v)``,
REPEAT GEN_TAC THEN
REWRITE_TAC [fmap_EXT, FDOM_o_f, FDOM_FUPDATE] THEN
GEN_TAC THEN REWRITE_TAC [IN_INSERT, FAPPLY_FUPDATE_THM, o_f_FAPPLY] THEN
ASM_REWRITE_TAC [o_f_FUPDATE, FAPPLY_FUPDATE_THM] THEN
Cases_on `x = k` THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
`x IN FDOM (fm \\ k)` by METIS_TAC [FDOM_DOMSUB, IN_DELETE] THEN
IMP_RES_TAC o_f_FAPPLY THEN ASM_REWRITE_TAC [DOMSUB_FAPPLY_THM] THEN
`k <> x` by METIS_TAC [] THEN AR);

val o_f_fmap = store_thm ("o_f_fmap",
``!f:'b->'c l:('a#'b)list. f o_f fmap l = fmap (MAP (AP_SND f) l)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [fmap, FUPDATE_LIST_THM]
,P_PGEN_TAC ``y:'a, z:'b`` THEN
 RW_TAC bool_ss [MAP, fmap_CONS, AP_SND, o_f_FUPDATE_ALT]
]);

(* ******************************************************************* *)
(*  Test for a bt with no spurious nodes, as should be invariably the  *)
(*  case, and justify quicker bt_to_orl for bt's passing the test,     *)
(*  makes exactly n - 1 comparisons in passing a tree with n nodes.    *)
(*  (A carbon copy of what is done with bt_to_ol in enumeralTheory.)   *)
(* ******************************************************************* *)

val ORL_bt_lb_ub = Define
`(ORL_bt_lb_ub cmp lb (nt:('a#'b) bt) ub = (apto cmp lb ub = LESS)) /\
 (ORL_bt_lb_ub cmp lb (node l (x,y) r) ub = ORL_bt_lb_ub cmp lb l x /\
                                            ORL_bt_lb_ub cmp x r ub)`;

val ORL_bt_lb = Define
`(ORL_bt_lb cmp lb (nt:('a#'b) bt) = T) /\
 (ORL_bt_lb cmp lb (node l (x,y) r) = ORL_bt_lb_ub cmp lb l x /\
                                      ORL_bt_lb cmp x r)`;

val ORL_bt_ub = Define
`(ORL_bt_ub cmp (nt:('a#'b) bt) ub = T) /\
 (ORL_bt_ub cmp (node l (x,y) r) ub = ORL_bt_ub cmp l x /\
                                      ORL_bt_lb_ub cmp x r ub)`;

val ORL_bt = Define
`(ORL_bt cmp (nt:('a#'b) bt) = T) /\
 (ORL_bt cmp (node l (x,y) r) = ORL_bt_ub cmp l x /\ ORL_bt_lb cmp x r)`;

val ORL_bt_lb_ub_lem = maybe_thm ("ORL_bt_lb_ub_lem",
``!cmp t lb ub. ORL_bt_lb_ub cmp lb t ub ==> (apto cmp lb ub = LESS)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [ORL_bt_lb_ub]
,P_PGEN_TAC ``x:'a,y:'b`` THEN
 RW_TAC (srw_ss ()) [ORL_bt_lb_ub] THEN METIS_TAC [totoLLtrans]
]);

val ORL_bt_lb_ub_thm = maybe_thm ("ORL_bt_lb_ub_thm",
``!cmp t:('a#'b) bt lb ub. ORL_bt_lb_ub cmp lb t ub ==>
                      (bt_to_orl_lb_ub cmp lb t ub = bt_to_list t)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_orl_lb_ub, bt_to_list]
,P_PGEN_TAC ``a:'a,b:'b`` THEN
 RW_TAC (srw_ss ()) [ORL_bt_lb_ub, bt_to_orl_lb_ub, bt_to_list] THEN
 METIS_TAC [ORL_bt_lb_ub_lem]
]);

val ORL_bt_lb_thm = maybe_thm ("ORL_bt_lb_thm",
``!cmp t:('a#'b) bt lb. ORL_bt_lb cmp lb t ==>
                   (bt_to_orl_lb cmp lb t = bt_to_list t)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_orl_lb, bt_to_list]
,P_PGEN_TAC ``a:'a,b:'b`` THEN
 RW_TAC (srw_ss ()) [ORL_bt_lb, bt_to_orl_lb, ORL_bt_lb_ub_thm, bt_to_list] THEN
 METIS_TAC [ORL_bt_lb_ub_lem]
]);

val ORL_bt_ub_thm = maybe_thm ("ORL_bt_ub_thm",
``!cmp t:('a#'b) bt ub. ORL_bt_ub cmp t ub ==>
                   (bt_to_orl_ub cmp t ub = bt_to_list t)``,
GEN_TAC THEN Induct THENL
[REWRITE_TAC [bt_to_orl_ub, bt_to_list]
,P_PGEN_TAC ``a:'a,b:'b`` THEN
 RW_TAC (srw_ss ()) [ORL_bt_ub, bt_to_orl_ub, ORL_bt_lb_ub_thm, bt_to_list] THEN
 METIS_TAC [ORL_bt_lb_ub_lem]
]);

val ORL_bt_thm = maybe_thm ("ORL_bt_thm",
``!cmp t:('a#'b) bt. ORL_bt cmp t ==> (bt_to_orl cmp t = bt_to_list t)``,
GEN_TAC THEN Induct THENL (* really Cases, but need !a to use P_PGEN_TAC *)
[REWRITE_TAC [bt_to_orl, bt_to_list]
,P_PGEN_TAC ``a:'a,b:'b`` THEN RW_TAC (srw_ss ())
       [ORL_bt, bt_to_orl, ORL_bt_lb_thm, ORL_bt_ub_thm, bt_to_list]]);

val better_bt_to_orl = store_thm ("better_bt_to_orl",
``!cmp t:('a#'b) bt. bt_to_orl cmp t = if ORL_bt cmp t then bt_to_list_ac t []
                                       else bt_to_orl_ac cmp t []``,
METIS_TAC [ORL_bt_thm, bt_to_list_thm, bt_to_orl_thm]);

(* ****************************************************************** *)
(* Theorems to support FUPDATE_CONV, for both FMAPAL and fmap terms.  *)
(* *** NOTE: FUPDATE_CONV will fail if it is asked to extend the  *** *)
(* *** domain, that is convert f |+ (x,y) where x NOTIN FDOM f,   *** *)
(* *** which could not be done efficiently for a FMAPAL, and      *** *)
(* *** has no clearly best implementation for fmap [ ... ]'s.     *** *)
(* ****************************************************************** *)

(* Making list_rplacv_cn exit directly on its error condition (not finding
   x) and use a continuation otherwise seems like reasonable programming;
   however, encoding the error condition as a return of the empty list
   (since that can never be a successful answer) is a hack, into which I
   am lured to save the bother of using an option type. *)

val list_rplacv_cn = Define
`(list_rplacv_cn (x:'a,y:'b) [] (cn:('a#'b)list -> ('a#'b)list) = []) /\
 (list_rplacv_cn (x,y) ((w,z)::l) cn =
   if x = w then cn ((x,y)::l)
   else list_rplacv_cn (x,y) l (\m. cn ((w,z)::m)))`;

val fmap_FDOM_rec = store_thm ("fmap_FDOM_rec",
``(!x:'a. x IN FDOM (fmap ([]:('a#'b)list)) = F) /\
  (!x w:'a z:'b l. x IN FDOM (fmap ((w,z)::l)) =
                  (x = w) \/ x IN FDOM (fmap l))``,
RW_TAC (srw_ss ()) [fmap_FDOM]);

val list_rplacv_NIL = maybe_thm ("list_rplacv_NIL",
``!x:'a y:'b l cn. (!m. cn m <> []) ==>
 ((list_rplacv_cn (x,y) l cn = []) <=> x NOTIN FDOM (fmap l))``,
GEN_TAC THEN GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss()) [list_rplacv_cn, fmap_FDOM_rec]
,P_PGEN_TAC ``w:'a,z:'b`` THEN
 RW_TAC (srw_ss()) [list_rplacv_cn, fmap_FDOM_rec]
]);

val list_rplacv_cont_lem = maybe_thm ("list_rplacv_cont_lem",
``!x:'a y:'b l cn cn'. list_rplacv_cn (x,y) l cn <> [] ==>
                  (list_rplacv_cn (x,y) l (cn' o cn) =
                   cn' (list_rplacv_cn (x,y) l cn))``,
GEN_TAC THEN GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [list_rplacv_cn]
,P_PGEN_TAC ``w:'a,z:'b`` THEN
 RW_TAC (srw_ss ()) [list_rplacv_cn] THEN RES_TAC THEN
 Q.SUBGOAL_THEN `(\m. cn' (cn ((w,z)::m))) = (cn' o (\m. cn ((w,z)::m)))`
 (ASM_REWRITE_TAC o ulist) THEN
 CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) []
]);

val bool_lem = prove (``!P Q.(if ~P then ~P else P /\ Q) <=> P ==> Q``,
RW_TAC bool_ss [IMP_DISJ_THM]);

val list_rplacv_thm = store_thm ("list_rplacv_thm",
``!x:'a y:'b l.
let ans = list_rplacv_cn (x,y) l (\m.m)
in if ans = [] then x NOTIN FDOM (fmap l)
   else x IN FDOM (fmap l) /\ (fmap l |+ (x,y) = fmap ans)``,
GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [LET_THM] THEN BETA_TAC THEN
Induct THENL
[RW_TAC (srw_ss ()) [list_rplacv_cn, fmap_FDOM, MAP]
,P_PGEN_TAC ``w:'a,z:'b`` THEN
 REWRITE_TAC [list_rplacv_cn, fmap_FDOM_rec] THEN Cases_on `x = w` THEN AR THENL
 [RW_TAC (srw_ss ()) [fmap_CONS]
 ,`!m.(\m. (\m.m) ((w,z)::m)) m <> []` by RW_TAC (srw_ss ()) [] THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) list_rplacv_NIL THEN
  REWRITE_TAC [bool_lem] THEN DISCH_TAC THEN
  `(fmap (list_rplacv_cn (x,y) l (\m.m)) = fmap l |+ (x,y)) /\
   list_rplacv_cn (x,y) l (\m.m) <> []` by METIS_TAC [] THEN
  Q.SUBGOAL_THEN `(\m. (\m.m)((w,z)::m)) = (\m. ((w,z)::m)) o (\m.m)` SUBST1_TAC
  THEN1 (CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) []) THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) list_rplacv_cont_lem THEN BETA_TAC THEN
  ASM_REWRITE_TAC [fmap_CONS] THEN MATCH_MP_TAC FUPDATE_COMMUTES THEN
  CONV_TAC (RAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN AR
]]);

(* *************************************************************** *)
(* Now to treat similarly terms of the form                        *)
(* FMAPAL cmp (node ... ) |+ (x,y), with similar provision that    *)
(* domain will not be extended.                                    *)
(* *************************************************************** *)

val bt_rplacv_cn = Define
`(bt_rplacv_cn cmp (x:'a,y:'b) nt (cn:('a#'b)bt -> ('a#'b)bt) = nt) /\
 (bt_rplacv_cn cmp (x,y) (node l (w,z) r) cn =
   case apto cmp x w of
           LESS => bt_rplacv_cn cmp (x,y) l (\m. cn (node m (w,z) r))
      |   EQUAL => cn (node l (x,y) r)
      | GREATER => bt_rplacv_cn cmp (x,y) r (\m. cn (node l (w,z) m)))`;

(* FMAPAL_FDOM_THM (corresp. to fmap_FDOM_rec) has already been proved. *)

val bt_rplacv_nt = maybe_thm ("bt_rplacv_nt",
``!cmp x:'a y:'b t cn. (!m. cn m <> nt) ==>
 ((bt_rplacv_cn cmp (x,y) t cn = nt) <=> x NOTIN FDOM (FMAPAL cmp t))``,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss()) [bt_rplacv_cn, FMAPAL_FDOM_THM]
,P_PGEN_TAC ``w:'a,z:'b`` THEN
 RW_TAC (srw_ss()) [bt_rplacv_cn, FMAPAL_FDOM_THM] THEN
 Cases_on `apto cmp x w` THEN RW_TAC (srw_ss ()) []
]);

val bt_rplacv_cont_lem = maybe_thm ("bt_rplacv_cont_lem",
``!cmp x:'a y:'b t cn cn'. bt_rplacv_cn cmp (x,y) t cn <> nt ==>
                  (bt_rplacv_cn cmp (x,y) t (cn' o cn) =
                   cn' (bt_rplacv_cn cmp (x,y) t cn))``,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss ()) [bt_rplacv_cn]
,P_PGEN_TAC ``w:'a,z:'b`` THEN Cases_on `apto cmp x w` THEN
 RW_TAC (srw_ss ()) [bt_rplacv_cn] THEN RES_TAC THENL
 [Q.SUBGOAL_THEN `(\m. cn' (cn (node m (w,z) t'))) =
                       (cn' o (\m. cn (node m (w,z) t')))`
  (ASM_REWRITE_TAC o ulist)
 ,Q.SUBGOAL_THEN `(\m. cn' (cn (node t (w,z) m))) =
                       (cn' o (\m. cn (node t (w,z) m)))`
  (ASM_REWRITE_TAC o ulist)
 ] THEN
 CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) []
]);

(* FUNION_FUPDATE_1 =
     |- !f g x y. f |+ (x,y) FUNION g = (f FUNION g) |+ (x,y)
   FUNION_FUPDATE_2 =
     (|- !f g x y. f FUNION g |+ (x,y) =
     if x IN FDOM f then f FUNION g else (f FUNION g) |+ (x,y) *)

val FUNION_FUPDATE_HALF_2 = maybe_thm ("FUNION_FUPDATE_HALF_2",
``!f:'a|->'b g x y. x NOTIN FDOM f ==>
                    ((f FUNION g) |+ (x,y) = f FUNION g |+ (x,y))``,
METIS_TAC [FUNION_FUPDATE_2]);

val bt_rplacv_thm = store_thm ("bt_rplacv_thm",
``!cmp x:'a y:'b t.
let ans = bt_rplacv_cn cmp (x,y) t (\m.m)
in if ans = nt then x NOTIN FDOM (FMAPAL cmp t)
else x IN FDOM (FMAPAL cmp t) /\ (FMAPAL cmp t |+ (x,y) = FMAPAL cmp ans)``,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [LET_THM] THEN BETA_TAC THEN
Induct THENL
[RW_TAC (srw_ss ()) [bt_rplacv_cn, FMAPAL_FDOM_THM]
,P_PGEN_TAC ``w:'a,z:'b`` THEN
 REWRITE_TAC [bt_rplacv_cn, FMAPAL_FDOM_THM] THEN
 Cases_on `apto cmp x w` THEN ASM_REWRITE_TAC [cpn_case_def] THENL
 [`!m.(\m. (\m.m) (node m (w,z) t')) m <> nt` by RW_TAC (srw_ss ()) [] THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) bt_rplacv_nt THEN
  REWRITE_TAC [bool_lem] THEN DISCH_TAC THEN
  `(FMAPAL cmp (bt_rplacv_cn cmp (x,y) t (\m.m)) = FMAPAL cmp t |+ (x,y)) /\
   bt_rplacv_cn cmp (x,y) t (\m.m) <> nt` by METIS_TAC [] THEN
  Q.SUBGOAL_THEN
  `(\m. (\m.m)(node m (w,z) t')) = (\m. (node m (w,z) t')) o (\m.m)` SUBST1_TAC
  THEN1 (CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) []) THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) bt_rplacv_cont_lem THEN BETA_TAC THEN
  ASM_REWRITE_TAC [bt_to_fmap, DRESTRICT_FUPDATE] THEN
  Q.SUBGOAL_THEN `x IN {z | apto cmp z w = LESS}` (REWRITE_TAC o ulist)
  THEN1 (CONV_TAC SET_SPEC_CONV THEN AR) THEN
  REWRITE_TAC [FUNION_FUPDATE_1]
 ,RW_TAC (srw_ss ()) [bt_to_fmap] THEN
  ONCE_REWRITE_TAC [GSYM FUNION_FUPDATE_1] THEN
  Q.SUBGOAL_THEN
  `x NOTIN FDOM (DRESTRICT (FMAPAL cmp t) {y | apto cmp y w = LESS})`
  (REWRITE_TAC o ulist o MATCH_MP FUNION_FUPDATE_HALF_2) THENL
  [REWRITE_TAC [FDOM_DRESTRICT, IN_INTER, DE_MORGAN_THM] THEN
   DISJ2_TAC THEN CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN RW_TAC (srw_ss ()) []
  ,IMP_RES_TAC toto_equal_imp_eq THEN ASM_REWRITE_TAC [FUPDATE_EQ]
  ]
 ,`!m.(\m. (\m.m) (node t (w,z) m)) m <> nt` by RW_TAC (srw_ss ()) [] THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) bt_rplacv_nt THEN
  REWRITE_TAC [bool_lem] THEN DISCH_TAC THEN
  `(FMAPAL cmp (bt_rplacv_cn cmp (x,y) t' (\m.m)) = FMAPAL cmp t' |+ (x,y)) /\
   bt_rplacv_cn cmp (x,y) t' (\m.m) <> nt` by METIS_TAC [] THEN
  Q.SUBGOAL_THEN
  `(\m. (\m.m) (node t (w,z) m)) = (\m. (node t (w,z) m)) o (\m.m)` SUBST1_TAC
  THEN1 (CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) []) THEN
  IMP_RES_THEN (REWRITE_TAC o ulist) bt_rplacv_cont_lem THEN BETA_TAC THEN
  ASM_REWRITE_TAC [bt_to_fmap, DRESTRICT_FUPDATE] THEN
  Q.SUBGOAL_THEN `x IN {z | apto cmp w z = LESS}` (REWRITE_TAC o ulist)
  THEN1 (CONV_TAC SET_SPEC_CONV THEN ASM_REWRITE_TAC [GSYM toto_antisym]) THEN
  Q.SUBGOAL_THEN
  `x NOTIN FDOM (DRESTRICT (FMAPAL cmp t) {y | apto cmp y w = LESS} FUNION
                 FEMPTY |+ (w,z))`
  (REWRITE_TAC o ulist o MATCH_MP FUNION_FUPDATE_HALF_2) THEN
  REWRITE_TAC [FDOM_FUNION, IN_UNION, FDOM_DRESTRICT, IN_INTER, DE_MORGAN_THM,
               FDOM_FUPDATE, IN_INSERT, FDOM_FEMPTY, NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
  [DISJ2_TAC THEN CONV_TAC (RAND_CONV SET_SPEC_CONV) THEN RW_TAC (srw_ss ()) []
  ,IMP_RES_TAC (CONJUNCT2 toto_glneq)
]]]);

(* ***************************************************************** *)
(*               Theorems to support FUN_fmap_CONV                   *)
(* ***************************************************************** *)

val FST_PAIR_ID = prove (``!f:'a->'b. FST o (\x. (x,f x)) = I``,
GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ())[combinTheory.o_THM]);

val FUN_fmap_thm = store_thm ("FUN_fmap_thm",
``!f:'a->'b l:'a list. fmap (MAP (\x. (x, f x)) l) = FUN_FMAP f (set l)``,
GEN_TAC THEN Induct THENL
[RW_TAC (srw_ss()) [LIST_TO_SET_THM, FUN_FMAP_DEF, fmap_NIL]
,RW_TAC (srw_ss()) [LIST_TO_SET_THM, FUN_FMAP_DEF, fmap_CONS, fmap_EXT] THENL
 [REWRITE_TAC [FAPPLY_FUPDATE]
 ,REWRITE_TAC [FAPPLY_FUPDATE_THM] THEN
  Cases_on `x = h` THEN AR THEN
  `FINITE (set l)` by MATCH_ACCEPT_TAC FINITE_LIST_TO_SET THEN
  `x IN set l` by ASM_REWRITE_TAC [IN_LIST_TO_SET] THEN
  IMP_RES_TAC FUN_FMAP_DEF THEN AR
]]);

(* ******************* Theorem to support fmap_TO_ORWL ********************* *)

val fmap_ORWL_thm = store_thm ("fmap_ORWL_thm",
``!cmp l:('a#'b)list. ORWL cmp (fmap l) (incr_sort cmp l)``,
REWRITE_TAC [ORWL, incr_sort_fmap, incr_sort_ORL]);

val _ = export_theory ();
val _ = print_theory "-";

end;
