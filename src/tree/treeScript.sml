(* ===================================================================== *)
(* FILE          : mk_tree.sml                                           *)
(* DESCRIPTION   : The definition of a type of (bare) trees. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHORS       : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.07.27                                              *)
(* MODIFIED      : Mike Gordon, John Carroll                             *)
(* DATE          : 26 August 1989                                        *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)

structure treeScript =
struct


(*---------------------------------------------------------------------------
 * Open some of the structures used in the body.
 *---------------------------------------------------------------------------*)
open HolKernel Parse basicHol90Lib Num_conv;
infix THEN ORELSE THENL |->;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val _ = new_theory "tree";


(*---------------------------------------------------------------------------
 * Fetch theorems and definitions from listTheory
 *---------------------------------------------------------------------------*)
val EVERY_DEF    = listTheory.EVERY_DEF
and MAP          = listTheory.MAP
and HD           = listTheory.HD
and TL           = listTheory.TL;
val list_Axiom   = listTheory.list_Axiom
and list_INDUCT  = listTheory.list_INDUCT
and CONS_11      = listTheory.CONS_11
and NULL         = listTheory.NULL
and NOT_CONS_NIL = listTheory.NOT_CONS_NIL
and NOT_NIL_CONS = listTheory.NOT_NIL_CONS
and EVERY_CONJ   = listTheory.EVERY_CONJ;

(*---------------------------------------------------------------------------
 * Need some arithmetic definitions and theorems.
 *---------------------------------------------------------------------------*)


val LESS_OR_EQ		= arithmeticTheory.LESS_OR_EQ;
val EXP   	        = arithmeticTheory.EXP;

val LESS_ADD_1 		= arithmeticTheory.LESS_ADD_1 and
    ADD_SYM		= arithmeticTheory.ADD_SYM and
    EXP_ADD		= arithmeticTheory.EXP_ADD and
    MULT_ASSOC		= arithmeticTheory.MULT_ASSOC and
    MULT_EXP_MONO	= arithmeticTheory.MULT_EXP_MONO and
    MULT_CLAUSES	= arithmeticTheory.MULT_CLAUSES and
    ADD_CLAUSES		= arithmeticTheory.ADD_CLAUSES and
    NOT_ODD_EQ_EVEN	= arithmeticTheory.NOT_ODD_EQ_EVEN and
    LESS_CASES		= arithmeticTheory.LESS_CASES and
    WOP			= arithmeticTheory.WOP and
    num_CASES		= arithmeticTheory.num_CASES and
    NOT_LESS		= arithmeticTheory.NOT_LESS and
    LESS_IMP_LESS_OR_EQ	= arithmeticTheory.LESS_IMP_LESS_OR_EQ and
    LESS_EQ_TRANS	= arithmeticTheory.LESS_EQ_TRANS and
    LESS_EQ_ADD		= arithmeticTheory.LESS_EQ_ADD and
    LESS_TRANS		= arithmeticTheory.LESS_TRANS and
    LESS_EQ_ANTISYM	= arithmeticTheory.LESS_EQ_ANTISYM and
    LESS_EQ 		= arithmeticTheory.LESS_EQ;


(*---------------------------------------------------------------------------
 * Need theorems from prim_recTheory
 *---------------------------------------------------------------------------*)

val INV_SUC_EQ    = prim_recTheory.INV_SUC_EQ and
    PRIM_REC_THM  = prim_recTheory.PRIM_REC_THM and
    LESS_0        = prim_recTheory.LESS_0 and
    LESS_SUC_REFL = prim_recTheory.LESS_SUC_REFL and
    LESS_THM      = prim_recTheory.LESS_THM and
    LESS_SUC      = prim_recTheory.LESS_SUC and
    NOT_LESS_0    = prim_recTheory.NOT_LESS_0 and
    LESS_REFL     = prim_recTheory.LESS_REFL;

(*---------------------------------------------------------------------------
 * Need theorems from numTheory
 *---------------------------------------------------------------------------*)
val NOT_SUC  = numTheory.NOT_SUC;

(*---------------------------------------------------------------------------
 * Create induction tactics.
 *---------------------------------------------------------------------------*)
val INDUCT_TAC = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC;
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* Define a one-to-one coding function from (num)list -> num:		*)
(*									*)
(* The coding function used will be iteration of (2n + 1) (2 ^ p)...	*)
(* --------------------------------------------------------------------- *)

(* First a few arithmetic lemmas:					*)
val arith_lemma = prove
 (--`!p q n m.
     (p < q) ==>
     (~(((SUC(n + n)) * (2 EXP p)) = ((SUC(m + m)) * (2 EXP q))))`--,
    REPEAT GEN_TAC THEN
    DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    CONV_TAC (REDEPTH_CONV num_CONV) THEN
    MAP_EVERY ONCE_REWRITE_TAC [[ADD_SYM], [EXP_ADD]] THEN
    REWRITE_TAC [MULT_ASSOC, MULT_EXP_MONO] THEN
    REWRITE_TAC [EXP_ADD, MULT_ASSOC, EXP] THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
    MATCH_ACCEPT_TAC NOT_ODD_EQ_EVEN);

(* The next two theorems state that the function (2n + 1)(2 ^ p) is 1-1	*)
val fun_11_1 = prove
 (--`!p q n m.
      (((SUC(n + n)) * (2 EXP p)) = ((SUC(m + m)) * (2 EXP q))) ==>
      (p = q)`--,
     REPEAT STRIP_TAC THEN
     FIRST_ASSUM (ASSUME_TAC o SYM) THEN
     IMP_RES_TAC (REWRITE_RULE []
		  ((CONV_RULE CONTRAPOS_CONV) (SPEC_ALL arith_lemma))) THEN
     STRIP_ASSUME_TAC (REWRITE_RULE [LESS_OR_EQ]
                                    (SPECL [--`q:num`--,--`p:num`--]
                                           LESS_CASES)) THEN
     RES_TAC);

val fun_11_2 = prove
 (--`!p q n m. (((SUC(n + n)) * (2 EXP p)) = ((SUC(m + m)) * (2 EXP q))) ==>
               (n = m)`--,
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN SUBST_ALL_TAC fun_11_1 THEN
     POP_ASSUM (MP_TAC o (CONV_RULE (DEPTH_CONV num_CONV))) THEN
     REWRITE_TAC [MULT_EXP_MONO, INV_SUC_EQ] THEN
     MAP_EVERY SPEC_TAC [(--`m:num`--,--`m:num`--), (--`n:num`--,--`n:num`--)]
     THEN
     REPEAT (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES]) THENL
     [REWRITE_TAC [NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      REWRITE_TAC [NOT_SUC],
      ASM_REWRITE_TAC [INV_SUC_EQ]]);

(* ---------------------------------------------------------------------*)
(* Representation of trees  ---- :num.					*)
(* ---------------------------------------------------------------------*)

(* The representation type for trees is:  ==`:num`==.			*)
val ty = ==`:num`==;

(*------------------------------------------------------------------------*)
(* node_REP: makes a tree representation from a tree representation list. *)
(* The idea is that the term --`node [t1;t2;t3;t4...]`-- represents the   *)
(* tree  with branches represented by t1, t2, ... etc.			  *)
(* node_REP is defined using the coding function above...		  *)
(*------------------------------------------------------------------------*)
val node_REP = new_recursive_definition
     {name = "node_REP",
      rec_axiom = list_Axiom,
      def = --`(node_REP NIL = 0) /\
               (node_REP (CONS h t) = SUC(h+h) * (2 EXP (node_REP t)))`--};

(* Prove that node_REP is one-to-one:					*)
val node_REP_one_one = prove
 (--`!l1 l2. (node_REP l1 = node_REP l2) = (l1 = l2)`--,
     LIST_INDUCT_TAC THENL
     [LIST_INDUCT_TAC THEN
      REWRITE_TAC [node_REP, NOT_NIL_CONS] THEN
      CONV_TAC (DEPTH_CONV num_CONV) THEN
      REWRITE_TAC [REWRITE_RULE [MULT_CLAUSES]
                    (SPECL [--`p:num`--, --`q:num`--, --`0`--]
                           MULT_EXP_MONO)] THEN
      REWRITE_TAC [NOT_EQ_SYM (SPEC_ALL NOT_SUC)],
      GEN_TAC THEN LIST_INDUCT_TAC THENL
      [REWRITE_TAC [node_REP, NOT_CONS_NIL] THEN
       CONV_TAC (DEPTH_CONV num_CONV) THEN
       REWRITE_TAC [REWRITE_RULE [MULT_CLAUSES]
                    (SPECL [--`p:num`--, --`q:num`--,
                            --`n:num`--, --`0`--]
                           MULT_EXP_MONO)] THEN
       REWRITE_TAC [NOT_SUC],
       REWRITE_TAC [node_REP, CONS_11] THEN
       MAP_EVERY POP_ASSUM [K ALL_TAC,
                            SUBST1_TAC o SYM o SPEC_ALL] THEN
       REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
       [IMP_RES_TAC fun_11_2,
	IMP_RES_TAC fun_11_1,
	ASM_REWRITE_TAC []]]]);

(* ---------------------------------------------------------------------*)
(* DEFINITION of the subset of --`:num`-- that will represent trees...	*)
(* .... and related theorems.						*)
(* ---------------------------------------------------------------------*)

val Is_tree_REP = new_definition("Is_tree_REP",
  --`Is_tree_REP = \t:^(ty_antiq ty).
                     !P. (!tl. (EVERY P tl) ==> P(node_REP tl)) ==>
                         P t`--);

(* A little lemma about EVERY and Is_tree_REP.				*)
val EVERY_Is_tree_REP = prove
 (--`!trl. EVERY Is_tree_REP trl =
	   !P. EVERY (\t.(!tl. EVERY P tl ==> P(node_REP tl)) ==> P t) trl`--,
    REWRITE_TAC [Is_tree_REP] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [EVERY_DEF] THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    RES_TAC THEN ASM_REWRITE_TAC[]);

(* Show that if EVERY Is_tree_REP trl then Is_tree_REP (node_REP v trl). *)
val Is_tree_lemma1 = prove
 (--`!trl. EVERY Is_tree_REP trl ==>  Is_tree_REP (node_REP trl)`--,
     REWRITE_TAC [Is_tree_REP, EVERY_Is_tree_REP] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     GEN_TAC THEN
     DISCH_THEN (fn thm => REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL thm)) THEN
     ASM_REWRITE_TAC [ETA_AX]);

(* A little propositional tautology:					*)
val taut1 = prove
 (--`!a b. ~(a ==> b) = (a /\ ~b)`--,
     REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM]);

(* Show that if t is a tree then it must be of the form --`node_REP tl`--  *)
(* for some v:* and tl (where each object in tl satisfies Is_tree_REP).    *)

val Is_tree_lemma2 = prove
 (--`!t. Is_tree_REP t ==>
         ?trl. EVERY Is_tree_REP trl /\ (t = node_REP trl)`--,
     GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
     SUBST1_TAC (RIGHT_BETA (AP_THM Is_tree_REP (--`t:^(ty_antiq ty)`--))) THEN
     CONV_TAC (REDEPTH_CONV NOT_EXISTS_CONV) THEN
     CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
     DISCH_TAC THEN
     EXISTS_TAC (--`\x:^(ty_antiq ty).
                        ?tl. (EVERY Is_tree_REP tl) /\ (x = node_REP tl)`--)
     THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [taut1] THEN
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC (--`tl:^(ty_antiq ty) list`--) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      SPEC_TAC (--`tl:^(ty_antiq ty) list`--,
                --`tl:^(ty_antiq ty) list`--) THEN
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF] THEN
      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THENL
      [IMP_RES_TAC Is_tree_lemma1 THEN
       RES_TAC THEN ASM_REWRITE_TAC[],
       RES_TAC THEN FIRST_ASSUM ACCEPT_TAC],
      RES_TAC]);

(* Show that Is_tree_REP(node_REP tl) ==> EVERY Is_tree_REP tl		*)
val Is_tree_lemma3 =
   let val spec = SPEC (--`node_REP tl`--) Is_tree_lemma2
       val rew1 = REWRITE_RULE [node_REP_one_one] spec
       val [t1, t2] = CONJUNCTS (SELECT_RULE (UNDISCH rew1))
   in
   GEN_ALL(DISCH_ALL (SUBS [SYM t2] t1))
   end;

(* Main result... of the past few lemmas.				*)
(* Show that !v tl. Is_tree_REP (node_REP v tl) = EVERY Is_tree_REP tl	*)
val Is_tree_lemma4 = prove
 (--`!tl. Is_tree_REP (node_REP tl) = EVERY Is_tree_REP tl`--,
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
      [IMP_RES_TAC Is_tree_lemma3,
       IMP_RES_TAC Is_tree_lemma1 THEN
       POP_ASSUM MATCH_ACCEPT_TAC]);

(* Show that a tree representation exists.				*)
val Exists_tree_REP = prove
 (--`?t:^(ty_antiq ty). Is_tree_REP t`--,
      EXISTS_TAC (--`node_REP NIL`--) THEN
      REWRITE_TAC [Is_tree_REP] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [EVERY_DEF]);

(* ---------------------------------------------------------------------*)
(* Introduction of the new type of trees.				*)
(* ---------------------------------------------------------------------*)

(* Define the new type.							*)
val tree_TY_DEF =
   new_type_definition{name = "tree",
                       pred = rator(#Body(dest_exists(concl Exists_tree_REP))),
                       inhab_thm = Exists_tree_REP};

(* ---------------------------------------------------------------------*)
(* Define a representation function, REP_tree, from the type tree to 	*)
(* the representing type, and the inverse abstraction 			*)
(* function ABS_tree, and prove some trivial lemmas about them.		*)
(* ---------------------------------------------------------------------*)

val tree_ISO_DEF = define_new_type_bijections
                      {name =  "tree_ISO_DEF",
                       ABS = "ABS_tree",
                       REP = "REP_tree",
                       tyax = tree_TY_DEF};

val R_11   = prove_rep_fn_one_one tree_ISO_DEF  and
    R_ONTO = prove_rep_fn_onto tree_ISO_DEF     and
    A_11   = prove_abs_fn_one_one tree_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto tree_ISO_DEF     and
    A_R = CONJUNCT1 tree_ISO_DEF                and
    R_A = CONJUNCT2 tree_ISO_DEF;


(* Definition of node -- the constructor for trees.			*)
val node = new_definition("node",
 --`node tl = ABS_tree (node_REP (MAP REP_tree tl))`--);

(* Definition of dest_node: inverse of node.				*)
val dest_node = new_definition("dest_node",
 --`!t. dest_node t = @p. t = node p`--);

(* ---------------------------------------------------------------------*)
(* Several lemmas about ABS and REP follow...				*)
(* ---------------------------------------------------------------------*)

val IS_REP_lemma = prove
 (--`!tl.EVERY Is_tree_REP (MAP REP_tree (tl: tree list))`--,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [MAP, EVERY_DEF, R_ONTO] THEN
     STRIP_TAC THEN EXISTS_TAC (--`h:tree`--) THEN REFL_TAC);

(* Prove that REP(ABS x) = x.						*)
val REP_ABS_lemma = prove
 (--`!tl. REP_tree(node tl) = node_REP (MAP REP_tree tl)`--,
     REWRITE_TAC [node, SYM(SPEC_ALL R_A)] THEN
     REPEAT GEN_TAC THEN
     REWRITE_TAC [Is_tree_lemma4] THEN
     SPEC_TAC (--`tl:(tree)list`--,--`tl:(tree)list`--) THEN
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [MAP, EVERY_DEF, R_ONTO] THEN
     GEN_TAC THEN EXISTS_TAC (--`h:tree`--) THEN REFL_TAC);

val ABS_REP = prove
 (--`!tl. Is_tree_REP (node_REP (MAP REP_tree tl))`--,
    REWRITE_TAC [Is_tree_lemma4] THEN
    MATCH_ACCEPT_TAC IS_REP_lemma);

val ABS_11_lemma =
   let val a11 = SPECL [--`node_REP (MAP REP_tree tl1)`--,
	                --`node_REP (MAP REP_tree tl2)`--] A_11
   in
   REWRITE_RULE [ABS_REP] a11
   end;

(* Prove that node is one-to-one... save this theorem.			*)
val node_11 = store_thm("node_11",
 --`!tl1 tl2. (node tl1 = node tl2) = (tl1 = tl2)`--,
    REWRITE_TAC [node, ABS_11_lemma,node_REP_one_one] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    MAP_EVERY SPEC_TAC [(--`tl1: tree list`--,--`tl1:tree list`--),
                        (--`tl2:tree list`--,--`tl2:tree list`--)] THEN
    LIST_INDUCT_TAC THENL
    [LIST_INDUCT_TAC THEN REWRITE_TAC [MAP,NOT_CONS_NIL],
     GEN_TAC THEN LIST_INDUCT_TAC THENL
     [REWRITE_TAC [MAP,NOT_EQ_SYM(SPEC_ALL NOT_CONS_NIL)],
      ASM_REWRITE_TAC [MAP,CONS_11,R_11] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]]);

(* Some more lemmas about ABS and REP....				*)

val A_R_list = prove
 (--`!(tl:(tree)list). tl = MAP ABS_tree (MAP REP_tree tl)`--,
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP, A_R, CONS_11] THEN
    POP_ASSUM ACCEPT_TAC);

val R_A_R = prove
 (--`REP_tree(ABS_tree(REP_tree (t:tree))) = (REP_tree t)`--,
     REWRITE_TAC [SYM(SPEC_ALL R_A)] THEN
     REWRITE_TAC [R_ONTO] THEN
     EXISTS_TAC (--`t:tree`--) THEN REFL_TAC);

val Is_R = prove
 (--`Is_tree_REP (REP_tree (t:tree))`--,
     REWRITE_TAC [R_ONTO] THEN
     EXISTS_TAC (--`t:tree`--) THEN REFL_TAC);

val R_A_R_list = prove
 (--`!tl:tree list.
      MAP REP_tree (MAP ABS_tree (MAP REP_tree tl)) = (MAP REP_tree tl)`--,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, R_A_R]);

val A_ONTO_list = prove
 (--`!tl: tree list.
     ?trl.(tl = MAP ABS_tree trl) /\ (EVERY Is_tree_REP trl)`--,
     LIST_INDUCT_TAC THENL
     [EXISTS_TAC (--`NIL:^(ty_antiq ty) list`--) THEN
      REWRITE_TAC [MAP, EVERY_DEF],
      POP_ASSUM STRIP_ASSUME_TAC THEN
      STRIP_TAC THEN
      STRIP_ASSUME_TAC (SPEC (--`h:tree`--) A_ONTO) THEN
      EXISTS_TAC (--`CONS (r:^(ty_antiq ty)) trl`--) THEN
      ASM_REWRITE_TAC [CONS_11, MAP, EVERY_DEF]]);

val R_ONTO_list = prove
 (--`!(trl:^(ty_antiq ty) list).
      EVERY Is_tree_REP trl ==> ?tl. trl = MAP REP_tree tl`--,
     LIST_INDUCT_TAC THENL
     [DISCH_TAC THEN
      EXISTS_TAC (--`NIL:tree list`--) THEN
      REWRITE_TAC [MAP],
      REWRITE_TAC [EVERY_DEF, R_ONTO] THEN
      REPEAT STRIP_TAC THEN
      RES_THEN STRIP_ASSUME_TAC THEN
      EXISTS_TAC (--`CONS (a:tree) tl`--) THEN
      ASM_REWRITE_TAC [MAP]]);

val R_A_list = prove
 (--`!trl. EVERY Is_tree_REP (trl:num list) ==>
           (MAP REP_tree (MAP ABS_tree trl) = trl)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EVERY_DEF, MAP, R_A] THEN
     REPEAT STRIP_TAC THEN
     RES_TAC THEN ASM_REWRITE_TAC[]);

(* A little lemma.							*)
val EVERY_MAP = prove
 (--`!l P f. EVERY P (MAP (f:'a->'b) (l :'a list)) =
             EVERY (\x.P(f x)) l`--,
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, EVERY_DEF] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN REFL_TAC);

(* Two lemmas showing how induction on trees relates to induction on	*)
(* tree representations....						*)
val induct_lemma1 = prove
 (--`(!tl. EVERY P tl ==> (P(node tl))) =
     (!trl. EVERY Is_tree_REP trl ==>
	    EVERY (\x.P(ABS_tree x)) trl ==>
            ((\x.P(ABS_tree x)) (node_REP trl)))`--,
    EQ_TAC THENL
    [DISCH_TAC THEN GEN_TAC THEN
     DISCH_THEN ((STRIP_THM_THEN SUBST1_TAC) o (MATCH_MP R_ONTO_list)) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [SYM(SPEC_ALL EVERY_MAP), SYM(SPEC_ALL A_R_list)] THEN
     ASM_REWRITE_TAC [SYM(SPEC_ALL node)],
     DISCH_TAC THEN GEN_TAC THEN
     STRIP_ASSUME_TAC (SPEC_ALL A_ONTO_list) THEN
     FIRST_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC [node, EVERY_MAP] THEN
     IMP_RES_TAC R_A_list THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     POP_ASSUM (MP_TAC o CONV_RULE BETA_CONV) THEN
     ASM_REWRITE_TAC []]);

val induct_lemma2 = prove
 (--`(!(t:tree). P t:bool) =
     (!rep. Is_tree_REP rep ==>
            (\r. Is_tree_REP r /\ ((\x.P(ABS_tree x)) r)) rep)`--,
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      EQ_TAC THENL
      [CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC [R_ONTO] THEN
       REPEAT STRIP_TAC THENL
       [EXISTS_TAC (--`a:tree`--) THEN FIRST_ASSUM ACCEPT_TAC,
        ASM_REWRITE_TAC [A_R]],
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC (--`t:tree`--) A_ONTO) THEN
       RES_TAC THEN ASM_REWRITE_TAC[]]);

(* Induction on trees.							*)
val tree_Induct = store_thm("tree_Induct",
--`!P. (!tl. EVERY P tl ==> P (node tl)) ==> !t. P t`--,
 REWRITE_TAC [induct_lemma1, induct_lemma2] THEN
 GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
 let val is_thm = RIGHT_BETA (AP_THM Is_tree_REP(--`trep:^(ty_antiq ty)`--))
 in DISCH_THEN (MATCH_MP_TAC o (REWRITE_RULE [is_thm])) end THEN
 REWRITE_TAC [EVERY_CONJ] THEN
 REPEAT STRIP_TAC THEN CONV_TAC BETA_CONV THEN
 RES_TAC THEN ASM_REWRITE_TAC [Is_tree_lemma4]);

(* ---------------------------------------------------------------------*)
(*   tree_INDUCT: thm  -> thm						*)
(*									*)
(*     A |- !tl. EVERY \t.P[t] tl ==> P[node tl]			*)
(* =======================================================		*)
(*               A |- !t. P[t]						*)
(*									*)
(* ---------------------------------------------------------------------*)

local val b = genvar (==`:bool`==)
      val node = (--`node`--)
in
fun tree_INDUCT th =
 let val {Bvar,Body} = dest_forall(concl th)
     val {ant,conseq} = dest_imp Body
     val (EVERY, [P, tll]) = strip_comb ant
     val concth = SYM(RIGHT_BETA
                   (REFL(mk_comb{Rator=P,Rand=mk_comb{Rator=node,Rand=Bvar}})))
     and IND' = SPEC P tree_Induct
     and th' = SPEC Bvar th
     val EVERY_P = mk_comb{Rator=EVERY, Rand=P}
     val right = mk_imp{ant=mk_comb{Rator=EVERY_P,  Rand=Bvar}, conseq = b}
     val th1 = SUBST [b |-> concth] (mk_eq{lhs=concl th', rhs=right})
                     (REFL (concl th'))
      val th2 = GEN Bvar (EQ_MP th1 th')
   in
     CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND' th2)
   end
end;

(* ---------------------------------------------------------------------*)
(*									*)
(* tree_INDUCT_TAC							*)
(*									*)
(*             [A] !t.P[t]						*)
(*  ================================					*)
(*    [A,EVERY \t.P[t] trl] |- P[node trl]				*)
(*									*)
(* ---------------------------------------------------------------------*)


local val trl  = --`trl : tree list`--
      val node = --`node`--
in
fun tree_INDUCT_TAC (A,term) =
   let val {Bvar,Body} = dest_forall term
       val Afrees = free_varsl A
       val t' = variant (free_vars term@Afrees) Bvar
       val body' = subst [{redex = Bvar, residue = t'}] Body
       val trl = variant (free_vars body'@Afrees) trl
       val asm = --`EVERY (\^t'.^body') trl`--
   in
   ([(asm::A, subst[{redex = t',residue = mk_comb{Rator = node,Rand = trl}}]
                   body')],
    fn [thm] => tree_INDUCT (GEN trl (DISCH asm thm)))
   end
end;

(* ---------------------------------------------------------------------*)
(* Definition of a height function on trees...				*)
(*									*)
(* ---------------------------------------------------------------------*)

(* First, define a relation `bht n tr` which is true if tr has height 	*)
(* bounded by n.  I.e. bht n tr = height of tr <= n.			*)
val bht = new_definition("bht",
 --`bht = PRIM_REC
           (\tr. tr = node NIL)
           (\res n tr. ?trl. (tr = node trl) /\ EVERY res trl)`--);

(* Show that bht has the following recursive definition:		*)
val bht_thm = prove
 (--`(bht 0 tr = (tr = node NIL)) /\
     (bht (SUC n) tr = ?trl. (tr = node trl) /\ EVERY (bht n) trl)`--,
    PURE_REWRITE_TAC [bht, PRIM_REC_THM] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN REFL_TAC);

(* Show that if height t <= n then height t <= (SUC n)			*)
val bht_lemma1 = prove
 (--`!n. !(tr:tree). bht n tr ==> bht (SUC n) tr`--,
     INDUCT_TAC THENL
     [REWRITE_TAC [bht_thm] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC (--`NIL:tree list`--) THEN
      ASM_REWRITE_TAC [EVERY_DEF],
      ONCE_REWRITE_TAC [bht_thm] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC (--`trl :tree list`--) THEN
      ASM_REWRITE_TAC [] THEN
      MAP_EVERY POP_ASSUM [MP_TAC, K ALL_TAC] THEN
      SPEC_TAC (--`trl :tree list`--,--`trl :tree list`--) THEN
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [EVERY_DEF] THEN
      REPEAT STRIP_TAC THEN RES_TAC]);

(* show that if height tr <= n then height tr <= n+m			*)
val bht_lemma2 =
    (GEN_ALL o DISCH_ALL o (GEN (--`m:num`--)) o UNDISCH o SPEC_ALL)
    (prove (--`!m n. !(tr:tree). bht n tr ==>  bht (n+m) tr`--,
    	       INDUCT_TAC THEN
	       REWRITE_TAC [ADD_CLAUSES] THEN
	       REPEAT STRIP_TAC THEN
	       RES_TAC THEN IMP_RES_TAC bht_lemma1));

(* show that height bounds for all the trees in a list implies a single	*)
(* bound for all the trees in the list.					*)
val bht_lemma3 = prove
 (--`!trl.EVERY (\tr:tree. ?n. bht n tr) trl ==> ?n. EVERY (bht n) trl`--,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     POP_ASSUM STRIP_ASSUME_TAC THEN
     EXISTS_TAC (--`n+n'`--) THEN
     STRIP_TAC THENL
     [IMP_RES_TAC bht_lemma2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      POP_ASSUM MP_TAC THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN
      SPEC_TAC (--`(trl:(tree)list)`--,--`(trl:(tree)list)`--) THEN
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [EVERY_DEF] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      IMP_RES_TAC bht_lemma2 THEN
      POP_ASSUM MATCH_ACCEPT_TAC]);

(* show that there always exists an n such that height tr <= n.		*)
val exists_bht = prove
 (--`!(tr:tree). ?n. bht n tr`--,
     tree_INDUCT_TAC THEN
     POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP bht_lemma3) THEN
     EXISTS_TAC (--`SUC n`--) THEN
     REWRITE_TAC [bht_thm] THEN
     EXISTS_TAC (--`trl:tree list`--) THEN
     ASM_REWRITE_TAC[]);

(* Show that there is always a minimum bound on the height of a tree.	*)
val min_bht = CONV_RULE (DEPTH_CONV BETA_CONV)
   (prove (--`!(t:tree).
              ?n. (\n. bht n t) n /\ (!m. (m < n) ==> ~((\n. bht n t)m))`--,
           GEN_TAC THEN
           MATCH_MP_TAC WOP THEN
           CONV_TAC (DEPTH_CONV BETA_CONV) THEN
           MATCH_ACCEPT_TAC exists_bht));

(* We can now define our height function as follows:			*)
val HT = new_definition("HT",
 --`HT (t:tree) = @n.  bht n t /\ (!m. (m < n) ==> ~(bht m t))`--);

(* A number of theorems about HT follow:				*)
(* The main thing is to show that:					*)
(* 1) !tl. EVERY (\t. HT t < HT(node tl)) tl				*)
(* 2) !trl. (HT (node trl) = 0) = (trl = NIL)				*)

val HT_thm1 = prove
 (--`!(tr:tree). bht (HT tr) tr`--,
     REWRITE_TAC [HT] THEN
     GEN_TAC THEN
     STRIP_ASSUME_TAC (SELECT_RULE (SPEC (--`tr:tree`--) min_bht)));

val HT_thm2 = prove
 (--`!(tr:tree).!m. (m < (HT tr)) ==> ~(bht m tr)`--,
     REWRITE_TAC [HT] THEN
     GEN_TAC THEN
     STRIP_ASSUME_TAC (SELECT_RULE (SPEC (--`tr:tree`--) min_bht)));

(* A key result about HT.						*)
val HT_leaf = prove
 (--`!trl. (HT (node trl) = 0) = (trl = NIL)`--,
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MP_TAC (SPEC (--`node trl`--) HT_thm1) THEN
      POP_ASSUM SUBST1_TAC THEN
      REWRITE_TAC [bht_thm, node_11] THEN
      STRIP_TAC,
      DISCH_THEN SUBST1_TAC THEN
      STRIP_ASSUME_TAC (SPEC (--`HT(node NIL)`--) num_CASES) THEN
      MP_TAC (SPEC (--`node NIL`--) HT_thm2) THEN
      POP_ASSUM SUBST1_TAC THEN
      REWRITE_TAC [NOT_SUC] THEN
      CONV_TAC NOT_FORALL_CONV THEN
      REWRITE_TAC [taut1] THEN
      EXISTS_TAC (--`0`--) THEN
      REWRITE_TAC [bht_thm, LESS_0]]);

val HT_thm3 = prove
 (--`!m. !(tr:tree). (~(bht m tr)) ==> (m < (HT tr))`--,
     CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
     REWRITE_TAC [NOT_LESS, LESS_OR_EQ] THEN
     REPEAT STRIP_TAC THENL
     [POP_ASSUM
       ((STRIP_THM_THEN SUBST1_TAC) o MATCH_MP LESS_ADD_1) THEN
      STRIP_ASSUME_TAC (SPEC (--`tr:tree`--) HT_thm1) THEN
      IMP_RES_TAC bht_lemma2 THEN POP_ASSUM MATCH_ACCEPT_TAC,
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      MATCH_ACCEPT_TAC HT_thm1]);

val HT_thm4 = prove
 (--`!(tr:tree). !m. (m < (HT tr)) = ~(bht m tr)`--,
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     (map MATCH_ACCEPT_TAC [HT_thm2, HT_thm3]));

(* TFM: fixed error --`tl`-- for --`trl`-- after quantifier. 88.11.17	*)
val HT_thm5 = prove
 (--`!n tl h. ~(bht n (node tl)) ==> ~(bht n (node (CONS h tl)))`--,
    CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
    GEN_TAC THEN STRIP_ASSUME_TAC (SPEC (--`n:num`--) num_CASES) THEN
    ASM_REWRITE_TAC [bht_thm] THEN
    POP_ASSUM (K ALL_TAC) THENL
    [REWRITE_TAC [node_11] THEN
     REPEAT STRIP_TAC THEN
     POP_ASSUM (MP_TAC o (AP_TERM (--`NULL:tree list->bool`--))) THEN
     REWRITE_TAC [NULL],
     REWRITE_TAC [node_11] THEN
     REPEAT STRIP_TAC THEN
     MAP_EVERY POP_ASSUM [MP_TAC, SUBST1_TAC o SYM] THEN
     REWRITE_TAC [EVERY_DEF] THEN STRIP_TAC THEN
     EXISTS_TAC (--`tl:tree list`--) THEN
     ASM_REWRITE_TAC []]);

val HT_thm6 = prove
 (--`!trl tl. !(t:tree).
     EVERY (\t. ~(bht (HT t) (node tl))) trl ==>
     EVERY (\t. ~(bht (HT t) (node (CONS h tl)))) trl`--,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC HT_thm5, RES_TAC]);

(* A key result about HT.						*)
val HT_node = prove
 (--`!tl. EVERY (\t. (HT t) < HT(node tl)) tl`--,
     REWRITE_TAC [HT_thm4] THEN
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT GEN_TAC THEN STRIP_TAC THENL
     [STRIP_ASSUME_TAC (SPEC (--`HT (h:tree)`--) num_CASES) THENL
      [ASM_REWRITE_TAC [bht_thm, node_11, CONS_11] THEN
       DISCH_THEN (MP_TAC o AP_TERM (--`NULL:tree list->bool`--)) THEN
       REWRITE_TAC [NULL],
       MP_TAC (SPEC (--`h:tree`--) HT_thm2) THEN
       ASM_REWRITE_TAC [bht_thm, EVERY_DEF, node_11] THEN
       DISCH_TAC THEN
       CONV_TAC (REDEPTH_CONV NOT_EXISTS_CONV) THEN
       ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN
       ONCE_REWRITE_TAC [SYM(SPEC_ALL IMP_DISJ_THM)] THEN
       REPEAT GEN_TAC THEN
       DISCH_THEN (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [EVERY_DEF, DE_MORGAN_THM] THEN
       DISJ1_TAC THEN
       FIRST_ASSUM MATCH_MP_TAC THEN
       MATCH_ACCEPT_TAC LESS_SUC_REFL],
       IMP_RES_THEN MATCH_ACCEPT_TAC HT_thm6]);

(* The following lemmas are used in the proof of approx_lemma below:	*)

val Less_lemma = prove
 (--`!n m. (n < SUC m) = (n <= m)`--,
     REWRITE_TAC [LESS_OR_EQ] THEN
     CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV DISJ_SYM)) THEN
     MATCH_ACCEPT_TAC LESS_THM);

val less_HT = prove
 (--`!trl m n.
     (m <= n) ==>
     EVERY (\t. HT t < m) trl ==>
     EVERY (\(t:tree). HT t <= n) trl`--,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
      IMP_RES_TAC LESS_EQ_TRANS,
      RES_TAC]);

val less_HT2 = prove
 (--`!trl n. (HT(node trl) < n) ==> EVERY (\t. HT t < n) trl`--,
     REPEAT GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     MP_TAC (SPEC (--`(trl:(tree)list)`--) HT_node) THEN
     SPEC_TAC (--`(HT(node trl))`--,--`n:num`--) THEN
     REWRITE_TAC [ADD_CLAUSES, num_CONV (--`1`--)] THEN
     SPEC_TAC (--`(trl:(tree)list)`--,--`(trl:(tree)list)`--) THEN
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     STRIP_ASSUME_TAC (REWRITE_RULE [LESS_OR_EQ]
                        (SPECL [--`n:num`--, --`p:num`--]
                               LESS_EQ_ADD)) THENL
     [IMP_RES_TAC LESS_TRANS,
      POP_ASSUM (SUBST1_TAC o SYM)] THEN
      IMP_RES_TAC LESS_SUC);

val less_HT3  = prove
 (--`!trl. (HT(node trl) <= HT(node (CONS (node trl) NIL)))`--,
    REPEAT STRIP_TAC THEN
    MP_TAC (SPEC (--`CONS (node trl) NIL`--) HT_node) THEN
    REWRITE_TAC [EVERY_DEF] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ);

val less_HT4 = prove
 (--`!trl m n. (m <= n) ==>
      EVERY (\t. HT t < m) trl ==>
      EVERY (\(t:tree). HT t < n) trl`--,
      PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN (STRIP_THM_THEN
                      (fn th => fn g => SUBST1_TAC th g
                                       handle _ => MP_TAC th g)) THENL
      [MAP_EVERY (fn t => SPEC_TAC(t,t))
                 [--`n:num`--, --`m:num`--,--`trl:tree list`--] THEN
       LIST_INDUCT_TAC THEN REWRITE_TAC [EVERY_DEF] THEN
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THENL [IMP_RES_TAC LESS_TRANS, RES_TAC],
       DISCH_THEN ACCEPT_TAC]);;

val less_HT5 =
   let val spec = SPEC (--`CONS (h:tree) NIL`--) HT_node
       val rew = CONV_RULE (DEPTH_CONV BETA_CONV)
    	                (REWRITE_RULE [EVERY_DEF] spec)
   in  GEN_ALL rew  end;

val less_HT6 =
   let val spec = SPEC (--`CONS (h:tree) trl`--) HT_node
       val rew = CONV_RULE (DEPTH_CONV BETA_CONV)
                           (REWRITE_RULE [EVERY_DEF] spec)
       val less1 = CONJUNCT1(SPEC_ALL rew)
       val spec2 = SPEC (--`node (CONS h trl)`--) (GEN_ALL less_HT5)
   in
   GEN_ALL(MATCH_MP LESS_TRANS (CONJ less1 spec2))
   end;

val less_HT7 =
   let val less1 = (SPEC_ALL HT_node)
       val less2 = (SPEC_ALL less_HT3)
   in
   MATCH_MP (GEN_ALL(MATCH_MP less_HT4 less2)) less1
   end;

val less_HT8 =
   let val sp = REWRITE_RULE [EVERY_DEF]
                   (SPEC (--`CONS (h:tree) trl`--)
                         (GEN_ALL less_HT7))
   in CONJUNCT2 sp end;


(* Show that dest is the destructor for node.				*)
val dest_node_thm = prove
 (--`!tl. dest_node (node tl) = tl`--,
    REWRITE_TAC [dest_node, node_11] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN
    CONV_TAC SELECT_CONV THEN
    EXISTS_TAC (--`tl:tree list`--) THEN
    REFL_TAC);

(* we now show that for all n there is a recursive function that works	*)
(* as desired for trees of height <= n.					*)
val approx_lemma = prove
 (--`!f n. ?fn. !trl.
      (HT(node trl) <= n) ==>
      (fn (node trl) = (f (MAP fn trl):'b))`--,
     GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [NOT_LESS_0, LESS_OR_EQ, HT_leaf] THEN
      EXISTS_TAC (--`\(t:tree). f (NIL:'b list):'b`--) THEN
      REPEAT (STRIP_GOAL_THEN SUBST1_TAC)  THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [MAP],
      POP_ASSUM STRIP_ASSUME_TAC THEN
      REWRITE_TAC [LESS_OR_EQ] THEN REWRITE_TAC [Less_lemma] THEN
      EXISTS_TAC
      (--`\(t:tree). ((HT t) <= n) => (fn t:'b) | f(MAP fn (dest_node t))`--)
      THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [dest_node_thm] THEN
      REPEAT STRIP_TAC THENL
      [RES_TAC THEN ASM_REWRITE_TAC [] THEN
       ASSUME_TAC (SPEC (--`(trl:(tree)list)`--) HT_node) THEN
       IMP_RES_TAC less_HT THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM_LIST (K ALL_TAC) THEN
       DISCH_THEN (fn th => AP_TERM_TAC THEN MP_TAC th) THEN
       SPEC_TAC (--`trl:tree list`--,--`trl:tree list`--) THEN
       LIST_INDUCT_TAC THEN
       REWRITE_TAC [EVERY_DEF, MAP] THEN
       CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[],
       MP_TAC (SPEC (--`trl:tree list`--) HT_node) THEN
       ASM_REWRITE_TAC [Less_lemma, SYM(SPEC_ALL LESS_EQ), LESS_REFL] THEN
       POP_ASSUM_LIST (K ALL_TAC) THEN
       DISCH_THEN (fn th => AP_TERM_TAC THEN MP_TAC th) THEN
       SPEC_TAC (--`trl:tree list`--,--`trl:tree list`--) THEN
       LIST_INDUCT_TAC THEN
       REWRITE_TAC [EVERY_DEF, MAP] THEN
       CONV_TAC (DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

(* Now, define tree_rec_fun n f to be the function that works for trees	*)
(* shorter than n.							*)
val trf = new_definition("trf",
  --`trf n f = @fn. !trl.
                HT(node trl) <= n ==> (fn(node trl):'b = f(MAP fn trl))`--);

(* Prove that trf has the appropriate property.				*)
val trf_thm = prove
 (--`!f n trl. (HT (node trl) <= n) ==>
               (trf n f (node trl):'b = f(MAP (trf n f) trl))`--,
     REWRITE_TAC [trf] THEN
     CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
     MATCH_ACCEPT_TAC approx_lemma);

(* show that trf n f = trf m f for trees shorter than n amd m.		*)
val trf_EQ_thm = prove
 (--`!(t:tree).
     !n m f.
     ((HT t < n) /\ (HT t < m)) ==>
     (trf n f t :'b = trf m f t)`--,
      tree_INDUCT_TAC THEN
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
      IMP_RES_THEN (SUBST1_TAC o SPEC_ALL) trf_thm THEN
      AP_TERM_TAC THEN
      MAP_EVERY POP_ASSUM [K ALL_TAC, K ALL_TAC] THEN
      REPEAT (POP_ASSUM (MP_TAC o MATCH_MP less_HT2)) THEN
      POP_ASSUM MP_TAC THEN
      SPEC_TAC (--`trl:tree list`--,--`trl:tree list`--) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, EVERY_DEF] THEN
      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
      GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN
      DISCH_THEN
         (fn th => ASSUME_TAC th THEN REPEAT STRIP_TAC THEN
                   MP_TAC (SPECL [--`n:num`--,
                                  --`m:num`--,
                                  --`f:'b list -> 'b `--] th)) THEN
      RES_TAC THEN POP_ASSUM SUBST1_TAC THEN
      REWRITE_TAC [CONS_11] THEN
      STRIP_TAC THEN RES_TAC THEN
      FIRST_ASSUM ACCEPT_TAC);

(* extend the above result for lists of trees.				*)
val trf_EQ_thm2 = prove
 (--`!(trl:tree list).
     !n m f.
      (EVERY (\t. (HT t) < n) trl  /\ EVERY (\t. (HT t) < m) trl) ==>
      (MAP (trf n f) trl:'b list = MAP(trf m f) trl)`--,
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP, EVERY_DEF] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC trf_EQ_thm THEN RES_TAC THEN
    REWRITE_TAC[CONS_11] THEN
    CONJ_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC);


(* Now, by taking `\t. trf (HT (node [t])) f t` we have a function that	*)
(* works for all trees t.						*)
val FN_EXISTS = prove
 (--`!f. ?fn. !trl. ((fn (node trl)):'b) = f (MAP fn trl)`--,
    STRIP_TAC THEN
    EXISTS_TAC (--`\t. trf (HT(node (CONS t NIL))) (f:('b)list->'b) t`--) THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC (--`trl: tree list`--) less_HT3) THEN
    IMP_RES_THEN (SUBST1_TAC o SPEC_ALL) trf_thm THEN
    POP_ASSUM (K ALL_TAC) THEN
    AP_TERM_TAC THEN
    SPEC_TAC (--`trl:(tree)list`--,--`trl:(tree)list`--) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [EVERY_DEF,MAP] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [CONS_11] THEN STRIP_TAC THENL
    [MATCH_MP_TAC trf_EQ_thm THEN STRIP_TAC THENL
     [MATCH_ACCEPT_TAC less_HT6,
      MATCH_ACCEPT_TAC less_HT5],
     FIRST_ASSUM (SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC trf_EQ_thm2 THEN
     STRIP_TAC THENL
     [ACCEPT_TAC less_HT8,
      MATCH_ACCEPT_TAC (GEN_ALL less_HT7)]]);

(* Now show that there is a function that produces the desired tree	*)
(* recursive function, given f.						*)
val FN_thm = prove
 (--`?FN. !f. !trl. (FN f) (node trl) = (f (MAP (FN f) trl):'b)`--,
     EXISTS_TAC (--`\f.  @fn. !trl. fn(node trl):'b = f(MAP fn trl)`--)
     THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
     MATCH_ACCEPT_TAC FN_EXISTS);

(* Prove the existence of a certain function AP.			*)
val AP =
    prove_rec_fn_exists list_Axiom
      (--`(!l. AP NIL l = NIL) /\
          (!h t l. AP (CONS h t) l = CONS (h (HD l:'a):'b) (AP t (TL l)))`--);

(* Got to have the types just right for use of AP below.		*)
val AP = INST_TYPE [==`:'a`== |-> ==`:tree`==] AP;
val AP_DEF = strip_conj(#Body(dest_exists(concl AP)));

(* A lemma about AP and MAP.						*)
val AP_MAP = TAC_PROOF
  ((AP_DEF, --`!l. AP (MAP (f:tree->tree->'b) l) l = MAP (\x. f x x) l`--),
            LIST_INDUCT_TAC THEN
	    ASM_REWRITE_TAC [MAP,HD,TL] THEN
	    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	    STRIP_TAC THEN REFL_TAC);

(* Now, prove the existence of the recursively defined functions.	*)
val EXISTS_THM = prove
 (--`!f. ?fn. !tl. fn (node tl):'b = f (MAP fn tl) tl`--,
     STRIP_TAC THEN
     STRIP_ASSUME_TAC (INST_TYPE [==`:'b`== |-> ==`:tree->'b`==] FN_thm) THEN
     STRIP_ASSUME_TAC AP THEN
     let val fn1 =
        --`\(n:tree). ((FN (\fnl:(tree->'b)list.\(n:tree).
		       f (AP fnl (dest_node n): 'b list)
    	    	         (dest_node n):'b)) (n:tree) (n:tree):'b)`--
     in
     EXISTS_TAC fn1
     end THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC [] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [dest_node_thm,AP_MAP]);


(* A little lemma...							*)
val lemma = prove
 (--`!l. EVERY (\x:'a. (f x):'b = g x) l ==> (MAP f l = MAP g l)`--,
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP,EVERY_DEF] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN
    ASM_REWRITE_TAC[]);


(* Finally, prove the theorem for trees!				*)
val tree_Axiom = store_thm("tree_Axiom",
 --`!f. ?!fn. !tl. fn (node tl):'b = f (MAP fn tl) tl`--,
     GEN_TAC THEN
     CONV_TAC EXISTS_UNIQUE_CONV THEN
     STRIP_TAC THENL
     [MATCH_ACCEPT_TAC EXISTS_THM,
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
      tree_INDUCT_TAC THEN
      IMP_RES_TAC lemma THEN
      ASM_REWRITE_TAC []]);

val _ = export_theory();

end;
