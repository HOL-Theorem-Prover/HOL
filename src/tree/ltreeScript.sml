(* ===================================================================== *)
(* FILE          : mk_ltree.sml                                          *)
(* DESCRIPTION   : Theory of polymorphically labelled trees. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.07.27                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure ltreeScript =
struct

(*---------------------------------------------------------------------------
 * Declare parent theory structures.
 *---------------------------------------------------------------------------*)
local open treeTheory combinTheory in end;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)

open HolKernel Parse basicHol90Lib;
infix THEN ORELSE ORELSEC THENL |->;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val _ = new_theory "ltree";

(*---------------------------------------------------------------------------
 * Fetch theorems from tree theory.
 *---------------------------------------------------------------------------*)

val node_11	 = treeTheory.node_11 and
    tree_Induct  = treeTheory.tree_Induct and
    tree_Axiom   = treeTheory.tree_Axiom;

(*---------------------------------------------------------------------------
 * Fetch definitions and theorems from list theory.
 *---------------------------------------------------------------------------*)

val SUM       = listTheory.SUM and
    LENGTH    = listTheory.LENGTH and
    MAP       = listTheory.MAP and
    FLAT      = listTheory.FLAT and
    APPEND    = listTheory.APPEND and
    HD        = listTheory.HD and
    TL        = listTheory.TL and
    EVERY_DEF = listTheory.EVERY_DEF;

val list_Axiom		 = listTheory.list_Axiom and
    list_INDUCT		 = listTheory.list_INDUCT and
    LENGTH_APPEND 	 = listTheory.LENGTH_APPEND and
    LENGTH_NIL		 = listTheory.LENGTH_NIL and
    LENGTH_CONS		 = listTheory.LENGTH_CONS ;

(*---------------------------------------------------------------------------
 * Fetch theorems from combinator theory.
 *---------------------------------------------------------------------------*)

val o_THM = combinTheory.o_THM;

(*---------------------------------------------------------------------------
 * Fetch theorems from arithmetic theory.
 *---------------------------------------------------------------------------*)

val ADD_CLAUSES = arithmeticTheory.ADD_CLAUSES and
    ADD_EQ_0    = arithmeticTheory.ADD_EQ_0;


(*---------------------------------------------------------------------------
 * Fetch theorems from prim_rec theory.
 *---------------------------------------------------------------------------*)

val num_Axiom  = prim_recTheory.num_Axiom and
    INV_SUC_EQ = prim_recTheory.INV_SUC_EQ;

(*---------------------------------------------------------------------------
 * Fetch theorems from pair theory.
 *---------------------------------------------------------------------------*)

val PAIR = pairTheory.PAIR;

(*---------------------------------------------------------------------------
 * Create induction tactics.
 *---------------------------------------------------------------------------*)

val INDUCT_TAC = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC;
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;


(* These next two functions are copied from mk_tree. *)
(* ---------------------------------------------------------------------*)
(*   tree_INDUCT: thm  -> thm						*)
(*									*)
(*     A |- !tl. EVERY \t.P[t] tl ==> P[node tl]			*)
(* =======================================================		*)
(*               A |- !t. P[t]						*)
(*									*)
(* ---------------------------------------------------------------------*)

fun INDUCT_ERR s =
      HOL_ERR{origin_structure="ltreeScript",
              origin_function=s, message=""};

local val b = genvar Type.bool
      val node = Term`node`
      val trl  = Term`trl:tree list`
      fun tree_INDUCT th =
        let val {Bvar,Body} = dest_forall(concl th)
            val {ant,conseq} = dest_imp Body
            val (EVERY, [P, tll]) = strip_comb ant
            val concth = SYM(RIGHT_BETA
                (REFL(mk_comb{Rator=P,Rand=mk_comb{Rator=node,Rand=Bvar}})))
            and IND' = SPEC P tree_Induct
            and th' = SPEC Bvar th
            val EVERY_P = mk_comb{Rator=EVERY, Rand=P}
            val right = mk_imp{ant=mk_comb{Rator=EVERY_P,Rand=Bvar},conseq=b}
            val th1 = SUBST [b |-> concth] (mk_eq{lhs=concl th', rhs=right})
                            (REFL (concl th'))
            val th2 = GEN Bvar (EQ_MP th1 th')
        in
          CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND' th2)
        end
in
fun tree_INDUCT_TAC (A,term) =
   let val {Bvar,Body} = dest_forall term
       val Afrees = free_varsl A
       val t'     = variant (free_vars term@Afrees) Bvar
       val body'  = subst [Bvar |-> t'] Body
       val trl    = variant (free_vars body'@Afrees) trl
       val asm    = Term`EVERY (\^t'.^body') trl`
   in
   ([(asm::A, subst[t' |-> mk_comb{Rator=node,Rand=trl}] body')],
    fn [thm] => tree_INDUCT (GEN trl (DISCH asm thm)))
   end
  handle _ => raise INDUCT_ERR "tree_INDUCT_TAC"
end;


(*----------------------------------------------------------------------*)
(* Define a function size on trees that gives the number of nodes in 	*)
(* a tree.								*)
(*----------------------------------------------------------------------*)

val size = new_definition("size",
 --`size = @fn. (!tl. fn (node tl:tree) = SUC(SUM (MAP fn tl)))`--);

(* Show that size has the desired prim rec defn.			*)

val size_thm = prove
 (--`!tl. size ((node tl):tree) = SUC(SUM (MAP size tl))`--,
      REWRITE_TAC [size] THEN
      CONV_TAC SELECT_CONV THEN
      MP_TAC (SPEC (--`\n. \(tl:(tree)list). SUC(SUM n)`--)
                   (INST_TYPE [{redex =  ==`:'b`==, residue = ==`:num`==}]
                              tree_Axiom)) THEN
      REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
      DISCH_THEN (STRIP_THM_THEN CHECK_ASSUME_TAC));


(* ---------------------------------------------------------------------*)
(* Subset predicate for *ltree and introduction of the new type.	*)
(* ---------------------------------------------------------------------*)

val Is_ltree = new_definition("Is_ltree",
  --`Is_ltree (t,l) = (size (t:tree) = LENGTH (l:'a list))`--);

val ty = Type`:tree # 'a list`;

(* Show that a ltree representation exists.				*)
val Exists_ltree_REP = prove
 (--`?t:^(ty_antiq ty). Is_ltree t`--,
     EXISTS_TAC (--`((node NIL:tree), [@v:'a.T])`--) THEN
     REWRITE_TAC [Is_ltree, LENGTH, size_thm, MAP, SUM]);

(* Define the new type.							*)
val ltree_TY_DEF =
  new_type_definition
     {name = "ltree",
      pred = rator(#Body(dest_exists(concl Exists_ltree_REP))),
      inhab_thm = Exists_ltree_REP};

(* ---------------------------------------------------------------------*)
(* Define a representation function, REP_tree, from the type tree to 	*)
(* the representing type, and the inverse abstraction 			*)
(* function ABS_tree, and prove some trivial lemmas about them.		*)
(* ---------------------------------------------------------------------*)

val ltree_ISO_DEF =
  define_new_type_bijections
     {name = "ltree_ISO_DEF",
      ABS = "ABS_ltree",
      REP = "REP_ltree",
      tyax = ltree_TY_DEF};

val R_11   = prove_rep_fn_one_one ltree_ISO_DEF  and
    R_ONTO = prove_rep_fn_onto ltree_ISO_DEF     and
    A_11   = prove_abs_fn_one_one ltree_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto ltree_ISO_DEF     and
    A_R    = CONJUNCT1 ltree_ISO_DEF             and
    R_A    = CONJUNCT2 ltree_ISO_DEF;

(* Definition of Node.							*)

val Node = new_definition("Node",
 --`Node (v:'a) (tl: 'a ltree list) =
        (ABS_ltree ((node (MAP (FST o REP_ltree) tl)),
                    ((CONS v (FLAT (MAP (SND o REP_ltree) tl))))))`--);

(* A lemma about Rep_ltree(Node v tl)					*)
val REP_Node = prove
 (--`!tl. REP_ltree (Node (v:'a) tl) =
         (node (MAP (FST o REP_ltree) tl),
          CONS v (FLAT (MAP (SND o REP_ltree) tl)))`--,
    REWRITE_TAC [Node, SYM(SPEC_ALL R_A), Is_ltree] THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [size_thm, MAP, LENGTH, FLAT, SUM],
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [size_thm, MAP, LENGTH, FLAT, SUM, LENGTH_APPEND] THEN
     REWRITE_TAC [SYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
     DISCH_THEN SUBST1_TAC THEN
     STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC (--`(h:('a)ltree)`--) A_ONTO) THEN
     MP_TAC (SPEC (--`r:^(ty_antiq ty)`--) R_A) THEN
     ASM_REWRITE_TAC [o_THM] THEN
     DISCH_THEN SUBST1_TAC THEN
     MAP_EVERY POP_ASSUM [MP_TAC, K ALL_TAC] THEN
     ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
     REWRITE_TAC [Is_ltree] THEN
     DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* A lemma about size and LENGTH of the components of REP_ltree t	*)
val size_LENGTH_lemma = prove
 (--`!(t:'a ltree). size (FST (REP_ltree t)) =
                    LENGTH (SND (REP_ltree t))`--,
    GEN_TAC THEN STRIP_ASSUME_TAC (SPEC (--`t:'a ltree`--) A_ONTO) THEN
    MP_TAC (SPEC_ALL R_A) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY POP_ASSUM [MP_TAC, K ALL_TAC] THEN
    ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
    REWRITE_TAC [Is_ltree]);

(* Extend the above thm to lists of REP_ltree				*)
val MAP_size_LENGTH = prove
 (--`!(tl:'a ltree list).
      MAP size (MAP (FST o REP_ltree) tl) =
      MAP LENGTH (MAP (SND o REP_ltree) tl)`--,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, size_thm, LENGTH, size_LENGTH_lemma, o_THM]);

(* ---------------------------------------------------------------------*)
(* In what follows, we define a few list processing functions.  These	*)
(* are rather special purpose.  But they are defined constants here,	*)
(* for convenience of use.  In a later version of HOL, these could be 	*)
(* defined by use of the assumption list to introduce `local` 		*)
(* definitions, so as not to clutter up the built-in theories		*)
(* with constants that will be only used locally here.			*)
(* ---------------------------------------------------------------------*)

val AP = new_recursive_definition
     {name = "AP",
      rec_axiom = list_Axiom,
      def = --`(!l. AP NIL l = NIL) /\
               (!h t l. AP (CONS h t) l = CONS (h (HD l:'a):'b)
                                               (AP t (TL l)))`--};

val SPLIT = new_recursive_definition
     {name = "SPLIT",
      rec_axiom = num_Axiom,
      def = --`(SPLIT 0 l = (NIL, (l:'a list))) /\
               (SPLIT (SUC n) l = (CONS (HD l) (FST(SPLIT n (TL l))),
                                   SND(SPLIT n (TL l))))`--};

val PART = new_recursive_definition
     {name = "PART",
      rec_axiom = list_Axiom,
      def = --`(PART NIL (l:('a)list) = NIL) /\
               (PART (CONS n t) l = (CONS (FST (SPLIT n l))
                                          (PART t (SND (SPLIT n l)))))`--};

(* ---------------------------------------------------------------------*)
(* Some theorems about SPLIT, PART, etc.				*)
(* ---------------------------------------------------------------------*)

val SPLIT_APPEND = prove
 (--`!l:'a list. !l'. SPLIT (LENGTH l) (APPEND l l') = (l,l')`--,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [APPEND, SPLIT, LENGTH, HD, TL]);

val PART_FLAT = prove
 (--`!l:'a list list. PART (MAP LENGTH l) (FLAT l) = l`--,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [PART, LENGTH, MAP, FLAT, SPLIT_APPEND]);

val NUM_EQ_SYM_EQ = INST_TYPE[{redex= ==`:'a`==,residue= ==`:num`==}] EQ_SYM_EQ

val LENGTH_SND_SPLIT = prove
 (--`!(l:'a list).
     !n m.(LENGTH l = n+m) ==>
          (LENGTH(SND(SPLIT n l)) = m)`--,
      LIST_INDUCT_TAC THENL
      [ONCE_REWRITE_TAC [NUM_EQ_SYM_EQ] THEN
       REWRITE_TAC [LENGTH, ADD_EQ_0] THEN
       REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
       REWRITE_TAC [SPLIT, LENGTH],
       REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
       INDUCT_TAC THENL
       [REWRITE_TAC [ADD_CLAUSES, SPLIT, LENGTH],
        REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ] THEN
	REPEAT STRIP_TAC THEN RES_TAC THEN
	ASM_REWRITE_TAC [SPLIT, TL]]]);


val LENGTH_FST_SPLIT = prove
 (--`!(l:'a list).
     !n m.(LENGTH l = n+m) ==>
          (LENGTH(FST(SPLIT n l)) = n)`--,
      LIST_INDUCT_TAC THENL
      [ONCE_REWRITE_TAC [NUM_EQ_SYM_EQ] THEN
       REWRITE_TAC [LENGTH, ADD_EQ_0] THEN
       REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
       REWRITE_TAC [SPLIT, LENGTH],
       REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
       INDUCT_TAC THENL
       [REWRITE_TAC [ADD_CLAUSES, SPLIT, LENGTH],
        REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ] THEN
	REPEAT STRIP_TAC THEN RES_TAC THEN
	ASM_REWRITE_TAC [SPLIT, HD, TL, LENGTH]]]);

val APPEND_SPLIT = prove
 (--`!(l:'a list).
     !n m. (LENGTH l = n + m) ==>
           (APPEND (FST(SPLIT n l)) (SND (SPLIT n l)) = l)`--,
     LIST_INDUCT_TAC THENL
     [ONCE_REWRITE_TAC [NUM_EQ_SYM_EQ] THEN
      REWRITE_TAC [LENGTH, ADD_EQ_0] THEN
      REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
      REWRITE_TAC [SPLIT, APPEND],
      REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
      INDUCT_TAC THENL
      [REWRITE_TAC [ADD_CLAUSES, SPLIT, APPEND],
       REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ] THEN
       REPEAT STRIP_TAC THEN RES_TAC THEN
       ASM_REWRITE_TAC [SPLIT, HD, TL, APPEND]]]);


(* Recursive functions on the REPRESENTATION type...(MAJOR THM)		*)
val REP_REC_lemma = prove
 (--`!f. ?!fn. !tl. !l:'a list.
     fn(node tl,l):'b =
     f (AP (MAP (\t e.fn(t,e)) tl)(PART (MAP size tl)(TL l)))
       (HD l :'a)
       (MAP ABS_ltree (AP (MAP $, tl) (PART (MAP size tl) (TL l))))`--,
     STRIP_TAC THEN
     MP_TAC (SPEC (--`\rl:('a list->'b)list. \tl:tree list. \l:'a list.
                    f (AP rl (PART (MAP size tl) (TL l)))
		      (HD l:'a)
       	              (MAP ABS_ltree
     	      		   (AP (MAP $, tl)
		               (PART (MAP size tl) (TL l)))):'b`--)
      	          (INST_TYPE[{redex = ==`:'b`==, residue = ==`:'a list->'b`==}]
                            tree_Axiom)) THEN
     REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC (--`\p. ((fn (FST p:tree) (SND p:'a list)):'b)`--) THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      ASM_REWRITE_TAC [ETA_AX] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC,
      REPEAT GEN_TAC THEN
      POP_ASSUM
      (MP_TAC o
        SPECL [--`\(t:tree). \(e:'a list). (x(t,e):'b)`--,
               --`\(t:tree) (e:'a list). (y(t,e):'b)`--]) THEN
      CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
      POP_ASSUM MATCH_ACCEPT_TAC]);

(* A little simplifying lemma						*)
val lemma1 = prove
 (--`!(tl:'a ltree list).
      (MAP ABS_ltree
           (AP (MAP $,(MAP(FST o REP_ltree)tl))
               (PART (MAP size(MAP(FST o REP_ltree)tl))
                          (FLAT(MAP(SND o REP_ltree)tl))))) = tl`--,
    REWRITE_TAC [MAP_size_LENGTH, PART_FLAT] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [o_THM, MAP, AP, A_R, HD, TL]);

(* Another								*)
val lemma2 = prove
 (--`!(tl:'a ltree list).
      (AP (MAP(\t e. fn'(t,e))(MAP(FST o REP_ltree)tl))
          (PART (MAP size(MAP(FST o REP_ltree)tl))
                     (FLAT(MAP(SND o REP_ltree)tl)))) =
      (MAP (fn' o REP_ltree) tl:('b)list)`--,
    REWRITE_TAC [MAP_size_LENGTH, PART_FLAT] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, AP, o_THM, TL, HD] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [PAIR]);

(* Another								*)
val lemma3 = prove
 (--`!(trl:tree list). !(l:'a list).
      (LENGTH l = SUM(MAP size trl)) ==>
      (FLAT (MAP (SND o REP_ltree)
            (MAP ABS_ltree (AP (MAP $, trl)
                               (PART(MAP size trl)l)))) = l)`--,
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [SUM, MAP, LENGTH_NIL] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PART, AP, MAP, FLAT],
     REWRITE_TAC [MAP, SUM, PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     IMP_RES_TAC LENGTH_FST_SPLIT THEN
     ASM_REWRITE_TAC [AP, MAP, FLAT, HD, TL, o_THM] THEN
     MP_TAC (SPEC (--`(h:tree),(FST(SPLIT(size h)(l:'a list)))`--) R_A) THEN
     REWRITE_TAC [Is_ltree] THEN
     POP_ASSUM (ASSUME_TAC o SYM) THEN
     DISCH_THEN
       (fn th1 => FIRST_ASSUM (fn th => (SUBST1_TAC (EQ_MP th1 th))
         handle _ => NO_TAC)) THEN
     IMP_RES_TAC APPEND_SPLIT THEN
     REWRITE_TAC [] THEN POP_ASSUM ACCEPT_TAC]);

(* Another								*)
val lemma4 = prove
 (--`!(trl:tree list). !(l:'a list).
     (LENGTH l = SUM(MAP size trl)) ==>
     (node (MAP (FST o REP_ltree)
           (MAP ABS_ltree (AP (MAP $, trl)
                              (PART(MAP size trl)l)))) = node trl)`--,
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [SUM, MAP, LENGTH_NIL] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PART, AP, MAP],
     REWRITE_TAC [MAP, SUM, PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     IMP_RES_TAC LENGTH_FST_SPLIT THEN
     ASM_REWRITE_TAC [AP, MAP, FLAT, HD, TL, o_THM] THEN
     MP_TAC (SPEC (--`(h:tree),(FST(SPLIT(size h)(l:'a list)))`--) R_A) THEN
     REWRITE_TAC [Is_ltree] THEN
     POP_ASSUM (ASSUME_TAC o SYM) THEN
     DISCH_THEN
       (fn th1 => FIRST_ASSUM (fn th => (SUBST1_TAC (EQ_MP th1 th))
           handle _ => NO_TAC)) THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [node_11] THEN
     DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* Another								*)
val lemma5 = prove
 (--`!trl l.
     (size (node trl) = LENGTH l) ==>
     (ABS_ltree(node trl,l) =
       Node ((HD l):'a)
            (MAP ABS_ltree
    	         (AP (MAP $, trl)
                     (PART (MAP size trl) (TL l)))))`--,
     ONCE_REWRITE_TAC [NUM_EQ_SYM_EQ] THEN
     REWRITE_TAC [size_thm, LENGTH_CONS] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [HD, TL, Node] THEN
     IMP_RES_TAC lemma3 THEN
     POP_ASSUM SUBST1_TAC THEN
     IMP_RES_TAC lemma4 THEN
     POP_ASSUM SUBST1_TAC THEN
     REFL_TAC);

(* Another								*)
val lemma6 = prove
 (--`!trl. !(l:'a list).
     (size (node trl) = LENGTH l) ==>
     EVERY (\p. size(FST p) = LENGTH(SND p))
           (AP(MAP $, trl)(PART(MAP size trl)(TL l)))`--,
     ONCE_REWRITE_TAC [NUM_EQ_SYM_EQ] THEN
     REWRITE_TAC [size_thm, LENGTH_CONS] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [HD, TL] THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     MAP_EVERY SPEC_TAC [(--`(l':'a list)`--,--`(l:'a list)`--),
                         (--`(trl:tree list)`--,--`(trl:tree list)`--)] THEN
     LIST_INDUCT_TAC THENL
     [REWRITE_TAC [MAP, AP, PART, EVERY_DEF],
     REWRITE_TAC [MAP, SUM, PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF, AP, HD, TL] THEN
     CONV_TAC BETA_CONV THEN
     REWRITE_TAC [] THEN IMP_RES_TAC LENGTH_FST_SPLIT]);


(* Another								*)
val lemma7 = prove
 (--`!trl.
      EVERY (\t.!l. (size t = LENGTH l) ==>
                    (x(ABS_ltree(t,l)) = y(ABS_ltree(t,l))))
            trl ==>
      (!(l:'a list list).
        EVERY (\p. size(FST p) = LENGTH(SND p))
              (AP(MAP $, trl)l) ==>
        (MAP x(MAP ABS_ltree(AP(MAP $, trl)l)) :'b list =
         MAP y(MAP ABS_ltree(AP(MAP $, trl)l))))`--,
     LIST_INDUCT_TAC THENL
     [REWRITE_TAC [EVERY_DEF, MAP, AP],
      REWRITE_TAC [EVERY_DEF, MAP, AP] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      ASM_REWRITE_TAC []]);

(* Prove the axiom for 'a ltree						*)

val ltree_Axiom = store_thm("ltree_Axiom",
 --`!f. ?!fn. !v tl. (fn(Node (v:'a) tl):'b) = f (MAP fn tl) v tl`--,
     GEN_TAC THEN MP_TAC (SPEC_ALL REP_REC_lemma) THEN
     PURE_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC (--`(fn:^(ty_antiq ty) ->'b) o REP_ltree`--) THEN
      ASM_REWRITE_TAC [REP_Node, o_THM, TL, HD, lemma1, lemma2],
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
      STRIP_ASSUME_TAC (SPEC (--`l:'a ltree`--) A_ONTO) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM SUBST1_TAC THEN
      PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
      PURE_REWRITE_TAC [Is_ltree] THEN
      SPEC_TAC (--`SND (r:^(ty_antiq ty))`--,--`(l:'a list)`--) THEN
      SPEC_TAC (--`FST (r:^(ty_antiq ty))`--, --`(t:tree)`--) THEN
      tree_INDUCT_TAC THEN
      REPEAT STRIP_TAC THEN
      IMP_RES_THEN SUBST1_TAC lemma5 THEN
      ASM_REWRITE_TAC [] THEN
      IMP_RES_TAC lemma6 THEN
      IMP_RES_TAC lemma7 THEN
      POP_ASSUM SUBST1_TAC THEN REFL_TAC]);


(* get uniqueness part of ltree_Axiom					*)
val unique_lemma =
   GEN_ALL(CONJUNCT2(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));

(* Move to conversion nets forces different tactic in this proof. kls. *)
(* Prove induction thm for 'a ltree					*)
val ltree_Induct = save_thm("ltree_Induct",
   let val unique = CONV_RULE (DEPTH_CONV BETA_CONV) unique_lemma
       val spec = SPECL
                [--`\b v tl.(EVERY (\x. (x:bool)) b \/ P (Node (v:'a) tl))`--,
                 --`\(t:'a ltree).T`--,
                 --`(P:'a ltree -> bool)`--]
                (INST_TYPE [{redex = ==`:'b`==,residue= ==`:bool`==}]
                           (GEN_ALL unique))
       val conv = CONV_RULE(REDEPTH_CONV(BETA_CONV ORELSEC FUN_EQ_CONV))spec
       val rew1 = prove(--`(X = Y \/ X) = (Y ==> X)`--,
		        ASM_CASES_TAC (--`X:bool`--) THEN ASM_REWRITE_TAC[])
       val rew2 = prove(--`(!(h:'a). !t. EVERY P t ==> P(Node h t)) =
			   (!t. EVERY P t ==> !h. P(Node h t))`--,
		       REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
		       RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC)
       val rew3 = prove(--`!(l:'a list). EVERY (\x.x) (MAP (\x.T) l)`--,
                        LIST_INDUCT_TAC THEN
                        ASM_REWRITE_TAC [MAP, EVERY_DEF] THEN
                        CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
                        REPEAT GEN_TAC THEN REFL_TAC)
       val rew4 = prove(--`!(l:'a list). EVERY (\x.x) (MAP P l) = EVERY P l`--,
                        LIST_INDUCT_TAC THEN
                        ASM_REWRITE_TAC [MAP, EVERY_DEF] THEN
                        CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
                        REPEAT GEN_TAC THEN REFL_TAC)
    in
    GEN_ALL(REWRITE_RULE[rew4, rew2](REWRITE_RULE [rew1, rew3] conv))
    end);

val exists_lemma =
   GEN_ALL(CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));

val Node_11 = store_thm("Node_11",
 --`!(v1:'a). !v2 trl1 trl2.
           ((Node v1 trl1) = (Node v2 trl2)) = ((v1 = v2) /\ (trl1 = trl2))`--,
    MP_TAC (SPEC (--`\(l:'a list). \(v:'a). \(trl:'a ltree list). v`--)
	   (INST_TYPE [Type.beta |-> Type.alpha] exists_lemma)) THEN
    MP_TAC (SPEC (--`\l:'a ltree list list.\v:'a.\trl:'a ltree list.trl`--)
	   (INST_TYPE [Type.beta |-> Type`:'a ltree list`]
              (GEN_ALL exists_lemma))) THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
    [POP_ASSUM (MP_TAC o (AP_TERM (--`(fn':'a ltree->'a)`--))) THEN
     ASM_REWRITE_TAC[],
     POP_ASSUM (MP_TAC o (AP_TERM (--`(fn:'a ltree ->'a ltree list)`--))) THEN
     ASM_REWRITE_TAC[],
     ASM_REWRITE_TAC[]]);


(* ---------------------------------------------------------------------*)
(*   ltree_INDUCT: thm  -> thm						*)
(*									*)
(*     A |- !tl. EVERY \t.P[t] tl ==> !v. P[Node v tl]			*)
(* ----------------------------------------------------------		*)
(*               A |- !t. P[t]						*)
(*									*)
(*									*)
(* ltree_INDUCT_TAC							*)
(*									*)
(*             [A] !t.P[t]						*)
(*  ================================					*)
(*    [A,EVERY \t.P[t] trl] |- !v. P[Node v trl]			*)
(*									*)
(* ---------------------------------------------------------------------*)

local val b = genvar Type.bool
      fun ltree_INDUCT th =
        let val {Bvar,Body} = dest_forall(concl th)
            val {ant,conseq} = dest_imp Body
            val {Bvar=v, Body=con} = dest_forall conseq
            val (EVERY, [P, tll]) = strip_comb ant
            val concth = SYM(RIGHT_BETA(REFL (--`^P(Node ^v ^Bvar)`--)))
            val IND' = SPEC P (INST_TYPE [Type.alpha |-> type_of v] ltree_Induct)
            val th' = DISCH ant (SPEC v (UNDISCH(SPEC Bvar th)))
            val th1 = SUBST [b |->  concth]
                        (--`^(concl th') = (EVERY ^P ^Bvar ==> ^b)`--)
                        (REFL (concl th'))
            val th2 = GEN Bvar (DISCH ant (GEN v (UNDISCH (EQ_MP th1 th'))))
        in
          CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND' th2)
        end
in
fun ltree_INDUCT_TAC (A,tm) =
   let val {Bvar,Body} = dest_forall tm
       val Afrees = free_varsl A
       val t' = variant (free_vars tm@Afrees) Bvar
       val {Args = (t_ty::_),...} = dest_type(type_of Bvar)
       val body' = subst [{redex = Bvar, residue = t'}] Body
       val fv = free_vars body'@Afrees
       val v = mk_var{Name = "v", Ty = t_ty}
       val v' = variant fv v
       val vtrl = mk_var{Name = "trl",
                         Ty=mk_type{Tyop = "list",
                                    Args=[mk_type{Tyop="ltree",Args=[t_ty]}]}}
       val trl = variant fv vtrl
       val asm = --`EVERY (\^t'.^body') trl`--
   in
   ([(asm::A,
      mk_forall{Bvar=v', Body=subst[t' |-> Term`Node ^v' ^trl`] body'})],
    fn [th] => ltree_INDUCT (GEN trl (DISCH asm th)))
   end
end;


(* Need this theorem						*)
val Node_onto = store_thm("Node_onto",
 --`!(t:'a ltree). ?(v:'a). ?trl. t = Node v trl`--,
     ltree_INDUCT_TAC THEN
     STRIP_TAC THEN
     MAP_EVERY EXISTS_TAC [--`v:'a`--, --`trl:'a ltree list`--] THEN
     REFL_TAC);

val th0 =
  GEN_ALL
   (BETA_RULE
     (SPEC (Term`\(rl:'b list) (v:'a) (tl:'a ltree list). g v tl:'b`)
           ltree_Axiom));

val th0 = prove(
  --`!g. ?f. !v tl. f (Node v tl) = g v tl`--,
  GEN_TAC THEN
  STRIP_ASSUME_TAC (CONV_RULE EXISTS_UNIQUE_CONV (Q.SPEC `g` th0)) THEN
  Q.EXISTS_TAC `fn` THEN FIRST_ASSUM ACCEPT_TAC);



val ltree_case_def =
  Lib.try new_recursive_definition
    {name = "ltree_case_def",
     rec_axiom = th0,
     def = Term `ltree_case f (Node v l) = f v l`};

val ltree_case_cong = store_thm("ltree_case_cong",
Term `!f g M N.
         (M = N) /\
         (!v tl. (N = Node v tl) ==> (f v tl = g v tl))
           ==>
         (ltree_case f M = ltree_case g N)`,
REPEAT GEN_TAC
  THEN STRUCT_CASES_TAC (SPEC (Term`N:'a ltree`) Node_onto)
  THEN REPEAT STRIP_TAC
  THEN ASM_REWRITE_TAC [ltree_case_def]
  THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC);


(*---------------------------------------------------------------------------
     The (parameterized) size of an ltree. The desired equation is:

         ltree_size f (Node v tl)
             =
         1 + f v + list_size (ltree_size f) tl
 ---------------------------------------------------------------------------*)

val th =
 BETA_RULE
   (SPEC
     (Term`\(rl:num list) (v:'a) (l:'a ltree list).
         SUM rl + (LENGTH l + (f v + 1))`)
     (INST_TYPE [Type.beta |-> Type`:num`] ltree_Axiom));

val th1 = CONJUNCT1 (CONV_RULE (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) th);
val th2 = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) (GEN_ALL th1);

val lem = prove
 (Term`?ltree_size. !f v l.
     ltree_size f (Node v l)
        =
     SUM (MAP (ltree_size f) l) + (LENGTH l + (f v + 1))`,
STRIP_ASSUME_TAC th2
   THEN EXISTS_TAC (Term`fn:('a->num) -> 'a ltree -> num`) THEN BETA_TAC
   THEN ONCE_ASM_REWRITE_TAC[]
   THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)
   THEN REWRITE_TAC[]);

local open arithmeticTheory
in
val ltree_size_eqns = prove(Term
  `?ltree_size.
     !l v f. ltree_size f (Node v l)
                 =
             list_size (ltree_size f) l + (f v + 1)`
 ,
STRIP_ASSUME_TAC lem
   THEN EXISTS_TAC (Term`ltree_size:('a->num) -> 'a ltree -> num`)
   THEN ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
   THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC [MAP,SUM,LENGTH,listTheory.list_size_def,ADD_CLAUSES],
    RULE_ASSUM_TAC GSYM
     THEN ASM_REWRITE_TAC
        [MAP,SUM,LENGTH,listTheory.list_size_def,GSYM ADD_ASSOC, ADD_CLAUSES]
     THEN REWRITE_TAC [ONCE_REWRITE_RULE[ADD_SYM] ADD1]])
end;

val ltree_size_def =
 new_specification
    {sat_thm = ltree_size_eqns,
     name = "ltree_size_def",
     consts = [{const_name="ltree_size", fixity=Prefix}]};


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in
    S "val _ = TypeBase.write";             NL();
    S "  (TypeBase.mk_tyinfo";              NL();
    S "     {ax=ltree_Axiom,";              NL();
    S "      case_def=ltree_case_def,";     NL();
    S "      case_cong=ltree_case_cong,";   NL();
    S "      induction=ltree_Induct,";      NL();
    S "      nchotomy=Node_onto,";          NL();
    S "      size=SOME(Parse.Term`ltree_size:('a->num)->'a ltree->num`,"; NL();
    S "                ltree_size_def),";   NL();
    S "      one_one=SOME Node_11,";        NL();
    S "      distinct=NONE});"
  end)};


val _ = export_theory();

end;
