(* ===================================================================== *)
(* FILE          : mk_rec_type.sml                                       *)
(* DESCRIPTION   : Creates a theory containing the master theorem for    *)
(*                 axiomatizing all recursive types. Translated from     *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.07.27                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure rec_typeScript =
struct

(*---------------------------------------------------------------------------
 * Declare parent theory structure.
 *---------------------------------------------------------------------------*)
local open oneTheory ltreeTheory in end;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)
open HolKernel Parse basicHol90Lib;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

infix THEN THENL |->;

type thm = Thm.thm;

(*---------------------------------------------------------------------------
 * Create the new theory segment.
 *---------------------------------------------------------------------------*)
val _ = new_theory "rec_type";


(*---------------------------------------------------------------------------
 * Fetch theorems from ltree theory.
 *---------------------------------------------------------------------------*)
val ltree_Axiom  =  ltreeTheory.ltree_Axiom and
    ltree_Induct =  ltreeTheory.ltree_Induct and
    Node_onto    =  ltreeTheory.Node_onto;

(*---------------------------------------------------------------------------
 * Fetch definitions from list theory.
 *---------------------------------------------------------------------------*)
val EVERY_DEF = listTheory.EVERY_DEF and
    MAP       = listTheory.MAP;

(*---------------------------------------------------------------------------
 * Fetch theorems from combinator theory.
 *---------------------------------------------------------------------------*)
val o_THM = combinTheory.o_THM;

(*---------------------------------------------------------------------------
 * Create induction tactics.
 *---------------------------------------------------------------------------*)
val LIST_INDUCT_TAC = INDUCT_THEN listTheory.list_INDUCT ASSUME_TAC;

(* Copied from mk_ltree.sml. *)
(* ---------------------------------------------------------------------*)
(*   ltree_INDUCT: thm  -> thm						*)
(*									*)
(*     A |- !tl. EVERY \t.P[t] tl ==> !v. P[Node v tl]			*)
(* ----------------------------------------------------------		*)
(*               A |- !t. P[t]						*)
(*									*)
(* ---------------------------------------------------------------------*)

exception ltree_INDUCT_ERR;
local val b = genvar(==`:bool`==)
      val alpha = ==`:'a`==
in
fun ltree_INDUCT th =
   let val {Bvar,Body} = dest_forall(concl th)
       val {ant,conseq} = dest_imp Body
       val {Bvar = v, Body = con} = dest_forall conseq
       val (EVERY, [P, tll]) = strip_comb ant
       val concth = SYM(RIGHT_BETA(REFL (--`^P(Node ^v ^Bvar)`--)))
       val IND' = SPEC P (INST_TYPE [{redex = alpha, residue = type_of v}]
                                    ltree_Induct)
       val th' = DISCH ant (SPEC v (UNDISCH(SPEC Bvar th)))
       val th1 = SUBST [b |-> concth]
                       (--`^(concl th') = (EVERY ^P ^Bvar ==> ^b)`--)
                       (REFL (concl th'))
      val th2 = GEN Bvar (DISCH ant (GEN v (UNDISCH (EQ_MP th1 th'))))
  in
  CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND' th2)
  end
  handle _ => raise ltree_INDUCT_ERR
end;


(* ---------------------------------------------------------------------*)
(*									*)
(* ltree_INDUCT_TAC							*)
(*									*)
(*             [A] !t.P[t]						*)
(*  ================================					*)
(*    [A,EVERY \t.P[t] trl] |- !v. P[Node v trl]			*)
(*									*)
(* ---------------------------------------------------------------------*)

exception ltree_INDUCT_TAC_ERR;

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
   ([(asm::A,mk_forall{Bvar = v',
                       Body = subst[{redex=t',residue= --`(Node ^v' ^trl)`--}]
                                   body'})],
    fn [th] => ltree_INDUCT (GEN trl (DISCH asm th)))
   end
   handle _ => raise ltree_INDUCT_TAC_ERR;


(* A little lemma about EVERY and MAP					*)
val EVERY_MAP_lemma = prove
 (--`!(l:'a list). EVERY (\x.x) (MAP P l) = EVERY P l`--,
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [EVERY_DEF, MAP] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     ASM_REWRITE_TAC[]);

(* Existence part of ltree_Axiom.					*)
val exists_lemma =
     GEN_ALL(CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));

(* Show that for every predicate P on Nodes of a *ltree, there is a	*)
(* predicate TRP that holds of a *ltree if P holds of every node in	*)
(* the tree.								*)
val TRP_thm = prove
 (--`!P. ?TRP. !(v:'a) tl. TRP(Node v tl) = P v tl /\ EVERY TRP tl`--,
     STRIP_TAC THEN
     MP_TAC (SPEC (--`\(rl:bool list). \(v:'a). \(tl:'a ltree list).
		     (P v tl) /\ (EVERY (\x.x) rl)`--)
  	     (INST_TYPE [{redex = ==`:'b`==, residue = ==`:bool`==}]
                        exists_lemma)) THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [EVERY_MAP_lemma] THEN STRIP_TAC THEN
     EXISTS_TAC (--`(fn:'a ltree->bool)`--) THEN
     POP_ASSUM ACCEPT_TAC);

(* A lemma 								*)
val lemma1 = prove
 (--`!(l:'a list) x y.
     (EVERY P l /\ EVERY (\e. P e ==> ((x e:'b) = y e)) l) ==>
     (MAP x l = MAP y l)`--,
     LIST_INDUCT_TAC THEN REWRITE_TAC [EVERY_DEF, MAP] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

(* There is a unique function on trees all of whose nodes satisfy P	*)
val TRP_EU = prove
 (--`!(TRP:'a ltree->bool).
     !P.
     (!(v:'a). !tl. TRP(Node v tl) = (P v tl) /\ (EVERY TRP tl)) ==>
     !f. (?fn. !v tl. TRP(Node v tl) ==>
     		      (fn(Node v tl):'b = f (MAP fn tl) v tl)) /\
         !x y. (!v tl. TRP(Node v tl) ==>
 		       (x(Node v tl) = f (MAP x tl) v tl)) ==>
               (!v tl. TRP(Node v tl) ==>
		       (y(Node v tl) = f (MAP y tl) v tl)) ==>
	       (!t. TRP t  ==> (x t = y t))`--,
     REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CONJ_TAC THENL
     [STRIP_ASSUME_TAC
         (SPEC (--`(f:'b list -> 'a -> 'a ltree list -> 'b)`--)
               exists_lemma)   THEN
      EXISTS_TAC (--`(fn:'a ltree -> 'b)`--) THEN ASM_REWRITE_TAC [],
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ltree_INDUCT_TAC THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      IMP_RES_TAC lemma1 THEN
      ASM_REWRITE_TAC[]]);

(* define a function TRP P t = P holds of every node in t		*)
val TRP_DEF = new_definition("TRP_DEF",
 --`TRP P = @trp. !(v:'a) tl. trp(Node v tl) = (P v tl) /\ (EVERY trp tl)`--);

val TRP = store_thm("TRP",
 --`!P v tl.(TRP P) (Node v tl) = (P (v:'a) tl) /\ (EVERY (TRP P)tl)`--,
     REWRITE_TAC [TRP_DEF] THEN
     CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
     MATCH_ACCEPT_TAC TRP_thm);

(* There is a unique recursive function on TRP-subsets of *ltree	*)
(*									*)
(* |- !P f.								*)
(*    (?fn. !v tl. TRP P(Node v tl) ==> 				*)
(*  	          (fn(Node v tl) = f(MAP fn tl)v tl)) /\		*)
(*    (!x y. (!v tl. TRP P(Node v tl) ==> 				*)
(*		    (x(Node v tl) = f(MAP x tl)v tl)) ==>		*)
(*           (!v tl. TRP P(Node v tl) ==> 				*)
(*		    (y(Node v tl) = f(MAP y tl)v tl)) ==>		*)
(*           (!x. TRP P x ==> (x x = y x)))				*)

val TRP_EU_thm =
    GEN_ALL (MATCH_MP TRP_EU (SPEC (--`(P:'a->'a ltree list->bool)`--) TRP));

(* Some lemmas about ABS and REP					*)
val AR_lemma1 = prove
 (--`(!a:'b. ABS(REP a:'a ltree) = a) ==>
     (!r:'a ltree. TRP P r = (REP(ABS r:'b) = r)) ==>
     !tl. EVERY (TRP P) (MAP REP tl)`--,
     REPEAT DISCH_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [MAP,EVERY_DEF]);

val AR_lemma2 = prove
 (--`(!a:'b. ABS(REP a:'a ltree) = a) ==>
     (!r:'a ltree. TRP P r = (REP(ABS r:'b) = r)) ==>
     !tl v. P v (MAP REP tl) ==>
           (REP(ABS(Node v (MAP REP tl))) = Node v (MAP REP tl))`--,
     DISCH_TAC THEN
     DISCH_THEN (fn th =>  REWRITE_TAC [SYM(SPEC_ALL th)] THEN
		           ASSUME_TAC th) THEN
     IMP_RES_TAC AR_lemma1 THEN
     REWRITE_TAC [TRP] THEN
     ASM_REWRITE_TAC[]);

val AR_lemma3 = prove
 (--`(!a:'b. ABS(REP a:'a ltree) = a) ==>
     (!r:'a ltree. TRP P r = (REP(ABS r:'b) = r)) ==>
     !trl. EVERY (TRP P) trl ==>
     ?tl. trl = MAP REP tl`--,
    REPEAT DISCH_TAC THEN LIST_INDUCT_TAC THENL
    [REWRITE_TAC[EVERY_DEF] THEN
     EXISTS_TAC (--`NIL:'b list`--) THEN REWRITE_TAC [MAP],
     ASM_REWRITE_TAC [EVERY_DEF] THEN REPEAT STRIP_TAC THEN
     RES_THEN STRIP_ASSUME_TAC THEN
     EXISTS_TAC (--`CONS (ABS (h:'a ltree):'b) tl`--) THEN
     ASM_REWRITE_TAC [MAP]]);

val AR_lemma4 = prove
 (--`(!a:'b. ABS(REP a:'a ltree) = a) ==>
     (!al. MAP ABS (MAP REP al) = al)`--,
     STRIP_TAC THEN
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [MAP]);

val AR_lemma5 =
    (GEN_ALL o UNDISCH_ALL o hd o IMP_CANON o DISCH_ALL o prove_abs_fn_onto)
    (ASSUME (--`(!a:'b. ABS(REP a:'a ltree) = a) /\
	        (!r:'a ltree. TRP P r = (REP(ABS r:'b) = r))`--));

val MAP_o = store_thm("MAP_o",
 --`!(f:'b->'c). !(g:'a->'b).  MAP (f o g) = (MAP f) o (MAP g)`--,
     REPEAT GEN_TAC THEN
     CONV_TAC FUN_EQ_CONV THEN
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [MAP, o_THM]);

(* ===================================================================== *)
(* NOW... the main theorem....						*)
(* ===================================================================== *)

val TY_DEF_THM = store_thm("TY_DEF_THM",
 --`!REP. !ABS. !P.
    ((!a:'b. ABS(REP a:'a ltree) = a) /\
     (!r:'a ltree. TRP P r = (REP(ABS r:'b) = r))) ==>
    !f. ?!fn. !v:'a. !tl.
    P v (MAP REP tl) ==>
    (fn(ABS(Node v (MAP REP tl)):'b):'c = f (MAP fn tl) v tl)`--,
    REPEAT GEN_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
    REPEAT STRIP_TAC THENL
    [MP_TAC (CONJUNCT1
          (SPECL [--`P:'a->'a ltree list->bool`--,
                  --`\l:('c)list.\v:'a.\tl:'a ltree list.
                     f l v (MAP ABS tl: 'b list):'c`--]
                   (INST_TYPE [==`:'b`== |-> ==`:'c`==] TRP_EU_thm))) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     PURE_ONCE_REWRITE_TAC [TRP] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC (--`((fn:'a ltree->'c) o REP) :'b->'c`--) THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     ASSUME_TAC (SPEC_ALL (UNDISCH_ALL AR_lemma1)) THEN
     IMP_RES_TAC AR_lemma2 THEN
     IMP_RES_TAC AR_lemma4 THEN
     RES_TAC THEN ASM_REWRITE_TAC [MAP_o,o_THM],
     REPEAT_TCL STRIP_THM_THEN
                  (fn th => fn g => SUBST1_TAC th g handle _ => MP_TAC th g)
     	          (SPEC (--`x:'b`--) AR_lemma5) THEN
     SPEC_TAC (--`r:'a ltree`--, --`r:'a ltree`--) THEN
     MP_TAC (CONJUNCT2
          (SPECL [--`P:'a->'a ltree list->bool`--,
                  --`\l:'c list. \v:'a.\tl:'a ltree list.
                       f l v (MAP ABS tl:'b list):'c`--]
                 (INST_TYPE [==`:'b`== |-> ==`:'c`==] TRP_EU_thm))) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     DISCH_THEN (MP_TAC o (REWRITE_RULE
                              [SYM(ANTE_CONJ_CONV (--`A /\ B ==> C`--))])) THEN
     DISCH_THEN(MP_TAC o(SPECL[--`((fn:'b->'c) o ABS):'a ltree->'c`--,
                               --`((fn':'b ->'c) o ABS):'a ltree->'c`--])) THEN
     REWRITE_TAC [o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
     REWRITE_TAC [TRP] THEN
     CONJ_TAC THEN REPEAT GEN_TAC THEN
     CONV_TAC ANTE_CONJ_CONV THEN
     DISCH_THEN (fn t => STRIP_TAC THEN MP_TAC t) THEN
     IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) (UNDISCH_ALL AR_lemma3) THEN
     IMP_RES_TAC AR_lemma4 THEN ASM_REWRITE_TAC [MAP_o,o_THM]]);

(* For use in type definition package    *)
val exists_TRP = store_thm("exists_TRP",
 --`!P. (?v:'a. P v NIL) ==> ?t:'a ltree. TRP P t`--,
    GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC (--`Node (v:'a) NIL`--) THEN
    ASM_REWRITE_TAC [TRP,EVERY_DEF]);

val _ = export_theory();

end;
