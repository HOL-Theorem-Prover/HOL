(* ===================================================================== *)
(* FILE          : mk_list.sml                                           *)
(* DESCRIPTION   : The logical definition of the list type operator. The *)
(*                 type is defined and the following "axiomatization" is *)
(*                 proven from the definition of the type:               *)
(*                                                                       *)
(*                    |- !x f. ?!fn. (fn NIL = x) /\                     *)
(*                             (!h t. fn (CONS h t) = f (fn t) h t) *)
(*                                                                       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* REVISED       : 87.03.14                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


structure listScript =
struct

(*---------------------------------------------------------------------------
 * Bind ancestor theory structures. The parents of list are "arithmetic" and
 * "pair".
 *---------------------------------------------------------------------------*)
local open arithmeticTheory pairTheory in end;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)
open HolKernel Parse basicHol90Lib Num_conv ConstrProofs;
infix THEN ORELSE THENL THENC ORELSEC  |->;

type thm = Thm.thm;

val _ = new_theory "list";


val NOT_SUC      = numTheory.NOT_SUC
and INV_SUC      = numTheory.INV_SUC
fun INDUCT_TAC g = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g;

val LESS_0       = prim_recTheory.LESS_0;
val NOT_LESS_0   = prim_recTheory.NOT_LESS_0;
val PRE          = prim_recTheory.PRE;
val LESS_MONO    = prim_recTheory.LESS_MONO;
val INV_SUC_EQ   = prim_recTheory.INV_SUC_EQ;
val PRIM_REC_THM = prim_recTheory.PRIM_REC_THM;
val num_Axiom    = prim_recTheory.num_Axiom;

val ADD_CLAUSES   = arithmeticTheory.ADD_CLAUSES;
val LESS_ADD_1    = arithmeticTheory.LESS_ADD_1;
val LESS_EQ       = arithmeticTheory.LESS_EQ;
val NOT_LESS      = arithmeticTheory.NOT_LESS;
val LESS_EQ_ADD   = arithmeticTheory.LESS_EQ_ADD;
val num_CASES     = arithmeticTheory.num_CASES;
val LESS_MONO_EQ  = arithmeticTheory.LESS_MONO_EQ;
val ADD_CLAUSES   = arithmeticTheory.ADD_CLAUSES;
val LESS_MONO_EQ  = arithmeticTheory.LESS_MONO_EQ;
val ADD_EQ_0      = arithmeticTheory.ADD_EQ_0;

val PAIR_EQ = pairTheory.PAIR_EQ;


(* Define the subset predicate for lists.				*)
val IS_list_REP = new_definition("IS_list_REP",
 --`IS_list_REP r = ?f n. r = ((\m.(m<n => (f m) | @(x:'a).T)),n)`--);

(* Show that the representation subset is nonempty.			*)
val EXISTS_list_REP = prove
  (--`?p. IS_list_REP (p:((num->'a) # num))`--,
      EXISTS_TAC (--`((\n:num.@e:'a.T),0)`--) THEN
      PURE_REWRITE_TAC [IS_list_REP] THEN
      MAP_EVERY EXISTS_TAC [--`\n:num.@e:'a.T`--, --`0`--] THEN
      REWRITE_TAC [NOT_LESS_0]);

(* Define the new type.							*)
val list_TY_DEF = new_type_definition
   {name = "list",
    pred = --`IS_list_REP:((num->'a) # num) -> bool`--,
    inhab_thm = EXISTS_list_REP};

(* Define a representation function, REP_list, from the type 'a list to  *)
(* the representing type and the inverse abstraction function ABS_list,  *)
(* and prove some trivial lemmas about them.                             *)
val list_ISO_DEF = define_new_type_bijections
                     {name = "list_ISO_DEF",
                      ABS = "ABS_list",
                      REP = "REP_list",
                      tyax = list_TY_DEF};

val R_ONTO = prove_rep_fn_onto list_ISO_DEF
and A_11   = prove_abs_fn_one_one list_ISO_DEF
and A_R = CONJUNCT1 list_ISO_DEF
and R_A = CONJUNCT2 list_ISO_DEF;

(* --------------------------------------------------------------------- *)
(* Definitions of NIL and CONS.						*)
(* --------------------------------------------------------------------- *)

val NIL_DEF = new_definition
 ("NIL_DEF",
          --`NIL = ABS_list ((\n:num. @e:'a. T),0)`--);

val CONS_DEF =
new_definition("CONS_DEF",
    --`CONS (h:'a) (t:'a list) =
        (ABS_list ((\m. ((m=0) => h | (FST(REP_list t)) (PRE m))),
		   (SUC(SND(REP_list t)))))`--);

val _ = add_listform {separator = ";", leftdelim = "[", rightdelim = "]",
                      cons = "CONS", nilstr = "NIL"};
(*
val _ = add_rule ("CONS", term_grammar.Infix (HOLgrammars.RIGHT, 800),
                  [term_grammar.TOK "::"])
*)

(* ---------------------------------------------------------------------*)
(* Now, prove the axiomatization of lists.				*)
(* ---------------------------------------------------------------------*)

val lemma1 =
    TAC_PROOF(([],
    --`!x:'b. !f: 'b -> 'a -> 'a list -> 'b.
       ?fn1: (num -> 'a) # num -> 'b.
	 (!g.   fn1(g,0)   = x) /\
	 (!g n. fn1(g,n+1) =
	        f (fn1 ((\i.g(i+1)),n)) (g 0) (ABS_list((\i.g(i+1)),n)))`--),
   REPEAT STRIP_TAC
   THEN EXISTS_TAC
   (--`\p:(num -> 'a)#num.
     (PRIM_REC (\g.(x:'b))
	       (\b m g. f (b (\i.g(i+1))) (g 0) (ABS_list((\i.g(i+1)),m))))
     (SND p)
     (FST p)`--)
   THEN
   CONV_TAC (DEPTH_CONV (BETA_CONV ORELSEC num_CONV)) THEN
   REWRITE_TAC [PRIM_REC_THM, ADD_CLAUSES] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[]);

val NIL_lemma =
    TAC_PROOF(([], --`REP_list NIL = ((\n:num.@x:'a.T), 0)`--),
              REWRITE_TAC [NIL_DEF, (SYM(SPEC_ALL R_A)), IS_list_REP] THEN
	      MAP_EVERY EXISTS_TAC [--`\n:num.@x:'a.T`--, --`0`--] THEN
	      REWRITE_TAC [NOT_LESS_0]);

val REP_lemma =
    TAC_PROOF(([], --`IS_list_REP (REP_list (l: 'a list))`--),
              REWRITE_TAC [R_ONTO] THEN
	      EXISTS_TAC (--`l:'a list`--) THEN
	      REFL_TAC);

val CONS_lemma = TAC_PROOF(([],
   --`REP_list (CONS (h:'a) t) =
     ((\m.((m=0)=>h|FST(REP_list t)(PRE m))),SUC(SND(REP_list t)))`--),
   REWRITE_TAC [CONS_DEF, (SYM(SPEC_ALL R_A)), IS_list_REP] THEN
   EXISTS_TAC (--`\n.((n=0) => (h:'a) | (FST(REP_list t)(PRE n)))`--) THEN
   EXISTS_TAC (--`SUC(SND(REP_list (t:('a)list)))`--) THEN
   REWRITE_TAC [PAIR_EQ] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   STRIP_TAC THEN
   ASM_CASES_TAC (--`n < (SUC(SND(REP_list (t:('a)list))))`--) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [IS_list_REP]
                                  (SPEC (--`t:'a list`--)
                                        (GEN_ALL REP_lemma))) THEN
   POP_ASSUM SUBST_ALL_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [NOT_LESS, (SYM(SPEC_ALL LESS_EQ))] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   DISCH_THEN ((STRIP_THM_THEN SUBST1_TAC) o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [num_CONV (--`1`--), PRE, ADD_CLAUSES, NOT_SUC] THEN
   REWRITE_TAC[REWRITE_RULE[SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD]);

val exists_lemma = TAC_PROOF(([],
 --`!x:'b. !(f :'b->'a->'a list->'b).
    ?fn1:'a list->'b.
       (fn1 NIL = x) /\
       (!h t. fn1 (CONS h t) = f (fn1 t) h t)`--),
    REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [num_CONV (--`1`--), ADD_CLAUSES]
		   (SPECL[--`x:'b`--, --`f:'b->'a->'a list->'b`--]
                         lemma1)) THEN
    EXISTS_TAC (--`\(x:('a)list).(fn1 (REP_list x):'b)`--) THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC [NIL_lemma, CONS_lemma] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [NOT_SUC, PRE, boolTheory.ETA_AX, A_R]);

val A_11_lemma =
    REWRITE_RULE [SYM (ANTE_CONJ_CONV (--`(A /\ B) ==> C`--))]
    (DISCH_ALL(snd(EQ_IMP_RULE (UNDISCH_ALL (SPEC_ALL A_11)))));

val R_A_lemma =
    TAC_PROOF(([],
	     --`REP_list(ABS_list((\m.((m<n) => f(SUC m) | @(x:'a).T)),n)) =
	        ((\m.((m<n) => f(SUC m) | @(x:'a).T)),n)`--),
	     REWRITE_TAC [SYM(SPEC_ALL R_A), IS_list_REP] THEN
	     MAP_EVERY EXISTS_TAC [--`\n.f(SUC n):'a`--, --`(n:num)`--] THEN
	     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	     REFL_TAC);

val cons_lemma = TAC_PROOF(([],
   --`ABS_list((\m.(m < SUC n) => f m | (@(x:'a).T)), (SUC n)) =
      (CONS(f 0)(ABS_list ((\m.((m<n) => (f (SUC m)) | (@(x:'a).T))), n)))`--),
   REWRITE_TAC [CONS_DEF] THEN
   MATCH_MP_TAC (GEN_ALL A_11_lemma) THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [R_ONTO] THEN
   EXISTS_TAC
   (--`CONS (f 0) (ABS_list((\m.((m<n) => (f (SUC m)) | (@x:'a.T))),n))`--)
   THEN
   REWRITE_TAC [CONS_lemma],
   REWRITE_TAC [IS_list_REP] THEN
   MAP_EVERY EXISTS_TAC [--`(f:num->'a)`--, --`SUC n`--] THEN REFL_TAC,
   REWRITE_TAC [PAIR_EQ, R_A_lemma] THEN
   CONV_TAC FUN_EQ_CONV THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_TAC THEN
   STRIP_ASSUME_TAC (SPEC (--`(n':num)`--) num_CASES) THEN
   POP_ASSUM SUBST1_TAC THENL
   [REWRITE_TAC [PRE, LESS_0],
   REWRITE_TAC [PRE, NOT_SUC, LESS_MONO_EQ]]]);


val list_Axiom = store_thm("list_Axiom",
 --`!x:'b.
    !f:'b -> 'a -> 'a list -> 'b.
    ?!(fn1: 'a list -> 'b).
        (fn1 NIL = x) /\
        (!h t. fn1 (CONS h t) = f (fn1 t) h t)`--,
    PURE_REWRITE_TAC [boolTheory.EXISTS_UNIQUE_DEF] THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [exists_lemma] THEN
    REWRITE_TAC [NIL_DEF] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC FUN_EQ_CONV THEN
    CONV_TAC (ONCE_DEPTH_CONV(REWR_CONV(SYM (SPEC_ALL A_R)))) THEN
    X_GEN_TAC (--`l :'a list`--) THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [IS_list_REP]
		          (SPEC (--`l :'a list`--)
                                (GEN_ALL REP_lemma))) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SPEC_TAC (--`f':num->'a`--,--`f':num->'a`--) THEN
    SPEC_TAC (--`n:num`--,--`n:num`--) THEN
    INDUCT_TAC THENL
    [ASM_REWRITE_TAC [NOT_LESS_0],
     STRIP_TAC THEN
     POP_ASSUM (ASSUME_TAC o (CONV_RULE (DEPTH_CONV BETA_CONV)) o
                (SPEC (--`\n.f'(SUC n):'a`--))) THEN
     ASM_REWRITE_TAC [cons_lemma]]);

val NULL_DEF = new_recursive_definition
      {name = "NULL_DEF",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(NULL (NIL:'a list) = T) /\
                (NULL (CONS (h:'a) t) = F)`--};

val HD = new_recursive_definition
      {name = "HD",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`HD (CONS (h:'a) t) = h`--};

val TL = new_recursive_definition
      {name = "TL",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`TL (CONS (h:'a) t) = t`--};

val SUM = new_recursive_definition
      {name = "SUM",
       fixity = Prefix,
       rec_axiom =  list_Axiom,
       def = --`(SUM NIL = 0) /\
                (!h t. SUM (CONS h t) = h + (SUM t))`--};

val APPEND = new_recursive_definition
      {name = "APPEND",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!l:'a list. APPEND NIL l = l) /\
                (!l1 l2 h. APPEND (CONS h l1) l2 = CONS h (APPEND l1 l2))`--};

val FLAT = new_recursive_definition
      {name = "FLAT",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(FLAT NIL = (NIL:'a list)) /\
                (!h t. FLAT (CONS h t) = APPEND h (FLAT t))`--};

val LENGTH = new_recursive_definition
      {name = "LENGTH",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(LENGTH NIL = 0) /\
                (!(h:'a). !t. LENGTH (CONS h t) = SUC (LENGTH t))`--};

val MAP = new_recursive_definition
      {name = "MAP",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!f. MAP f NIL = NIL) /\
                (!f h t. MAP f (CONS (h:'a) t) = CONS (f h:'b) (MAP f t))`--};

(*---------------------------------------------------------------------------*
 * Added to support TFL -- kxs, June 1997                                    *
 *---------------------------------------------------------------------------*)
val list_case_def = new_recursive_definition
      {name = "list_case_def",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!b f. list_case b f NIL = (b:'b)) /\
            (!b f h t. list_case b f (CONS (h:'a) t) = f h t)`--};

(*---------------------------------------------------------------------------*
 * Added to support TFL -- kxs, Sept 1998                                    *
 *---------------------------------------------------------------------------*)
val list_size_def = new_recursive_definition
    {def = Term`(list_size f [] = 0) /\
                (list_size f (CONS h t) = 1 + f h + list_size f t)`,
     fixity = Prefix, name = "list_size_def", rec_axiom = list_Axiom};

(* ---------------------------------------------------------------------*)
(* Definition of a function 						*)
(*									*)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list		*)
(* 									*)
(* for mapping a curried binary function down a pair of lists:		*)
(* 									*)
(* |- (!f. MAP2 f[][] = []) /\						*)
(*   (!f h1 t1 h2 t2.							*)
(*      MAP2 f(CONS h1 t1)(CONS h2 t2) = CONS(f h1 h2)(MAP2 f t1 t2))	*)
(* 									*)
(* [TFM 92.04.21]							*)
(* ---------------------------------------------------------------------*)

val MAP2 =
  let val lemma = prove
     (--`?fn.
         (!f:'a -> 'b -> 'c. fn f [] [] = []) /\
         (!f h1 t1 h2 t2.
           fn f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (fn f t1 t2))`--,
      let val th = prove_rec_fn_exists list_Axiom
           (--`(fn (f:'a -> 'b -> 'c) [] l = []) /\
               (fn f (CONS h t) l = CONS (f h (HD l)) (fn f t (TL l)))`--)
      in
      STRIP_ASSUME_TAC th THEN
      EXISTS_TAC (--`fn:('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list`--)
      THEN ASM_REWRITE_TAC [HD,TL]
      end)
  in
  new_specification{name = "MAP2", sat_thm = lemma,
                    consts = [{const_name="MAP2", fixity=Prefix}]}
  end

val EL = new_recursive_definition
      {name = "EL",
       fixity = Prefix,
       rec_axiom = num_Axiom,
       def = --`(!l. EL 0 l = (HD l:'a)) /\
                (!l:'a list. !n. EL (SUC n) l = EL n (TL l))`--};

val EVERY_DEF = new_recursive_definition
      {name = "EVERY_DEF",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EVERY P NIL = T)  /\
                (!P h t. EVERY P (CONS h t) = (P h /\ EVERY P t))`--};


(* ---------------------------------------------------------------------*)
(* Proofs of some theorems about lists.					*)
(* ---------------------------------------------------------------------*)

val NULL = store_thm ("NULL",
 --`NULL (NIL :'a list) /\ (!h t. ~NULL(CONS (h:'a) t))`--,
   REWRITE_TAC [NULL_DEF]);

(* List induction							*)
(* |- P NIL /\ (!t. P t ==> !h. P(CONS h t)) ==> (!x.P x) 		*)
val list_INDUCT = save_thm("list_INDUCT",prove_induction_thm list_Axiom);

(* Create a tactic.							*)
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* Cases theorem: |- !l. (l = []) \/ (?t h. l = CONS h t)		*)
val list_CASES = save_thm("list_CASES", prove_cases_thm list_INDUCT);

(* CONS11:  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t') *)
val CONS_11 = save_thm("CONS_11",
   ConstrProofs.prove_constructors_one_one list_Axiom);

val NOT_NIL_CONS = save_thm("NOT_NIL_CONS",
   ConstrProofs.prove_constructors_distinct list_Axiom);

val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);

val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 --`!l1 l2. ~(l1 = l2) ==> !h1:'a. !h2. ~(CONS h1 l1 = CONS h2 l2)`--,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [CONS_11]);

val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 --`!h1:'a. !h2. ~(h1 = h2) ==> !l1 l2. ~(CONS h1 l1 = CONS h2 l2)`--,
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [CONS_11]);

val EQ_LIST = store_thm("EQ_LIST",
 --`!h1:'a.!h2.(h1=h2) ==> !l1 l2. (l1 = l2) ==> (CONS h1 l1 = CONS h2 l2)`--,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [CONS_11]);


val CONS = store_thm   ("CONS",
  --`!l : 'a list. ~NULL l ==> (CONS (HD l) (TL l) = l)`--,
       STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC (--`l:'a list`--) list_CASES) THEN
       POP_ASSUM SUBST1_TAC THEN
       ASM_REWRITE_TAC [HD, TL, NULL]);

val APPEND_NIL = store_thm("APPEND_NIL",
--`!(l:'a list). APPEND l [] = l`--,
 LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);


val APPEND_ASSOC = store_thm ("APPEND_ASSOC",
 --`!(l1:'a list) l2 l3.
     APPEND l1 (APPEND l2 l3) = (APPEND (APPEND l1 l2) l3)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);

val LENGTH_APPEND = store_thm ("LENGTH_APPEND",
 --`!(l1:'a list) (l2:'a list).
     LENGTH (APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, APPEND, ADD_CLAUSES]);

val MAP_APPEND = store_thm ("MAP_APPEND",
 --`!(f:'a->'b).!l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`--,
    STRIP_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, APPEND]);

val LENGTH_MAP = store_thm ("LENGTH_MAP",
 --`!l. !(f:'a->'b). LENGTH (MAP f l) = LENGTH l`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH]);

val EVERY_EL = store_thm ("EVERY_EL",
 --`!(l:'a list) P. EVERY P l = !n. (n < LENGTH l) ==> P (EL n l)`--,
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF, LENGTH, NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN INDUCT_TAC THENL
       [ASM_REWRITE_TAC [EL, HD],
        ASM_REWRITE_TAC [LESS_MONO_EQ, EL, TL]],
       REPEAT STRIP_TAC THENL
       [POP_ASSUM (MP_TAC o (SPEC (--`0`--))) THEN
        REWRITE_TAC [LESS_0, EL, HD],
	POP_ASSUM ((ANTE_RES_THEN ASSUME_TAC) o (MATCH_MP LESS_MONO)) THEN
	POP_ASSUM MP_TAC THEN REWRITE_TAC [EL, TL]]]);

val EVERY_CONJ = store_thm("EVERY_CONJ",
 --`!l. EVERY (\(x:'a). (P x) /\ (Q x)) l = (EVERY P l /\ EVERY Q l)`--,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

val LENGTH_NIL = store_thm("LENGTH_NIL",
 --`!l:'a list. (LENGTH l = 0) = (l = NIL)`--,
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL]);

val LENGTH_CONS = store_thm("LENGTH_CONS",
 --`!l n. (LENGTH l = SUC n) =
          ?h:'a. ?l'. (LENGTH l' = n) /\ (l = CONS h l')`--,
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC
       [LENGTH, NOT_EQ_SYM(SPEC_ALL NOT_SUC), NOT_NIL_CONS],
     REWRITE_TAC [LENGTH, INV_SUC_EQ, CONS_11] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC (--`h:'a`--) THEN
      EXISTS_TAC (--`l:'a list`--) THEN
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []]]);

val LENGTH_EQ_CONS = store_thm("LENGTH_EQ_CONS",
 --`!P:'a list->bool.
    !n:num.
      (!l. (LENGTH l = SUC n) ==> P l) =
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)`--,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH,NOT_NIL_CONS,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH,INV_SUC_EQ,CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);

val LENGTH_EQ_NIL = store_thm("LENGTH_EQ_NIL",
 --`!P: 'a list->bool.
    (!l. (LENGTH l = 0) ==> P l) = P []`--,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LENGTH],
    DISCH_TAC THEN
    INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [LENGTH,NOT_SUC]]]);;

val CONS_ACYCLIC = store_thm("CONS_ACYCLIC",
Term`!l x. ~(l = CONS x l) /\ ~(CONS x l = l)`,
 LIST_INDUCT_TAC
 THEN ASM_REWRITE_TAC[CONS_11,NOT_NIL_CONS, NOT_CONS_NIL, LENGTH_NIL]);

val APPEND_eq_NIL = store_thm("APPEND_eq_NIL",
Term `(!l1 l2:'a list. ([] = APPEND l1 l2) = (l1=[]) /\ (l2=[])) /\
      (!l1 l2:'a list. (APPEND l1 l2 = []) = (l1=[]) /\ (l2=[]))`,
CONJ_TAC THEN
  INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC
   THEN REWRITE_TAC [CONS_11,NOT_NIL_CONS, NOT_CONS_NIL,APPEND]
   THEN GEN_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);


val list_case_cong =
  save_thm("list_case_cong", Prim_rec.case_cong_thm list_CASES list_case_def);

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in
    S "val _ = TypeBase.write";         NL();
    S "  (TypeBase.mk_tyinfo";          NL();
    S "     {ax=list_Axiom,";           NL();
    S "      case_def=list_case_def,";  NL();
    S "      case_cong=list_case_cong,"; NL();
    S "      induction=list_INDUCT,";    NL();
    S "      nchotomy=list_CASES,";      NL();
    S "      size=SOME(Parse.Term`list_size:('a->num)->'a list->num`,"; NL();
    S "                list_size_def),"; NL();
    S "      one_one=SOME CONS_11,"; NL();
    S "      distinct=SOME NOT_NIL_CONS});"
  end)};

val _ = export_theory();

end;
