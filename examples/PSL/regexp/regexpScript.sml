(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(* Originated from Konrad Slind, tweaked by MJCG for Accellera PSL SEREs     *)
(* An automata-based matcher added by Joe Hurd                               *)
(*---------------------------------------------------------------------------*)

(*
app load ["bossLib", "rich_listTheory", "metisLib"];
*)

open HolKernel Parse boolLib;
open bossLib metisLib pairTheory combinTheory listTheory rich_listTheory
     arithmeticTheory;

val () = new_theory "regexp";

(*---------------------------------------------------------------------------*)
(* Symbolic tacticals.                                                       *)
(*---------------------------------------------------------------------------*)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

(*---------------------------------------------------------------------------*)
(* Make list append into an infix recognized by the parser                   *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "<>" (Infixl 500);
val _ = overload_on ("<>", Term`APPEND`);

(*---------------------------------------------------------------------------*)
(* Misc. theorems                                                            *)
(*---------------------------------------------------------------------------*)

val IN_THM = prove
  (``!x. P x = x IN P``,
   RW_TAC bool_ss [boolTheory.IN_DEF]);

val APPEND_ID_THM = prove
  (``!l1 l2. ((l1<>l2 = l1) = (l2=[])) /\
             ((l1<>l2 = l2) = (l1=[]))``,
   Induct THEN EVAL_TAC THEN ASM_REWRITE_TAC []
   THEN GEN_TAC THEN Cases THEN RW_TAC list_ss [] THEN DISJ2_TAC
   THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `LENGTH`)
   THEN RW_TAC list_ss []);

val APPEND_CONS = prove
  (``!h t. [h]<>t = h::t``,
   RW_TAC list_ss []);

val NULL_EQ_NIL = prove
  (``!l. NULL l = (l = [])``,
   Cases THEN RW_TAC list_ss []);

val LENGTH_EQ_ONE = store_thm
  ("LENGTH_EQ_ONE",
   ``!l. (LENGTH l = 1) = ?x. l = [x]``,
   Cases THEN RW_TAC list_ss [] THEN
   Cases_on `t` THEN RW_TAC list_ss []);

val MEM_TL = prove
  (``!x l. ~NULL l ==> MEM x (TL l) ==> MEM x l``,
   Induct_on `l` THEN RW_TAC list_ss []);

val FIRST_EXISTS_THM = prove
  (``!P L. EXISTS P L ==>
       ?prefix w suffix.
         (L = prefix <> [w] <> suffix) /\ EVERY ($~ o P) prefix /\ P w``,
   GEN_TAC THEN Induct THEN RW_TAC list_ss []
   THEN FULL_SIMP_TAC list_ss [EXISTS_DEF] THEN RW_TAC list_ss []
   THENL [MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `L`] THEN RW_TAC list_ss [],
          RES_TAC THEN Cases_on `P h` THENL
          [MAP_EVERY Q.EXISTS_TAC [`[]`, `h`, `prefix <> [w] <> suffix`]
           THEN RW_TAC list_ss [],
           MAP_EVERY Q.EXISTS_TAC [`h::prefix`, `w`, `suffix`] THEN
           RW_TAC list_ss [combinTheory.o_DEF]]]);

val EXISTS_ELIM_THM = prove
  (``!P l. EXISTS P l = ?x. MEM x l /\ x IN P``,
   GEN_TAC THEN Induct
   THEN RW_TAC list_ss [EXISTS_DEF]
   THEN PROVE_TAC [IN_THM]);

val EVERY_ELIM_THM = prove
  (``!P l. EVERY P l = !x. MEM x l ==> x IN P``,
    GEN_TAC THEN Induct
    THEN RW_TAC list_ss [EVERY_DEF]
    THEN PROVE_TAC [IN_THM]);

(*---------------------------------------------------------------------------*)
(* Concatenate a list of lists                                               *)
(*---------------------------------------------------------------------------*)

val CONCAT_def = Define
  `(CONCAT []     = []) /\
   (CONCAT(l::ll) = l <> CONCAT ll)`;

val CONCAT_EQ_NIL = prove
  (``!wlist. (CONCAT wlist = []) = EVERY NULL wlist``,
   Induct THEN RW_TAC list_ss [CONCAT_def,NULL_EQ_NIL]);

val NULL_CONCAT_THM = prove
  (``!L. NULL (CONCAT L) = EVERY NULL L``,
   PROVE_TAC [CONCAT_EQ_NIL, NULL_EQ_NIL]);

val CONCAT_APPEND_DISTRIB = prove
  (``!l1 l2. CONCAT (l1 <> l2) = CONCAT l1 <> CONCAT l2``,
   Induct THEN RW_TAC list_ss [CONCAT_def]);

(*---------------------------------------------------------------------------*)
(* All ways to split a list in 2 pieces                                      *)
(*---------------------------------------------------------------------------*)

val ALL_SPLITS_def = Define
  `(ALL_SPLITS (l,[]) = [(l,[])]) /\
   (ALL_SPLITS (l,h::t) = (l,h::t)::ALL_SPLITS(l<>[h],t))`;

val SPLITS_def = Define `SPLITS l = ALL_SPLITS ([],l)`;

(*---------------------------------------------------------------------------*)
(* Testing

    EVAL (Term`SPLITS [1;2;3;4]`);
    EVAL (Term`SPLITS [1;2;3;4;5;6;7;8;9]`);
    EVAL (Term`LENGTH (SPLITS [1;2;3;4;5;6;7;8;9;
                               1;2;3;4;5;6;7;8;9;
                               1;2;3;4;5;6;7;8;9])`);
*)
(*---------------------------------------------------------------------------*)

val ALL_SPLITS_LEMMA = prove
  (``!l1 l2 l3 l4. MEM (l3,l4) (ALL_SPLITS (l1,l2)) ==> (l1<>l2 = l3<>l4)``,
   Induct_on `l2` THEN RW_TAC list_ss [ALL_SPLITS_def] THEN
   METIS_TAC [APPEND,APPEND_ASSOC]);

val SPLITS_APPEND = prove
  (``!l l1 l2. MEM (l1,l2) (SPLITS l) ==> (l1<>l2 = l)``,
   RW_TAC list_ss [SPLITS_def] THEN
   METIS_TAC [ALL_SPLITS_LEMMA,APPEND]);

val MEM_ALL_SPLITS_ID = prove
  (``!x. MEM x (ALL_SPLITS x)``,
   Cases THEN Cases_on `r` THEN RW_TAC list_ss [ALL_SPLITS_def]);

val MEM_ALL_SPLITS_LEM = prove
  (``!l1 l2 w1 w2. (l2 = w1<>w2) ==> MEM (l1<>w1,w2) (ALL_SPLITS (l1, l2))``,
   recInduct (fetch "-" "ALL_SPLITS_ind")
   THEN RW_TAC list_ss [ALL_SPLITS_def,APPEND_ID_THM]
   THEN Cases_on `w1` THEN FULL_SIMP_TAC list_ss []
   THEN PROVE_TAC [APPEND_ASSOC,APPEND_CONS]);

val MEM_ALL_SPLITS = prove
  (``!w1 w2.  MEM (w1,w2) (ALL_SPLITS ([],w1<>w2))``,
   PROVE_TAC [MEM_ALL_SPLITS_LEM, CONJUNCT1 APPEND]);

val MEM_SPLITS = prove
  (``!w1 w2.  MEM (w1,w2) (SPLITS (w1<>w2))``,
   PROVE_TAC [MEM_ALL_SPLITS, SPLITS_def]);

val MEM_TL_SPLITS = prove
  (``!w1 w2. ~NULL w1 ==> MEM(w1,w2) (TL (SPLITS (w1<>w2)))``,
   RW_TAC list_ss [SPLITS_def, ALL_SPLITS_def]
   THEN Cases_on `w1` THEN FULL_SIMP_TAC list_ss [ALL_SPLITS_def]
   THEN ONCE_REWRITE_TAC [GSYM APPEND_CONS]
   THEN PURE_REWRITE_TAC [APPEND_NIL]
   THEN RW_TAC list_ss [SIMP_RULE bool_ss [] MEM_ALL_SPLITS_LEM]);

val SPLITS_LENGTH = prove
  (``!l l1 l2. MEM (l1,l2) (SPLITS l) ==> (LENGTH l1 + LENGTH l2 = LENGTH l)``,
   METIS_TAC [SPLITS_APPEND,LENGTH_APPEND]);

val SPLITS_NON_EMPTY = prove
  (``!l. ~NULL (SPLITS l)``,
   RW_TAC list_ss [SPLITS_def] THEN
   Induct_on `l` THEN RW_TAC list_ss [ALL_SPLITS_def]);

val lem = prove
  (``!l1 l2 l3 s1 s2.
       MEM (s1,s2) (ALL_SPLITS (l1,l2))
       ==>
       ?s3. MEM (s3,s2) (ALL_SPLITS (l3,l2))``,
   Induct_on `l2` THEN RW_TAC list_ss [ALL_SPLITS_def] THEN PROVE_TAC []);

val MEM_ALL_SPLITS_LENGTH = prove
  (``!l s1 s2.
       ~NULL l ==> MEM (s1,s2) (TL (SPLITS l)) ==> LENGTH s2 < LENGTH l``,
   REWRITE_TAC [SPLITS_def] THEN
   Induct THEN RW_TAC list_ss [ALL_SPLITS_def]
   THEN Cases_on `l`
   THEN FULL_SIMP_TAC list_ss [ALL_SPLITS_def]
   THEN METIS_TAC [lem, DECIDE (Term `x < y ==> x < SUC y`)]);

(*---------------------------------------------------------------------------*)
(* Datatype of regular expressions                                           *)
(* Modified by MJCG from KXS version to match Accellera PSL                  *)
(*---------------------------------------------------------------------------*)

val () = Hol_datatype
  `regexp =
     Atom of ('s -> bool)                 (* Boolean expression       *)
   | Cat of regexp => regexp              (* Concatenation            *)
   | Fuse of regexp => regexp             (* Fusion                   *)
   | Or of regexp => regexp               (* Disjunction              *)
   | And of regexp => regexp              (* Conjunction              *)
   | Repeat of regexp                     (* Iterated concat, >= 0    *)
   | Prefix of regexp`;                   (* Prefix                   *)

val Dot_def  = Define `Dot  = Atom (\x : 'a. T)`;
val Zero_def = Define `Zero = Atom (\x : 'a. F)`;
val One_def  = Define `One = Repeat Zero`;

(*---------------------------------------------------------------------------*)
(* Following mysterious invocations remove old-style syntax for conditionals *)
(* from the grammar and thus allow | to be used for "or" patterns.           *)
(*---------------------------------------------------------------------------*)

val _ = remove_termtok{term_name = "COND",tok="=>"};
val _ = overload_on ("|", Term`$Or`);
val _ = overload_on ("&", Term`$And`);
val _ = overload_on ("#", Term`$Cat`);
val _ = overload_on ("%", Term`$Fuse`);

val _ = set_fixity "|" (Infixr 501);
val _ = set_fixity "&" (Infixr 511);
val _ = set_fixity "#" (Infixr 601);
val _ = set_fixity "%" (Infixr 602);

(*---------------------------------------------------------------------------*)
(* PSL style semantics of regular expressions                                *)
(*                                                                           *)
(* sem r w means regular expression r matches word w (represented as a list) *)
(*---------------------------------------------------------------------------*)

val sem_def =
 Define
  `(sem (Atom b) w   =
     (LENGTH w = 1) /\ b(HD w))                                           /\
   (sem (r1#r2) w    =
     ?w1 w2. (w = w1<>w2) /\ sem r1 w1 /\ sem r2 w2)                      /\
   (sem (r1%r2) w    =
     ?w1 w2 l. (w = w1<>[l]<>w2) /\ sem r1 (w1<>[l]) /\ sem r2 ([l]<>w2)) /\
   (sem (r1|r2) w    =
     sem r1 w \/ sem r2 w)                                                /\
   (sem (r1&r2) w    =
     sem r1 w /\ sem r2 w)                                                /\
   (sem (Repeat r) w =
     ?wlist. (w = CONCAT wlist) /\ EVERY (sem r) wlist)                   /\
   (sem (Prefix r) w =
     ?w'. sem r (w <> w'))`;

val sem_Dot = store_thm
  ("sem_Dot",
   ``!l. sem Dot l = (LENGTH l = 1)``,
   RW_TAC std_ss [sem_def, Dot_def]);

val sem_Zero = store_thm
  ("sem_Zero",
   ``!l. ~(sem Zero l)``,
   RW_TAC std_ss [sem_def, Zero_def]);

val sem_One = store_thm
  ("sem_One",
   ``!l. sem One l = (l = [])``,
   RW_TAC std_ss [sem_def, One_def]
   ++ REVERSE EQ_TAC
   >> (RW_TAC std_ss []
       ++ Q.EXISTS_TAC `[]`
       ++ RW_TAC std_ss [CONCAT_def, ALL_EL])
   ++ RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `wlist`
   ++ RW_TAC std_ss [CONCAT_def, ALL_EL, sem_Zero]);

(*---------------------------------------------------------------------------*)
(* Misc. semantics lemmas                                                    *)
(*---------------------------------------------------------------------------*)

val Concat_ID = prove
(``!r w. (sem (r # One) w = sem r w) /\ (sem (One # r) w = sem r w)``,
 RW_TAC std_ss [sem_def, sem_One, APPEND_NIL]);

(* Should be true, but the proof is currently broken
val Then_ASSOC = Count.apply Q.prove
(`!r1 r2 r3 w. sem (r1 # (r2 # r3)) w = sem ((r1 # r2) # r3) w`,
  Cases THENL
  [EVAL_TAC THEN METIS_TAC [APPEND_ASSOC],
   EVAL_TAC THEN REPEAT GEN_TAC THEN EQ_TAC
    THEN RW_TAC list_ss [] THEN EVAL_TAC THENL
    [Q.EXISTS_TAC `x::w1'` THEN Q.EXISTS_TAC `w2'` THEN RW_TAC list_ss [] THEN
     Q.EXISTS_TAC `[x]` THEN Q.EXISTS_TAC `w1'` THEN RW_TAC list_ss [],
     Q.EXISTS_TAC `[x]` THEN Q.EXISTS_TAC `w2'<>w2`
       THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `c::w1` THEN Q.EXISTS_TAC `w2'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC `w2'<>w2` THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC`w1<>w1'` THEN Q.EXISTS_TAC`w2'` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w1` THEN Q.EXISTS_TAC`w1'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1<>w1'` THEN Q.EXISTS_TAC`w2'` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w1` THEN Q.EXISTS_TAC `w1'` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1'` THEN Q.EXISTS_TAC`w2'<>w2` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC `w2'` THEN Q.EXISTS_TAC `w2` THEN RW_TAC list_ss [],
      Q.EXISTS_TAC`w1'` THEN Q.EXISTS_TAC`w2'<>w2` THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC`w2'` THEN Q.EXISTS_TAC`w2` THEN RW_TAC list_ss []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `(w1'<>w2')<>w1''` THEN Q.EXISTS_TAC `w2''`
        THEN RW_TAC list_ss []
        THEN Q.EXISTS_TAC `w1'<>w2'` THEN Q.EXISTS_TAC `w1''`
        THEN RW_TAC list_ss [] THEN METIS_TAC[],
      Q.EXISTS_TAC `(w1''<>w2'')` THEN Q.EXISTS_TAC `w2'<>w2`
        THEN RW_TAC list_ss [] THEN METIS_TAC []],
     REPEAT GEN_TAC THEN EVAL_TAC THEN EQ_TAC THEN RW_TAC list_ss [] THENL
     [Q.EXISTS_TAC `(CONCAT wlist <> w1')` THEN Q.EXISTS_TAC `w2'`
        THEN RW_TAC list_ss [] THEN
      Q.EXISTS_TAC `CONCAT wlist` THEN Q.EXISTS_TAC `w1'` THEN METIS_TAC[],
      Q.EXISTS_TAC `CONCAT wlist` THEN Q.EXISTS_TAC `w2'<>w2`
        THEN RW_TAC list_ss [] THEN METIS_TAC[]]]);
*)

val Or_lemma = prove
  (``!r1 r2 r3. sem ((r1 | r2) # r3) w = sem (r1 # r3) w \/ sem (r2 # r3) w``,
   RW_TAC list_ss [sem_def] THEN PROVE_TAC []);

(*---------------------------------------------------------------------------*)
(* Checker - from a tech. report of Simon Thompson                           *)
(*---------------------------------------------------------------------------*)

val match_defn = Hol_defn
   "match"
  `(match (Atom b) l = (LENGTH l = 1) /\ b(HD l))
/\ (match (r1|r2) l  = match r1 l \/ match r2 l)
/\ (match (r1&r2) l  = match r1 l /\ match r2 l)
/\ (match (r1#r2) l  =
     EXISTS (\(s1,s2). match r1 s1 /\ match r2 s2) (SPLITS l))
/\ (match (r1%r2) l  =
     if NULL l then F else
     EXISTS (\(s1,s2). if NULL s2
                        then match r1 s1 /\ match r2 [LAST s1]
                        else match r1 (s1<>[HD s2]) /\ match r2 s2)
            (SPLITS l))
/\ (match (Repeat r) l =
      if NULL l then T
      else EXISTS (\(s1,s2). match r s1 /\ match (Repeat r) s2)
                  (TL(SPLITS l)))
/\ (match (Prefix r) l = ?l'. match r (l <> l'))`;

val (match_def, match_ind) = Defn.tprove
(match_defn,
 WF_REL_TAC `measure (regexp_size (K 0)) LEX (measure LENGTH)`
 THEN RW_TAC list_ss [fetch "-" "regexp_size_def"]
 THEN PROVE_TAC [MEM_ALL_SPLITS_LENGTH]);

(*---------------------------------------------------------------------------*)
(* Correctness of the matcher                                                *)
(*---------------------------------------------------------------------------*)

val sem_match = store_thm
  ("sem_match",
   ``!r w. sem r w = match r w``,
   recInduct match_ind THEN REPEAT CONJ_TAC THENL
   [(* Atom c *) RW_TAC list_ss [sem_def,match_def],
    (* r | r' *) RW_TAC list_ss [sem_def,match_def],
    (* r & r' *) RW_TAC list_ss [sem_def,match_def],
    (* r # r' *) RW_TAC list_ss [sem_def,match_def,EXISTS_ELIM_THM,GSYM IN_THM]
    THEN EQ_TAC THEN RW_TAC list_ss [] THENL
    [Q.EXISTS_TAC `(w1,w2)`
     THEN SIMP_TAC list_ss [MEM_SPLITS] THEN PROVE_TAC [MEM_SPLITS],
     Cases_on`x` THEN FULL_SIMP_TAC list_ss [] THEN PROVE_TAC[SPLITS_APPEND]],
    (* r1 % r2 *)
    RW_TAC list_ss [sem_def,match_def,EXISTS_ELIM_THM,GSYM IN_THM]
    THEN EQ_TAC THEN SIMP_TAC list_ss [pairTheory.EXISTS_PROD] THENL
    [STRIP_TAC THEN
     `~NULL (w1 <> [l'] <> w2)` by (Cases_on `w1` THEN RW_TAC list_ss []) THEN
     `MEM (w1, l' ::w2) (SPLITS (w1 <> [l'] <> w2))`
     by PROVE_TAC[MEM_SPLITS,GSYM listTheory.APPEND_ASSOC,APPEND_CONS]
     THEN ASM_SIMP_TAC list_ss []
     THEN MAP_EVERY Q.EXISTS_TAC [`w1`, `l' ::w2`]
     THEN RW_TAC list_ss []
     THEN METIS_TAC [listTheory.NULL,APPEND_CONS,listTheory.HD],
     Cases_on `l` THEN FULL_SIMP_TAC list_ss []
     THEN BasicProvers.NORM_TAC list_ss []
     THEN Cases_on `p_2` THEN FULL_SIMP_TAC list_ss [] THENL
     [METIS_TAC [listTheory.APPEND_FRONT_LAST,listTheory.NULL,
                 SPLITS_APPEND,APPEND_NIL],
      METIS_TAC [SPLITS_APPEND,CONS_APPEND,listTheory.NULL, listTheory.HD,
                 listTheory.APPEND_ASSOC,listTheory.APPEND_FRONT_LAST]]],
    (* Repeat r *)
    RW_TAC list_ss [sem_def]
    THEN ONCE_REWRITE_TAC [match_def]
    THEN RW_TAC list_ss [EXISTS_ELIM_THM]
    THEN Cases_on `NULL l` THENL
    [RW_TAC list_ss [] THEN Q.EXISTS_TAC `[]` THEN
     RW_TAC list_ss [CONCAT_def] THEN PROVE_TAC [NULL_EQ_NIL],
     FULL_SIMP_TAC list_ss [GSYM IN_THM] THEN EQ_TAC THEN
     RW_TAC list_ss [EXISTS_PROD] THENL
     [`EXISTS ($~ o NULL) wlist` by PROVE_TAC [NULL_CONCAT_THM,NOT_EVERY] THEN
      IMP_RES_TAC FIRST_EXISTS_THM THEN
      RULE_ASSUM_TAC (SIMP_RULE list_ss [o_DEF]) THEN
      `sem r w /\ EVERY (sem r) suffix` by FULL_SIMP_TAC list_ss [EVERY_APPEND]
      THEN
      `CONCAT wlist = CONCAT (w::suffix)`
      by (RW_TAC list_ss [CONCAT_APPEND_DISTRIB,CONCAT_def] THEN
          RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV ETA_CONV)) THEN
          METIS_TAC[NULL_CONCAT_THM,APPEND,NULL_EQ_NIL]) THEN
      `MEM (w,CONCAT suffix) (TL(SPLITS(CONCAT wlist)))`
      by RW_TAC list_ss [CONCAT_def, MEM_TL_SPLITS] THEN
      PROVE_TAC []
      ,
      `?wlist. (p_2=CONCAT wlist) /\ EVERY (sem r) wlist` by PROVE_TAC[] THEN
      Q.EXISTS_TAC `p_1::wlist` THEN RW_TAC list_ss [CONCAT_def] THEN
      PROVE_TAC [MEM_TL,SPLITS_NON_EMPTY,SPLITS_APPEND]]],
    RW_TAC std_ss [sem_def, match_def]]);

val () = export_theory ();
