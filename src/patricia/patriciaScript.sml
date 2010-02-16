(* ========================================================================= *)
(* FILE         : patriciaScript.sml                                         *)
(* DESCRIPTION  : A Patricia tree implementation of finite maps: num |-> 'a  *)
(* AUTHOR       : Anthony Fox, University of Cambridge                       *)
(* DATE         : 2008                                                       *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "bitSyntax", "sortingTheory", "pred_setSyntax"];
*)

open HolKernel Parse boolLib bossLib Q
     arithmeticTheory numeralTheory bitTheory numeral_bitTheory
     listTheory rich_listTheory sortingTheory;

val _ = new_theory "patricia";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = wordsLib.deprecate_word();

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "'" (Infixl 2000);
val _ = set_fixity "|+"  (Infixl 600);
val _ = set_fixity "|++" (Infixl 500);
val _ = set_fixity "\\\\" (Infixl 600);

val _ = Hol_datatype`
  ptree = Empty | Leaf of num => 'a | Branch of num => num => ptree => ptree`;

val _ = computeLib.auto_import_definitions := false;

val BRANCHING_BIT_def = tDefine "BRANCHING_BIT"
  `BRANCHING_BIT p0 p1 =
    if (ODD p0 = EVEN p1) \/ (p0 = p1) then 0
    else SUC (BRANCHING_BIT (DIV2 p0) (DIV2 p1))`
 (WF_REL_TAC `measure (\(x,y). x + y)` \\ SRW_TAC [ARITH_ss] [DIV2_def]
    \\ Cases_on `ODD p0` \\ FULL_SIMP_TAC bool_ss []
    \\ FULL_SIMP_TAC bool_ss [GSYM ODD_EVEN, GSYM EVEN_ODD]
    \\ IMP_RES_TAC EVEN_ODD_EXISTS
    \\ SRW_TAC [ARITH_ss] [ADD1,
         ONCE_REWRITE_RULE [MULT_COMM] (CONJ ADD_DIV_ADD_DIV MULT_DIV)]);

val PEEK_def = Define`
  (PEEK Empty k = NONE) /\
  (PEEK (Leaf j d) k = if k = j then SOME d else NONE) /\
  (PEEK (Branch p m l r) k = PEEK (if BIT m k then l else r) k)`;

val _ = overload_on ("'", Term`$PEEK`);

val JOIN_def = Define`
  JOIN (p0,t0,p1,t1) =
    let m = BRANCHING_BIT p0 p1 in
      if BIT m p0 then
        Branch (MOD_2EXP m p0) m t0 t1
      else
        Branch (MOD_2EXP m p0) m t1 t0`;

val ADD_def = Define`
  (ADD Empty (k,e) = Leaf k e) /\
  (ADD (Leaf j d) (k,e) = if j = k then Leaf k e
                           else JOIN (k, Leaf k e, j, Leaf j d)) /\
  (ADD (Branch p m l r) (k,e) =
         if MOD_2EXP_EQ m k p then
           if BIT m k then
                Branch p m (ADD l (k,e)) r
              else
                Branch p m l (ADD r (k,e))
         else
           JOIN (k, Leaf k e, p, Branch p m l r))`;

val _ = overload_on ("|+", Term`$ADD`);

val BRANCH_def = Define`
  (BRANCH (p,m,Empty,t) = t) /\
  (BRANCH (p,m,t,Empty) = t) /\
  (BRANCH (p,m,t0,t1) = Branch p m t0 t1)`;

val REMOVE_def = Define`
  (REMOVE Empty k = Empty) /\
  (REMOVE (Leaf j d) k = if j = k then Empty else Leaf j d) /\
  (REMOVE (Branch p m l r) k =
         if MOD_2EXP_EQ m k p then
           if BIT m k then
             BRANCH (p, m, REMOVE l k, r)
           else
             BRANCH (p, m, l, REMOVE r k)
         else
           Branch p m l r)`;

val _ = overload_on ("\\\\", Term`$REMOVE`);

val TRAVERSE_AUX_def =
  with_flag (computeLib.auto_import_definitions, true) Define`
    (TRAVERSE_AUX Empty a = a) /\
    (TRAVERSE_AUX (Leaf k d) a = k::a) /\
    (TRAVERSE_AUX (Branch p m l r) a = TRAVERSE_AUX l (TRAVERSE_AUX r a))`;

val TRAVERSE_def = Define`
  (TRAVERSE Empty = []) /\
  (TRAVERSE (Leaf j d) = [j]) /\
  (TRAVERSE (Branch p m l r) = TRAVERSE l ++ TRAVERSE r)`;

val KEYS_def = with_flag (computeLib.auto_import_definitions, true) Define`
  KEYS t = QSORT $< (TRAVERSE t)`;

val TRANSFORM_def = Define`
  (TRANSFORM f Empty = Empty) /\
  (TRANSFORM f (Leaf j d) = Leaf j (f d)) /\
  (TRANSFORM f (Branch p m l r) = Branch p m (TRANSFORM f l) (TRANSFORM f r))`;

val EVERY_LEAF_def = Define`
  (EVERY_LEAF P Empty = T) /\
  (EVERY_LEAF P (Leaf j d) = P j d) /\
  (EVERY_LEAF P (Branch p m l r) = EVERY_LEAF P l /\ EVERY_LEAF P r)`;

val EXISTS_LEAF_def = Define`
  (EXISTS_LEAF P Empty = F) /\
  (EXISTS_LEAF P (Leaf j d) = P j d) /\
  (EXISTS_LEAF P (Branch p m l r) = EXISTS_LEAF P l \/ EXISTS_LEAF P r)`;

val SIZE_def = Define `SIZE t = LENGTH (TRAVERSE t)`;

val DEPTH_def = Define`
  (DEPTH Empty = 0) /\
  (DEPTH (Leaf j d) = 1) /\
  (DEPTH (Branch p m l r) = 1 + MAX (DEPTH l) (DEPTH r))`;

val IS_PTREE_def = Define`
  (IS_PTREE Empty = T) /\
  (IS_PTREE (Leaf k d) = T) /\
  (IS_PTREE (Branch p m l r) =
     p < 2 ** m /\ IS_PTREE l /\ IS_PTREE r /\
     ~(l = Empty) /\ ~(r = Empty) /\
     EVERY_LEAF (\k d. MOD_2EXP_EQ m k p /\ BIT m k) l /\
     EVERY_LEAF (\k d. MOD_2EXP_EQ m k p /\ ~BIT m k) r)`;

(* ------------------------------------------------------------------------- *)

val _ = hide "set";
val _ = overload_on("LIST_TO_SET", ``list$LIST_TO_SET``);

val _ = set_fixity "IN_PTREE" (Infix (NONASSOC, 425));
val _ = set_fixity "INSERT_PTREE" (Infixr 490);
val _ = set_fixity "UNION_PTREE" (Infixl 500);

val _ = type_abbrev("ptreeset", ``:unit ptree``);

val IN_PTREE_def = Define `$IN_PTREE n t = IS_SOME (PEEK (t:unit ptree) n)`;
val INSERT_PTREE_def = Define `$INSERT_PTREE n t = ADD t (n,())`;

val _ = add_listform {leftdelim = [TOK "<{"], rightdelim = [TOK "}>"],
                      separator = [TOK ";", BreakSpace(1,0)],
                      cons = "INSERT_PTREE", nilstr = "Empty",
                      block_info = (PP.INCONSISTENT, 0)};

val PTREE_OF_NUMSET_def = Define`
  PTREE_OF_NUMSET t (s:num set) =
  FOLDL (combin$C $INSERT_PTREE) t (SET_TO_LIST s)`;

val _ = overload_on ("|++", Term`$PTREE_OF_NUMSET`);

val _ = computeLib.auto_import_definitions := true;

val NUMSET_OF_PTREE_def = Define`
  NUMSET_OF_PTREE (t:unit ptree) = LIST_TO_SET (TRAVERSE t)`;

val UNION_PTREE_def = Define`
  $UNION_PTREE t1 t2 = PTREE_OF_NUMSET t1 (NUMSET_OF_PTREE t2)`;

val IS_EMPTY_def = Define `(IS_EMPTY Empty = T) /\ (IS_EMPTY _ = F)`;

val FIND_def = Define `FIND t k = THE (PEEK t k)`;

val ADD_LIST_def = Define `ADD_LIST = FOLDL ADD`;

val _ = overload_on ("|++", Term`$ADD_LIST`);

(* ------------------------------------------------------------------------- *)

val lem = prove(
  `!n a b. n < BRANCHING_BIT a b ==> (BIT n a = BIT n b)`,
  Induct \\ SRW_TAC [] [Once BRANCHING_BIT_def, GSYM BIT_DIV2, DIV2_def]
    \\ SPOSE_NOT_THEN STRIP_ASSUME_TAC
    \\ `ODD a = EVEN b` by METIS_TAC [EVEN_ODD]
    \\ FULL_SIMP_TAC arith_ss [Once BRANCHING_BIT_def]);

val MOD_2EXP_EQ_BRANCHING_BIT = prove(
  `!a b. MOD_2EXP_EQ (BRANCHING_BIT a b) a b`,
  NTAC 2 STRIP_TAC \\ Cases_on `BRANCHING_BIT a b`
    \\ SRW_TAC [ARITH_ss] [GSYM BIT_BITS_THM, GSYM BITS_ZERO3,
          MOD_2EXP_EQ_def, MOD_2EXP_def, lem]);

val NOT_MOD_2EXP_EQ_IMP_BRANCHING_BIT_LT = prove(
  `!n a b. ~MOD_2EXP_EQ n a b ==> BRANCHING_BIT a b < n`,
  Cases \\ SRW_TAC [] [GSYM BIT_BITS_THM, MOD_2EXP_EQ_def, MOD_2EXP_def,
                       GSYM BITS_ZERO3]
    \\ SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LESS])
    \\ `x < BRANCHING_BIT a b` by DECIDE_TAC
    \\ IMP_RES_TAC lem);

val MOD_2EXP_EQ_BIT_EQ = prove(
  `!n a b. MOD_2EXP_EQ n a b ==> (!x. x < n ==> (BIT x a = BIT x b))`,
  Cases \\ SRW_TAC [ARITH_ss]
    [MOD_2EXP_EQ_def, MOD_2EXP_def, GSYM BIT_BITS_THM, GSYM BITS_ZERO3]);

val MOD_2EXP_EQ_REFL = prove(
  `!n a. MOD_2EXP_EQ n a a`, METIS_TAC [MOD_2EXP_EQ_def]);

val MOD_2EXP_EQ_SYM = prove(
  `!n a b. MOD_2EXP_EQ n a b = MOD_2EXP_EQ n b a`,
  METIS_TAC [MOD_2EXP_EQ_def]);

val MOD_2EXP_EQ_TRANS = prove(
  `!n a b c. MOD_2EXP_EQ n a b /\ MOD_2EXP_EQ n b c ==> MOD_2EXP_EQ n a c`,
  METIS_TAC [MOD_2EXP_EQ_def]);

val NOT_MOD_2EXP_EQ = prove(
  `!n a b. ~MOD_2EXP_EQ n a b ==> ~(a = b)`,
  METIS_TAC [MOD_2EXP_EQ_def]);

val MOD_2EXP_EQ_MOD_2EXP = prove(
  `(!n a b. MOD_2EXP_EQ n a (MOD_2EXP n b) = MOD_2EXP_EQ n a b) /\
   (!n a b. MOD_2EXP_EQ n (MOD_2EXP n a) b = MOD_2EXP_EQ n a b)`,
  SRW_TAC [ARITH_ss] [MOD_2EXP_EQ_def, MOD_2EXP_def]);

val MONO_MOD_2EXP_EQ = prove(
  `!m n a b. n <= m /\ MOD_2EXP_EQ m a b ==> MOD_2EXP_EQ n a b`,
  Cases \\ Cases \\ SRW_TAC [ARITH_ss] [MOD_2EXP_EQ_def, MOD_2EXP_def,
    GSYM BIT_BITS_THM, GSYM BITS_ZERO3]);

val lem = prove(
  `!a b. ~(a = b) /\ ~(ODD a = EVEN b) ==> ~(a DIV 2 = b DIV 2)`,
  SRW_TAC [] [METIS_PROVE [EVEN_MOD2,ODD_MOD2_LEM,NOT_MOD2_LEM2]
                ``~(ODD a = EVEN b) = (a MOD 2 = b MOD 2)``]
    \\ STRIP_TAC
    \\ PAT_ASSUM `~(a = b)` MATCH_MP_TAC
    \\ ONCE_REWRITE_TAC [(SIMP_RULE std_ss [] o SPEC `2`) DIVISION]
    \\ SRW_TAC [] []);

val BRANCHING_BIT = store_thm("BRANCHING_BIT",
  `!a b. ~(a = b) ==> ~(BIT (BRANCHING_BIT a b) a = BIT (BRANCHING_BIT a b) b)`,
  Induct_on `BRANCHING_BIT a b` \\ SRW_TAC [] []
    << [
      PAT_ASSUM `0 = x` (fn th => let val sth = SYM th in
                           SUBST1_TAC sth THEN ASSUME_TAC sth end)
        \\ Cases_on `ODD a = EVEN b`
        \\ FULL_SIMP_TAC arith_ss
             [EVEN_ODD, Once BRANCHING_BIT_def, GSYM LSB_def, LSB_ODD]
        \\ METIS_TAC [],
      ONCE_REWRITE_TAC [BRANCHING_BIT_def]
        \\ SRW_TAC [] [GSYM BIT_DIV2, DIV2_def] >> METIS_TAC [EVEN_ODD]
        \\ PAT_ASSUM `!a b. P` (SPECL_THEN [`a DIV 2`,`b DIV 2`] ASSUME_TAC)
        \\ IMP_RES_TAC lem
        \\ FULL_SIMP_TAC std_ss [lem]
        \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MATCH_MP_TAC
        \\ RULE_ASSUM_TAC (REWRITE_RULE [Once BRANCHING_BIT_def])
        \\ FULL_SIMP_TAC std_ss [DIV2_def]]);

val BRANCHING_BIT_ZERO = store_thm("BRANCHING_BIT_ZERO",
  `!a b. (BRANCHING_BIT a b = 0) = (ODD a = EVEN b) \/ (a = b)`,
  SRW_TAC [ARITH_ss] [Once BRANCHING_BIT_def]);

val BRANCHING_BIT_SYM = store_thm("BRANCHING_BIT_SYM",
  `!a b. BRANCHING_BIT a b = BRANCHING_BIT b a`,
  Induct_on `BRANCHING_BIT a b` \\ SRW_TAC [] []
    >> METIS_TAC [BRANCHING_BIT_ZERO,
         ONCE_REWRITE_RULE [METIS_PROVE [ODD_EVEN]
            ``(ODD a = EVEN b) = (ODD b = EVEN a)``] BRANCHING_BIT_ZERO]
    \\ ONCE_REWRITE_TAC [BRANCHING_BIT_def]
    \\ SRW_TAC [] [GSYM BIT_DIV2, DIV2_def]
    << [METIS_TAC [EVEN_ODD], METIS_TAC [EVEN_ODD],
        RULE_ASSUM_TAC (REWRITE_RULE [Once BRANCHING_BIT_def])
          \\ FULL_SIMP_TAC (srw_ss()) []
          \\ METIS_TAC [DIV2_def]]);

val EVERY_LEAF_ADD = store_thm("EVERY_LEAF_ADD",
  `!P t k d. P k d /\ EVERY_LEAF P t ==> EVERY_LEAF P (ADD t (k,d))`,
  Induct_on `t`
    \\ SRW_TAC [boolSimps.LET_ss] [ADD_def, EVERY_LEAF_def, JOIN_def]);

val MONO_EVERY_LEAF = store_thm("MONO_EVERY_LEAF",
  `!P Q t. (!k d. P k d ==> Q k d) /\ EVERY_LEAF P t ==> EVERY_LEAF Q t`,
  Induct_on `t` \\ SRW_TAC [] [EVERY_LEAF_def] \\ METIS_TAC []);

val NOT_ADD_EMPTY = store_thm("NOT_ADD_EMPTY",
  `!t k d. ~(ADD t (k,d) = Empty)`,
  Cases \\ SRW_TAC [] [ADD_def, JOIN_def] \\ SRW_TAC [] []);

val MOD_2EXP_LT_COR =
  METIS_PROVE [MOD_2EXP_LT, MOD_2EXP_def] ``MOD_2EXP x n < 2 ** x``;

val EMPTY_IS_PTREE = save_thm("EMPTY_IS_PTREE",
  EQT_ELIM (CONJUNCT1 IS_PTREE_def));

val ADD_IS_PTREE = store_thm("ADD_IS_PTREE",
  `!t x. IS_PTREE t ==> IS_PTREE (ADD t x)`,
  Cases_on `x` \\ Induct
    \\ SRW_TAC [boolSimps.LET_ss]
         [MOD_2EXP_EQ_MOD_2EXP, MOD_2EXP_EQ_REFL, EVERY_LEAF_ADD,
          IS_PTREE_def, ADD_def, JOIN_def, EVERY_LEAF_def]
    \\ TRY (METIS_TAC [MOD_2EXP_EQ_SYM, MOD_2EXP_EQ_BRANCHING_BIT,
                       BRANCHING_BIT, NOT_ADD_EMPTY, MOD_2EXP_LT_COR])
    << [
      SPEC_THEN `\k d. MOD_2EXP_EQ n k n0 /\ BIT n k`
                MATCH_MP_TAC MONO_EVERY_LEAF
        \\ `~BIT (BRANCHING_BIT q n0) n0`
        by METIS_TAC [NOT_MOD_2EXP_EQ, BRANCHING_BIT],
      SPEC_THEN `\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k`
                MATCH_MP_TAC MONO_EVERY_LEAF
        \\ `~BIT (BRANCHING_BIT q n0) n0`
        by METIS_TAC [NOT_MOD_2EXP_EQ, BRANCHING_BIT],
      SPEC_THEN `\k d. MOD_2EXP_EQ n k n0 /\ BIT n k`
                MATCH_MP_TAC MONO_EVERY_LEAF
        \\ `BIT (BRANCHING_BIT q n0) n0`
        by METIS_TAC [NOT_MOD_2EXP_EQ, BRANCHING_BIT],
      SPEC_THEN `\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k`
                MATCH_MP_TAC MONO_EVERY_LEAF
        \\ `BIT (BRANCHING_BIT q n0) n0`
        by METIS_TAC [NOT_MOD_2EXP_EQ, BRANCHING_BIT]]
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC NOT_MOD_2EXP_EQ_IMP_BRANCHING_BIT_LT
    \\ `MOD_2EXP_EQ (BRANCHING_BIT q n0) n0 q`
    by METIS_TAC [MOD_2EXP_EQ_BRANCHING_BIT, MOD_2EXP_EQ_SYM]
    \\ METIS_TAC [MONO_MOD_2EXP_EQ, DECIDE ``a < b ==> a <= b:num``,
                  MOD_2EXP_EQ_SYM, MOD_2EXP_EQ_TRANS, MOD_2EXP_EQ_BIT_EQ]);

val _ = export_rewrites ["EMPTY_IS_PTREE", "ADD_IS_PTREE"];

val EVERY_LEAF_BRANCH = store_thm("EVERY_LEAF_BRANCH",
  `!P p m l r. EVERY_LEAF P (BRANCH (p, m, l, r)) =
             EVERY_LEAF P l /\ EVERY_LEAF P r`,
  Cases_on `l` \\ Cases_on `r` \\ SRW_TAC [] [BRANCH_def, EVERY_LEAF_def]);

val EVERY_LEAF_REMOVE = store_thm("EVERY_LEAF_REMOVE",
  `!P t k. EVERY_LEAF P t ==> EVERY_LEAF P (REMOVE t k)`,
  Induct_on `t` \\ SRW_TAC [] [REMOVE_def, EVERY_LEAF_def, EVERY_LEAF_BRANCH]);

val IS_PTREE_BRANCH = store_thm("IS_PTREE_BRANCH",
  `!p m l r. p < 2 ** m /\ ~((l = Empty) /\ (r = Empty)) /\
             EVERY_LEAF (\k d. MOD_2EXP_EQ m k p /\ BIT m k) l /\
             EVERY_LEAF (\k d. MOD_2EXP_EQ m k p /\ ~BIT m k) r /\
             IS_PTREE l /\ IS_PTREE r ==>
             IS_PTREE (BRANCH (p, m, l, r))`,
  Cases_on `l` \\ Cases_on `r`
    \\ SRW_TAC [] [BRANCH_def, IS_PTREE_def, EVERY_LEAF_def]);

val REMOVE_IS_PTREE = store_thm("REMOVE_IS_PTREE",
  `!t k. IS_PTREE t ==> IS_PTREE (REMOVE t k)`,
  Induct \\ SRW_TAC [] [REMOVE_def, IS_PTREE_def]
    \\ METIS_TAC [IS_PTREE_BRANCH, EVERY_LEAF_REMOVE]);

val _ = export_rewrites ["REMOVE_IS_PTREE"];

val PEEK_NONE = store_thm("PEEK_NONE",
  `!P t k. (!d. ~P k d) /\ EVERY_LEAF P t ==> (PEEK t k = NONE)`,
  Induct_on `t` \\ SRW_TAC [] [EVERY_LEAF_def, PEEK_def] \\ METIS_TAC []);

val PEEK_NONE_LEFT = SPEC `\k d. MOD_2EXP_EQ n k n0 /\ BIT n k` PEEK_NONE;
val PEEK_NONE_RIGHT = SPEC `\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k` PEEK_NONE;

val PEEK_ADD = store_thm("PEEK_ADD",
  `!t k d j. IS_PTREE t ==>
       (PEEK (ADD t (k,d)) j = if k = j then SOME d else PEEK t j)`,
  Induct_on `t`
    \\ SRW_TAC [boolSimps.LET_ss] [ADD_def, PEEK_def, JOIN_def, IS_PTREE_def]
    \\ SRW_TAC [] [PEEK_def]
    \\ METIS_TAC [NOT_MOD_2EXP_EQ_IMP_BRANCHING_BIT_LT, BRANCHING_BIT,
         MOD_2EXP_EQ_BIT_EQ, NOT_MOD_2EXP_EQ, PEEK_NONE_LEFT, PEEK_NONE_RIGHT]);

val BRANCH = store_thm("BRANCH",
  `!p m l r. BRANCH (p,m,l,r) =
             if l = Empty then r
             else if r = Empty then l
             else Branch p m l r`,
  Cases_on `l` \\ Cases_on `r` \\ SRW_TAC [] [BRANCH_def]);

val PEEK_REMOVE = store_thm("PEEK_REMOVE",
  `!t k j. IS_PTREE t ==>
       (PEEK (REMOVE t k) j = if k = j then NONE else PEEK t j)`,
  Induct_on `t`
    \\ SRW_TAC [boolSimps.LET_ss]
         [PEEK_def, REMOVE_def, IS_PTREE_def, IS_PTREE_BRANCH, BRANCH_def]
    \\ SRW_TAC [] [BRANCH, PEEK_def]
    \\ METIS_TAC [PEEK_NONE_LEFT, PEEK_NONE_RIGHT, PEEK_def]);

val EVERY_LEAF_TRANSFORM = store_thm("EVERY_LEAF_TRANSFORM",
  `!P Q f t. (!k d. P k d ==> Q k (f d)) /\ EVERY_LEAF P t ==>
           EVERY_LEAF Q (TRANSFORM f t)`,
  Induct_on `t` \\ SRW_TAC [] [TRANSFORM_def, EVERY_LEAF_def] \\ METIS_TAC []);

val EVERY_LEAF_TRANSFORM_LEFT = (SIMP_RULE (srw_ss()) [] o
  SPECL [`\k d. MOD_2EXP_EQ n k n0 /\ BIT n k`,
         `\k d. MOD_2EXP_EQ n k n0 /\ BIT n k`]) EVERY_LEAF_TRANSFORM;

val EVERY_LEAF_TRANSFORM_RIGHT = (SIMP_RULE (srw_ss()) [] o
  SPECL [`\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k`,
         `\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k`]) EVERY_LEAF_TRANSFORM;

val TRANSFORM_EMPTY = store_thm("TRANSFORM_EMPTY",
  `!f t. (TRANSFORM f t = Empty) = (t = Empty)`,
  Cases_on `t` \\ SRW_TAC [] [TRANSFORM_def]);

val TRANSFORM_IS_PTREE = store_thm("TRANSFORM_IS_PTREE",
  `!f t. IS_PTREE t ==> IS_PTREE (TRANSFORM f t)`,
  Induct_on `t` \\ SRW_TAC [] [TRANSFORM_def, IS_PTREE_def, TRANSFORM_EMPTY]
    \\ METIS_TAC [EVERY_LEAF_TRANSFORM_LEFT, EVERY_LEAF_TRANSFORM_RIGHT]);

val _ = export_rewrites ["TRANSFORM_IS_PTREE"];

val PEEK_TRANSFORM = store_thm("PEEK_TRANSFORM",
  `!f t k. PEEK (TRANSFORM f t) k =
              case PEEK t k of
                 NONE -> NONE
              || SOME x -> SOME (f x)`,
  Induct_on `t` \\ SRW_TAC [] [TRANSFORM_def, PEEK_def]);

val ADD_TRANSFORM = store_thm("ADD_TRANSFORM",
  `!f t k d. TRANSFORM f (ADD t (k,d)) = ADD (TRANSFORM f t) (k,f d)`,
  Induct_on `t` \\ SRW_TAC [] [TRANSFORM_def, ADD_def, JOIN_def]
    \\ SRW_TAC [] [TRANSFORM_def]);

val TRANSFORM_BRANCH = store_thm("TRANSFORM_BRANCH",
  `!f p m l r. TRANSFORM f (BRANCH (p,m,l,r)) =
               BRANCH (p,m,TRANSFORM f l, TRANSFORM f r)`,
  Cases_on `l` \\ Cases_on `r` \\ SRW_TAC [] [BRANCH_def, TRANSFORM_def]);

val REMOVE_TRANSFORM = store_thm("REMOVE_TRANSFORM",
  `!f t k. TRANSFORM f (REMOVE t k) = REMOVE (TRANSFORM f t) k`,
  Induct_on `t` \\ SRW_TAC [] [TRANSFORM_def, REMOVE_def, TRANSFORM_BRANCH]);

val REMOVE_ADD_EQ = store_thm("REMOVE_ADD_EQ",
  `!t k d. REMOVE (ADD t (k,d)) k = REMOVE t k`,
  Induct
    \\ SRW_TAC [boolSimps.LET_ss]
         [MOD_2EXP_EQ_BRANCHING_BIT, MOD_2EXP_EQ_MOD_2EXP, MOD_2EXP_EQ_REFL,
          REMOVE_def, ADD_def, JOIN_def, BRANCH_def]);

val ADD_ADD = store_thm("ADD_ADD",
  `!t k d e. ADD (ADD t (k,d)) (k,e) = ADD t (k,e)`,
  Induct \\ SRW_TAC [boolSimps.LET_ss]
    [MOD_2EXP_EQ_MOD_2EXP, MOD_2EXP_EQ_REFL, ADD_def, JOIN_def]);

val _ = export_rewrites ["REMOVE_ADD_EQ", "ADD_ADD"];

val EVERY_LEAF_PEEK = store_thm("EVERY_LEAF_PEEK",
  `!P t k. EVERY_LEAF P t /\ IS_SOME (PEEK t k) ==> P k (THE (PEEK t k))`,
  Induct_on `t` \\ SRW_TAC [] [PEEK_def, EVERY_LEAF_def]);

val EVERY_LEAF_PEEK_LEFT = (SIMP_RULE (srw_ss()) [] o
  SPEC `\k d. MOD_2EXP_EQ n k n0 /\ BIT n k`) EVERY_LEAF_PEEK;

val EVERY_LEAF_PEEK_RIGHT = (SIMP_RULE (srw_ss()) [] o
  SPEC `\k d. MOD_2EXP_EQ n k n0 /\ ~BIT n k`) EVERY_LEAF_PEEK;

val PEEK_NONE_LEFT = SPEC `\k d. MOD_2EXP_EQ m k p /\ BIT m k` PEEK_NONE;
val PEEK_NONE_RIGHT = SPEC `\k d. MOD_2EXP_EQ m k p /\ ~BIT m k` PEEK_NONE;

val IS_PTREE_PEEK = store_thm("IS_PTREE_PEEK",
  `(!k. ~IS_SOME (PEEK Empty k)) /\
   (!k j b. IS_SOME (PEEK (Leaf j b) k) = (j = k)) /\
   (!p m l r.
      IS_PTREE (Branch p m l r) ==>
      (?k. BIT m k /\ IS_SOME (PEEK l k)) /\
      (?k. ~BIT m k /\ IS_SOME (PEEK r k)) /\
      (!k n. ~MOD_2EXP_EQ m k p \/ n < m /\ ~(BIT n p = BIT n k) ==>
          ~IS_SOME (PEEK l k) /\ ~IS_SOME (PEEK r k)))`,
  SRW_TAC [] [PEEK_def]
    << [
     Induct_on `l` \\ SRW_TAC [] [IS_PTREE_def, PEEK_def]
       >> (EXISTS_TAC `n` \\ FULL_SIMP_TAC (srw_ss()) [EVERY_LEAF_def])
       \\ `IS_PTREE (Branch p m l r) /\ IS_PTREE (Branch p m l' r)`
       by FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def, EVERY_LEAF_def]
       \\ METIS_TAC [EVERY_LEAF_PEEK_LEFT, EVERY_LEAF_PEEK_RIGHT],
     Induct_on `r` \\ SRW_TAC [] [IS_PTREE_def, PEEK_def]
       >> (EXISTS_TAC `n` \\ FULL_SIMP_TAC (srw_ss()) [EVERY_LEAF_def])
       \\ `IS_PTREE (Branch p m l r) /\ IS_PTREE (Branch p m l r')`
       by FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def, EVERY_LEAF_def]
       \\ METIS_TAC [EVERY_LEAF_PEEK_LEFT, EVERY_LEAF_PEEK_RIGHT],
     FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
       \\ METIS_TAC [PEEK_NONE_LEFT, PEEK_NONE_RIGHT],
     FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
       \\ METIS_TAC [PEEK_NONE_LEFT, PEEK_NONE_RIGHT],
     FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
       \\ METIS_TAC [MOD_2EXP_EQ_BIT_EQ, PEEK_NONE_LEFT, PEEK_NONE_RIGHT],
     FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
       \\ METIS_TAC [MOD_2EXP_EQ_BIT_EQ, PEEK_NONE_LEFT, PEEK_NONE_RIGHT]]);

val IS_NONE_SOME =
  METIS_PROVE [optionTheory.IS_NONE_EQ_NONE, optionTheory.NOT_IS_SOME_EQ_NONE]
  ``~IS_NONE x = IS_SOME x``;

val OPTION_EQ = prove(
  `!a b. (a = b) = (~IS_SOME a /\ ~IS_SOME b) \/
                   (IS_SOME a /\ IS_SOME b) /\ (THE a = THE b)`,
  Cases \\ Cases \\ SRW_TAC [] []);

val LT_MOD_2EXP_EQ = prove(
  `!n a b. a < 2 ** n /\ b < 2 ** n /\ MOD_2EXP_EQ n a b ==> (a = b)`,
  SIMP_TAC (arith_ss++boolSimps.CONJ_ss)
    [MOD_2EXP_EQ_def, MOD_2EXP_def, ZERO_LT_TWOEXP]);

val PEEK_NONE_LEFT = SPEC `\k d. MOD_2EXP_EQ n' k n0' /\ BIT n' k` PEEK_NONE;
val PEEK_NONE_RIGHT = SPEC `\k d. MOD_2EXP_EQ n' k n0' /\ ~BIT n' k` PEEK_NONE;

val PTREE_EQ = store_thm("PTREE_EQ",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           ((!k. PEEK t1 k = PEEK t2 k) = (t1 = t2))`,
  Induct \\ Induct_on `t2`
    \\ SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [OPTION_EQ]
    \\ SIMP_TAC bool_ss [IS_PTREE_PEEK, IS_NONE_SOME]
    \\ RW_TAC bool_ss [PEEK_def]
    << [
      METIS_TAC [IS_PTREE_PEEK],
      METIS_TAC [IS_PTREE_PEEK, optionTheory.THE_DEF],
      METIS_TAC [IS_PTREE_PEEK], METIS_TAC [IS_PTREE_PEEK],
      METIS_TAC [IS_PTREE_PEEK],
      Tactical.REVERSE EQ_TAC >> METIS_TAC []
        \\ STRIP_TAC
        \\ IMP_RES_TAC IS_PTREE_PEEK
        \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
        \\ `~(n < n')` by (Cases_on `~(BIT n n0' = BIT n k')` \\ METIS_TAC [])
        \\ `~(n' < n)` by (Cases_on `~(BIT n' n0 = BIT n' k')` \\ PROVE_TAC [])
        \\ `n = n'` by DECIDE_TAC
        \\ `n0 < 2 ** n /\ n0' < 2 ** n`
        by FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
        \\ `n0 = n0'`
        by METIS_TAC [LT_MOD_2EXP_EQ, MOD_2EXP_EQ_TRANS, MOD_2EXP_EQ_SYM]
        \\ `(t1 = t2) = (!k. PEEK t1 k = PEEK t2 k)`
        by METIS_TAC [IS_PTREE_def]
        \\ `(t1' = t2') = (!k. PEEK t1' k = PEEK t2' k)`
        by METIS_TAC [IS_PTREE_def]
        \\ FULL_SIMP_TAC bool_ss [GSYM OPTION_EQ]
        \\ CONJ_TAC \\ STRIP_TAC
        << [Cases_on `BIT n' k''''` >> METIS_TAC [],
            Tactical.REVERSE (Cases_on `BIT n' k''''`) >> METIS_TAC []]
        \\ FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
        \\ METIS_TAC [PEEK_NONE_LEFT, PEEK_NONE_RIGHT]]);

val REMOVE_REMOVE = store_thm("REMOVE_REMOVE",
  `!t k. IS_PTREE t ==> (REMOVE (REMOVE t k) k = REMOVE t k)`,
  SRW_TAC [] [GSYM PTREE_EQ, PEEK_REMOVE]);

val _ = export_rewrites ["REMOVE_REMOVE"];

val REMOVE_ADD = store_thm("REMOVE_ADD",
  `!t k d j. IS_PTREE t ==>
          (REMOVE (ADD t (k,d)) j =
           if k = j then REMOVE t j else ADD (REMOVE t j) (k,d))`,
  SRW_TAC [] [GSYM PTREE_EQ, PEEK_REMOVE, PEEK_ADD]
    \\ SRW_TAC [] []);

val ADD_ADD_SYM = store_thm("ADD_ADD_SYM",
  `!t k j d e. IS_PTREE t /\ ~(k = j) ==>
               (ADD (ADD t (k,d)) (j,e) = ADD (ADD t (j,e)) (k,d))`,
  SRW_TAC [] [GSYM PTREE_EQ, PEEK_ADD] \\ SRW_TAC [] []);

(* ------------------------------------------------------------------------- *)

val FILTER_ALL = store_thm("FILTER_ALL",
  `!P l. (!n. n < LENGTH l ==> ~P (EL n l)) = (FILTER P l = [])`,
  Induct_on `l` \\ SRW_TAC [] []
    >> (EXISTS_TAC `0` \\ SRW_TAC [] [])
    \\ PAT_ASSUM `!P. x` (SPEC_THEN `P` (SUBST1_TAC o SYM))
    \\ EQ_TAC \\ SRW_TAC [] []
    >> METIS_TAC [LESS_MONO_EQ, EL, TL]
    \\ Cases_on `n` >> SRW_TAC [] []
    \\ METIS_TAC [LESS_MONO_EQ, EL, TL]);

val TRAVERSE_TRANSFORM = store_thm("TRAVERSE_TRANSFORM",
  `!f t. TRAVERSE (TRANSFORM f t) = TRAVERSE t`,
  Induct_on `t` \\ SRW_TAC [] [TRAVERSE_def, TRANSFORM_def]);

val MEM_TRAVERSE_PEEK = store_thm("MEM_TRAVERSE_PEEK",
  `!t k. IS_PTREE t ==> (MEM k (TRAVERSE t) = IS_SOME (PEEK t k))`,
  Induct \\ SRW_TAC [] [TRAVERSE_def, PEEK_def, IS_PTREE_def]
    \\ METIS_TAC [optionTheory.NOT_IS_SOME_EQ_NONE,
         PEEK_NONE_LEFT, PEEK_NONE_RIGHT]);

val IN_NUMSET_OF_PTREE = store_thm("IN_NUMSET_OF_PTREE",
  `!t n. IS_PTREE t ==> (n IN NUMSET_OF_PTREE t = n IN_PTREE t)`,
  SRW_TAC [] [NUMSET_OF_PTREE_def, IN_PTREE_def, MEM_TRAVERSE_PEEK]);

val FOLD_INDUCT = prove(
  `!P f e l. P e /\ (!x y. P x ==> P (f x y)) ==>  P (FOLDL f e l)`,
  Induct_on `l` \\ SRW_TAC [] []);

val ADD_LIST_IS_PTREE = store_thm("ADD_LIST_IS_PTREE",
  `!t l. IS_PTREE t ==> IS_PTREE (ADD_LIST t l)`,
  SRW_TAC [] [ADD_LIST_def]
    \\ MATCH_MP_TAC FOLD_INDUCT
    \\ SRW_TAC [] []
    \\ Cases_on `y`
    \\ SRW_TAC [] []);

val PTREE_OF_NUMSET_IS_PTREE = store_thm("PTREE_OF_NUMSET_IS_PTREE",
  `!t s. IS_PTREE t ==> IS_PTREE (PTREE_OF_NUMSET t s)`,
  SRW_TAC [] [PTREE_OF_NUMSET_def]
    \\ MATCH_MP_TAC FOLD_INDUCT
    \\ SRW_TAC [] [INSERT_PTREE_def]);

val PTREE_OF_NUMSET_IS_PTREE_EMPTY = save_thm("PTREE_OF_NUMSET_IS_PTREE_EMPTY",
  (SIMP_RULE (srw_ss()) [] o SPEC `Empty`) PTREE_OF_NUMSET_IS_PTREE);

val _ = export_rewrites ["ADD_LIST_IS_PTREE", "PTREE_OF_NUMSET_IS_PTREE",
                         "PTREE_OF_NUMSET_IS_PTREE_EMPTY"];

val EVERY_LEAF_PEEK_LEFT = (SIMP_RULE (srw_ss()) [] o
  SPEC `\k d. MOD_2EXP_EQ m k p /\ BIT m k`) EVERY_LEAF_PEEK;

val EVERY_LEAF_PEEK_RIGHT = (SIMP_RULE (srw_ss()) [] o
  SPEC `\k d. MOD_2EXP_EQ m k p /\ ~BIT m k`) EVERY_LEAF_PEEK;

val NOT_KEY_LEFT_AND_RIGHT = store_thm("NOT_KEY_LEFT_AND_RIGHT",
  `!p m l r k j.
      IS_PTREE (Branch p m l r) /\
      IS_SOME (PEEK l k) /\ IS_SOME (PEEK r j) ==> ~(k = j)`,
  SRW_TAC [] [IS_PTREE_def]
    \\ METIS_TAC [EVERY_LEAF_PEEK_LEFT, EVERY_LEAF_PEEK_RIGHT]);

val ALL_DISTINCT_TRAVERSE = store_thm("ALL_DISTINCT_TRAVERSE",
  `!t. IS_PTREE t ==> ALL_DISTINCT (TRAVERSE t)`,
  Induct \\ SRW_TAC [] [ALL_DISTINCT, TRAVERSE_def, ALL_DISTINCT_APPEND]
    \\ `IS_PTREE t /\ IS_PTREE t'` by FULL_SIMP_TAC (srw_ss()) [IS_PTREE_def]
    \\ METIS_TAC [MEM_TRAVERSE_PEEK, NOT_KEY_LEFT_AND_RIGHT]);

val _ = export_rewrites ["ALL_DISTINCT_TRAVERSE"];

val MEM_ALL_DISTINCT_IMP_PERM = store_thm("MEM_ALL_DISTINCT_IMP_PERM",
  `!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ (!x. MEM x l1 = MEM x l2) ==>
           PERM l1 l2`,
  SRW_TAC [] [PERM_DEF, ALL_DISTINCT_FILTER]
    \\ MATCH_MP_TAC listTheory.LIST_EQ
    \\ Cases_on `MEM x l1` >> METIS_TAC []
    \\ SPEC_THEN `$= x` ASSUME_TAC FILTER_ALL
    \\ METIS_TAC [MEM_EL]);

val MEM_TRAVERSE = store_thm("MEM_TRAVERSE",
  `!t k. IS_PTREE t ==> (MEM k (TRAVERSE t) = k IN (NUMSET_OF_PTREE t))`,
  SRW_TAC [] [IN_NUMSET_OF_PTREE, IN_PTREE_def, MEM_TRAVERSE_PEEK]);

val INSERT_PTREE_IS_PTREE = store_thm("INSERT_PTREE_IS_PTREE",
  `!t x. IS_PTREE t ==> IS_PTREE (x INSERT_PTREE t)`,
  SRW_TAC [] [INSERT_PTREE_def]);

val FINITE_NUMSET_OF_PTREE = store_thm("FINITE_NUMSET_OF_PTREE",
  `!t. FINITE (NUMSET_OF_PTREE t)`,
  SRW_TAC [] [NUMSET_OF_PTREE_def, FINITE_LIST_TO_SET]);

val ADD_INSERT = save_thm("ADD_INSERT",
  (GEN_ALL o SIMP_CONV (srw_ss()) [GSYM INSERT_PTREE_def, oneTheory.one])
  ``ADD t (n,v:unit)``);

val _ = export_rewrites ["INSERT_PTREE_IS_PTREE", "FINITE_NUMSET_OF_PTREE",
                         "ADD_INSERT"];

val IS_PTREE_FOLDR_INSERT_PTREE = prove(
  `!l t. IS_PTREE t ==> IS_PTREE (FOLDR (\x y. x INSERT_PTREE y) t l)`,
  Induct_on `l` \\ SRW_TAC [] []);

val PEEK_INSERT_PTREE = save_thm("PEEK_INSERT_PTREE",
   (GEN_ALL o SPEC_ALL o ONCE_REWRITE_RULE [oneTheory.one] o
    REWRITE_RULE [ADD_INSERT] o ISPEC `t:ptreeset`) PEEK_ADD);

val MEM_TRAVERSE_INSERT_PTREE = store_thm("MEM_TRAVERSE_INSERT_PTREE",
  `!t x h. IS_PTREE t ==>
         (MEM x (TRAVERSE (h INSERT_PTREE t)) =
          (x = h) \/ ~(x = h) /\ MEM x (TRAVERSE t))`,
  SRW_TAC [] [MEM_TRAVERSE_PEEK, PEEK_INSERT_PTREE]);

val MEM_TRAVERSE_FOLDR = prove(
  `!l t x. IS_PTREE t ==>
      (MEM x (TRAVERSE (FOLDR (\x y. x INSERT_PTREE y) (h INSERT_PTREE t) l)) =
       (x = h) \/
      ~(x = h) /\ MEM x (TRAVERSE (FOLDR (\x y. x INSERT_PTREE y) t l)))`,
   Induct
     \\ SRW_TAC [] [IS_PTREE_FOLDR_INSERT_PTREE, MEM_TRAVERSE_INSERT_PTREE]
     \\ METIS_TAC []);

val PERM_INSERT_PTREE = prove(
  `!t l. IS_PTREE t /\ ALL_DISTINCT l ==>
           (PERM (TRAVERSE (FOLDL (combin$C $INSERT_PTREE) t l))
              (SET_TO_LIST (NUMSET_OF_PTREE t UNION LIST_TO_SET l)))`,
  REWRITE_TAC [FOLDL_FOLDR_REVERSE]
    \\ Induct_on `l`
    \\ SRW_TAC [] [TRAVERSE_def, FOLDR_APPEND, NUMSET_OF_PTREE_def]
    \\ MATCH_MP_TAC MEM_ALL_DISTINCT_IMP_PERM
    \\ SRW_TAC [] [MEM_SET_TO_LIST, FINITE_LIST_TO_SET, MEM_TRAVERSE_FOLDR,
                   IS_PTREE_FOLDR_INSERT_PTREE]
    \\ RES_TAC \\ IMP_RES_TAC PERM_MEM_EQ \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST, MEM_TRAVERSE]
     \\ METIS_TAC []);

val PERM_INSERT_PTREE = save_thm("PERM_INSERT_PTREE",
  (GEN_ALL o SIMP_RULE (srw_ss()) [SET_TO_LIST_INV] o
   DISCH `FINITE s` o SPECL [`t`, `SET_TO_LIST s`]) PERM_INSERT_PTREE);

val IN_PTREE_OF_NUMSET = store_thm("IN_PTREE_OF_NUMSET",
  `!t s n. IS_PTREE t /\ FINITE s ==>
         (n IN_PTREE (PTREE_OF_NUMSET t s) = n IN_PTREE t \/ n IN s)`,
  SRW_TAC [] [IN_PTREE_def, GSYM MEM_TRAVERSE_PEEK, MEM_TRAVERSE]
    \\ REWRITE_TAC [GSYM pred_setTheory.IN_UNION]
    \\ `FINITE (NUMSET_OF_PTREE t UNION s)`
    by SRW_TAC [] [pred_setTheory.FINITE_UNION]
    \\ POP_ASSUM
         (fn th => SUBST1_TAC (SPEC `n` (MATCH_MP SET_TO_LIST_IN_MEM th)))
    \\ ASM_SIMP_TAC bool_ss [GSYM MEM_TRAVERSE, PTREE_OF_NUMSET_IS_PTREE]
    \\ MATCH_MP_TAC PERM_MEM_EQ
    \\ SRW_TAC [] [PTREE_OF_NUMSET_def, PERM_INSERT_PTREE]);

val IN_PTREE_EMPTY = save_thm("IN_PTREE_EMPTY", (GEN_ALL o EQF_ELIM o
  SIMP_CONV (srw_ss()) [IN_PTREE_def, PEEK_def]) ``n IN_PTREE <{}>``);

val _ = export_rewrites ["IN_PTREE_EMPTY"];

val IN_PTREE_OF_NUMSET_EMPTY = save_thm("IN_PTREE_OF_NUMSET_EMPTY",
  (GSYM o SIMP_RULE (srw_ss()) [] o SPEC `Empty`) IN_PTREE_OF_NUMSET);

val IS_SOME_EQ_UNIT = prove(
  `!a b:unit option. (IS_SOME a = IS_SOME b) = (a = b)`,
  Cases \\ Cases \\ SRW_TAC [] [oneTheory.one]);

val PTREE_EXTENSION = store_thm("PTREE_EXTENSION",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           ((t1 = t2) = (!x. x IN_PTREE t1 = x IN_PTREE t2))`,
  SRW_TAC [] [GSYM PTREE_EQ, GSYM IS_SOME_EQ_UNIT, GSYM IN_PTREE_def]);

val PTREE_OF_NUMSET_NUMSET_OF_PTREE = store_thm(
  "PTREE_OF_NUMSET_NUMSET_OF_PTREE",
  `!t s. IS_PTREE t /\ FINITE s ==>
         (PTREE_OF_NUMSET Empty (NUMSET_OF_PTREE t UNION s) =
          PTREE_OF_NUMSET t s)`,
  SRW_TAC [] [PTREE_EXTENSION, pred_setTheory.FINITE_UNION, IN_PTREE_OF_NUMSET]
    \\ SRW_TAC [] [IN_PTREE_EMPTY, IN_NUMSET_OF_PTREE]);

val NUMSET_OF_PTREE_PTREE_OF_NUMSET = store_thm(
  "NUMSET_OF_PTREE_PTREE_OF_NUMSET",
  `!t s. IS_PTREE t /\ FINITE s ==>
         (NUMSET_OF_PTREE (PTREE_OF_NUMSET t s) =
          NUMSET_OF_PTREE t UNION s)`,
  SRW_TAC []
    [pred_setTheory.EXTENSION, IN_NUMSET_OF_PTREE, IN_PTREE_OF_NUMSET]);

val NUMSET_OF_PTREE_EMPTY = store_thm("NUMSET_OF_PTREE_EMPTY",
  `NUMSET_OF_PTREE Empty = {}`,
  SRW_TAC [] [NUMSET_OF_PTREE_def, TRAVERSE_def, LIST_TO_SET_THM]);

val PTREE_OF_NUMSET_EMPTY = store_thm("PTREE_OF_NUMSET_EMPTY",
  `!t. PTREE_OF_NUMSET t {} = t`,
  SRW_TAC [] [PTREE_OF_NUMSET_def, SET_TO_LIST_THM]);

val _ = export_rewrites ["NUMSET_OF_PTREE_EMPTY", "PTREE_OF_NUMSET_EMPTY"];

val NUMSET_OF_PTREE_PTREE_OF_NUMSET_EMPTY = save_thm(
  "NUMSET_OF_PTREE_PTREE_OF_NUMSET_EMPTY",
  (SIMP_RULE (srw_ss()) [] o SPEC `Empty`) NUMSET_OF_PTREE_PTREE_OF_NUMSET);

val IN_PTREE_INSERT_PTREE = store_thm("IN_PTREE_INSERT_PTREE",
  `!t m n. IS_PTREE t ==>
           (n IN_PTREE (m INSERT_PTREE t) = (m = n) \/ n IN_PTREE t)`,
  SRW_TAC [] [IN_PTREE_def, PEEK_INSERT_PTREE]);

val IN_PTREE_REMOVE = store_thm("IN_PTREE_REMOVE",
  `!t m n. IS_PTREE t ==>
           (n IN_PTREE (REMOVE t m) = ~(n = m) /\ n IN_PTREE t)`,
  SRW_TAC [] [IN_PTREE_def, PEEK_REMOVE]);

val IN_PTREE_UNION_PTREE = store_thm("IN_PTREE_UNION_PTREE",
  `!t1 t2 n. IS_PTREE t1 /\ IS_PTREE t2 ==>
           (n IN_PTREE (t1 UNION_PTREE t2) = n IN_PTREE t1 \/ n IN_PTREE t2)`,
  SRW_TAC [] [UNION_PTREE_def, IN_PTREE_OF_NUMSET]
    \\ SRW_TAC [] [IN_NUMSET_OF_PTREE]);

val UNION_PTREE_IS_PTREE = store_thm("UNION_PTREE_IS_PTREE",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           IS_PTREE (t1 UNION_PTREE t2)`,
  SRW_TAC [] [UNION_PTREE_def]);

val _ = export_rewrites ["UNION_PTREE_IS_PTREE"];

val UNION_PTREE_COMM = store_thm("UNION_PTREE_COMM",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           (t1 UNION_PTREE t2 = t2 UNION_PTREE t1)`,
  SRW_TAC [] [PTREE_EXTENSION] \\ METIS_TAC [IN_PTREE_UNION_PTREE]);

val UNION_PTREE_COMM_EMPTY = save_thm("UNION_PTREE_COMM_EMPTY",
  (GEN_ALL o SIMP_RULE (srw_ss()) [] o SPECL [`Empty`,`t`]) UNION_PTREE_COMM);

val UNION_PTREE_EMPTY = store_thm("UNION_PTREE_EMPTY",
   `(!t. t UNION_PTREE Empty = t) /\
    (!t. IS_PTREE t ==> (Empty UNION_PTREE t = t))`,
  SRW_TAC [] [UNION_PTREE_COMM_EMPTY, UNION_PTREE_def]);

val UNION_PTREE_ASSOC = store_thm("UNION_PTREE_ASSOC",
  `!t1 t2 t3. IS_PTREE t1 /\ IS_PTREE t2 /\ IS_PTREE t3 ==>
             (t1 UNION_PTREE (t2 UNION_PTREE t3) =
              t1 UNION_PTREE t2 UNION_PTREE t3)`,
  SRW_TAC [] [PTREE_EXTENSION, IN_PTREE_UNION_PTREE] \\ METIS_TAC []);

val PTREE_OF_NUMSET_UNION = store_thm("PTREE_OF_NUMSET_UNION",
  `!t s1 s2. IS_PTREE t /\ FINITE s1 /\ FINITE s2 ==>
         (PTREE_OF_NUMSET t (s1 UNION s2) =
          PTREE_OF_NUMSET (PTREE_OF_NUMSET t s1) s2)`,
  SRW_TAC [] [PTREE_EXTENSION, IN_PTREE_OF_NUMSET] \\ METIS_TAC []);

val PTREE_OF_NUMSET_INSERT = store_thm("PTREE_OF_NUMSET_INSERT",
  `!t s x. IS_PTREE t /\ FINITE s ==>
         (PTREE_OF_NUMSET t (x INSERT s) =
          x INSERT_PTREE (PTREE_OF_NUMSET t s))`,
  SRW_TAC [] [PTREE_EXTENSION, IN_PTREE_OF_NUMSET, IN_PTREE_INSERT_PTREE]
    \\ METIS_TAC []);

val PTREE_OF_NUMSET_INSERT_EMPTY = save_thm("PTREE_OF_NUMSET_INSERT_EMPTY",
  (SIMP_RULE (srw_ss()) [] o SPEC `Empty`) PTREE_OF_NUMSET_INSERT);

val PTREE_OF_NUMSET_DELETE = store_thm("PTREE_OF_NUMSET_DELETE",
  `!t s x. IS_PTREE t /\ FINITE s ==>
      (PTREE_OF_NUMSET t (s DELETE x) =
       if x IN_PTREE t then
         PTREE_OF_NUMSET t s
       else
         REMOVE (PTREE_OF_NUMSET t s) x)`,
  SRW_TAC [] [PTREE_EXTENSION, IN_PTREE_OF_NUMSET, IN_PTREE_REMOVE]
    \\ METIS_TAC []);

val PTREE_OF_NUMSET_DELETE = save_thm("PTREE_OF_NUMSET_DELETE",
  (SIMP_RULE (srw_ss()) [] o SPEC `Empty`) PTREE_OF_NUMSET_DELETE);

(* ------------------------------------------------------------------------- *)

val TRAVERSE_AUX_lem = prove(
  `!t l. TRAVERSE_AUX t l = TRAVERSE_AUX t [] ++ l`,
  Induct
    >> SRW_TAC [] [TRAVERSE_AUX_def]
    >> SRW_TAC [] [TRAVERSE_AUX_def]
    \\ ONCE_REWRITE_TAC [TRAVERSE_AUX_def]
    \\ METIS_TAC [listTheory.APPEND_ASSOC]);

val TRAVERSE_AUX = store_thm("TRAVERSE_AUX",
  `!t. TRAVERSE t = TRAVERSE_AUX t []`,
  Induct \\ SRW_TAC [] [TRAVERSE_def, TRAVERSE_AUX_def]
    \\ METIS_TAC [TRAVERSE_AUX_lem]);

val PTREE_TRAVERSE_EQ = store_thm("PTREE_TRAVERSE_EQ",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           ((!k. MEM k (TRAVERSE t1) = MEM k (TRAVERSE t2)) =
            (TRAVERSE t1 = TRAVERSE t2))`,
  REPEAT STRIP_TAC
    \\ EQ_TAC \\ SRW_TAC [] []
    \\ POP_ASSUM MP_TAC
    \\ `TRAVERSE t1 = TRAVERSE (TRANSFORM (K ()) t1)`
    by METIS_TAC [TRAVERSE_TRANSFORM]
    \\ `TRAVERSE t2 = TRAVERSE (TRANSFORM (K ()) t2)`
    by METIS_TAC [TRAVERSE_TRANSFORM]
    \\ NTAC 2 (POP_ASSUM SUBST1_TAC)
    \\ SRW_TAC [] [IS_SOME_EQ_UNIT, MEM_TRAVERSE_PEEK, PTREE_EQ]);

val QSORT_EQ =
  METIS_PROVE [QSORT_PERM, PERM_TRANS, PERM_SYM, PERM_REFL]
  ``!R l1 l2. (QSORT R l1 = QSORT R l2) ==> PERM l1 l2``;

val QSORT_MEM_EQ = save_thm("QSORT_MEM_EQ",
  GEN_ALL (IMP_TRANS (SPEC_ALL QSORT_EQ) (SPEC_ALL PERM_MEM_EQ)));

val KEYS_PEEK = store_thm("KEYS_PEEK",
  `!t1 t2. IS_PTREE t1 /\ IS_PTREE t2 ==>
           ((KEYS t1 = KEYS t2) = (TRAVERSE t1 = TRAVERSE t2))`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ SRW_TAC [] [KEYS_def]
    \\ IMP_RES_TAC QSORT_MEM_EQ
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ METIS_TAC [PTREE_TRAVERSE_EQ]);

val lem1 = prove(
  `!t k. IS_PTREE t /\ ~MEM k (TRAVERSE t) ==>
          PERM (SET_TO_LIST (NUMSET_OF_PTREE (k INSERT_PTREE t)))
               (k::TRAVERSE t)`,
  REPEAT STRIP_TAC
    \\ MATCH_MP_TAC MEM_ALL_DISTINCT_IMP_PERM
    \\ SRW_TAC [] [MEM_TRAVERSE, IN_NUMSET_OF_PTREE, IN_PTREE_INSERT_PTREE]
    \\ METIS_TAC []);

val lem2 = (SIMP_RULE (srw_ss()) [PTREE_OF_NUMSET_INSERT,
      GSYM NUMSET_OF_PTREE_PTREE_OF_NUMSET] o
    SPECL [`t`, `{x}`]) PERM_INSERT_PTREE;

val PERM_ADD = store_thm("PERM_ADD",
  `!t k d. IS_PTREE t /\ ~MEM k (TRAVERSE t) ==>
           PERM (TRAVERSE (ADD t (k,d))) (k::TRAVERSE t)`,
  NTAC 3 STRIP_TAC
    \\ `TRAVERSE (ADD t (k,d)) = TRAVERSE (ADD (TRANSFORM (K ()) t) (k,()))`
    by REWRITE_TAC [TRAVERSE_TRANSFORM, (GSYM o SIMP_RULE std_ss [] o
                      ISPEC `K ()`) ADD_TRANSFORM]
    \\ POP_ASSUM SUBST1_TAC
    \\ ISPECL_THEN [`K ()`,`t`] (SUBST1_TAC o SYM) TRAVERSE_TRANSFORM
    \\ SRW_TAC [] []
    \\ METIS_TAC [lem1, lem2, PERM_SYM, PERM_TRANS, TRANSFORM_IS_PTREE]);

val TRAVERSE_ADD_MEM = prove(
  `!t k d. IS_PTREE t ==>
          (MEM j (TRAVERSE (ADD t (k,d))) =
             (j = k) \/ MEM j (TRAVERSE t))`,
  SRW_TAC [] [MEM_TRAVERSE_PEEK, PEEK_ADD]);

val PERM_NOT_ADD = store_thm("PERM_NOT_ADD",
  `!t k d. IS_PTREE t /\ MEM k (TRAVERSE t) ==>
           (TRAVERSE (ADD t (k,d)) = TRAVERSE t)`,
  SRW_TAC [] [GSYM PTREE_TRAVERSE_EQ, TRAVERSE_ADD_MEM]
    \\ METIS_TAC []);

val TRAVERSE_REMOVE_MEM = prove(
  `!t k. IS_PTREE t ==>
        (MEM j (TRAVERSE (REMOVE t k)) =
           ~(j = k) /\ MEM j (TRAVERSE t))`,
  SRW_TAC [] [MEM_TRAVERSE_PEEK, PEEK_REMOVE]);

val PERM_NOT_REMOVE = store_thm("PERM_NOT_REMOVE",
  `!t k. IS_PTREE t /\ ~MEM k (TRAVERSE t) ==>
         (TRAVERSE (REMOVE t k) = TRAVERSE t)`,
  SRW_TAC [] [GSYM PTREE_TRAVERSE_EQ, TRAVERSE_REMOVE_MEM]
    \\ METIS_TAC []);

val PERM_DELETE_PTREE = store_thm("PERM_DELETE_PTREE",
  `!t:unit ptree k.
           IS_PTREE t /\ MEM k (TRAVERSE t) ==>
           PERM (TRAVERSE (REMOVE t k))
                (FILTER (\x. ~(x = k)) (TRAVERSE t))`,
  REPEAT STRIP_TAC
    \\ MATCH_MP_TAC MEM_ALL_DISTINCT_IMP_PERM
    \\ SRW_TAC [] [MEM_FILTER, MEM_TRAVERSE_PEEK,
                   PEEK_REMOVE]
    \\ SRW_TAC [] [ALL_DISTINCT_FILTER, MEM_FILTER, FILTER_FILTER,
                   METIS_PROVE [] ``~(x = k) ==>
                     ((\x'. (x = x') /\ ~(x' = k)) = ($= x))``]
    \\ POP_ASSUM MP_TAC \\ SPEC_TAC (`x`,`x`)
    \\ ASM_SIMP_TAC (srw_ss()) [GSYM ALL_DISTINCT_FILTER]);

val FILTER_NONE = store_thm("FILTER_NONE",
  `!P l. (!n. n < LENGTH l ==> P (EL n l)) ==> (FILTER P l = l)`,
  Induct_on `l` \\ SRW_TAC [] []
    >> POP_ASSUM (fn th => ASM_SIMP_TAC std_ss
         [(GEN_ALL o SIMP_RULE (srw_ss()) [] o SPEC `SUC n`) th])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [] o SPEC `0`));

val MEM_NOT_NULL = prove(
  `!l x. MEM x l ==> 0 < LENGTH l`,
  Cases \\ SRW_TAC [] []);

val LENGTH_FILTER_ONE_ALL_DISTINCT = prove(
  `!l k. ALL_DISTINCT l /\ MEM k l ==>
        (LENGTH (FILTER (\x. ~(x = k)) l) = LENGTH l - 1)`,
  Induct \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC (srw_ss()) []
    >> METIS_TAC [DECIDE ``0 < n ==> (SUC (n - 1) = n)``, MEM_NOT_NULL]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(a = b) ==> (LENGTH a = LENGTH b)``)
    \\ MATCH_MP_TAC FILTER_NONE
    \\ METIS_TAC [MEM_EL]);

val PERM_REMOVE = store_thm("PERM_REMOVE",
  `!t k. IS_PTREE t /\ MEM k (TRAVERSE t) ==>
           PERM (TRAVERSE (REMOVE t k)) (FILTER (\x. ~(x = k)) (TRAVERSE t))`,
  NTAC 2 STRIP_TAC
    \\ `TRAVERSE (REMOVE t k) = TRAVERSE (REMOVE (TRANSFORM (K ()) t) k)`
    by REWRITE_TAC [TRAVERSE_TRANSFORM, (GSYM o SIMP_RULE (srw_ss()) [] o
                      ISPEC `K ()`) REMOVE_TRANSFORM]
    \\ POP_ASSUM SUBST1_TAC
    \\ ISPECL_THEN [`K ()`,`t`] (SUBST1_TAC o SYM) TRAVERSE_TRANSFORM
    \\ SRW_TAC [] [PERM_DELETE_PTREE]);

val SIZE_ADD = store_thm("SIZE_ADD",
  `!t k d.
      IS_PTREE t ==>
     (SIZE (ADD t (k,d)) =
      if MEM k (TRAVERSE t) then
        SIZE t
      else
        SIZE t + 1)`,
  SRW_TAC [] [SIZE_def, PERM_NOT_ADD]
    \\ METIS_TAC [PERM_ADD, PERM_LENGTH, LENGTH, ADD1]);

val SIZE_REMOVE = store_thm("SIZE_REMOVE",
  `!t k.
      IS_PTREE t ==>
     (SIZE (REMOVE t k) =
      if MEM k (TRAVERSE t) then
        SIZE t - 1
      else
        SIZE t)`,
  SRW_TAC [] [SIZE_def, PERM_NOT_REMOVE]
    \\ METIS_TAC [PERM_REMOVE, PERM_LENGTH, ALL_DISTINCT_TRAVERSE,
         LENGTH_FILTER_ONE_ALL_DISTINCT]);

(* ------------------------------------------------------------------------- *)

val SIZE = store_thm("SIZE",
  `(SIZE Empty = 0) /\
   (!k d. SIZE (Leaf k d) = 1) /\
   (!p m l r. SIZE (Branch p m l r) = SIZE l + SIZE r)`,
  SRW_TAC [] [SIZE_def, TRAVERSE_def]);
val _ = computeLib.add_persistent_funs [("SIZE", SIZE)];

val LENGTH_FOLDL_ADD = prove(
  `!l t. IS_PTREE t /\ ALL_DISTINCT (TRAVERSE t ++ l) ==>
        (SIZE (FOLDL (combin$C $INSERT_PTREE) t l) = SIZE t + LENGTH l)`,
  Induct \\ SRW_TAC [] [SIZE]
    \\ `ALL_DISTINCT (TRAVERSE (h INSERT_PTREE t) ++ l) /\ ~MEM h (TRAVERSE t)`
    by (FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND,
              MEM_TRAVERSE_INSERT_PTREE] \\ METIS_TAC [])
    \\ `SIZE (h INSERT_PTREE t) = SIZE t + 1`
    by RW_TAC std_ss [SIZE_ADD, INSERT_PTREE_def]
    \\ METIS_TAC [INSERT_PTREE_IS_PTREE, DECIDE ``a + 1 + b = a + SUC b``]);

val SIZE_PTREE_OF_NUMSET = save_thm("SIZE_PTREE_OF_NUMSET",
  (GEN_ALL o SIMP_RULE (srw_ss()) [GSYM PTREE_OF_NUMSET_def, SET_TO_LIST_CARD] o
   DISCH `FINITE s` o SPECL [`SET_TO_LIST s`,`t`]) LENGTH_FOLDL_ADD);

val SIZE_PTREE_OF_NUMSET_EMPTY = save_thm("SIZE_PTREE_OF_NUMSET_EMPTY",
  (SIMP_RULE (srw_ss()) [TRAVERSE_def, SIZE] o
   SPEC `Empty`) SIZE_PTREE_OF_NUMSET);

val CARD_LIST_TO_SET = store_thm("CARD_LIST_TO_SET",
  `!l. ALL_DISTINCT l ==> (CARD (LIST_TO_SET l) = LENGTH l)`,
  Induct \\ SRW_TAC [] [LIST_TO_SET_THM, ALL_DISTINCT]);

val CARD_NUMSET_OF_PTREE = store_thm("CARD_NUMSET_OF_PTREE",
  `!t. IS_PTREE t ==> (CARD (NUMSET_OF_PTREE t) = SIZE t)`,
  SRW_TAC [] [NUMSET_OF_PTREE_def, CARD_LIST_TO_SET, SIZE_def]);

(* ------------------------------------------------------------------------- *)

val DELETE_UNION = store_thm("DELETE_UNION",
  `!x s1 s2. (s1 UNION s2) DELETE x = (s1 DELETE x) UNION (s2 DELETE x)`,
  SRW_TAC [] [pred_setTheory.EXTENSION] \\ METIS_TAC []);

val _ = computeLib.add_persistent_funs
  [("listTheory.LIST_TO_SET_THM", LIST_TO_SET_THM),
   ("pred_setTheory.EMPTY_DELETE", pred_setTheory.EMPTY_DELETE),
   ("pred_setTheory.DELETE_INSERT", pred_setTheory.DELETE_INSERT),
   ("DELETE_UNION", DELETE_UNION),
   ("pred_setTheory.FINITE_EMPTY", pred_setTheory.FINITE_EMPTY),
   ("pred_setTheory.FINITE_INSERT", pred_setTheory.FINITE_INSERT),
   ("pred_setTheory.FINITE_UNION", pred_setTheory.FINITE_UNION),
   ("pred_setTheory.FINITE_DELETE", pred_setTheory.FINITE_DELETE),
   ("TRAVERSE_AUX", TRAVERSE_AUX),
   ("ADD_INSERT", ADD_INSERT),
   ("PTREE_OF_NUMSET_EMPTY", PTREE_OF_NUMSET_EMPTY)];

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
