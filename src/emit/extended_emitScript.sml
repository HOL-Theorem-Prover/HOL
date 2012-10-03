open HolKernel boolLib bossLib Parse;
open EmitML bagTheory gcdTheory llistTheory patriciaTheory patricia_castsTheory;
open state_transformerTheory basis_emitTheory;

val _ = new_theory "extended_emit";

(* == Bags ================================================================= *)

(*---------------------------------------------------------------------------*)
(* The ML representation of bags is a datatype, not a function. So we need   *)
(* to re-create the functional aspect, via BAG_VAL.                          *)
(*---------------------------------------------------------------------------*)

fun ARITH q = EQT_ELIM (numLib.ARITH_CONV (Parse.Term q));

val BAG_VAL_DEF = Q.new_definition
("BAG_VAL_DEF",`BAG_VAL b x = b(x)`);

val BAG_VAL_THM = Q.prove
(`(!x. BAG_VAL EMPTY_BAG x = 0) /\
  (!x b e. BAG_VAL (BAG_INSERT e b) x =
     if (e=x) then 1 + BAG_VAL b x else BAG_VAL b x)`,
 CONJ_TAC THENL
 [RW_TAC arith_ss [EMPTY_BAG,BAG_VAL_DEF],
  RW_TAC arith_ss [BAG_VAL_DEF] THEN METIS_TAC [BAG_VAL_DEF,BAG_INSERT]]);

val BAG_IN_EQNS = Q.prove
(`(!x. BAG_IN x {||} = F) /\
  !x y. BAG_IN x (BAG_INSERT y b) = (x = y) \/ BAG_IN x b`,
METIS_TAC [NOT_IN_EMPTY_BAG,BAG_IN_BAG_INSERT]);

val BAG_INN_EQN = Q.prove
(`BAG_INN e n b = BAG_VAL b e >= n`,
 RW_TAC arith_ss [BAG_VAL_DEF, BAG_INN]);

val BAG_DIFF_EQNS = Q.store_thm
("BAG_DIFF_EQNS",
 `(!b:'a bag. BAG_DIFF b {||} = b) /\
  (!b:'a bag. BAG_DIFF {||} b = {||}) /\
  (!(x:'a) b (y:'a). BAG_DIFF (BAG_INSERT x b) {|y|} =
            if x = y then b else BAG_INSERT x (BAG_DIFF b {|y|})) /\
  (!(b1:'a bag) y (b2:'a bag).
      BAG_DIFF b1 (BAG_INSERT y b2) = BAG_DIFF (BAG_DIFF b1 {|y|}) b2)`,
 RW_TAC arith_ss [BAG_DIFF,FUN_EQ_THM,BAG_INSERT,EMPTY_BAG] THEN
 RW_TAC arith_ss []);

val BAG_INTER_EQNS = Q.store_thm
("BAG_INTER_EQNS",
 `(!b:'a bag. BAG_INTER {||} b = {||}) /\
  (!b: 'a bag. BAG_INTER b {||} = {||}) /\
  (!(x:'a) b1 (b2:'a bag).
     BAG_INTER (BAG_INSERT x b1) b2 =
        if BAG_IN x b2
           then BAG_INSERT x (BAG_INTER b1 (BAG_DIFF b2 {|x|}))
           else BAG_INTER b1 b2)`,
 RW_TAC arith_ss [BAG_INTER, EMPTY_BAG,FUN_EQ_THM,BAG_INSERT,BAG_DIFF]
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss []
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss [BAG_IN, BAG_INN]
 THEN REPEAT (POP_ASSUM MP_TAC)
 THEN RW_TAC arith_ss []);

val BAG_MERGE_EQNS = Q.store_thm
("BAG_MERGE_EQNS",
 `(!b:'a bag. BAG_MERGE {||} b = b) /\
  (!b:'a bag. BAG_MERGE b {||} = b) /\
  (!x:'a. !b1 b2:'a bag.
         BAG_MERGE (BAG_INSERT x b1) b2 =
             BAG_INSERT x (BAG_MERGE b1 (BAG_DIFF b2 {|x|})))`,
 RW_TAC arith_ss [BAG_MERGE, EMPTY_BAG,FUN_EQ_THM,BAG_INSERT,BAG_DIFF]
 THEN RW_TAC arith_ss []
 THEN FULL_SIMP_TAC arith_ss []);

val SUB_BAG_EQNS = Q.store_thm
("SUB_BAG_EQNS",
 `(!b:'a bag. SUB_BAG {||} b = T) /\
  (!x:'a. !b1 b2:'a bag.
      SUB_BAG (BAG_INSERT x b1) b2 =
             BAG_IN x b2 /\ SUB_BAG b1 (BAG_DIFF b2 {|x|}))`,
 RW_TAC arith_ss [SUB_BAG_EMPTY,SUB_BAG, BAG_INSERT, BAG_INN,
          BAG_IN, BAG_DIFF,EMPTY_BAG, ARITH`!m. 0 >= m = (m=0n)`]
  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RW_TAC arith_ss []
  THEN RW_TAC arith_ss []
  THEN POP_ASSUM MP_TAC THEN RW_TAC arith_ss [] THENL
  [FULL_SIMP_TAC bool_ss [ARITH `a+1n >= n = a >=n \/ (n=a+1)`]
   THENL [RES_TAC THEN FULL_SIMP_TAC arith_ss [],
         `b1(x) >= n-1` by DECIDE_TAC THEN
         RES_THEN MP_TAC THEN REWRITE_TAC [] THEN DECIDE_TAC],
  RES_THEN MP_TAC THEN ASM_REWRITE_TAC [] THEN DECIDE_TAC]);

val PSUB_BAG_LEM = Q.prove
(`!b1 b2.PSUB_BAG b1 b2 = SUB_BAG b1 b2 /\ ~SUB_BAG b2 b1`,
 METIS_TAC [SUB_BAG_PSUB_BAG,PSUB_BAG_ANTISYM]);

val SET_OF_BAG_EQNS = Q.prove
(`(SET_OF_BAG ({||}:'a bag) = ({}:'a set)) /\
  (!(x:'a) b. SET_OF_BAG (BAG_INSERT x b) = x INSERT (SET_OF_BAG b))`,
 REWRITE_TAC [SET_OF_BAG_INSERT] THEN
 RW_TAC arith_ss [SET_OF_BAG,EMPTY_BAG,FUN_EQ_THM,NOT_IN_EMPTY_BAG,
                pred_setTheory.EMPTY_DEF]);

val BAG_OF_SET_EQNS = Q.prove
(`(BAG_OF_SET ({}:'a set) = ({||}:'a bag)) /\
  (!(x:'a) (s:'a set).
      BAG_OF_SET (x INSERT s) = if x IN s then BAG_OF_SET s
                                 else BAG_INSERT x (BAG_OF_SET s))`,
 RW_TAC bool_ss [SET_OF_EMPTY] THEN
 RW_TAC arith_ss [BAG_OF_SET,FUN_EQ_THM,BAG_INSERT] THEN
 METIS_TAC [pred_setTheory.IN_INSERT]);

val defs =
  map DEFN_NOSIG
    [BAG_VAL_THM, BAG_IN_EQNS, BAG_INN_EQN,
     INST_TYPE [beta |-> alpha]
       (CONJ (CONJUNCT1 (CONJUNCT2 BAG_UNION_EMPTY))
             (CONJUNCT1 (SPEC_ALL (Q.SPEC `x` BAG_UNION_INSERT)))),
     BAG_DIFF_EQNS, BAG_INTER_EQNS, BAG_MERGE_EQNS,
     SUB_BAG_EQNS, PSUB_BAG_LEM,
     CONJ BAG_FILTER_EMPTY (BAG_FILTER_BAG_INSERT),
     CONJ (INST_TYPE [alpha |-> beta, beta |-> alpha] BAG_IMAGE_EMPTY)
          (UNDISCH (SPEC_ALL BAG_IMAGE_FINITE_INSERT)),
     CONJ BAG_CARD_EMPTY (UNDISCH (SPEC_ALL (CONJUNCT2 BAG_CARD_THM))),
     SET_OF_BAG_EQNS, (*BAG_OF_SET_EQNS,*)
     BAG_DISJOINT]

val (tyg,tmg) = (type_grammar(),term_grammar())
val tyg' = type_grammar.remove_abbreviation tyg "bag"
val _ = temp_set_grammars(tyg',tmg)
val _ = new_type("bag",1)

val _ = eSML "bag"
  (ABSDATATYPE (["'a"], `bag = EMPTY_BAG | BAG_INSERT of 'a => bag`)
   :: OPEN ["num", "set"]
   :: MLSIG "type num = numML.num"
   :: MLSIG "type 'a set = 'a setML.set"
   :: MLSIG "val EMPTY_BAG    : 'a bag"
   :: MLSIG "val BAG_INSERT   : 'a * 'a bag -> 'a bag"
   :: MLSIG "val BAG_VAL      : ''a bag -> ''a -> num"
   :: MLSIG "val BAG_IN       : ''a -> ''a bag -> bool"
   :: MLSIG "val BAG_INN      : ''a -> num -> ''a bag -> bool"
   :: MLSIG "val BAG_UNION    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_DIFF     : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_INTER    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val BAG_MERGE    : ''a bag -> ''a bag -> ''a bag"
   :: MLSIG "val SUB_BAG      : ''a bag -> ''a bag -> bool"
   :: MLSIG "val PSUB_BAG     : ''a bag -> ''a bag -> bool"
   :: MLSIG "val BAG_DISJOINT : ''a bag -> ''a bag -> bool"
   :: MLSIG "val BAG_FILTER   : ('a -> bool) -> 'a bag -> 'a bag"
   :: MLSIG "val BAG_IMAGE    : ('a -> 'b) -> 'a bag -> 'b bag"
   :: MLSIG "val BAG_CARD     : 'a bag -> num"
   :: MLSIG "val SET_OF_BAG   : 'a bag -> 'a set"
(* :: MLSIG "val BAG_OF_SET   : ''a set -> ''a bag" *)
   :: defs)

(*
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set", "",
       "type 'a bag = EMPTY_BAG | BAG_INSERT of 'a * 'a bag"]
*)

val _ = eCAML "bag"
  (MLSIGSTRUCT ["type num = NumML.num", "type 'a set = 'a SetML.set"] @
   ABSDATATYPE (["'a"], `bag = EMPTY_BAG | BAG_INSERT of 'a => bag`) ::
   OPEN ["num", "set"] ::
   map MLSIG
      ["val _BAG_VAL      : 'a bag -> 'a -> num",
       "val _BAG_IN       : 'a -> 'a bag -> bool",
       "val _BAG_INN      : 'a -> num -> 'a bag -> bool",
       "val _BAG_UNION    : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_DIFF     : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_INTER    : 'a bag -> 'a bag -> 'a bag",
       "val _BAG_MERGE    : 'a bag -> 'a bag -> 'a bag",
       "val _SUB_BAG      : 'a bag -> 'a bag -> bool",
       "val _PSUB_BAG     : 'a bag -> 'a bag -> bool",
       "val _BAG_DISJOINT : 'a bag -> 'a bag -> bool",
       "val _BAG_FILTER   : ('a -> bool) -> 'a bag -> 'a bag",
       "val _BAG_IMAGE    : ('a -> 'b) -> 'a bag -> 'b bag",
       "val _BAG_CARD     : 'a bag -> num",
       "val _SET_OF_BAG   : 'a bag -> 'a set",
       "val bag_of_list  : 'a list -> 'a bag",
       "val list_of_bag  : 'a bag -> 'a list"] @
   map MLSTRUCT
      ["let bag_of_list l = ListML._FOLDL (function s -> function a ->\n\
       \    BAG_INSERT(a,s)) EMPTY_BAG l", "",
       "let rec list_of_bag b = match b with EMPTY_BAG -> []\n\
       \  | BAG_INSERT(a,s) -> a::list_of_bag s", ""] @
   defs)

(* == GCD ================================================================== *)

val defs = map DEFN [dividesTheory.compute_divides, GCD_EFFICIENTLY, lcm_def];

val _ = eSML "gcd"
  (MLSIG "type num = numML.num" ::
   OPEN ["num"] ::
   defs);

val _ = eCAML "gcd"
  (MLSIGSTRUCT ["type num = NumML.num"] @
   OPEN ["num"] ::
   defs);

(* == Lazy lists =========================================================== *)

val llcases_exists0 = prove(
  ``!l. ?v. (l = [||]) /\ (v = n) \/
            ?h t. (l = h:::t) /\ (v = c (h, t))``,
  GEN_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][EXISTS_OR_THM])
val llcases_exists =
    llcases_exists0 |> GEN_ALL |> SIMP_RULE bool_ss [SKOLEM_THM]
val llcases_def = new_specification("llcases_def", ["llcases"],
                                    llcases_exists)

val llcases_LNIL = llcases_def |> SPEC_ALL |> Q.INST [`l` |-> `LNIL`]
                               |> SIMP_RULE (srw_ss()) []
val llcases_LCONS = llcases_def |> SPEC_ALL |> Q.INST [`l` |-> `h:::t`]
                               |> SIMP_RULE (srw_ss()) []

val LLCONS_def = Define`
  LLCONS h t = LCONS h (t ())`;

val LAPPEND_llcases = prove(
  ``LAPPEND l1 l2 = llcases l2 (\(h,t). LLCONS h (\(). LAPPEND t l2)) l1``,
  Q.SPEC_THEN `l1` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LMAP_llcases = prove(
  ``LMAP f l = llcases LNIL (\(h,t). LLCONS (f h) (\(). LMAP f t)) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LFILTER_llcases = prove(
  ``LFILTER P l = llcases LNIL (\(h,t). if P h then LLCONS h (\(). LFILTER P t)
                                        else LFILTER P t) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LHD_llcases = prove(
  ``LHD ll = llcases NONE (\(h,t). SOME h) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LTL_llcases = prove(
  ``LTL ll = llcases NONE (\(h,t). SOME t) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LTAKE_thm = prove(
  ``!ll. LTAKE n ll =
                if n = 0 then SOME []
                else case LHD ll of
                       NONE => NONE
                     | SOME h => OPTION_MAP (\t. h::t)
                                            (LTAKE (n - 1) (THE (LTL ll)))``,
  Induct_on `n` THEN SRW_TAC [boolSimps.ETA_ss][LTAKE] THEN
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][] THEN Cases_on `LHD t` THEN SRW_TAC [][] THEN
  Cases_on `OPTION_MAP (CONS x) (LTAKE (n - 1) (THE (LTL t)))` THEN
  SRW_TAC [][]);

val toList_llcases = prove(
  ``toList ll = llcases (SOME []) (\(h,t). OPTION_MAP (\t. h::t) (toList t)) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [boolSimps.ETA_ss][llcases_LCONS, llcases_LNIL, toList_THM])

fun insert_const c = let val t = Parse.Term [QUOTE c] in
  ConstMapML.prim_insert(t, (false, "", c, type_of t))
end
val _ = insert_const "llcases"
val _ = insert_const "LLCONS"
val _ = insert_const "LCONS"
val _ = insert_const "LNIL"
val _ = insert_const "LUNFOLD"
val _ = adjoin_to_theory
{sig_ps = NONE, struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in S "fun insert_const c = let val t = Parse.Term [QUOTE c] in"; NL();
     S "  ConstMapML.prim_insert(t, (false, \"\", c, type_of t))"; NL();
     S "end"; NL();
     S "val _ = insert_const \"llcases\""; NL();
     S "val _ = insert_const \"LLCONS\""; NL();
     S "val _ = insert_const \"LCONS\""; NL();
     S "val _ = insert_const \"LNIL\""; NL();
     S "val _ = insert_const \"LUNFOLD\""
  end)}

val _ = eSML "llist"
        (MLSIG "type 'a llist" ::
         MLSIG "val LNIL : 'a llist" ::
         MLSIG "val LLCONS : 'a -> (unit -> 'a llist) -> 'a llist" ::
         MLSIG "val LCONS : 'a -> 'a llist -> 'a llist" ::
         MLSIG "val ::: : 'a * 'a llist -> 'a llist" ::
         MLSIG "val llcases : 'b -> ('a * 'a llist -> 'b) -> 'a llist -> 'b" ::
         MLSIG "val LUNFOLD : ('a -> ('a * 'b) option) -> 'a -> 'b llist" ::
         MLSIG "type num = numML.num" ::
         OPEN ["num", "list"] ::
         MLSTRUCT "type 'a llist = 'a seq.seq" ::
         MLSTRUCT "fun llcases n c seq = seq.fcases seq (n,c)" ::
         MLSTRUCT "fun LLCONS h t = seq.cons h (seq.delay t)"::
         MLSTRUCT "fun LCONS h t = seq.cons h t"::
         MLSTRUCT "val LNIL = seq.empty"::
         MLSTRUCT "fun :::(h,t) = LCONS h t"::
         MLSTRUCT "fun LUNFOLD f x = seq.delay (fn () => case f x of NONE => LNIL | SOME (y,e) => LCONS e (LUNFOLD f y))" ::
         map DEFN [
           LAPPEND_llcases, LMAP_llcases, LFILTER_llcases,
           LHD_llcases, LTL_llcases, LTAKE_thm,
           toList_llcases])

(* == Patricia tress ======================================================= *)

val _ = set_trace "Unicode" 0
fun Datatype x = DATATYPE [QUOTE (EmitTeX.datatype_thm_to_string x)]

val fun_rule = REWRITE_RULE [FUN_EQ_THM]

val _ = ConstMapML.insert ``SKIP1``;
val _ = ConstMapML.insert ``string_to_num``;

val _ = temp_remove_rules_for_term "Empty"
val _ = temp_disable_tyabbrev_printing "ptreeset"
val _ = temp_disable_tyabbrev_printing "word_ptreeset"

val defs =
   [BRANCHING_BIT_def, PEEK_def, JOIN_def, ADD_def, BRANCH_def,
    REMOVE_def, TRAVERSE_def, KEYS_def, TRANSFORM_def, EVERY_LEAF_def,
    EXISTS_LEAF_def, SIZE_def, DEPTH_def, IS_PTREE_def, IN_PTREE_def,
    INSERT_PTREE_def, patriciaTheory.IS_EMPTY_def, FIND_def,
    fun_rule ADD_LIST_def];

val _ = eSML "patricia"
   (OPEN ["num", "option", "set"]
    :: MLSIG "type num = numML.num"
    :: Datatype datatype_ptree
    :: MLSIG "val toList : 'a ptree -> (num * 'a) list"
    :: MLSTRUCT "fun toList Empty = []\n\
              \    | toList (Leaf(j,d)) = [(j,d)]\n\
              \    | toList (Branch(p,m,l,r)) =\n\
              \        listML.APPEND (toList l) (toList r)"
    :: map DEFN defs);

val _ = eCAML "patricia"
   (MLSIGSTRUCT ["type num = NumML.num"]
     @ Datatype datatype_ptree
    :: MLSIG "val toList : 'a ptree -> (num * 'a) list"
    :: MLSTRUCT "let rec toList t = match t with\n\
              \      Empty -> []\n\
              \    | Leaf(j,d) -> [(j,d)]\n\
              \    | Branch(p,m,l,r) ->\n\
              \        ListML._APPEND (toList l) (toList r)"
    :: map DEFN defs);

val _ = eSML "patricia_casts"
   (OPEN ["num", "option", "set", "bit", "words", "patricia"]
    :: MLSIG "type 'a ptree = 'a patriciaML.ptree"
    :: MLSIG "type 'a word = 'a wordsML.word"
    :: MLSIG "type num = numML.num"
    :: MLSIG "type string = stringML.string"
    :: MLSIG "val SKIP1 : string -> string"
    :: MLSIG "val string_to_num : string -> num"
    :: MLSTRUCT "type string = stringML.string"
    :: MLSTRUCT "fun SKIP1 s = String.extract(s,1,NONE)"
    :: MLSTRUCT "fun string_to_num s = s2n (numML.fromInt 256) stringML.ORD\n\
        \                            (String.^(String.str (Char.chr 1), s))"
    :: Datatype datatype_word_ptree
    :: map DEFN
         [THE_PTREE_def, SOME_PTREE_def,
          PEEKw_def, ADDw_def, REMOVEw_def, TRANSFORMw_def, SIZEw_def,
          DEPTHw_def, IN_PTREEw_def, INSERT_PTREEw_def, FINDw_def,
          fun_rule ADD_LISTw_def, num_to_string_def, PEEKs_def, FINDs_def,
          ADDs_def, fun_rule ADD_LISTs_def, REMOVEs_def, TRAVERSEs_def,
          KEYSs_def, IN_PTREEs_def, INSERT_PTREEs_def]);

fun adjoin_to_theory_struct l = adjoin_to_theory {sig_ps = NONE,
  struct_ps = SOME (fn ppstrm =>
    app (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) l)};

val _ = adjoin_to_theory_struct
  ["val _ = ConstMapML.insert (\
   \Term.prim_mk_const{Name=\"SKIP1\",Thy=\"patricia_casts\"});",
   "val _ = ConstMapML.insert (\
   \Term.prim_mk_const{Name=\"string_to_num\",Thy=\"patricia_casts\"});"];

(* == State transformer ==================================================== *)

val defs = map DEFN [UNIT_DEF, BIND_DEF, IGNORE_BIND_DEF, MMAP_DEF, JOIN_DEF, READ_def, WRITE_def]

val _ = eSML "state_transformer" defs
val _ = eCAML "state_transformer" defs;

val _ = export_theory ();
