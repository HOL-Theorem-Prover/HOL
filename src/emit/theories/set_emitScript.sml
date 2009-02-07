open HolKernel boolLib bossLib Parse;
open EmitML pred_setTheory;
open num_emitTheory;

val _ = new_theory "set_emit";

(*---------------------------------------------------------------------------*)
(* Export an ML model of (finite) sets. Although the representation used in  *)
(* pred_set is 'a -> bool, the ML representation is a concrete type with     *)
(* constructors EMPTY and INSERT. Which is quite different, but we wanted to *)
(* be able to compute cardinality, which would not be possible with sets-as- *)
(* predicates. An alternative would be to have a parallel theory of finite   *)
(* sets, as in hol88, but that could lead to a proliferation of theories     *)
(* which required sets.                                                      *)
(*                                                                           *)
(* The implementation is not efficient. Insertion is constant time, but      *)
(* membership checks are linear and subset checks are quadratic.             *)
(*---------------------------------------------------------------------------*)

fun TAKE2 l = case List.take(l, 2) of [a,b] => (a,b)
  | _ => raise (mk_HOL_ERR "emitCAML" "TAKE2" "Not three elements");

val TAKE2_CONJUNCTS = TAKE2 o CONJUNCTS;

val F_INTRO = PURE_REWRITE_RULE [PROVE[] (Term `~x = (x = F)`)];
val T_INTRO = PURE_ONCE_REWRITE_RULE [PROVE[] (Term `x = (x = T)`)];

val BIGINTER_EMPTY = Q.prove
(`BIGINTER EMPTY = FAIL BIGINTER ^(mk_var("empty set",bool)) EMPTY`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val MAX_SET_EMPTY = Q.prove
(`MAX_SET EMPTY = FAIL MAX_SET ^(mk_var("empty set",bool)) EMPTY`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val MIN_SET_EMPTY = Q.prove
(`MIN_SET EMPTY = FAIL MIN_SET ^(mk_var("empty set",bool)) EMPTY`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val (tyg,tmg) = (type_grammar(),term_grammar())
val tyg' = type_grammar.remove_abbreviation tyg "set"
val _ = temp_set_grammars(tyg',tmg)
val _ = new_type("set",1)

val defs =
  map DEFN_NOSIG [CONJ (F_INTRO NOT_IN_EMPTY) IN_INSERT,
       CONJ (CONJUNCT1 UNION_EMPTY) INSERT_UNION,
       CONJ (CONJUNCT1 INTER_EMPTY) INSERT_INTER,
       CONJ EMPTY_DELETE DELETE_INSERT, CONJ DIFF_EMPTY DIFF_INSERT,
       CONJ (T_INTRO (SPEC_ALL EMPTY_SUBSET)) INSERT_SUBSET, PSUBSET_EQN,
       CONJ IMAGE_EMPTY IMAGE_INSERT, CONJ BIGUNION_EMPTY BIGUNION_INSERT,
       LIST_CONJ [BIGINTER_EMPTY,BIGINTER_SING, BIGINTER_INSERT],
       CONJ CARD_EMPTY (UNDISCH (SPEC_ALL CARD_INSERT)),
       CONJ (T_INTRO (CONJUNCT1 (SPEC_ALL DISJOINT_EMPTY))) DISJOINT_INSERT,
       CROSS_EQNS,
       let val (c1,c2) = TAKE2_CONJUNCTS (SPEC_ALL SUM_IMAGE_THM)
       in CONJ c1 (UNDISCH (SPEC_ALL c2)) end,
       let val (c1,c2) = TAKE2_CONJUNCTS SUM_SET_THM
       in CONJ c1 (UNDISCH (SPEC_ALL c2)) end,
       let val (c1,c2) = TAKE2_CONJUNCTS MAX_SET_THM
       in CONJ MAX_SET_EMPTY (CONJ c1 (UNDISCH (SPEC_ALL c2))) end,
       CONJ MIN_SET_EMPTY MIN_SET_THM, count_EQN,POW_EQNS];

val _ = eSML "set"
   (ABSDATATYPE (["'a"], `set = EMPTY | INSERT of 'a => set`)
    :: OPEN ["num"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "val EMPTY    : 'a set"
    :: MLSIG "val INSERT   : 'a * 'a set -> 'a set"
    :: MLSIG "val IN       : ''a -> ''a set -> bool"
    :: MLSIG "val UNION    : ''a set -> ''a set -> ''a set"
    :: MLSIG "val INTER    : ''a set -> ''a set -> ''a set"
    :: MLSIG "val DELETE   : ''a set -> ''a -> ''a set"
    :: MLSIG "val DIFF     : ''a set -> ''a set -> ''a set"
    :: MLSIG "val SUBSET   : ''a set -> ''a set -> bool"
    :: MLSIG "val PSUBSET  : ''a set -> ''a set -> bool"
    :: MLSIG "val IMAGE    : ('a -> 'b) -> 'a set -> 'b set"
    :: MLSIG "val BIGUNION : ''a set set -> ''a set"
    :: MLSIG "val BIGINTER : ''a set set -> ''a set"
    :: MLSIG "val CARD     : ''a set -> num"
    :: MLSIG "val DISJOINT : ''a set -> ''a set -> bool"
    :: MLSIG "val CROSS    : ''a set -> ''b set -> (''a * ''b) set"
    :: MLSIG "val SUM_IMAGE : (''a -> num) -> ''a set -> num"
    :: MLSIG "val SUM_SET  : num set -> num"
    :: MLSIG "val MAX_SET  : num set -> num"
    :: MLSIG "val MIN_SET  : num set -> num"
    :: MLSIG "val count    : num -> num set"
    :: MLSIG "val POW      : ''a set -> ''a set set"
    :: defs
    @ [MLSIG "val fromList : 'a list -> 'a set",
      MLSIG "val toList   : 'a set -> 'a list",
      MLSTRUCT "fun fromList alist =\
               \ listML.FOLDL (fn s => fn a => INSERT(a,s)) EMPTY alist",
      MLSTRUCT "fun toList EMPTY = []\n\
               \    | toList (INSERT(a,s)) = a::toList s"])

val _ = eCAML "set"
  (MLSIGSTRUCT
     ["type num = NumML.num", "",
      "type 'a set = EMPTY | INSERT of 'a * 'a set"] @
   map MLSIG
     ["val _IN        : 'a -> 'a set -> bool",
      "val _UNION     : 'a set -> 'a set -> 'a set",
      "val _INTER     : 'a set -> 'a set -> 'a set",
      "val _DELETE    : 'a set -> 'a -> 'a set",
      "val _DIFF      : 'a set -> 'a set -> 'a set",
      "val _SUBSET    : 'a set -> 'a set -> bool",
      "val _PSUBSET   : 'a set -> 'a set -> bool",
      "val _IMAGE     : ('a -> 'b) -> 'a set -> 'b set",
      "val _BIGUNION  : 'a set set -> 'a set",
      "val _BIGINTER  : 'a set set -> 'a set",
      "val _CARD      : 'a set -> num",
      "val _DISJOINT  : 'a set -> 'a set -> bool",
      "val _CROSS     : 'a set -> 'b set -> ('a * 'b) set",
      "val _SUM_IMAGE : ('a -> num) -> 'a set -> num",
      "val _SUM_SET   : num set -> num",
      "val _MAX_SET   : num set -> num",
      "val _MIN_SET   : num set -> num",
      "val count      : num -> num set",
      "val _POW       : 'a set -> 'a set set"] @
   defs)

val _ = export_theory ();
