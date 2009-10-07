open HolKernel boolLib bossLib Parse;
open emitLib patriciaTheory patricia_castsTheory;
open words_emitTheory string_emitTheory sorting_emitTheory;

val _ = new_theory "patricia_emit";

val _ = set_trace "Unicode" 0
fun Datatype x = DATATYPE [QUOTE (EmitTeX.datatype_thm_to_string x)]

val fun_rule = REWRITE_RULE [FUN_EQ_THM]

val _ = ConstMapML.insert ``SKIP1``;
val _ = ConstMapML.insert ``string_to_num``;

val _ = temp_remove_rules_for_term "Empty"
val _ = temp_disable_tyabbrev_printing "ptreeset"
val _ = temp_disable_tyabbrev_printing "word_ptreeset"

val _ = eSML "patricia"
   (OPEN ["num", "option", "set"]
    :: MLSIG "type num = numML.num"
    :: Datatype datatype_ptree
    :: MLSIG "val toList : 'a ptree -> (num * 'a) list"
    :: MLSTRUCT "fun toList Empty = []\n\
              \    | toList (Leaf(j,d)) = [(j,d)]\n\
              \    | toList (Branch(p,m,l,r)) =\n\
              \        listML.APPEND (toList l) (toList r)"
    :: map DEFN
         [BRANCHING_BIT_def, PEEK_def, JOIN_def, ADD_def, BRANCH_def,
          REMOVE_def, TRAVERSE_def, KEYS_def, TRANSFORM_def, EVERY_LEAF_def,
          EXISTS_LEAF_def, SIZE_def, DEPTH_def, IS_PTREE_def, IN_PTREE_def,
          INSERT_PTREE_def, IS_EMPTY_def, FIND_def, fun_rule ADD_LIST_def]);

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

val _ = export_theory ();
