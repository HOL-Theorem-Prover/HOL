open HolKernel Parse boolLib bossLib cvTheory;
open integerTheory wordsTheory sptreeTheory cv_typesTheory cv_typesLib;

val _ = Datatype ‘
  a = A1 (num list) (((a # b) list) list)
    | A2 ((a + b) list) ;
  b = B1
    | B2
    | B3 (c option) ;
  c = C1
    | C2 a 'aa 'bb
’

val ty = “:('d, 'c) b”
val res = define_from_to ty

val _ = Datatype ‘
  tree = Leaf
       | Branch ((tree list + bool) option list)
’

val res = define_from_to “:tree”

val _ = Datatype ‘
  t1 = T1 num (t1 list)
’

val res = define_from_to “:t1”

val _ = Datatype ‘
  word_tree =
    | Fork word_tree word_tree
    | Word1 ('a word)
    | Other 'b
    | Word2 ('c word)
’

val ty = “:('a,'b,'c) word_tree”
val res = define_from_to ty
val _ = (type_of “from_word_tree f0 t” = “:cv”) orelse fail()

val res = define_from_to “:'a sptree$spt”

val _ = Datatype‘
  op = Add | Sub
’

val _ = Datatype ‘
  exp = Var string | Const int | Op op (exp list)
’

val _ = Datatype ‘
  prog = Skip | Seq prog prog | Assign string exp
’

val thms = rec_define_from_to “:prog”;
