open HolKernel Parse boolLib bossLib cvTheory;
open integerTheory wordsTheory sptreeTheory cv_typesTheory cv_typesLib;

val _ = new_theory "cv_types_demo";

val _ = set_grammar_ancestry ["cv_types"];

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(* tests *)

Datatype:
  a = A1 (num list) (((a # b) list) list)
    | A2 ((a + b) list) ;
  b = B1
    | B2
    | B3 (c option) ;
  c = C1
    | C2 a 'aa 'bb
End

val ty = “:('d, 'c) b”
val res = define_from_to ty

Datatype:
  tree = Leaf
       | Branch ((tree list + bool) option list)
End

val res = define_from_to “:tree”

Datatype:
  t1 = T1 num (t1 list)
End

val res = define_from_to “:t1”

Datatype:
  word_tree =
    | Fork word_tree word_tree
    | Word1 ('a word)
    | Other 'b
    | Word2 ('c word)
End

val ty = “:('a,'b,'c) word_tree”
val res = define_from_to ty
val _ = (type_of “from_word_tree f0 t” = “:cv”) orelse fail()

val res = define_from_to “:'a sptree$spt”

Datatype:
  op = Add | Sub
End

Datatype:
  exp = Var string | Const int | Op op (exp list)
End

Datatype:
  prog = Skip | Seq prog prog | Assign string exp
End

val thms = rec_define_from_to “:prog”;

val _ = export_theory();
