structure patricia_castsLib :> patricia_castsLib =
struct

(* interactive use:
  app load ["patriciaLib", "patricia_castsSyntax"];
*)

open HolKernel Parse boolLib bossLib Q computeLib patriciaLib
     patriciaTheory patricia_castsTheory patriciaSyntax patricia_castsSyntax;

(* ------------------------------------------------------------------------- *)

val emit_mesg = !Feedback.emit_MESG;
val _ = Feedback.emit_MESG := false;

val m = apropos;

val ERR = mk_HOL_ERR "patricia_casts";

(* ------------------------------------------------------------------------- *)

fun dest_word_ptree t =
let val sz = fcpLib.index_to_num (fst (dest_word_ptree_type (type_of t)))
in
  (sz, dest_ptree (dest_some_ptree t))
end;

fun mk_word_ptree (n, t) =
  if every_leaf (fn k => fn _ =>
                   (k = Arbnum.zero) orelse
                   (Arbnum.<(Arbnum.log2 k, n))) t
  then
    mk_some_ptree(fcpLib.index_type n, mk_ptree t)
  else
    raise ERR "mk_word_ptree"
              "At least one key is larger than the required word length.";

(* ------------------------------------------------------------------------- *)

val the_ptree_compset =
  new_compset [THE_PTREE_def, THE_PTREE_SOME_PTREE, WordEmpty_def];

val THE_PTREE_CONV = CBV_CONV the_ptree_compset;

fun add_cast_ptree_compset compset =
let open listTheory pred_setTheory in
  add_thms [IMAGE_EMPTY, IMAGE_INSERT, IMAGE_UNION,
            ADD_INSERT_WORD, ADD_INSERT_STRING,
            stringTheory.ORD_CHR_COMPUTE, stringTheory.CHAR_EQ_THM, SKIP1_def,
            string_to_num_def, num_to_string_def, num_to_string_string_to_num,
            PEEKs_def, PEEKs_def, ADDs_def, ADD_LISTs_def, REMOVEs_def,
            TRAVERSEs_def, KEYSs_def, IN_PTREEs_def, INSERT_PTREEs_def,
            STRINGSET_OF_PTREE_def, PTREE_OF_STRINGSET_def,
            PEEKw_def, FINDw_def, ADDw_def, ADD_LISTw_def, REMOVEw_def,
            TRAVERSEw_def, KEYSw_def, TRANSFORMw_def, EVERY_LEAFw_def,
            EXISTS_LEAFw_def, SIZEw_def, DEPTHw_def, IN_PTREEw_def,
            INSERT_PTREEw_def, WORDSET_OF_PTREE_def, PTREE_OF_WORDSET_def]
          compset;
  add_conv (the_ptree_tm, 1, THE_PTREE_CONV) compset
end;

fun cast_ptree_compset () =
let val compset = wordsLib.words_compset()
    val _ = add_ptree_compset compset
    val _ = add_cast_ptree_compset compset
in
  compset
end;

val CAST_PTREE_CONV = CBV_CONV (cast_ptree_compset());

(* ------------------------------------------------------------------------- *)

fun Define_mk_word_ptree (s1,s2) n t =
let val _ = mk_word_ptree (n,t)
    val thm1 = Define_mk_ptree s2 t
    val tree = mk_some_ptree(fcpLib.index_type n, lhs (concl thm1))
    val thm2 = Definition.new_definition(s1^"_def", mk_eq(mk_var(s1,Term.type_of tree), tree))
    val _ = add_thms [thm2] the_compset
    val _ = add_thms [thm2] the_ptree_compset
in
  (thm2, thm1)
end;

fun iDefine_mk_word_ptree s i t = Define_mk_word_ptree s (Arbnum.fromInt i) t;

(* ------------------------------------------------------------------------- *)

val _ = Feedback.emit_MESG := emit_mesg

end
