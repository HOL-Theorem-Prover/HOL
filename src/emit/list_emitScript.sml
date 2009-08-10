open HolKernel boolLib bossLib Parse;
open EmitML listTheory;
open num_emitTheory;

val _ = new_theory "list_emit";

val LENGTH_THM = REWRITE_RULE [arithmeticTheory.ADD1] LENGTH;

val HD_NIL = Q.prove(`HD [] = FAIL HD ^(mk_var("Empty list",bool)) []`,
                     REWRITE_TAC [combinTheory.FAIL_THM]);

val TL_NIL = Q.prove(`TL [] = FAIL TL ^(mk_var("Empty list",bool)) []`,
                     REWRITE_TAC [combinTheory.FAIL_THM]);

val MAP2_FAIL = Q.prove
(`(!f h t.
   (MAP2 (f:'a->'b->'c) [] (h::t) =
    FAIL MAP2 ^(mk_var("unequal length lists",bool)) f [] (h::t))) /\
  !f h t.
    (MAP2 (f:'a->'b->'c) (h::t) [] =
     FAIL MAP2 ^(mk_var("unequal length lists",bool)) f (h::t) [])`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val MAP2_THM = let val [a,b] = CONJUNCTS MAP2
                   val [c,d] = CONJUNCTS MAP2_FAIL
               in LIST_CONJ [a,c,d,b]
               end;

val ZIP_FAIL = Q.prove
(`(!(h:'b) t. ZIP ([]:'a list,h::t) =
         FAIL ZIP ^(mk_var("unequal length lists",bool)) ([],h::t)) /\
  (!(h:'a) t. ZIP (h::t,[]:'b list) =
              FAIL ZIP ^(mk_var("unequal length lists",bool)) (h::t,[]))`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val ZIP_THM = let val [a,b] = CONJUNCTS ZIP
                  val [c,d] = CONJUNCTS ZIP_FAIL
               in LIST_CONJ [a,c,d,b]
               end;

val LAST_NIL = Q.prove
(`LAST [] = FAIL LAST ^(mk_var("empty list",bool))  []`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val FRONT_NIL = Q.prove
(`FRONT [] = FAIL FRONT ^(mk_var("empty list",bool))  []`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val defs =
  map DEFN [NULL_DEF, CONJ HD_NIL HD, CONJ TL_NIL TL, APPEND, FLAT, MAP,
            MEM, FILTER, FOLDR, FOLDL, EVERY_DEF,
            EXISTS_DEF, MAP2_THM, ZIP_THM, UNZIP_THM, REVERSE_DEF,
            CONJ LAST_NIL LAST_CONS, CONJ FRONT_NIL FRONT_CONS,
            ALL_DISTINCT, EL_compute, LENGTH_THM, LEN_DEF, REV_DEF,
            list_size_def]

val _ = eSML "list"
  (MLSIG "type num = numML.num" ::
   OPEN ["num"] ::
   defs)

val _ = eCAML "list"
  (MLSIG "type num = NumML.num" ::
   MLSTRUCT "type num = NumML.num" ::
   OPEN ["Num"] ::
   defs)

val _ = adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
     let val S = PP.add_string ppstrm
         fun NL() = PP.add_newline ppstrm
     in S "val _ = ConstMapML.insert\
        \ (Term.prim_mk_const{Name=\"CONS\",Thy=\"list\"});";
        NL();
        S "val _ = ConstMapML.insert\
        \ (Term.prim_mk_const{Name=\"NIL\",Thy=\"list\"});";
        NL(); NL()
     end)};

val _ = export_theory ();
