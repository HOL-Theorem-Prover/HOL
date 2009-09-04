open HolKernel boolLib bossLib Parse;
open EmitML optionTheory;

val _ = new_theory "option_emit";

val THE_NONE = Q.prove (
  `THE NONE = FAIL THE ^(mk_var("applied to NONE",bool)) NONE`,
  REWRITE_TAC [combinTheory.FAIL_THM]);

val _ = ConstMapML.insert_cons(Term.prim_mk_const{Name="SOME",Thy="option"});
val _ = ConstMapML.insert_cons(Term.prim_mk_const{Name="NONE",Thy="option"});

val defs =
  map DEFN [OPTION_MAP_DEF, IS_SOME_DEF, IS_NONE_DEF,
            CONJ THE_NONE THE_DEF, OPTION_JOIN_DEF];

val _ = eSML "option"
  (MLSIGSTRUCT ["datatype option = datatype Option.option"] @ defs);

val _ = eCAML "option" defs;

val _ = adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME
     (fn ppstrm =>
        let val S = PP.add_string ppstrm
            fun NL() = PP.add_newline ppstrm
        in S "val _ = ConstMapML.insert_cons\
             \(Term.prim_mk_const{Name=\"SOME\",Thy=\"option\"});";
           NL();
           S "val _ = ConstMapML.insert_cons\
             \(Term.prim_mk_const{Name=\"NONE\",Thy=\"option\"});";
           NL(); NL()
        end)}

val _ = export_theory ();
