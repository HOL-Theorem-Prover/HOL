structure Rsyntax :> Rsyntax =

struct
    type term = Term.term;
    type thm = Thm.thm;
    type hol_type = Type.hol_type;
    type fixity = Parse.fixity;

val mk_var = Term.mk_var;
val mk_const = Term.mk_const;
val mk_comb = Term.mk_comb;
val mk_abs = Term.mk_abs;
val mk_primed_var = Term.mk_primed_var;
val mk_eq = Dsyntax.mk_eq;
val mk_imp = Dsyntax.mk_imp;
val mk_select = Dsyntax.mk_select;
val mk_forall = Dsyntax.mk_forall;
val mk_exists = Dsyntax.mk_exists;
val mk_conj = Dsyntax.mk_conj;
val mk_disj = Dsyntax.mk_disj;
val mk_cond = Dsyntax.mk_cond;
val mk_pair = Dsyntax.mk_pair;
val mk_let= Dsyntax.mk_let;
val mk_cons = Dsyntax.mk_cons;
val mk_list = Dsyntax.mk_list;
val mk_pabs = Dsyntax.mk_pabs;

val dest_var = Term.dest_var;
val dest_const = Term.dest_const;
val dest_comb = Term.dest_comb
val dest_abs = Term.dest_abs;
val dest_eq = Dsyntax.dest_eq;
val dest_imp = Dsyntax.dest_imp
val dest_select = Dsyntax.dest_select;
val dest_forall = Dsyntax.dest_forall;
val dest_exists = Dsyntax.dest_exists;
val dest_conj = Dsyntax.dest_conj
val dest_disj = Dsyntax.dest_disj
val dest_cond = Dsyntax.dest_cond;
val dest_pair = Dsyntax.dest_pair;
val dest_let = Dsyntax.dest_let;
val dest_cons = Dsyntax.dest_cons;
val dest_list = Dsyntax.dest_list;
val dest_pabs = Dsyntax.dest_pabs;

val mk_type = Type.mk_type;
val dest_type = Type.dest_type;

val type_subst = Type.type_subst;
val subst = Term.subst;
val subst_occs = Dsyntax.subst_occs;
val inst = Term.inst;

val match_type = Type.match_type
val match_term = Term.match_term;

val SUBST = Thm.SUBST
val INST_TYPE = Thm.INST_TYPE;
val SUBST_CONV = Drule.SUBST_CONV;
val INST = Thm.INST;
val INST_TY_TERM = Conv.INST_TY_TERM;


val new_type = Parse.new_type;
val new_constant = Theory.new_constant;
val new_infix = Parse.new_infix;
val new_binder = Parse.new_binder;

val new_specification = Parse.new_specification;

val new_type_definition = Parse.new_type_definition;

val new_recursive_definition = Prim_rec.new_recursive_definition;
val define_new_type_bijections = Type_def_support.define_new_type_bijections;

end; (* Rsyntax *)
