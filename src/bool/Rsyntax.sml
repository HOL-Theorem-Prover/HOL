structure Rsyntax :> Rsyntax =
struct

    type term     = Term.term;
    type thm      = Thm.thm;
    type hol_type = Type.hol_type;
    type fixity   = Parse.fixity;

val mk_var = Term.mk_var;
val mk_primed_var = Term.mk_primed_var;
val mk_const = Term.mk_const;
val mk_thy_const = Term.mk_thy_const;
val mk_comb = Term.mk_comb;
val mk_abs = Term.mk_abs;
val mk_eq = boolSyntax.mk_eq;
val mk_imp = boolSyntax.mk_imp;
val mk_select = boolSyntax.mk_select;
val mk_forall = boolSyntax.mk_forall;
val mk_exists = boolSyntax.mk_exists;
val mk_exists1 = boolSyntax.mk_exists1;
val mk_conj = boolSyntax.mk_conj;
val mk_disj = boolSyntax.mk_disj;
val mk_cond = boolSyntax.mk_cond;
val mk_let= boolSyntax.mk_let;

val dest_var = Term.dest_var;
val dest_const = Term.dest_const;
val dest_thy_const = Term.dest_thy_const;
val dest_comb = Term.dest_comb
val dest_abs = Term.dest_abs;
val dest_eq = boolSyntax.dest_eq;
val dest_imp = boolSyntax.dest_imp
val dest_imp_only = boolSyntax.dest_imp_only
val dest_select = boolSyntax.dest_select;
val dest_forall = boolSyntax.dest_forall;
val dest_exists = boolSyntax.dest_exists;
val dest_exists1 = boolSyntax.dest_exists1;
val dest_conj = boolSyntax.dest_conj
val dest_disj = boolSyntax.dest_disj
val dest_cond = boolSyntax.dest_cond;
val dest_let = boolSyntax.dest_let;

val mk_type = Type.mk_type;
val dest_type = Type.dest_type;

val type_subst = Type.type_subst;
val subst = Term.subst;
val subst_occs = HolKernel.subst_occs;
val inst = Term.inst;

val match_type = Type.match_type
val match_term = Term.match_term;

val SUBST = Thm.SUBST
val INST_TYPE = Thm.INST_TYPE;
val SUBST_CONV = Drule.SUBST_CONV;
val INST = Thm.INST;
val INST_TY_TERM = Drule.INST_TY_TERM;

val new_type = boolSyntax.new_type;
val new_constant = boolSyntax.new_constant;
val new_infix = boolSyntax.new_infix;
val new_binder = boolSyntax.new_binder;
val new_specification = boolSyntax.new_specification;
fun new_type_definition{name,inhab_thm} = 
    boolSyntax.new_type_definition(name,inhab_thm);

end; (* Rsyntax *)
