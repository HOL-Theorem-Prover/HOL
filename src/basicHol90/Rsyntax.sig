signature Rsyntax =
  sig
    type hol_type = Type.hol_type
    type term  = Term.term
    type thm = Thm.thm
    val INST : (term,term) Lib.subst -> thm -> thm
    val INST_TYPE : (hol_type,hol_type) Lib.subst -> thm -> thm
    val INST_TY_TERM : (term,term)Lib.subst * (hol_type,hol_type) Lib.subst
                         -> thm -> thm
    val SUBST : (term,thm)Lib.subst -> term -> thm -> thm
    val SUBST_CONV : (term,thm)Lib.subst -> term -> term -> thm
    val define_new_type_bijections
        : {ABS:string, REP:string, name:string, tyax:thm} -> thm
    val dest_abs : term -> {Body:term, Bvar:term}
    val dest_comb : term -> {Rand:term, Rator:term}
    val dest_cond : term -> {cond:term, larm:term, rarm:term}
    val dest_conj : term -> {conj1:term, conj2:term}
    val dest_cons : term -> {hd:term, tl:term}
    val dest_const : term -> {Name:string, Ty:hol_type}
    val dest_disj : term -> {disj1:term, disj2:term}
    val dest_eq : term -> {lhs:term, rhs:term}
    val dest_exists : term -> {Body:term, Bvar:term}
    val dest_forall : term -> {Body:term, Bvar:term}
    val dest_imp : term -> {ant:term, conseq:term}
    val dest_let : term -> {arg:term, func:term}
    val dest_list : term -> {els:term list, ty:hol_type}
    val dest_pabs : term -> {body:term, varstruct:term}
    val dest_pair : term -> {fst:term, snd:term}
    val dest_select : term -> {Body:term, Bvar:term}
    val dest_type : hol_type -> {Args:hol_type list, Tyop:string}
    val dest_var : term -> {Name:string, Ty:hol_type}
    val inst : (hol_type,hol_type) Lib.subst -> term -> term
    val match_term : term -> term
                     -> (term,term) Lib.subst * (hol_type,hol_type) Lib.subst
    val match_type : hol_type -> hol_type -> (hol_type,hol_type) Lib.subst
    val mk_abs : {Body:term, Bvar:term} -> term
    val mk_comb : {Rand:term, Rator:term} -> term
    val mk_cond : {cond:term, larm:term, rarm:term} -> term
    val mk_conj : {conj1:term, conj2:term} -> term
    val mk_cons : {hd:term, tl:term} -> term
    val mk_const : {Name:string, Ty:hol_type} -> term
    val mk_disj : {disj1:term, disj2:term} -> term
    val mk_eq : {lhs:term, rhs:term} -> term
    val mk_exists : {Body:term, Bvar:term} -> term
    val mk_forall : {Body:term, Bvar:term} -> term
    val mk_imp : {ant:term, conseq:term} -> term
    val mk_let : {arg:term, func:term} -> term
    val mk_list : {els:term list, ty:hol_type} -> term
    val mk_pabs : {body:term, varstruct:term} -> term
    val mk_pair : {fst:term, snd:term} -> term
    val mk_primed_var : {Name:string, Ty:hol_type} -> term
    val mk_select : {Body:term, Bvar:term} -> term
    val mk_type : {Args:hol_type list, Tyop:string} -> hol_type
    val mk_var : {Name:string, Ty:hol_type} -> term
    val new_binder : {Name:string, Ty:hol_type} -> unit
    val new_constant : {Name:string, Ty:hol_type} -> unit
    val new_infix : {Name:string, Prec:int, Ty:hol_type} -> unit
    val new_recursive_definition
        : {def:term, fixity:Parse.fixity, name:string, rec_axiom:thm} -> thm
    val new_specification
        : {consts:{const_name:string, fixity:Parse.fixity} list,
           name:string, sat_thm:thm} -> thm
    val new_type : {Arity:int, Name:string} -> unit
    val new_type_definition : {inhab_thm:thm, name:string, pred:term} -> thm
    val subst : (term,term) Lib.subst -> term -> term
    val subst_occs : int list list -> (term,term) Lib.subst -> term -> term
    val type_subst : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type
  end
