signature Dsyntax =
sig

  (* Construction routines *)
  val mk_eq  :{lhs:Term.term, rhs:Term.term} -> Term.term
  val mk_imp :{ant:Term.term, conseq: Term.term} -> Term.term
  val mk_select :{Bvar:Term.term, Body:Term.term} -> Term.term
  val mk_forall :{Bvar:Term.term, Body:Term.term} -> Term.term
  val mk_exists :{Bvar:Term.term, Body:Term.term} -> Term.term
  val mk_neg  :Term.term -> Term.term
  val mk_conj :{conj1:Term.term, conj2:Term.term} -> Term.term
  val mk_disj :{disj1:Term.term, disj2:Term.term} -> Term.term
  val mk_cond :{cond: Term.term, larm:Term.term, rarm:Term.term} -> Term.term
  val mk_pair :{fst:Term.term, snd:Term.term} -> Term.term
  val mk_let  :{func:Term.term, arg:Term.term} -> Term.term
  val mk_cons :{hd:Term.term, tl:Term.term} -> Term.term
  val mk_list :{els:Term.term list, ty :Type.hol_type} -> Term.term
  val mk_pabs :{varstruct:Term.term, body:Term.term} -> Term.term

  (* Destruction routines *)
  val dest_eq:Term.term -> {lhs:Term.term, rhs:Term.term}
  val dest_eq_ty:Term.term -> {lhs:Term.term, rhs:Term.term, ty:Type.hol_type}
  val lhs:Term.term -> Term.term
  val rhs:Term.term -> Term.term
  val dest_imp:Term.term -> {ant:Term.term, conseq:Term.term}
  val dest_select:Term.term -> {Bvar:Term.term, Body:Term.term}
  val dest_forall:Term.term -> {Bvar:Term.term, Body:Term.term}
  val dest_exists:Term.term -> {Bvar:Term.term, Body:Term.term}
  val dest_neg :Term.term -> Term.term
  val dest_conj:Term.term -> {conj1:Term.term, conj2:Term.term}
  val dest_disj:Term.term -> {disj1:Term.term, disj2:Term.term}
  val dest_cond:Term.term -> {cond:Term.term, larm:Term.term, rarm:Term.term}
  val dest_pair:Term.term -> {fst:Term.term, snd:Term.term}
  val dest_let: Term.term -> {func:Term.term, arg:Term.term}
  val dest_cons:Term.term -> {hd:Term.term, tl:Term.term}
  val dest_list:Term.term -> {els:Term.term list, ty :Type.hol_type}
  val dest_pabs:Term.term -> {varstruct:Term.term, body:Term.term}

  (* Query routines *)
  val is_eq:Term.term -> bool
  val is_imp:Term.term -> bool
  val is_select:Term.term -> bool
  val is_forall:Term.term -> bool
  val is_exists:Term.term -> bool
  val is_neg :Term.term -> bool
  val is_conj:Term.term -> bool
  val is_disj:Term.term -> bool
  val is_cond:Term.term -> bool
  val is_pair:Term.term -> bool
  val is_let:Term.term -> bool
  val is_cons:Term.term -> bool
  val is_list:Term.term -> bool
  val is_pabs:Term.term -> bool

  (* Construction of a term from a list of terms *)
  val list_mk_abs:(Term.term list * Term.term) -> Term.term
  val list_mk_imp:(Term.term list * Term.term) -> Term.term
  val list_mk_forall:(Term.term list * Term.term) -> Term.term
  val gen_all:Term.term -> Term.term
  val list_mk_exists:(Term.term list * Term.term) -> Term.term
  val list_mk_conj:Term.term list -> Term.term
  val list_mk_disj:Term.term list -> Term.term
  val list_mk_pair:Term.term list -> Term.term

  (* Destructing a term to a list of terms *)
  val strip_comb:Term.term -> (Term.term * Term.term list)
  val strip_abs:Term.term -> (Term.term list * Term.term)
  val strip_imp:Term.term -> (Term.term list * Term.term)
  val strip_forall:Term.term -> (Term.term list * Term.term)
  val strip_exists:Term.term -> (Term.term list * Term.term)
  val strip_conj:Term.term -> Term.term list
  val strip_disj:Term.term -> Term.term list
  val strip_pair:Term.term -> Term.term list


  (* Miscellaneous *)
  val disch:Term.term * Term.term list -> Term.term list
  val find_term:(Term.term -> bool) -> Term.term -> Term.term
  val find_terms:(Term.term -> bool) -> Term.term -> Term.term list
  val subst_occs:int list list -> (Term.term,Term.term) Lib.subst
                     -> Term.term -> Term.term
end;
