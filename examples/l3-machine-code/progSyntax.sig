signature progSyntax =
sig

   val star_tm: Term.term
   val cond_tm: Term.term
   val spec_tm: Term.term

   val mk_star: Term.term * Term.term -> Term.term
   val mk_cond: Term.term -> Term.term
   val mk_spec: Term.term * Term.term * Term.term * Term.term -> Term.term

   val list_mk_star: Term.term list -> Term.term
   val strip_star: Term.term -> Term.term list

   val dest_star: Term.term -> Term.term * Term.term
   val dest_cond: Term.term -> Term.term
   val dest_spec: Term.term -> Term.term * Term.term * Term.term * Term.term

   val is_star: Term.term -> bool
   val is_cond: Term.term -> bool
   val is_spec: Term.term -> bool

end
