signature tripleSyntax =
sig

   val case_sum_tm: Term.term
   val triple_tm: Term.term

   val mk_case_sum: Term.term * Term.term * Term.term -> Term.term
   val mk_triple: Term.term * Term.term * Term.term * Term.term -> Term.term

   val dest_case_sum: Term.term -> Term.term * Term.term * Term.term
   val dest_code: Term.term -> Term.term
   val dest_model: Term.term -> Term.term
   val dest_post: Term.term -> Term.term
   val dest_pre: Term.term -> Term.term
   val dest_pre_post: Term.term -> Term.term * Term.term
   val dest_triple: Term.term -> Term.term * Term.term * Term.term * Term.term

   val is_case_sum: Term.term -> bool
   val is_triple: Term.term -> bool

   val get_component: (Term.term -> bool) -> Thm.thm -> Term.term
end
