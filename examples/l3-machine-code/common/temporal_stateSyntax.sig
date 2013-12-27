signature temporal_stateSyntax =
sig

   val temporal_next_tm: Term.term

   val mk_temporal_next:
      Term.term * Term.term * Term.term * Term.term -> Term.term

   val dest_code: Term.term -> Term.term
   val dest_post: Term.term -> Term.term
   val dest_pre: Term.term -> Term.term
   val dest_pre_post: Term.term -> Term.term * Term.term
   val dest_temporal_next:
      Term.term -> Term.term * Term.term * Term.term * Term.term

   val mk_spec_or_temporal_next:
      Term.term -> bool -> Term.term * Term.term * Term.term -> Term.term

   val dest_code': Term.term -> Term.term
   val dest_post': Term.term -> Term.term
   val dest_pre': Term.term -> Term.term
   val dest_pre_post': Term.term -> Term.term * Term.term
   val dest_spec': Term.term -> Term.term * Term.term * Term.term * Term.term

   val is_temporal_next: Term.term -> bool

end
