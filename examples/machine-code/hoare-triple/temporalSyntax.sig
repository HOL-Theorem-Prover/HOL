signature temporalSyntax =
sig
   val always_tm: Term.term
   val eventually_tm: Term.term
   val next_tm: Term.term
   val now_tm: Term.term
   val t_and_tm: Term.term
   val t_implies_tm: Term.term
   val temporal_tm: Term.term

   val dest_always: Term.term -> Term.term
   val dest_eventually: Term.term -> Term.term
   val dest_next: Term.term -> Term.term
   val dest_now: Term.term -> Term.term
   val dest_t_and: Term.term -> Term.term * Term.term
   val dest_t_implies: Term.term -> Term.term * Term.term
   val dest_temporal: Term.term -> Term.term * Term.term * Term.term

   val is_always: Term.term -> bool
   val is_eventually: Term.term -> bool
   val is_next: Term.term -> bool
   val is_now: Term.term -> bool
   val is_t_and: Term.term -> bool
   val is_t_implies: Term.term -> bool
   val is_temporal: Term.term -> bool

   val mk_always: Term.term -> Term.term
   val mk_eventually: Term.term -> Term.term
   val mk_next: Term.term -> Term.term
   val mk_now: Term.term -> Term.term
   val mk_t_and: Term.term * Term.term -> Term.term
   val mk_t_implies: Term.term * Term.term -> Term.term
   val mk_temporal: Term.term * Term.term * Term.term -> Term.term
end
