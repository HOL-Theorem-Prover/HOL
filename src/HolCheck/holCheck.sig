signature holCheck =
sig

type hcinit

val holCheck : 
  Term.term * (string * Term.term) list * bool * string option * string list option *
  Term.term option -> Term.term list -> Term.term list option ->
  (hcinit option * hcinit option) option ->
  (PrimitiveBddRules.term_bdd * Thm.thm option * Term.term list option) list * (Thm.thm option * Thm.thm option) *
  (hcinit option * hcinit option) option

end