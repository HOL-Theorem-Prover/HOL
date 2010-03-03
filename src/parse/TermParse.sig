signature TermParse =
sig

  type term = Term.term
  type hol_type = Type.hol_type
  type kind = Kind.kind
  type grammar = term_grammar.grammar
  type tygrammar = type_grammar.grammar
  type kdgrammar = kind_grammar.grammar
  type absyn = Absyn.absyn
  type preterm = Preterm.preterm
  type 'a quotation = 'a Portable.frag list
  type pprinters = ((term -> string) * (hol_type -> string) * (kind -> string)) option

  (* standard transformations *)
  val absyn : grammar -> tygrammar -> kdgrammar -> term quotation -> absyn
  val preterm : grammar -> tygrammar -> kdgrammar -> term quotation -> preterm
  val absyn_to_preterm : grammar -> absyn -> preterm
  val absyn_to_term : pprinters -> grammar -> absyn -> term
  val preterm_to_term : pprinters -> preterm -> term
  val term : pprinters -> grammar -> tygrammar -> kdgrammar -> term quotation -> term

  (* in contexts *)
  val ctxt_preterm_to_term : pprinters -> term list -> preterm -> term
  val ctxt_term : pprinters -> grammar -> tygrammar -> kdgrammar -> term list ->
                  term quotation -> term

end
