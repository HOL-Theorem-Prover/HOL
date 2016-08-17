signature TermParse =
sig

  type term = Term.term
  type hol_type = Type.hol_type
  type grammar = term_grammar.grammar
  type tygrammar = type_grammar.grammar
  type absyn = Absyn.absyn
  type preterm = Preterm.preterm
  type 'a quotation = 'a Portable.frag list
  type pprinters = ((term -> string) * (hol_type -> string)) option
  type 'a in_env = 'a Pretype.in_env

  (* standard transformations *)
  val absyn : grammar -> tygrammar -> term quotation -> absyn
  val preterm : grammar -> tygrammar -> term quotation -> preterm in_env
  val typed_preterm : grammar -> tygrammar -> hol_type -> term quotation ->
                      preterm in_env
  val absyn_to_preterm : grammar -> absyn -> preterm in_env
  val absyn_to_preterm_in_env : grammar -> absyn -> Parse_support.preterm_in_env
  val absyn_to_term : pprinters -> grammar -> absyn -> term
  val preterm_to_term : pprinters -> preterm -> term Preterm.errM
  val term : pprinters -> grammar -> tygrammar -> term quotation -> term
  val termS : grammar -> tygrammar -> term quotation -> term seq.seq

  (* in contexts *)
  val ctxt_preterm_to_term : pprinters -> hol_type option -> term list ->
                             preterm -> term in_env
  val ctxt_term : pprinters -> grammar -> tygrammar -> hol_type option ->
                  term list -> term quotation -> term Preterm.errM
  val ctxt_termS : grammar -> tygrammar -> hol_type option -> term list ->
                   term quotation -> term seq.seq

end
