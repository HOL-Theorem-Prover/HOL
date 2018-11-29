signature TermParse =
sig

  type term = Term.term
  type hol_type = Type.hol_type
  type grammar = term_grammar.grammar
  type tygrammar = type_grammar.grammar
  type absyn = Absyn.absyn
  type preterm = Preterm.preterm
  type 'a quotation = 'a PP.frag list
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
  val prim_ctxt_termS : (term quotation -> absyn) -> grammar -> term list ->
                        term quotation -> term seq.seq

end

(*
   Note that ctxt_termS and other functions that take grammars and move from
   quotations through the Absyn type (to terms, preterms and similar) will
   almost certainly calculate the precedence matrix for the given term
   grammar, which can take noticeable amounts of time for large grammars.

   For this reason, prim_ctxt_termS takes a function parameter which is given
   the task of doing the concrete syntax parsing. In particular, Parse.Absyn
   is a good choice for this parameter: it is rebound (using a reference)
   when the global grammar changes.

   Alternatively, write something like

     val p = ctxt_termS g tyg

   and then use the p function from then on; that way the precedence matrix
   calculation is only done with the call to ctxt_termS, not when p is applied.
*)
